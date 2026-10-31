-- Prove2me | solution 1 for MinBuying.triangular_price_raising
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:29:49.205571+00:00
-- url     : https://prove2.me/submissions/c28850ff-dccb-4c1e-b9ed-fe6daf0cd424

import Theorems.Thm_MinBuying_triangular_law_specification

open MeasureTheory Set MinBuying
open scoped BigOperators

private lemma payment_measurable {n : ℕ} (p : Prices n) : Measurable (payment p) := by
  have ha : Measurable (affordable p) := by
    apply measurable_finset_iff.mpr
    intro i
    apply measurableSet_setOfPred.mp
    simpa [affordable] using
      (measurableSet_le measurable_const (measurable_pi_apply i) :
        MeasurableSet {v : Valuations n | p i ≤ v i})
  have hf : Measurable (fun A : Finset (Fin n) => if h : A.Nonempty then A.inf' h p else 0) :=
    measurable_of_countable _
  exact hf.comp ha

private lemma payment_bounds {n : ℕ} (p : Prices n) (hp : FeasiblePrices p)
    (v : Valuations n) : 0 ≤ payment p v ∧ payment p v ≤ ∑ i, p i := by
  unfold payment
  split_ifs with h
  · constructor
    · exact Finset.le_inf' h p (fun i _ => hp i)
    · obtain ⟨i, hi⟩ := h
      exact (Finset.inf'_le p hi).trans
        (Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i))
  · exact ⟨le_rfl, Finset.sum_nonneg (fun i _ => hp i)⟩

private lemma payment_integrable {n : ℕ} (μ : JointLaw n) [IsFiniteMeasure μ]
    (p : Prices n) (hp : FeasiblePrices p) : Integrable (payment p) μ := by
  apply Integrable.of_bound (payment_measurable p).aestronglyMeasurable (∑ i, p i)
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_of_nonneg (payment_bounds p hp v).1]
  exact (payment_bounds p hp v).2

private lemma payment_update {n : ℕ} (p : Prices n) (v : Valuations n)
    (i : Fin n) (s x : ℝ) :
    payment (Function.update p i s) (Function.update v i x) =
      if h : ((affordable p v).erase i).Nonempty then
        if s ≤ x then min s (((affordable p v).erase i).inf' h p)
        else ((affordable p v).erase i).inf' h p
      else if s ≤ x then s else 0 := by
  classical
  let A := (affordable p v).erase i
  have hA : affordable (Function.update p i s) (Function.update v i x) =
      if s ≤ x then insert i A else A := by
    ext j
    by_cases hji : j = i
    · subst j
      by_cases hsx : s ≤ x <;> simp [affordable, A, hsx]
    · by_cases hsx : s ≤ x <;> simp [affordable, A, hji, hsx, Function.update]
  have hval (h : A.Nonempty) : A.inf' h (Function.update p i s) = A.inf' h p := by
    apply Finset.inf'_congr h rfl
    intro j hj
    simp [Function.update, Finset.ne_of_mem_erase hj]
  change payment (Function.update p i s) (Function.update v i x) =
    if h : A.Nonempty then if s ≤ x then min s (A.inf' h p) else A.inf' h p
    else if s ≤ x then s else 0
  by_cases h : A.Nonempty
  · by_cases hsx : s ≤ x
    · simp [payment, hA, hsx, h, Finset.inf'_insert, hval]
    · simp [payment, hA, hsx, h, hval]
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    by_cases hsx : s ≤ x <;> simp [payment, hA, hsx, h, he]

private lemma integrate_choice (μ : Measure ℝ) [IsProbabilityMeasure μ] (s r b : ℝ) :
    (∫ x : ℝ, if s ≤ x then b else r ∂μ) =
      (1 - rejection μ s) * b + rejection μ s * r := by
  change (∫ x : ℝ, (Ici s).piecewise (fun _ => b) (fun _ => r) x ∂μ) = _
  rw [integral_piecewise measurableSet_Ici (integrable_const b).integrableOn
    (integrable_const r).integrableOn]
  simp only [setIntegral_const, smul_eq_mul, compl_Ici]
  have hμ : μ.real (Ici s) = 1 - rejection μ s := by
    simpa [rejection, Measure.real] using
      (probReal_compl_eq_one_sub (μ := μ) (s := Iio s) measurableSet_Iio)
  rw [hμ]
  rfl

private lemma active_choice_mono (a r s t : ℝ) (ha : 0 < a) (hr : 0 ≤ r)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    (1 - s / (s + a)) * min s r + s / (s + a) * r ≤
      (1 - t / (t + a)) * min t r + t / (t + a) * r := by
  have ht : 0 ≤ t := hs.trans hst
  have hsden : 0 < s + a := add_pos_of_nonneg_of_pos hs ha
  have htden : 0 < t + a := add_pos_of_nonneg_of_pos ht ha
  have hfrac : s / (s + a) ≤ t / (t + a) := by
    apply (div_le_div_iff₀ hsden htden).2
    nlinarith [mul_le_mul_of_nonneg_right hst ha.le]
  by_cases hsr : s ≤ r
  · rw [min_eq_left hsr]
    by_cases htr : t ≤ r
    · rw [min_eq_left htr]
      have heq (z : ℝ) (hz : 0 < z + a) :
          (1 - z / (z + a)) * z + z / (z + a) * r = (z / (z + a)) * (a + r) := by
        field_simp
        ring
      rw [heq s hsden, heq t htden]
      exact mul_le_mul_of_nonneg_right hfrac (add_nonneg ha.le hr)
    · rw [min_eq_right (le_of_not_ge htr)]
      have hf : 0 ≤ 1 - s / (s + a) := by
        apply sub_nonneg.mpr
        exact (div_le_one hsden).mpr (le_add_of_nonneg_right ha.le)
      nlinarith [mul_nonneg hf (sub_nonneg.mpr hsr)]
  · have hrs : r ≤ s := le_of_not_ge hsr
    rw [min_eq_right hrs, min_eq_right (hrs.trans hst)]
    ring_nf
    rfl

private lemma single_choice_mono (a s t : ℝ) (ha : 0 < a)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    (1 - s / (s + a)) * s ≤ (1 - t / (t + a)) * t := by
  have ht := hs.trans hst
  have hsden : 0 < s + a := add_pos_of_nonneg_of_pos hs ha
  have htden : 0 < t + a := add_pos_of_nonneg_of_pos ht ha
  have hfrac : s / (s + a) ≤ t / (t + a) := by
    apply (div_le_div_iff₀ hsden htden).2
    nlinarith [mul_le_mul_of_nonneg_right hst ha.le]
  have heq (z : ℝ) (hz : 0 < z + a) : (1 - z / (z + a)) * z = (z / (z + a)) * a := by
    field_simp
    ring
  rw [heq s hsden, heq t htden]
  exact mul_le_mul_of_nonneg_right hfrac ha.le

private lemma coordinate_integral_mono {n : ℕ} (I : TriangularInstance n)
    (p : Prices n) (hp : FeasiblePrices p) (i : Fin n) (v : Valuations n)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (hcap : s ≤ I.cap i → t ≤ I.cap i) :
    (∫ x : ℝ, payment (Function.update p i s) (Function.update v i x) ∂triangularMarginals I i) ≤
      ∫ x : ℝ, payment (Function.update p i t) (Function.update v i x) ∂triangularMarginals I i := by
  haveI : IsProbabilityMeasure (triangularMarginals I i) :=
    (triangular_law_specification _ _ (I.a_pos i) (I.cap_pos i)).1.1
  have ht : 0 ≤ t := hs.trans hst
  have hbelow (u : ℝ) (hu : 0 ≤ u) (hucap : u ≤ I.cap i) :
      rejection (triangularMarginals I i) u = u / (u + I.a i) := by
    change rejection (triangularLaw (I.a i) (I.cap i)) u = _
    rw [(triangular_law_specification _ _ (I.a_pos i) (I.cap_pos i)).2.2.1]
    by_cases h0 : u ≤ 0
    · have hz : u = 0 := le_antisymm h0 hu
      simp [triangularReject, hz]
    · simp [triangularReject, h0, hucap]
  have habove (u : ℝ) (hu : I.cap i < u) : rejection (triangularMarginals I i) u = 1 := by
    change rejection (triangularLaw (I.a i) (I.cap i)) u = _
    rw [(triangular_law_specification _ _ (I.a_pos i) (I.cap_pos i)).2.2.1]
    simp [triangularReject, not_le_of_gt hu, not_le_of_gt ((I.cap_pos i).trans hu)]
  simp_rw [payment_update]
  by_cases hA : ((affordable p v).erase i).Nonempty
  · simp only [dif_pos hA]
    rw [integrate_choice, integrate_choice]
    by_cases hactive : s ≤ I.cap i
    · rw [hbelow s hs hactive, hbelow t ht (hcap hactive)]
      exact active_choice_mono _ _ s t (I.a_pos i)
        (Finset.le_inf' hA p (fun j _ => hp j)) hs hst
    · rw [habove s (lt_of_not_ge hactive), habove t ((lt_of_not_ge hactive).trans_le hst)]
      simp
  · simp only [dif_neg hA]
    rw [integrate_choice, integrate_choice]
    by_cases hactive : s ≤ I.cap i
    · rw [hbelow s hs hactive, hbelow t ht (hcap hactive)]
      simpa using single_choice_mono (I.a i) s t (I.a_pos i) hs hst
    · rw [habove s (lt_of_not_ge hactive), habove t ((lt_of_not_ge hactive).trans_le hst)]
      simp

private lemma coordinate_decomposition {n : ℕ} (I : TriangularInstance (n + 1))
    (p : Prices (n + 1)) (hp : FeasiblePrices p) (i : Fin (n + 1)) :
    Revenue (triangularJoint I) p =
      (∫ w : Fin n → ℝ, ∫ x : ℝ, payment p (i.insertNth x w)
        ∂triangularMarginals I i ∂Measure.pi (fun j => triangularMarginals I (i.succAbove j))) ∧
    Integrable (fun w : Fin n → ℝ => ∫ x : ℝ, payment p (i.insertNth x w)
        ∂triangularMarginals I i) (Measure.pi (fun j => triangularMarginals I (i.succAbove j))) := by
  haveI : ∀ j, IsProbabilityMeasure (triangularMarginals I j) :=
    fun j => (triangular_law_specification _ _ (I.a_pos j) (I.cap_pos j)).1.1
  have hpint : Integrable (payment p) (Measure.pi (triangularMarginals I)) :=
    payment_integrable _ p hp
  have hpres := (measurePreserving_piFinSuccAbove (triangularMarginals I) i).symm
  have hc := hpres.integrable_comp_of_integrable hpint
  constructor
  · exact (hpres.integral_comp' (payment p)).symm.trans (integral_prod_symm _ hc)
  · exact hc.integral_prod_right

private lemma coordinate_raise {n : ℕ} (I : TriangularInstance (n + 1))
    (p : Prices (n + 1)) (hp : FeasiblePrices p) (i : Fin (n + 1)) (t : ℝ)
    (hpt : p i ≤ t) (hcap : p i ≤ I.cap i → t ≤ I.cap i) :
    Revenue (triangularJoint I) p ≤ Revenue (triangularJoint I) (Function.update p i t) := by
  have hq : FeasiblePrices (Function.update p i t) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using (hp i).trans hpt
    · simpa [Function.update, hji] using hp j
  obtain ⟨hR, hInt⟩ := coordinate_decomposition I p hp i
  obtain ⟨hS, hJnt⟩ := coordinate_decomposition I (Function.update p i t) hq i
  rw [hR, hS]
  apply integral_mono hInt hJnt
  intro w
  have h := coordinate_integral_mono I p hp i (i.insertNth 0 w) (p i) t (hp i) hpt hcap
  simpa using h

theorem solution (n : ℕ) (I : TriangularInstance n)
    (p q : Prices n) (hp : FeasiblePrices p) (hq : FeasiblePrices q)
    (hpq : ∀ i, p i ≤ q i)
    (hcap : ∀ i, p i ≤ I.cap i → q i ≤ I.cap i) :
    Revenue (triangularJoint I) p ≤ Revenue (triangularJoint I) q := by
  classical
  cases n with
  | zero =>
    have heq : p = q := by funext i; exact Fin.elim0 i
    rw [heq]
  | succ n =>
    let r := fun A : Finset (Fin (n + 1)) => fun i => if i ∈ A then q i else p i
    have hfeas (A : Finset (Fin (n + 1))) : FeasiblePrices (r A) := by
      intro i
      dsimp [r]
      split_ifs <;> [exact hq i; exact hp i]
    have hdom (A : Finset (Fin (n + 1))) :
        Revenue (triangularJoint I) p ≤ Revenue (triangularJoint I) (r A) := by
      induction A using Finset.induction_on with
      | empty => simp [r]
      | @insert i A hi ih =>
        have hri : r A i = p i := by simp [r, hi]
        have hstep := coordinate_raise I (r A) (hfeas A) i (q i)
          (by simpa only [hri] using hpq i)
          (by simpa only [hri] using hcap i)
        have heq : Function.update (r A) i (q i) = r (insert i A) := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [r]
          · simp [Function.update, r, hji]
        rw [heq] at hstep
        exact ih.trans hstep
    simpa [r] using hdom Finset.univ
