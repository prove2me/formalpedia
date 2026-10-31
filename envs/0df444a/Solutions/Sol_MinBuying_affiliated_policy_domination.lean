-- Prove2me | solution 1 for MinBuying.affiliated_policy_domination
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:19:25.496228+00:00
-- url     : https://prove2.me/submissions/5271b47b-6b6b-4796-896b-f622209a9a28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MinBuying_affiliated_threshold_comparison
import Theorems.Thm_MinBuying_affiliated_rejection_conditioning

open MeasureTheory Set MinBuying
open scoped BigOperators
noncomputable section
namespace MinBuyingAffiliatedProof

private lemma maxEvent_measurable {n : ℕ} (t : ℝ) :
    MeasurableSet (upperMaximumEvent (n := n) t) := by
  have heq : upperMaximumEvent (n := n) t = ⋃ i : Fin n, {v | t ≤ v i} := by
    ext v
    simp [upperMaximumEvent]
  rw [heq]
  exact MeasurableSet.iUnion (fun i => measurableSet_le measurable_const (measurable_pi_apply i))

private lemma belowMax_measurable {n : ℕ} (i : Fin n) (a t : ℝ) :
    MeasurableSet (coordinateBelowAndUpperMaximumEvent i a t) :=
  (measurableSet_lt (measurable_pi_apply i) measurable_const).inter (maxEvent_measurable t)

private lemma uniform_payment {n : ℕ} (q : ℝ) (v : Valuations n) :
    payment (fun _ : Fin n => q) v =
      (upperMaximumEvent q).indicator (fun _ => q) v := by
  classical
  by_cases h : (affordable (fun _ : Fin n => q) v).Nonempty
  · have hv : v ∈ upperMaximumEvent q := by
      obtain ⟨i,hi⟩ := h
      exact ⟨i,(Finset.mem_filter.mp hi).2⟩
    simp [payment,h,hv]
  · have hv : v ∉ upperMaximumEvent q := by
      rintro ⟨i,hi⟩
      exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    simp [payment,h,hv]

private lemma uniform_revenue {n : ℕ} (μ : JointLaw n) (q : ℝ) :
    uniformRevenue μ q = q * μ.real (upperMaximumEvent q) := by
  unfold uniformRevenue Revenue
  simp_rw [uniform_payment]
  rw [integral_indicator_const _ (maxEvent_measurable q),smul_eq_mul,mul_comm]

private def twoTier (n : ℕ) (a b : ℝ) : Prices (n+1) := Fin.cons a (fun _ => b)

private lemma twoTier_zero (n : ℕ) (a b : ℝ) : twoTier n a b 0 = a := rfl
private lemma twoTier_succ (n : ℕ) (a b : ℝ) (i : Fin n) : twoTier n a b i.succ = b := rfl

private lemma twoTier_ne_zero (n : ℕ) (a b : ℝ) (i : Fin (n+1)) (hi : i ≠ 0) :
    twoTier n a b i = b := by
  refine Fin.cases (fun h => (h rfl).elim) (fun j _ => rfl) i hi

private lemma twoTier_payment (n : ℕ) (a b : ℝ) (hab : a ≤ b) (v : Valuations (n+1)) :
    payment (twoTier n a b) v =
      {v : Valuations (n+1) | a ≤ v 0}.indicator (fun _ => a) v +
      (coordinateBelowAndUpperMaximumEvent 0 a b).indicator (fun _ => b) v := by
  classical
  by_cases ha : a ≤ v 0
  · have haC : v ∈ {v : Valuations (n+1) | a ≤ v 0} := ha
    have haff : 0 ∈ affordable (twoTier n a b) v := by simp [affordable,ha,twoTier_zero]
    have hnon : (affordable (twoTier n a b) v).Nonempty := ⟨0,haff⟩
    have hb : v ∉ coordinateBelowAndUpperMaximumEvent 0 a b := by
      intro hv;exact not_lt_of_ge ha hv.1
    simp only [payment,dif_pos hnon,Set.indicator_of_mem haC,Set.indicator_of_notMem hb,add_zero]
    apply le_antisymm
    · simpa only [twoTier_zero] using Finset.inf'_le (twoTier n a b) haff
    · apply Finset.le_inf'
      intro i _
      by_cases hi : i = 0
      · subst i;exact le_rfl
      · rw [twoTier_ne_zero n a b i hi];exact hab
  · have haC : v ∉ {v : Valuations (n+1) | a ≤ v 0} := ha
    have hlt : v 0 < a := lt_of_not_ge ha
    by_cases hb : v ∈ coordinateBelowAndUpperMaximumEvent 0 a b
    · obtain ⟨hlt', j, hj⟩ := hb
      have hj0 : j ≠ 0 := by intro heq;subst j;linarith
      have hnon : (affordable (twoTier n a b) v).Nonempty := by
        refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
        simpa [twoTier_ne_zero n a b j hj0] using hj
      have hbmem : v ∈ coordinateBelowAndUpperMaximumEvent 0 a b := ⟨hlt',j,hj⟩
      simp only [payment,dif_pos hnon,Set.indicator_of_notMem haC,Set.indicator_of_mem hbmem,zero_add]
      calc
        (affordable (twoTier n a b) v).inf' hnon (twoTier n a b)
            = (affordable (twoTier n a b) v).inf' hnon (fun _ => b) := by
          apply Finset.inf'_congr hnon rfl
          intro i hi
          apply twoTier_ne_zero
          intro hi0
          subst i
          exact ha (by simpa only [twoTier_zero] using (Finset.mem_filter.mp hi).2)
        _ = b := by simp
    · have hnon : ¬ (affordable (twoTier n a b) v).Nonempty := by
        rintro ⟨j,hj⟩
        have hj0 : j ≠ 0 := by
          intro heq;subst j
          exact ha (by simpa only [twoTier_zero] using (Finset.mem_filter.mp hj).2)
        apply hb
        refine ⟨hlt,j,?_⟩
        simpa [twoTier_ne_zero n a b j hj0] using (Finset.mem_filter.mp hj).2
      simp only [payment,dif_neg hnon,Set.indicator_of_notMem haC,Set.indicator_of_notMem hb,zero_add]

private lemma twoTier_revenue (n : ℕ) (μ : JointLaw (n+1)) [IsProbabilityMeasure μ]
    (a b : ℝ) (hab : a ≤ b) :
    Revenue μ (twoTier n a b) =
      a*μ.real {v : Valuations (n+1) | a ≤ v 0} +
      b*μ.real (coordinateBelowAndUpperMaximumEvent 0 a b) := by
  have hC : MeasurableSet {v : Valuations (n+1) | a ≤ v 0} :=
    measurableSet_le measurable_const (measurable_pi_apply 0)
  have hB := belowMax_measurable (0 : Fin (n+1)) a b
  unfold Revenue
  simp_rw [twoTier_payment n a b hab]
  rw [integral_add ((integrable_const a).indicator hC) ((integrable_const b).indicator hB),
    integral_indicator_const _ hC,integral_indicator_const _ hB]
  simp only [smul_eq_mul]
  ring

private lemma maxEvent_split (n : ℕ) (a : ℝ) :
    upperMaximumEvent (n := n+1) a =
      {v : Valuations (n+1) | a ≤ v 0} ∪ coordinateBelowAndUpperMaximumEvent 0 a a := by
  ext v
  constructor
  · intro hv
    by_cases h : a ≤ v 0
    · exact Or.inl h
    · exact Or.inr ⟨lt_of_not_ge h,hv⟩
  · rintro (h | h)
    · exact ⟨0,h⟩
    · exact h.2

private lemma maxEvent_split_real (n : ℕ) (μ : JointLaw (n+1)) [IsProbabilityMeasure μ] (a : ℝ) :
    μ.real (upperMaximumEvent a) =
      μ.real {v : Valuations (n+1) | a ≤ v 0} +
      μ.real (coordinateBelowAndUpperMaximumEvent 0 a a) := by
  rw [maxEvent_split]
  apply measureReal_union
  · exact Set.disjoint_left.mpr (fun v hv hw => not_lt_of_ge hv hw.1)
  · exact belowMax_measurable 0 a a
  all_goals exact measure_ne_top _ _

private lemma twoTier_bound (n : ℕ) (μ : JointLaw (n+1))
    (hμ : ValidLaw μ) (hex : Exchangeable μ) (haff : Affiliated μ)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    Revenue μ (twoTier n a b) ≤ max (uniformRevenue μ a) (uniformRevenue μ b) := by
  haveI : IsProbabilityMeasure μ := hμ.1
  let A := μ.real (upperMaximumEvent a)
  let B := μ.real (upperMaximumEvent b)
  let C := μ.real {v : Valuations (n+1) | a ≤ v 0}
  let D := μ.real (coordinateBelowAndUpperMaximumEvent 0 a a)
  let E := μ.real (coordinateBelowAndUpperMaximumEvent 0 a b)
  have hCD : A = C+D := maxEvent_split_real n μ a
  have hC : 0 ≤ C := measureReal_nonneg
  have hD : 0 ≤ D := measureReal_nonneg
  have hB : 0 ≤ B := measureReal_nonneg
  have hE : 0 ≤ E := measureReal_nonneg
  have hBA : B ≤ A := by
    apply measureReal_mono
    · intro v hv
      obtain ⟨i,hi⟩ := hv
      exact ⟨i,hab.trans hi⟩
    · exact measure_ne_top _ _
  have hEB : E ≤ B := measureReal_mono (fun _ h => h.2)
  rw [twoTier_revenue n μ a b hab,uniform_revenue,uniform_revenue]
  change a*C+b*E ≤ max (a*A) (b*B)
  by_cases hB0 : B = 0
  · have hE0 : E = 0 := le_antisymm (hEB.trans_eq hB0) hE
    rw [hE0,mul_zero,add_zero]
    exact (mul_le_mul_of_nonneg_left (by linarith [hCD]) ha).trans (le_max_left _ _)
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    have hApos : 0 < A := hBpos.trans_le hBA
    have hBmeasure : 0 < μ (upperMaximumEvent b) := by
      exact ENNReal.toReal_pos_iff.mp hBpos |>.1
    have hcomp : E/B ≤ D/A := affiliated_threshold_comparison (n+1) (by omega) μ hμ hex haff 0 a b hab hBmeasure
    have hcross : E*A ≤ D*B := (div_le_div_iff₀ hBpos hApos).mp hcomp
    have hweight : C/A+D/A = 1 := by rw [← add_div,← hCD];exact div_self (ne_of_gt hApos)
    have hDC : 0 ≤ C/A := div_nonneg hC hApos.le
    have hDD : 0 ≤ D/A := div_nonneg hD hApos.le
    have hM1 : a*A ≤ max (a*A) (b*B) := le_max_left _ _
    have hM2 : b*B ≤ max (a*A) (b*B) := le_max_right _ _
    have hw1 := mul_le_mul_of_nonneg_left hM1 hDC
    have hw2 := mul_le_mul_of_nonneg_left hM2 hDD
    have hmult := mul_le_mul_of_nonneg_left hcross (ha.trans hab)
    have hid1 : C/A*(a*A) = a*C := by field_simp
    have hid2 : D/A*(b*B) = b*(D*B)/A := by ring
    have hEb : b*E ≤ b*(D*B)/A := (le_div_iff₀ hApos).mpr (by nlinarith only [hmult])
    calc
      a*C+b*E ≤ C/A*(a*A)+D/A*(b*B) := by rw [hid1,hid2];linarith
      _ ≤ C/A*max (a*A) (b*B)+D/A*max (a*A) (b*B) := add_le_add hw1 hw2
      _ = max (a*A) (b*B) := by rw [← add_mul,hweight,one_mul]

private def firstPurchase {n : ℕ} (p : Prices n) (i : Fin n) : Set (Valuations n) :=
  Set.univ.pi (fun j => if j < i then Iio (p j) else if j = i then Ici (p j) else Set.univ)

private lemma firstPurchase_iff {n : ℕ} (p : Prices n) (i : Fin n) (v : Valuations n) :
    v ∈ firstPurchase p i ↔ p i ≤ v i ∧ ∀ j, j < i → v j < p j := by
  simp only [firstPurchase, Set.mem_pi, Set.mem_univ, forall_true_left]
  constructor
  · intro h
    constructor
    · simpa using h i
    · intro j hj
      simpa [hj] using h j
  · rintro ⟨hi, hprev⟩ j
    by_cases hj : j < i
    · simpa [hj] using hprev j hj
    · by_cases heq : j = i
      · subst j
        simpa using hi
      · simp [hj, heq]

private lemma firstPurchase_measurable {n : ℕ} (p : Prices n) (i : Fin n) :
    MeasurableSet (firstPurchase p i) := by
  apply MeasurableSet.pi Set.countable_univ
  intro j _
  split_ifs <;> measurability

private lemma payment_sum {n : ℕ} (p : Prices n) (hsorted : Monotone p)
    (v : Valuations n) :
    payment p v = ∑ i : Fin n, (firstPurchase p i).indicator (fun _ => p i) v := by
  classical
  by_cases h : (affordable p v).Nonempty
  · let k := (affordable p v).min' h
    have hk : k ∈ affordable p v := Finset.min'_mem _ _
    have hkval : p k ≤ v k := (Finset.mem_filter.mp hk).2
    have hkle : ∀ j ∈ affordable p v, k ≤ j := by
      intro j hj
      exact Finset.min'_le _ _ hj
    have hpay : payment p v = p k := by
      rw [payment, dif_pos h]
      apply le_antisymm
      · exact Finset.inf'_le _ hk
      · exact Finset.le_inf' h p (fun j hj => hsorted (hkle j hj))
    have hkfirst : v ∈ firstPurchase p k := by
      apply (firstPurchase_iff p k v).mpr
      refine ⟨hkval, ?_⟩
      intro j hj
      by_contra hrej
      have hja : j ∈ affordable p v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt hrej⟩
      exact (not_lt_of_ge (hkle j hja)) hj
    have hother : ∀ j, j ≠ k → v ∉ firstPurchase p j := by
      intro j hj hfirst
      obtain ⟨hjval, hprev⟩ := (firstPurchase_iff p j v).mp hfirst
      have hja : j ∈ affordable p v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjval⟩
      have hkj : k < j := lt_of_le_of_ne (hkle j hja) (Ne.symm hj)
      exact (not_lt_of_ge hkval) (hprev k hkj)
    rw [hpay, Finset.sum_eq_single k]
    · simp [hkfirst]
    · intro j _ hj
      exact Set.indicator_of_notMem (hother j hj) _
    · simp
  · have hnone : ∀ i, v ∉ firstPurchase p i := by
      intro i hi
      have hia : i ∈ affordable p v :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((firstPurchase_iff p i v).mp hi).1⟩
      exact h ⟨i, hia⟩
    simp [payment, h, hnone]

private lemma payment_measurable {n : ℕ} (p : Prices n) (hp : Monotone p) :
    Measurable (payment p) := by
  have heq : payment p = fun v => ∑ i : Fin n, (firstPurchase p i).indicator (fun _ => p i) v :=
    funext (payment_sum p hp)
  rw [heq]
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (firstPurchase_measurable p i))

private lemma payment_integrable {n : ℕ} (μ : JointLaw n) [IsFiniteMeasure μ]
    (p : Prices n) (hp : Monotone p) : Integrable (payment p) μ := by
  have heq : payment p = fun v => ∑ i : Fin n, (firstPurchase p i).indicator (fun _ => p i) v :=
    funext (payment_sum p hp)
  rw [heq]
  exact integrable_finsetSum _ (fun i _ => (integrable_const (p i)).indicator (firstPurchase_measurable p i))

private lemma payment_recursion {n : ℕ} (p : Prices (n+1)) (hsorted : Monotone p)
    (v : Valuations (n+1)) :
    payment p v = {v : Valuations (n+1) | p 0 ≤ v 0}.indicator (fun _ => p 0) v +
      {v : Valuations (n+1) | v 0 < p 0}.indicator
        (fun v => payment (p ∘ Fin.succ) (v ∘ Fin.succ)) v := by
  classical
  by_cases h : p 0 ≤ v 0
  · have hC : v ∈ {v : Valuations (n+1) | p 0 ≤ v 0} := h
    have hB : v ∉ {v : Valuations (n+1) | v 0 < p 0} := not_lt_of_ge h
    rw [Set.indicator_of_mem hC,Set.indicator_of_notMem hB,add_zero]
    have h0 : 0 ∈ affordable p v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
    have hn : (affordable p v).Nonempty := ⟨0,h0⟩
    rw [payment,dif_pos hn]
    exact le_antisymm (Finset.inf'_le _ h0) (Finset.le_inf' hn p (fun i _ => hsorted (Fin.zero_le i)))
  · have hC : v ∉ {v : Valuations (n+1) | p 0 ≤ v 0} := h
    have hB : v ∈ {v : Valuations (n+1) | v 0 < p 0} := lt_of_not_ge h
    rw [Set.indicator_of_notMem hC,Set.indicator_of_mem hB,zero_add]
    have himage : (affordable (p ∘ Fin.succ) (v ∘ Fin.succ)).image Fin.succ = affordable p v := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [affordable,h]
      · simp [affordable,Function.comp_apply]
    by_cases ht : (affordable (p ∘ Fin.succ) (v ∘ Fin.succ)).Nonempty
    · have ho : (affordable p v).Nonempty := by rw [← himage];exact ht.image Fin.succ
      rw [payment,dif_pos ho,payment,dif_pos ht]
      rw [Finset.inf'_comp_eq_image ht p]
      simp only [himage]
    · have ho : ¬ (affordable p v).Nonempty := by rw [← himage,Finset.image_nonempty];exact ht
      simp only [payment,dif_neg ho,dif_neg ht]

private def rejectTail {n : ℕ} (μ : JointLaw (n+1)) (a : ℝ) : JointLaw n :=
  Measure.map (fun v : Valuations (n+1) => fun i : Fin n => v i.succ)
    (ProbabilityTheory.cond μ {v : Valuations (n+1) | v 0 < a})

private lemma revenue_recursion {n : ℕ} (μ : JointLaw (n+1)) [IsProbabilityMeasure μ]
    (p : Prices (n+1)) (hsorted : Monotone p) :
    Revenue μ p = p 0 * μ.real {v : Valuations (n+1) | p 0 ≤ v 0} +
      μ.real {v : Valuations (n+1) | v 0 < p 0} *
        Revenue (rejectTail μ (p 0)) (p ∘ Fin.succ) := by
  let tail : Valuations (n+1) → Valuations n := fun v i => v i.succ
  let B : Set (Valuations (n+1)) := {v | v 0 < p 0}
  have htail : Measurable tail := measurable_pi_lambda _ (fun i => measurable_pi_apply i.succ)
  have hpt : Monotone (p ∘ Fin.succ) := hsorted.comp (fun i j hij => Fin.succ_le_succ_iff.mpr hij)
  have hm := payment_measurable (p ∘ Fin.succ) hpt
  have hB : MeasurableSet B := measurableSet_lt (measurable_pi_apply 0) measurable_const
  have hC : MeasurableSet {v : Valuations (n+1) | p 0 ≤ v 0} :=
    measurableSet_le measurable_const (measurable_pi_apply 0)
  have htailrev : μ.real B * Revenue (rejectTail μ (p 0)) (p ∘ Fin.succ) =
      ∫ v in B, payment (p ∘ Fin.succ) (tail v) ∂μ := by
    unfold Revenue rejectTail
    rw [integral_map_of_stronglyMeasurable htail hm.stronglyMeasurable]
    rw [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
    change μ.real B * ((μ.real B)⁻¹ * ∫ v in B, payment (p ∘ Fin.succ) (tail v) ∂μ) = _
    by_cases hz : μ B = 0
    · rw [Measure.real,hz,ENNReal.toReal_zero,zero_mul]
      rw [Measure.restrict_eq_zero.mpr hz,integral_zero_measure]
    · have hz' : μ.real B ≠ 0 := (ENNReal.toReal_ne_zero).mpr ⟨hz,measure_ne_top μ B⟩
      field_simp
  unfold Revenue
  simp_rw [payment_recursion p hsorted]
  rw [integral_add ((integrable_const _).indicator hC)]
  · rw [integral_indicator_const _ hC,integral_indicator hB,smul_eq_mul]
    change _ = p 0 * μ.real {v : Valuations (n+1) | p 0 ≤ v 0} + μ.real B * _
    unfold Revenue at htailrev
    rw [htailrev]
    simp only [tail,Function.comp_def]
    ring
  · exact ((payment_integrable (μ.map tail) (p ∘ Fin.succ) hpt).comp_measurable htail).indicator hB

private lemma payment_permute {n : ℕ} (p : Prices n)
    (σ : Equiv.Perm (Fin n)) (v : Valuations n) :
    payment (p ∘ σ) v = payment p (v ∘ σ.symm) := by
  classical
  have himage : (affordable (p ∘ σ) v).image σ = affordable p (v ∘ σ.symm) := by
    ext i
    simp only [Finset.mem_image, affordable, Finset.mem_filter, Finset.mem_univ,
      true_and, Function.comp_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩
      simpa using hj
    · intro hi
      exact ⟨σ.symm i, by simpa using hi, σ.apply_symm_apply i⟩
  by_cases h : (affordable (p ∘ σ) v).Nonempty
  · have hr : (affordable p (v ∘ σ.symm)).Nonempty := by
      rw [← himage]
      exact h.image σ
    rw [payment, dif_pos h, payment, dif_pos hr]
    rw [Finset.inf'_comp_eq_image h p]
    simp only [himage]
  · have hr : ¬ (affordable p (v ∘ σ.symm)).Nonempty := by
      rw [← himage, Finset.image_nonempty]
      exact h
    simp only [payment, dif_neg h, dif_neg hr]

private lemma exchangeable_revenue_permute {n : ℕ} (μ : JointLaw n)
    (hex : Exchangeable μ) (p : Prices n) (σ : Equiv.Perm (Fin n)) :
    Revenue μ (p ∘ σ) = Revenue μ p := by
  unfold Revenue
  simp_rw [payment_permute]
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ) μ μ := by
    refine ⟨(MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ).measurable, ?_⟩
    convert hex σ.symm using 1
    congr 1
    funext v i
    simp [permuteCoordinates,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft']
  convert hmp.integral_comp' (payment p) using 1
  congr 1
  funext v
  congr 1
  funext i
  simp [MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft']

private lemma twoTier_monotone (n : ℕ) (a b : ℝ) (hab : a ≤ b) :
    Monotone (twoTier n a b) := by
  intro i j hij
  by_cases hi : i = 0
  · subst i
    rw [twoTier_zero]
    by_cases hj : j = 0
    · subst j;exact le_rfl
    · rw [twoTier_ne_zero n a b j hj];exact hab
  · have hj : j ≠ 0 := by
      intro hj
      subst j
      exact hi (Fin.le_zero_iff.mp hij)
    rw [twoTier_ne_zero n a b i hi,twoTier_ne_zero n a b j hj]

private lemma twoTier_self (n : ℕ) (a : ℝ) : twoTier n a a = fun _ => a := by
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

private lemma sorted_policy (n : ℕ) (hn : 0 < n) (μ : JointLaw n)
    (hμ : ValidLaw μ) (hex : Exchangeable μ) (haff : Affiliated μ)
    (p : Prices n) (hp : FeasiblePrices p) (hsorted : Monotone p) :
    ∃ i : Fin n, Revenue μ p ≤ uniformRevenue μ (p i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    haveI : IsProbabilityMeasure μ := hμ.1
    cases n with
    | zero =>
      refine ⟨0,?_⟩
      have heq : (fun _ : Fin 1 => p 0) = p := by
        funext i
        simpa only [Fin.eq_zero i]
      rw [uniformRevenue,heq]
    | succ n =>
      let a := p 0
      let B : Set (Valuations (n+1+1)) := {v | v 0 < a}
      let ν := rejectTail μ a
      have hpt : Monotone (p ∘ Fin.succ) := hsorted.comp (fun i j hij => Fin.succ_le_succ_iff.mpr hij)
      have hR := revenue_recursion μ p hsorted
      change Revenue μ p = a * μ.real {v | a ≤ v 0} + μ.real B * Revenue ν (p ∘ Fin.succ) at hR
      by_cases hBzero : μ B = 0
      · have hreal : μ.real B = 0 := by simp [Measure.real,hBzero]
        have hU := revenue_recursion μ (twoTier (n+1) a a) (twoTier_monotone (n+1) a a le_rfl)
        change Revenue μ (twoTier (n+1) a a) = a * μ.real {v | a ≤ v 0} +
          μ.real B * uniformRevenue ν a at hU
        rw [twoTier_self] at hU
        simp only [hreal,zero_mul,add_zero] at hR hU
        exact ⟨0,le_of_eq (hR.trans hU.symm)⟩
      · have hBpos : 0 < μ B := lt_of_le_of_ne bot_le (Ne.symm hBzero)
        have hc : ValidLaw ν ∧ Exchangeable ν ∧ Affiliated ν :=
          affiliated_rejection_conditioning (n+1) μ hμ hex haff a hBpos
        obtain ⟨j,hj⟩ := ih (by omega) ν hc.1 hc.2.1 hc.2.2 (p ∘ Fin.succ)
          (fun i => hp i.succ) hpt
        let b := p j.succ
        have hab : a ≤ b := hsorted (Fin.zero_le _)
        have hT := revenue_recursion μ (twoTier (n+1) a b) (twoTier_monotone (n+1) a b hab)
        change Revenue μ (twoTier (n+1) a b) = a * μ.real {v | a ≤ v 0} +
          μ.real B * uniformRevenue ν b at hT
        have hred : Revenue μ p ≤ Revenue μ (twoTier (n+1) a b) := by
          rw [hR,hT]
          exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hj measureReal_nonneg)
        have hmax := hred.trans (twoTier_bound (n+1) μ hμ hex haff a b (hp 0) hab)
        rcases le_max_iff.mp hmax with h | h
        · exact ⟨0,h⟩
        · exact ⟨j.succ,h⟩

end MinBuyingAffiliatedProof

open MinBuyingAffiliatedProof

theorem solution (n : ℕ) (hn : 0 < n) (μ : JointLaw n)
    (hμ : ValidLaw μ) (hex : Exchangeable μ) (haff : Affiliated μ)
    (p : Prices n) (hp : FeasiblePrices p) :
    ∃ i : Fin n, Revenue μ p ≤ uniformRevenue μ (p i) := by
  let σ := Tuple.sort p
  have hq : FeasiblePrices (p ∘ σ) := fun i => hp (σ i)
  obtain ⟨i,hi⟩ := MinBuyingAffiliatedProof.sorted_policy n hn μ hμ hex haff (p ∘ σ) hq (Tuple.monotone_sort p)
  refine ⟨σ i,?_⟩
  have hperm := MinBuyingAffiliatedProof.exchangeable_revenue_permute μ hex p σ
  exact hperm ▸ hi

