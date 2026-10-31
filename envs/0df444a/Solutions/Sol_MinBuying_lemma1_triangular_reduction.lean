-- Prove2me | solution 1 for MinBuying.lemma1_triangular_reduction
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:38:13.282823+00:00
-- url     : https://prove2.me/submissions/ade81293-5be4-4519-91e4-657cec631680

import Theorems.Thm_MinBuying_regular_triangular_minorant
import Theorems.Thm_MinBuying_triangular_wellposed
import Theorems.Thm_MinBuying_triangular_law_specification
import Theorems.Thm_MinBuying_independent_revenue_formula

open MeasureTheory Set Filter MinBuying
open scoped BigOperators Topology
noncomputable section

private lemma rejection_mono (F : Measure ℝ) [IsProbabilityMeasure F] : Monotone (rejection F) :=
  fun a b h => ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iio_subset_Iio h))

private lemma rejection_zero (F : Measure ℝ) (hF : ValidMarginal F) : rejection F 0 = 0 := by
  have hz : F (Iio (0 : ℝ)) = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr (hF.2.mono (fun _ hx => not_lt_of_ge hx))
  simp [rejection, hz]

private lemma continuous_rejection (F : Measure ℝ) [IsProbabilityMeasure F]
    (hac : F ≪ volume) : Continuous (rejection F) := by
  haveI : NullSingletonClass F := ⟨fun x => hac (by simp)⟩
  have heq : rejection F = fun x => ProbabilityTheory.cdf F x := by
    funext x
    rw [ProbabilityTheory.cdf_eq_real]
    change (F (Iio x)).toReal = (F (Iic x)).toReal
    rw [measure_congr Iio_ae_eq_Iic]
  rw [heq]
  apply continuous_iff_continuousAt.mpr
  intro x
  let C := ProbabilityTheory.cdf F
  apply C.mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [C.rightLim_eq]
  have hz : ENNReal.ofReal (C x - Function.leftLim C x) = 0 := by
    rw [← C.measure_singleton, ProbabilityTheory.measure_cdf]
    simp
  have hle : C x ≤ Function.leftLim C x := sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hz)
  exact le_antisymm (C.mono.leftLim_le le_rfl) hle

private lemma exists_interior_rejection (F : Measure ℝ) (hF : ContinuousRegular F) :
    ∃ p : ℝ, 0 < p ∧ rejection F p ∈ Ioo (0 : ℝ) 1 := by
  letI : IsProbabilityMeasure F := hF.1.1
  haveI : NullSingletonClass F := ⟨fun x => hF.2.1 (by simp)⟩
  have heq : rejection F = fun x => ProbabilityTheory.cdf F x := by
    funext x
    rw [ProbabilityTheory.cdf_eq_real]
    change (F (Iio x)).toReal = (F (Iic x)).toReal
    rw [measure_congr Iio_ae_eq_Iic]
  have hlim : Tendsto (rejection F) atTop (𝓝 1) := by
    rw [heq]
    exact ProbabilityTheory.tendsto_cdf_atTop F
  have he : ∀ᶠ x : ℝ in atTop, 0 ≤ x ∧ (1/2 : ℝ) < rejection F x :=
    (eventually_ge_atTop 0).and (hlim.eventually (eventually_gt_nhds (by norm_num)))
  obtain ⟨b, hb0, hb⟩ := he.exists
  have hcont := (continuous_rejection F hF.2.1).continuousOn (s := Icc 0 b)
  obtain ⟨p, hp, hpv⟩ := intermediate_value_Icc hb0 hcont
    (show (1/2 : ℝ) ∈ Icc (rejection F 0) (rejection F b) by
      rw [rejection_zero F hF.1]
      exact ⟨by norm_num, hb.le⟩)
  refine ⟨p, ?_, ?_⟩
  · have hne : p ≠ 0 := by intro hz; simpa [hz, rejection_zero F hF.1] using hpv
    exact lt_of_le_of_ne hp.1 (Ne.symm hne)
  · rw [hpv]
    constructor <;> norm_num

private lemma replacement_item (F : Measure ℝ) (hF : ContinuousRegular F)
    (p : ℝ) (hp : 0 ≤ p) (hr : 0 < rejection F p) :
    ∃ a v : ℝ, 0 < a ∧ 0 < v ∧
      rejection (triangularLaw a v) p = rejection F p ∧
      ∀ t : ℝ, 0 ≤ t → rejection F t ≤ rejection (triangularLaw a v) t := by
  letI : IsProbabilityMeasure F := hF.1.1
  have hle : rejection F p ≤ 1 := measureReal_le_one
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hpp : 0 < p := by
      by_contra h
      have h0 : p = 0 := le_antisymm (le_of_not_gt h) hp
      simpa [h0, rejection_zero F hF.1] using hr
    obtain ⟨ha, he, hm⟩ := regular_triangular_minorant F hF.1 hF.2.2 p hpp ⟨hr,hlt⟩
    exact ⟨_, p, ha, hpp, he, hm⟩
  · obtain ⟨v, hv, hrv⟩ := exists_interior_rejection F hF
    obtain ⟨ha, _, hm⟩ := regular_triangular_minorant F hF.1 hF.2.2 v hv hrv
    let a := v * (1 - rejection F v) / rejection F v
    have hvp : v < p := by
      by_contra h
      have hh := rejection_mono F (le_of_not_gt h)
      rw [heq] at hh
      linarith [hrv.2]
    refine ⟨a,v,ha,hv,?_,hm⟩
    rw [(triangular_law_specification a v ha hv).2.2.1 p, heq]
    simp [triangularReject, not_le_of_gt (hv.trans hvp), not_le_of_gt hvp]

private lemma uniform_formula {n : ℕ} (hn : 0 < n) (F : Fin n → Measure ℝ)
    (hF : ∀ i, ValidMarginal (F i)) (q : ℝ) (hq : 0 ≤ q) :
    uniformRevenue (productLaw F) q = q * (1 - ∏ i, rejection (F i) q) :=
  (independent_revenue_formula n hn F hF (fun _ => 0) (fun _ => le_rfl) monotone_const).2 q hq

private lemma payment_measurable {n : ℕ} (p : Prices n) : Measurable (payment p) := by
  have ha : Measurable (affordable p) := by
    apply measurable_finset_iff.mpr
    intro i
    apply measurableSet_setOfPred.mp
    simpa [affordable] using
      (measurableSet_le measurable_const (measurable_pi_apply i) :
        MeasurableSet {v : Valuations n | p i ≤ v i})
  exact (measurable_of_countable
    (fun A : Finset (Fin n) => if h : A.Nonempty then A.inf' h p else 0)).comp ha

private lemma payment_integrable {n : ℕ} (μ : JointLaw n) [IsFiniteMeasure μ]
    (p : Prices n) (hp : FeasiblePrices p) : Integrable (payment p) μ := by
  apply Integrable.of_bound (payment_measurable p).aestronglyMeasurable (∑ i, p i)
  apply ae_of_all
  intro v
  have hsum : 0 ≤ ∑ i, p i := Finset.sum_nonneg (fun i _ => hp i)
  by_cases h : (affordable p v).Nonempty
  · have hl : 0 ≤ (affordable p v).inf' h p := Finset.le_inf' h p (fun i _ => hp i)
    obtain ⟨i, hi⟩ := h
    have hu := Finset.inf'_le p hi
    have hpi : p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
    rw [payment, dif_pos ⟨i,hi⟩, Real.norm_eq_abs, abs_of_nonneg hl]
    exact hu.trans hpi
  · simpa [payment,h] using hsum

private lemma certain_item_bound {n : ℕ} (F : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (F i)] (p : Prices n) (hp : FeasiblePrices p)
    (i : Fin n) (hi : rejection (F i) (p i) = 0) :
    Revenue (productLaw F) p ≤ p i := by
  have hz : F i (Iio (p i)) = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp hi).resolve_right (measure_ne_top _ _)
  have hzero : (productLaw F) {v : Valuations n | v i < p i} = 0 :=
    (measurePreserving_eval F i).preimage_null hz
  have hae : ∀ᵐ v ∂productLaw F, p i ≤ v i := by
    have h := measure_eq_zero_iff_ae_notMem.mp hzero
    exact h.mono (fun _ hv => le_of_not_gt hv)
  have hb : ∀ᵐ v ∂productLaw F, payment p v ≤ p i := by
    filter_upwards [hae] with v hv
    have hiA : i ∈ affordable p v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    rw [payment, dif_pos ⟨i,hiA⟩]
    exact Finset.inf'_le p hiA
  haveI : IsProbabilityMeasure (productLaw F) := inferInstanceAs (IsProbabilityMeasure (Measure.pi F))
  calc
    Revenue (productLaw F) p ≤ ∫ _, p i ∂productLaw F :=
      integral_mono_ae (payment_integrable _ p hp) (integrable_const _) hb
    _ = p i := by simp

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

private lemma revenue_permute {n : ℕ} (F : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (F i)] (p : Prices n) (σ : Equiv.Perm (Fin n)) :
    Revenue (productLaw (F ∘ σ)) (p ∘ σ) = Revenue (productLaw F) p := by
  unfold Revenue productLaw
  simp_rw [payment_permute]
  have hmp := measurePreserving_piCongrLeft F σ
  convert hmp.integral_comp' (payment p) using 1
  congr 1
  funext v
  congr 1
  funext i
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']

private lemma same_rejection_revenue {n : ℕ} (hn : 0 < n)
    (F G : Fin n → Measure ℝ) (hF : ∀ i, ValidMarginal (F i))
    (hG : ∀ i, ValidMarginal (G i)) (p : Prices n) (hp : FeasiblePrices p)
    (heq : ∀ i, rejection (G i) (p i) = rejection (F i) (p i)) :
    Revenue (productLaw G) p = Revenue (productLaw F) p := by
  classical
  letI (i : Fin n) : IsProbabilityMeasure (F i) := (hF i).1
  letI (i : Fin n) : IsProbabilityMeasure (G i) := (hG i).1
  let σ := Tuple.sort p
  rw [← revenue_permute F p σ, ← revenue_permute G p σ]
  rw [(independent_revenue_formula n hn (G ∘ σ) (fun i => hG (σ i))
      (p ∘ σ) (fun i => hp (σ i)) (Tuple.monotone_sort p)).1,
    (independent_revenue_formula n hn (F ∘ σ) (fun i => hF (σ i))
      (p ∘ σ) (fun i => hp (σ i)) (Tuple.monotone_sort p)).1]
  simp only [independentRevenueFormula, Function.comp_apply, heq]

private lemma up_le_dp {n : ℕ} (μ : JointLaw n) (hμ : WellPosed μ) :
    UPRevenue μ ≤ DPRevenue μ := by
  obtain ⟨q,hq,heq⟩ := hμ.2.2.2.1
  rw [← heq]
  exact le_csSup hμ.1 ⟨fun _ => q, fun _ => hq, rfl⟩

private lemma single_triangle (u : ℝ) (hu : 0 < u) :
    ∃ I : TriangularInstance 1, WellPosed (triangularJoint I) ∧
      u ≤ DPRevenue (triangularJoint I) ∧ UPRevenue (triangularJoint I) ≤ u := by
  let I : TriangularInstance 1 :=
    ⟨fun _ => 2*u, fun _ => 2*u, fun _ => by positivity, fun _ => by positivity⟩
  have hw := (triangular_wellposed 1 (by omega) I).2
  have hF : ∀ i, ValidMarginal (triangularMarginals I i) := fun i =>
    (triangular_law_specification (I.a i) (I.cap i) (I.a_pos i) (I.cap_pos i)).1
  have hf (q : ℝ) (hq : 0 ≤ q) :
      uniformRevenue (triangularJoint I) q = q * (1 - triangularReject (2*u) (2*u) q) := by
    rw [triangularJoint, uniform_formula (by omega) _ hF q hq]
    simp only [Fin.prod_univ_one, triangularMarginals]
    rw [(triangular_law_specification (I.a 0) (I.cap 0) (I.a_pos 0) (I.cap_pos 0)).2.2.1]
  have hcap : uniformRevenue (triangularJoint I) (2*u) = u := by
    rw [hf (2*u) (by positivity)]
    simp only [triangularReject, not_le_of_gt (by positivity : 0 < 2*u), ↓reduceIte,
      le_refl]
    field_simp
    <;> ring
  have hub (q : ℝ) (hq : 0 ≤ q) : uniformRevenue (triangularJoint I) q ≤ u := by
    rw [hf q hq]
    by_cases h0 : q ≤ 0
    · simp only [triangularReject, if_pos h0, sub_zero, mul_one]
      exact h0.trans hu.le
    · by_cases hc : q ≤ 2*u
      · simp only [triangularReject, if_neg h0, if_pos hc]
        have hd : 0 < q+2*u := by positivity
        have he : q * (1-q/(q+2*u)) = q*(2*u)/(q+2*u) := by field_simp; ring
        rw [he]
        apply (div_le_iff₀ hd).mpr
        nlinarith
      · simpa [triangularReject,h0,hc] using hu.le
  refine ⟨I,hw,?_,?_⟩
  · rw [← hcap]
    exact le_csSup hw.1 ⟨fun _ => 2*u, fun _ => by positivity, rfl⟩
  · obtain ⟨q,hq,he⟩ := hw.2.2.2.1
    rw [← he]
    exact hub q hq

theorem solution (n : ℕ) (F : Fin n → Measure ℝ)
    (hF : RegularInstance F) :
    ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ ∃ I : TriangularInstance m,
      WellPosed (triangularJoint I) ∧
      DPRevenue (productLaw F) ≤ DPRevenue (triangularJoint I) ∧
      UPRevenue (triangularJoint I) ≤ UPRevenue (productLaw F) := by
  classical
  obtain ⟨hn,hF,hW⟩ := hF
  letI (i : Fin n) : IsProbabilityMeasure (F i) := (hF i).1.1
  obtain ⟨p,hp,hopt⟩ := hW.2.2.1
  by_cases hz : ∃ i, rejection (F i) (p i) = 0
  · obtain ⟨i,hi⟩ := hz
    have hd : DPRevenue (productLaw F) ≤ p i := by
      rw [← hopt]
      exact certain_item_bound F p hp i hi
    have huni : uniformRevenue (productLaw F) (p i) = p i := by
      rw [uniform_formula hn F (fun j => (hF j).1) _ (hp i)]
      have hprod : ∏ j, rejection (F j) (p i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hi
      simp [hprod]
    have hpu : p i ≤ UPRevenue (productLaw F) := by
      rw [← huni]
      exact le_csSup hW.2.1 ⟨p i,hp i,rfl⟩
    have hpp : 0 < p i := hW.2.2.2.2.trans_le ((up_le_dp _ hW).trans hd)
    obtain ⟨I,hI,hdI,huI⟩ := single_triangle (p i) hpp
    exact ⟨1,by omega,by omega,I,hI,hd.trans hdI,huI.trans hpu⟩
  · have hr (i : Fin n) : 0 < rejection (F i) (p i) :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm (fun hi => hz ⟨i,hi⟩))
    choose a v ha hv he hm using fun i => replacement_item (F i) (hF i) (p i) (hp i) (hr i)
    let I : TriangularInstance n := ⟨a,v,ha,hv⟩
    have hWI := (triangular_wellposed n hn I).2
    have hGI : ∀ i, ValidMarginal (triangularMarginals I i) := fun i =>
      (triangular_law_specification (a i) (v i) (ha i) (hv i)).1
    have hrev : Revenue (triangularJoint I) p = DPRevenue (productLaw F) :=
      (same_rejection_revenue hn F (triangularMarginals I) (fun i => (hF i).1)
        hGI p hp he).trans hopt
    refine ⟨n,hn,le_rfl,I,hWI,?_,?_⟩
    · rw [← hrev]
      exact le_csSup hWI.1 ⟨p,hp,rfl⟩
    · obtain ⟨q,hq,hqopt⟩ := hWI.2.2.2.1
      have hub : uniformRevenue (triangularJoint I) q ≤ uniformRevenue (productLaw F) q := by
        rw [triangularJoint, uniform_formula hn _ hGI q hq,
          uniform_formula hn F (fun i => (hF i).1) q hq]
        apply mul_le_mul_of_nonneg_left _ hq
        apply sub_le_sub_left
        exact Finset.prod_le_prod (fun _ _ => ENNReal.toReal_nonneg) (fun i _ => hm i q hq)
      rw [← hqopt]
      exact hub.trans (le_csSup hW.2.1 ⟨q,hq,rfl⟩)

