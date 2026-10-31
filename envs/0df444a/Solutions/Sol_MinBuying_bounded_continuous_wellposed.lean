-- Prove2me | solution 1 for MinBuying.bounded_continuous_wellposed
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:51:58.271573+00:00
-- url     : https://prove2.me/submissions/082139a4-c59f-4785-ad06-c5e5c10978e7

import Theorems.Thm_MinBuying_independent_revenue_formula

open MeasureTheory Set Filter MinBuying
open scoped BigOperators Topology
noncomputable section

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

private lemma exists_interior_rejection (F : Measure ℝ) (hF : ValidMarginal F) (hac : F ≪ volume) :
    ∃ p : ℝ, 0 < p ∧ rejection F p ∈ Ioo (0 : ℝ) 1 := by
  letI : IsProbabilityMeasure F := hF.1
  haveI : NullSingletonClass F := ⟨fun x => hac (by simp)⟩
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
  have hcont := (continuous_rejection F hac).continuousOn (s := Icc 0 b)
  obtain ⟨p, hp, hpv⟩ := intermediate_value_Icc hb0 hcont
    (show (1/2 : ℝ) ∈ Icc (rejection F 0) (rejection F b) by
      rw [rejection_zero F hF]
      exact ⟨by norm_num, hb.le⟩)
  refine ⟨p, ?_, ?_⟩
  · have hne : p ≠ 0 := by intro hz; simpa [hz, rejection_zero F hF] using hpv
    exact lt_of_le_of_ne hp.1 (Ne.symm hne)
  · rw [hpv]
    constructor <;> norm_num

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

private lemma payment_continuousAt {n : ℕ} (p : Prices n) (v : Valuations n)
    (hneq : ∀ i, p i ≠ v i) : ContinuousAt (fun q : Prices n => payment q v) p := by
  classical
  have heach (i : Fin n) : ∀ᶠ q : Prices n in 𝓝 p, (q i ≤ v i ↔ p i ≤ v i) := by
    rcases lt_or_gt_of_ne (hneq i) with hi | hi
    · filter_upwards [((continuous_apply i).continuousAt).eventually (eventually_lt_nhds hi)] with q hq
      exact iff_of_true hq.le hi.le
    · filter_upwards [((continuous_apply i).continuousAt).eventually (eventually_gt_nhds hi)] with q hq
      exact iff_of_false (not_le_of_gt hq) (not_le_of_gt hi)
  have hnear : ∀ᶠ q : Prices n in 𝓝 p, affordable q v = affordable p v := by
    filter_upwards [Filter.eventually_all.mpr heach] with q hq
    ext i
    simp [affordable, hq]
  let f : Prices n → ℝ := fun q =>
    if h : (affordable p v).Nonempty then (affordable p v).inf' h q else 0
  have hc : ContinuousAt f p := by
    dsimp [f]
    split_ifs with h
    · exact ContinuousAt.finset_inf'_apply h (fun i _ => (continuous_apply i).continuousAt)
    · exact continuousAt_const
  apply hc.congr_of_eventuallyEq
  filter_upwards [hnear] with q hq
  simp [payment,hq,f]

private lemma payment_cube_bound {n : ℕ} (B : ℝ) (hB : 0 ≤ B) (p : Prices n)
    (hp : p ∈ Icc (fun _ => 0) (fun _ => B)) (v : Valuations n) : ‖payment p v‖ ≤ B := by
  by_cases h : (affordable p v).Nonempty
  · have hl : 0 ≤ (affordable p v).inf' h p := Finset.le_inf' h p (fun i _ => hp.1 i)
    obtain ⟨i,hi⟩ := h
    rw [payment,dif_pos ⟨i,hi⟩,Real.norm_eq_abs,abs_of_nonneg hl]
    exact (Finset.inf'_le p hi).trans (hp.2 i)
  · simpa [payment,h] using hB

private lemma revenue_continuousOn_cube {n : ℕ} (F : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (F i)] (hac : ∀ i, F i ≪ volume)
    (B : ℝ) (hB : 0 ≤ B) :
    ContinuousOn (Revenue (productLaw F)) (Icc (fun _ => 0) (fun _ => B)) := by
  letI : IsProbabilityMeasure (productLaw F) := inferInstanceAs (IsProbabilityMeasure (Measure.pi F))
  intro p hp
  apply continuousWithinAt_of_dominated (bound := fun _ => B)
  · exact Eventually.of_forall (fun q => (payment_measurable q).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact ae_of_all _ (fun v => payment_cube_bound B hB q hq v)
  · exact integrable_const B
  · have heach (i : Fin n) : ∀ᵐ x ∂F i, p i ≠ x := by
      have hz : (F i) {p i} = 0 := hac i (by simp)
      exact (measure_eq_zero_iff_ae_notMem.mp hz).mono (fun x hx h =>
        hx (mem_singleton_iff.mpr h.symm))
    have hall : ∀ᵐ v ∂productLaw F, ∀ i, p i ≠ v i := by
      rw [ae_all_iff]
      intro i
      exact Measure.tendsto_eval_ae_ae (heach i)
    filter_upwards [hall] with v hv
    exact (payment_continuousAt p v hv).continuousWithinAt

private lemma payment_clip {n : ℕ} (p : Prices n) (B : ℝ) (v : Valuations n)
    (hv : ∀ i, v i < B) : payment (fun i => min (p i) B) v = payment p v := by
  have ha (i : Fin n) : min (p i) B ≤ v i ↔ p i ≤ v i := by
    simp [min_le_iff, not_le_of_gt (hv i)]
  have hA : affordable (fun i => min (p i) B) v = affordable p v := by
    ext i
    simp [affordable,ha]
  unfold payment
  rw [hA]
  split_ifs with h
  · apply Finset.inf'_congr h rfl
    intro i hi
    exact min_eq_left ((Finset.mem_filter.mp hi).2.trans (hv i).le)
  · rfl

private lemma uniform_positive {n : ℕ} (hn : 0 < n) (F : Fin n → Measure ℝ)
    (hF : ∀ i, ValidMarginal (F i)) (hac : ∀ i, F i ≪ volume) :
    ∃ p : ℝ, 0 ≤ p ∧ 0 < uniformRevenue (productLaw F) p := by
  classical
  letI (i : Fin n) : IsProbabilityMeasure (F i) := (hF i).1
  let i : Fin n := ⟨0,hn⟩
  obtain ⟨p,hp,hr⟩ := exists_interior_rejection (F i) (hF i) (hac i)
  refine ⟨p,hp.le,?_⟩
  rw [(independent_revenue_formula n hn F hF (fun _ => 0)
    (fun _ => le_rfl) monotone_const).2 p hp.le]
  apply mul_pos hp
  apply sub_pos.mpr
  have hrest : ∏ j ∈ Finset.univ.erase i, rejection (F j) p ≤ 1 :=
    Finset.prod_le_one (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => measureReal_le_one)
  rw [← Finset.mul_prod_erase Finset.univ (fun j => rejection (F j) p) (Finset.mem_univ i)]
  calc
    rejection (F i) p * ∏ j ∈ Finset.univ.erase i, rejection (F j) p
        ≤ rejection (F i) p := by
      have hnn : 0 ≤ rejection (F i) p := ENNReal.toReal_nonneg
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hrest hnn
    _ < 1 := hr.2

theorem solution (n : ℕ) (hn : 0 < n) (F : Fin n → Measure ℝ)
    (hF : ∀ i, ValidMarginal (F i)) (hac : ∀ i, F i ≪ volume)
    (M : ℝ) (hM : ∀ i, ∀ᵐ x ∂F i, x ≤ M) : WellPosed (productLaw F) := by
  classical
  letI (i : Fin n) : IsProbabilityMeasure (F i) := (hF i).1
  letI : IsProbabilityMeasure (productLaw F) := inferInstanceAs (IsProbabilityMeasure (Measure.pi F))
  let B := max M 0 + 1
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right M 0]
  have hMB : M < B := by dsimp [B]; linarith [le_max_left M 0]
  let K : Set (Prices n) := Icc (fun _ => 0) (fun _ => B)
  have hKs : K.Nonempty := ⟨fun _ => 0,fun _ => le_rfl,fun _ => hB.le⟩
  have hKc : IsCompact K := isCompact_Icc
  have hcont : ContinuousOn (Revenue (productLaw F)) K := revenue_continuousOn_cube F hac B hB.le
  have hsupport : ∀ᵐ v ∂productLaw F, ∀ i, v i < B := by
    rw [ae_all_iff]
    intro i
    exact Measure.tendsto_eval_ae_ae ((hM i).mono (fun _ hx => hx.trans_lt hMB))
  have hclip (p : Prices n) :
      Revenue (productLaw F) (fun i => min (p i) B) = Revenue (productLaw F) p := by
    apply integral_congr_ae
    filter_upwards [hsupport] with v hv
    exact payment_clip p B v hv
  have hclipK (p : Prices n) (hp : FeasiblePrices p) : (fun i => min (p i) B) ∈ K :=
    ⟨fun i => le_min (hp i) hB.le,fun i => min_le_right _ _⟩
  obtain ⟨p,hp,hmax⟩ := hKc.exists_isMaxOn hKs hcont
  have hDP : ∀ r ∈ differentiatedValues (productLaw F), r ≤ Revenue (productLaw F) p := by
    rintro r ⟨q,hq,rfl⟩
    rw [← hclip q]
    exact hmax (hclipK q hq)
  have hDPmem : Revenue (productLaw F) p ∈ differentiatedValues (productLaw F) :=
    ⟨p,hp.1,rfl⟩
  have hDPbdd : BddAbove (differentiatedValues (productLaw F)) := ⟨_,hDP⟩
  have hDPopt : Revenue (productLaw F) p = DPRevenue (productLaw F) :=
    le_antisymm (le_csSup hDPbdd hDPmem) (csSup_le ⟨_,hDPmem⟩ hDP)
  have huc : ContinuousOn (uniformRevenue (productLaw F)) (Icc 0 B) := by
    apply hcont.comp (continuous_pi (fun _ : Fin n => continuous_id)).continuousOn
    intro q hq
    exact ⟨fun _ => hq.1,fun _ => hq.2⟩
  obtain ⟨q,hq,hqmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hB.le) huc
  have hUP : ∀ r ∈ uniformValues (productLaw F), r ≤ uniformRevenue (productLaw F) q := by
    rintro r ⟨s,hs,rfl⟩
    change Revenue (productLaw F) (fun _ => s) ≤ _
    rw [← hclip (fun _ => s)]
    exact hqmax ⟨le_min hs hB.le,min_le_right _ _⟩
  have hUPmem : uniformRevenue (productLaw F) q ∈ uniformValues (productLaw F) :=
    ⟨q,hq.1,rfl⟩
  have hUPbdd : BddAbove (uniformValues (productLaw F)) := ⟨_,hUP⟩
  have hUPopt : uniformRevenue (productLaw F) q = UPRevenue (productLaw F) :=
    le_antisymm (le_csSup hUPbdd hUPmem) (csSup_le ⟨_,hUPmem⟩ hUP)
  refine ⟨hDPbdd,hUPbdd,⟨p,hp.1,hDPopt⟩,⟨q,hq.1,hUPopt⟩,?_⟩
  obtain ⟨s,hs,hpos⟩ := uniform_positive hn F hF hac
  exact hpos.trans_le (le_csSup hUPbdd ⟨s,hs,rfl⟩)

