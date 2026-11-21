-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_down_payoff_continuous_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T13:47:53.647974+00:00
-- url     : https://prove2.me/submissions/ba0a6438-ffae-4f58-b814-679cc8b3b619

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open Set Filter Topology MeasureTheory ProbabilityTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem lower_clock_eq_rational_iInf
    (f : ℝ≥0 → ℝ) (hright : ∀ t, ContinuousWithinAt f (Ici t) t) :
    tauMinus (fun s (_ : Unit) => f s) 0 () =
      ⨅ r : ℚ, if 0 < (r : ℝ).toNNReal ∧ f (r : ℝ).toNNReal < 0 then
        ((r : ℝ).toNNReal : ℝ≥0∞) else ⊤ := by
  let k : ℚ → ℝ≥0 := fun r => (r : ℝ).toNNReal
  let C : ℚ → ℝ≥0∞ := fun r => if 0 < k r ∧ f (k r) < 0 then k r else ⊤
  let S : Set ℝ≥0∞ := {y | ∃ u : ℝ≥0, 0 < u ∧ (u : ℝ≥0∞) = y ∧ f u < 0}
  change sInf S = ⨅ r, C r
  apply le_antisymm
  · apply le_iInf
    intro r
    by_cases h : 0 < k r ∧ f (k r) < 0
    · rw [show C r = (k r : ℝ≥0∞) from if_pos h]
      exact sInf_le ⟨k r, h.1, rfl, h.2⟩
    · simp [C, h]
  · apply le_sInf
    rintro _ ⟨u, hu, rfl, hfu⟩
    by_contra! hlt
    obtain ⟨w, huw, hw⟩ := exists_between hlt
    obtain ⟨v, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt (hw.trans_le le_top))
    obtain ⟨b, hub, hsub⟩ :=
      mem_nhdsGE_iff_exists_Ico_subset.mp ((hright u) (Iio_mem_nhds hfu))
    obtain ⟨r, hur, hrm⟩ := exists_rat_btwn
      (show (u : ℝ) < (min v b : ℝ≥0) by exact_mod_cast lt_min (WithTop.coe_lt_coe.mp huw) hub)
    have hcoe : (k r : ℝ) = (r : ℝ) := Real.coe_toNNReal _ (by linarith [u.coe_nonneg])
    have huk : u < k r := by exact_mod_cast (show (u : ℝ) < (k r : ℝ) by rwa [hcoe])
    have hkm : k r < min v b := by
      exact_mod_cast (show (k r : ℝ) < (min v b : ℝ≥0) by rwa [hcoe])
    have hneg : f (k r) < 0 := hsub ⟨huk.le, hkm.trans_le (min_le_right _ _)⟩
    have hkv : C r < (v : ℝ≥0∞) := by
      rw [show C r = (k r : ℝ≥0∞) from if_pos ⟨hu.trans huk, hneg⟩]
      exact WithTop.coe_lt_coe.mpr (hkm.trans_le (min_le_left _ _))
    exact (not_le_of_gt (hkv.trans hw)) (iInf_le C r)

private theorem downward_clock_aemeasurable
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (x : ℝ) :
    AEMeasurable (fun ω => (tauMinus (shifted D.X x) 0 ω : ℝ≥0∞)) P := by
  have hX (t : ℝ≥0) : AEMeasurable (D.X t) P := by
    have hi := (D.levy.stationary_increments 0 t).aemeasurable_snd
    change AEMeasurable (fun ω => D.X t ω - D.X 0 ω) P at hi
    simpa only [D.levy.start_zero, sub_zero] using hi
  let k : ℚ → ℝ≥0 := fun r => (r : ℝ).toNNReal
  have hparts (r : ℚ) : AEMeasurable (fun ω =>
      if 0 < k r ∧ x + D.X (k r) ω < 0 then (k r : ℝ≥0∞) else ⊤) P := by
    by_cases h : 0 < k r
    · simp only [h, true_and]
      have hg : Measurable (fun z : ℝ => if z < 0 then (k r : ℝ≥0∞) else ⊤) :=
        Measurable.ite (measurableSet_lt measurable_id measurable_const)
          measurable_const measurable_const
      exact hg.comp_aemeasurable (aemeasurable_const.add (hX (k r)))
    · simpa only [h, false_and, if_false] using
        (aemeasurable_const : AEMeasurable (fun _ : Ω => (⊤ : ℝ≥0∞)) P)
  refine (AEMeasurable.iInf hparts).congr ?_
  filter_upwards [D.levy.cadlag_ae] with ω hc
  exact (lower_clock_eq_rational_iInf (fun t => x + D.X t ω)
    (fun t => continuous_const.continuousWithinAt.add (hc t).1)).symm

private theorem discountedAt_norm_le_one (q : ℝ) (hq : 0 ≤ q) (t : WithTop ℝ≥0) :
    ‖discountedAt q t‖ ≤ 1 := by
  induction t using WithTop.recTopCoe with
  | top => simp [discountedAt]
  | coe s =>
    change ‖Real.exp (-q * (s : ℝ))‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) s.coe_nonneg

private theorem discountedAt_continuous_in_discount (t : WithTop ℝ≥0) :
    Continuous (fun q : ℝ => discountedAt q t) := by
  induction t using WithTop.recTopCoe with
  | top => simpa only [discountedAt] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  | coe s =>
    change Continuous (fun q : ℝ => Real.exp (-q * (s : ℝ)))
    exact Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)

private theorem discountedAt_measurable (q : ℝ) :
    Measurable (fun t : ℝ≥0∞ => discountedAt q t) := by
  have heq : (fun t : ℝ≥0∞ => discountedAt q t) =
      fun t => if t = ⊤ then 0 else Real.exp (-q * t.toReal) := by
    funext t
    induction t using WithTop.recTopCoe with
    | top => exact (if_pos rfl).symm
    | coe s => simp [discountedAt]
  rw [heq]
  exact Measurable.ite (measurableSet_singleton (⊤ : ℝ≥0∞)) measurable_const
    (Real.continuous_exp.measurable.comp (measurable_const.mul ENNReal.measurable_toReal))

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (x : ℝ) :
    Tendsto (fun q : ℝ => downExpectation P D.X q x)
      (nhdsWithin 0 (Ioi 0)) (nhds (downExpectation P D.X 0 x)) := by
  let τ : Ω → ℝ≥0∞ := tauMinus (shifted D.X x) 0
  have hτ := downward_clock_aemeasurable Ω P D x
  unfold downExpectation
  refine tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    (Filter.Eventually.of_forall fun q => ((discountedAt_measurable q).comp_aemeasurable hτ).aestronglyMeasurable)
    ?_ (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact Filter.Eventually.of_forall fun ω => discountedAt_norm_le_one q hq.le (τ ω)
  · exact Filter.Eventually.of_forall fun ω =>
      (discountedAt_continuous_in_discount (τ ω)).continuousWithinAt
