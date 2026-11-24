-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_exit_payoff_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:05:54.328887+00:00
-- url     : https://prove2.me/submissions/3c6d2a18-cc6f-44eb-af80-189811225253

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_measurable_ruin_path_reward
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_strict_exit_clocks_aemeasurable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
/-- The two strict exits cannot both contribute to the payoff. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      0 ≤ downBeforeUpExpectation P D.X q x a ∧
      upBeforeDownExpectation P D.X q x a + downBeforeUpExpectation P D.X q x a ≤ 1 := by
  intro Ω mΩ P hP D ψ W hψ hW q x a hq ha hx hxa
  obtain ⟨hm, hb, _⟩ := source_result81_measurable_ruin_path_reward q a hq
  let u := fun ω => tauPlus (shifted D.X x) a ω
  let v := fun ω => tauMinus (shifted D.X x) 0 ω
  let f := fun ω => if u ω < v ω then discountedAt q (u ω) else 0
  let g := fun ω => if v ω < u ω then discountedAt q (v ω) else 0
  have hf (ω : Ω) : 0 ≤ f ω ∧ f ω ≤ 1 := by
    dsimp [f]
    split
    · exact hb _
    · norm_num
  have hg (ω : Ω) : 0 ≤ g ω ∧ g ω ≤ 1 := by
    dsimp [g]
    split
    · exact hb _
    · norm_num
  have hfg (ω : Ω) : f ω + g ω ≤ 1 := by
    by_cases h : u ω < v ω
    · simp [f, g, h, not_lt_of_ge h.le, (hb (u ω)).2]
    · by_cases h' : v ω < u ω
      · simp [f, g, h, h', (hb (v ω)).2]
      · simp [f, g, h, h']
  obtain ⟨hu, hv⟩ := source_result81_strict_exit_clocks_aemeasurable Ω P D x a
  have hfun : Measurable (fun z : ℝ≥0∞ × ℝ≥0∞ =>
      if z.1 < z.2 then discountedAt q z.1 else 0) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      (hm.comp measurable_fst) measurable_const
  have hfm : AEMeasurable f P := hfun.comp_aemeasurable (hu.prodMk hv)
  have hgm : AEMeasurable g P := hfun.comp_aemeasurable (hv.prodMk hu)
  have hfi : Integrable f P := (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs, abs_of_nonneg (hf ω).1] using (hf ω).2)
  have hgi : Integrable g P := (integrable_const (1 : ℝ)).mono' hgm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs, abs_of_nonneg (hg ω).1] using (hg ω).2)
  change 0 ≤ ∫ ω, g ω ∂P ∧ (∫ ω, f ω ∂P) + (∫ ω, g ω ∂P) ≤ 1
  refine ⟨integral_nonneg (fun ω => (hg ω).1), ?_⟩
  rw [← integral_add hfi hgi]
  simpa using integral_mono (hfi.add hgi) (integrable_const (1 : ℝ)) hfg
