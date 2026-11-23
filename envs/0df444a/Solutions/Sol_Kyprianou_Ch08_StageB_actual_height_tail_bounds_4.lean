-- Prove2me | solution 4 for Kyprianou.Ch08.StageB.actual_height_tail_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T03:19:55.636718+00:00
-- url     : https://prove2.me/submissions/12ee8111-a56a-46a1-bc12-0e2f990b7fa5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_integral_core_left_continuous
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ h : ℝ, 0 < h →
      0 < (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) ∧
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) ≤ 1 := by
  intro h hh
  obtain ⟨hpos, hmono, _hcont, hlim, _hleft⟩ :=
    Kyprianou.Ch08.StageB.actual_height_tail_integral_core_left_continuous
      P D ψ W hψ hW q hq
  refine ⟨hpos h hh, ?_⟩
  have hbound : ∀ᶠ x : ℝ in (Filter.atTop : Filter ℝ),
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) ≤
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 x ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) := by
    filter_upwards [Filter.eventually_gt_atTop h, Filter.eventually_gt_atTop 0] with x hxh hx0
    exact hmono (Set.mem_Ioi.mpr hh) (Set.mem_Ioi.mpr hx0) (le_of_lt hxh)
  exact ge_of_tendsto hlim hbound
