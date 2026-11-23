-- Prove2me | solution 5 for Kyprianou.Ch08.StageB.actual_height_tail_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:04:54.783621+00:00
-- url     : https://prove2.me/submissions/a90c1212-3329-464d-a36f-4937c5dd8fce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_positivity_independent
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_unit_cap_independent
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
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) ≤ 1  := by
  intro h hh
  exact ⟨
    Kyprianou.Ch08.StageB.actual_height_tail_positivity_independent
      P D ψ W hψ hW q hq h hh,
    Kyprianou.Ch08.StageB.actual_height_tail_unit_cap_independent
      P D ψ W hψ hW q hq h hh⟩
