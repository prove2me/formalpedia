-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.actualHeightUnrestrictedUpcrossingNormalisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:29:31.994715+00:00
-- url     : https://prove2.me/submissions/d1b26dd8-1f20-45d2-a17b-800dc45225ad

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_kyprianou82_actualHeight_pos_raw
import Theorems.Thm_kyprianou82_actualHeight_zero_raw
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
    (∫ ω, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) = 1 := by
  have hraw :
      (∫ ω, discountedAt q (tauPlus D.X 1 ω) ∂P) =
        Real.exp (-(Phi ψ q * 1)) := by
    by_cases hz : q = 0
    · subst q
      exact kyprianou82_actualHeight_zero_raw P D ψ W hψ hW
    · exact kyprianou82_actualHeight_pos_raw P D ψ W hψ hW q
        (lt_of_le_of_ne hq (Ne.symm hz))
  rw [integral_const_mul, hraw, ← Real.exp_add]
  simp
