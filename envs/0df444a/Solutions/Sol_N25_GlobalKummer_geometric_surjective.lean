-- Prove2me | solution 1 for N25.GlobalKummer.geometric_surjective
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:41.639111+00:00
-- url     : https://prove2.me/submissions/414b3d64-2b1a-4581-902a-11a398d967d3

import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Definitions.Def_N25_LocalKummerPolynomial
import Definitions.Def_N25_KummerFactorization
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange

noncomputable section

namespace N25.GlobalKummer

/-- The selected polynomial operator is onto the geometric Jacobian. -/
theorem _root_.solution (hPhi : PhiFiveZero) : Function.Surjective piEnd := by
  intro x
  have hcurve : AlgebraicCurve.IsCurveOver (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25) := (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
    (AlgebraicClosure ℚ) 25 H25).1
  letI : (CohCarrier.GammaH 25 H25).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH 25 H25)
  have hfg := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CohCarrier.GammaH 25 H25)
    (ModularCurve.translation_mem_GammaH 25 H25)
  obtain ⟨y, hy⟩ := @AlgebraicCurve.Pic0.exists_nsmul_eq
    (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar 25 H25)
    inferInstance inferInstance inferInstance inferInstance inferInstance hfg hcurve 71 (by decide) x
  refine ⟨rhoEnd y, ?_⟩
  have h := congrArg (fun f : J →+ J => f y) (piEnd_comp_rhoEnd hPhi)
  exact h.trans hy

end N25.GlobalKummer
