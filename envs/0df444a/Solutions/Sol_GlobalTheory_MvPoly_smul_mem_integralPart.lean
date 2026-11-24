-- Prove2me | solution 1 for GlobalTheory.MvPoly.smul_mem_integralPart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:21.164732+00:00
-- url     : https://prove2.me/submissions/aeddb53b-c5a2-436b-b086-ad4379669092

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsReducedBasisIntegralPartOfLinearIndependen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MvPolynomial NumberField
open GlobalTheory
open GlobalTheory.MvPoly
variable {K σ : Type*} [Field K]
namespace GlobalTheory.MvPoly
theorem _root_.solution {W : Submodule K (MvPolynomial σ K)} (c : 𝓞 K)
    {P : MvPolynomial σ K} (hP : P ∈ integralPart W) : c • P ∈ integralPart W :=
  ⟨W.smul_mem (c : K) hP.1, fun α => by
    change IsIntegral ℤ (coeff α ((c : K) • P))
    rw [coeff_smul, smul_eq_mul]
    exact c.isIntegral_coe.mul (hP.2 α)⟩
end GlobalTheory.MvPoly
