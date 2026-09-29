-- Prove2me | solution 1 for ModularCurve.degeneracyPushforwardInputs
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a1c3c1f9-c18c-5984-92c4-79a5d58e680f

import Mathlib
import Definitions.Def_ModularCurve_ToricDescentData
import Theorems.Thm_ModularCurve_heckeAlphaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_heckeBetaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_prime
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_degeneracyPushforwardInputs
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

theorem solution (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) :
    ModularCurve.DegeneracyPushforwardInputs N q := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharZero (AlgebraicClosure ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  haveI : AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ)
      (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.modularFunctionFieldFull (N * q))) :=
    ModularCurve.hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional
      (AlgebraicClosure ℚ) (N * q)
  exact ModularCurve.degeneracyPushforwardInputs_intro
    (ModularCurve.heckeAlphaBarIntegral_of_prime (AlgebraicClosure ℚ) N q)
    (ModularCurve.heckeBetaBarIntegral_of_prime (AlgebraicClosure ℚ) N q)
    (ModularCurve.finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) N q)
    (AlgebraicCurve.normFormulaAlong (ModularCurve.heckeAlphaBar (AlgebraicClosure ℚ) N q)
      (ModularCurve.finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) N q)
      (AlgebraicCurve.separableAlong_of_charZero (ModularCurve.heckeAlphaBar (AlgebraicClosure ℚ) N q)
        (ModularCurve.heckeAlphaBarIntegral_of_prime (AlgebraicClosure ℚ) N q)))
    (ModularCurve.finiteAlong_heckeBetaBar_of_prime (AlgebraicClosure ℚ) N q)
    (AlgebraicCurve.normFormulaAlong (ModularCurve.heckeBetaBar (AlgebraicClosure ℚ) N q)
      (ModularCurve.finiteAlong_heckeBetaBar_of_prime (AlgebraicClosure ℚ) N q)
      (AlgebraicCurve.separableAlong_of_charZero (ModularCurve.heckeBetaBar (AlgebraicClosure ℚ) N q)
        (ModularCurve.heckeBetaBarIntegral_of_prime (AlgebraicClosure ℚ) N q)))

end S_ModularCurve_degeneracyPushforwardInputs
end P2MW
export P2MW.S_ModularCurve_degeneracyPushforwardInputs (solution)
