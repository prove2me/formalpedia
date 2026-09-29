-- Prove2me | solution 1 for ModularCurve.constantsAreBase_modularFunctionFieldBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f6d4404c-571c-5b84-bdf8-54169a0f7e47

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin_pair
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_constantsAreBase_modularFunctionFieldBar
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

open IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasPrincipalDivisors ConstantsAreBase constantsAreBase_of_deg_eq_one"
p2m_open "AlgebraicCurve~IsCurveOver"

namespace RCAB

open ModularCurve

private theorem constantsAreBase_of_mem (K : Type*) [Field K] (E : IntermediateField K (LaurentSeries K))
    [HasPrincipalDivisors K E] {j : LaurentSeries K} (hjE : j ∈ E) (hj : j.order = -1) :
    ConstantsAreBase K E :=
  have h : ∃ x : E, (qSeriesBar K E x).order = -1 := ⟨⟨j, hjE⟩, hj⟩
  constantsAreBase_of_deg_eq_one (qInftyPlaceBar K E h) (deg_qInftyPlaceBar K h)

private theorem constantsAreBase_laurentBaseChange (L : Type*) [Field L] {instQL : Algebra ℚ L}
    (N : ℕ) [NeZero N] : ConstantsAreBase L (laurentBaseChange L (modularFunctionFieldFull N)) := by
  haveI := hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional L N
  have hmem : jqModC L ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
    rw [laurentBaseChange_adjoin_pair L N (functionFieldGeneration N)]
    exact jqModC_mem L N
  exact constantsAreBase_of_mem L _ hmem (order_jqModC L)

end RCAB

end AlgebraicCurve

end

p2m_open "ModularCurve AlgebraicCurve~IsCurveOver P2MW.S_ModularCurve_constantsAreBase_modularFunctionFieldBar.AlgebraicCurve"

theorem solution (N : ℕ) [NeZero N] :
    ConstantsAreBase (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  AlgebraicCurve.RCAB.constantsAreBase_laurentBaseChange (AlgebraicClosure ℚ) N

example : ∀ (N : ℕ) [NeZero N], ConstantsAreBase (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := @solution

#print axioms solution

end S_ModularCurve_constantsAreBase_modularFunctionFieldBar
end P2MW
export P2MW.S_ModularCurve_constantsAreBase_modularFunctionFieldBar (solution)
