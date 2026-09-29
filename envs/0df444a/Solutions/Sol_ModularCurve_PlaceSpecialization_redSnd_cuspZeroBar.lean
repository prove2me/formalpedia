-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.redSnd_cuspZeroBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/90b5edbe-7d7e-58bd-b63a-2da15f8bbb9d

import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_redSnd_cuspZeroBar
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace ModularCurve p2m_export "ModularCurve" "PlaceSpecialization.redFst PlaceSpecialization.redSnd ModularPolynomialData PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence charLGeomPlaceEquiv cuspZeroBar cuspZeroBar_def restrictAlong_heckeBetaBar_frickeInvolutionBar_smul PlaceSpecialization.redFst_cuspInftyBar" namespace PlaceSpecialization p2m_export "ModularCurve.PlaceSpecialization" "redFst redSnd redFst_cuspInftyBar" end ModularCurve.PlaceSpecialization
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization" in
open AlgebraicCurve _root_.ModularCurve in
theorem ModularCurve.PlaceSpecialization.redSnd_cuspZeroBar'
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq (RatFunc k)] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    P.redSnd (cuspZeroBar (1 * q)) = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k) := by
  rw [← ModularCurve.PlaceSpecialization.redFst_cuspInftyBar P, PlaceSpecialization.redSnd, PlaceSpecialization.redFst,
    cuspZeroBar_def, ModularCurve.restrictAlong_heckeBetaBar_frickeInvolutionBar_smul q hα hβ]

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_redSnd_cuspZeroBar.ModularCurve in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq (RatFunc k)] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    P.redSnd (cuspZeroBar (1 * q)) = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k) :=
  ModularCurve.PlaceSpecialization.redSnd_cuspZeroBar' P

end S_ModularCurve_PlaceSpecialization_redSnd_cuspZeroBar
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_redSnd_cuspZeroBar (solution)
