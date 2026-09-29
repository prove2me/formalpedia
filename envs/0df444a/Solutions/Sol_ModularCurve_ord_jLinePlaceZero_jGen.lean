-- Prove2me | solution 1 for ModularCurve.ord_jLinePlaceZero_jGen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/fbf818ba-15bc-5b9a-a4e6-d195725c76f8

import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_X_sub_C
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeOfPoint_ne_placeInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_jLinePlaceZero_jGen
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial
attribute [local instance] ModularCurve.instDecidableEqRatFuncRat

namespace ModularCurve
p2m_export "ModularCurve" "jLineRingEquiv jLineRingEquiv_X instDecidableEqRatFuncRat jLinePlaceZero jq jGen"
namespace JLineOrdAux
p2m_open "ModularCurve"

theorem equiv_X_sub_C (b : ℚ) :
    ModularCurve.jLineRingEquiv (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - Polynomial.C b))
      = ModularCurve.jGen - algebraMap ℚ ↥ℚ⟮ModularCurve.jq⟯ b := by
  rw [map_sub, RatFunc.algebraMap_X, map_sub, ModularCurve.jLineRingEquiv_X, RatFunc.algebraMap_C]
  congr 1
  exact RingHom.map_rat_algebraMap ModularCurve.jLineRingEquiv.toRingHom b

theorem exists_eq_congr (v : Place ℚ ↥ℚ⟮ModularCurve.jq⟯) :
    ∃ v' : Place ℚ (RatFunc ℚ), v = Place.congrRingEquiv ModularCurve.jLineRingEquiv
      (RingHom.map_rat_algebraMap ModularCurve.jLineRingEquiv.toRingHom) v' :=
  ⟨(Place.congrEquiv ModularCurve.jLineRingEquiv
      (RingHom.map_rat_algebraMap ModularCurve.jLineRingEquiv.toRingHom)).symm v,
    ((Place.congrEquiv _ _).apply_symm_apply v).symm⟩

theorem ord_congr_jGen_sub (b : ℚ) (v' : Place ℚ (RatFunc ℚ)) :
    (Place.congrRingEquiv ModularCurve.jLineRingEquiv
        (RingHom.map_rat_algebraMap ModularCurve.jLineRingEquiv.toRingHom) v').ord
      (ModularCurve.jGen - algebraMap ℚ ↥ℚ⟮ModularCurve.jq⟯ b)
    = (Finsupp.single (placeOfPoint ℚ b) (1 : ℤ) + Finsupp.single (placeInfty ℚ) (-1 : ℤ)) v' := by
  rw [← equiv_X_sub_C, Place.ord_congrRingEquiv]
  exact ord_X_sub_C ℚ b v'

theorem injective_congr : Function.Injective (Place.congrRingEquiv ModularCurve.jLineRingEquiv
      (RingHom.map_rat_algebraMap ModularCurve.jLineRingEquiv.toRingHom) : Place ℚ (RatFunc ℚ) → _) :=
  (Place.congrEquiv ModularCurve.jLineRingEquiv
      (RingHom.map_rat_algebraMap ModularCurve.jLineRingEquiv.toRingHom)).injective

end ModularCurve.JLineOrdAux

open ModularCurve.JLineOrdAux

theorem solution : ModularCurve.jLinePlaceZero.ord ModularCurve.jGen = 1 := by
  have h := ord_congr_jGen_sub 0 (placeOfPoint ℚ 0)
  rw [map_zero, sub_zero] at h
  have h01 := placeOfPoint_ne_placeInfty ℚ 0
  unfold ModularCurve.jLinePlaceZero
  rw [h]
  simp [Finsupp.single_apply, h01, h01.symm]

end S_ModularCurve_ord_jLinePlaceZero_jGen
end P2MW
export P2MW.S_ModularCurve_ord_jLinePlaceZero_jGen (solution)
