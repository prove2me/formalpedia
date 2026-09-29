-- Prove2me | solution 1 for ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/44203b79-0f70-5eac-a423-ad01239c8b8f

import Definitions.Def_ModularCurve_SpecializeModuli
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem solution
    (k : Type*) [Field k] [DecidableEq k] (a c : k) :
    (charLGeomPlaceOfPoint k a).ord
        ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))
          - algebraMap k ↥(modularFunctionFieldC k 1) c)
      = if c = a then 1 else 0 := by
  classical
  have hq : (Polynomial.X - Polynomial.C c : Polynomial k) ≠ 0 := Polynomial.X_sub_C_ne_zero c
  have key : (ratFuncEquivCharLOneC k).toRingEquiv
        (algebraMap (Polynomial k) (RatFunc k) (Polynomial.X - Polynomial.C c))
      = (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))
          - algebraMap k ↥(modularFunctionFieldC k 1) c := by
    apply Subtype.ext
    change ((IntermediateField.equivOfEq (modularFunctionFieldC_one k).symm
        (RatFunc.algEquivOfTranscendental (jqModC k) _
          (algebraMap (Polynomial k) (RatFunc k) (Polynomial.X - Polynomial.C c))) :
            ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = _
    have hcoe : ∀ (h : IntermediateField.adjoin k {jqModC k} = modularFunctionFieldC k 1)
        (x : ↥(IntermediateField.adjoin k {jqModC k})),
        ((IntermediateField.equivOfEq h x : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)
          = (x : LaurentSeries k) := fun _ _ => rfl
    rw [hcoe, RatFunc.algEquivOfTranscendental_algebraMap, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    rfl
  have hplace : charLGeomPlaceOfPoint k a
      = Place.congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
          (fun x => (ratFuncEquivCharLOneC k).commutes x) (RationalFunctionField.placeOfPoint k a) := rfl
  rw [hplace, ← key, Place.ord_congrRingEquiv, RationalFunctionField.ord_placeOfPoint_algebraMap a hq,
    Polynomial.rootMultiplicity_X_sub_C]
  by_cases h : c = a
  · subst h; simp
  · simp [h, Ne.symm h]

end S_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
end P2MW
export P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap (solution)
