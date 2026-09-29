-- Prove2me | solution 1 for ModularCurve.ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/c5f3ad13-2e47-5257-a54e-bfa78f2ef033

import Definitions.Def_ModularCurve_SpecializeModuli

import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

open Polynomial

namespace FltWs21
namespace Transport

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_algebraMap (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hu : IsUnit (algebraMap K v.toValuationSubring c) := hc.isUnit.map _
    have h := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec, Place.coe_algebraMap] at h

theorem jqModC_sub_algebraMap_ne_zero (k : Type*) [Field k] [DecidableEq k] (r : k) :
    ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) r) ≠ 0 := by
  intro h0
  have h := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k r r
  rw [h0, Place.ord_zero, if_pos rfl] at h
  exact zero_ne_one h

theorem ord_aeval_prod_X_sub_C (k : Type*) [Field k] [DecidableEq k] (a : k) (s : Multiset k) :
    (charLGeomPlaceOfPoint k a).ord
        (aeval ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))) (s.map fun r => X - C r).prod) =
      (s.count a : ℤ) ∧
    aeval ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))) (s.map fun r => X - C r).prod ≠ 0 := by
  induction s using Multiset.induction with
  | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero, map_one, Multiset.count_zero, Nat.cast_zero, ne_eq,
        one_ne_zero, not_false_eq_true, and_true]
      have := ord_algebraMap (charLGeomPlaceOfPoint k a) (1 : k)
      rwa [map_one] at this
  | cons r s ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hr : aeval ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))) (X - C r) =
          (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k _ r := by
        rw [map_sub, aeval_X, aeval_C]
      rw [Multiset.map_cons, Multiset.prod_cons, map_mul, hr]
      refine ⟨?_, mul_ne_zero (jqModC_sub_algebraMap_ne_zero k r) ih2⟩
      rw [(charLGeomPlaceOfPoint k a).ord_mul (jqModC_sub_algebraMap_ne_zero k r) ih2, ih1,
        ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k a r, Multiset.count_cons]
      by_cases h : r = a
      · rw [if_pos h, if_pos h.symm]; push_cast; ring
      · rw [if_neg h, if_neg (Ne.symm h)]; push_cast; ring

end FltWs21.Transport

theorem solution
    (k : Type*) [Field k] [IsAlgClosed k] [DecidableEq k] (a : k) (P : Polynomial k) :
    (charLGeomPlaceOfPoint k a).ord
        (Polynomial.aeval ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))) P) =
      (P.rootMultiplicity a : ℤ) := by
  by_cases hP : P = 0
  · subst hP; simp
  have hsplit : P = C P.leadingCoeff * (P.roots.map fun r => X - C r).prod := (IsAlgClosed.splits P).eq_prod_roots
  have hlead : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  obtain ⟨h1, h2⟩ := FltWs21.Transport.ord_aeval_prod_X_sub_C k a P.roots
  conv_lhs => rw [hsplit]
  rw [map_mul, aeval_C, (charLGeomPlaceOfPoint k a).ord_mul ((_root_.map_ne_zero _).mpr hlead) h2,
    FltWs21.Transport.ord_algebraMap, h1, zero_add, count_roots]

end S_ModularCurve_ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity
end P2MW
export P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity (solution)
