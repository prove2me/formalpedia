-- Prove2me | solution 1 for ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_pow_sq_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d28ff1fe-8302-59ea-a3c8-5999d0edc6ff

import Mathlib
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_pow_sq_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option autoImplicit false

open AlgebraicCurve ModularCurve Polynomial AlgebraicCurve.RationalFunctionField

namespace FltWs24
namespace BranchUnif

variable {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q] [DecidableEq k]

theorem ratFuncEquivCharLOneC_X :
    (ratFuncEquivCharLOneC k (RatFunc.X : RatFunc k) : ↥(modularFunctionFieldC k 1))
      = ⟨jqModC k, jqModC_mem k 1⟩ := by
  apply Subtype.ext
  rw [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  show ((RatFunc.algEquivOfTranscendental (jqModC k) (transcendental_jqModC k) RatFunc.X :
      ↥(IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)))) : LaurentSeries k) = jqModC k
  simp

theorem rootMultiplicity_X_sub_X_pow (a : k) (ha2 : a ^ (q ^ 2) = a) :
    Polynomial.rootMultiplicity a ((X : k[X]) - X ^ (q ^ 2)) = 1 := by
  have hq1 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (Fact.out : q.Prime).one_lt

  have hfrob : ((X : k[X]) - C a) ^ (q ^ 2) = X ^ (q ^ 2) - C (a ^ (q ^ 2)) := by
    rw [sub_pow_char_pow, C_pow]
  have hfac : (X : k[X]) - X ^ (q ^ 2) = (X - C a) * (1 - (X - C a) ^ (q ^ 2 - 1)) := by
    have : (X : k[X]) - C a - ((X : k[X]) - C a) ^ (q ^ 2) = X - X ^ (q ^ 2) := by
      rw [hfrob, ha2]; ring
    rw [← this, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hq1.le]
  have hu0 : ¬ ((1 : k[X]) - (X - C a) ^ (q ^ 2 - 1)).IsRoot a := by
    rw [IsRoot, eval_sub, eval_one, eval_pow, eval_sub, eval_X, eval_C, sub_self,
      zero_pow (by omega), sub_zero]
    exact one_ne_zero
  have hne : ((X : k[X]) - C a) * (1 - (X - C a) ^ (q ^ 2 - 1)) ≠ 0 := by
    refine mul_ne_zero (X_sub_C_ne_zero a) (fun h => hu0 ?_)
    rw [h]; simp
  rw [hfac, rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_self, rootMultiplicity_eq_zero hu0]

end FltWs24.BranchUnif

open FltWs24.BranchUnif in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q] [DecidableEq k] (a : k) (ha2 : a ^ (q ^ 2) = a) :
    (charLGeomPlaceOfPoint k a).ord
      ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))
        - (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) ^ (q ^ 2)) = 1 := by
  classical
  have hq1 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (Fact.out : q.Prime).one_lt

  have hX := ratFuncEquivCharLOneC_X (k := k)
  have himg : ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))
        - (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) ^ (q ^ 2))
      = (ratFuncEquivCharLOneC k).toRingEquiv (algebraMap k[X] (RatFunc k) ((X : k[X]) - X ^ (q ^ 2))) := by
    rw [map_sub, map_pow, RatFunc.algebraMap_X, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, map_sub,
      map_pow, hX]
  rw [himg, charLGeomPlaceOfPoint, charLGeomPlaceEquiv, Place.congrEquiv_apply, Place.ord_congrRingEquiv,
    ord_placeOfPoint_algebraMap a (by
      intro h
      have := congrArg (Polynomial.rootMultiplicity a) h
      rw [rootMultiplicity_X_sub_X_pow a ha2, rootMultiplicity_zero] at this
      exact one_ne_zero this),
    rootMultiplicity_X_sub_X_pow a ha2]
  rfl

end S_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_pow_sq_eq_one
end P2MW
export P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_pow_sq_eq_one (solution)
