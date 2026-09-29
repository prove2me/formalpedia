-- Prove2me | solution 1 for ModularCurve.restrict_eq_jLinePlaceInfty_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d237ebb6-cb86-5259-9c06-2021cc8b647e

import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_eq_jLinePlaceInfty_iff_ord_jGen_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_restrict_eq_jLinePlaceInfty_iff
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open IntermediateField AlgebraicCurve

namespace ModularCurve p2m_export "ModularCurve" "jAdjoinAlgebra jLinePlaceInfty jq modularFunctionField jq_mem jGen eq_jLinePlaceInfty_iff_ord_jGen_neg" namespace RestrictAux end ModularCurve.RestrictAux
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.RestrictAux.ord_algebraMap_pos_iff (N : ℕ) [NeZero N] :
    letI := ModularCurve.jAdjoinAlgebra N
    ∀ [Algebra.IsIntegral ↥ℚ⟮ModularCurve.jq⟯ ↥(ModularCurve.modularFunctionField N)]
      (w : AlgebraicCurve.Place ℚ ↥(ModularCurve.modularFunctionField N)) (x : ↥ℚ⟮ModularCurve.jq⟯),
      (0 < w.ord (algebraMap ↥ℚ⟮ModularCurve.jq⟯ ↥(ModularCurve.modularFunctionField N) x) ↔
          0 < (w.restrict ↥ℚ⟮ModularCurve.jq⟯).ord x) ∧
      (w.ord (algebraMap ↥ℚ⟮ModularCurve.jq⟯ ↥(ModularCurve.modularFunctionField N) x) < 0 ↔
          (w.restrict ↥ℚ⟮ModularCurve.jq⟯).ord x < 0) := by
  letI := ModularCurve.jAdjoinAlgebra N
  intro _ w x
  have he : (0 : ℤ) < (w.ramificationIndex ↥ℚ⟮ModularCurve.jq⟯ : ℤ) :=
    Int.natCast_pos.mpr (w.ramificationIndex_pos (F := ↥ℚ⟮ModularCurve.jq⟯))
  rw [w.ord_restrict (F := ↥ℚ⟮ModularCurve.jq⟯) x]
  constructor
  · constructor
    · intro h; by_contra hle; rw [not_lt] at hle; nlinarith
    · intro h; positivity
  · constructor
    · intro h; by_contra hle; rw [not_lt] at hle; nlinarith
    · intro h; nlinarith

theorem solution (N : ℕ) [NeZero N] :
    letI := ModularCurve.jAdjoinAlgebra N
    ∀ [Algebra.IsIntegral ↥ℚ⟮ModularCurve.jq⟯ ↥(ModularCurve.modularFunctionField N)]
      (w : AlgebraicCurve.Place ℚ ↥(ModularCurve.modularFunctionField N)),
      w.restrict ↥ℚ⟮ModularCurve.jq⟯ = ModularCurve.jLinePlaceInfty ↔
        w.ord (⟨ModularCurve.jq, ModularCurve.jq_mem N⟩ : ↥(ModularCurve.modularFunctionField N)) < 0 := by
  letI := ModularCurve.jAdjoinAlgebra N
  intro _ w
  rw [ModularCurve.eq_jLinePlaceInfty_iff_ord_jGen_neg,
    ← (ModularCurve.RestrictAux.ord_algebraMap_pos_iff N w ModularCurve.jGen).2]
  rfl

end S_ModularCurve_restrict_eq_jLinePlaceInfty_iff
end P2MW
export P2MW.S_ModularCurve_restrict_eq_jLinePlaceInfty_iff (solution)
