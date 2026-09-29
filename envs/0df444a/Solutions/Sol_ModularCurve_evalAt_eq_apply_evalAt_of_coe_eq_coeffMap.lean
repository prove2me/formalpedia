-- Prove2me | solution 1 for ModularCurve.evalAt_eq_apply_evalAt_of_coe_eq_coeffMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/33d703e6-22e9-5937-bca0-a9e72ab7ad2a

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_AlgebraicCurve_Place_mk_mem_maximalIdeal_iff
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_evalAt_eq_apply_evalAt_of_coe_eq_coeffMap
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem solution {K K' : Type*} [Field K] [Field K']
    [Algebra ℚ K] [Algebra ℚ K'] (σ : K →+* K') (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (v : Place K (laurentBaseChange K F₀)) (w : Place K' (laurentBaseChange K' F₀))
    (hw : ∀ (x : laurentBaseChange K F₀) (x' : laurentBaseChange K' F₀),
      (x' : LaurentSeries K') = coeffMap σ (x : LaurentSeries K) → w.ord x' = v.ord x)
    (hv : v.IsRational)
    (x : laurentBaseChange K F₀) (x' : laurentBaseChange K' F₀)
    (hx' : (x' : LaurentSeries K') = coeffMap σ (x : LaurentSeries K)) (hx : x ∈ v.toValuationSubring) :
    w.evalAt x' = σ (v.evalAt x) := by

  have hx'mem : x' ∈ w.toValuationSubring := by
    by_cases h0 : x' = 0
    · rw [h0]; exact zero_mem _
    · exact w.mem_of_ord_nonneg h0 ((hw x x' hx').symm ▸ v.ord_nonneg_of_mem hx)

  have hres : IsLocalRing.residue v.toValuationSubring ⟨x, hx⟩
      = algebraMap K v.ResidueField (v.evalAt x) := (v.algebraMap_evalAt hv hx).symm
  have hya : x - algebraMap K (laurentBaseChange K F₀) (v.evalAt x) ∈ v.toValuationSubring :=
    sub_mem hx (v.algebraMap_mem' _)
  have hmax : (⟨x - algebraMap K (laurentBaseChange K F₀) (v.evalAt x), hya⟩ : v.toValuationSubring)
      ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    have e : (⟨x - algebraMap K (laurentBaseChange K F₀) (v.evalAt x), hya⟩ : v.toValuationSubring)
        = ⟨x, hx⟩ - algebraMap K v.toValuationSubring (v.evalAt x) := by
      apply Subtype.ext
      rw [AddSubgroupClass.coe_sub, v.coe_algebraMap]
    rw [e, ← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_eq_zero,
      IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]
  have hy : x - algebraMap K (laurentBaseChange K F₀) (v.evalAt x) = 0
      ∨ 0 < v.ord (x - algebraMap K (laurentBaseChange K F₀) (v.evalAt x)) :=
    (v.mk_mem_maximalIdeal_iff hya).1 hmax

  have hcK : ((algebraMap K (laurentBaseChange K F₀) (v.evalAt x) : laurentBaseChange K F₀) : LaurentSeries K)
      = HahnSeries.single 0 (v.evalAt x) := by
    rw [← IntermediateField.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      algebraMap_laurentSeries_eq_single]
  have hcK' : ((algebraMap K' (laurentBaseChange K' F₀) (σ (v.evalAt x)) : laurentBaseChange K' F₀)
      : LaurentSeries K') = HahnSeries.single 0 (σ (v.evalAt x)) := by
    rw [← IntermediateField.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      algebraMap_laurentSeries_eq_single]

  have hcoe : ((x' - algebraMap K' (laurentBaseChange K' F₀) (σ (v.evalAt x)) : laurentBaseChange K' F₀)
        : LaurentSeries K')
      = coeffMap σ ((x - algebraMap K (laurentBaseChange K F₀) (v.evalAt x) : laurentBaseChange K F₀)
        : LaurentSeries K) := by
    rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, map_sub, hx', hcK, hcK', coeffMap_single]
  have hy' : x' - algebraMap K' (laurentBaseChange K' F₀) (σ (v.evalAt x)) = 0
      ∨ 0 < w.ord (x' - algebraMap K' (laurentBaseChange K' F₀) (σ (v.evalAt x))) := by
    rcases hy with h0 | hpos
    · left
      have h1 : ((x' - algebraMap K' (laurentBaseChange K' F₀) (σ (v.evalAt x)) : laurentBaseChange K' F₀)
          : LaurentSeries K') = 0 := by
        rw [hcoe, h0, ZeroMemClass.coe_zero, map_zero]
      exact ZeroMemClass.coe_eq_zero.1 h1
    · right
      rw [hw _ _ hcoe]
      exact hpos

  calc w.evalAt x' = w.evalAt (algebraMap K' (laurentBaseChange K' F₀) (σ (v.evalAt x))) :=
        w.evalAt_congr hx'mem (w.algebraMap_mem' _) hy'
    _ = σ (v.evalAt x) := w.evalAt_algebraMap _

end S_ModularCurve_evalAt_eq_apply_evalAt_of_coe_eq_coeffMap
end P2MW
export P2MW.S_ModularCurve_evalAt_eq_apply_evalAt_of_coe_eq_coeffMap (solution)
