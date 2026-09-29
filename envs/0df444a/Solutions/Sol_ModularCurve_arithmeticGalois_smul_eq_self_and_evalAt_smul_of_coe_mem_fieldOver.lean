-- Prove2me | solution 1 for ModularCurve.arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/bea4a06c-2adf-5fe4-aa54-e33632fa12b8

import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_evalAt_eq_apply_evalAt_of_coe_eq_coeffMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

private theorem SIGMA_fix (M : ℕ) [NeZero M] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : ∀ z ∈ K, σ z = z)
    (g : ↥(modularFunctionFieldBar M))
    (hg : ((g : ↥(modularFunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ NodeLocalized.fieldOver M K) :
    arithmeticGalois (modularFunctionFieldFull M) σ • g = g := by
  apply Subtype.ext
  rw [coe_arithmeticGalois_smul]
  have hg' : ((g : ↥(modularFunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ Subfield.closure (Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring)
        ∪ {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) M}) := hg
  have key : Set.EqOn (coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))
      (RingHom.id (LaurentSeries (AlgebraicClosure ℚ)))
      (Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring)
        ∪ {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) M}) := by
    rintro x (⟨z, rfl⟩ | hx)
    · show coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)
          (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (z : AlgebraicClosure ℚ))
        = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (z : AlgebraicClosure ℚ)
      rw [coeffMap_algebraMap, RingHom.coe_coe, hσ z z.2]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact coeffSemilinearAut.coeffMap_jqModC _
      · exact coeffSemilinearAut.coeffMap_jqNModC _ M
  exact RingHom.eqOn_field_closure key hg'

set_option maxHeartbeats 1600000 in

theorem solution
    (M : ℕ) [NeZero M] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : ∀ z ∈ K, σ z = z)
    (g : ↥(modularFunctionFieldBar M))
    (hg : ((g : ↥(modularFunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ NodeLocalized.fieldOver M K) :
    arithmeticGalois (modularFunctionFieldFull M) σ • g = g ∧
      ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M), V.IsRational →
        (arithmeticGalois (modularFunctionFieldFull M) σ • V).evalAt g = σ (V.evalAt g) := by
  have hfix : arithmeticGalois (modularFunctionFieldFull M) σ • g = g := SIGMA_fix M K σ hσ g hg
  refine ⟨hfix, fun V hV => ?_⟩
  by_cases hmem : g ∈ V.toValuationSubring
  · refine ModularCurve.evalAt_eq_apply_evalAt_of_coe_eq_coeffMap
      (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (modularFunctionFieldFull M) V (arithmeticGalois (modularFunctionFieldFull M) σ • V) ?_ hV g g ?_ hmem
    · intro x x' hx'
      have hxx : x' = arithmeticGalois (modularFunctionFieldFull M) σ • x :=
        Subtype.ext (hx'.trans (coe_arithmeticGalois_smul _ σ x).symm)
      rw [hxx]
      exact SemilinearAut.ord_smul _ V x
    · rw [← coe_arithmeticGalois_smul _ σ g, hfix]
  · have h1 : (arithmeticGalois (modularFunctionFieldFull M) σ • V).evalAt g = 0 := by
      have hmem' : g ∉ (arithmeticGalois (modularFunctionFieldFull M) σ • V).toValuationSubring := by
        rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
        have hinv : (arithmeticGalois (modularFunctionFieldFull M) σ)⁻¹ • g = g := by
          rw [inv_smul_eq_iff, hfix]
        rw [hinv]
        exact hmem
      unfold Place.evalAt
      rw [dif_neg hmem']
    have h2 : V.evalAt g = 0 := by
      unfold Place.evalAt
      rw [dif_neg hmem]
    rw [h1, h2, map_zero]

#print axioms solution

end S_ModularCurve_arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver
end P2MW
export P2MW.S_ModularCurve_arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver (solution)
