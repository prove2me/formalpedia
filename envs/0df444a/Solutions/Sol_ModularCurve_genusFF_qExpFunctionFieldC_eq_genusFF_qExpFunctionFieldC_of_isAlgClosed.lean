-- Prove2me | solution 1 for ModularCurve.genusFF_qExpFunctionFieldC_eq_genusFF_qExpFunctionFieldC_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/57c94146-ba9b-52cb-ac7f-ffe750fe10ed

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_genusFF_qExpFunctionFieldC_eq_genusFF_qExpFunctionFieldC_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    (κ K : Type*) [Field κ] [Field K] [IsAlgClosed κ] [IsAlgClosed K] [Algebra κ K]
    (Γ : Subgroup SL(2, ℤ))
    [AlgebraicCurve.IsCurveOver κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)]
    [AlgebraicCurve.IsCurveOver K ↥(ModularCurve.qExpFunctionFieldC K Γ)]
    (hfgκ : ∃ x : ↥(ModularCurve.qExpFunctionFieldC κ Γ), Transcendental κ x ∧
      FiniteDimensional ↥(IntermediateField.adjoin κ ({x} : Set ↥(ModularCurve.qExpFunctionFieldC κ Γ)))
        ↥(ModularCurve.qExpFunctionFieldC κ Γ))
    (hfgK : ∃ x : ↥(ModularCurve.qExpFunctionFieldC K Γ), Transcendental K x ∧
      FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set ↥(ModularCurve.qExpFunctionFieldC K Γ)))
        ↥(ModularCurve.qExpFunctionFieldC K Γ)) :
    AlgebraicCurve.genusFF K ↥(ModularCurve.qExpFunctionFieldC K Γ) =
      AlgebraicCurve.genusFF κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) := by
  classical

  have hBC : ModularCurve.qExpFunctionFieldC K Γ =
      IntermediateField.adjoin K (⇑(ModularCurve.coeffMap (algebraMap κ K)) ''
        (ModularCurve.qExpFunctionFieldC κ Γ : Set (LaurentSeries κ))) :=
    ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC κ K Γ
  have hmem : ∀ x : ↥(ModularCurve.qExpFunctionFieldC κ Γ), ModularCurve.coeffMap (algebraMap κ K) (x : LaurentSeries κ) ∈ ModularCurve.qExpFunctionFieldC K Γ := by
    intro x
    rw [hBC]
    exact IntermediateField.subset_adjoin K _ ⟨x, x.2, rfl⟩

  let φ : ↥(ModularCurve.qExpFunctionFieldC κ Γ) →+* ↥(ModularCurve.qExpFunctionFieldC K Γ) :=
    { toFun := fun x => ⟨ModularCurve.coeffMap (algebraMap κ K) (x : LaurentSeries κ), hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hφ : ∀ x : ↥(ModularCurve.qExpFunctionFieldC κ Γ), ((φ x : ↥(ModularCurve.qExpFunctionFieldC K Γ)) : LaurentSeries K) = ModularCurve.coeffMap (algebraMap κ K) (x : LaurentSeries κ) :=
    fun x => rfl
  letI instA : Algebra ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) := φ.toAlgebra
  letI instB : Algebra κ ↥(ModularCurve.qExpFunctionFieldC K Γ) := ((algebraMap K ↥(ModularCurve.qExpFunctionFieldC K Γ)).comp (algebraMap κ K)).toAlgebra
  haveI : IsScalarTower κ K ↥(ModularCurve.qExpFunctionFieldC K Γ) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hcmC : ∀ a : κ, ModularCurve.coeffMap (algebraMap κ K) (algebraMap κ (LaurentSeries κ) a) =
      algebraMap K (LaurentSeries K) (algebraMap κ K a) := by
    intro a
    ext n
    rw [ModularCurve.coeffMap_coeff]
    by_cases h : n = 0
    · subst h; simp [HahnSeries.algebraMap_apply']
    · simp [HahnSeries.algebraMap_apply', h]
  haveI : IsScalarTower κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => Subtype.ext ?_)
    exact (hcmC a).symm

  have hgen : IntermediateField.adjoin K (Set.range (algebraMap ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ))) = ⊤ := by
    apply IntermediateField.lift_injective
    erw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
    have hset : Subtype.val '' Set.range (algebraMap ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ)) =
        ⇑(ModularCurve.coeffMap (algebraMap κ K)) '' (ModularCurve.qExpFunctionFieldC κ Γ : Set (LaurentSeries κ)) := by
      ext y
      constructor
      · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨φ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    rw [hset, ← hBC]

  exact AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) K ↥(ModularCurve.qExpFunctionFieldC K Γ) hfgκ hfgK hgen

end S_ModularCurve_genusFF_qExpFunctionFieldC_eq_genusFF_qExpFunctionFieldC_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_genusFF_qExpFunctionFieldC_eq_genusFF_qExpFunctionFieldC_of_isAlgClosed (solution)
