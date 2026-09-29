-- Prove2me | solution 1 for ModularCurve.symVec_mem_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/29aecd4d-df46-57e9-b91c-4670eec863c7

import Definitions.Def_ModularCurve_JZeroNaiveHeight
import Theorems.Thm_ModularCurve_jCoordinate_spec_modularFunctionFieldBar
import Mathlib.FieldTheory.Galois.Infinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_symVec_mem_of_stable
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

open ModularCurve AlgebraicCurve

set_option autoImplicit false in
private theorem cure_isAlgebraic : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _

set_option autoImplicit false in
private theorem cure_isAlgClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  (isAlgClosure_iff (k := ℚ) (K := AlgebraicClosure ℚ)).mpr ⟨inferInstance, cure_isAlgebraic⟩

attribute [local instance] cure_isAlgClosure

set_option autoImplicit false in
private theorem mwP3_galois_smul_jbar (N : ℕ) [NeZero N]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (modularFunctionFieldFull N) σ •
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)
      = ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :=
  Subtype.ext (coeffMap_coeffEmb σ jq)

set_option autoImplicit false in
private theorem mwP3_ord_smul_jbar (N : ℕ) [NeZero N]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (arithmeticGalois (modularFunctionFieldFull N) σ • v).ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)
      = v.ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) := by
  conv_lhs => rw [← mwP3_galois_smul_jbar N σ]
  exact SemilinearAut.ord_smul _ v _

set_option autoImplicit false in
private theorem mwP3_jCoord_smul (N : ℕ) [NeZero N]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hv : 0 ≤ v.ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)) :
    jCoord N (arithmeticGalois (modularFunctionFieldFull N) σ • v)
      = (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (jCoord N v) := by
  have hP2 := (ModularCurve.jCoordinate_spec_modularFunctionFieldBar N).1
  have hsat : 0 < v.ord
      ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (jCoord N v)) :=
    Classical.epsilon_spec (hP2 v hv).exists
  have hvτ : 0 ≤ (arithmeticGalois (modularFunctionFieldFull N) σ • v).ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) := by
    rw [mwP3_ord_smul_jbar]
    exact hv
  have hτeps : 0 < (arithmeticGalois (modularFunctionFieldFull N) σ • v).ord
      ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (jCoord N (arithmeticGalois (modularFunctionFieldFull N) σ • v))) :=
    Classical.epsilon_spec (hP2 _ hvτ).exists
  have key : arithmeticGalois (modularFunctionFieldFull N) σ •
      ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (jCoord N v))
      = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          ((σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (jCoord N v)) := by
    rw [smul_sub, mwP3_galois_smul_jbar N σ, SemilinearAut.smul_algebraMap,
      baseAut_arithmeticGalois]
    rfl
  have hτσ : 0 < (arithmeticGalois (modularFunctionFieldFull N) σ • v).ord
      ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          ((σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (jCoord N v))) := by
    rw [← key, SemilinearAut.ord_smul]
    exact hsat
  exact (hP2 _ hvτ).unique hτeps hτσ

set_option autoImplicit false in
private theorem mwP3_jFactor_smul (N : ℕ) [NeZero N]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    jFactor N (arithmeticGalois (modularFunctionFieldFull N) σ • v)
      = Polynomial.map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (jFactor N v) := by
  by_cases hv : 0 ≤ v.ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)
  · have hvτ : 0 ≤ (arithmeticGalois (modularFunctionFieldFull N) σ • v).ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) := by
      rw [mwP3_ord_smul_jbar]
      exact hv
    rw [jFactor_of_nonneg hvτ, jFactor_of_nonneg hv, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, mwP3_jCoord_smul N σ v hv]
  · have hv' : v.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) < 0 := not_le.mp hv
    have hvτ : (arithmeticGalois (modularFunctionFieldFull N) σ • v).ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) < 0 := by
      rw [mwP3_ord_smul_jbar]
      exact hv'
    rw [jFactor_of_neg hvτ, jFactor_of_neg hv', Polynomial.map_one]

set_option autoImplicit false in
private theorem mwP3_symPoly_smul (N : ℕ) [NeZero N]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    symPoly N (arithmeticGalois (modularFunctionFieldFull N) σ • D)
      = Polynomial.map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (symPoly N D) := by
  unfold symPoly
  rw [SemilinearAut.divisor_smul_def,
    Finsupp.prod_mapDomain_index_inj (MulAction.injective _),
    ← Polynomial.coe_mapRingHom, map_finsuppProd]
  refine Finsupp.prod_congr fun v _ => ?_
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_pow, mwP3_jFactor_smul N σ]

set_option autoImplicit false in
private theorem mwP3_symVec_smul (N : ℕ) [NeZero N] (g' : ℕ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (k : Fin (g' + 1)) :
    symVec N g' (arithmeticGalois (modularFunctionFieldFull N) σ • D) k
      = σ (symVec N g' D k) := by
  unfold symVec
  rw [mwP3_symPoly_smul N σ D]
  exact Polynomial.coeff_map _ _

set_option autoImplicit false in
theorem solution (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (g' : ℕ) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
        arithmeticGalois (modularFunctionFieldFull N) σ • D = D)
    (k : Fin (g' + 1)) : symVec N g' D k ∈ K
    := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
      intro σ hσ
      rw [← mwP3_symVec_smul N g' D σ k, hD σ hσ]

end S_ModularCurve_symVec_mem_of_stable
end P2MW
export P2MW.S_ModularCurve_symVec_mem_of_stable (solution)
