-- Prove2me | solution 1 for NumberField.PrimeNormIndex.secondInequalityCTM_of_finrank_eq_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/87aa3bc8-eceb-5a8c-a886-6300b4ac37de

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_PrimeNormIndex_AdmissibleExpAt
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Definitions.Def_NarrowRayClassGroup
import Theorems.Thm_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

section NormSquare

set_option autoImplicit false

noncomputable section

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField"

namespace M4aKummer

attribute [local instance] FractionRing.liftAlgebra

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem finrank_fractionRing_eq :
    Module.finrank (FractionRing (𝓞 k)) (FractionRing (𝓞 E)) = Module.finrank k E := by
  refine Algebra.finrank_eq_of_equiv_equiv
    (FractionRing.algEquiv (𝓞 k) k).toRingEquiv
    (FractionRing.algEquiv (𝓞 E) E).toRingEquiv ?_
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 k))
  ext a
  show algebraMap k E ((FractionRing.algEquiv (𝓞 k) k)
      ((algebraMap (𝓞 k) (FractionRing (𝓞 k))) a)) =
    (FractionRing.algEquiv (𝓞 E) E)
      ((algebraMap (FractionRing (𝓞 k)) (FractionRing (𝓞 E)))
        ((algebraMap (𝓞 k) (FractionRing (𝓞 k))) a))
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply (𝓞 k) k E,
    ← IsScalarTower.algebraMap_apply (𝓞 k) (FractionRing (𝓞 k)) (FractionRing (𝓞 E)),
    IsScalarTower.algebraMap_apply (𝓞 k) (𝓞 E) (FractionRing (𝓞 E)),
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply (𝓞 k) (𝓞 E) E]

private theorem relNorm_map_eq_sq (h2 : Module.finrank k E = 2) (𝔟 : Ideal (𝓞 k)) :
    Ideal.relNorm (𝓞 k) (𝔟.map (algebraMap (𝓞 k) (𝓞 E))) = 𝔟 ^ 2 := by
  rw [Ideal.relNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 k) k (𝓞 E) E, h2]

end M4aKummer

end

end NormSquare

section FadContent

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain Deep.NTSupply WithZero"
open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

section ContentApply

private theorem fadContentHom_apply (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    fadContentHom K u = ∏ᶠ v : HeightOneSpectrum (𝓞 K), (primeUnit K v) ^ (placeOrd K u v) :=
  rfl

private theorem fadContentHom_single_uniformizer (u : (FiniteAdeleRing (𝓞 K) K)ˣ)
    {v : HeightOneSpectrum (𝓞 K)}
    (huw : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v →
      Valued.v ((u : FiniteAdeleRing (𝓞 K) K) w) = 1)
    (huv : Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) = WithZero.exp (-1 : ℤ)) :
    fadContentHom K u = primeUnit K v := by
  rw [fadContentHom_apply]
  rw [finprod_eq_single _ v]
  · have : placeOrd K u v = 1 := by unfold placeOrd; rw [huv, WithZero.log_exp]; ring
    rw [this, zpow_one]
  · intro w hwv
    have : placeOrd K u w = 0 := (placeOrd_eq_zero_iff K u w).mpr (huw w hwv)
    rw [this, zpow_zero]

end ContentApply

section ContentPrincipal

private theorem coe_fadContentHom (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((fadContentHom K u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (placeOrd K u v) := by
  rw [fadContentHom_apply, ← Units.coeHom_apply,
    (Units.coeHom _).map_finprod_of_preimage_one (fun _ h => Units.ext h)
      (fun v => primeUnit K v ^ placeOrd K u v)]
  refine finprod_congr fun v => ?_
  rw [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, primeUnit_val]

private theorem count_fadContentHom (u : (FiniteAdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w ((fadContentHom K u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = placeOrd K u w := by
  rw [coe_fadContentHom]
  exact FractionalIdeal.count_finprod K w (placeOrd K u) (by
    rw [Filter.eventually_cofinite]
    exact finite_support_placeOrd K u)

private theorem fadContentHom_mem_coprimeToModulus_iff (u : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (𝔣 : Ideal (𝓞 K)) :
    fadContentHom K u ∈ coprimeToModulus K 𝔣 ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
        Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
  rw [mem_coprimeToModulus_iff]
  refine forall_congr' fun v => forall_congr' fun _ => ?_
  rw [count_fadContentHom, placeOrd_eq_zero_iff]

private theorem placeOrd_unitEmbedding (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    placeOrd K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) v
      = FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (α : K)) := by
  classical

  have hLHS : placeOrd K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) v
      = -WithZero.log (v.valuation K (α : K)) := by
    unfold placeOrd
    rw [FiniteAdeleRing.unitEmbedding, Units.coe_map, MonoidHom.coe_coe,
      FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (α : K)]
  rw [hLHS]

  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.mk'_surjective (M := (𝓞 K)⁰) (S := K) (α : K)
  have hnd' : IsLocalization.mk' K n d = (α : K) := hnd
  have hn0 : n ≠ 0 := by
    rintro rfl; simp only [IsLocalization.mk'_zero] at hnd'; exact α.ne_zero hnd'.symm
  have hd0 : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  rw [← hnd', HeightOneSpectrum.valuation_of_mk',
    HeightOneSpectrum.intValuation_if_neg _ hn0, HeightOneSpectrum.intValuation_if_neg _ hd0,
    ← WithZero.exp_sub, WithZero.log_exp, neg_sub_neg,
    IsFractionRing.mk'_eq_div, div_eq_mul_inv,
    ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K v
      (by rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
          exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hn0)
      (by rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff, inv_eq_zero]
          exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0),
    ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v
      (by simp only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hn0),
    show FractionalIdeal.spanSingleton ((𝓞 K)⁰) (algebraMap (𝓞 K) K d)⁻¹
        = (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (algebraMap (𝓞 K) K d))⁻¹ by
        rw [← one_div, ← FractionalIdeal.spanSingleton_div_spanSingleton,
          FractionalIdeal.spanSingleton_one, one_div],
    FractionalIdeal.count_inv, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K v
      (by simp only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd0)]
  ring

private theorem coe_fadContentHom_principal (α : Kˣ) :
    ((fadContentHom K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton ((𝓞 K)⁰) (α : K) := by
  rw [coe_fadContentHom]
  conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K)
    (I := FractionalIdeal.spanSingleton ((𝓞 K)⁰) (α : K))
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr α.ne_zero)]
  exact finprod_congr fun v => by rw [placeOrd_unitEmbedding]

private theorem fadContentHom_unitEmbedding (α : Kˣ) :
    fadContentHom K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) = toPrincipalIdeal (𝓞 K) K α :=
  Units.ext <| (coe_fadContentHom_principal K α).trans (coe_toPrincipalIdeal α).symm

end ContentPrincipal

end HeckeCharacter

end

end FadContent

section IdeleContentBuild

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain Deep.NTSupply WithZero"
open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

section Adjusters

private theorem projFin_val (u : (AdeleRing (𝓞 K) K)ˣ) :
    ((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) =
      (u : AdeleRing (𝓞 K) K).2 := rfl

private theorem projFin_principal (α : Kˣ) :
    projFin K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)
      = FiniteAdeleRing.unitEmbedding (𝓞 K) K α := by
  apply Units.ext; rfl

omit [NumberField K] in
omit [NumberField K] in
omit [NumberField K] in

private theorem embedding_of_isReal_placeOf (τ : K →+* ℝ) :
    InfinitePlace.embedding_of_isReal (isReal_placeOf K τ) = τ := by
  ext x
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, show (placeOf K τ).embedding
      = Complex.ofRealHom.comp τ from
    InfinitePlace.embedding_mk_eq_of_isReal (isReal_compOfRealHom K τ)]
  rfl

private theorem archSign_principal (τ : K →+* ℝ) (α : Kˣ) :
    archSign K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) ↔ 0 < τ (α : K) := by
  unfold archSign archRealProjTau
  rw [Units.coe_map, MonoidHom.coe_coe, AdeleRing.algebraMap_fst_apply,
    InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe,
    embedding_of_isReal_placeOf K τ]
  rfl

namespace IsAdjuster p2m_export "HeckeCharacter.IsAdjuster" "mk cong sign" end IsAdjuster
namespace IsAdjuster
p2m_open_scoped "HeckeCharacter.IsAdjuster" in
private theorem _root_.HeckeCharacter.IsAdjuster.coprime {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α : Kˣ}
    (h : IsAdjuster K 𝔣 u α) :
    fadContentHom K (projFin K (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹))
      ∈ coprimeToModulus K 𝔣 := by
  rw [fadContentHom_mem_coprimeToModulus_iff]
  intro v hv
  rw [projFin_val]
  exact (h.cong v hv).1

end IsAdjuster
p2m_export "HeckeCharacter" "IsAdjuster.coprime"
private theorem isAdjuster_one_one (𝔣 : Ideal (𝓞 K)) : IsAdjuster K 𝔣 1 1 := by
  refine ⟨fun v _ => ?_, fun τ => ?_⟩
  · simp only [map_one, inv_one, mul_one]
    refine ⟨?_, ?_⟩
    · show Valued.v ((1 : FiniteAdeleRing (𝓞 K) K) v) = 1
      rw [fad_one_apply]; exact map_one _
    · show Valued.v ((1 : FiniteAdeleRing (𝓞 K) K) v - 1) ≤ _
      rw [fad_one_apply, sub_self, map_zero]; exact zero_le'
  · simp only [map_one, inv_one, mul_one]
    exact archSign_of_fst_eq_one K τ rfl

private abbrev adjFinV (u : (AdeleRing (𝓞 K) K)ˣ) (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K :=
  (((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v

private theorem four_comm {G : Type*} [CommMonoid G] (a b c d : G) :
    a * b * (d * c) = a * c * (b * d) := by
  simp only [mul_comm, mul_left_comm]

private abbrev pK : Kˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K))

private theorem adj_adele_mul (u u' : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) :
    u * u' * (pK K (α * α'))⁻¹ = (u * (pK K α)⁻¹) * (u' * (pK K α')⁻¹) := by
  rw [map_mul, mul_inv_rev]; exact four_comm _ _ _ _

private theorem adj_adele_ratio (u : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) :
    (u * (pK K α)⁻¹)⁻¹ * (u * (pK K α')⁻¹) = pK K (α * α'⁻¹) := by
  rw [mul_inv_rev, inv_inv, map_mul, map_inv, mul_assoc, ← mul_assoc u⁻¹, inv_mul_cancel,
    one_mul]

private theorem adjFinV_mul (u u' : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    adjFinV K (u * u') (α * α') v = adjFinV K u α v * adjFinV K u' α' v := by
  unfold adjFinV
  rw [show u * u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (α * α'))⁻¹
      = (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)
        * (u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α')⁻¹) from by
    rw [map_mul, mul_inv_rev]; exact four_comm _ _ _ _]
  exact fad_mul_apply K _ _ v

namespace IsAdjuster
p2m_open_scoped "HeckeCharacter.IsAdjuster" in
private theorem _root_.HeckeCharacter.IsAdjuster.mul {𝔣 : Ideal (𝓞 K)} {u u' : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u' α') :
    IsAdjuster K 𝔣 (u * u') (α * α') := by
  have hfac : u * u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (α * α'))⁻¹
      = (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)
        * (u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α')⁻¹) := by
    rw [map_mul, mul_inv_rev]; exact four_comm _ _ _ _
  refine ⟨fun v hv𝔣 => ?_, fun τ => ?_⟩
  · show Valued.v (adjFinV K (u * u') (α * α') v) = 1 ∧
      Valued.v (adjFinV K (u * u') (α * α') v - 1) ≤ _
    rw [adjFinV_mul]
    exact unit_cong_mul K (hα.cong v hv𝔣).1 (hα.cong v hv𝔣).2 (hα'.cong v hv𝔣).1
      (hα'.cong v hv𝔣).2
  · rw [hfac, archSign_mul K τ]
    exact iff_of_true (hα.sign τ) (hα'.sign τ)

end IsAdjuster
p2m_export "HeckeCharacter" "IsAdjuster.mul"
private theorem isAdjuster_principal_self (𝔣 : Ideal (𝓞 K)) (α : Kˣ) :
    IsAdjuster K 𝔣 (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) α := by
  refine ⟨fun v _ => ?_, fun τ => ?_⟩
  · have h1 : adjFinV K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) α v = 1 := by
      unfold adjFinV; simp only [mul_inv_cancel, Units.val_one]
      exact fad_one_apply K v
    show Valued.v (adjFinV K _ α v) = 1 ∧ Valued.v (adjFinV K _ α v - 1) ≤ _
    rw [h1]
    exact ⟨map_one _, by rw [sub_self, map_zero]; exact zero_le'⟩
  · have h1 : (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α : (AdeleRing (𝓞 K) K)ˣ)
        * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ = 1 := mul_inv_cancel _
    rw [h1]; exact archSign_one K τ

private theorem adjFinV_ratio (u : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((α * α'⁻¹ : Kˣ) : K) : v.adicCompletion K)
      = adjFinV K u α' v * (adjFinV K u α v)⁻¹ := by
  have hkey := congrArg (fun x : (FiniteAdeleRing (𝓞 K) K)ˣ =>
    ((x : FiniteAdeleRing (𝓞 K) K) : FiniteAdeleRing (𝓞 K) K) v)
    (congrArg (projFin K) (adj_adele_ratio K u α α'))
  rw [map_mul, map_inv, projFin_principal] at hkey
  simp only [Units.val_mul, fad_mul_apply, fad_units_inv_apply, projFin_val] at hkey
  rw [show ((FiniteAdeleRing.unitEmbedding (𝓞 K) K (α * α'⁻¹) : (FiniteAdeleRing (𝓞 K) K)ˣ) :
      FiniteAdeleRing (𝓞 K) K) v = (((α * α'⁻¹ : Kˣ) : K) : v.adicCompletion K) from by
    rw [FiniteAdeleRing.unitEmbedding_apply]; exact FiniteAdeleRing.algebraMap_apply ..] at hkey
  rw [← hkey, mul_comm]; rfl

private theorem valuation_ratio_sub_one_le {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u α')
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ 𝔣) :
    v.valuation K (((α * α'⁻¹ : Kˣ) : K) - 1)
      ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)) := by
  rw [← v.valuedAdicCompletion_eq_valuation']
  have hcoe : ((((α * α'⁻¹ : Kˣ) : K) - 1 : K) : v.adicCompletion K)
      = (((α * α'⁻¹ : Kˣ) : K) : v.adicCompletion K) - 1 := by
    have h : ∀ y : K, (y : v.adicCompletion K) = algebraMap K (v.adicCompletion K) y := fun y => by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
    rw [h, h, map_sub, map_one]
  rw [hcoe, adjFinV_ratio K u α α']
  exact unit_cong_div K (hα'.cong v hv).2 (hα.cong v hv).1 (hα.cong v hv).2

private theorem ratio_totally_positive {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u α') (τ : K →+* ℝ) :
    0 < τ ((α * α'⁻¹ : Kˣ) : K) := by
  rw [← archSign_principal K τ, show Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (α * α'⁻¹)
    = pK K (α * α'⁻¹) from rfl, map_mul, map_inv, archSign_mul K τ, archSign_inv K τ]
  have h1 : archSign K τ u ↔ archSign K τ (pK K α) := by
    have := hα.sign τ; rwa [archSign_mul K τ, archSign_inv K τ] at this
  have h2 : archSign K τ u ↔ archSign K τ (pK K α') := by
    have := hα'.sign τ; rwa [archSign_mul K τ, archSign_inv K τ] at this
  exact h1.symm.trans h2

private theorem valuation_eq_one_of_cong {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {β : K}
    (hcong : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K (β - 1) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ 𝔣) :
    v.valuation K β = 1 := by
  have hm1 : 1 ≤ idealMultiplicity K v 𝔣 := by
    unfold idealMultiplicity
    rwa [Nat.one_le_iff_ne_zero, Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible]
  have hlt : v.valuation K (β - 1) < 1 :=
    lt_of_le_of_lt (hcong v hv) (by
      rw [show (1 : ℤᵐ⁰) = WithZero.exp (0 : ℤ) from (WithZero.exp_zero).symm,
        WithZero.exp_lt_exp]
      omega)
  have hβ : β = (β - 1) + 1 := (sub_add_cancel β 1).symm
  rw [hβ, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one]), map_one]

private theorem count_spanSingleton_eq_zero_of_valuation_eq_one {β : Kˣ}
    (v : HeightOneSpectrum (𝓞 K)) (h : v.valuation K (β : K) = 1) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (β : K)) = 0 := by
  rw [← placeOrd_unitEmbedding]
  unfold placeOrd
  rw [FiniteAdeleRing.unitEmbedding, Units.coe_map, MonoidHom.coe_coe,
    FiniteAdeleRing.algebraMap_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (β : K), h,
    WithZero.log_one, neg_zero]

private theorem mem_modulus_of_forall_valuation_le {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {x : 𝓞 K}
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K (algebraMap (𝓞 K) K x) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ))) :
    x ∈ 𝔣 := by
  have h𝔣0 : (𝔣 : Ideal (𝓞 K)) ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  rw [← Ideal.iInf_maxPowDividing_eq h𝔣0, Submodule.mem_iInf]
  intro v
  show x ∈ v.asIdeal ^ (idealMultiplicity K v 𝔣)
  by_cases hv : v.asIdeal ∣ 𝔣
  · rw [← v.intValuation_le_pow_iff_mem, ← v.valuation_of_algebraMap (K := K)]
    exact hx v hv
  · have hm0 : idealMultiplicity K v 𝔣 = 0 := by
      unfold idealMultiplicity
      by_contra hne
      exact hv ((Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible).mp hne)
    simp [hm0]

private theorem toPrincipalIdeal_mem_narrowRaySubgroup {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (β : Kˣ)
    (hcong : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K ((β : K) - 1) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)))
    (hsign : ∀ τ : K →+* ℝ, 0 < τ (β : K)) :
    toPrincipalIdeal (𝓞 K) K β ∈ narrowRaySubgroup K 𝔣 := by

  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (β : K)) = 0 :=
    fun v hv => count_spanSingleton_eq_zero_of_valuation_eq_one K v
      (valuation_eq_one_of_cong K h𝔣 hcong v hv)

  obtain ⟨d, hd0, hd1, n, hn⟩ := movingLemma K h𝔣 (β : K) β.ne_zero hloc

  have hd0' : (algebraMap (𝓞 K) K) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  have hn0 : n ≠ 0 := by
    rintro rfl; rw [map_zero] at hn
    exact β.ne_zero ((mul_eq_zero.mp hn.symm).resolve_left hd0')

  have hnd1 : n - d ∈ 𝔣 := by
    refine mem_modulus_of_forall_valuation_le K h𝔣 fun v hv => ?_
    have hval_d : v.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      rw [v.valuation_of_algebraMap (K := K)]
      refine le_antisymm (v.intValuation_le_one d) ?_
      rw [← not_lt, v.intValuation_lt_one_iff_mem]
      intro hmem
      exact v.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr
        (show (1 : 𝓞 K) ∈ v.asIdeal from by
          have : (d : 𝓞 K) - (d - 1) ∈ v.asIdeal := sub_mem hmem
            ((Ideal.dvd_iff_le.mp hv) hd1)
          simpa using this))
    have hsplit : (algebraMap (𝓞 K) K) (n - d)
        = algebraMap (𝓞 K) K d * ((β : K) - 1) := by
      rw [map_sub, hn]; ring
    rw [hsplit, map_mul, hval_d, one_mul]
    exact hcong v hv
  have hn1 : n - 1 ∈ 𝔣 := by
    have : n - 1 = (n - d) + (d - 1) := by ring
    rw [this]; exact add_mem hnd1 hd1

  have hn0' : (algebraMap (𝓞 K) K) n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hn0
  have hsgn : ∀ τ : K →+* ℝ, (0 < τ (algebraMap (𝓞 K) K n))
      ↔ (0 < τ (algebraMap (𝓞 K) K d)) := by
    intro τ
    have hτβ : 0 < τ (β : K) := hsign τ
    rw [show (algebraMap (𝓞 K) K) n = (algebraMap (𝓞 K) K) d * (β : K) from hn,
      map_mul]
    refine ⟨fun h => ?_, fun h => mul_pos h hτβ⟩
    exact ((mul_pos_iff.mp h).resolve_right fun ⟨_, hb⟩ => hb.not_gt hτβ).1

  set yn : ↥(coprimeToModulus K 𝔣) :=
    ⟨principalUnit K n hn0, principalUnit_mem_coprimeToModulus K hn0 hn1⟩ with hyn_def
  set yd : ↥(coprimeToModulus K 𝔣) :=
    ⟨principalUnit K d hd0, principalUnit_mem_coprimeToModulus K hd0 hd1⟩ with hyd_def
  have hyn_val : ((yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = ((Ideal.span {n} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) :=
    principalUnit_val K n hn0
  have hyd_val : ((yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = ((Ideal.span {d} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) :=
    principalUnit_val K d hd0

  have hyd2 : ((yd * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈
      narrowRaySubgroup K 𝔣 :=
    Subgroup.subset_closure (mul_mem_narrowRaySet_of_sameSign K hd0 hd1 hyd_val hd0 hd1 hyd_val
      fun _ => Iff.rfl)
  have hynyd : ((yn * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈
      narrowRaySubgroup K 𝔣 :=
    Subgroup.subset_closure (mul_mem_narrowRaySet_of_sameSign K hn0 hn1 hyn_val hd0 hd1 hyd_val
      hsgn)

  have hβnd' : toPrincipalIdeal (𝓞 K) K β * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)
      = (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := by
    refine Units.ext ?_
    rw [Units.val_mul, hyn_val, hyd_val, coe_toPrincipalIdeal,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton, mul_comm, hn]
  have hβnd : toPrincipalIdeal (𝓞 K) K β
      = (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)⁻¹ :=
    eq_mul_inv_of_mul_eq hβnd'

  rw [hβnd]
  have hrw : (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)⁻¹
      = (((yd * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))⁻¹
        * ((yn * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc,
      show ((yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))⁻¹
          * ((yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))
        = (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) from by
          rw [mul_comm (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) _, ← mul_assoc, inv_mul_cancel,
            one_mul],
      mul_comm]
  rw [hrw]
  exact mul_mem (inv_mem hyd2) hynyd

private theorem mk_eq_mk_of_isAdjuster {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {u : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u α') :
    NarrowRayClassGroup.mk K 𝔣 ⟨_, hα.coprime⟩
      = NarrowRayClassGroup.mk K 𝔣 ⟨_, hα'.coprime⟩ := by
  rw [NarrowRayClassGroup.mk_eq_mk_iff]
  show (fadContentHom K (projFin K _))⁻¹ * fadContentHom K (projFin K _) ∈ _
  rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, adj_adele_ratio K u α α',
    projFin_principal, fadContentHom_unitEmbedding]
  exact toPrincipalIdeal_mem_narrowRaySubgroup K h𝔣 (α * α'⁻¹)
    (fun v hv => valuation_ratio_sub_one_le K hα hα' v hv)
    (fun τ => ratio_totally_positive K hα hα' τ)

end Adjusters

end HeckeCharacter

end

end IdeleContentBuild

section MixedApprox

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain AbsoluteValue"
open Filter Topology

namespace NumberField
p2m_export "NumberField" "FinitePlace ComplexEmbedding.isReal_iff InfinitePlace.mk_embedding FinitePlace.norm_lt_one_iff_mem FinitePlace.mk InfinitePlace.embedding_of_isReal_apply RingOfIntegers.mapRingHom InfinitePlace.IsReal InfinitePlace.map_natCast of_module_finite mk InfinitePlace.mk_eq_iff InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe FinitePlace.norm_eq_one_iff_notMem InfinitePlace.embedding_mk_eq_of_isReal RingOfIntegers.not_isField InfinitePlace.mk InfinitePlace.denseRange_algebraMap_pi AdeleRing.algebraMap_fst_apply InfinitePlace.Completion FinitePlace.norm_embedding InfinitePlace.embedding_of_isReal HeightOneSpectrum.adicAbv InfinitePlace.eq_iff_isEquiv RingOfIntegers RingOfIntegers.basis HeightOneSpectrum.adicAbv_def HeightOneSpectrum.adicAbv_natCast_le_one InfinitePlace.isReal_iff InfinitePlace.apply ComplexEmbedding.IsReal InfinitePlace ComplexEmbedding.conjugate AdeleRing FinitePlace.embedding_apply InfinitePlace.mk_conjugate_eq HeightOneSpectrum.one_lt_absNorm_nnreal InfinitePlace.Completion.ringEquivRealOfIsReal_apply InfinitePlace.isNontrivial InfinitePlace.coe_apply RingOfIntegers.ext FinitePlace.mk_apply FinitePlace.embedding ComplexEmbedding.conjugate_coe_eq PrimeNormIndex.IsAdmissibleModulusAt PrimeNormIndex.secondInequalityCTM_of_primitiveRoots"
p2m_open "NumberField"

variable (K : Type*) [Field K] [NumberField K]

namespace FinitePlace p2m_export "NumberField.FinitePlace" "norm_lt_one_iff_mem mk coe_apply norm_eq_one_iff_notMem mk_eq_iff pos_iff norm_embedding embedding_apply mk_apply embedding" end FinitePlace
namespace FinitePlace
p2m_open_scoped "NumberField.FinitePlace" in
private theorem _root_.NumberField.FinitePlace.isNontrivial (v : HeightOneSpectrum (𝓞 K)) :
    (FinitePlace.mk v).1.IsNontrivial := by
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ v.asIdeal, x ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr v.ne_bot)
    exact ⟨x, hx, fun h => hx0 (h ▸ Ideal.zero_mem _)⟩
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hx0
  · show (FinitePlace.mk v).1 (algebraMap (𝓞 K) K x) ≠ 1
    rw [show (FinitePlace.mk v).1 (algebraMap (𝓞 K) K x)
        = ‖FinitePlace.embedding v (algebraMap (𝓞 K) K x)‖ from rfl]
    exact ((FinitePlace.norm_lt_one_iff_mem K v x).mpr hx).ne

end FinitePlace
p2m_export "NumberField" "FinitePlace.isNontrivial"
p2m_open_scoped "NumberField.FinitePlace" in
private theorem FinitePlace.not_isEquiv_of_ne {v₁ v₂ : HeightOneSpectrum (𝓞 K)} (h : v₁ ≠ v₂) :
    ¬ (FinitePlace.mk v₁).1.IsEquiv (FinitePlace.mk v₂).1 := by
  rw [isEquiv_iff_lt_one_iff]
  push Not
  have ⟨x, hx1, hx2⟩ : ∃ x : 𝓞 K, x ∈ v₁.asIdeal ∧ x ∉ v₂.asIdeal := by
    by_contra! H
    exact h (HeightOneSpectrum.ext_iff.mpr
      (Ideal.IsMaximal.eq_of_le (HeightOneSpectrum.isMaximal v₁) Ideal.IsPrime.ne_top' H))
  refine ⟨algebraMap (𝓞 K) K x, ?_⟩
  rw [show ((FinitePlace.mk v₁).1 : K → ℝ) = fun y => ‖FinitePlace.embedding v₁ y‖ from rfl,
    show ((FinitePlace.mk v₂).1 : K → ℝ) = fun y => ‖FinitePlace.embedding v₂ y‖ from rfl]
  simp only
  exact Or.inl ⟨(FinitePlace.norm_lt_one_iff_mem K v₁ x).mpr hx1,
    ((FinitePlace.norm_eq_one_iff_notMem K v₂ x).mpr hx2).ge⟩

namespace InfinitePlace p2m_export "NumberField.InfinitePlace" "mk_embedding embedding_of_isReal_apply IsReal smul_apply mk_eq_iff Completion.extensionEmbeddingOfIsReal_coe embedding_mk_eq_of_isReal mk denseRange_algebraMap_pi Completion embedding_of_isReal eq_iff_isEquiv ext comap pos_iff isReal_iff apply embedding mk_conjugate_eq Completion.ringEquivRealOfIsReal_apply isNontrivial coe_apply le_iff_le" end InfinitePlace
p2m_open_scoped "NumberField.InfinitePlace" in
private theorem InfinitePlace.not_isEquiv_finitePlace (w : InfinitePlace K)
    (v : HeightOneSpectrum (𝓞 K)) :
    ¬ w.1.IsEquiv (FinitePlace.mk v).1 := by
  intro hequiv
  have hw2 : ¬ w.1 (2 : K) ≤ 1 := by
    have : (2 : K) = ((2 : ℕ) : K) := by norm_num
    rw [← InfinitePlace.coe_apply, this, InfinitePlace.map_natCast w 2]
    norm_num
  have hv2 : (FinitePlace.mk v).1 (2 : K) ≤ 1 := by
    show ‖FinitePlace.embedding v (2 : K)‖ ≤ 1
    have : (2 : K) = ((2 : ℕ) : K) := by norm_num
    rw [FinitePlace.norm_embedding, this]
    exact HeightOneSpectrum.adicAbv_natCast_le_one K v 2
  exact hw2 (hequiv.le_one_iff.mpr hv2)

private noncomputable def mixedAbs (S : Finset (HeightOneSpectrum (𝓞 K))) :
    InfinitePlace K ⊕ ↥S → AbsoluteValue K ℝ :=
  Sum.elim (·.1) (fun v => (FinitePlace.mk v.1).1)

private theorem mixedAbs_isNontrivial (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : InfinitePlace K ⊕ ↥S) : (mixedAbs K S i).IsNontrivial := by
  rcases i with w | v
  · exact InfinitePlace.isNontrivial w
  · exact FinitePlace.isNontrivial K v.1

private theorem mixedAbs_pairwise_not_isEquiv (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Pairwise fun i j => ¬ (mixedAbs K S i).IsEquiv (mixedAbs K S j) := by
  intro i j hij
  match i, j with
  | Sum.inl w, Sum.inl w' =>
    exact (InfinitePlace.eq_iff_isEquiv (K := K)).not.mp (by simpa using hij)
  | Sum.inl w, Sum.inr v => exact InfinitePlace.not_isEquiv_finitePlace K w v.1
  | Sum.inr v, Sum.inl w =>
    exact fun h => InfinitePlace.not_isEquiv_finitePlace K w v.1 h.symm
  | Sum.inr v, Sum.inr v' =>
    exact FinitePlace.not_isEquiv_of_ne K (by simpa using hij)

private theorem denseRange_algebraMap_pi_mixedAbs (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (algebraMap K ((i : InfinitePlace K ⊕ ↥S) → WithAbs (mixedAbs K S i))) := by
  classical
  refine Metric.denseRange_iff.mpr fun z r hr ↦ ?_
  choose a hx using AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv
    (mixedAbs_isNontrivial K S) (mixedAbs_pairwise_not_isEquiv K S)
  let y := fun n ↦
    ∑ i, (1 / (1 + (a i)⁻¹ ^ n)) * WithAbs.equiv (mixedAbs K S i) (z i)
  have htend : Filter.atTop.Tendsto
      (fun n i ↦ (WithAbs.equiv (mixedAbs K S i)).symm (y n)) (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun u ↦ ?_
    simp_rw [← Fintype.sum_pi_single u z, y, map_sum, map_mul]
    refine tendsto_finsetSum _ fun w _ ↦ ?_
    by_cases hw : u = w
    · rw [← hw, Pi.single_eq_same]
      have : mixedAbs K S u (a u)⁻¹ < 1 := by
        simpa [← inv_pow, inv_lt_one_iff₀] using .inr (hx u).1
      simpa using (WithAbs.tendsto_one_div_one_add_pow_nhds_one this).mul_const (z u)
    · rw [Pi.single_eq_of_ne (M := fun i ↦ WithAbs (mixedAbs K S i)) hw (z w)]
      have haw0 : a w ≠ 0 := fun ha => by
        have := (hx w).1; rw [ha, map_zero] at this; linarith
      have hu : 1 < mixedAbs K S u (a w)⁻¹ := by
        rw [map_inv₀, one_lt_inv_iff₀]
        exact ⟨(mixedAbs K S u).pos_iff.2 haw0, (hx w).2 u hw⟩
      have := (mixedAbs K S u).tendsto_div_one_add_pow_nhds_zero hu
      simp_rw [← WithAbs.norm_toAbs_eq] at this
      simpa using (tendsto_zero_iff_norm_tendsto_zero.2 this).mul_const
        ((WithAbs.equiv (mixedAbs K S u)).symm (WithAbs.equiv (mixedAbs K S w) (z w)))
  let ⟨N, h⟩ := Metric.tendsto_atTop.1 htend r hr
  exact ⟨y N, dist_comm z (algebraMap K _ (y N)) ▸ h N le_rfl⟩

private theorem denseRange_algebraMap_pi_mixedAbs_empty :
    DenseRange (algebraMap K ((w : InfinitePlace K) → WithAbs w.1)) :=
  InfinitePlace.denseRange_algebraMap_pi K

end NumberField

end MixedApprox

section ExistsAdjuster

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

private theorem isometry_finitePlaceEmbedding_withAbs (v : HeightOneSpectrum (𝓞 K)) :
    Isometry (fun x : WithAbs (FinitePlace.mk v).1 =>
      FinitePlace.embedding v (WithAbs.equiv (FinitePlace.mk v).1 x)) := by
  refine Isometry.of_dist_eq (fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← map_sub (FinitePlace.embedding v),
    show WithAbs.equiv _ x - WithAbs.equiv _ y
      = WithAbs.ofAbs (v := (FinitePlace.mk v).1) (x - y) from (WithAbs.ofAbs_sub _ _ _).symm]
  exact (FinitePlace.mk_apply v (WithAbs.ofAbs (x - y))).symm

private theorem valuation_le_of_adicAbv_le (v : HeightOneSpectrum (𝓞 K)) {x y : K}
    (h : NumberField.HeightOneSpectrum.adicAbv K v x
      ≤ NumberField.HeightOneSpectrum.adicAbv K v y) :
    v.valuation K x ≤ v.valuation K y := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, NumberField.HeightOneSpectrum.adicAbv_def] at h
  exact (WithZeroMulInt.toNNReal_strictMono
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le.mp
    (by exact_mod_cast h)

private theorem sign_eq_of_withAbs_dist_lt (τ : K →+* ℝ) (α t : K) (ht : t ≠ 0)
    (h : (placeOf K τ).1 (α - t) < (placeOf K τ).1 t) :
    (0 < τ α ↔ 0 < τ t) := by

  have hval : ∀ x : K, (placeOf K τ).1 x = |τ x| := by
    intro x
    rw [← InfinitePlace.coe_apply]
    show (InfinitePlace.mk (Complex.ofRealHom.comp τ)) x = |τ x|
    rw [InfinitePlace.apply, RingHom.comp_apply, Complex.ofRealHom_eq_coe,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hval, hval, map_sub] at h

  have ht0 : τ t ≠ 0 := fun h0 => ht ((map_eq_zero τ).mp h0)
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · refine ⟨fun hα => absurd ?_ (not_lt.mpr hα.le), fun hα => absurd hα hneg.not_gt⟩
    calc τ α = τ t + (τ α - τ t) := by ring
      _ < 0 := by
        have := abs_lt.mp h
        linarith [abs_of_neg hneg ▸ this.2]
  · refine ⟨fun _ => hpos, fun _ => ?_⟩
    calc (0 : ℝ) < τ t - |τ α - τ t| := by linarith [abs_of_pos hpos ▸ h]
      _ ≤ τ t - (τ t - τ α) := by linarith [neg_abs_le (τ α - τ t)]
      _ = τ α := by ring

private noncomputable def primesOf (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot])).toFinset

private theorem mem_primesOf {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ primesOf K 𝔣 h𝔣 ↔ v.asIdeal ∣ 𝔣 :=
  Set.Finite.mem_toFinset _

private noncomputable def fadComp (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K :=
  ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v

private theorem fadComp_ne_zero (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    fadComp K u v ≠ 0 := by
  intro h
  exact valued_ne_zero_of_unit K (projFin K u) v (by rw [projFin_val, ← fadComp, h, map_zero])

private theorem archRealProjTau_principal (τ : K →+* ℝ) (α : Kˣ) :
    archRealProjTau K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) = τ (α : K) := by
  unfold archRealProjTau
  rw [Units.coe_map, MonoidHom.coe_coe, AdeleRing.algebraMap_fst_apply,
    InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, embedding_of_isReal_placeOf]
  rfl

private theorem exists_embedding_near_fadComp (u : (AdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : K, ‖FinitePlace.embedding v t - fadComp K u v‖ < ε := by
  obtain ⟨t, ht⟩ := Metric.denseRange_iff.mp (v.denseRange_algebraMap K) (fadComp K u v) ε hε
  exact ⟨t, by rw [FinitePlace.embedding_apply]; rwa [dist_comm, dist_eq_norm] at ht⟩

private theorem cong_of_completion_close {v : HeightOneSpectrum (𝓞 K)} {α : K} {U : v.adicCompletion K}
    (hU : U ≠ 0) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (h : ‖FinitePlace.embedding v α - U‖ < ‖U‖ * δ) :
    ‖U * (FinitePlace.embedding v α)⁻¹‖ = 1 ∧
    ‖U * (FinitePlace.embedding v α)⁻¹ - 1‖ ≤ δ := by
  set αv := FinitePlace.embedding v α with hαv
  have hUpos : 0 < ‖U‖ := norm_pos_iff.mpr hU
  have hlt : ‖αv - U‖ < ‖U‖ :=
    h.trans_le (by nlinarith)
  have hαeq : ‖αv‖ = ‖U‖ := by
    have hne : ‖U‖ ≠ ‖αv - U‖ := (hlt.trans_le (le_refl _)).ne'
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := U) (y := αv - U) hne
    rw [add_sub_cancel, max_eq_left hlt.le] at this
    exact this
  have hα0 : αv ≠ 0 := fun h0 => by simp [h0] at hαeq; exact hU (norm_eq_zero.mp hαeq.symm)
  refine ⟨?_, ?_⟩
  · rw [norm_mul, norm_inv, hαeq, mul_inv_cancel₀ hUpos.ne']
  · have hfac : U * αv⁻¹ - 1 = (U - αv) * αv⁻¹ := by
      field_simp
    rw [hfac, norm_mul, norm_inv, hαeq, norm_sub_rev]
    calc ‖αv - U‖ * ‖U‖⁻¹ ≤ (‖U‖ * δ) * ‖U‖⁻¹ := by
          exact mul_le_mul_of_nonneg_right h.le (inv_nonneg.mpr hUpos.le)
      _ = δ := by field_simp

private theorem adjCompEq (u : (AdeleRing (𝓞 K) K)ˣ) (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v
      = fadComp K u v * (FinitePlace.embedding v (α : K))⁻¹ := by
  have hmul : ((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
      = (u : AdeleRing (𝓞 K) K).2
        * (((Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 := by
    rw [Units.val_mul]; rfl
  rw [hmul, fad_mul_apply K, ← fadComp]
  congr 1
  rw [← map_inv, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val,
    FinitePlace.embedding_apply]
  show ((algebraMap K (AdeleRing (𝓞 K) K)) ((α : K)⁻¹)).2 v = _
  rw [show ∀ x : K, ((algebraMap K (AdeleRing (𝓞 K) K)) x).2 v
      = algebraMap K (v.adicCompletion K) x from fun x => rfl,
    map_inv₀]
  rfl

private theorem valued_cong_of_norm_cong {v : HeightOneSpectrum (𝓞 K)} {X Y : v.adicCompletion K}
    (h1 : ‖X‖ = 1) (h2 : ‖X - 1‖ ≤ ‖Y‖) :
    Valued.v X = 1 ∧ Valued.v (X - 1) ≤ Valued.v Y := by
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · exact (Valued.toNormedField.norm_le_one_iff).mp h1.le
  · exact (Valued.toNormedField.one_le_norm_iff).mp h1.ge
  · exact (Valued.toNormedField.norm_le_iff).mp h2

private theorem exists_isAdjuster {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (u : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ α : Kˣ, IsAdjuster K 𝔣 u α := by
  classical
  set S := primesOf K 𝔣 h𝔣 with hS

  obtain ⟨γ, hγ𝔣, hγ0⟩ : ∃ γ : 𝓞 K, γ ∈ 𝔣 ∧ γ ≠ 0 := by
    obtain ⟨γ, hγ𝔣, hγ0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr h𝔣)
    exact ⟨γ, hγ𝔣, fun h => hγ0 (h ▸ Ideal.zero_mem ⊥)⟩
  have hγK0 : (γ : K) ≠ 0 := by exact_mod_cast hγ0

  have hγemb_ne : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.embedding v (γ : K) ≠ 0 :=
    fun v => (map_ne_zero _).mpr hγK0
  have hγnorm_pos : ∀ v : HeightOneSpectrum (𝓞 K), 0 < ‖FinitePlace.embedding v (γ : K)‖ :=
    fun v => norm_pos_iff.mpr (hγemb_ne v)
  have hγnorm_le_one : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖FinitePlace.embedding v (γ : K)‖ ≤ 1 := by
    intro v
    rw [Valued.toNormedField.norm_le_one_iff,
      show FinitePlace.embedding v (γ : K) = ((γ : K) : v.adicCompletion K) from rfl,
      v.valuedAdicCompletion_eq_valuation']
    exact v.valuation_le_one γ
  have hγval_le : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v (FinitePlace.embedding v (γ : K))
        ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)) := by
    intro v _
    rw [show FinitePlace.embedding v (γ : K) = ((γ : K) : v.adicCompletion K) from rfl,
      v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]
    refine (v.intValuation_le_pow_iff_dvd γ _).mpr
      (dvd_trans ?_ ((Ideal.dvd_iff_le).mpr
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hγ𝔣))))
    have h𝔣0 : (Associates.mk 𝔣) ≠ 0 :=
      Associates.mk_ne_zero.mpr (by rwa [Ne, Ideal.zero_eq_bot])
    have hirr := Associates.irreducible_mk.mpr v.irreducible
    have := (Associates.prime_pow_dvd_iff_le h𝔣0 hirr
        (k := idealMultiplicity K v 𝔣)).mpr le_rfl
    rwa [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at this

  have hUpos : ∀ v : HeightOneSpectrum (𝓞 K), 0 < ‖fadComp K u v‖ :=
    fun v => norm_pos_iff.mpr (fadComp_ne_zero K u v)

  set bnd : HeightOneSpectrum (𝓞 K) → ℝ :=
    fun v => ‖fadComp K u v‖ * ‖FinitePlace.embedding v (γ : K)‖ with hbnd
  have hbnd_pos : ∀ v, 0 < bnd v := fun v => mul_pos (hUpos v) (hγnorm_pos v)
  obtain ⟨r, hr0, hr1, hrS⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ v ∈ S, r < bnd v := by
    by_cases hne : S.Nonempty
    · have hm_pos : 0 < S.inf' hne bnd :=
        (Finset.lt_inf'_iff hne).mpr (fun v _ => hbnd_pos v)
      refine ⟨min (1/2) (S.inf' hne bnd / 2), ?_, ?_, ?_⟩
      · exact lt_min (by norm_num) (by linarith)
      · exact (min_le_left _ _).trans_lt (by norm_num)
      · intro v hv
        refine (min_le_right _ _).trans_lt ?_
        have hle := Finset.inf'_le bnd hv
        linarith [hbnd_pos v]
    · exact ⟨1/2, by norm_num, by norm_num, fun v hv => absurd ⟨v, hv⟩ hne⟩

  have htv : ∀ v ∈ S, ∃ t : K, ‖FinitePlace.embedding v t - fadComp K u v‖ < r :=
    fun v _ => exists_embedding_near_fadComp K u v hr0
  choose tv htv using htv

  set archTgt : InfinitePlace K → K := fun w =>
    if hw : w.IsReal then
      (if archSign K (InfinitePlace.embedding_of_isReal hw) u then (1:K) else (-1:K))
    else (1:K) with harchTgt
  have harchTgt_ne : ∀ w, archTgt w ≠ 0 := by
    intro w; unfold archTgt; split_ifs
    · exact one_ne_zero
    · exact neg_ne_zero.mpr one_ne_zero
    · exact one_ne_zero
  have harchTgt_abs : ∀ w : InfinitePlace K, w (archTgt w) = 1 := by
    intro w; unfold archTgt; split_ifs
    · exact map_one _
    · exact (w.1.map_neg 1).trans (map_one _)
    · exact map_one _

  set z : InfinitePlace K ⊕ ↥S → K := Sum.elim archTgt (fun v => tv v.1 v.2) with hz

  obtain ⟨α, hα⟩ := Metric.denseRange_iff.mp
    (NumberField.denseRange_algebraMap_pi_mixedAbs K S)
    (fun i => (WithAbs.equiv (NumberField.mixedAbs K S i)).symm (z i)) r hr0
  have hα_at : ∀ i, (NumberField.mixedAbs K S i) (α - z i) < r := by
    intro i
    have hi := (dist_pi_lt_iff hr0).mp hα i
    rw [dist_comm, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub] at hi
    convert hi using 2
    all_goals first | rfl | simp

  have hα0 : α ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
    intro h
    have := hα_at (Sum.inl w)
    simp only [hz, Sum.elim_inl, h, zero_sub] at this
    have heq : (NumberField.mixedAbs K S (Sum.inl w)) (-archTgt w) = 1 := by
      change (w.1 : AbsoluteValue K ℝ) (-archTgt w) = 1
      rw [(w.1).map_neg, ← InfinitePlace.coe_apply, harchTgt_abs w]
    rw [heq] at this; linarith
  refine ⟨Units.mk0 α hα0, ?_, ?_⟩
  ·
    intro v hv
    have hvS : v ∈ S := (mem_primesOf K h𝔣 v).mpr hv
    rw [adjCompEq K u (Units.mk0 α hα0) v, Units.val_mk0]

    have hstep : ‖FinitePlace.embedding v α - fadComp K u v‖
        < ‖fadComp K u v‖ * ‖FinitePlace.embedding v (γ : K)‖ := by
      have hα_fin := hα_at (Sum.inr ⟨v, hvS⟩)
      simp only [hz, Sum.elim_inr, NumberField.mixedAbs] at hα_fin

      have h1 : ‖FinitePlace.embedding v α - FinitePlace.embedding v (tv v hvS)‖ < r := by
        rw [← map_sub]; exact hα_fin
      have h2 := htv v hvS
      calc ‖FinitePlace.embedding v α - fadComp K u v‖
          ≤ max ‖FinitePlace.embedding v α - FinitePlace.embedding v (tv v hvS)‖
              ‖FinitePlace.embedding v (tv v hvS) - fadComp K u v‖ := by
            rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
            exact IsUltrametricDist.dist_triangle_max _ _ _
        _ < r := max_lt h1 h2
        _ < bnd v := hrS v hvS
    have hcong := cong_of_completion_close K (fadComp_ne_zero K u v)
      (hγnorm_pos v) (hγnorm_le_one v) hstep
    have hbr := valued_cong_of_norm_cong K hcong.1 hcong.2
    exact ⟨hbr.1, hbr.2.trans (hγval_le v hv)⟩
  ·
    intro τ
    rw [archSign_mul K τ, archSign_inv K τ]
    show archSign K τ u ↔ archSign K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.mk0 α hα0))
    unfold archSign
    rw [archRealProjTau_principal K τ (Units.mk0 α hα0), Units.val_mk0]

    have hwτ := isReal_placeOf K τ
    have htgt_τ : archTgt (placeOf K τ)
        = if (0:ℝ) < archRealProjTau K τ u then (1:K) else (-1:K) := by
      unfold archTgt; rw [dif_pos hwτ]
      congr 1
      · unfold archSign
        rw [show InfinitePlace.embedding_of_isReal hwτ = τ from embedding_of_isReal_placeOf K τ]
    have habs_tgt : (placeOf K τ) (archTgt (placeOf K τ)) = 1 := harchTgt_abs _
    have hclose : (placeOf K τ) (α - archTgt (placeOf K τ)) < (placeOf K τ) (archTgt (placeOf K τ)) := by
      rw [habs_tgt]
      have := hα_at (Sum.inl (placeOf K τ))
      simp only [hz, Sum.elim_inl, NumberField.mixedAbs] at this
      exact this.trans hr1
    have hsign_iff := sign_eq_of_withAbs_dist_lt K τ α (archTgt (placeOf K τ))
      (harchTgt_ne _) hclose
    constructor
    · intro hpos
      refine hsign_iff.mpr ?_
      rw [htgt_τ, if_pos hpos, map_one]; exact one_pos
    · intro hτα
      by_contra hneg
      have hlt : (0:ℝ) < -1 := by
        have := hsign_iff.mp hτα
        rwa [htgt_τ, if_neg hneg, map_neg, map_one] at this
      linarith

end HeckeCharacter

end ExistsAdjuster

section IdeleContent

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain Deep.NTSupply WithZero"
open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

private def ideleContentHom (𝔣 : Ideal (𝓞 K)) :
    (AdeleRing (𝓞 K) K)ˣ →* NarrowRayClassGroup K 𝔣 := by
  classical
  by_cases h𝔣 : 𝔣 = ⊥
  · exact 1
  · exact
      { toFun := fun u => NarrowRayClassGroup.mk K 𝔣
          ⟨_, (Classical.choose_spec (exists_isAdjuster K h𝔣 u)).coprime⟩
        map_one' := by
          rw [mk_eq_mk_of_isAdjuster K h𝔣
            (Classical.choose_spec (exists_isAdjuster K h𝔣 1)) (isAdjuster_one_one K 𝔣)]
          simp only [map_one, inv_one, mul_one]; rfl
        map_mul' := fun u u' => by
          have hαu := Classical.choose_spec (exists_isAdjuster K h𝔣 u)
          have hαu' := Classical.choose_spec (exists_isAdjuster K h𝔣 u')
          have hαuu' : IsAdjuster K 𝔣 (u * u') (_ * _) := IsAdjuster.mul K hαu hαu'
          rw [mk_eq_mk_of_isAdjuster K h𝔣
              (Classical.choose_spec (exists_isAdjuster K h𝔣 (u * u'))) hαuu',
            ← (NarrowRayClassGroup.mk K 𝔣).map_mul ⟨_, hαu.coprime⟩ ⟨_, hαu'.coprime⟩]
          refine congrArg (NarrowRayClassGroup.mk K 𝔣) (Subtype.ext ?_)
          show fadContentHom K (projFin K _) = fadContentHom K (projFin K _)
            * fadContentHom K (projFin K _)
          rw [← map_mul, ← map_mul, adj_adele_mul K u u'] }

private theorem ideleContentHom_apply {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {u : (AdeleRing (𝓞 K) K)ˣ} {α : Kˣ} (hα : IsAdjuster K 𝔣 u α) :
    ideleContentHom K 𝔣 u = NarrowRayClassGroup.mk K 𝔣 ⟨_, hα.coprime⟩ := by
  unfold ideleContentHom
  rw [dif_neg h𝔣]
  exact mk_eq_mk_of_isAdjuster K h𝔣 (Classical.choose_spec (exists_isAdjuster K h𝔣 u)) hα

private theorem ideleContentHom_principal (𝔣 : Ideal (𝓞 K)) (α : Kˣ) :
    ideleContentHom K 𝔣 (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) = 1 := by
  by_cases h𝔣 : 𝔣 = ⊥
  · unfold ideleContentHom; rw [dif_pos h𝔣]; rfl
  · rw [ideleContentHom_apply K h𝔣 (isAdjuster_principal_self K 𝔣 α)]
    have h1 : fadContentHom K (projFin K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α
        * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)) = 1 := by
      rw [mul_inv_cancel, map_one, map_one]
    rw [show (⟨_, (isAdjuster_principal_self K 𝔣 α).coprime⟩ : ↥(coprimeToModulus K 𝔣)) = 1
      from Subtype.ext h1, map_one]

private theorem ideleContentHom_uniformizerIdele_v2 (𝔣 : Ideal (𝓞 K))
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (huarch : (u : AdeleRing (𝓞 K) K).1 = 1)
    (huw : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v →
      Valued.v ((u : AdeleRing (𝓞 K) K).2 w) = 1)
    (huv : Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = WithZero.exp (-1 : ℤ))
    (hu𝔣 : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ 𝔣 →
      Valued.v ((u : AdeleRing (𝓞 K) K).2 w - 1)
        ≤ WithZero.exp (-(idealMultiplicity K w 𝔣 : ℤ))) :
    ideleContentHom K 𝔣 u = primeClass K 𝔣 v hv := by
  by_cases h𝔣 : 𝔣 = ⊥
  · subst h𝔣; simp only [show v.asIdeal ∣ (⊥ : Ideal (𝓞 K)) from ⟨0, (mul_zero _).symm⟩,
      not_true] at hv
  ·
    have hadj : IsAdjuster K 𝔣 u 1 := by
      refine ⟨fun w hw𝔣 => ?_, fun τ => ?_⟩
      · have hwv : w ≠ v := fun h => hv (h ▸ hw𝔣)
        show Valued.v (adjFinV K u 1 w) = 1 ∧ Valued.v (adjFinV K u 1 w - 1) ≤ _
        have hu1 : adjFinV K u 1 w = (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K)
            w) := by unfold adjFinV; simp only [map_one, inv_one, mul_one]
        rw [hu1]
        exact ⟨huw w hwv, hu𝔣 w hw𝔣⟩
      · simp only [map_one, inv_one, mul_one]
        exact archSign_of_fst_eq_one K τ huarch
    rw [ideleContentHom_apply K h𝔣 hadj]

    refine congrArg (NarrowRayClassGroup.mk K 𝔣) (Subtype.ext ?_)
    show fadContentHom K (projFin K (u * (pK K 1)⁻¹)) = primeUnit K v
    rw [map_one, inv_one, mul_one, fadContentHom_apply]
    refine finprod_eq_single (fun w => primeUnit K w ^ placeOrd K (projFin K u) w) v
      ?_ |>.trans ?_
    · intro w hwv
      show primeUnit K w ^ placeOrd K (projFin K u) w = 1
      rw [show placeOrd K (projFin K u) w = 0 from
        (placeOrd_eq_zero_iff K (projFin K u) w).mpr (projFin_val K u ▸ huw w hwv), zpow_zero]
    · show primeUnit K v ^ placeOrd K (projFin K u) v = primeUnit K v
      rw [show placeOrd K (projFin K u) v = 1 from by
        unfold placeOrd; rw [projFin_val, huv, WithZero.log_exp, neg_neg], zpow_one]

end HeckeCharacter

end

end IdeleContent

section ServedNorm

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.HeckeCharacter WithZero"
open scoped nonZeroDivisors

noncomputable section

namespace M4aKummer

section Gen

variable (K : Type*) [Field K] [NumberField K]

private def primeGens (𝔣 : Ideal (𝓞 K)) : Set (FractionalIdeal ((𝓞 K)⁰) K)ˣ :=
  {I | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 ∧ I = primeUnit K v}

private theorem closure_primeGens_le (𝔣 : Ideal (𝓞 K)) : Subgroup.closure (primeGens K 𝔣) ≤ coprimeToModulus K 𝔣 :=
  (Subgroup.closure_le _).mpr (by rintro _ ⟨v, hv, rfl⟩; exact primeUnit_mem_coprimeToModulus K hv)

omit [NumberField K] in

private theorem val_finprod {ι α : Type*} [CommMonoid α] (f : ι → αˣ) (hf : Function.HasFiniteMulSupport f) :
    (((∏ᶠ i, f i : αˣ)) : α) = ∏ᶠ i, (f i : α) :=
  MonoidHom.map_finprod (Units.coeHom α) hf

private theorem finprod_primeUnit_zpow_count (I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeUnit K v ^ FractionalIdeal.count K v (I : FractionalIdeal ((𝓞 K)⁰) K) = I := by
  apply Units.ext
  rw [val_finprod _ (hasFiniteMulSupport_raySymbol_factors K (primeUnit K) _)]
  simp only [Units.val_zpow_eq_zpow_val, primeUnit_val]
  exact FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero

private theorem coprimeToModulus_le_closure (𝔣 : Ideal (𝓞 K)) :
    coprimeToModulus K 𝔣 ≤ Subgroup.closure (primeGens K 𝔣) := by
  intro I hI
  rw [← finprod_primeUnit_zpow_count K I]
  refine finprod_induction (· ∈ Subgroup.closure _) (one_mem _) (fun _ _ => mul_mem) fun v => ?_
  by_cases hv : v.asIdeal ∣ 𝔣
  · rw [(mem_coprimeToModulus_iff (K := K)).mp hI v hv, zpow_zero]
    exact one_mem _
  · exact zpow_mem (Subgroup.subset_closure (show primeUnit K v ∈ primeGens K 𝔣 from ⟨v, hv, rfl⟩)) _

private theorem closure_primeCarriers_eq_top (𝔣 : Ideal (𝓞 K)) :
    Subgroup.closure {c : ↥(coprimeToModulus K 𝔣) | ∃ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣),
      c = ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩} = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨I, hI⟩ -
  have key : ∀ J ∈ Subgroup.closure (primeGens K 𝔣), ∀ hJ : J ∈ coprimeToModulus K 𝔣,
      (⟨J, hJ⟩ : ↥(coprimeToModulus K 𝔣)) ∈ Subgroup.closure {c : ↥(coprimeToModulus K 𝔣) |
        ∃ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣), c = ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩} := by
    intro J hJ
    refine Subgroup.closure_induction (p := fun J (_ : J ∈ Subgroup.closure (primeGens K 𝔣)) =>
      ∀ hJ : J ∈ coprimeToModulus K 𝔣, (⟨J, hJ⟩ : ↥(coprimeToModulus K 𝔣)) ∈ Subgroup.closure _) ?_ ?_ ?_ ?_ hJ
    · rintro _ ⟨v, hv, rfl⟩ hJ
      exact Subgroup.subset_closure ⟨v, hv, rfl⟩
    · intro _
      exact one_mem _
    · intro a b ha hb iha ihb hab
      have hmul : (⟨a * b, hab⟩ : ↥(coprimeToModulus K 𝔣))
          = ⟨a, closure_primeGens_le K 𝔣 ha⟩ * ⟨b, closure_primeGens_le K 𝔣 hb⟩ := rfl
      rw [hmul]
      exact mul_mem (iha _) (ihb _)
    · intro a ha iha hainv
      have hinv : (⟨a⁻¹, hainv⟩ : ↥(coprimeToModulus K 𝔣)) = ⟨a, closure_primeGens_le K 𝔣 ha⟩⁻¹ := rfl
      rw [hinv]
      exact inv_mem (iha _)
  exact key I (coprimeToModulus_le_closure K 𝔣 hI) hI

end Gen

section Uniformizer

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private def unifAt : v.adicCompletion K := ((v.valuation_exists_uniformizer K).choose : K)

private theorem valued_unifAt : Valued.v (unifAt K v) = exp (-1 : ℤ) := by
  unfold unifAt
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (v.valuation_exists_uniformizer K).choose_spec

private theorem unifAt_ne_zero : unifAt K v ≠ 0 := fun h => by
  have h1 := valued_unifAt K v
  rw [h, map_zero] at h1
  exact exp_ne_zero h1.symm

private theorem isUnit_mulSingle (x : v.adicCompletion K) (hx : x ≠ 0) [DecidableEq (HeightOneSpectrum (𝓞 K))] :
    IsUnit (show FiniteAdeleRing (𝓞 K) K from
      RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v x) := by
  rw [FiniteAdeleRing.isUnit_iff]
  refine ⟨fun w => ?_, ?_⟩
  · show Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x w ≠ 0
    by_cases h : w = v
    · subst h; rw [Pi.mulSingle_eq_same]; exact hx
    · rw [Pi.mulSingle_eq_of_ne h]; exact one_ne_zero
  · filter_upwards [show ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K))) ∈ Filter.cofinite by simp] with w hw
    show Valued.v (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x w) = 1
    rw [Pi.mulSingle_eq_of_ne (by simpa using hw), map_one]

open scoped Classical in

private def uniformizerFad : (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (isUnit_mulSingle K v (unifAt K v) (unifAt_ne_zero K v)).unit

open scoped Classical in
private theorem uniformizerFad_apply (w : HeightOneSpectrum (𝓞 K)) :
    ((uniformizerFad K v : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w =
      Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v (unifAt K v) w := by
  unfold uniformizerFad
  rw [IsUnit.unit_spec]
  rfl

open scoped Classical in
private theorem uniformizerFad_apply_self :
    ((uniformizerFad K v : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = unifAt K v := by
  rw [uniformizerFad_apply, Pi.mulSingle_eq_same]

open scoped Classical in
private theorem uniformizerFad_apply_of_ne {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    ((uniformizerFad K v : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = 1 := by
  rw [uniformizerFad_apply, Pi.mulSingle_eq_of_ne hw]

private def uniformizerIdele : (AdeleRing (𝓞 K) K)ˣ where
  val := (1, (uniformizerFad K v : FiniteAdeleRing (𝓞 K) K))
  inv := (1, ((uniformizerFad K v)⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ))
  val_inv := Prod.ext (one_mul 1) (uniformizerFad K v).mul_inv
  inv_val := Prod.ext (one_mul 1) (uniformizerFad K v).inv_mul

private theorem uniformizerIdele_fst : ((uniformizerIdele K v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl

private theorem uniformizerIdele_snd :
    ((uniformizerIdele K v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = uniformizerFad K v := rfl

private theorem ideleContentHom_uniformizerIdele (𝔣 : Ideal (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    ideleContentHom K 𝔣 (uniformizerIdele K v) = primeClass K 𝔣 v hv := by
  refine ideleContentHom_uniformizerIdele_v2 K 𝔣 hv (uniformizerIdele K v) rfl
    (fun w hw => ?_) ?_ (fun w hw𝔣 => ?_)
  · rw [uniformizerIdele_snd, uniformizerFad_apply_of_ne K v hw, map_one]
  · rw [uniformizerIdele_snd, uniformizerFad_apply_self, valued_unifAt]
  · have hwv : w ≠ v := fun h => hv (h ▸ hw𝔣)
    rw [uniformizerIdele_snd, uniformizerFad_apply_of_ne K v hwv, sub_self, map_zero]
    exact zero_le'

end Uniformizer

section Surj

variable (K : Type*) [Field K] [NumberField K]

private theorem ideleContentHom_surjective (𝔣 : Ideal (𝓞 K)) :
    Function.Surjective (ideleContentHom K 𝔣) := by
  intro x
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ x
  have hc : c ∈ (⊤ : Subgroup ↥(coprimeToModulus K 𝔣)) := Subgroup.mem_top c
  rw [← closure_primeCarriers_eq_top K 𝔣] at hc
  refine Subgroup.closure_induction
    (p := fun c _ => ∃ u, ideleContentHom K 𝔣 u = QuotientGroup.mk' _ c) ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨uniformizerIdele K w, ideleContentHom_uniformizerIdele K w 𝔣 hw⟩
  · exact ⟨1, by rw [map_one, map_one]⟩
  · rintro a b _ _ ⟨u, hu⟩ ⟨u', hu'⟩
    exact ⟨u * u', by rw [map_mul, map_mul, hu, hu']⟩
  · rintro a _ ⟨u, hu⟩
    exact ⟨u⁻¹, by rw [map_inv, map_inv, hu]⟩

private theorem range_ideleContentHom (𝔣 : Ideal (𝓞 K)) : (ideleContentHom K 𝔣).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (ideleContentHom_surjective K 𝔣)

end Surj

section Norm

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private abbrev _root_.M4aKummer.modulusExt (𝔠 : Ideal (𝓞 k)) : Ideal (𝓞 E) := 𝔠.map (algebraMap (𝓞 k) (𝓞 E))

p2m_export "M4aKummer" "modulusExt"
private def fracRelNormUnit : (FractionalIdeal ((𝓞 E)⁰) E)ˣ →* (FractionalIdeal ((𝓞 k)⁰) k)ˣ :=
  raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
    primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal))

private theorem fracRelNormUnit_primeUnit (w : HeightOneSpectrum (𝓞 E)) :
    fracRelNormUnit k E (primeUnit E w) = primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal) := by
  show raySymbol E _ ((primeUnit E w : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) : FractionalIdeal ((𝓞 E)⁰) E) = _
  rw [raySymbol_primeUnit]

private theorem relNorm_mem_nzd {I : Ideal (𝓞 E)} (hI : I ∈ (nonZeroDivisors (Ideal (𝓞 E)))) :
    Ideal.relNorm (𝓞 k) I ∈ nonZeroDivisors (Ideal (𝓞 k)) :=
  mem_nonZeroDivisors_of_ne_zero (fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hI) (by
      rw [Submodule.zero_eq_bot] at *; exact Ideal.relNorm_eq_bot_iff.mp h))

private theorem fracRelNormUnit_primeUnit_eq_relNorm (w : HeightOneSpectrum (𝓞 E)) :
    fracRelNormUnit k E (primeUnit E w)
      = FractionalIdeal.mk0 k ⟨Ideal.relNorm (𝓞 k) w.asIdeal, relNorm_mem_nzd k E
          (mem_nonZeroDivisors_of_ne_zero (by rw [Ne, Submodule.zero_eq_bot]; exact w.ne_bot))⟩ := by
  haveI : PerfectField (FractionRing (𝓞 k)) := PerfectField.ofCharZero
  haveI : w.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal w.isPrime w.ne_bot
  haveI : (w.under (𝓞 k)).asIdeal.IsMaximal :=
    Ideal.IsPrime.isMaximal (w.under (𝓞 k)).isPrime (w.under (𝓞 k)).ne_bot
  haveI : w.asIdeal.LiesOver (w.under (𝓞 k)).asIdeal := ⟨rfl⟩
  rw [fracRelNormUnit_primeUnit k E w]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, primeUnit_val, FractionalIdeal.coe_mk0, ← FractionalIdeal.coeIdeal_pow,
    Ideal.inertiaDeg'_eq_inertiaDeg (w.under (𝓞 k)).asIdeal w.asIdeal]
  exact congrArg _ (Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 k)).asIdeal).symm

private theorem fracRelNormUnit_mk0 (I : (Ideal (𝓞 E))⁰) :
    ((fracRelNormUnit k E (FractionalIdeal.mk0 E I) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ) : FractionalIdeal ((𝓞 k)⁰) k)
      = ((Ideal.relNorm (𝓞 k) (I : Ideal (𝓞 E)) : Ideal (𝓞 k)) : FractionalIdeal ((𝓞 k)⁰) k) := by
  obtain ⟨J, hJ⟩ := I
  have hJ' : J ≠ ⊥ := fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hJ) (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm)
  simp only at *
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ'
  | h₂ u hu =>
    obtain rfl : u = ⊤ := Ideal.isUnit_iff.mp hu
    rw [show FractionalIdeal.mk0 E (⟨(⊤ : Ideal (𝓞 E)), hJ⟩ : (Ideal (𝓞 E))⁰) = 1 from
        Units.ext (by rw [FractionalIdeal.coe_mk0, Units.val_one, FractionalIdeal.coeIdeal_top]),
      map_one, Units.val_one, ← Ideal.one_eq_top, map_one, Ideal.one_eq_top, FractionalIdeal.coeIdeal_top]
  | h₃ a p ha hp ih =>
    have ha' : a ≠ ⊥ := fun h => ha (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm)
    have hp_nz : p ∈ nonZeroDivisors (Ideal (𝓞 E)) :=
      mem_nonZeroDivisors_of_ne_zero (fun h => hp.ne_zero (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm))
    have ha_nz : a ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero ha
    let w : HeightOneSpectrum (𝓞 E) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hpw : (FractionalIdeal.mk0 E ⟨p, hp_nz⟩ : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) = primeUnit E w := by
      unfold primeUnit; exact congrArg (FractionalIdeal.mk0 E) (Subtype.ext rfl)
    rw [show (⟨p * a, hJ⟩ : (Ideal (𝓞 E))⁰) = ⟨p, hp_nz⟩ * ⟨a, ha_nz⟩ from rfl,
      map_mul, map_mul (fracRelNormUnit k E), Units.val_mul, hpw,
      fracRelNormUnit_primeUnit_eq_relNorm k E w, FractionalIdeal.coe_mk0,
      ih ha_nz ha', map_mul (Ideal.relNorm (𝓞 k)), FractionalIdeal.coeIdeal_mul]

private theorem intNorm_ne_zero {α : 𝓞 E} (hα : α ≠ 0) : Algebra.intNorm (𝓞 k) (𝓞 E) α ≠ 0 := by
  intro h
  have : Ideal.relNorm (𝓞 k) (Ideal.span {α}) = (⊥ : Ideal (𝓞 k)) := by
    rw [Ideal.relNorm_singleton, h, Ideal.span_singleton_eq_bot]
  exact hα (Ideal.span_singleton_eq_bot.mp (Ideal.relNorm_eq_bot_iff.mp this))

private theorem fracRelNormUnit_principalUnit (α : 𝓞 E) (hα : α ≠ 0) :
    fracRelNormUnit k E (principalUnit E α hα) = principalUnit k (Algebra.intNorm (𝓞 k) (𝓞 E) α) (intNorm_ne_zero k E hα) := by
  apply Units.ext
  rw [show principalUnit E α hα = FractionalIdeal.mk0 E ⟨Ideal.span {α}, _⟩ from rfl, fracRelNormUnit_mk0 k E,
    Ideal.relNorm_singleton, principalUnit_val]

private theorem fracRelNormUnit_mem_coprimeToModulus {𝔠 : Ideal (𝓞 k)} {Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ}
    (hY : Y ∈ coprimeToModulus E (modulusExt k E 𝔠)) : fracRelNormUnit k E Y ∈ coprimeToModulus k 𝔠 := by

  have hY' := coprimeToModulus_le_closure E (modulusExt k E 𝔠) hY
  refine Subgroup.closure_induction (p := fun J (_ : J ∈ Subgroup.closure (primeGens E (modulusExt k E 𝔠))) =>
    fracRelNormUnit k E J ∈ coprimeToModulus k 𝔠) ?_ ?_ ?_ ?_ hY'
  rotate_left
  · simp only [map_one]
    exact one_mem _
  · intro _ _ _ _ ha hb
    simp only [map_mul]
    exact mul_mem ha hb
  · intro _ _ ha
    simp only [map_inv]
    exact inv_mem ha
  rintro _ ⟨w, hw, rfl⟩
  show fracRelNormUnit k E (primeUnit E w) ∈ coprimeToModulus k 𝔠
  rw [fracRelNormUnit_primeUnit]
  refine pow_mem (primeUnit_mem_coprimeToModulus k fun h => hw ?_) _

  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
  exact Ideal.dvd_iff_le.mp h

private def _root_.M4aKummer.relNormCTM (𝔠 : Ideal (𝓞 k)) : ↥(coprimeToModulus E (modulusExt k E 𝔠)) →* ↥(coprimeToModulus k 𝔠) :=
  ((fracRelNormUnit k E).comp (coprimeToModulus E (modulusExt k E 𝔠)).subtype).codRestrict
    (coprimeToModulus k 𝔠) (fun Y => fracRelNormUnit_mem_coprimeToModulus k E Y.2)

p2m_export "M4aKummer" "relNormCTM"
private theorem coe_relNormCTM {𝔠 : Ideal (𝓞 k)} (Y : ↥(coprimeToModulus E (modulusExt k E 𝔠))) :
    ((relNormCTM k E 𝔠 Y : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = fracRelNormUnit k E (Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) := rfl

private theorem relNormCTM_primeUnit {𝔠 : Ideal (𝓞 k)} {w : HeightOneSpectrum (𝓞 E)} (hw : ¬ w.asIdeal ∣ modulusExt k E 𝔠) :
    ((relNormCTM k E 𝔠 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩ : ↥(coprimeToModulus k 𝔠)) :
        (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal) :=
  fracRelNormUnit_primeUnit k E w

private theorem relNormCTM_principalUnit {𝔠 : Ideal (𝓞 k)} {α : 𝓞 E} (hα : α ≠ 0)
    (hαcop : principalUnit E α hα ∈ coprimeToModulus E (modulusExt k E 𝔠)) :
    ((relNormCTM k E 𝔠 ⟨principalUnit E α hα, hαcop⟩ : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = principalUnit k (Algebra.intNorm (𝓞 k) (𝓞 E) α) (intNorm_ne_zero k E hα) :=
  fracRelNormUnit_principalUnit k E α hα

private theorem range_relNormCTM (𝔠 : Ideal (𝓞 k)) :
    (relNormCTM k E 𝔠).range = ((coprimeToModulus E (modulusExt k E 𝔠)).map (fracRelNormUnit k E)).subgroupOf
      (coprimeToModulus k 𝔠) := by
  ext X
  constructor
  · rintro ⟨Y, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨Y, Y.2, rfl⟩
  · intro hX
    obtain ⟨Y, hY, hYX⟩ := Subgroup.mem_subgroupOf.mp hX
    exact ⟨⟨Y, hY⟩, Subtype.ext hYX⟩

private def normRaySubgroup (𝔠 : Ideal (𝓞 k)) : Subgroup ↥(coprimeToModulus k 𝔠) :=
  (narrowRaySubgroup k 𝔠).subgroupOf (coprimeToModulus k 𝔠) ⊔ (relNormCTM k E 𝔠).range

private theorem normRaySubgroup_eq_frozen (𝔣 : Ideal (𝓞 k)) :
    normRaySubgroup k E 𝔣 =
      (narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) ⊔
        ((coprimeToModulus E (𝔣.map (algebraMap (𝓞 k) (𝓞 E)))).map
          (raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
            primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
          (coprimeToModulus k 𝔣) := by
  rw [normRaySubgroup, range_relNormCTM]
  rfl

end Norm

end M4aKummer

end

end ServedNorm

section NormBridge

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain Deep.NTSupply"
open scoped nonZeroDivisors

noncomputable section

attribute [local instance] FractionRing.liftAlgebra

namespace M4aKummer
namespace NormBridge

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem count_coe_eq_zero_iff (v : HeightOneSpectrum (𝓞 k)) {J : Ideal (𝓞 k)} (hJ : J ≠ ⊥) :
    FractionalIdeal.count k v (J : FractionalIdeal ((𝓞 k)⁰) k) = 0 ↔ ¬ v.asIdeal ∣ J := by
  have hJ0 : J ≠ 0 := by rwa [Ne, Submodule.zero_eq_bot]
  rw [FractionalIdeal.count_coe k v hJ0, Nat.cast_eq_zero]
  have h := Associates.count_ne_zero_iff_dvd hJ0 v.irreducible
  exact ⟨fun h0 hd => (h.mpr hd) h0, fun hnd => by_contra fun h0 => hnd (h.mp h0)⟩

private theorem dvd_of_dvd_map_of_dvd_map {𝔠 : Ideal (𝓞 k)} {v : HeightOneSpectrum (𝓞 k)} {u : HeightOneSpectrum (𝓞 E)}
    (huv : u.asIdeal ∣ v.asIdeal.map (algebraMap (𝓞 k) (𝓞 E))) (hu𝔠 : u.asIdeal ∣ modulusExt k E 𝔠) :
    v.asIdeal ∣ 𝔠 := by
  by_contra hv
  have htop : v.asIdeal ⊔ 𝔠 = ⊤ := by
    by_contra hne
    exact hv (Ideal.dvd_iff_le.mpr (le_sup_right.trans_eq (v.isMaximal.eq_of_le hne le_sup_left).symm))
  apply u.isPrime.ne_top
  rw [eq_top_iff, ← Ideal.map_top (algebraMap (𝓞 k) (𝓞 E)), ← htop, Ideal.map_sup]
  exact sup_le (Ideal.dvd_iff_le.mp huv) (Ideal.dvd_iff_le.mp hu𝔠)

omit [NumberField k] [NumberField E] in
private theorem map_ne_bot (v : HeightOneSpectrum (𝓞 k)) : v.asIdeal.map (algebraMap (𝓞 k) (𝓞 E)) ≠ ⊥ := fun h =>
  v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 E))).mp h)

private def extUnit (v : HeightOneSpectrum (𝓞 k)) : (FractionalIdeal ((𝓞 E)⁰) E)ˣ :=
  FractionalIdeal.mk0 E ⟨v.asIdeal.map (algebraMap (𝓞 k) (𝓞 E)), mem_nonZeroDivisors_of_ne_zero (map_ne_bot k E v)⟩

omit [NumberField k] in
private theorem coe_extUnit (v : HeightOneSpectrum (𝓞 k)) :
    ((extUnit k E v : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) : FractionalIdeal ((𝓞 E)⁰) E)
      = (v.asIdeal.map (algebraMap (𝓞 k) (𝓞 E)) : Ideal (𝓞 E)) := by
  rw [extUnit, FractionalIdeal.coe_mk0]

private theorem extUnit_mem {𝔠 : Ideal (𝓞 k)} {v : HeightOneSpectrum (𝓞 k)} (hv : ¬ v.asIdeal ∣ 𝔠) :
    extUnit k E v ∈ coprimeToModulus E (modulusExt k E 𝔠) := by
  rw [mem_coprimeToModulus_iff]
  intro u hu
  rw [coe_extUnit, count_coe_eq_zero_iff E u (map_ne_bot k E v)]
  exact fun huv => hv (dvd_of_dvd_map_of_dvd_map k E huv hu)

private theorem fracRelNormUnit_extUnit (h2 : Module.finrank k E = 2) (v : HeightOneSpectrum (𝓞 k)) :
    fracRelNormUnit k E (extUnit k E v) = primeUnit k v ^ 2 := by
  apply Units.ext
  rw [extUnit, fracRelNormUnit_mk0, Units.val_pow_eq_pow_val, primeUnit_val, ← FractionalIdeal.coeIdeal_pow]
  exact congrArg _ (relNorm_map_eq_sq k E h2 v.asIdeal)

private theorem sq_mem_range_relNormCTM (h2 : Module.finrank k E = 2) (𝔠 : Ideal (𝓞 k)) (X : ↥(coprimeToModulus k 𝔠)) :
    X ^ 2 ∈ (relNormCTM k E 𝔠).range := by
  obtain ⟨I, hI⟩ := X

  have key : ∀ J ∈ Subgroup.closure (primeGens k 𝔠),
      ∀ hJ : J ∈ coprimeToModulus k 𝔠, (⟨J, hJ⟩ : ↥(coprimeToModulus k 𝔠)) ^ 2 ∈ (relNormCTM k E 𝔠).range := by
    intro J hJ
    refine Subgroup.closure_induction (p := fun J (_ : J ∈ Subgroup.closure (primeGens k 𝔠)) =>
      ∀ hJ : J ∈ coprimeToModulus k 𝔠, (⟨J, hJ⟩ : ↥(coprimeToModulus k 𝔠)) ^ 2 ∈ (relNormCTM k E 𝔠).range)
      ?_ ?_ ?_ ?_ hJ
    · rintro _ ⟨v, hv, rfl⟩ hJ
      refine ⟨⟨extUnit k E v, extUnit_mem k E hv⟩, Subtype.ext ?_⟩
      rw [coe_relNormCTM, fracRelNormUnit_extUnit k E h2]
      rfl
    · intro _
      rw [show (⟨(1 : (FractionalIdeal ((𝓞 k)⁰) k)ˣ), _⟩ : ↥(coprimeToModulus k 𝔠)) = 1 from rfl, one_pow]
      exact one_mem _
    · intro a b ha hb iha ihb hab
      have ha' : a ∈ coprimeToModulus k 𝔠 := closure_primeGens_le k 𝔠 ha
      have hb' : b ∈ coprimeToModulus k 𝔠 := closure_primeGens_le k 𝔠 hb
      have hmul : (⟨a * b, hab⟩ : ↥(coprimeToModulus k 𝔠)) = ⟨a, ha'⟩ * ⟨b, hb'⟩ := rfl
      rw [hmul, mul_pow]
      exact mul_mem (iha ha') (ihb hb')
    · intro a ha iha hainv
      have ha' : a ∈ coprimeToModulus k 𝔠 := closure_primeGens_le k 𝔠 ha
      have hinv : (⟨a⁻¹, hainv⟩ : ↥(coprimeToModulus k 𝔠)) = ⟨a, ha'⟩⁻¹ := rfl
      rw [hinv, inv_pow]
      exact inv_mem (iha ha')
  exact key I (coprimeToModulus_le_closure k 𝔠 hI) hI

private theorem relNorm_eq_of_mul_eq_map (h2 : Module.finrank k E = 2) (v : HeightOneSpectrum (𝓞 k)) {w w' : Ideal (𝓞 E)}
    (hmul : w * w' = v.asIdeal.map (algebraMap (𝓞 k) (𝓞 E))) (hw : w ≠ ⊤) (hw' : w' ≠ ⊤) :
    Ideal.relNorm (𝓞 k) w = v.asIdeal := by
  have hprod : Ideal.relNorm (𝓞 k) w * Ideal.relNorm (𝓞 k) w' = v.asIdeal ^ 2 := by
    rw [← map_mul, hmul, relNorm_map_eq_sq k E h2]

  obtain ⟨j, hj2, hj⟩ := (dvd_prime_pow v.prime 2).mp (Dvd.intro _ hprod)
  rw [associated_iff_eq] at hj

  have hne : ∀ {I : Ideal (𝓞 E)}, I ≠ ⊤ → Ideal.relNorm (𝓞 k) I ≠ ⊤ := fun {I} hI h => by
    have hle := Ideal.relNorm_le_comap (R := 𝓞 k) I
    rw [h, top_le_iff, Ideal.comap_eq_top_iff] at hle
    exact hI hle
  interval_cases j
  · exact absurd (hj.trans (by rw [pow_zero, Ideal.one_eq_top])) (hne hw)
  · rw [hj, pow_one]
  · exfalso
    apply hne hw'
    rw [hj] at hprod
    have hv0 : v.asIdeal ^ 2 ≠ 0 := pow_ne_zero 2 (by rw [Ne, Submodule.zero_eq_bot]; exact v.ne_bot)
    exact ((mul_eq_left₀ hv0).mp hprod).trans Ideal.one_eq_top

private theorem primeUnit_mem_range_relNormCTM_of_split (h2 : Module.finrank k E = 2) {𝔠 : Ideal (𝓞 k)}
    {v : HeightOneSpectrum (𝓞 k)} (hv : ¬ v.asIdeal ∣ 𝔠) {w w' : Ideal (𝓞 E)}
    (hmul : w * w' = v.asIdeal.map (algebraMap (𝓞 k) (𝓞 E))) (hw : w ≠ ⊤) (hw' : w' ≠ ⊤) :
    (⟨primeUnit k v, primeUnit_mem_coprimeToModulus k hv⟩ : ↥(coprimeToModulus k 𝔠))
      ∈ (relNormCTM k E 𝔠).range := by
  have hwne : w ≠ ⊥ := by
    rintro rfl
    exact map_ne_bot k E v (by rw [← hmul, Ideal.bot_mul])
  refine ⟨⟨FractionalIdeal.mk0 E ⟨w, mem_nonZeroDivisors_of_ne_zero hwne⟩, ?_⟩, Subtype.ext ?_⟩
  · rw [mem_coprimeToModulus_iff]
    intro u hu
    rw [FractionalIdeal.coe_mk0, count_coe_eq_zero_iff E u hwne]
    exact fun huw => hv (dvd_of_dvd_map_of_dvd_map k E (huw.trans (Dvd.intro _ hmul)) hu)
  · rw [coe_relNormCTM]
    apply Units.ext
    rw [fracRelNormUnit_mk0, primeUnit_val]
    exact congrArg _ (relNorm_eq_of_mul_eq_map k E h2 v hmul hw hw')

end M4aKummer.NormBridge

end

end NormBridge

section ArtinCount

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom normRaySubgroup SecondInequalityCTM IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
namespace Count
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

variable {A T : Type*} [Group A] [Group T]

private theorem ker_eq_and_surjective_of_le_of_index_eq_card [Finite T] (φ : A →* T) {N : Subgroup A}
    (hker : φ.ker ≤ N) (hidx : N.index = Nat.card T) :
    φ.ker = N ∧ Function.Surjective φ := by
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hkidx : φ.ker.index = Nat.card φ.range := Subgroup.index_ker φ
  have hle : Nat.card φ.range ≤ Nat.card T :=
    Nat.card_le_card_of_injective _ φ.range.subtype_injective
  have hmul := Subgroup.relIndex_mul_index hker
  rw [hkidx, hidx] at hmul

  have hrpos : 0 < Nat.card φ.range := Nat.card_pos
  have hrel1 : φ.ker.relIndex N = 1 := by
    have h1 : φ.ker.relIndex N * Nat.card T ≤ 1 * Nat.card T := by rw [one_mul, hmul]; exact hle
    have h2 : 1 ≤ φ.ker.relIndex N := by
      rcases Nat.eq_zero_or_pos (φ.ker.relIndex N) with h | h
      · rw [h, zero_mul] at hmul; omega
      · exact h
    exact le_antisymm (Nat.le_of_mul_le_mul_right h1 hTpos) h2
  have hkerN : φ.ker = N := le_antisymm hker (Subgroup.relIndex_eq_one.mp hrel1)
  refine ⟨hkerN, ?_⟩

  have hcard : Nat.card φ.range = Nat.card T := by
    rw [← hkidx, hkerN, hidx]
  have : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by simpa using hcard)
  exact MonoidHom.range_eq_top.mp this

private theorem ker_eq_of_le_of_index_eq_card [Finite T] (φ : A →* T) {N : Subgroup A}
    (hker : φ.ker ≤ N) (hidx : N.index = Nat.card T) : φ.ker = N :=
  (ker_eq_and_surjective_of_le_of_index_eq_card φ hker hidx).1

private theorem surjective_of_le_of_index_eq_card [Finite T] (φ : A →* T) {N : Subgroup A}
    (hker : φ.ker ≤ N) (hidx : N.index = Nat.card T) : Function.Surjective φ :=
  (ker_eq_and_surjective_of_le_of_index_eq_card φ hker hidx).2

private theorem apply_eq_one_of_mem [Finite T] (φ : A →* T) {N : Subgroup A}
    (hker : φ.ker ≤ N) (hidx : N.index = Nat.card T) {x : A} (hx : x ∈ N) : φ x = 1 := by
  have h := ker_eq_of_le_of_index_eq_card φ hker hidx
  rw [← MonoidHom.mem_ker, h]
  exact hx

private theorem le_ker_of_le_of_index_eq_card [Finite T] (φ : A →* T) {N P : Subgroup A}
    (hker : φ.ker ≤ N) (hidx : N.index = Nat.card T) (hP : P ≤ N) : P ≤ φ.ker := by
  rw [ker_eq_of_le_of_index_eq_card φ hker hidx]
  exact hP

end LanglandsTunnell.P2.Artin.Count

end ArtinCount

section ArtinCrossing

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom normRaySubgroup SecondInequalityCTM IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

variable {I : Type*} [CommGroup I] (𝔑 : Subgroup I) {G : Type*} [Group G] (ω : I →* G) (σ : G)

section Transfer

variable {Ip : Type*} [CommGroup Ip] (N : Ip →* I) (ωp : Ip →* G)

private def transferClass (b : Ip) : I ⧸ 𝔑 := ((N b : I) : I ⧸ 𝔑)

variable {𝔑 N ωp σ}

private theorem transferClass_indep (hker : ∀ x, ωp x = 1 → N x ∈ 𝔑) {b b' : Ip} (hb : ωp b = σ) (hb' : ωp b' = σ) :
    transferClass 𝔑 N b = transferClass 𝔑 N b' := by
  unfold transferClass
  rw [QuotientGroup.eq, ← map_inv, ← map_mul]
  exact hker _ (by rw [map_mul, map_inv, hb, hb', inv_mul_cancel])

private theorem transferClass_pow_orderOf (hker : ∀ x, ωp x = 1 → N x ∈ 𝔑) {b : Ip} (hb : ωp b = σ) :
    transferClass 𝔑 N b ^ orderOf σ = 1 := by
  unfold transferClass
  rw [← QuotientGroup.mk_pow, ← map_pow, QuotientGroup.eq_one_iff]
  exact hker _ (by rw [map_pow, hb, pow_orderOf_eq_one])

private theorem coe_eq_transferClass_zpow (hker : ∀ x, ωp x = 1 → N x ∈ 𝔑) {b : Ip} (hb : ωp b = σ) {P : Ip} {p : I} (hNP : N P = p)
    {d : ℤ} (hd : ωp P = σ ^ d) : ((p : I) : I ⧸ 𝔑) = transferClass 𝔑 N b ^ d := by
  unfold transferClass
  rw [← hNP, ← QuotientGroup.mk_zpow, ← map_zpow, QuotientGroup.eq, ← map_inv, ← map_mul]
  exact hker _ (by rw [map_mul, map_inv, map_zpow, hb, hd, inv_mul_cancel])

private theorem apply_eq_zpow_of_transfer (hcompat : ∀ x, ω (N x) = ωp x) {P : Ip} {p : I} (hNP : N P = p) {d : ℤ} (hd : ωp P = σ ^ d) :
    ω p = σ ^ d := by
  rw [← hNP, hcompat, hd]

end Transfer

section Crossing

variable {Ip Iq Ipq : Type*} [CommGroup Ip] [CommGroup Iq] [CommGroup Ipq]
variable {N : Ip →* I} {ωp : Ip →* G} {N' : Iq →* I} {ωq : Iq →* G}
variable {𝔑 σ}

private theorem transferClass_eq_of_common_norm (hkerp : ∀ x, ωp x = 1 → N x ∈ 𝔑) (hkerq : ∀ x, ωq x = 1 → N' x ∈ 𝔑)
    {bp : Ip} {bq : Iq} (hN : N bp = N' bq) (hbp : ωp bp = σ) (hbq : ωq bq = σ)
    {b : Ip} (hb : ωp b = σ) {b' : Iq} (hb' : ωq b' = σ) : transferClass 𝔑 N b = transferClass 𝔑 N' b' := by
  rw [transferClass_indep hkerp hb hbp, transferClass_indep hkerq hb' hbq]
  unfold transferClass
  rw [hN]

variable {Np : Ipq →* Ip} {Nq : Ipq →* Iq} {ωpq : Ipq →* G}

private theorem transferClass_eq_of_crossing (hkerp : ∀ x, ωp x = 1 → N x ∈ 𝔑) (hkerq : ∀ x, ωq x = 1 → N' x ∈ 𝔑)
    (hNN : ∀ x, N (Np x) = N' (Nq x)) (hωp : ∀ x, ωp (Np x) = ωpq x) (hωq : ∀ x, ωq (Nq x) = ωpq x)
    {B : Ipq} (hB : ωpq B = σ) {b : Ip} (hb : ωp b = σ) {b' : Iq} (hb' : ωq b' = σ) :
    transferClass 𝔑 N b = transferClass 𝔑 N' b' :=
  transferClass_eq_of_common_norm hkerp hkerq (hNN B) (by rw [hωp, hB]) (by rw [hωq, hB]) hb hb'

end Crossing

private theorem exists_zpow_of_mem_closure (c : I ⧸ 𝔑) (S : Set I)
    (hS : ∀ p ∈ S, ∃ d : ℤ, ω p = σ ^ d ∧ ((p : I) : I ⧸ 𝔑) = c ^ d) {x : I} (hx : x ∈ Subgroup.closure S) :
    ∃ e : ℤ, ω x = σ ^ e ∧ ((x : I) : I ⧸ 𝔑) = c ^ e := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hS y hy
  | one => exact ⟨0, by rw [map_one, zpow_zero], by rw [QuotientGroup.mk_one, zpow_zero]⟩
  | mul y z _ _ ihy ihz =>
    obtain ⟨e, he, he'⟩ := ihy
    obtain ⟨f, hf, hf'⟩ := ihz
    exact ⟨e + f, by rw [map_mul, he, hf, zpow_add], by rw [QuotientGroup.mk_mul, he', hf', zpow_add]⟩
  | inv y _ ihy =>
    obtain ⟨e, he, he'⟩ := ihy
    exact ⟨-e, by rw [map_inv, he, zpow_neg], by rw [QuotientGroup.mk_inv, he', zpow_neg]⟩

private theorem mem_of_ker_of_classes (c : I ⧸ 𝔑) (hc : c ^ orderOf σ = 1) (S : Set I)
    (hS : ∀ p ∈ S, ∃ d : ℤ, ω p = σ ^ d ∧ ((p : I) : I ⧸ 𝔑) = c ^ d) {x : I} (hx : x ∈ Subgroup.closure S) (hω : ω x = 1) :
    x ∈ 𝔑 := by
  obtain ⟨e, he, he'⟩ := exists_zpow_of_mem_closure 𝔑 ω σ c S hS hx

  have hdvd : (orderOf σ : ℤ) ∣ e := orderOf_dvd_iff_zpow_eq_one.mpr (by rw [← he, hω])
  have hce : c ^ e = 1 := by
    obtain ⟨t, rfl⟩ := hdvd
    rw [zpow_mul, zpow_natCast, hc, one_zpow]
  rw [← QuotientGroup.eq_one_iff, he', hce]

private theorem ker_inf_closure_le (c : I ⧸ 𝔑) (hc : c ^ orderOf σ = 1) (S : Set I)
    (hS : ∀ p ∈ S, ∃ d : ℤ, ω p = σ ^ d ∧ ((p : I) : I ⧸ 𝔑) = c ^ d) : ω.ker ⊓ Subgroup.closure S ≤ 𝔑 :=
  fun _ hx => mem_of_ker_of_classes 𝔑 ω σ c hc S hS hx.2 (MonoidHom.mem_ker.mp hx.1)

private theorem ker_inf_closure_le_of_transfer {Ip : Type*} [CommGroup Ip] (S : Set I)
    (N : I → (Ip →* I)) (ωp : I → (Ip →* G)) (P : I → Ip) (d : I → ℤ)
    (hcompat : ∀ p ∈ S, ∀ x, ω (N p x) = ωp p x) (hker : ∀ p ∈ S, ∀ x, ωp p x = 1 → N p x ∈ 𝔑)
    (hNP : ∀ p ∈ S, N p (P p) = p) (hd : ∀ p ∈ S, ωp p (P p) = σ ^ d p)
    (hcross : ∀ p ∈ S, ∀ q ∈ S, ∃ bp bq : Ip, N p bp = N q bq ∧ ωp p bp = σ) :
    ω.ker ⊓ Subgroup.closure S ≤ 𝔑 := by
  by_cases hS : S.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hS
    obtain ⟨b₀, -, -, hb₀⟩ := hcross p₀ hp₀ p₀ hp₀
    refine ker_inf_closure_le 𝔑 ω σ (transferClass 𝔑 (N p₀) b₀) (transferClass_pow_orderOf (hker p₀ hp₀) hb₀) S ?_
    intro p hp
    obtain ⟨bp, bq, hN, hbp⟩ := hcross p₀ hp₀ p hp

    have hbq : ωp p bq = σ := by rw [← hcompat p hp, ← hN, hcompat p₀ hp₀, hbp]
    refine ⟨d p, apply_eq_zpow_of_transfer ω (hcompat p hp) (hNP p hp) (hd p hp), ?_⟩
    rw [transferClass_eq_of_common_norm (hker p₀ hp₀) (hker p hp) hN hbp hbq hb₀ hbq]
    exact coe_eq_transferClass_zpow (hker p hp) hbq (hNP p hp) (hd p hp)
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, Subgroup.closure_empty, inf_bot_eq]
    exact bot_le

end LanglandsTunnell.P2.Artin

end ArtinCrossing

section ArtinFrob

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom normRaySubgroup SecondInequalityCTM IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain"
open scoped Pointwise

section Transport

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

private theorem inertia_smul_eq_bot (τ : G) (Q : Ideal S) (hI : Q.inertia G = ⊥) : (τ • Q).inertia G = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' : ∀ x : S, g • x - x ∈ τ • Q := fun x => hg x
  have hmem : τ⁻¹ * g * τ ∈ Q.inertia G := by
    intro x
    have hx := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 (hg' (τ • x))
    rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul] at hx
    exact hx
  rw [hI, Subgroup.mem_bot] at hmem
  have hgg : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
  rw [hmem] at hgg
  simpa using hgg

private theorem eq_of_isArithFrobAt_of_inertia_eq_bot {σ σ' : G} {Q : Ideal S} (H : IsArithFrobAt R σ Q) (H' : IsArithFrobAt R σ' Q)
    (hI : Q.inertia G = ⊥) : σ = σ' := by
  have h := H.mul_inv_mem_inertia H'
  rw [hI, Subgroup.mem_bot] at h
  exact mul_inv_eq_one.1 h

private theorem pow_smul_sub_pow_mem {σ : G} {Q : Ideal S} [Q.IsPrime] (H : IsArithFrobAt R σ Q) (k : ℕ) (x : S) :
    σ ^ k • x - x ^ (Nat.card (R ⧸ Q.under R) ^ k) ∈ Q := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hσQ : ∀ y ∈ Q, σ • y ∈ Q := fun y hy => by
      have hstab := H.mem_stabilizer
      rw [MulAction.mem_stabilizer_iff] at hstab
      have h := Ideal.smul_mem_pointwise_smul σ y Q hy
      rwa [hstab] at h
    have h1 : σ ^ (k + 1) • x - σ • x ^ (Nat.card (R ⧸ Q.under R) ^ k) ∈ Q := by
      rw [pow_succ', mul_smul, ← smul_sub]
      exact hσQ _ (ih x)
    have h2 : σ • x ^ (Nat.card (R ⧸ Q.under R) ^ k) - x ^ (Nat.card (R ⧸ Q.under R) ^ (k + 1)) ∈ Q := by
      rw [smul_pow', pow_succ', pow_mul]
      exact Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow _ _ _) (H x)
    have h := Q.add_mem h1 h2
    rwa [sub_add_sub_cancel] at h

private theorem smul_pow_zero_sub_mem {σ : G} {Q : Ideal S} [Q.IsPrime] (H : IsArithFrobAt R σ Q) (x : S) :
    σ ^ 0 • x - x ^ (Nat.card (R ⧸ Q.under R) ^ 0) ∈ Q :=
  pow_smul_sub_pow_mem H 0 x

variable [Finite G] [Algebra.IsInvariant R S G]

private theorem arithFrobAt_smul (τ : G) (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] [Finite (S ⧸ τ • Q)] (hI : Q.inertia G = ⊥) :
    arithFrobAt R G (τ • Q) = τ * arithFrobAt R G Q * τ⁻¹ := by
  have h1 : IsArithFrobAt R (arithFrobAt R G (τ • Q)) (τ • Q) := IsArithFrobAt.arithFrobAt R G (τ • Q)
  have h2 : IsArithFrobAt R (τ * arithFrobAt R G Q * τ⁻¹) (τ • Q) := (IsArithFrobAt.arithFrobAt R G Q).conj τ
  have h3 := h1.mul_inv_mem_inertia h2
  rw [inertia_smul_eq_bot τ Q hI, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.1 h3

end Transport

section Artin

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  (v : HeightOneSpectrum (𝓞 K))

private theorem arithFrobAt_eq_artinFrob [IsMulCommutative (M ≃ₐ[K] M)] (Q : Ideal (𝓞 M)) [Q.IsPrime] [Finite (𝓞 M ⧸ Q)]
    (hQ : Q.under (𝓞 K) = v.asIdeal) (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) :
    arithFrobAt (𝓞 K) (M ≃ₐ[K] M) Q = artinFrob K M v := by
  haveI : Q.LiesOver v.asIdeal := ⟨hQ.symm⟩
  haveI := v.isMaximal
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal (primeAbove K M v) Q (M ≃ₐ[K] M)
  subst hτ
  have hI₀ : (primeAbove K M v).inertia (M ≃ₐ[K] M) = ⊥ := by
    have h := inertia_smul_eq_bot τ⁻¹ (τ • primeAbove K M v) hI
    rwa [inv_smul_smul] at h
  rw [arithFrobAt_smul τ (primeAbove K M v) hI₀, IsMulCommutative.is_comm.comm τ, mul_inv_cancel_right]
  rfl

private theorem eq_artinFrob_of_isArithFrobAt [IsMulCommutative (M ≃ₐ[K] M)] {σ : M ≃ₐ[K] M} {Q : Ideal (𝓞 M)} [Q.IsPrime]
    (H : IsArithFrobAt (𝓞 K) σ Q) (hQ : Q.under (𝓞 K) = v.asIdeal) (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) : σ = artinFrob K M v := by
  haveI := finite_quotient_of_under_eq K M v hQ
  rw [← arithFrobAt_eq_artinFrob K M v Q hQ hI]
  exact eq_of_isArithFrobAt_of_inertia_eq_bot H (IsArithFrobAt.arithFrobAt (𝓞 K) (M ≃ₐ[K] M) Q) hI

end Artin

section Restrict

variable (K M M' : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field M'] [NumberField M']
  [Algebra K M] [Algebra K M'] [Algebra M M'] [IsScalarTower K M M'] [IsGalois K M] [IsGalois K M']

private scoped instance : IsScalarTower (𝓞 K) (𝓞 M) (𝓞 M') :=
  IsScalarTower.of_algebraMap_eq fun x => by
    refine RingOfIntegers.ext ?_
    show algebraMap K M' (x : K) = algebraMap M M' (algebraMap (𝓞 K) (𝓞 M) x : M)
    rw [show (algebraMap (𝓞 K) (𝓞 M) x : M) = algebraMap K M (x : K) from rfl, ← IsScalarTower.algebraMap_apply K M M']

private theorem isArithFrobAt_restrictNormal (τ : M' ≃ₐ[K] M') (Q' : Ideal (𝓞 M')) (H : IsArithFrobAt (𝓞 K) τ Q') :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom M τ) (Q'.under (𝓞 M)) := by
  intro x
  have hcard : Nat.card (𝓞 K ⧸ (Q'.under (𝓞 M)).under (𝓞 K)) = Nat.card (𝓞 K ⧸ Q'.under (𝓞 K)) := by
    rw [Ideal.under_under]
  have hkey : algebraMap (𝓞 M) (𝓞 M') ((AlgEquiv.restrictNormalHom M τ) • x) = τ • algebraMap (𝓞 M) (𝓞 M') x := by
    refine RingOfIntegers.ext ?_
    show algebraMap M M' ((τ.restrictNormal M) (x : M)) = τ (algebraMap M M' (x : M))
    exact AlgEquiv.restrictNormal_commutes τ M (x : M)
  rw [hcard, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow]
  erw [hkey]
  exact H (algebraMap (𝓞 M) (𝓞 M') x)

private theorem restrictNormal_artinFrob [IsMulCommutative (M ≃ₐ[K] M)] (v : HeightOneSpectrum (𝓞 K))
    (hI : ((primeAbove K M' v).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    AlgEquiv.restrictNormalHom M (artinFrob K M' v) = artinFrob K M v := by
  have H := isArithFrobAt_restrictNormal K M M' (artinFrob K M' v) (primeAbove K M' v) (isArithFrobAt_artinFrob K M' v)
  haveI : ((primeAbove K M' v).under (𝓞 M)).IsPrime := Ideal.IsPrime.under (𝓞 M) (primeAbove K M' v)
  refine eq_artinFrob_of_isArithFrobAt K M v H ?_ hI
  rw [Ideal.under_under, under_primeAbove]

end Restrict

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end ArtinFrob
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

section ArtinSymbol

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom normRaySubgroup SecondInequalityCTM IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain"

section Symbol

open Deep.NTSupply
open scoped nonZeroDivisors

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

open scoped IsMulCommutative

omit [NumberField M] [Algebra K M] [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)] in

private theorem map_raySymbol {N N' : Type*} [CommGroup N] [CommGroup N'] (φ : N →* N') (f : HeightOneSpectrum (𝓞 K) → N)
    (I : FractionalIdeal ((𝓞 K)⁰) K) : φ (raySymbol K f I) = raySymbol K (φ ∘ f) I := by
  unfold raySymbol
  rw [φ.map_finprod (hasFiniteMulSupport_raySymbol_factors K f I)]
  simp only [map_zpow, Function.comp_apply]

variable (M' : Type*) [Field M'] [NumberField M'] [Algebra K M'] [Algebra M M'] [IsScalarTower K M M'] [IsGalois K M']
  [IsMulCommutative (M' ≃ₐ[K] M')]

private theorem restrictNormalHom_artinSymbol (𝔣 : Ideal (𝓞 K))
    (hI : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → ((primeAbove K M' v).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥)
    (I : ↥(coprimeToModulus K 𝔣)) :
    AlgEquiv.restrictNormalHom M (artinSymbol K M' 𝔣 I) = artinSymbol K M 𝔣 I := by
  rw [artinSymbol, artinSymbol, raySymbolHom_apply, raySymbolHom_apply, map_raySymbol]
  unfold raySymbol
  refine finprod_congr fun v => ?_
  by_cases hv : v.asIdeal ∣ 𝔣
  · rw [I.2 v hv, zpow_zero, zpow_zero]
  · rw [Function.comp_apply, restrictNormal_artinFrob K M M' v (hI v hv)]

end Symbol
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end ArtinSymbol
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

section ArtinReciprocity

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom normRaySubgroup SecondInequalityCTM IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain Deep.NTSupply"
open scoped nonZeroDivisors IsMulCommutative

section Carriers

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))

private theorem primeCarrier_mem (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    primeCarrier K 𝔣 v hv ∈ primeCarriers K 𝔣 :=
  ⟨v, hv, rfl⟩

open Classical in

private def carrierOrOne (v : HeightOneSpectrum (𝓞 K)) : ↥(coprimeToModulus K 𝔣) :=
  if hv : v.asIdeal ∣ 𝔣 then 1 else primeCarrier K 𝔣 v hv

private theorem carrierOrOne_mem_closure (v : HeightOneSpectrum (𝓞 K)) :
    carrierOrOne K 𝔣 v ∈ Subgroup.closure (primeCarriers K 𝔣) := by
  unfold carrierOrOne
  split_ifs with hv
  · exact one_mem _
  · exact Subgroup.subset_closure (primeCarrier_mem K 𝔣 v hv)

open Classical in

private theorem val_carrierOrOne_zpow (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    (((carrierOrOne K 𝔣 v ^ n : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = if v.asIdeal ∣ 𝔣 then 1 else (v.asIdeal : FractionalIdeal ((𝓞 K)⁰) K) ^ n := by
  rw [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val]
  unfold carrierOrOne
  split_ifs with hv
  · rw [OneMemClass.coe_one, Units.val_one, one_zpow]
  · rw [primeCarrier, primeUnit_val]

private theorem raySymbolHom_carrierOrOne (I : ↥(coprimeToModulus K 𝔣)) : raySymbolHom K 𝔣 (carrierOrOne K 𝔣) I = I := by
  apply Subtype.ext
  apply Units.ext
  rw [raySymbolHom_apply]
  unfold raySymbol
  have hfin := hasFiniteMulSupport_raySymbol_factors K (carrierOrOne K 𝔣)
    ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)

  let φ : ↥(coprimeToModulus K 𝔣) →* FractionalIdeal ((𝓞 K)⁰) K :=
    (Units.coeHom (FractionalIdeal ((𝓞 K)⁰) K)).comp (coprimeToModulus K 𝔣).subtype
  show φ (∏ᶠ v, carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v
      ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)) = φ I
  rw [MonoidHom.map_finprod φ hfin]
  conv_rhs => rw [show φ I = ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) from rfl,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K (Units.ne_zero (I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))]
  refine finprod_congr fun v => ?_
  rw [show φ (carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K))
      = (((carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
          : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) from rfl,
    val_carrierOrOne_zpow]
  split_ifs with hv
  · rw [I.2 v hv, zpow_zero]
  · rfl

private theorem closure_primeCarriers_eq_top : Subgroup.closure (primeCarriers K 𝔣) = ⊤ := by
  rw [eq_top_iff]
  intro I _
  rw [← raySymbolHom_carrierOrOne K 𝔣 I, raySymbolHom_apply]
  unfold raySymbol
  exact finprod_induction (· ∈ Subgroup.closure (primeCarriers K 𝔣)) (one_mem _) (fun _ _ => mul_mem)
    fun v => zpow_mem (carrierOrOne_mem_closure K 𝔣 v) _

end Carriers
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

section Assembly

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]
variable (𝔣 : Ideal (𝓞 K)) (𝔑 : Subgroup ↥(coprimeToModulus K 𝔣)) (σ : L ≃ₐ[K] L)
variable {Ip : Type*} [CommGroup Ip]
  (N : ↥(coprimeToModulus K 𝔣) → (Ip →* ↥(coprimeToModulus K 𝔣))) (ωp : ↥(coprimeToModulus K 𝔣) → (Ip →* (L ≃ₐ[K] L)))
  (P : ↥(coprimeToModulus K 𝔣) → Ip) (d : ↥(coprimeToModulus K 𝔣) → ℤ)

private theorem artinSymbol_ker_eq_and_surjective_of_transfer
    (hcompat : ∀ p ∈ primeCarriers K 𝔣, ∀ x, artinSymbol K L 𝔣 (N p x) = ωp p x)
    (hker : ∀ p ∈ primeCarriers K 𝔣, ∀ x, ωp p x = 1 → N p x ∈ 𝔑)
    (hNP : ∀ p ∈ primeCarriers K 𝔣, N p (P p) = p) (hd : ∀ p ∈ primeCarriers K 𝔣, ωp p (P p) = σ ^ d p)
    (hcross : ∀ p ∈ primeCarriers K 𝔣, ∀ q ∈ primeCarriers K 𝔣, ∃ bp bq : Ip, N p bp = N q bq ∧ ωp p bp = σ)
    (hidx : 𝔑.index = Nat.card (L ≃ₐ[K] L)) :
    (artinSymbol K L 𝔣).ker = 𝔑 ∧ Function.Surjective (artinSymbol K L 𝔣) := by
  refine Count.ker_eq_and_surjective_of_le_of_index_eq_card (artinSymbol K L 𝔣) ?_ hidx
  have h := ker_inf_closure_le_of_transfer 𝔑 (artinSymbol K L 𝔣) σ (primeCarriers K 𝔣) N ωp P d hcompat hker hNP hd hcross
  rwa [closure_primeCarriers_eq_top, inf_top_eq] at h

private theorem raySymbol_artinFrob_eq_one_of_transfer
    (hcompat : ∀ p ∈ primeCarriers K 𝔣, ∀ x, artinSymbol K L 𝔣 (N p x) = ωp p x)
    (hker : ∀ p ∈ primeCarriers K 𝔣, ∀ x, ωp p x = 1 → N p x ∈ 𝔑)
    (hNP : ∀ p ∈ primeCarriers K 𝔣, N p (P p) = p) (hd : ∀ p ∈ primeCarriers K 𝔣, ωp p (P p) = σ ^ d p)
    (hcross : ∀ p ∈ primeCarriers K 𝔣, ∀ q ∈ primeCarriers K 𝔣, ∃ bp bq : Ip, N p bp = N q bq ∧ ωp p bp = σ)
    (hidx : 𝔑.index = Nat.card (L ≃ₐ[K] L))
    (hP : ∀ (α : 𝓞 K) (hα0 : α ≠ 0) (hα1 : α - 1 ∈ 𝔣), (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
      (⟨principalUnit K α hα0, principalUnit_mem_coprimeToModulus K hα0 hα1⟩ : ↥(coprimeToModulus K 𝔣)) ∈ 𝔑)
    {α : 𝓞 K} (hα0 : α ≠ 0) (hα1 : α - 1 ∈ 𝔣) (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) :
    raySymbol K (artinFrob K L) (((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K)) = 1 := by
  obtain ⟨hkerEq, -⟩ :=
    artinSymbol_ker_eq_and_surjective_of_transfer K L 𝔣 𝔑 σ N ωp P d hcompat hker hNP hd hcross hidx
  have hmem : (⟨principalUnit K α hα0, principalUnit_mem_coprimeToModulus K hα0 hα1⟩ : ↥(coprimeToModulus K 𝔣))
      ∈ (artinSymbol K L 𝔣).ker := hkerEq ▸ hP α hα0 hα1 hpos
  rw [MonoidHom.mem_ker, artinSymbol, raySymbolHom_apply] at hmem
  rw [← principalUnit_val K α hα0]
  exact hmem

end Assembly
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end ArtinReciprocity
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

section ArtinNorm

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom normRaySubgroup SecondInequalityCTM IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain"
open scoped Pointwise

section FrobLike

variable {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]

private theorem mul_inv_mem_inertia_of_frobLike {σ τ : G} {Q : Ideal S} {q : ℕ}
    (hσ : ∀ x : S, σ • x - x ^ q ∈ Q) (hτ : ∀ x : S, τ • x - x ^ q ∈ Q) : σ * τ⁻¹ ∈ Q.inertia G := by
  intro x
  have h1 := hσ (τ⁻¹ • x)
  have h2 := hτ (τ⁻¹ • x)
  rw [smul_inv_smul] at h2
  have h := Q.sub_mem h1 h2
  rwa [sub_sub_sub_cancel_right, ← mul_smul] at h

private theorem eq_of_frobLike {σ τ : G} {Q : Ideal S} {q : ℕ}
    (hσ : ∀ x : S, σ • x - x ^ q ∈ Q) (hτ : ∀ x : S, τ • x - x ^ q ∈ Q) (hI : Q.inertia G = ⊥) : σ = τ := by
  have h := mul_inv_mem_inertia_of_frobLike hσ hτ
  rw [hI, Subgroup.mem_bot] at h
  exact mul_inv_eq_one.1 h

end FrobLike
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

section ResidueTower

attribute [local instance] Ideal.Quotient.field

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

private theorem natCard_residue_eq_pow (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E)) (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal) :
    Nat.card (𝓞 E ⧸ w.asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal) ^ v.asIdeal.inertiaDeg' w.asIdeal := by
  haveI := v.isMaximal
  haveI := w.isMaximal
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  rw [Ideal.inertiaDeg_algebraMap]
  exact Module.natCard_eq_pow_finrank

end ResidueTower
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

section Norm

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E] [Field N] [NumberField N]
  [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N] [IsScalarTower K M N] [IsScalarTower K E N]
  [IsGalois K M] [IsGalois E N]

private theorem restrictNormal_artinFrob_eq_pow [IsMulCommutative (M ≃ₐ[K] M)] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hI : ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    ((artinFrob E N w).restrictScalars K).restrictNormal M = artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal := by
  haveI : ((primeAbove E N w).under (𝓞 M)).IsPrime := Ideal.IsPrime.under (𝓞 M) (primeAbove E N w)
  have hQMv : ((primeAbove E N w).under (𝓞 M)).under (𝓞 K) = v.asIdeal := by
    rw [Ideal.under_under, ← Ideal.under_under (B := 𝓞 E), under_primeAbove, hwv]
  haveI : Finite (𝓞 M ⧸ (primeAbove E N w).under (𝓞 M)) := finite_quotient_of_under_eq K M v hQMv

  have hw : Nat.card (𝓞 E ⧸ (primeAbove E N w).under (𝓞 E)) = Nat.card (𝓞 E ⧸ w.asIdeal) := by rw [under_primeAbove]
  have hφ : ∀ y : 𝓞 M, (((artinFrob E N w).restrictScalars K).restrictNormal M) • y - y ^ Nat.card (𝓞 E ⧸ w.asIdeal)
      ∈ (primeAbove E N w).under (𝓞 M) := by
    intro y
    have hkey : algebraMap (𝓞 M) (𝓞 N) ((((artinFrob E N w).restrictScalars K).restrictNormal M) • y)
        = (artinFrob E N w) • algebraMap (𝓞 M) (𝓞 N) y := by
      refine RingOfIntegers.ext ?_
      show algebraMap M N ((((artinFrob E N w).restrictScalars K).restrictNormal M) (y : M)) = (artinFrob E N w) (algebraMap M N (y : M))
      exact AlgEquiv.restrictNormal_commutes _ M (y : M)
    rw [Ideal.under_def, Ideal.mem_comap, map_sub, map_pow]
    erw [hkey]
    rw [← hw]
    exact isArithFrobAt_artinFrob E N w (algebraMap (𝓞 M) (𝓞 N) y)

  have hF : IsArithFrobAt (𝓞 K) (arithFrobAt (𝓞 K) (M ≃ₐ[K] M) ((primeAbove E N w).under (𝓞 M))) ((primeAbove E N w).under (𝓞 M)) :=
    IsArithFrobAt.arithFrobAt (𝓞 K) (M ≃ₐ[K] M) _
  have hcard : Nat.card (𝓞 E ⧸ w.asIdeal)
      = Nat.card (𝓞 K ⧸ ((primeAbove E N w).under (𝓞 M)).under (𝓞 K)) ^ v.asIdeal.inertiaDeg' w.asIdeal := by
    rw [hQMv]
    exact natCard_residue_eq_pow v w hwv
  have hFf : ∀ y : 𝓞 M, arithFrobAt (𝓞 K) (M ≃ₐ[K] M) ((primeAbove E N w).under (𝓞 M)) ^ v.asIdeal.inertiaDeg' w.asIdeal • y
      - y ^ Nat.card (𝓞 E ⧸ w.asIdeal) ∈ (primeAbove E N w).under (𝓞 M) := fun y => by
    rw [hcard]
    exact pow_smul_sub_pow_mem hF _ y

  rw [eq_of_frobLike hφ hFf hI, arithFrobAt_eq_artinFrob K M v ((primeAbove E N w).under (𝓞 M)) hQMv hI]

end Norm
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end ArtinNorm
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

section ArtinRelNorm

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom normRaySubgroup SecondInequalityCTM IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain Deep.NTSupply"
open scoped IsMulCommutative nonZeroDivisors

section Finite
variable (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

private scoped instance moduleFinite_ringOfIntegers : Module.Finite (𝓞 K) (𝓞 E) :=
  Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 E)

end Finite
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

section RaySymbolAux
variable (K : Type*) [Field K] [NumberField K] {G : Type*} [CommGroup G] (f : HeightOneSpectrum (𝓞 K) → G)

private theorem raySymbol_one' : raySymbol K f (1 : FractionalIdeal ((𝓞 K)⁰) K) = 1 := by
  simp [raySymbol, FractionalIdeal.count_one]

private theorem raySymbol_coeIdeal_prime (v : HeightOneSpectrum (𝓞 K)) :
    raySymbol K f (v.asIdeal : FractionalIdeal ((𝓞 K)⁰) K) = f v := by
  rw [← primeUnit_val, raySymbol_primeUnit]

private theorem raySymbol_coeIdeal_pow (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (n : ℕ) :
    raySymbol K f ((I ^ n : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = raySymbol K f (I : FractionalIdeal ((𝓞 K)⁰) K) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Ideal.one_eq_top, FractionalIdeal.coeIdeal_top, raySymbol_one']
  | succ n ih =>
    rw [pow_succ, pow_succ, FractionalIdeal.coeIdeal_mul, raySymbol_mul K f ?_ ?_, ih]
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr (pow_ne_zero n hI)
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr hI

end RaySymbolAux
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

section Tower

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E] [Field N] [NumberField N]
  [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N] [IsScalarTower K M N] [IsScalarTower K E N]
  [IsGalois K M] [IsGalois E N]

omit [NumberField K] [NumberField M] [NumberField E] [NumberField N] [IsGalois E N] in
private theorem resHom_apply (σ : N ≃ₐ[E] N) : resHom K M E N σ = (σ.restrictScalars K).restrictNormal M := rfl

variable [IsMulCommutative (M ≃ₐ[K] M)]

private theorem resHom_artinFrob (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E)) (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hI : ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    resHom K M E N (artinFrob E N w) = artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal :=
  restrictNormal_artinFrob_eq_pow K M E N v w hwv hI

private def placeUnder (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 K) :=
  ⟨w.asIdeal.under (𝓞 K), inferInstance, fun h => w.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)⟩

omit [NumberField K] [NumberField E] [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)] in
private theorem placeUnder_asIdeal (w : HeightOneSpectrum (𝓞 E)) : (placeUnder K E w).asIdeal = w.asIdeal.under (𝓞 K) := rfl

variable [IsMulCommutative (N ≃ₐ[E] N)]

private theorem resHom_raySymbol_eq_raySymbol_relNorm (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥)
    (hI : ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal ∣ 𝔞 → ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    resHom K M E N (raySymbol E (artinFrob E N) (𝔞 : FractionalIdeal ((𝓞 E)⁰) E)) =
      raySymbol K (artinFrob K M) ((Ideal.relNorm (𝓞 K) 𝔞 : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) := by
  induction 𝔞 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (h𝔞 Submodule.zero_eq_bot).elim
  | h₂ u hu =>
    have h1 : Ideal.relNorm (𝓞 K) (⊤ : Ideal (𝓞 E)) = ⊤ := by rw [← Ideal.one_eq_top, map_one, Ideal.one_eq_top]
    rw [Ideal.isUnit_iff.mp hu, h1, FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_top, raySymbol_one', raySymbol_one', map_one]
  | h₃ a p ha hp ih =>

    haveI hpP : p.IsPrime := Ideal.isPrime_of_prime hp
    let w : HeightOneSpectrum (𝓞 E) := ⟨p, hpP, hp.ne_zero⟩
    let v : HeightOneSpectrum (𝓞 K) := placeUnder K E w
    haveI := v.isMaximal
    haveI := w.isMaximal
    haveI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
    have hab : a ≠ ⊥ := ha
    have hIa : ∀ w' : HeightOneSpectrum (𝓞 E), w'.asIdeal ∣ a → ((primeAbove E N w').under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥ :=
      fun w' hw' => hI w' (dvd_mul_of_dvd_right hw' p)
    have hIw : ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥ := hI w (dvd_mul_right p a)

    rw [FractionalIdeal.coeIdeal_mul, raySymbol_mul E (artinFrob E N) (FractionalIdeal.coeIdeal_ne_zero.mpr hp.ne_zero)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hab), map_mul, ih hab hIa,
      show (p : FractionalIdeal ((𝓞 E)⁰) E) = (w.asIdeal : FractionalIdeal ((𝓞 E)⁰) E) from rfl, raySymbol_coeIdeal_prime,
      resHom_artinFrob K M E N v w rfl hIw]

    have hrel : Ideal.relNorm (𝓞 K) p = v.asIdeal ^ v.asIdeal.inertiaDeg' w.asIdeal := by
      show Ideal.relNorm (𝓞 K) w.asIdeal = _
      rw [Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w.asIdeal]
      exact Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal v.asIdeal
    have hrel0 : Ideal.relNorm (𝓞 K) a ≠ ⊥ := by
      rw [Ne, Ideal.relNorm_eq_bot_iff]; exact hab
    rw [map_mul, hrel, FractionalIdeal.coeIdeal_mul, raySymbol_mul K (artinFrob K M) ?_ (FractionalIdeal.coeIdeal_ne_zero.mpr hrel0),
      raySymbol_coeIdeal_pow K (artinFrob K M) v.asIdeal v.ne_bot, raySymbol_coeIdeal_prime]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr (pow_ne_zero _ v.ne_bot)

end Tower
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end ArtinRelNorm
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

section ICNNormUnit

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem fracRelNormUnit_primeUnit (w : HeightOneSpectrum (𝓞 E))
    (𝔭 : HeightOneSpectrum (𝓞 k)) (h𝔭w : w.asIdeal.under (𝓞 k) = 𝔭.asIdeal) :
    fracRelNormUnit k E (primeUnit E w)
      = primeUnit k 𝔭 ^ (𝔭.asIdeal.inertiaDeg' w.asIdeal) := by
  have heq : placeUnder' k E w = 𝔭 :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, h𝔭w])
  show raySymbolUnitsHom E _ (primeUnit E w) = _
  rw [show raySymbolUnitsHom E _ (primeUnit E w)
        = raySymbol E _ ((primeUnit E w : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) :
            FractionalIdeal ((𝓞 E)⁰) E) from rfl,
    raySymbol_primeUnit, heq]

private theorem relNorm_mem_nzd {I : Ideal (𝓞 E)} (hI : I ∈ (nonZeroDivisors (Ideal (𝓞 E)))) :
    Ideal.relNorm (𝓞 k) I ∈ nonZeroDivisors (Ideal (𝓞 k)) :=
  mem_nonZeroDivisors_of_ne_zero (fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hI) (by
      rw [Submodule.zero_eq_bot] at *; exact Ideal.relNorm_eq_bot_iff.mp h))

private theorem fracRelNormUnit_primeUnit_eq_relNorm (w : HeightOneSpectrum (𝓞 E)) :
    fracRelNormUnit k E (primeUnit E w)
      = FractionalIdeal.mk0 k ⟨Ideal.relNorm (𝓞 k) w.asIdeal, relNorm_mem_nzd k E
          (mem_nonZeroDivisors_of_ne_zero (by
            rw [Ne, Submodule.zero_eq_bot]; exact w.ne_bot))⟩ := by
  haveI : PerfectField (FractionRing (𝓞 k)) := PerfectField.ofCharZero
  haveI : w.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal w.isPrime w.ne_bot
  haveI : (placeUnder' k E w).asIdeal.IsMaximal :=
    Ideal.IsPrime.isMaximal (placeUnder' k E w).isPrime (placeUnder' k E w).ne_bot
  haveI : w.asIdeal.LiesOver (placeUnder' k E w).asIdeal :=
    ⟨(placeUnder'_asIdeal k E w).symm⟩
  rw [fracRelNormUnit_primeUnit k E w (placeUnder' k E w) (placeUnder'_asIdeal k E w).symm]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, primeUnit_val, FractionalIdeal.coe_mk0,
    ← FractionalIdeal.coeIdeal_pow, Ideal.inertiaDeg'_eq_inertiaDeg (placeUnder' k E w).asIdeal w.asIdeal]
  exact congrArg _
    (Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (placeUnder' k E w).asIdeal).symm

private theorem fracRelNormUnit_mk0 (I : (Ideal (𝓞 E))⁰) :
    ((fracRelNormUnit k E (FractionalIdeal.mk0 E I) :
        (FractionalIdeal ((𝓞 k)⁰) k)ˣ) : FractionalIdeal ((𝓞 k)⁰) k)
      = ((Ideal.relNorm (𝓞 k) (I : Ideal (𝓞 E)) : Ideal (𝓞 k)) :
          FractionalIdeal ((𝓞 k)⁰) k) := by
  obtain ⟨J, hJ⟩ := I
  have hJ' : J ≠ ⊥ := fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hJ) (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm)
  simp only at *
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ'
  | h₂ u hu =>
    obtain rfl : u = ⊤ := Ideal.isUnit_iff.mp hu
    rw [show FractionalIdeal.mk0 E (⟨(⊤ : Ideal (𝓞 E)), hJ⟩ : (Ideal (𝓞 E))⁰) = 1 from
        Units.ext (by rw [FractionalIdeal.coe_mk0, Units.val_one, FractionalIdeal.coeIdeal_top]),
      map_one, Units.val_one, ← Ideal.one_eq_top, map_one, Ideal.one_eq_top,
      FractionalIdeal.coeIdeal_top]
  | h₃ a p ha hp ih =>
    have ha' : a ≠ ⊥ := fun h => ha (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm)
    have hp_nz : p ∈ nonZeroDivisors (Ideal (𝓞 E)) :=
      mem_nonZeroDivisors_of_ne_zero
        (fun h => hp.ne_zero (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm))
    have ha_nz : a ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero ha
    let w : HeightOneSpectrum (𝓞 E) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hpw : (FractionalIdeal.mk0 E ⟨p, hp_nz⟩ : (FractionalIdeal ((𝓞 E)⁰) E)ˣ)
        = primeUnit E w := by
      unfold primeUnit; exact congrArg (FractionalIdeal.mk0 E) (Subtype.ext rfl)
    rw [show (⟨p * a, hJ⟩ : (Ideal (𝓞 E))⁰) = ⟨p, hp_nz⟩ * ⟨a, ha_nz⟩ from rfl,
      map_mul, map_mul (fracRelNormUnit k E), Units.val_mul, hpw,
      fracRelNormUnit_primeUnit_eq_relNorm k E w, FractionalIdeal.coe_mk0,
      ih ha_nz ha', map_mul (Ideal.relNorm (𝓞 k)), FractionalIdeal.coeIdeal_mul]

private theorem fracRelNormUnit_principalUnit (α : 𝓞 E) (hα : α ≠ 0) :
    ((fracRelNormUnit k E (principalUnit E α hα) :
        (FractionalIdeal ((𝓞 k)⁰) k)ˣ) : FractionalIdeal ((𝓞 k)⁰) k)
      = ((Ideal.span {Algebra.intNorm (𝓞 k) (𝓞 E) α} : Ideal (𝓞 k)) :
          FractionalIdeal ((𝓞 k)⁰) k) := by
  rw [show principalUnit E α hα = FractionalIdeal.mk0 E ⟨Ideal.span {α}, _⟩ from rfl,
    fracRelNormUnit_mk0 k E, Ideal.relNorm_singleton]

end HeckeCharacter
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end ICNNormUnit
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

section NormClassKill

set_option autoImplicit false

noncomputable section

namespace M4aP2

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField nonZeroDivisors IsDedekindDomain Deep.NTSupply"

variable (K : Type*) [Field K] [NumberField K] (q : ℕ)

private theorem norm_int_cast_eq_one_of_sub_one_mem {α : 𝓞 K}
    (hα : α - 1 ∈ Ideal.span {(q : 𝓞 K)}) :
    ((Algebra.norm ℤ α : ℤ) : ZMod q) = 1 := by
  classical
  obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.mp hα
  have hsm : q • γ = γ * (q : 𝓞 K) := by rw [nsmul_eq_mul, mul_comm]
  have hαeq : α = 1 + q • γ := by rw [hsm, hγ]; ring
  let b := RingOfIntegers.basis K
  have h1 : ((Algebra.norm ℤ α : ℤ) : ZMod q)
      = ((Int.castRingHom (ZMod q)).mapMatrix (Algebra.leftMulMatrix b α)).det := by
    rw [Algebra.norm_eq_matrix_det b, ← RingHom.map_det]; rfl
  have h0 : (q • (Int.castRingHom (ZMod q)).mapMatrix (Algebra.leftMulMatrix b γ)
      : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 K))
        (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (ZMod q)) = 0 := by
    ext i j
    simp [Matrix.smul_apply, nsmul_eq_mul]
  rw [h1, hαeq, map_add, map_one, map_nsmul, map_add, map_one, map_nsmul, h0, add_zero,
    Matrix.det_one]

private theorem norm_int_pos_of_totPos {α : 𝓞 K} (h0 : α ≠ 0)
    (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) :
    0 < Algebra.norm ℤ α := by
  classical
  set x : K := algebraMap (𝓞 K) K α with hxdef
  have hx0 : x ≠ 0 := by
    rw [hxdef, map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
    exact h0

  have hper : ∀ w : InfinitePlace K, ∃ r : ℝ, 0 < r ∧
      (∏ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ)), φ x) = (r : ℂ) := by
    intro w
    have hfibset : ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ))
        = {w.embedding, NumberField.ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h
        have h' : InfinitePlace.mk φ = InfinitePlace.mk w.embedding :=
          h.trans (InfinitePlace.mk_embedding w).symm
        rcases InfinitePlace.mk_eq_iff.mp h' with h1 | h2
        · exact Or.inl h1
        · exact Or.inr ((star_star φ).symm.trans (congrArg star h2))
      · rintro (h | h)
        · rw [h, InfinitePlace.mk_embedding]
        · rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
    by_cases hw : InfinitePlace.IsReal w
    · have hre : NumberField.ComplexEmbedding.conjugate w.embedding = w.embedding :=
        NumberField.ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
      refine ⟨(InfinitePlace.embedding_of_isReal hw) x, hpos _, ?_⟩
      rw [hfibset, hre, Finset.insert_eq_self.mpr (Finset.mem_singleton_self _),
        Finset.prod_singleton, InfinitePlace.embedding_of_isReal_apply hw]
    · have hne : w.embedding ≠ NumberField.ComplexEmbedding.conjugate w.embedding := by
        intro h
        exact hw (InfinitePlace.isReal_iff.mpr
          (NumberField.ComplexEmbedding.isReal_iff.mpr h.symm))
      have hval0 : w.embedding x ≠ 0 := by
        rw [← map_zero w.embedding]
        exact fun h => hx0 (w.embedding.injective h)
      refine ⟨Complex.normSq (w.embedding x), Complex.normSq_pos.mpr hval0, ?_⟩
      rw [hfibset, Finset.prod_pair hne,
        NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]
  choose r hrpos hreq using hper

  have htot : algebraMap ℚ ℂ (Algebra.norm ℚ x) = ((∏ w : InfinitePlace K, r w : ℝ) : ℂ) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x,
      ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ x)
        (fun σ : K →ₐ[ℚ] ℂ => σ x)
        (fun φ => by simp [RingHom.equivRatAlgHom_apply]),
      ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ x),
      Finset.prod_congr rfl fun w _ => hreq w, ← Complex.ofReal_prod]

  have hofreal : (((Algebra.norm ℚ x : ℚ) : ℝ) : ℂ) = ((∏ w : InfinitePlace K, r w : ℝ) : ℂ) := by
    rw [← htot, eq_ratCast (algebraMap ℚ ℂ) (Algebra.norm ℚ x), Complex.ofReal_ratCast]
  have hQpos : 0 < Algebra.norm ℚ x := by
    have hreal : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ w : InfinitePlace K, r w :=
      Complex.ofReal_inj.mp hofreal
    have hP : 0 < ∏ w : InfinitePlace K, r w :=
      Finset.prod_pos fun w _ => hrpos w
    rw [← Rat.cast_pos (K := ℝ), hreal]
    exact hP

  have hcoe : ((Algebra.norm ℤ α : ℤ) : ℚ) = Algebra.norm ℚ x := Algebra.coe_norm_int α
  have : (0 : ℚ) < ((Algebra.norm ℤ α : ℤ) : ℚ) := by rw [hcoe]; exact hQpos
  exact_mod_cast this

private theorem absNorm_coprime_of_not_dvd (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    Nat.Coprime (Ideal.absNorm v.asIdeal) q := by
  classical
  haveI hmax : v.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal v.isPrime v.ne_bot
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  obtain ⟨n, hp, hcard⟩ :=
    FiniteField.card (𝓞 K ⧸ v.asIdeal) (ringChar (𝓞 K ⧸ v.asIdeal))
  have habs : Ideal.absNorm v.asIdeal = ringChar (𝓞 K ⧸ v.asIdeal) ^ (n : ℕ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, ← hcard]
  rw [habs]
  refine Nat.Coprime.pow_left _ ?_
  by_contra hnc
  have hpq : ringChar (𝓞 K ⧸ v.asIdeal) ∣ q := by
    by_contra hdvd
    exact hnc ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd)
  apply hv
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  have hpmem : ((ringChar (𝓞 K ⧸ v.asIdeal) : ℕ) : 𝓞 K) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_natCast (Ideal.Quotient.mk v.asIdeal), CharP.cast_eq_zero]
  obtain ⟨t, ht⟩ := hpq
  have hqt : ((q : ℕ) : 𝓞 K)
      = ((ringChar (𝓞 K ⧸ v.asIdeal) : ℕ) : 𝓞 K) * ((t : ℕ) : 𝓞 K) := by
    rw [← Nat.cast_mul, ← ht]
  rw [SetLike.mem_coe, hqt]
  exact Ideal.mul_mem_right _ _ hpmem

private def normClass (v : HeightOneSpectrum (𝓞 K)) : (ZMod q)ˣ :=
  if h : Nat.Coprime (Ideal.absNorm v.asIdeal) q then ZMod.unitOfCoprime _ h else 1

private theorem normClass_coe (v : HeightOneSpectrum (𝓞 K))
    (h : Nat.Coprime (Ideal.absNorm v.asIdeal) q) :
    ((normClass K q v : (ZMod q)ˣ) : ZMod q) = (Ideal.absNorm v.asIdeal : ZMod q) := by
  rw [normClass, dif_pos h, ZMod.coe_unitOfCoprime]

private theorem raySymbol_normClass_coe {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hcop : I ⊔ Ideal.span {(q : 𝓞 K)} = ⊤) :
    ((raySymbol K (normClass K q) (I : FractionalIdeal ((𝓞 K)⁰) K) : (ZMod q)ˣ) : ZMod q)
      = (Ideal.absNorm I : ZMod q) := by
  classical
  have hI0 : I ≠ 0 := by simpa using hI
  have hvcop : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I →
      Nat.Coprime (Ideal.absNorm v.asIdeal) q := by
    intro v hvI
    refine absNorm_coprime_of_not_dvd K q v fun hdvd => ?_
    have h1 : I ≤ v.asIdeal := Ideal.le_of_dvd hvI
    have h2 : Ideal.span {(q : 𝓞 K)} ≤ v.asIdeal := Ideal.le_of_dvd hdvd
    have htop : (⊤ : Ideal (𝓞 K)) ≤ v.asIdeal := hcop ▸ sup_le h1 h2
    exact v.isPrime.ne_top (top_le_iff.mp htop)
  have hdvd_of_n : ∀ v : HeightOneSpectrum (𝓞 K),
      (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0 → v.asIdeal ∣ I := by
    intro v hv
    rwa [← Associates.count_ne_zero_iff_dvd hI0 v.irreducible]
  have hfuneq : (fun v : HeightOneSpectrum (𝓞 K) =>
        normClass K q v ^ FractionalIdeal.count K v (I : FractionalIdeal ((𝓞 K)⁰) K))
      = fun v => normClass K q v
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    funext v
    rw [FractionalIdeal.count_coe K v hI0, zpow_natCast]
  have hfin := hasFiniteMulSupport_raySymbol_factors K (normClass K q)
    (I : FractionalIdeal ((𝓞 K)⁰) K)
  rw [hfuneq] at hfin
  have hsym : raySymbol K (normClass K q) (I : FractionalIdeal ((𝓞 K)⁰) K)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    rw [raySymbol, hfuneq]
  have hcoe : ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
        normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors
          : (ZMod q)ˣ) : ZMod q)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          ((normClass K q v : ZMod q))
            ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    rw [show ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
          normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors
            : (ZMod q)ˣ) : ZMod q)
        = Units.coeHom (ZMod q) (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
        from rfl,
      MonoidHom.map_finprod (Units.coeHom (ZMod q)) hfin]
    exact finprod_congr fun v => by
      rw [Units.coeHom_apply, Units.val_pow_eq_pow_val]
  have hval : (fun v : HeightOneSpectrum (𝓞 K) =>
        ((normClass K q v : ZMod q))
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
      = fun v => ((Ideal.absNorm v.asIdeal : ZMod q))
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    funext v
    by_cases hv : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0
    · rw [hv, pow_zero, pow_zero]
    · rw [normClass_coe K q v (hvcop v (hdvd_of_n v hv))]
  have hnfin : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors) := by
    show (Function.mulSupport _).Finite
    refine ((Filter.eventually_cofinite.mp
      (FractionalIdeal.finite_factors (I : FractionalIdeal ((𝓞 K)⁰) K))).subset ?_)
    intro v hv
    rw [Function.mem_mulSupport] at hv
    simp only [Set.mem_setOf_eq]
    intro hcount
    apply hv
    rw [FractionalIdeal.count_coe K v hI0, Nat.cast_eq_zero] at hcount
    show Ideal.absNorm v.asIdeal
      ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors = 1
    rw [hcount, pow_zero]
  have hmfin : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) => v.maxPowDividing I) := by
    show (Function.mulSupport _).Finite
    refine ((Filter.eventually_cofinite.mp
      (FractionalIdeal.finite_factors (I : FractionalIdeal ((𝓞 K)⁰) K))).subset ?_)
    intro v hv
    rw [Function.mem_mulSupport] at hv
    simp only [Set.mem_setOf_eq]
    intro hcount
    apply hv
    rw [FractionalIdeal.count_coe K v hI0, Nat.cast_eq_zero] at hcount
    show v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors = 1
    rw [hcount, pow_zero]
  have hcast : ((∏ᶠ v : HeightOneSpectrum (𝓞 K), Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors : ℕ) : ZMod q)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ZMod q))
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    rw [show ((∏ᶠ v : HeightOneSpectrum (𝓞 K), Ideal.absNorm v.asIdeal
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors : ℕ) : ZMod q)
        = (Nat.castRingHom (ZMod q)) (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            Ideal.absNorm v.asIdeal
              ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
        from rfl,
      map_finprod (Nat.castRingHom (ZMod q)) hnfin]
    exact finprod_congr fun v => by rw [map_pow]; rfl
  have hnat : (∏ᶠ v : HeightOneSpectrum (𝓞 K), Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
      = Ideal.absNorm I := by
    conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI0]
    rw [map_finprod Ideal.absNorm hmfin]
    refine finprod_congr fun v => ?_
    show Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors
      = Ideal.absNorm (v.asIdeal
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
    exact (map_pow Ideal.absNorm _ _).symm
  rw [hsym, hcoe, hval, ← hcast, hnat]

private theorem normClassKillsRay {𝔣 : Ideal (𝓞 K)} (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣) :
    ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
      (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
      raySymbol K (normClass K q)
        ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1 := by
  intro α hα0 hα1 hpos
  have hspan : (Ideal.span {α} : Ideal (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hα0
  have hα1q : α - 1 ∈ Ideal.span {(q : 𝓞 K)} := Ideal.le_of_dvd hq𝔣 hα1
  have hcop : (Ideal.span {α} : Ideal (𝓞 K)) ⊔ Ideal.span {(q : 𝓞 K)} = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : α - (α - 1) = 1 := by ring
    exact h1 ▸ Submodule.sub_mem _
      (Ideal.mem_sup_left (Ideal.subset_span rfl))
      (Ideal.mem_sup_right hα1q)
  have h1 := raySymbol_normClass_coe K q hspan hcop
  rw [Ideal.absNorm_span_singleton] at h1
  have hpos' : 0 < Algebra.norm ℤ α := norm_int_pos_of_totPos K hα0 hpos
  have hnat : (((Algebra.norm ℤ α).natAbs : ℕ) : ZMod q) = 1 := by
    rw [← Int.cast_natCast (R := ZMod q), Int.natAbs_of_nonneg hpos'.le,
      norm_int_cast_eq_one_of_sub_one_mem K q hα1q]
  rw [hnat] at h1
  exact Units.val_eq_one.mp h1

private def normClassChar {𝔣 : Ideal (𝓞 K)} (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣) :
    NarrowRayClassGroup K 𝔣 →* (ZMod q)ˣ :=
  raySymbolDescend K (normClass K q) (normClassKillsRay K q hq𝔣)

private theorem normClassChar_primeClass {𝔣 : Ideal (𝓞 K)} (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    normClassChar K q hq𝔣 (primeClass K 𝔣 v hv) = normClass K q v :=
  raySymbolDescend_primeClass K (normClass K q) (normClassKillsRay K q hq𝔣) hv

end M4aP2
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

end NormClassKill
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"

section NormRayCompat

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField"

namespace M4aP2

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem prod_sub_one_mem {R : Type*} [CommRing R] (J : Ideal R)
    {ι : Type*} (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, f i - 1 ∈ J) :
    (∏ i ∈ s, f i) - 1 ∈ J := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons]
    have h1 := h a (Finset.mem_cons_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_cons_of_mem hi)
    have hsplit : f a * ∏ i ∈ s, f i - 1 = f a * ((∏ i ∈ s, f i) - 1) + (f a - 1) := by ring
    rw [hsplit]
    exact J.add_mem (Ideal.mul_mem_left _ _ h2) h1

private abbrev NCl := ↥(IntermediateField.normalClosure k E (AlgebraicClosure k))

@[reducible] private noncomputable def algONcl : Algebra (𝓞 k) (𝓞 (NCl k E)) :=
  (RingOfIntegers.mapRingHom (algebraMap k (NCl k E))).toAlgebra

attribute [local instance] algONcl

omit [NumberField k] [NumberField E] in
private theorem algONcl_coe (x : 𝓞 k) :
    (algebraMap (𝓞 k) (𝓞 (NCl k E)) x : NCl k E) = algebraMap k (NCl k E) (x : k) := rfl

omit [NumberField k] [NumberField E] in
private theorem algONcl_injective :
    Function.Injective (algebraMap (𝓞 k) (𝓞 (NCl k E))) := by
  intro a b h
  have h1 : algebraMap k (NCl k E) (a : k) = algebraMap k (NCl k E) (b : k) := by
    rw [← algONcl_coe, ← algONcl_coe, h]
  exact FaithfulSMul.algebraMap_injective (𝓞 k) k ((algebraMap k (NCl k E)).injective h1)

private scoped instance : IsScalarTower ℤ (𝓞 k) (𝓞 (NCl k E)) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

private scoped instance : Algebra.IsIntegral (𝓞 k) (𝓞 (NCl k E)) :=
  ⟨fun x => IsIntegral.tower_top (R := ℤ) (Algebra.IsIntegral.isIntegral x)⟩

private scoped instance : FaithfulSMul (𝓞 k) (𝓞 (NCl k E)) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (algONcl_injective k E)

variable {k E}

private noncomputable def embO (σ : E →ₐ[k] AlgebraicClosure k) :
    𝓞 E →+* 𝓞 (NCl k E) :=
  RingOfIntegers.mapRingHom
    ((σ.codRestrict _ fun x => σ.fieldRange_le_normalClosure ⟨x, rfl⟩ :
      E →ₐ[k] NCl k E) : E →+* NCl k E)

omit [NumberField k] [NumberField E] in
private theorem embO_coe (σ : E →ₐ[k] AlgebraicClosure k) (x : 𝓞 E) :
    algebraMap (NCl k E) (AlgebraicClosure k) ((embO σ x : 𝓞 (NCl k E)) : NCl k E)
    = σ (algebraMap (𝓞 E) E x) := rfl

omit [NumberField k] [NumberField E] in
private theorem embO_comp (σ : E →ₐ[k] AlgebraicClosure k) :
    (embO σ).comp (algebraMap (𝓞 k) (𝓞 E)) = algebraMap (𝓞 k) (𝓞 (NCl k E)) := by
  apply RingHom.ext
  intro x
  apply FaithfulSMul.algebraMap_injective (𝓞 (NCl k E)) (NCl k E)
  show (σ.codRestrict _ fun z => σ.fieldRange_le_normalClosure ⟨z, rfl⟩ :
      E →ₐ[k] NCl k E) (algebraMap k E (x : k))
    = algebraMap k (NCl k E) (x : k)
  exact (σ.codRestrict _ fun z => σ.fieldRange_le_normalClosure ⟨z, rfl⟩ :
    E →ₐ[k] NCl k E).commutes (x : k)

variable (k E)

private theorem intNorm_sub_one_mem_of_sub_one_mem (𝔠 : Ideal (𝓞 k)) (y : 𝓞 E)
    (hy : y - 1 ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 E))) :
    Algebra.intNorm (𝓞 k) (𝓞 E) y - 1 ∈ 𝔠 := by
  classical
  haveI : FiniteDimensional k E := FiniteDimensional.right ℚ k E

  have hmem : ∀ σ : E →ₐ[k] AlgebraicClosure k,
      embO σ y - 1 ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 (NCl k E))) := by
    intro σ
    have h1 : embO σ (y - 1) ∈ (𝔠.map (algebraMap (𝓞 k) (𝓞 E))).map (embO σ) :=
      Ideal.mem_map_of_mem (embO σ) hy
    rw [Ideal.map_map, embO_comp σ] at h1
    simpa [map_sub] using h1
  have hPsub : (∏ σ : E →ₐ[k] AlgebraicClosure k, embO σ y) - 1
      ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 (NCl k E))) :=
    prod_sub_one_mem _ _ _ fun σ _ => hmem σ

  have hPeq : (∏ σ : E →ₐ[k] AlgebraicClosure k, embO σ y)
      = algebraMap (𝓞 k) (𝓞 (NCl k E)) (Algebra.intNorm (𝓞 k) (𝓞 E) y) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (NCl k E)) (NCl k E)
    apply RingHom.injective (algebraMap (NCl k E) (AlgebraicClosure k))
    rw [show ((algebraMap (𝓞 (NCl k E)) (NCl k E))
        (∏ σ : E →ₐ[k] AlgebraicClosure k, embO σ y))
        = ∏ σ : E →ₐ[k] AlgebraicClosure k,
          ((embO σ y : 𝓞 (NCl k E)) : NCl k E) from map_prod _ _ _,
      map_prod]
    have hL : ∀ σ : E →ₐ[k] AlgebraicClosure k,
        algebraMap (NCl k E) (AlgebraicClosure k) ((embO σ y : 𝓞 (NCl k E)) : NCl k E)
        = σ (algebraMap (𝓞 E) E y) := fun σ => embO_coe σ y
    rw [Finset.prod_congr rfl fun σ _ => hL σ]
    have hR : algebraMap (NCl k E) (AlgebraicClosure k)
        ((algebraMap (𝓞 k) (𝓞 (NCl k E)) (Algebra.intNorm (𝓞 k) (𝓞 E) y) : NCl k E))
        = algebraMap k (AlgebraicClosure k)
          (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) := by
      rw [algONcl_coe]
      exact (IsScalarTower.algebraMap_apply k (NCl k E) (AlgebraicClosure k) _).symm
    rw [hR, Algebra.algebraMap_intNorm (A := 𝓞 k) (B := 𝓞 E) (K := k) (L := E)]
    exact (Algebra.norm_eq_prod_embeddings (K := k) (L := E)
      (E := AlgebraicClosure k) _).symm

  have hfin : algebraMap (𝓞 k) (𝓞 (NCl k E)) (Algebra.intNorm (𝓞 k) (𝓞 E) y - 1)
      ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 (NCl k E))) := by
    rw [map_sub, map_one, ← hPeq]
    exact hPsub
  haveI hTF : Module.IsTorsionFree (𝓞 k) (𝓞 (NCl k E)) := inferInstance
  haveI hFlat : Module.Flat (𝓞 k) (𝓞 (NCl k E)) := inferInstance
  haveI hFF : Module.FaithfullyFlat (𝓞 k) (𝓞 (NCl k E)) := inferInstance
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat
    (A := 𝓞 k) (B := 𝓞 (NCl k E)) 𝔠]
  exact Ideal.mem_comap.mpr hfin

private theorem intNorm_totPos_of_totPos (y : 𝓞 E) (hy0 : y ≠ 0)
    (hpos : ∀ τ : E →+* ℝ, 0 < τ (algebraMap (𝓞 E) E y)) :
    ∀ τ' : k →+* ℝ, 0 < τ' (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) := by
  intro τ'
  classical
  letI : Algebra k ℂ := (Complex.ofRealHom.comp τ').toAlgebra
  haveI : FiniteDimensional k E := FiniteDimensional.right ℚ k E
  set yE : E := algebraMap (𝓞 E) E y with hyEdef
  have hyE0 : yE ≠ 0 := fun h =>
    hy0 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mp h)
  have hσ0 : ∀ σ : E →ₐ[k] ℂ, σ yE ≠ 0 := fun σ h =>
    hyE0 ((map_eq_zero_iff _ (RingHom.injective (σ : E →+* ℂ))).mp h)
  have hstar_alg : ∀ c : k, (starRingEnd ℂ) (algebraMap k ℂ c) = algebraMap k ℂ c := fun c =>
    Complex.conj_ofReal _
  let conjA : (E →ₐ[k] ℂ) → (E →ₐ[k] ℂ) := fun σ =>
    { toRingHom := (starRingEnd ℂ).comp (σ : E →+* ℂ)
      commutes' := fun c => by
        show (starRingEnd ℂ) (σ (algebraMap k E c)) = algebraMap k ℂ c
        rw [σ.commutes]
        exact hstar_alg c }
  have hconjA_apply : ∀ (σ : E →ₐ[k] ℂ) (x : E), conjA σ x = (starRingEnd ℂ) (σ x) :=
    fun _ _ => rfl
  have hconjA_invol : ∀ σ, conjA (conjA σ) = σ := fun σ => AlgHom.ext fun x =>
    Complex.conj_conj (σ x)
  have hf_pair : ∀ σ : E →ₐ[k] ℂ,
      σ yE / (‖σ yE‖ : ℂ) * ((conjA σ) yE / (‖(conjA σ) yE‖ : ℂ)) = 1 := by
    intro σ
    have hz : σ yE ≠ 0 := hσ0 σ
    have hr0 : (‖σ yE‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    have hc : (conjA σ) yE = (starRingEnd ℂ) (σ yE) := rfl
    rw [hc, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj', ← sq]
    exact div_self (pow_ne_zero 2 hr0)
  have hf_fixed : ∀ σ : E →ₐ[k] ℂ, σ yE / (‖σ yE‖ : ℂ) ≠ 1 → conjA σ ≠ σ := by
    intro σ hf1 heq
    apply hf1
    have hreal : NumberField.ComplexEmbedding.IsReal (σ : E →+* ℂ) := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      ext x
      have h1 := congrArg (fun ψ : E →ₐ[k] ℂ => ψ x) heq
      simpa [NumberField.ComplexEmbedding.conjugate_coe_eq, hconjA_apply] using h1
    have hτpos := hpos hreal.embedding
    have hval : σ yE = ((hreal.embedding yE : ℝ) : ℂ) := (hreal.coe_embedding_apply yE).symm
    rw [hval, Complex.norm_real, Real.norm_of_nonneg hτpos.le]
    exact div_self (Complex.ofReal_ne_zero.mpr hτpos.ne')
  have hprod1 : ∏ σ : E →ₐ[k] ℂ, (σ yE / (‖σ yE‖ : ℂ)) = 1 :=
    Finset.prod_involution (fun σ _ => conjA σ) (fun σ _ => hf_pair σ)
      (fun σ _ h => hf_fixed σ h) (fun σ _ => Finset.mem_univ _) (fun σ _ => hconjA_invol σ)
  have hsplit : ∀ σ : E →ₐ[k] ℂ, σ yE = σ yE / (‖σ yE‖ : ℂ) * (‖σ yE‖ : ℂ) := fun σ =>
    (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (hσ0 σ)))).symm
  have hprodR : ∏ σ : E →ₐ[k] ℂ, σ yE = ((∏ σ : E →ₐ[k] ℂ, ‖σ yE‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    calc ∏ σ : E →ₐ[k] ℂ, σ yE
        = ∏ σ : E →ₐ[k] ℂ, (σ yE / (‖σ yE‖ : ℂ) * (‖σ yE‖ : ℂ)) :=
          Finset.prod_congr rfl fun σ _ => hsplit σ
      _ = (∏ σ : E →ₐ[k] ℂ, (σ yE / (‖σ yE‖ : ℂ))) * ∏ σ : E →ₐ[k] ℂ, (‖σ yE‖ : ℂ) :=
          Finset.prod_mul_distrib
      _ = ∏ σ : E →ₐ[k] ℂ, (‖σ yE‖ : ℂ) := by rw [hprod1, one_mul]
  have hbridge : algebraMap k ℂ (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y))
      = ∏ σ : E →ₐ[k] ℂ, σ yE := by
    rw [Algebra.algebraMap_intNorm (A := 𝓞 k) (B := 𝓞 E) (K := k) (L := E)]
    exact Algebra.norm_eq_prod_embeddings (K := k) (L := E) (E := ℂ) yE
  have hfinal : ((τ' (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) : ℝ) : ℂ)
      = ((∏ σ : E →ₐ[k] ℂ, ‖σ yE‖ : ℝ) : ℂ) := by
    rw [show ((τ' (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) : ℝ) : ℂ)
        = algebraMap k ℂ (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) from rfl,
      hbridge, hprodR]
  have hval := Complex.ofReal_injective hfinal
  rw [hval]
  exact Finset.prod_pos fun σ _ => norm_pos_iff.mpr (hσ0 σ)

end M4aP2
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end NormRayCompat
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section ICNRelNormRCG

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem intNorm_ne_zero {α : 𝓞 E} (hα : α ≠ 0) : Algebra.intNorm (𝓞 k) (𝓞 E) α ≠ 0 := by
  intro h
  have : Ideal.relNorm (𝓞 k) (Ideal.span {α}) = (⊥ : Ideal (𝓞 k)) := by
    rw [Ideal.relNorm_singleton, h, Ideal.span_singleton_eq_bot]
  exact hα (Ideal.span_singleton_eq_bot.mp (Ideal.relNorm_eq_bot_iff.mp this))

open scoped Classical in

private def fNC2 (𝔠 : Ideal (𝓞 k)) (w : HeightOneSpectrum (𝓞 E)) : NarrowRayClassGroup k 𝔠 :=
  if h : ¬ (placeUnder' k E w).asIdeal ∣ 𝔠
  then primeClass k 𝔠 (placeUnder' k E w) h ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal)
  else 1

omit [NumberField E] in
private theorem fNC2_of_dvd (𝔠 : Ideal (𝓞 k)) (w : HeightOneSpectrum (𝓞 E))
    (h : (placeUnder' k E w).asIdeal ∣ 𝔠) : fNC2 k E 𝔠 w = 1 := by
  simp [fNC2, h]

omit [NumberField E] in

private theorem fNC2_eq_mk_gcop (𝔠 : Ideal (𝓞 k)) (w : HeightOneSpectrum (𝓞 E)) :
    fNC2 k E 𝔠 w = NarrowRayClassGroup.mk k 𝔠 (gcopNC2 k E 𝔠 w) := by
  classical
  unfold fNC2 gcopNC2
  split
  · simp only [primeClass, ← map_pow]; rfl
  · rw [map_one]

private theorem coe_raySymbol_gcop_eq_fracRelNormUnit {𝔠 : Ideal (𝓞 k)} (α : 𝓞 E) (hα0 : α ≠ 0)
    (hα1 : α - 1 ∈ modulusExt k E 𝔠) :
    ((raySymbol E (gcopNC2 k E 𝔠)
        ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E)
      : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = fracRelNormUnit k E (principalUnit E α hα0) := by
  set J := ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E)
  have hfRN : fracRelNormUnit k E (principalUnit E α hα0)
      = raySymbol E
          (fun w => primeUnit k (placeUnder' k E w)
            ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal)) J := by
    show raySymbol E _ ((principalUnit E α hα0 : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) :
        FractionalIdeal ((𝓞 E)⁰) E) = _
    exact congrArg _ (principalUnit_val E α hα0)
  rw [hfRN]
  unfold raySymbol
  refine ((MonoidHom.map_finprod ((coprimeToModulus k 𝔠).subtype)
    (hasFiniteMulSupport_raySymbol_factors E (gcopNC2 k E 𝔠) J))).trans ?_
  refine finprod_congr (fun w => ?_)
  rw [map_zpow, Subgroup.coe_subtype]
  classical
  by_cases hw : (placeUnder' k E w).asIdeal ∣ 𝔠
  ·
    have hct : FractionalIdeal.count E w J = 0 :=
      count_span_singleton_eq_zero_of_sub_one_mem E hα0 hα1
        ((placeUnder'_dvd_iff k E 𝔠 w).mp hw)
    rw [hct]; simp
  ·
    simp only [gcopNC2]
    rw [dif_pos hw]

set_option maxSynthPendingDepth 3 in

private theorem relNormRCG_hkill (𝔠 : Ideal (𝓞 k)) (α : 𝓞 E) (hα0 : α ≠ 0)
    (hα1 : α - 1 ∈ modulusExt k E 𝔠) (hpos : ∀ τ : E →+* ℝ, 0 < τ (algebraMap (𝓞 E) E α)) :
    raySymbol E (fNC2 k E 𝔠)
      ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E) = 1 := by
  set J := ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E)

  have hstep1 : raySymbol E (fNC2 k E 𝔠) J
      = NarrowRayClassGroup.mk k 𝔠 (raySymbol E (gcopNC2 k E 𝔠) J) := by
    unfold raySymbol
    rw [show (fun v => fNC2 k E 𝔠 v ^ FractionalIdeal.count E v J)
        = (fun v => NarrowRayClassGroup.mk k 𝔠 (gcopNC2 k E 𝔠 v ^ FractionalIdeal.count E v J))
      from funext (fun w => by rw [fNC2_eq_mk_gcop, map_zpow])]
    exact (_root_.map_finprod (NarrowRayClassGroup.mk k 𝔠)
      (hasFiniteMulSupport_raySymbol_factors E (gcopNC2 k E 𝔠) J)).symm
  rw [hstep1]

  apply NarrowRayClassGroup.mk_eq_one_of_mem

  rw [coe_raySymbol_gcop_eq_fracRelNormUnit k E α hα0 hα1]

  apply Subgroup.subset_closure
  rw [mem_narrowRaySet_iff]
  exact ⟨Algebra.intNorm (𝓞 k) (𝓞 E) α, intNorm_ne_zero k E hα0,
    M4aP2.intNorm_sub_one_mem_of_sub_one_mem k E 𝔠 α hα1,
    M4aP2.intNorm_totPos_of_totPos k E α hα0 hpos,
    fracRelNormUnit_principalUnit k E α hα0⟩

private def relNormRCG (𝔠 : Ideal (𝓞 k)) :
    NarrowRayClassGroup E (modulusExt k E 𝔠) →* NarrowRayClassGroup k 𝔠 :=
  raySymbolDescend E (fNC2 k E 𝔠)
    (fun α hα0 hα1 hpos => relNormRCG_hkill k E 𝔠 α hα0 hα1 hpos)

private theorem relNormRCG_primeClass (𝔠 : Ideal (𝓞 k)) (h𝔠 : 𝔠 ≠ ⊥)
    (w : HeightOneSpectrum (𝓞 E)) (hw : ¬ w.asIdeal ∣ modulusExt k E 𝔠)
    (𝔭 : HeightOneSpectrum (𝓞 k)) (h𝔭w : w.asIdeal.under (𝓞 k) = 𝔭.asIdeal)
    (h𝔭 : ¬ 𝔭.asIdeal ∣ 𝔠) :
    relNormRCG k E 𝔠 (primeClass E (modulusExt k E 𝔠) w hw)
      = primeClass k 𝔠 𝔭 h𝔭 ^ (𝔭.asIdeal.inertiaDeg' w.asIdeal) := by
  have _ := h𝔠
  have heq : placeUnder' k E w = 𝔭 :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, h𝔭w])
  subst heq
  classical
  rw [relNormRCG, raySymbolDescend_primeClass E (fNC2 k E 𝔠) _ hw, fNC2,
    dif_pos h𝔭]

end HeckeCharacter
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end ICNRelNormRCG
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section ICNIdeleNorm

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

omit [NumberField k] [NumberField E] in

private theorem modulusExt_ne_bot {𝔠 : Ideal (𝓞 k)} (h𝔠 : 𝔠 ≠ ⊥) : modulusExt k E 𝔠 ≠ ⊥ := by
  intro h
  exact h𝔠 ((Ideal.map_eq_bot_iff_of_injective
    (f := algebraMap (𝓞 k) (𝓞 E)) (FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 E))).mp h)

set_option maxSynthPendingDepth 3 in

private theorem relNormRCG_mk (𝔠 : Ideal (𝓞 k)) (Y : ↥(coprimeToModulus E (modulusExt k E 𝔠))) :
    relNormRCG k E 𝔠 (NarrowRayClassGroup.mk E (modulusExt k E 𝔠) Y)
      = NarrowRayClassGroup.mk k 𝔠
          ⟨fracRelNormUnit k E (Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ),
            fracRelNormUnit_mem_coprimeToModulus k E Y.2⟩ := by
  rw [relNormRCG, raySymbolDescend_mk]

  rw [raySymbolHom_apply]
  set J := ((Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) : FractionalIdeal ((𝓞 E)⁰) E)

  have hstep1 : raySymbol E (fNC2 k E 𝔠) J
      = NarrowRayClassGroup.mk k 𝔠 (raySymbol E (gcopNC2 k E 𝔠) J) := by
    unfold raySymbol
    rw [show (fun v => fNC2 k E 𝔠 v ^ FractionalIdeal.count E v J)
        = (fun v => NarrowRayClassGroup.mk k 𝔠 (gcopNC2 k E 𝔠 v ^ FractionalIdeal.count E v J))
      from funext (fun w => by rw [fNC2_eq_mk_gcop, map_zpow])]
    exact (_root_.map_finprod (NarrowRayClassGroup.mk k 𝔠)
      (hasFiniteMulSupport_raySymbol_factors E (gcopNC2 k E 𝔠) J)).symm
  rw [hstep1]
  exact congrArg _ (Subtype.ext (coe_raySymbol_gcop_eq_fracRelNormUnit' k E _ Y.2))

private theorem fracRelNormUnit_principalUnit' (a : 𝓞 E) (ha : a ≠ 0) :
    fracRelNormUnit k E (principalUnit E a ha)
      = principalUnit k (Algebra.intNorm (𝓞 k) (𝓞 E) a) (intNorm_ne_zero k E ha) :=
  Units.ext ((fracRelNormUnit_principalUnit k E a ha).trans
    (principalUnit_val k _ (intNorm_ne_zero k E ha)).symm)

private theorem toPrincipalIdeal_algebraMap (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) (ha : a ≠ 0) :
    toPrincipalIdeal (𝓞 K) K
        (Units.mk0 (algebraMap (𝓞 K) K a)
          (fun h => ha (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 K) K) h)))
      = principalUnit K a ha :=
  Units.ext <| by
    rw [coe_toPrincipalIdeal, Units.val_mk0, principalUnit_val,
      FractionalIdeal.coeIdeal_span_singleton]

private theorem fracRelNormUnit_toPrincipalIdeal (α : Eˣ) :
    fracRelNormUnit k E (toPrincipalIdeal (𝓞 E) E α)
      = toPrincipalIdeal (𝓞 k) k (Units.map (Algebra.norm k) α) := by

  obtain ⟨x, y, hy, hαxy⟩ := IsFractionRing.div_surjective (A := 𝓞 E) (α : E)
  have hy0 : (y : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨y, hy⟩
  have hey : (algebraMap (𝓞 E) E) y ≠ 0 := fun h => hy0
    (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 E) E) h)
  have hx0 : x ≠ 0 := by
    intro h; subst h
    exact α.ne_zero (hαxy.symm.trans (by simp))
  have hex : (algebraMap (𝓞 E) E) x ≠ 0 := fun h => hx0
    (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 E) E) h)

  have hα_dec : α = Units.mk0 _ hex / Units.mk0 _ hey :=
    Units.ext (by rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0, ← hαxy])
  rw [hα_dec]
  simp only [map_div]

  rw [toPrincipalIdeal_algebraMap E x hx0, toPrincipalIdeal_algebraMap E y hy0,
    fracRelNormUnit_principalUnit' k E x hx0, fracRelNormUnit_principalUnit' k E y hy0]
  congr 1 <;>
    · rw [← toPrincipalIdeal_algebraMap k]
      exact congrArg _ (Units.ext (by
        simp only [Units.coe_map, Units.val_mk0]
        exact Algebra.algebraMap_intNorm (K := k) (L := E) _))

private theorem ideleContentHom_comp_ideleNorm (𝔠 : Ideal (𝓞 k)) (h𝔠 : 𝔠 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 k) k)ˣ)
    (hNrm_adjuster : ∀ {u : (AdeleRing (𝓞 E) E)ˣ} {α : Eˣ},
      IsAdjuster E (modulusExt k E 𝔠) u α →
      IsAdjuster k 𝔠 (Nrm u) (Units.map (Algebra.norm k) α))
    (hNrm_fadContent : ∀ u : (AdeleRing (𝓞 E) E)ˣ,
      fadContentHom k (projFin k (Nrm u)) = fracRelNormUnit k E (fadContentHom E (projFin E u))) :
    (ideleContentHom k 𝔠).comp Nrm
      = (relNormRCG k E 𝔠).comp (ideleContentHom E (modulusExt k E 𝔠)) := by
  ext u
  have h𝔠E := modulusExt_ne_bot k E h𝔠
  obtain ⟨α, hα⟩ := exists_isAdjuster E h𝔠E u
  have hNα := hNrm_adjuster hα
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
    ideleContentHom_apply k h𝔠 hNα, ideleContentHom_apply E h𝔠E hα,
    relNormRCG_mk k E 𝔠]

  congr 1
  apply Subtype.ext
  show fadContentHom k (projFin k _) = fracRelNormUnit k E (fadContentHom E (projFin E _))
  simp only [map_mul, map_inv]
  rw [hNrm_fadContent u]
  congr 1
  rw [projFin_principal, projFin_principal, fadContentHom_unitEmbedding,
    fadContentHom_unitEmbedding, fracRelNormUnit_toPrincipalIdeal]

end HeckeCharacter
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end ICNIdeleNorm
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section RelNormCTM

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem _root_.HeckeCharacter.coe_relNormCTM {𝔠 : Ideal (𝓞 k)} (Y : ↥(coprimeToModulus E (modulusExt k E 𝔠))) :
    ((relNormCTM k E 𝔠 Y : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = fracRelNormUnit k E (Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) := rfl

p2m_export "HeckeCharacter" "coe_relNormCTM"
private theorem relNormCTM_primeUnit {𝔠 : Ideal (𝓞 k)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt k E 𝔠) :
    ((relNormCTM k E 𝔠 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩
        : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = primeUnit k (placeUnder' k E w)
          ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal) := by
  exact fracRelNormUnit_primeUnit k E w (placeUnder' k E w) (placeUnder'_asIdeal k E w).symm

private theorem relNormCTM_principalUnit {𝔠 : Ideal (𝓞 k)} {α : 𝓞 E} (hα : α ≠ 0)
    (hαcop : principalUnit E α hα ∈ coprimeToModulus E (modulusExt k E 𝔠)) :
    ((relNormCTM k E 𝔠 ⟨principalUnit E α hα, hαcop⟩
        : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = principalUnit k (Algebra.intNorm (𝓞 k) (𝓞 E) α) (intNorm_ne_zero k E hα) := by
  exact fracRelNormUnit_principalUnit' k E α hα

private theorem mk_relNormCTM {𝔠 : Ideal (𝓞 k)} (Y : ↥(coprimeToModulus E (modulusExt k E 𝔠))) :
    NarrowRayClassGroup.mk k 𝔠 (relNormCTM k E 𝔠 Y)
      = relNormRCG k E 𝔠 (NarrowRayClassGroup.mk E (modulusExt k E 𝔠) Y) :=
  (relNormRCG_mk k E 𝔠 Y).symm

end HeckeCharacter
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end RelNormCTM
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section ArtinDischargeGlue

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom normRaySubgroup SecondInequalityCTM IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section DefN

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem principalCarrier_mem_normRaySubgroup {𝔣 : Ideal (𝓞 K)} {α : 𝓞 K} (hα0 : α ≠ 0) (hα1 : α - 1 ∈ 𝔣)
    (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) :
    (⟨principalUnit K α hα0, principalUnit_mem_coprimeToModulus K hα0 hα1⟩ : ↥(coprimeToModulus K 𝔣))
      ∈ normRaySubgroup K L 𝔣 :=
  le_sup_left (a := (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣))
    (Subgroup.mem_subgroupOf.mpr
      (Subgroup.subset_closure ⟨α, hα0, hα1, hpos, (principalUnit_val K α hα0).symm ▸ rfl⟩))

end DefN
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section hNP

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.HeckeCharacter"

private theorem relNormCTM_primeCarrier_of_inertiaDeg_eq_one {𝔠 : Ideal (𝓞 k)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt k E 𝔠) {v : HeightOneSpectrum (𝓞 k)} (hv : ¬ v.asIdeal ∣ 𝔠)
    (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal) (hf : v.asIdeal.inertiaDeg' w.asIdeal = 1) :
    relNormCTM k E 𝔠 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩
      = ⟨primeUnit k v, primeUnit_mem_coprimeToModulus k hv⟩ := by
  have heq : placeUnder' k E w = v :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, hwv])
  exact Subtype.ext (by rw [relNormCTM_primeUnit k E hw, heq, hf, pow_one])

end hNP
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section hcompat

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E]
  [Field N] [NumberField N] [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N]
  [IsScalarTower K M N] [IsScalarTower K E N] [IsGalois K M] [IsGalois E N]
  [IsMulCommutative (M ≃ₐ[K] M)] [IsMulCommutative (N ≃ₐ[E] N)]

p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.HeckeCharacter"

set_option maxSynthPendingDepth 3 in

private theorem artinSymbol_relNormCTM_primeCarrier (𝔣 : Ideal (𝓞 K)) {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt K E 𝔣) {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hI : ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    artinSymbol K M 𝔣 (relNormCTM K E 𝔣 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩)
      = resHom K M E N (artinSymbol E N (modulusExt K E 𝔣) ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩) := by
  have heq : placeUnder' K E w = v :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, hwv])
  have hvcop : ¬ (placeUnder' K E w).asIdeal ∣ 𝔣 := heq ▸ hv

  rw [show relNormCTM K E 𝔣 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩
      = (⟨primeUnit K (placeUnder' K E w), primeUnit_mem_coprimeToModulus K hvcop⟩
          : ↥(coprimeToModulus K 𝔣)) ^ ((placeUnder' K E w).asIdeal.inertiaDeg' w.asIdeal) from
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact relNormCTM_primeUnit K E hw),
    map_pow, artinSymbol_prime K M hvcop]

  rw [artinSymbol_prime E N hw, resHom_artinFrob K M E N v w hwv hI, heq]

set_option maxSynthPendingDepth 3 in

private theorem artinSymbol_comp_relNormCTM_eq (𝔣 : Ideal (𝓞 K))
    (hI_all : ∀ w : HeightOneSpectrum (𝓞 E), ¬ w.asIdeal ∣ modulusExt K E 𝔣 →
      ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    (artinSymbol K M 𝔣).comp (relNormCTM K E 𝔣)
      = (resHom K M E N).comp (artinSymbol E N (modulusExt K E 𝔣)) := by
  refine MonoidHom.eq_of_eqOn_dense (closure_primeCarriers_eq_top E (modulusExt K E 𝔣)) ?_
  rintro _ ⟨w, hw, rfl⟩
  have hv : ¬ (placeUnder' K E w).asIdeal ∣ 𝔣 := fun h => hw ((placeUnder'_dvd_iff K E 𝔣 w).mp h)
  exact artinSymbol_relNormCTM_primeCarrier K M E N 𝔣 hw hv (placeUnder'_asIdeal K E w).symm
    (hI_all w hw)

end hcompat
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end ArtinDischargeGlue
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section ArtinField

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom normRaySubgroup SecondInequalityCTM IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

open IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]
variable (L : IntermediateField K M) [IsGalois K L]
variable {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m)
variable {C : Type*} [Group C] (ψ : (ZMod m)ˣ ≃* C)

private theorem autToPow_eq_one_iff (τ : M ≃ₐ[K] M) : hζ.autToPow K τ = 1 ↔ τ ζ = ζ := by
  have key : ∀ v : ℕ, ζ ^ v = ζ ↔ (v : ZMod m) = 1 := fun v => by
    rw [show (ζ ^ v = ζ ↔ ζ ^ v = ζ ^ 1) by rw [pow_one], (hζ.isOfFinOrder (NeZero.ne m)).pow_eq_pow_iff_modEq,
      ← hζ.eq_orderOf, ← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  rw [← hζ.autToPow_spec K τ, key, ZMod.natCast_zmod_val, Units.val_eq_one]

private theorem mem_fixingSubgroup_intermediateField_iff (E : IntermediateField K M) (τ : M ≃ₐ[K] M) :
    τ ∈ E.fixingSubgroup ↔ ∀ x ∈ E, τ x = x :=
  _root_.mem_fixingSubgroup_iff _

private theorem apply_eq_self_iff_mem_fixingSubgroup_adjoin (τ : M ≃ₐ[K] M) : τ ζ = ζ ↔ τ ∈ K⟮ζ⟯.fixingSubgroup := by
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, adjoin_simple_le_iff, mem_fixedField_iff]
  constructor
  · intro h g hg
    exact (Subgroup.zpowers_le.mpr (show τ ∈ MulAction.stabilizer (M ≃ₐ[K] M) ζ from h) : _ ≤ _) hg
  · intro h
    exact h τ (Subgroup.mem_zpowers τ)

private noncomputable def galProd : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L) × C :=
  (AlgEquiv.restrictNormalHom L).prod (ψ.toMonoidHom.comp (hζ.autToPow K))

private theorem galProd_apply_fst (τ : M ≃ₐ[K] M) : (galProd L hζ ψ τ).1 = AlgEquiv.restrictNormalHom L τ := rfl

private theorem galProd_apply_snd (τ : M ≃ₐ[K] M) : (galProd L hζ ψ τ).2 = ψ (hζ.autToPow K τ) := rfl

private theorem galProd_fst_eq_one_iff (τ : M ≃ₐ[K] M) : (galProd L hζ ψ τ).1 = 1 ↔ τ ∈ L.fixingSubgroup := by
  rw [galProd_apply_fst, mem_fixingSubgroup_intermediateField_iff]
  exact AlgEquiv.restrictNormal_eq_one_iff L τ

private theorem galProd_snd_eq_one_iff (τ : M ≃ₐ[K] M) : (galProd L hζ ψ τ).2 = 1 ↔ τ ∈ K⟮ζ⟯.fixingSubgroup := by
  rw [galProd_apply_snd, EmbeddingLike.map_eq_one_iff, autToPow_eq_one_iff, apply_eq_self_iff_mem_fixingSubgroup_adjoin]

private theorem comap_galProd_prod_bot :
    ((⊤ : Subgroup (L ≃ₐ[K] L)).prod (⊥ : Subgroup C)).comap (galProd L hζ ψ) = K⟮ζ⟯.fixingSubgroup := by
  ext τ
  rw [Subgroup.mem_comap, Subgroup.mem_prod, ← galProd_snd_eq_one_iff L hζ ψ, Subgroup.mem_bot]
  exact ⟨fun h => h.2, fun h => ⟨Subgroup.mem_top _, h⟩⟩

private theorem comap_galProd_bot_prod :
    ((⊥ : Subgroup (L ≃ₐ[K] L)).prod (⊤ : Subgroup C)).comap (galProd L hζ ψ) = L.fixingSubgroup := by
  ext τ
  rw [Subgroup.mem_comap, Subgroup.mem_prod, ← galProd_fst_eq_one_iff L hζ ψ, Subgroup.mem_bot]
  exact ⟨fun h => h.1, fun h => ⟨h, Subgroup.mem_top _⟩⟩

private theorem galProd_injective (htop : L ⊔ K⟮ζ⟯ = ⊤) : Function.Injective (galProd L hζ ψ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro τ hτ
  rw [MonoidHom.mem_ker, Prod.ext_iff] at hτ
  have h1 : τ ∈ L.fixingSubgroup := (galProd_fst_eq_one_iff L hζ ψ τ).mp hτ.1
  have h2 : τ ∈ K⟮ζ⟯.fixingSubgroup := (galProd_snd_eq_one_iff L hζ ψ τ).mp hτ.2
  have h : τ ∈ (L ⊔ K⟮ζ⟯).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨h1, h2⟩
  rw [htop, mem_fixingSubgroup_intermediateField_iff] at h
  exact Subgroup.mem_bot.mpr (AlgEquiv.ext fun x => h x IntermediateField.mem_top)

private theorem galProd_bijective [Finite C] [FiniteDimensional K M] [IsGalois K M] (htop : L ⊔ K⟮ζ⟯ = ⊤)
    (hdeg : Module.finrank K M = Module.finrank K L * m.totient) : Function.Bijective (galProd L hζ ψ) := by
  classical
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨galProd_injective L hζ ψ htop, ?_⟩
  rw [Nat.card_prod, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank, hdeg, ← Nat.card_congr ψ.toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

private noncomputable def galEquivProd [Finite C] [FiniteDimensional K M] [IsGalois K M] (htop : L ⊔ K⟮ζ⟯ = ⊤)
    (hdeg : Module.finrank K M = Module.finrank K L * m.totient) : (M ≃ₐ[K] M) ≃* (L ≃ₐ[K] L) × C :=
  MulEquiv.ofBijective (galProd L hζ ψ) (galProd_bijective L hζ ψ htop hdeg)

private theorem galEquivProd_apply [Finite C] [FiniteDimensional K M] [IsGalois K M] (htop : L ⊔ K⟮ζ⟯ = ⊤)
    (hdeg : Module.finrank K M = Module.finrank K L * m.totient) (τ : M ≃ₐ[K] M) :
    galEquivProd L hζ ψ htop hdeg τ = galProd L hζ ψ τ := rfl

private noncomputable def auxField (H : Subgroup ((L ≃ₐ[K] L) × C)) : IntermediateField K M :=
  fixedField (H.comap (galProd L hζ ψ))

variable [FiniteDimensional K M]

private theorem fixingSubgroup_auxField (H : Subgroup ((L ≃ₐ[K] L) × C)) :
    (auxField L hζ ψ H).fixingSubgroup = H.comap (galProd L hζ ψ) :=
  fixingSubgroup_fixedField _

private theorem mem_fixingSubgroup_auxField {H : Subgroup ((L ≃ₐ[K] L) × C)} {τ : M ≃ₐ[K] M} (h : galProd L hζ ψ τ ∈ H) :
    τ ∈ (auxField L hζ ψ H).fixingSubgroup := by
  rw [fixingSubgroup_auxField]
  exact h

variable [IsGalois K M]

private theorem auxField_sup_adjoin_eq_top (htop : L ⊔ K⟮ζ⟯ = ⊤) {H : Subgroup ((L ≃ₐ[K] L) × C)}
    (hH : H ⊓ (⊤ : Subgroup (L ≃ₐ[K] L)).prod (⊥ : Subgroup C) = ⊥) : auxField L hζ ψ H ⊔ K⟮ζ⟯ = ⊤ := by
  have hfix : (auxField L hζ ψ H ⊔ K⟮ζ⟯).fixingSubgroup = ⊥ := by
    rw [IntermediateField.fixingSubgroup_sup, fixingSubgroup_auxField, ← comap_galProd_prod_bot L hζ ψ,
      ← Subgroup.comap_inf, hH, MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff _).mpr (galProd_injective L hζ ψ htop)]
  rw [← IsGalois.fixedField_fixingSubgroup (auxField L hζ ψ H ⊔ K⟮ζ⟯), hfix, IntermediateField.fixedField_bot]

private theorem adjoin_auxField_eq_top (htop : L ⊔ K⟮ζ⟯ = ⊤) {H : Subgroup ((L ≃ₐ[K] L) × C)}
    (hH : H ⊓ (⊤ : Subgroup (L ≃ₐ[K] L)).prod (⊥ : Subgroup C) = ⊥) :
    IntermediateField.adjoin (auxField L hζ ψ H) ({ζ} : Set M) = ⊤ := by
  apply IntermediateField.restrictScalars_injective K
  rw [restrictScalars_adjoin, restrictScalars_top, adjoin_union, adjoin_self]
  exact auxField_sup_adjoin_eq_top L hζ ψ htop hH

private theorem auxField_inf_eq_bot [Finite C] (htop : L ⊔ K⟮ζ⟯ = ⊤) (hdeg : Module.finrank K M = Module.finrank K L * m.totient)
    {H : Subgroup ((L ≃ₐ[K] L) × C)} (hH : H ⊔ (⊥ : Subgroup (L ≃ₐ[K] L)).prod (⊤ : Subgroup C) = ⊤) :
    auxField L hζ ψ H ⊓ L = ⊥ := by
  have hsup : H.comap (galProd L hζ ψ) ⊔ L.fixingSubgroup = ⊤ := by
    rw [← comap_galProd_bot_prod L hζ ψ, Subgroup.comap_sup_eq (galProd L hζ ψ) _ _ (galProd_bijective L hζ ψ htop hdeg).2,
      hH, Subgroup.comap_top]
  rw [eq_bot_iff, ← IsGalois.fixedField_top (F := K) (E := M)]
  rintro x ⟨hxE, hxL⟩ ⟨g, -⟩
  have hstab : H.comap (galProd L hζ ψ) ⊔ L.fixingSubgroup ≤ MulAction.stabilizer (M ≃ₐ[K] M) x :=
    sup_le (fun τ hτ => hxE ⟨τ, hτ⟩) (fun τ hτ => (_root_.mem_fixingSubgroup_iff _).mp hτ x hxL)
  exact hstab (by rw [hsup]; exact Subgroup.mem_top g)

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end ArtinField
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section CycCharCross

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField nonZeroDivisors IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin"
open scoped IsMulCommutative

namespace M4aP2

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

open _root_.NumberField.HeightOneSpectrum _root_.IsDedekindDomain.HeightOneSpectrum in
omit [NumberField M] [IsGalois K M] in

private theorem natCast_notMem_primeAbove (q : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (hq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    (q : 𝓞 M) ∉ primeAbove K M v := by
  intro hmem
  apply hq
  have h1 : (q : 𝓞 K) ∈ (primeAbove K M v).under (𝓞 K) := by
    rw [Ideal.under, Ideal.mem_comap, map_natCast]
    exact hmem
  rw [under_primeAbove] at h1
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  exact h1

open _root_.NumberField.HeightOneSpectrum _root_.IsDedekindDomain.HeightOneSpectrum in

private theorem artinFrob_primitiveRoot {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)
    (v : HeightOneSpectrum (𝓞 K)) (hq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    artinFrob K M v ζ = ζ ^ Ideal.absNorm v.asIdeal := by
  classical
  have hq0 : q ≠ 0 := NeZero.ne q
  have hint : IsIntegral ℤ ζ :=
    ⟨Polynomial.X ^ q - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hq0, by
      simp [hζ.pow_eq_one]⟩
  let ζO : 𝓞 M := ⟨ζ, hint⟩
  have hpow : ζO ^ q = 1 := Subtype.coe_injective (by push_cast; exact hζ.pow_eq_one)
  have H : (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 M) (artinFrob K M v)).IsArithFrobAt
      (primeAbove K M v) := isArithFrobAt_artinFrob K M v
  have h2 := H.apply_of_pow_eq_one hpow (natCast_notMem_primeAbove K M q v hq)
  have hcard : Nat.card (𝓞 K ⧸ (primeAbove K M v).under (𝓞 K)) = Ideal.absNorm v.asIdeal := by
    rw [under_primeAbove, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard] at h2
  have h3 := congrArg (algebraMap (𝓞 M) M) h2
  rw [map_pow] at h3
  exact h3

open _root_.NumberField.HeightOneSpectrum _root_.IsDedekindDomain.HeightOneSpectrum in

private theorem autToPow_artinFrob {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)
    (v : HeightOneSpectrum (𝓞 K)) (hq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    hζ.autToPow K (artinFrob K M v) = normClass K q v := by
  have hact := artinFrob_primitiveRoot K M hζ v hq
  have hcop := absNorm_coprime_of_not_dvd K q v hq
  refine Units.ext ?_
  rw [normClass_coe K q v hcop]
  have hspec := hζ.autToPow_spec K (artinFrob K M v)
  have hordζ : orderOf ζ = q := hζ.eq_orderOf.symm
  have hval : ζ ^ ((Ideal.absNorm v.asIdeal : ZMod q)).val = ζ ^ Ideal.absNorm v.asIdeal := by
    rw [ZMod.val_natCast, ← hordζ]
    exact pow_mod_orderOf ζ _
  have hvals : ((hζ.autToPow K (artinFrob K M v) : ZMod q)).val
      = ((Ideal.absNorm v.asIdeal : ZMod q)).val :=
    hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (by rw [hspec, hact]; exact hval.symm)
  exact ZMod.val_injective q hvals

open _root_.NumberField.HeightOneSpectrum _root_.IsDedekindDomain.HeightOneSpectrum in

private theorem autToPow_artinSymbol {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)
    [IsMulCommutative (M ≃ₐ[K] M)] {𝔣 : Ideal (𝓞 K)}
    (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣) (I : coprimeToModulus K 𝔣) :
    hζ.autToPow K (artinSymbol K M 𝔣 I) = raySymbol K (normClass K q) I.1 := by
  have hunf : artinSymbol K M 𝔣 I = raySymbolHom K 𝔣 (artinFrob K M) I := rfl
  rw [hunf, raySymbolHom_apply, map_raySymbol]
  unfold raySymbol
  refine finprod_congr fun v => ?_
  by_cases hcv : FractionalIdeal.count K v
      ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) = 0
  · rw [hcv, zpow_zero, zpow_zero]
  · have hv𝔣 : ¬ v.asIdeal ∣ 𝔣 := fun hdvd => hcv ((mem_coprimeToModulus_iff K).mp I.2 v hdvd)
    have hvq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)} := fun h => hv𝔣 (h.trans hq𝔣)
    simp only [Function.comp_apply]
    rw [autToPow_artinFrob K M hζ v hvq]

open _root_.NumberField.HeightOneSpectrum _root_.IsDedekindDomain.HeightOneSpectrum in

private theorem autToPow_artinSymbol_eq_normClassChar {q : ℕ} [NeZero q] {ζ : M}
    (hζ : IsPrimitiveRoot ζ q) [IsMulCommutative (M ≃ₐ[K] M)] {𝔣 : Ideal (𝓞 K)}
    (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣) (I : coprimeToModulus K 𝔣) :
    hζ.autToPow K (artinSymbol K M 𝔣 I)
      = normClassChar K q hq𝔣 (NarrowRayClassGroup.mk K 𝔣 I) := by
  rw [autToPow_artinSymbol K M hζ hq𝔣 I]
  unfold normClassChar
  rw [raySymbolDescend_mk, raySymbolHom_apply]

end M4aP2
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end CycCharCross
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section ArtinFrobProd

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom normRaySubgroup SecondInequalityCTM IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain IntermediateField Polynomial"

section FrobProd

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
variable (L : IntermediateField K M) [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
variable {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m) {C : Type*} [Group C] (ψ : (ZMod m)ˣ ≃* C)

private theorem galProd_artinFrob_fst (v : HeightOneSpectrum (𝓞 K)) (hI : ((primeAbove K M v).under (𝓞 L)).inertia (L ≃ₐ[K] L) = ⊥) :
    (galProd L hζ ψ (artinFrob K M v)).1 = artinFrob K L v := by
  rw [galProd_apply_fst]
  exact restrictNormal_artinFrob K L M v hI

omit [IsMulCommutative (L ≃ₐ[K] L)] in

private theorem galProd_artinFrob_snd (v : HeightOneSpectrum (𝓞 K)) (hm : ¬ v.asIdeal ∣ Ideal.span {(m : 𝓞 K)}) :
    (galProd L hζ ψ (artinFrob K M v)).2 = ψ (M4aP2.normClass K m v) := by
  rw [galProd_apply_snd, M4aP2.autToPow_artinFrob K M hζ v hm]

private theorem galProd_artinFrob (v : HeightOneSpectrum (𝓞 K)) (hI : ((primeAbove K M v).under (𝓞 L)).inertia (L ≃ₐ[K] L) = ⊥)
    (hm : ¬ v.asIdeal ∣ Ideal.span {(m : 𝓞 K)}) :
    galProd L hζ ψ (artinFrob K M v) = (artinFrob K L v, ψ (M4aP2.normClass K m v)) :=
  Prod.ext (galProd_artinFrob_fst K M L hζ ψ v hI) (galProd_artinFrob_snd K M L hζ ψ v hm)

end FrobProd
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section DegreeOne

attribute [local instance] Ideal.Quotient.field

variable {K M : Type*} [Field K] [Field M] [Algebra K M]
variable (E : IntermediateField K M)

private theorem smul_fixingSubgroupEquiv (τ : E.fixingSubgroup) (x : 𝓞 M) :
    (E.fixingSubgroupEquiv τ : M ≃ₐ[E] M) • x = (τ : M ≃ₐ[K] M) • x :=
  RingOfIntegers.ext rfl

private theorem isMulCommutative_gal_intermediateField [IsMulCommutative (M ≃ₐ[K] M)] : IsMulCommutative (M ≃ₐ[E] M) :=
  ⟨⟨fun a b => by
    have h := IsMulCommutative.is_comm.comm (a.restrictScalars K) (b.restrictScalars K)
    ext x
    exact AlgEquiv.congr_fun h x⟩⟩

variable {E}
variable [NumberField K] [NumberField M] [IsGalois K M]

private theorem card_quot_under_eq_of_fix {τ : M ≃ₐ[K] M} (hτ : τ ∈ E.fixingSubgroup) (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (H : IsArithFrobAt (𝓞 K) τ Q) :
    Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) = Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := by
  classical
  haveI hP : (Q.under (𝓞 E)).IsMaximal := Ideal.IsMaximal.under (𝓞 E) Q
  haveI hp : (Q.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) Q
  have hpP : (Q.under (𝓞 E)).under (𝓞 K) = Q.under (𝓞 K) := Ideal.under_under Q
  haveI : (Q.under (𝓞 E)).LiesOver (Q.under (𝓞 K)) := ⟨hpP.symm⟩
  have hPne : Q.under (𝓞 E) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hpne : Q.under (𝓞 K) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField K)
  haveI : Finite (𝓞 E ⧸ Q.under (𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hPne
  haveI : Finite (𝓞 K ⧸ Q.under (𝓞 K)) := Ideal.finiteQuotientOfFreeOfNeBot _ hpne
  set q := Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) with hqdef
  have hq1 : 1 < q := Finite.one_lt_card

  have hge : q ≤ Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) :=
    Nat.card_le_card_of_injective _ (algebraMap (𝓞 K ⧸ Q.under (𝓞 K)) (𝓞 E ⧸ Q.under (𝓞 E))).injective

  have hfix : ∀ a : 𝓞 E, τ • algebraMap (𝓞 E) (𝓞 M) a = algebraMap (𝓞 E) (𝓞 M) a := fun a =>
    RingOfIntegers.ext ((mem_fixingSubgroup_intermediateField_iff E τ).mp hτ _ (a : E).2)
  have hroot : ∀ y : 𝓞 E ⧸ Q.under (𝓞 E), y ^ q = y := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_pow, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow]
    have h := H (algebraMap (𝓞 E) (𝓞 M) a)
    rw [MulSemiringAction.toAlgHom_apply, hfix] at h
    exact h
  have hle : Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) ≤ q := by
    letI := Fintype.ofFinite (𝓞 E ⧸ Q.under (𝓞 E))
    have hne : (X ^ q - X : (𝓞 E ⧸ Q.under (𝓞 E))[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hq1
    have hsub : (Finset.univ : Finset (𝓞 E ⧸ Q.under (𝓞 E))).val ⊆ (X ^ q - X : (𝓞 E ⧸ Q.under (𝓞 E))[X]).roots := by
      intro y _
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, eval_sub, eval_pow, eval_X, hroot y, sub_self]
    have h := Polynomial.card_le_degree_of_subset_roots hsub
    rwa [Finset.card_univ, FiniteField.X_pow_card_sub_X_natDegree_eq _ hq1, ← Nat.card_eq_fintype_card] at h
  exact le_antisymm hle hge

private theorem inertiaDeg_under_eq_one_of_fix {τ : M ≃ₐ[K] M} (hτ : τ ∈ E.fixingSubgroup) (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (H : IsArithFrobAt (𝓞 K) τ Q) :
    (Q.under (𝓞 K)).inertiaDeg' (Q.under (𝓞 E)) = 1 := by
  classical
  haveI hP : (Q.under (𝓞 E)).IsMaximal := Ideal.IsMaximal.under (𝓞 E) Q
  haveI hp : (Q.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) Q
  haveI : (Q.under (𝓞 E)).LiesOver (Q.under (𝓞 K)) := ⟨(Ideal.under_under Q).symm⟩
  have hPne : Q.under (𝓞 E) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hpne : Q.under (𝓞 K) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField K)
  haveI : Finite (𝓞 E ⧸ Q.under (𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hPne
  haveI : Finite (𝓞 K ⧸ Q.under (𝓞 K)) := Ideal.finiteQuotientOfFreeOfNeBot _ hpne
  have hq1 : 1 < Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := Finite.one_lt_card
  have hcard := card_quot_under_eq_of_fix hτ Q H
  have hpow := Module.natCard_eq_pow_finrank (K := 𝓞 K ⧸ Q.under (𝓞 K)) (V := 𝓞 E ⧸ Q.under (𝓞 E))
  rw [hcard] at hpow
  rw [Ideal.inertiaDeg_algebraMap]
  have h1 : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ^ Module.finrank (𝓞 K ⧸ Q.under (𝓞 K)) (𝓞 E ⧸ Q.under (𝓞 E))
      = Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ^ 1 := by
    rw [pow_one]; exact hpow.symm
  exact Nat.pow_right_injective hq1 h1

private theorem relNorm_under_eq_of_fix {τ : M ≃ₐ[K] M} (hτ : τ ∈ E.fixingSubgroup) (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (H : IsArithFrobAt (𝓞 K) τ Q) :
    Ideal.relNorm (𝓞 K) (Q.under (𝓞 E)) = Q.under (𝓞 K) := by
  haveI : (Q.under (𝓞 E)).IsMaximal := Ideal.IsMaximal.under (𝓞 E) Q
  haveI : (Q.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) Q
  haveI : (Q.under (𝓞 E)).LiesOver (Q.under (𝓞 K)) := ⟨(Ideal.under_under Q).symm⟩
  rw [Ideal.relNorm_eq_pow_of_isMaximal (Q.under (𝓞 E)) (Q.under (𝓞 K)),
    ← Ideal.inertiaDeg'_eq_inertiaDeg (Q.under (𝓞 K)) (Q.under (𝓞 E)), inertiaDeg_under_eq_one_of_fix hτ Q H, pow_one]

private theorem isArithFrobAt_fixingSubgroupEquiv {τ : M ≃ₐ[K] M} (hτ : τ ∈ E.fixingSubgroup) (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (H : IsArithFrobAt (𝓞 K) τ Q) :
    IsArithFrobAt (𝓞 E) (E.fixingSubgroupEquiv ⟨τ, hτ⟩ : M ≃ₐ[E] M) Q := by
  intro x
  show (MulSemiringAction.toAlgHom (𝓞 E) (𝓞 M) (E.fixingSubgroupEquiv ⟨τ, hτ⟩ : M ≃ₐ[E] M)) x
      - x ^ Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) ∈ Q
  rw [MulSemiringAction.toAlgHom_apply, smul_fixingSubgroupEquiv, card_quot_under_eq_of_fix hτ Q H]
  exact H x

private theorem fixingSubgroupEquiv_eq_artinFrob [IsMulCommutative (M ≃ₐ[K] M)] {τ : M ≃ₐ[K] M} (hτ : τ ∈ E.fixingSubgroup)
    (Q : Ideal (𝓞 M)) [Q.IsMaximal] (H : IsArithFrobAt (𝓞 K) τ Q)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Q.under (𝓞 E) = w.asIdeal) (hI : Q.inertia (M ≃ₐ[E] M) = ⊥) :
    (E.fixingSubgroupEquiv ⟨τ, hτ⟩ : M ≃ₐ[E] M) = artinFrob E M w := by
  haveI := isMulCommutative_gal_intermediateField E (K := K) (M := M)
  exact eq_artinFrob_of_isArithFrobAt E M w (isArithFrobAt_fixingSubgroupEquiv hτ Q H) hw hI

end DegreeOne
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end ArtinFrobProd
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section ArtinDischargeHdCross

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom normRaySubgroup SecondInequalityCTM IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section hd

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E]
  [Field N] [NumberField N] [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N]
  [IsScalarTower K M N] [IsScalarTower K E N] [IsGalois K M] [IsGalois E N]
  [IsMulCommutative (M ≃ₐ[K] M)] [IsMulCommutative (N ≃ₐ[E] N)]

p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.HeckeCharacter"

set_option maxSynthPendingDepth 3 in

private theorem resHom_artinSymbol_primeCarrier_eq_artinFrob (𝔣 : Ideal (𝓞 K)) {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt K E 𝔣) {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal) (hf : v.asIdeal.inertiaDeg' w.asIdeal = 1)
    (hI : ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    resHom K M E N (artinSymbol E N (modulusExt K E 𝔣) ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩)
      = artinFrob K M v := by
  have hcompat := artinSymbol_relNormCTM_primeCarrier K M E N 𝔣 hw hv hwv hI
  rw [relNormCTM_primeCarrier_of_inertiaDeg_eq_one K E hw hv hwv hf, artinSymbol_prime K M hv] at hcompat
  exact hcompat.symm

private theorem exists_resHom_artinSymbol_primeCarrier_eq_zpow {σ : M ≃ₐ[K] M}
    (hσ : ∀ g : M ≃ₐ[K] M, g ∈ Subgroup.zpowers σ)
    (𝔣 : Ideal (𝓞 K)) {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt K E 𝔣) {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal) (hf : v.asIdeal.inertiaDeg' w.asIdeal = 1)
    (hI : ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    ∃ d : ℤ,
      resHom K M E N (artinSymbol E N (modulusExt K E 𝔣) ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩)
        = σ ^ d := by
  obtain ⟨d, hd⟩ := Subgroup.mem_zpowers_iff.mp (hσ (artinFrob K M v))
  exact ⟨d, (resHom_artinSymbol_primeCarrier_eq_artinFrob K M E N 𝔣 hw hv hwv hf hI).trans hd.symm⟩

end hd
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section hcross

set_option maxSynthPendingDepth 3

variable (k E E' : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra k E] [Algebra k E'] [Algebra E E'] [IsScalarTower k E E']

p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.HeckeCharacter"

omit [NumberField k] [NumberField E] [NumberField E'] in

private theorem placeUnder'_placeUnder' (w' : HeightOneSpectrum (𝓞 E')) :
    placeUnder' k E' w' = placeUnder' k E (placeUnder' E E' w') :=
  IsDedekindDomain.HeightOneSpectrum.ext
    (by rw [placeUnder'_asIdeal, placeUnder'_asIdeal, placeUnder'_asIdeal, Ideal.under_under])

private theorem fracRelNormUnit_fracRelNormUnit_primeUnit (w' : HeightOneSpectrum (𝓞 E')) :
    fracRelNormUnit k E (fracRelNormUnit E E' (primeUnit E' w'))
      = fracRelNormUnit k E' (primeUnit E' w') := by
  rw [fracRelNormUnit_primeUnit E E' w' (placeUnder' E E' w') (placeUnder'_asIdeal E E' w').symm,
    map_pow,
    fracRelNormUnit_primeUnit k E (placeUnder' E E' w') (placeUnder' k E (placeUnder' E E' w'))
      (placeUnder'_asIdeal k E _).symm,
    fracRelNormUnit_primeUnit k E' w' (placeUnder' k E' w') (placeUnder'_asIdeal k E' w').symm,
    ← pow_mul, placeUnder'_placeUnder' k E E']
  congr 1
  haveI : (placeUnder' k E (placeUnder' E E' w')).asIdeal.IsMaximal :=
    (placeUnder' k E (placeUnder' E E' w')).isMaximal
  haveI : (placeUnder' E E' w').asIdeal.IsMaximal := (placeUnder' E E' w').isMaximal
  haveI : (placeUnder' E E' w').asIdeal.LiesOver (placeUnder' k E (placeUnder' E E' w')).asIdeal :=
    ⟨(placeUnder'_asIdeal k E _).symm⟩
  haveI : w'.asIdeal.LiesOver (placeUnder' E E' w').asIdeal := ⟨(placeUnder'_asIdeal E E' w').symm⟩
  exact (Ideal.inertiaDeg_algebra_tower (placeUnder' k E (placeUnder' E E' w')).asIdeal
    (placeUnder' E E' w').asIdeal w'.asIdeal).symm

end hcross
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section ModulusCast
p2m_open "Deep.NTSupply NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain"
open scoped nonZeroDivisors
variable (F : Type*) [Field F] [NumberField F]

private theorem coe_modulusExt_cast {𝔠₁ 𝔠₂ : Ideal (𝓞 F)} (h : 𝔠₁ = 𝔠₂)
    (B : ↥(coprimeToModulus F 𝔠₁)) :
    ((h ▸ B : ↥(coprimeToModulus F 𝔠₂)) : (FractionalIdeal ((𝓞 F)⁰) F)ˣ)
      = (B : (FractionalIdeal ((𝓞 F)⁰) F)ˣ) := by subst h; rfl
end ModulusCast
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section hcross2
set_option maxSynthPendingDepth 3
variable (k E E' : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra k E] [Algebra k E'] [Algebra E E'] [IsScalarTower k E E']
p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.HeckeCharacter"

private theorem fracRelNormUnit_comp (u : (FractionalIdeal ((𝓞 E')⁰) E')ˣ) :
    fracRelNormUnit k E' u = fracRelNormUnit k E (fracRelNormUnit E E' u) := by
  have hmem : u ∈ coprimeToModulus E' ⊤ := fun v hv =>
    absurd (top_le_iff.mp (Ideal.le_of_dvd hv)) v.isPrime.ne_top
  have h := MonoidHom.eq_of_eqOn_dense (closure_primeCarriers_eq_top E' ⊤)
    (f := (fracRelNormUnit k E').comp (coprimeToModulus E' ⊤).subtype)
    (g := ((fracRelNormUnit k E).comp (fracRelNormUnit E E')).comp (coprimeToModulus E' ⊤).subtype)
    (by
      rintro _ ⟨w', _, rfl⟩
      exact (fracRelNormUnit_fracRelNormUnit_primeUnit k E E' w').symm)
  exact DFunLike.congr_fun h ⟨u, hmem⟩

omit [NumberField k] [NumberField E] [NumberField E'] in

private theorem modulusExt_modulusExt (𝔠 : Ideal (𝓞 k)) :
    modulusExt k E' 𝔠 = modulusExt E E' (modulusExt k E 𝔠) := by
  unfold modulusExt
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

omit [Algebra E E'] [IsScalarTower k E E'] in

private theorem exists_common_relNormCTM {E'' : Type*} [Field E''] [NumberField E'']
    [Algebra k E''] [Algebra E E''] [Algebra E' E''] [IsScalarTower k E E''] [IsScalarTower k E' E'']
    (𝔠 : Ideal (𝓞 k)) (B : ↥(coprimeToModulus E'' (modulusExt k E'' 𝔠))) :
    ∃ (b : ↥(coprimeToModulus E (modulusExt k E 𝔠))) (b' : ↥(coprimeToModulus E' (modulusExt k E' 𝔠))),
      relNormCTM k E 𝔠 b = relNormCTM k E' 𝔠 b' := by

  refine ⟨relNormCTM E E'' (modulusExt k E 𝔠) ((modulusExt_modulusExt k E E'' 𝔠) ▸ B),
    relNormCTM E' E'' (modulusExt k E' 𝔠) ((modulusExt_modulusExt k E' E'' 𝔠) ▸ B), ?_⟩
  apply Subtype.ext
  rw [coe_relNormCTM, coe_relNormCTM, coe_relNormCTM, coe_relNormCTM,
    coe_modulusExt_cast E'' (modulusExt_modulusExt k E E'' 𝔠) B,
    coe_modulusExt_cast E'' (modulusExt_modulusExt k E' E'' 𝔠) B,
    ← fracRelNormUnit_comp k E E'', ← fracRelNormUnit_comp k E' E'']

end hcross2
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end ArtinDischargeHdCross
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

set_option autoImplicit false

universe u v

noncomputable section

namespace CyclotomicDescent

section PowLaw
p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aKummer P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aKummer.NormBridge"
open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem relNorm_map_eq_pow (𝔟 : Ideal (𝓞 k)) :
    Ideal.relNorm (𝓞 k) (𝔟.map (algebraMap (𝓞 k) (𝓞 E))) = 𝔟 ^ Module.finrank k E := by
  rw [Ideal.relNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 k) k (𝓞 E) E]

private theorem fracRelNormUnit_extUnit_pow (v : HeightOneSpectrum (𝓞 k)) :
    M4aKummer.fracRelNormUnit k E (extUnit k E v) = primeUnit k v ^ Module.finrank k E := by
  apply Units.ext
  rw [extUnit, fracRelNormUnit_mk0, Units.val_pow_eq_pow_val, primeUnit_val, ← FractionalIdeal.coeIdeal_pow]
  exact congrArg _ (relNorm_map_eq_pow k E v.asIdeal)

private theorem pow_finrank_mem_range (𝔠 : Ideal (𝓞 k)) (X : ↥(coprimeToModulus k 𝔠)) :
    X ^ Module.finrank k E ∈ (M4aKummer.relNormCTM k E 𝔠).range := by
  obtain ⟨I, hI⟩ := X
  have key : ∀ J ∈ Subgroup.closure (primeGens k 𝔠),
      ∀ hJ : J ∈ coprimeToModulus k 𝔠, (⟨J, hJ⟩ : ↥(coprimeToModulus k 𝔠)) ^ Module.finrank k E
        ∈ (M4aKummer.relNormCTM k E 𝔠).range := by
    intro J hJ
    refine Subgroup.closure_induction (p := fun J (_ : J ∈ Subgroup.closure (primeGens k 𝔠)) =>
      ∀ hJ : J ∈ coprimeToModulus k 𝔠, (⟨J, hJ⟩ : ↥(coprimeToModulus k 𝔠)) ^ Module.finrank k E
        ∈ (M4aKummer.relNormCTM k E 𝔠).range)
      ?_ ?_ ?_ ?_ hJ
    · rintro _ ⟨v, hv, rfl⟩ hJ
      refine ⟨⟨extUnit k E v, extUnit_mem k E hv⟩, Subtype.ext ?_⟩
      rw [M4aKummer.coe_relNormCTM, fracRelNormUnit_extUnit_pow k E]
      rfl
    · intro _
      rw [show (⟨(1 : (FractionalIdeal ((𝓞 k)⁰) k)ˣ), _⟩ : ↥(coprimeToModulus k 𝔠)) = 1 from rfl, one_pow]
      exact one_mem _
    · intro a b ha hb iha ihb hab
      have ha' : a ∈ coprimeToModulus k 𝔠 := closure_primeGens_le k 𝔠 ha
      have hb' : b ∈ coprimeToModulus k 𝔠 := closure_primeGens_le k 𝔠 hb
      have hmul : (⟨a * b, hab⟩ : ↥(coprimeToModulus k 𝔠)) = ⟨a, ha'⟩ * ⟨b, hb'⟩ := rfl
      rw [hmul, mul_pow]
      exact mul_mem (iha ha') (ihb hb')
    · intro a ha iha hainv
      have ha' : a ∈ coprimeToModulus k 𝔠 := closure_primeGens_le k 𝔠 ha
      have hinv : (⟨a⁻¹, hainv⟩ : ↥(coprimeToModulus k 𝔠)) = ⟨a, ha'⟩⁻¹ := rfl
      rw [hinv, inv_pow]
      exact inv_mem (iha ha')
  exact key I (coprimeToModulus_le_closure k 𝔠 hI) hI

private theorem served_relNormCTM_eq (𝔠 : Ideal (𝓞 k)) :
    HeckeCharacter.relNormCTM k E 𝔠 = M4aKummer.relNormCTM k E 𝔠 := rfl

private theorem pow_finrank_mem_range_served (𝔠 : Ideal (𝓞 k)) (X : ↥(coprimeToModulus k 𝔠)) :
    X ^ Module.finrank k E ∈ (HeckeCharacter.relNormCTM k E 𝔠).range := by
  rw [served_relNormCTM_eq]
  exact pow_finrank_mem_range k E 𝔠 X

end PowLaw
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end CyclotomicDescent
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom normRaySubgroup SecondInequalityCTM IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
namespace NormRayDescent
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "Deep.NTSupply NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.HeckeCharacter"
open scoped nonZeroDivisors IsMulCommutative Pointwise

section PPlus

variable (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

private theorem relNormCTM_narrowRaySubgroup_subgroupOf_le (𝔣 : Ideal (𝓞 K))
    (I : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
    (hI : I ∈ (narrowRaySubgroup E (modulusExt K E 𝔣)).subgroupOf
      (coprimeToModulus E (modulusExt K E 𝔣))) :
    relNormCTM K E 𝔣 I ∈ (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) := by
  have hI' := Subgroup.mem_subgroupOf.mp hI
  have step : (relNormCTM K E 𝔣
      ⟨_, narrowRaySubgroup_le_coprimeToModulus E (modulusExt K E 𝔣) hI'⟩ : ↥(coprimeToModulus K 𝔣)).1
        ∈ narrowRaySubgroup K 𝔣 := by
    refine Subgroup.closure_induction
      (p := fun J hJ => ((relNormCTM K E 𝔣
          ⟨J, narrowRaySubgroup_le_coprimeToModulus E (modulusExt K E 𝔣) hJ⟩).1
        : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈ narrowRaySubgroup K 𝔣)
      ?_ ?_ (fun J₁ J₂ hJ₁ hJ₂ ih₁ ih₂ => ?_) (fun J hJ ih => ?_) hI'
    · intro J hJgen
      obtain ⟨α, hα0, hα1, hpos, hJα⟩ := (mem_narrowRaySet_iff E).mp hJgen
      have heq : (⟨J, narrowRaySubgroup_le_coprimeToModulus E _ (Subgroup.subset_closure hJgen)⟩
            : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
          = ⟨principalUnit E α hα0, principalUnit_mem_coprimeToModulus E hα0 hα1⟩ :=
        Subtype.ext (Units.ext (hJα.trans (principalUnit_val E α hα0).symm))
      show ((relNormCTM K E 𝔣 ⟨J, _⟩).1 : _) ∈ _
      rw [heq]
      refine Subgroup.subset_closure ?_
      rw [mem_narrowRaySet_iff, coe_relNormCTM, Subgroup.coe_mk]
      exact ⟨_, intNorm_ne_zero K E hα0, M4aP2.intNorm_sub_one_mem_of_sub_one_mem K E 𝔣 α hα1,
        M4aP2.intNorm_totPos_of_totPos K E α hα0 hpos,
        (congrArg Units.val (fracRelNormUnit_principalUnit' K E α hα0)).trans
          (principalUnit_val K _ (intNorm_ne_zero K E hα0))⟩
    · show ((relNormCTM K E 𝔣
          ⟨(1 : (FractionalIdeal ((𝓞 E)⁰) E)ˣ), narrowRaySubgroup_le_coprimeToModulus E _ (one_mem _)⟩
          ).1 : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈ narrowRaySubgroup K 𝔣
      rw [show (⟨(1 : (FractionalIdeal ((𝓞 E)⁰) E)ˣ), _⟩ : ↥(coprimeToModulus E _))
          = 1 from rfl, map_one]
      exact one_mem _
    · show ((relNormCTM K E 𝔣 ⟨J₁ * J₂, _⟩).1 : _) ∈ _
      rw [show (⟨J₁ * J₂, _⟩ : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
          = ⟨J₁, narrowRaySubgroup_le_coprimeToModulus E _ hJ₁⟩
            * ⟨J₂, narrowRaySubgroup_le_coprimeToModulus E _ hJ₂⟩ from rfl, map_mul]
      exact mul_mem ih₁ ih₂
    · show ((relNormCTM K E 𝔣 ⟨J⁻¹, _⟩).1 : _) ∈ _
      rw [show (⟨J⁻¹, _⟩ : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
          = (⟨J, narrowRaySubgroup_le_coprimeToModulus E _ hJ⟩ : ↥(coprimeToModulus E _))⁻¹ from rfl,
        map_inv]
      exact inv_mem ih
  rwa [show (⟨(I : (FractionalIdeal ((𝓞 E)⁰) E)ˣ), _⟩ : ↥(coprimeToModulus E _)) = I from rfl,
    ← Subgroup.mem_subgroupOf] at step

end PPlus
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section Range

set_option maxSynthPendingDepth 3

variable (K L E N : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field E] [NumberField E] [Field N] [NumberField N]
  [Algebra K L] [Algebra K E] [Algebra K N] [Algebra E N] [Algebra L N]
  [IsScalarTower K E N] [IsScalarTower K L N]

private theorem relNormCTM_range_le (𝔣 : Ideal (𝓞 K))
    (I : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
    (hI : I ∈ (relNormCTM E N (modulusExt K E 𝔣)).range) :
    relNormCTM K E 𝔣 I ∈ (relNormCTM K L 𝔣).range := by
  obtain ⟨x, hx⟩ := hI

  refine ⟨relNormCTM L N (modulusExt K L 𝔣) ((modulusExt_modulusExt K L N 𝔣) ▸
    ((modulusExt_modulusExt K E N 𝔣).symm ▸ x)), ?_⟩
  apply Subtype.ext
  rw [coe_relNormCTM, coe_relNormCTM, ← hx, coe_relNormCTM, coe_relNormCTM,
    coe_modulusExt_cast N (modulusExt_modulusExt K L N 𝔣),
    coe_modulusExt_cast N (modulusExt_modulusExt K E N 𝔣).symm,
    ← fracRelNormUnit_comp K L N, ← fracRelNormUnit_comp K E N]

end Range
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

section Main

set_option maxSynthPendingDepth 3

variable (K L E N : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field E] [NumberField E] [Field N] [NumberField N]
  [Algebra K L] [Algebra K E] [Algebra K N] [Algebra E N] [Algebra L N]
  [IsScalarTower K E N] [IsScalarTower K L N]

private theorem relNormCTM_normRaySubgroup_le (𝔣 : Ideal (𝓞 K))
    (I : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
    (hI : I ∈ normRaySubgroup E N (modulusExt K E 𝔣)) :
    relNormCTM K E 𝔣 I ∈ normRaySubgroup K L 𝔣 := by
  unfold normRaySubgroup at hI ⊢
  have key := (Subgroup.map_sup _ _ (relNormCTM K E 𝔣)).symm ▸
    Subgroup.mem_map_of_mem (relNormCTM K E 𝔣) hI
  have hle : Subgroup.map (relNormCTM K E 𝔣)
        ((narrowRaySubgroup E (modulusExt K E 𝔣)).subgroupOf (coprimeToModulus E (modulusExt K E 𝔣)))
      ⊔ Subgroup.map (relNormCTM K E 𝔣) (relNormCTM E N (modulusExt K E 𝔣)).range
      ≤ (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) ⊔ (relNormCTM K L 𝔣).range :=
    sup_le_sup
      (fun y hy => by obtain ⟨z, hz, hzy⟩ := hy
                      exact hzy ▸ relNormCTM_narrowRaySubgroup_subgroupOf_le K E 𝔣 z hz)
      (fun y hy => by obtain ⟨z, hz, hzy⟩ := hy
                      exact hzy ▸ relNormCTM_range_le K L E N 𝔣 z hz)
  exact hle key

end Main
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

end LanglandsTunnell.P2.Artin.NormRayDescent
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2"

namespace CyclotomicDescent

p2m_open_scoped "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField"

variable (k : Type u) (E : Type v) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
variable (p : ℕ) [NeZero p]

private abbrev Ep : Type v := CyclotomicField p E

private scoped instance finiteDimensional_Ep : FiniteDimensional k (Ep E p) :=
  Module.Finite.trans E (Ep E p)

private def ζ : Ep E p := IsCyclotomicExtension.zeta p E (Ep E p)

private theorem ζ_spec : IsPrimitiveRoot (ζ E p) p := IsCyclotomicExtension.zeta_spec p E (Ep E p)

private abbrev kζ : IntermediateField k (Ep E p) := IntermediateField.adjoin k {ζ E p}

private scoped instance numberField_kζ : NumberField ↥(kζ k E p) := NumberField.of_module_finite k _

omit [NumberField k] in
private theorem ζ_mem : ζ E p ∈ kζ k E p := IntermediateField.subset_adjoin k {ζ E p} (Set.mem_singleton _)

omit [NumberField k] in
private theorem hμ' : (primitiveRoots p ↥(kζ k E p)).Nonempty := by
  refine ⟨⟨ζ E p, ζ_mem k E p⟩, ?_⟩
  rw [mem_primitiveRoots (NeZero.pos p)]
  exact IsPrimitiveRoot.coe_submonoidClass_iff.mp (ζ_spec E p)

omit [NumberField k] in

private theorem isSplittingField_Ep_cyc :
    Polynomial.IsSplittingField E (Ep E p) ((Polynomial.cyclotomic p k).map (algebraMap k E)) := by
  rw [Polynomial.map_cyclotomic]
  exact IsCyclotomicExtension.splitting_field_cyclotomic p E (Ep E p)

private theorem isGalois_Ep [IsGalois k E] : IsGalois k (Ep E p) := by
  haveI : FiniteDimensional k E := FiniteDimensional.right ℚ k E
  obtain ⟨q, hq, hsp⟩ := IsGalois.is_separable_splitting_field (F := k) (E := E)
  haveI := hsp
  haveI := isSplittingField_Ep_cyc k E p
  haveI : Polynomial.IsSplittingField k (Ep E p) (q * Polynomial.cyclotomic p k) :=
    Polynomial.IsSplittingField.mul (K := E) (Ep E p) q (Polynomial.cyclotomic p k) hq.ne_zero
      (Polynomial.cyclotomic_ne_zero p k)
  haveI : Normal k (Ep E p) := Normal.of_isSplittingField (q * Polynomial.cyclotomic p k)
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

private theorem finrank_E_Ep : Module.finrank E (Ep E p) = (minpoly E (ζ E p)).natDegree := by
  rw [((ζ_spec E p).powerBasis E).finrank, IsPrimitiveRoot.powerBasis_dim]

private theorem finrank_k_kζ : Module.finrank k ↥(kζ k E p) = (minpoly k (ζ E p)).natDegree :=
  IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := k) (ζ E p))

omit [NumberField k] in

private theorem natDegree_minpoly_k_lt (hp : p.Prime) : (minpoly k (ζ E p)).natDegree < p := by
  have hφ : (Polynomial.cyclotomic p k).natDegree = p - 1 := by
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hp]
  have hle : (minpoly k (ζ E p)).natDegree ≤ (Polynomial.cyclotomic p k).natDegree := by
    refine Polynomial.natDegree_le_of_dvd (minpoly.dvd k (ζ E p) ?_) (Polynomial.cyclotomic_ne_zero p k)
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (ζ_spec E p).isRoot_cyclotomic (NeZero.pos p)
  have h1 : 1 < p := hp.one_lt
  omega

private theorem natDegree_minpoly_E_le : (minpoly E (ζ E p)).natDegree ≤ (minpoly k (ζ E p)).natDegree := by
  have hk : (minpoly k (ζ E p)).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral (R := k) (ζ E p))
  calc (minpoly E (ζ E p)).natDegree ≤ ((minpoly k (ζ E p)).map (algebraMap k E)).natDegree :=
        Polynomial.natDegree_le_of_dvd (minpoly.dvd_map_of_isScalarTower k E (ζ E p))
          ((hk.map (algebraMap k E)).ne_zero)
    _ = (minpoly k (ζ E p)).natDegree := hk.natDegree_map (algebraMap k E)

private theorem not_dvd_finrank_k_kζ (hp : p.Prime) : ¬ p ∣ Module.finrank k ↥(kζ k E p) := by
  intro h
  have hlt : Module.finrank k ↥(kζ k E p) < p := by
    rw [finrank_k_kζ]; exact natDegree_minpoly_k_lt k E p hp
  have hpos : 0 < Module.finrank k ↥(kζ k E p) := Module.finrank_pos
  exact absurd (Nat.le_of_dvd hpos h) (not_le.mpr hlt)

private theorem finrank_kζ_Ep (hp : p.Prime) (hdeg : Module.finrank k E = p) :
    Module.finrank ↥(kζ k E p) (Ep E p) = p := by
  have h1 : Module.finrank k ↥(kζ k E p) * Module.finrank ↥(kζ k E p) (Ep E p) = Module.finrank k (Ep E p) :=
    Module.finrank_mul_finrank k ↥(kζ k E p) (Ep E p)
  have h2 : Module.finrank k E * Module.finrank E (Ep E p) = Module.finrank k (Ep E p) :=
    Module.finrank_mul_finrank k E (Ep E p)
  have hd_le : Module.finrank E (Ep E p) ≤ Module.finrank k ↥(kζ k E p) := by
    rw [finrank_E_Ep, finrank_k_kζ]; exact natDegree_minpoly_E_le k E p
  have ha_pos : 0 < Module.finrank k ↥(kζ k E p) := Module.finrank_pos
  have hb_pos : 0 < Module.finrank ↥(kζ k E p) (Ep E p) := Module.finrank_pos
  have hpa : ¬ p ∣ Module.finrank k ↥(kζ k E p) := not_dvd_finrank_k_kζ k E p hp
  set a := Module.finrank k ↥(kζ k E p) with ha
  set b := Module.finrank ↥(kζ k E p) (Ep E p) with hb
  set d := Module.finrank E (Ep E p) with hd
  rw [hdeg] at h2
  have hab : a * b = p * d := by rw [h1, h2]
  have hpb : p ∣ b := ((Nat.Prime.dvd_mul hp).mp ⟨d, hab⟩).resolve_left hpa
  obtain ⟨c, hc⟩ := hpb
  have hac : a * c = d := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc p * (a * c) = a * (p * c) := by ring
      _ = a * b := by rw [hc]
      _ = p * d := hab
  have hc_le : c ≤ 1 := by
    apply Nat.le_of_mul_le_mul_left _ ha_pos
    rw [mul_one, hac]
    exact hd_le
  have hc_ne : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact absurd hc hb_pos.ne'
  have hc1 : c = 1 := by omega
  rw [hc, hc1, mul_one]

private theorem upstairs (hp : p.Prime) (hdeg : Module.finrank k E = p) [IsGalois k E]
    (hFI : ∀ (L : Type v) [Field L] [NumberField L] (M : Type v) [Field M] [NumberField M] [Algebra L M]
        [IsGalois L M], Module.finrank L M = p →
      ∀ 𝔣₀ : Ideal (NumberField.RingOfIntegers L), NumberField.PrimeNormIndex.IsAdmissibleModulusAt L M p 𝔣₀ →
        LanglandsTunnell.P2.Artin.IdeleFirstIneqDataAt L M 𝔣₀)
    (𝔣 : Ideal (𝓞 k)) :
    LanglandsTunnell.P2.Artin.SecondInequalityCTM ↥(kζ k E p) (Ep E p)
      (𝔣.map (algebraMap (𝓞 k) (𝓞 ↥(kζ k E p)))) := by
  haveI : IsGalois k (Ep E p) := isGalois_Ep k E p
  exact NumberField.PrimeNormIndex.secondInequalityCTM_of_primitiveRoots ↥(kζ k E p) (Ep E p) p hp
    (hμ' k E p) (finrank_kζ_Ep k E p hp hdeg) (hFI (Ep E p)) _

open _root_.NumberField _root_.P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField IsDedekindDomain Deep.NTSupply _root_.LanglandsTunnell.P2.Artin _root_.P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin in
open scoped nonZeroDivisors in

private theorem index_dvd (hp : p.Prime) (hdeg : Module.finrank k E = p) [IsGalois k E]
    (hFI : ∀ (L : Type v) [Field L] [NumberField L] (M : Type v) [Field M] [NumberField M] [Algebra L M]
        [IsGalois L M], Module.finrank L M = p →
      ∀ 𝔣₀ : Ideal (NumberField.RingOfIntegers L), NumberField.PrimeNormIndex.IsAdmissibleModulusAt L M p 𝔣₀ →
        LanglandsTunnell.P2.Artin.IdeleFirstIneqDataAt L M 𝔣₀)
    (𝔣 : Ideal (𝓞 k)) :
    (normRaySubgroup k E 𝔣).index ∣ p := by
  haveI : IsGalois k (Ep E p) := isGalois_Ep k E p

  have up : (normRaySubgroup ↥(kζ k E p) (Ep E p) (HeckeCharacter.modulusExt k ↥(kζ k E p) 𝔣)).index ∣ p := by
    have h := upstairs k E p hp hdeg hFI 𝔣
    unfold SecondInequalityCTM at h
    rwa [IsGalois.card_aut_eq_finrank, finrank_kζ_Ep k E p hp hdeg] at h

  set N := normRaySubgroup k E 𝔣 with hN
  set N' := normRaySubgroup ↥(kζ k E p) (Ep E p) (HeckeCharacter.modulusExt k ↥(kζ k E p) 𝔣) with hN'
  let f : ↥(coprimeToModulus ↥(kζ k E p) (HeckeCharacter.modulusExt k ↥(kζ k E p) 𝔣)) →*
      (↥(coprimeToModulus k 𝔣) ⧸ N) :=
    (QuotientGroup.mk' N).comp (HeckeCharacter.relNormCTM k ↥(kζ k E p) 𝔣)

  have hker : N' ≤ f.ker := by
    intro I hI
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact NormRayDescent.relNormCTM_normRaySubgroup_le k E ↥(kζ k E p) (Ep E p) 𝔣 I hI

  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨X, rfl⟩ := QuotientGroup.mk_surjective q
    have hXp : X ^ p ∈ N := by
      have h := pow_finrank_mem_range_served k E 𝔣 X
      rw [hdeg] at h
      exact Subgroup.mem_sup_right h
    obtain ⟨Y, hY⟩ := pow_finrank_mem_range_served k ↥(kζ k E p) 𝔣 X
    have hcop : Nat.Coprime (Module.finrank k ↥(kζ k E p)) p :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_finrank_k_kζ k E p hp))
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have hXam : ((X ^ (Module.finrank k ↥(kζ k E p) * m) : ↥(coprimeToModulus k 𝔣)) :
        ↥(coprimeToModulus k 𝔣) ⧸ N) = (X : ↥(coprimeToModulus k 𝔣) ⧸ N) := by
      have hq : Module.finrank k ↥(kζ k E p) * m = p * (Module.finrank k ↥(kζ k E p) * m / p) + 1 := by
        have h := Nat.div_add_mod (Module.finrank k ↥(kζ k E p) * m) p
        omega
      rw [QuotientGroup.eq, hq, pow_succ, mul_comm (X ^ (p * (Module.finrank k ↥(kζ k E p) * m / p))) X,
        mul_inv_rev, inv_mul_cancel_right]
      exact inv_mem (by rw [pow_mul]; exact Subgroup.pow_mem N hXp _)
    refine ⟨Y ^ m, ?_⟩
    rw [map_pow, MonoidHom.comp_apply, QuotientGroup.mk'_apply, hY, ← QuotientGroup.mk_pow, ← pow_mul]
    exact hXam

  calc N.index = (⊥ : Subgroup (↥(coprimeToModulus k 𝔣) ⧸ N)).index := by rw [Subgroup.index_bot]; rfl
    _ = (N'.map f).index := by rw [(Subgroup.map_eq_bot_iff (H := N') (f := f)).mpr hker]
    _ ∣ N'.index := N'.index_map_dvd hsurj
    _ ∣ p := up

open _root_.NumberField _root_.P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.NumberField _root_.LanglandsTunnell.P2.Artin _root_.P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin in

private theorem child (hp : p.Prime) (hdeg : Module.finrank k E = p) [IsGalois k E]
    (hFI : ∀ (L : Type v) [Field L] [NumberField L] (M : Type v) [Field M] [NumberField M] [Algebra L M]
        [IsGalois L M], Module.finrank L M = p →
      ∀ 𝔣₀ : Ideal (NumberField.RingOfIntegers L), NumberField.PrimeNormIndex.IsAdmissibleModulusAt L M p 𝔣₀ →
        LanglandsTunnell.P2.Artin.IdeleFirstIneqDataAt L M 𝔣₀)
    (𝔣 : Ideal (𝓞 k)) :
    SecondInequalityCTM k E 𝔣 := by
  haveI : FiniteDimensional k E := Module.Finite.of_restrictScalars_finite ℚ k E
  unfold SecondInequalityCTM
  rw [IsGalois.card_aut_eq_finrank, hdeg]
  exact index_dvd k E p hp hdeg hFI 𝔣

end CyclotomicDescent
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.CyclotomicDescent"

theorem solution
    (k : Type u) (E : Type v) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
    (p : ℕ) (hp : p.Prime) (hdeg : Module.finrank k E = p)
    [IsGalois k E]
    (hFI : ∀ (L : Type v) [Field L] [NumberField L] (M : Type v) [Field M] [NumberField M] [Algebra L M]
        [IsGalois L M], Module.finrank L M = p →
      ∀ 𝔣₀ : Ideal (NumberField.RingOfIntegers L), NumberField.PrimeNormIndex.IsAdmissibleModulusAt L M p 𝔣₀ →
        LanglandsTunnell.P2.Artin.IdeleFirstIneqDataAt L M 𝔣₀)
    (𝔣 : Ideal (NumberField.RingOfIntegers k)) :
    LanglandsTunnell.P2.Artin.SecondInequalityCTM k E 𝔣 :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  CyclotomicDescent.child k E p hp hdeg hFI 𝔣

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime.CyclotomicDescent"

end S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime
end P2MW
export P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime (solution)
