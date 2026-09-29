-- Prove2me | solution 1 for NumberField.exists_artinSymbol_principalUnit_eq_prod_of_isConj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/955a2d78-91d1-52d1-9e27-dd17a5550318

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Theorems.Thm_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree
import Theorems.Thm_LT_Artin_eq_artinFrob_of_isArithFrobAt
import Theorems.Thm_NumberField_exists_ne_zero_and_sub_one_mem_and_lt_zero_iff
import Theorems.Thm_NumberField_apply_norm_lt_zero_iff_odd_card_filter
import Theorems.Thm_NumberField_raySymbol_artinFrob_apply_eq_pow_absNorm_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_artinSymbol_principalUnit_eq_prod_of_isConj
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions"
p2m_attr_erase "instance" "RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe"
p2m_attr_erase "simp" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply"
p2m_attr_erase "simp" "Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option linter.unusedSectionVars false

noncomputable section

section SignBridge
p2m_open "NumberField P2MW.S_NumberField_exists_artinSymbol_principalUnit_eq_prod_of_isConj.NumberField"

namespace NumberField p2m_export "NumberField" "ComplexEmbedding.isReal_iff of_module_finite ComplexEmbedding.IsReal.coe_embedding_apply mk Embeddings.card ComplexEmbedding.isConj_apply_apply place ComplexEmbedding.IsConj RingOfIntegers.coe_eq_zero_iff RingOfIntegers RingOfIntegers.coe_injective ComplexEmbedding.IsReal ComplexEmbedding.conjugate RingOfIntegers.coe_eq_algebraMap RingOfIntegers.coe_ne_zero_iff ComplexEmbedding.exists_comp_symm_eq_of_comp_eq ComplexEmbedding.conjugate_coe_eq NormIndex.IsAdmissibleModulusOfDegree exists_ne_zero_and_sub_one_mem_and_lt_zero_iff apply_norm_lt_zero_iff_odd_card_filter raySymbol_artinFrob_apply_eq_pow_absNorm_of_pow_eq_one" end NumberField
p2m_open_scoped "NumberField" in
theorem NumberField.exists_ne_zero_dvd_sub_one_forall_lt_zero_iff
    (K : Type*) [Field K] [NumberField K] (m : ℕ) (hm : m ≠ 0) (s : Set (K →+* ℝ)) :
    ∃ α : 𝓞 K, α ≠ 0 ∧ (m : 𝓞 K) ∣ α - 1 ∧
      ∀ τ : K →+* ℝ, τ (algebraMap (𝓞 K) K α) < 0 ↔ τ ∈ s := by
  have hbot : Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hm
  obtain ⟨α, hα, hmem, hsign⟩ :=
    NumberField.exists_ne_zero_and_sub_one_mem_and_lt_zero_iff K _ hbot s
  exact ⟨α, hα, Ideal.mem_span_singleton.mp hmem, hsign⟩

end SignBridge

namespace RecipSign

p2m_open "NumberField P2MW.S_NumberField_exists_artinSymbol_principalUnit_eq_prod_of_isConj.NumberField IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin NumberField.NormIndex HeckeCharacter"

open scoped IsMulCommutative nonZeroDivisors Pointwise

section Ramification

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]

omit [NumberField K] [NumberField F] [IsGalois K F] in

theorem mem_inertia_smul_iff (g σ : F ≃ₐ[K] F) (Q : Ideal (𝓞 F)) :
    σ ∈ (g • Q).inertia (F ≃ₐ[K] F) ↔ g⁻¹ * σ * g ∈ Q.inertia (F ≃ₐ[K] F) := by
  simp only [Ideal.inertia, AddSubgroup.mem_inertia]
  constructor
  · intro h x
    have := h (g • x)
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub,
      inv_smul_smul] at this
    simpa [mul_smul] using this
  · intro h x
    have := h (g⁻¹ • x)
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub]
    simpa [mul_smul] using this

theorem inertia_eq_bot_of_primeAbove (v : HeightOneSpectrum (𝓞 K))
    (hv : (primeAbove K F v).inertia (F ≃ₐ[K] F) = ⊥)
    (Q : Ideal (𝓞 F)) [Q.IsPrime] (hQ : Q.under (𝓞 K) = v.asIdeal) :
    Q.inertia (F ≃ₐ[K] F) = ⊥ := by
  haveI hGG : IsGaloisGroup (F ≃ₐ[K] F) (𝓞 K) (𝓞 F) := isGaloisGroup_ringOfIntegers K F
  haveI := hGG.isInvariant
  haveI : (primeAbove K F v).IsPrime := (primeAbove_isMaximal K F v).isPrime
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 F) (F ≃ₐ[K] F)
    (primeAbove K F v) Q ((under_primeAbove K F v).trans hQ.symm)
  rw [eq_bot_iff]
  intro σ hσ
  rw [hg, mem_inertia_smul_iff] at hσ
  rw [hv, Subgroup.mem_bot] at hσ
  rw [Subgroup.mem_bot]
  calc σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
    _ = 1 := by rw [hσ]; group

theorem finite_ramified :
    {v : HeightOneSpectrum (𝓞 K) | (primeAbove K F v).inertia (F ≃ₐ[K] F) ≠ ⊥}.Finite := by
  classical
  haveI hGG : IsGaloisGroup (F ≃ₐ[K] F) (𝓞 K) (𝓞 F) := isGaloisGroup_ringOfIntegers K F

  have hmove : ∀ σ : F ≃ₐ[K] F, σ ≠ 1 → ∃ x : 𝓞 F, σ • x - x ≠ 0 := by
    intro σ hσ
    by_contra h
    push Not at h
    apply hσ
    haveI : FaithfulSMul (F ≃ₐ[K] F) (𝓞 F) := hGG.faithful
    exact FaithfulSMul.eq_of_smul_eq_smul (M := F ≃ₐ[K] F) (α := 𝓞 F)
      fun x ↦ by rw [one_smul]; exact sub_eq_zero.1 (h x)
  choose! x hx using hmove
  set N : 𝓞 F := ∏ σ ∈ (Finset.univ.filter fun σ : F ≃ₐ[K] F ↦ σ ≠ 1), (σ • x σ - x σ) with hN
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun σ hσ => hx σ (Finset.mem_filter.1 hσ).2
  have hNmem : ∀ σ : F ≃ₐ[K] F, σ ≠ 1 → ∀ P : Ideal (𝓞 F), (∀ y : 𝓞 F, σ • y - y ∈ P) → N ∈ P := by
    intro σ hσ P hP
    have hmem : σ ∈ Finset.univ.filter fun σ : F ≃ₐ[K] F ↦ σ ≠ 1 :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hσ⟩
    rw [hN, ← Finset.mul_prod_erase _ _ hmem]
    exact Ideal.mul_mem_right _ _ (hP (x σ))
  let f : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 F) := fun v ↦
    ⟨primeAbove K F v, (primeAbove_isMaximal K F v).isPrime, primeAbove_ne_bot K F v⟩
  have hinj : Function.Injective f := by
    intro v w h
    have h' : primeAbove K F v = primeAbove K F w := congrArg HeightOneSpectrum.asIdeal h
    apply HeightOneSpectrum.ext
    rw [← under_primeAbove K F v, ← under_primeAbove K F w, h']
  refine Set.Finite.of_finite_image ?_ hinj.injOn
  refine (Ideal.finite_factors (I := Ideal.span {N}) ?_).subset ?_
  · rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact hN0
  · rintro P ⟨v, hv, rfl⟩
    rw [Set.mem_setOf_eq] at hv ⊢
    obtain ⟨σ, hσI, hσ1⟩ : ∃ σ, σ ∈ (primeAbove K F v).inertia (F ≃ₐ[K] F) ∧ σ ≠ 1 := by
      by_contra h
      push Not at h
      exact hv ((Subgroup.eq_bot_iff_forall _).mpr fun σ hσ => h σ hσ)
    show primeAbove K F v ∣ Ideal.span {N}
    rw [Ideal.dvd_span_singleton]
    exact hNmem σ hσ1 _ hσI

def ramified : Finset (HeightOneSpectrum (𝓞 K)) := (finite_ramified K F).toFinset

theorem mem_ramified {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ ramified K F ↔ (primeAbove K F v).inertia (F ≃ₐ[K] F) ≠ ⊥ := by
  simp [ramified]

def modulus (n : ℕ) : Ideal (𝓞 K) :=
  ∏ v ∈ ramified K F, v.asIdeal ^ admissibleExpOfDegree K n v

theorem modulus_ne_bot (n : ℕ) : modulus K F n ≠ ⊥ := by
  rw [modulus, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  intro v _
  exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)

theorem isAdmissibleModulusOfDegree_modulus (n : ℕ) :
    IsAdmissibleModulusOfDegree K F n (modulus K F n) := by
  refine ⟨modulus_ne_bot K F n, fun v hv => ?_⟩
  exact Finset.dvd_prod_of_mem _ ((mem_ramified K F).mpr hv)

theorem inertia_eq_bot_of_not_dvd {n : ℕ} {𝔣 : Ideal (𝓞 K)} (h𝔣 : modulus K F n ∣ 𝔣)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣)
    (Q : Ideal (𝓞 F)) [Q.IsPrime] (hQ : Q.under (𝓞 K) = v.asIdeal) :
    Q.inertia (F ≃ₐ[K] F) = ⊥ := by
  apply inertia_eq_bot_of_primeAbove K F v _ Q hQ
  by_contra h
  apply hv
  have h1 : v.asIdeal ^ admissibleExpOfDegree K n v ∣ modulus K F n :=
    Finset.dvd_prod_of_mem _ ((mem_ramified K F).mpr h)
  have h2 : v.asIdeal ∣ v.asIdeal ^ admissibleExpOfDegree K n v :=
    dvd_pow_self _ (by unfold admissibleExpOfDegree; omega)
  exact h2.trans (h1.trans h𝔣)

def cmod : Ideal (𝓞 K) := modulus K F (Nat.card (F ≃ₐ[K] F))

theorem cmod_ne_bot : cmod K F ≠ ⊥ := modulus_ne_bot K F _

theorem absNorm_cmod_ne_zero : Ideal.absNorm (cmod K F) ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff]; exact cmod_ne_bot K F

theorem inertia_eq_bot_of_mem {α : 𝓞 K} (hα : α - 1 ∈ cmod K F) (v : HeightOneSpectrum (𝓞 K))
    (hv : α ∈ v.asIdeal) (Q : Ideal (𝓞 F)) (hQp : Q.IsPrime) (hQ : Q.under (𝓞 K) = v.asIdeal) :
    Q.inertia (F ≃ₐ[K] F) = ⊥ := by
  refine inertia_eq_bot_of_not_dvd K F (dvd_refl (cmod K F)) v ?_ Q hQ
  intro hdvd
  have h1 : α - 1 ∈ v.asIdeal := Ideal.le_of_dvd hdvd hα
  have : (1 : 𝓞 K) ∈ v.asIdeal := by
    have := v.asIdeal.sub_mem hv h1
    simpa using this
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)

end Ramification

section NarrowRay

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F] [IsMulCommutative (F ≃ₐ[K] F)]

theorem ker_artinSymbol_cmod :
    (artinSymbol K F (cmod K F)).ker = normRaySubgroup K F (cmod K F) := by
  haveI : Finite (F ≃ₐ[K] F) := inferInstance
  exact (LanglandsTunnell.Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree
    K F (Nat.card (F ≃ₐ[K] F)) Nat.card_pos.ne' (fun x => pow_card_eq_one')
    (cmod K F) (isAdmissibleModulusOfDegree_modulus K F _)).2

theorem raySymbol_principal_eq_artinSymbol {𝔣 : Ideal (𝓞 K)} (α : 𝓞 K) (hα : α ≠ 0)
    (h : principalUnit K α hα ∈ coprimeToModulus K 𝔣) :
    raySymbol K (artinFrob K F) (((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) =
      artinSymbol K F 𝔣 ⟨principalUnit K α hα, h⟩ := by
  rw [← principalUnit_val K α hα]
  rfl

theorem raySymbol_eq_one_of_totallyPositive (α : 𝓞 K) (hα : α ≠ 0) (h1 : α - 1 ∈ cmod K F)
    (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) :
    raySymbol K (artinFrob K F) (((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
      = 1 := by
  have hc := principalUnit_mem_coprimeToModulus K hα h1
  rw [raySymbol_principal_eq_artinSymbol K F α hα hc, ← MonoidHom.mem_ker, ker_artinSymbol_cmod]
  refine Subgroup.mem_sup_left ?_
  rw [Subgroup.mem_subgroupOf]
  exact Subgroup.subset_closure ⟨α, hα, h1, hpos, principalUnit_val K α hα⟩

omit [IsGalois K F] [IsMulCommutative (F ≃ₐ[K] F)] in

theorem fracRelNormUnit_principalUnit (β : 𝓞 F) (hβ : β ≠ 0) :
    ((fracRelNormUnit K F (principalUnit F β hβ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) =
      ((Ideal.span {Algebra.intNorm (𝓞 K) (𝓞 F) β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  set I : Ideal (𝓞 F) := Ideal.span {β} with hI
  have hI0 : I ≠ 0 := by
    rw [hI, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hβ
  let e : HeightOneSpectrum (𝓞 F) → ℕ := fun w =>
    (Associates.mk w.asIdeal).count (Associates.mk I).factors
  set T := (Ideal.finite_factors hI0).toFinset with hT
  have hmemT : ∀ w : HeightOneSpectrum (𝓞 F), e w ≠ 0 → w ∈ T := fun w hw => by
    rw [hT, Set.Finite.mem_toFinset]
    exact (Associates.count_ne_zero_iff_dvd hI0 w.irreducible).mp hw

  have hR : ((Ideal.span {Algebra.intNorm (𝓞 K) (𝓞 F) β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      = ∏ w ∈ T, ((placeUnder' K F w).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          ((placeUnder' K F w).asIdeal.inertiaDeg' w.asIdeal * e w) := by
    rw [← Ideal.relNorm_singleton, ← hI]
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI0,
      finprod_eq_prod_of_mulSupport_subset _ (s := T) (fun w hw => hmemT w (fun h => by
        rw [Function.mem_mulSupport, HeightOneSpectrum.maxPowDividing] at hw
        exact hw (by rw [show (Associates.mk w.asIdeal).count (Associates.mk I).factors = e w
          from rfl, h, pow_zero])))]
    rw [map_prod, ← FractionalIdeal.coeIdealHom_apply, map_prod]
    simp only [FractionalIdeal.coeIdealHom_apply]
    refine Finset.prod_congr rfl fun w _ => ?_
    haveI : w.asIdeal.LiesOver (placeUnder' K F w).asIdeal := ⟨rfl⟩
    rw [HeightOneSpectrum.maxPowDividing, map_pow,
      Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (placeUnder' K F w).asIdeal, ← pow_mul,
        FractionalIdeal.coeIdeal_pow]
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
  have hL : ((fracRelNormUnit K F (principalUnit F β hβ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K)
      = ∏ w ∈ T, ((placeUnder' K F w).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          ((placeUnder' K F w).asIdeal.inertiaDeg' w.asIdeal * e w) := by
    rw [fracRelNormUnit, show (raySymbolUnitsHom F _ (principalUnit F β hβ)) =
        raySymbol F _ ((principalUnit F β hβ : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
          FractionalIdeal (𝓞 F)⁰ F) from rfl, principalUnit_val, raySymbol, ← hI,
      finprod_eq_prod_of_mulSupport_subset _ (s := T) (fun w hw => hmemT w (fun h => by
        rw [Function.mem_mulSupport, FractionalIdeal.count_coe F w hI0] at hw
        exact hw (by rw [show (Associates.mk w.asIdeal).count (Associates.mk I).factors = e w
          from rfl, h, Nat.cast_zero, zpow_zero]))),
      Units.coe_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [FractionalIdeal.count_coe F w hI0, zpow_natCast, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, primeUnit_val, ← pow_mul]
  rw [hL, hR]

theorem raySymbol_norm_eq_one (β : 𝓞 F) (hβ : β ≠ 0)
    (h1 : β - 1 ∈ (cmod K F).map (algebraMap (𝓞 K) (𝓞 F))) :
    raySymbol K (artinFrob K F)
      (((Ideal.span {Algebra.intNorm (𝓞 K) (𝓞 F) β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
      = 1 := by
  have hc : principalUnit F β hβ ∈ coprimeToModulus F (modulusExt K F (cmod K F)) :=
    principalUnit_mem_coprimeToModulus F hβ h1
  have hmem : relNormCTM K F (cmod K F) ⟨principalUnit F β hβ, hc⟩ ∈ (artinSymbol K F (cmod K F)).ker := by
    rw [ker_artinSymbol_cmod]
    exact Subgroup.mem_sup_right ⟨_, rfl⟩
  rw [MonoidHom.mem_ker] at hmem
  rw [← fracRelNormUnit_principalUnit K F β hβ]
  exact hmem

end NarrowRay

section Restriction

variable (K F N : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Field N]
  [NumberField N] [Algebra K F] [Algebra K N] [Algebra F N] [IsScalarTower K F N]
  [IsGalois K F] [IsGalois K N] [IsMulCommutative (F ≃ₐ[K] F)] [IsMulCommutative (N ≃ₐ[K] N)]

omit [IsMulCommutative (N ≃ₐ[K] N)] in

theorem restrictNormal_artinFrob (v : HeightOneSpectrum (𝓞 K))
    (hunr : ∀ Q : Ideal (𝓞 F), Q.IsPrime → Q.under (𝓞 K) = v.asIdeal → Q.inertia (F ≃ₐ[K] F) = ⊥) :
    (artinFrob K N v).restrictNormal F = artinFrob K F v := by
  set σ := artinFrob K N v
  set QN := primeAbove K N v
  set QF : Ideal (𝓞 F) := QN.comap (algebraMap (𝓞 F) (𝓞 N)) with hQF
  haveI : QN.IsPrime := (primeAbove_isMaximal K N v).isPrime
  haveI : QF.IsPrime := Ideal.IsPrime.comap _
  have hQF_under : QF.under (𝓞 K) = v.asIdeal := by
    rw [Ideal.under_def, hQF, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      ← Ideal.under_def, under_primeAbove]
  have H := isArithFrobAt_artinFrob K N v
  have hres : IsArithFrobAt (𝓞 K) (σ.restrictNormal F) QF := by
    intro x
    rw [hQF, Ideal.mem_comap, map_sub, map_pow, MulSemiringAction.toAlgHom_apply]
    have hcard : Nat.card (𝓞 K ⧸ QF.under (𝓞 K)) = Nat.card (𝓞 K ⧸ QN.under (𝓞 K)) := by
      rw [hQF_under, under_primeAbove]
    rw [hcard]
    have h1 : algebraMap (𝓞 F) (𝓞 N) (σ.restrictNormal F • x) = σ • algebraMap (𝓞 F) (𝓞 N) x := by
      apply RingOfIntegers.coe_injective
      change algebraMap F N (algebraMap (𝓞 F) F (σ.restrictNormal F • x)) =
        algebraMap (𝓞 N) N (σ • algebraMap (𝓞 F) (𝓞 N) x)
      rw [algebraMap.smul', AlgEquiv.smul_def, AlgEquiv.restrictNormal_commutes,
        algebraMap.smul', AlgEquiv.smul_def]
      rfl
    rw [h1]
    exact H (algebraMap (𝓞 F) (𝓞 N) x)
  exact LT.Artin.eq_artinFrob_of_isArithFrobAt K F v hres hQF_under (hunr QF inferInstance hQF_under)

theorem restrictNormalHom_raySymbol (α : 𝓞 K) (hα : α ≠ 0)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 K), α ∈ v.asIdeal →
      ∀ Q : Ideal (𝓞 F), Q.IsPrime → Q.under (𝓞 K) = v.asIdeal → Q.inertia (F ≃ₐ[K] F) = ⊥) :
    AlgEquiv.restrictNormalHom F
      (raySymbol K (artinFrob K N) (((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)))
      = raySymbol K (artinFrob K F) (((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) := by
  set I : Ideal (𝓞 K) := Ideal.span {α} with hI
  have hI0 : I ≠ 0 := by
    rw [hI, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hα
  unfold raySymbol
  rw [MonoidHom.map_finprod _ (hasFiniteMulSupport_raySymbol_factors K _ _)]
  refine finprod_congr fun v => ?_
  rw [map_zpow]
  by_cases hv : FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0
  · rw [hv, zpow_zero, zpow_zero]
  · congr 1
    change (artinFrob K N v).restrictNormal F = artinFrob K F v
    apply restrictNormal_artinFrob K F N v (hunr v ?_)
    rw [FractionalIdeal.count_coe K v hI0, Nat.cast_eq_zero] at hv
    have hdvd := (Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hv
    exact Ideal.le_of_dvd hdvd (Ideal.subset_span (Set.mem_singleton α))

end Restriction

section NormCong

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

theorem exists_norm_eq_one_add (m : ℕ) (β : 𝓞 F) (hβ : (m : 𝓞 F) ∣ β - 1) :
    ∃ z : 𝓞 K, Algebra.norm K (β : F) = 1 + m * (z : K) := by
  classical
  obtain ⟨y, hy⟩ := hβ
  have hβ' : (β : F) = 1 + m * (y : F) := by
    have : β = 1 + m * y := by rw [← hy]; ring
    rw [this]; push_cast; rfl

  have hne : Nonempty (K →+* ℂ) := by
    rw [← Fintype.card_pos_iff, NumberField.Embeddings.card K ℂ]
    exact Module.finrank_pos
  obtain ⟨κ⟩ := hne
  letI : Algebra K ℂ := κ.toAlgebra
  have hprod := Algebra.norm_eq_prod_embeddings K ℂ (β : F)

  have key : ∀ S : Finset (F →ₐ[K] ℂ), ∃ w : ℂ, IsIntegral ℤ w ∧
      ∏ σ ∈ S, σ (β : F) = 1 + m * w := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨0, isIntegral_zero, by simp⟩
    | insert a S ha ih =>
      obtain ⟨w, hw, hS⟩ := ih
      have hya : IsIntegral ℤ (a (y : F)) := map_isIntegral_int a y.isIntegral_coe
      refine ⟨a (y : F) + w + m * (a (y : F) * w), ?_, ?_⟩
      · exact ((hya.add hw).add ((isIntegral_algebraMap (x := (m : ℤ))).mul (hya.mul hw)) :) |>
          fun h => by simpa using h
      · rw [Finset.prod_insert ha, hS, hβ', map_add, map_one, map_mul, map_natCast]
        ring
  obtain ⟨w, hw, hprod'⟩ := key Finset.univ
  rw [hprod'] at hprod
  by_cases hm : m = 0
  · refine ⟨0, ?_⟩
    subst hm
    simp only [Nat.cast_zero, zero_mul, add_zero] at hprod ⊢
    exact (algebraMap K ℂ).injective (by rw [hprod, map_one])

  set r : K := (Algebra.norm K (β : F) - 1) / m with hr
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm
  have hr' : algebraMap K ℂ r = w := by
    rw [hr, map_div₀, map_sub, map_one, hprod, map_natCast]
    field_simp
    ring
  have hrint : IsIntegral ℤ r := by
    rw [← isIntegral_algebraMap_iff (algebraMap K ℂ).injective, hr']
    exact hw
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 K, (z : K) = r := ⟨⟨r, hrint⟩, rfl⟩
  refine ⟨z, ?_⟩
  rw [hz, hr]
  field_simp
  ring

end NormCong

section Compositum

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Ω : Type _ := AlgebraicClosure L

scoped instance isAlgebraic_Ω : Algebra.IsAlgebraic K (Ω L) := Algebra.IsAlgebraic.trans K L (Ω L)

scoped instance isIntegral_Ω : Algebra.IsIntegral K (Ω L) := inferInstance

def ιL : L →ₐ[K] Ω L := IsScalarTower.toAlgHom K L (Ω L)

def Lι : IntermediateField K (Ω L) := IntermediateField.map (ιL K L) ⊤

def eL : L ≃ₐ[K] Lι K L :=
  IntermediateField.topEquiv.symm.trans (IntermediateField.equivMap ⊤ (ιL K L))

theorem coe_eL (x : L) : ((eL K L x : Lι K L) : Ω L) = algebraMap L (Ω L) x := rfl

scoped instance isGalois_Lι [IsGalois K L] : IsGalois K (Lι K L) := IsGalois.of_algEquiv (eL K L)

scoped instance finiteDimensional_Lι : FiniteDimensional K (Lι K L) :=
  (eL K L).toLinearEquiv.finiteDimensional

def iΩ : Ω L := Classical.choose (IsAlgClosed.exists_pow_nat_eq (-1 : Ω L) two_pos)

theorem iΩ_sq : iΩ L ^ 2 = -1 := Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (-1 : Ω L) two_pos)

theorem iΩ_pow_four : iΩ L ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, iΩ_sq]; norm_num

theorem isPrimitiveRoot_iΩ : IsPrimitiveRoot (iΩ L) 4 := by
  rw [IsPrimitiveRoot.iff (by norm_num : 0 < 4)]
  refine ⟨iΩ_pow_four L, fun l hl hl4 h => ?_⟩
  have hsq := iΩ_sq L
  have h11 : (-1 : Ω L) ≠ 1 := by
    intro h
    have : (2 : Ω L) = 0 := by linear_combination -h
    exact two_ne_zero this
  interval_cases l
  · rw [pow_one] at h
    rw [h, one_pow] at hsq
    exact h11 hsq.symm
  · rw [hsq] at h
    exact h11 h
  · have : iΩ L ^ 4 = iΩ L := by rw [pow_succ, h, one_mul]
    rw [iΩ_pow_four] at this
    rw [← this, one_pow] at hsq
    exact h11 hsq.symm

open scoped IntermediateField in

abbrev Ei : IntermediateField K (Ω L) := K⟮iΩ L⟯

scoped instance isGalois_Ei : IsGalois K (Ei K L) := by
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  haveI := (isPrimitiveRoot_iΩ L).intermediateField_adjoin_isCyclotomicExtension (K := K)
  exact IsCyclotomicExtension.isGalois {4} K _

scoped instance finiteDimensional_Ei : FiniteDimensional K (Ei K L) :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (iΩ L))

def NN : IntermediateField K (Ω L) := Lι K L ⊔ Ei K L

scoped instance isGalois_NN [IsGalois K L] : IsGalois K (NN K L) := by unfold NN; infer_instance

scoped instance finiteDimensional_NN : FiniteDimensional K (NN K L) := by unfold NN; infer_instance

scoped instance numberField_NN : NumberField (NN K L) := NumberField.of_module_finite K _

theorem Lι_le_NN : Lι K L ≤ NN K L := le_sup_left

theorem iΩ_mem_NN : iΩ L ∈ NN K L :=
  (le_sup_right : Ei K L ≤ NN K L) (IntermediateField.mem_adjoin_simple_self K (iΩ L))

def iN : NN K L := ⟨iΩ L, iΩ_mem_NN K L⟩

theorem iN_sq : iN K L ^ 2 = -1 := by
  apply Subtype.ext
  change iΩ L ^ 2 = -1
  exact iΩ_sq L

theorem iN_pow_four : iN K L ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, iN_sq]; norm_num

theorem iN_ne_zero : iN K L ≠ 0 := by
  intro h
  have := iN_sq K L
  rw [h] at this
  norm_num at this

theorem neg_iN_ne_iN : -iN K L ≠ iN K L := by
  intro h
  have : (2 : NN K L) * iN K L = 0 := by linear_combination -h
  exact iN_ne_zero K L ((mul_eq_zero.mp this).resolve_left two_ne_zero)

theorem apply_iN (g : NN K L ≃ₐ[K] NN K L) : g (iN K L) = iN K L ∨ g (iN K L) = -iN K L := by
  rw [← sq_eq_sq_iff_eq_or_eq_neg, ← map_pow, iN_sq, map_neg, map_one]

scoped instance algebra_Lι_NN : Algebra (Lι K L) (NN K L) :=
  (IntermediateField.inclusion (Lι_le_NN K L)).toRingHom.toAlgebra

scoped instance isScalarTower_Lι_NN : IsScalarTower K (Lι K L) (NN K L) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem algebraMap_Lι_NN (y : Lι K L) :
    algebraMap (Lι K L) (NN K L) y = ⟨(y : Ω L), Lι_le_NN K L y.2⟩ := rfl

theorem isMulCommutative_Lι [IsMulCommutative (L ≃ₐ[K] L)] :
    IsMulCommutative ((Lι K L) ≃ₐ[K] (Lι K L)) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨a', rfl⟩ := (eL K L).autCongr.surjective a
  obtain ⟨b', rfl⟩ := (eL K L).autCongr.surjective b
  rw [← map_mul, ← map_mul, mul_comm]

scoped instance isMulCommutative_NN [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] :
    IsMulCommutative ((NN K L) ≃ₐ[K] (NN K L)) := by
  haveI := isMulCommutative_Lι K L
  refine ⟨⟨fun g h => ?_⟩⟩
  have hS : NN K L = IntermediateField.adjoin K ((Lι K L : Set (Ω L)) ∪ {iΩ L}) := by
    rw [IntermediateField.adjoin_union, IntermediateField.adjoin_self]; rfl
  have key : ((g * h : (NN K L) ≃ₐ[K] (NN K L)) : (NN K L) →ₐ[K] (NN K L)) =
      ((h * g : (NN K L) ≃ₐ[K] (NN K L)) : (NN K L) →ₐ[K] (NN K L)) := by
    refine IntermediateField.algHom_ext_of_eq_adjoin K hS ?_
    rintro x (hx | hx)
    ·
      set y : Lι K L := ⟨x, hx⟩
      have hy : (⟨x, hS.ge (IntermediateField.subset_adjoin _ _ (Or.inl hx))⟩ : NN K L) =
          algebraMap (Lι K L) (NN K L) y := rfl
      rw [hy, AlgEquiv.coe_algHom, AlgEquiv.coe_algHom, AlgEquiv.mul_apply, AlgEquiv.mul_apply,
        ← AlgEquiv.restrictNormal_commutes, ← AlgEquiv.restrictNormal_commutes,
        ← AlgEquiv.restrictNormal_commutes, ← AlgEquiv.restrictNormal_commutes,
        ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, mul_comm]
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      have hi : (⟨iΩ L, hS.ge (IntermediateField.subset_adjoin _ _ (Or.inr rfl))⟩ : NN K L) =
          iN K L := rfl
      rw [hi, AlgEquiv.coe_algHom, AlgEquiv.coe_algHom, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
      rcases apply_iN K L g with hg | hg <;> rcases apply_iN K L h with hh | hh <;>
        simp only [hg, hh, map_neg, neg_neg]
  exact AlgEquiv.ext fun x => congr($key x)

scoped instance algebra_L_NN : Algebra L (NN K L) :=
  ((algebraMap (Lι K L) (NN K L)).comp (eL K L : L →+* Lι K L)).toAlgebra

theorem algebraMap_L_NN (x : L) :
    (algebraMap L (NN K L) x : Ω L) = algebraMap L (Ω L) x := rfl

scoped instance isScalarTower_L_NN : IsScalarTower K L (NN K L) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    apply Subtype.ext
    rw [algebraMap_L_NN, ← IsScalarTower.algebraMap_apply]
    rfl

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

def PhiΩ (τ : K →+* ℝ) : Ω L →+* ℂ := by
  letI : Algebra K ℂ := (Complex.ofRealHom.comp τ).toAlgebra
  exact (IsAlgClosed.lift (R := K) (M := ℂ) (S := Ω L)).toRingHom

theorem PhiΩ_algebraMap (τ : K →+* ℝ) (x : K) : PhiΩ K L τ (algebraMap K (Ω L) x) = τ x := by
  letI : Algebra K ℂ := (Complex.ofRealHom.comp τ).toAlgebra
  exact (IsAlgClosed.lift (R := K) (M := ℂ) (S := Ω L)).commutes x

def Phi (τ : K →+* ℝ) : NN K L →+* ℂ := (PhiΩ K L τ).comp (algebraMap (NN K L) (Ω L))

theorem Phi_apply (τ : K →+* ℝ) (x : NN K L) : Phi K L τ x = PhiΩ K L τ (x : Ω L) := rfl

theorem Phi_algebraMap (τ : K →+* ℝ) (x : K) : Phi K L τ (algebraMap K (NN K L) x) = τ x :=
  PhiΩ_algebraMap K L τ x

theorem exists_isConj (τ : K →+* ℝ) :
    ∃ σ : NN K L ≃ₐ[K] NN K L, ComplexEmbedding.IsConj (Phi K L τ) σ := by
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := K) (Phi K L τ)
    (ComplexEmbedding.conjugate (Phi K L τ)) (by
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply, ComplexEmbedding.conjugate_coe_eq,
        Phi_algebraMap, Complex.conj_ofReal])
  exact ⟨σ.symm, hσ.symm⟩

def cN (τ : K →+* ℝ) : NN K L ≃ₐ[K] NN K L := Classical.choose (exists_isConj K L τ)

theorem isConj_cN (τ : K →+* ℝ) : ComplexEmbedding.IsConj (Phi K L τ) (cN K L τ) :=
  Classical.choose_spec (exists_isConj K L τ)

theorem cN_mul_cN (τ : K →+* ℝ) : cN K L τ * cN K L τ = 1 :=
  AlgEquiv.ext fun x => ComplexEmbedding.isConj_apply_apply (isConj_cN K L τ) x

theorem cN_iN (τ : K →+* ℝ) : cN K L τ (iN K L) = -iN K L := by
  have hI : (Phi K L τ (iN K L)) ^ 2 = -1 := by
    rw [← map_pow, iN_sq, map_neg, map_one]
  have hz : Phi K L τ (iN K L) = Complex.I ∨ Phi K L τ (iN K L) = -Complex.I := by
    rw [← sq_eq_sq_iff_eq_or_eq_neg, Complex.I_sq]; exact hI
  apply (Phi K L τ).injective
  rw [(isConj_cN K L τ).eq, map_neg]
  rcases hz with h | h <;> rw [h] <;> simp

def Lp (τ : K →+* ℝ) : IntermediateField K (NN K L) :=
  IntermediateField.fixedField (Subgroup.zpowers (cN K L τ))

theorem cN_apply_Lp (τ : K →+* ℝ) (y : Lp K L τ) :
    cN K L τ (algebraMap (Lp K L τ) (NN K L) y) = algebraMap (Lp K L τ) (NN K L) y := by
  have := (IntermediateField.mem_fixedField_iff (Subgroup.zpowers (cN K L τ)) (y : NN K L)).mp y.2
  exact this _ (Subgroup.mem_zpowers _)

scoped instance isGalois_Lp (τ : K →+* ℝ) :
    IsGalois K (Lp K L τ) := by
  unfold Lp; infer_instance

scoped instance isMulCommutative_Lp (τ : K →+* ℝ) :
    IsMulCommutative ((Lp K L τ) ≃ₐ[K] (Lp K L τ)) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨a', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (NN K L) a
  obtain ⟨b', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (NN K L) b
  rw [← map_mul, ← map_mul, mul_comm]

theorem isReal_Phi_comp (τ : K →+* ℝ) :
    ComplexEmbedding.IsReal ((Phi K L τ).comp (algebraMap (Lp K L τ) (NN K L))) := by
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have h := RingHom.congr_fun (isConj_cN K L τ) (algebraMap (Lp K L τ) (NN K L) y)
  rw [RingHom.comp_apply] at h
  change _ = Phi K L τ (cN K L τ (algebraMap _ _ y)) at h
  rw [cN_apply_Lp, ComplexEmbedding.conjugate_coe_eq] at h
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply]
  exact h

def psi0 (τ : K →+* ℝ) : Lp K L τ →+* ℝ := (isReal_Phi_comp K L τ).embedding

theorem psi0_apply (τ : K →+* ℝ) (y : Lp K L τ) : (psi0 K L τ y : ℂ) = Phi K L τ (y : NN K L) :=
  ComplexEmbedding.IsReal.coe_embedding_apply (isReal_Phi_comp K L τ) y

theorem psi0_comp (τ : K →+* ℝ) : (psi0 K L τ).comp (algebraMap K (Lp K L τ)) = τ := by
  ext x
  apply Complex.ofReal_injective
  rw [RingHom.comp_apply, psi0_apply]
  exact Phi_algebraMap K L τ x

theorem realEmb_eq_psi0_comp (τ : K →+* ℝ) (ψ : Lp K L τ →+* ℝ)
    (hψ : ψ.comp (algebraMap K (Lp K L τ)) = τ) :
    ∃ σ : (Lp K L τ) ≃ₐ[K] (Lp K L τ), ψ = (psi0 K L τ).comp (σ : Lp K L τ →+* Lp K L τ) := by
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := K)
    (Complex.ofRealHom.comp (psi0 K L τ)) (Complex.ofRealHom.comp ψ) (by
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← RingHom.comp_apply (psi0 K L τ), psi0_comp, ← RingHom.comp_apply ψ, hψ])
  refine ⟨σ.symm, ?_⟩
  ext y
  have := congr($hσ y)
  simp only [RingHom.coe_comp, Function.comp_apply] at this
  rw [RingHom.comp_apply]
  exact (Complex.ofReal_injective this).symm

end Compositum

section Crossing

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

theorem raySymbol_span_mul {M : Type*} [CommGroup M] (f : HeightOneSpectrum (𝓞 K) → M)
    (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0) :
    raySymbol K f (((Ideal.span {a * b} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) =
      raySymbol K f (((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
        raySymbol K f (((Ideal.span {b} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) := by
  rw [← Ideal.span_singleton_mul_span_singleton, FractionalIdeal.coeIdeal_mul,
    raySymbol_mul]
  · rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]; exact ha
  · rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]; exact hb

omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in
theorem sub_one_mem_of_mul {I : Ideal (𝓞 K)} {a b : 𝓞 K} (ha : a - 1 ∈ I) (hb : b - 1 ∈ I) :
    a * b - 1 ∈ I := by
  have : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  rw [this]
  exact I.add_mem (I.mul_mem_left _ hb) ha

theorem raySymbol_Lp_eq_one (τ : K →+* ℝ) (α : 𝓞 K) (hα : α ≠ 0)
    (h1 : α - 1 ∈ cmod K (Lp K L τ)) (hneg : τ (α : K) < 0)
    (hpos : ∀ τ' : K →+* ℝ, τ' ≠ τ → 0 < τ' (α : K)) :
    raySymbol K (artinFrob K (Lp K L τ))
      (((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) = 1 := by
  classical
  set F := Lp K L τ
  set m := Ideal.absNorm (cmod K F) with hm_def
  have hm : m ≠ 0 := absNorm_cmod_ne_zero K F
  have hmmem : (m : 𝓞 K) ∈ cmod K F := Ideal.absNorm_mem _

  obtain ⟨β, hβ0, hβ1, hβsign⟩ :=
    NumberField.exists_ne_zero_dvd_sub_one_forall_lt_zero_iff F m hm {ψ | ψ = psi0 K L τ}
  set γ : 𝓞 K := Algebra.intNorm (𝓞 K) (𝓞 F) β with hγ_def
  have hγK : (γ : K) = Algebra.norm K (β : F) := Algebra.algebraMap_intNorm (A := 𝓞 K) (K := K)
    (L := F) (B := 𝓞 F) β
  have hβ0' : (β : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hβ0
  have hnorm0 : Algebra.norm K (β : F) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ0'
  have hγ0 : γ ≠ 0 := by
    intro h; apply hnorm0; rw [← hγK, h]; rfl
  have hγ0' : (γ : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hγ0

  obtain ⟨z, hz⟩ := exists_norm_eq_one_add K F m β hβ1
  have hγ1 : γ - 1 ∈ cmod K F := by
    have : γ - 1 = m * z := by
      apply RingOfIntegers.coe_injective
      simp only [map_sub, map_one, map_mul, map_natCast]
      rw [← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, hγK, hz]
      ring
    rw [this]
    exact Ideal.mul_mem_right _ _ hmmem

  have hsign : ∀ τ' : K →+* ℝ, τ' (γ : K) < 0 ↔ τ' = τ := by
    intro τ'
    rw [hγK, NumberField.apply_norm_lt_zero_iff_odd_card_filter K F τ' (β : F) hβ0']
    have hset : (Finset.univ.filter fun ψ : F →+* ℝ =>
        ψ.comp (algebraMap K F) = τ' ∧ ψ (β : F) < 0) =
        if τ' = τ then {psi0 K L τ} else ∅ := by
      ext ψ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show ψ (β : F) < 0 ↔ ψ = psi0 K L τ from hβsign ψ]
      split_ifs with h
      · simp only [Finset.mem_singleton]
        constructor
        · exact fun hh => hh.2
        · rintro rfl; exact ⟨h ▸ psi0_comp K L τ, rfl⟩
      · simp only [Finset.notMem_empty, iff_false, not_and]
        rintro hh rfl
        exact h ((psi0_comp K L τ).symm.trans hh).symm
    rw [hset]
    split_ifs with h <;> simp [h]

  have hP0 : α * γ ≠ 0 := mul_ne_zero hα hγ0
  have hP1 : α * γ - 1 ∈ cmod K F := sub_one_mem_of_mul K h1 hγ1
  have hPpos : ∀ τ' : K →+* ℝ, 0 < τ' (algebraMap (𝓞 K) K (α * γ)) := by
    intro τ'
    rw [map_mul, map_mul]
    by_cases h : τ' = τ
    · subst h
      exact mul_pos_of_neg_of_neg hneg ((hsign τ').mpr rfl)
    · have hγ' : 0 < τ' (γ : K) := by
        rcases lt_trichotomy (τ' (γ : K)) 0 with h' | h' | h'
        · exact absurd ((hsign τ').mp h') h
        · exact absurd h' ((map_ne_zero τ').mpr hγ0')
        · exact h'
      exact mul_pos (hpos τ' h) hγ'
  have hray := raySymbol_eq_one_of_totallyPositive K F (α * γ) hP0 hP1 hPpos
  have hβ1' : β - 1 ∈ (cmod K F).map (algebraMap (𝓞 K) (𝓞 F)) := by
    obtain ⟨y, hy⟩ := hβ1
    rw [hy]
    exact Ideal.mul_mem_right _ _ (by
      have := Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 F)) hmmem
      simpa using this)
  have hγray := raySymbol_norm_eq_one K F β hβ0 hβ1'
  rw [← hγ_def] at hγray
  rw [raySymbol_span_mul K _ α γ hα hγ0, hγray, mul_one] at hray
  exact hray

theorem four_notMem {α : 𝓞 K} (h4 : α - 1 ∈ Ideal.span {(4 : 𝓞 K)}) (v : HeightOneSpectrum (𝓞 K))
    (hv : α ∈ v.asIdeal) : ((4 : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  intro h
  have h1 : α - 1 ∈ v.asIdeal := by
    refine (Ideal.span_le.mpr ?_) h4
    simpa using h
  have : (1 : 𝓞 K) ∈ v.asIdeal := by simpa using v.asIdeal.sub_mem hv h1
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)

theorem absNorm_mod_four (τ : K →+* ℝ) (α : 𝓞 K) (hα : α ≠ 0)
    (h4 : α - 1 ∈ Ideal.span {(4 : 𝓞 K)}) (hneg : τ (α : K) < 0)
    (hpos : ∀ τ' : K →+* ℝ, τ' ≠ τ → 0 < τ' (α : K)) :
    Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K))) % 4 = 3 := by
  classical
  rw [Ideal.absNorm_span_singleton]

  obtain ⟨z, hz⟩ := exists_norm_eq_one_add ℚ K 4 α (by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h4
    exact ⟨c, by rw [← hc, mul_comm, Nat.cast_ofNat]⟩)
  set t : ℤ := Rat.ringOfIntegersEquiv z with ht
  have hzt : (z : ℚ) = t := by rw [ht, Rat.ringOfIntegersEquiv_apply_coe]
  have hN : Algebra.norm ℤ α = 1 + 4 * t := by
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_norm_int, hz, hzt]; push_cast; ring

  have hNneg : Algebra.norm ℤ α < 0 := by
    have h := NumberField.apply_norm_lt_zero_iff_odd_card_filter ℚ K (Rat.castHom ℝ) (α : K)
      (by exact_mod_cast hα)
    have hset : (Finset.univ.filter fun ψ : K →+* ℝ =>
        ψ.comp (algebraMap ℚ K) = Rat.castHom ℝ ∧ ψ (α : K) < 0) = {τ} := by
      ext ψ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hψ⟩
        by_contra hne
        exact absurd hψ (hpos ψ hne).not_gt
      · rintro rfl
        exact ⟨Subsingleton.elim _ _, hneg⟩
    have hodd : Odd (Finset.univ.filter fun ψ : K →+* ℝ =>
        ψ.comp (algebraMap ℚ K) = Rat.castHom ℝ ∧ ψ (α : K) < 0).card := by
      rw [hset, Finset.card_singleton]; exact odd_one
    have h' : (Rat.castHom ℝ) (Algebra.norm ℚ (α : K)) < 0 := by
      refine h.mpr ?_
      convert hodd using 4
    rw [← Algebra.coe_norm_int] at h'
    simp only [eq_ratCast, Rat.cast_intCast, Int.cast_lt_zero] at h'
    exact h'
  rw [hN] at hNneg ⊢
  omega

theorem restrictNormal_cN_eq (τ : K →+* ℝ) (c : L ≃ₐ[K] L) (φ : L →+* ℂ)
    (hφ : ∀ x : K, φ (algebraMap K L x) = τ x) (hc : ComplexEmbedding.IsConj φ c) :
    (cN K L τ).restrictNormal L = c := by
  set φ₁ : L →+* ℂ := (Phi K L τ).comp (algebraMap L (NN K L)) with hφ₁
  have hconj₁ : ComplexEmbedding.IsConj φ₁ ((cN K L τ).restrictNormal L) := by
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, RingHom.comp_apply,
      RingHom.comp_apply]
    change _ = Phi K L τ (algebraMap L (NN K L) ((cN K L τ).restrictNormal L x))
    rw [AlgEquiv.restrictNormal_commutes, (isConj_cN K L τ).eq]
    rfl
  have hover : φ₁.comp (algebraMap K L) = φ.comp (algebraMap K L) := by
    ext x
    change Phi K L τ (algebraMap L (NN K L) (algebraMap K L x)) = φ (algebraMap K L x)
    rw [hφ, ← IsScalarTower.algebraMap_apply]
    exact Phi_algebraMap K L τ x
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := K) φ₁ φ hover
  have h2 := hconj₁.comp σ.symm
  rw [hσ, IsMulCommutative.is_comm.comm (σ.symm⁻¹), mul_assoc, inv_mul_cancel, mul_one] at h2
  exact (h2.ext hc)

theorem raySymbol_eq_of_neg (τ : K →+* ℝ) (α : 𝓞 K) (hα : α ≠ 0)
    (h4 : α - 1 ∈ Ideal.span {(4 : 𝓞 K)}) (hL : α - 1 ∈ cmod K L)
    (hLp : α - 1 ∈ cmod K (Lp K L τ)) (hneg : τ (α : K) < 0)
    (hpos : ∀ τ' : K →+* ℝ, τ' ≠ τ → 0 < τ' (α : K))
    (c : L ≃ₐ[K] L) (φ : L →+* ℂ) (hφ : ∀ x : K, φ (algebraMap K L x) = τ x)
    (hc : ComplexEmbedding.IsConj φ c) :
    raySymbol K (artinFrob K L) (((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
      = c := by
  set I : FractionalIdeal (𝓞 K)⁰ K := ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
  set A := raySymbol K (artinFrob K (NN K L)) I with hA

  have hresLp : AlgEquiv.restrictNormalHom (Lp K L τ) A = 1 := by
    rw [hA, restrictNormalHom_raySymbol K (Lp K L τ) (NN K L) α hα
      (fun v hv Q hQp hQ => inertia_eq_bot_of_mem K (Lp K L τ) hLp v hv Q hQp hQ)]
    exact raySymbol_Lp_eq_one K L τ α hα hLp hneg hpos
  have hAmem : A ∈ Subgroup.zpowers (cN K L τ) := by
    have : A ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := NN K L) (Lp K L τ)).ker := by
      rw [MonoidHom.mem_ker]; exact hresLp
    rwa [IntermediateField.restrictNormalHom_ker, Lp, IntermediateField.fixingSubgroup_fixedField] at this
  have hA01 : A = 1 ∨ A = cN K L τ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hAmem
    rw [← hk, ← Int.mul_ediv_add_emod k 2, zpow_add, zpow_mul]
    have h2 : cN K L τ ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, cN_mul_cN]
    rw [h2, one_zpow, one_mul]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h]
    · left; rw [zpow_zero]
    · right; rw [zpow_one]

  have hAi : A (iN K L) = -iN K L := by
    rw [hA, NumberField.raySymbol_artinFrob_apply_eq_pow_absNorm_of_pow_eq_one K (NN K L) 4
      (iN K L) (iN_pow_four K L) α hα (four_notMem K h4),
      ← Nat.div_add_mod (Ideal.absNorm (Ideal.span {α})) 4, absNorm_mod_four K τ α hα h4 hneg hpos,
      pow_add, pow_mul, iN_pow_four, one_pow, one_mul, pow_succ, iN_sq]
    ring
  have hAc : A = cN K L τ := by
    rcases hA01 with h | h
    · exfalso
      rw [h, AlgEquiv.one_apply] at hAi
      exact neg_iN_ne_iN K L hAi.symm
    · exact h

  have hresL : AlgEquiv.restrictNormalHom L A = raySymbol K (artinFrob K L) I :=
    restrictNormalHom_raySymbol K L (NN K L) α hα
      (fun v hv Q hQp hQ => inertia_eq_bot_of_mem K L hL v hv Q hQp hQ)
  rw [← hresL, hAc]
  exact restrictNormal_cN_eq K L τ c φ hφ hc

end Crossing

section Main

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

def fmod : Ideal (𝓞 K) :=
  Ideal.span {(4 : 𝓞 K)} * cmod K L * ∏ τ : K →+* ℝ, cmod K (Lp K L τ)

theorem fmod_ne_bot : fmod K L ≠ ⊥ := by
  rw [fmod, ← Ideal.zero_eq_bot]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; norm_num
  · rw [Ideal.zero_eq_bot]; exact cmod_ne_bot K L
  · rw [Finset.prod_ne_zero_iff]
    intro τ _
    rw [Ideal.zero_eq_bot]; exact cmod_ne_bot K (Lp K L τ)

theorem fmod_le_four : fmod K L ≤ Ideal.span {(4 : 𝓞 K)} := by
  rw [fmod, mul_assoc]; exact Ideal.mul_le_left

theorem fmod_le_cmod : fmod K L ≤ cmod K L := by
  rw [fmod, mul_comm (Ideal.span _), mul_assoc]; exact Ideal.mul_le_left

theorem fmod_le_cmod_Lp (τ : K →+* ℝ) : fmod K L ≤ cmod K (Lp K L τ) := by
  rw [fmod]
  refine Ideal.mul_le_right.trans ?_
  exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ τ))

theorem main :
    ∃ 𝔣 : Ideal (𝓞 K), 𝔣 ≠ ⊥ ∧
      (∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 →
        ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.under (𝓞 K) = v.asIdeal →
          Q.inertia (L ≃ₐ[K] L) = ⊥) ∧
      (∀ (α : 𝓞 K) (hα : α ≠ 0) (𝔪 : Ideal (𝓞 K))
        (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔪) (c : (K →+* ℝ) → (L ≃ₐ[K] L)),
        α - 1 ∈ 𝔣 →
        (∀ τ : K →+* ℝ, ∃ φ : L →+* ℂ,
          (∀ x : K, φ (algebraMap K L x) = τ x) ∧ ComplexEmbedding.IsConj φ (c τ)) →
        artinSymbol K L 𝔪 ⟨principalUnit K α hα, hc⟩ =
          ∏ τ ∈ Finset.univ.filter (fun τ : K →+* ℝ => τ (algebraMap (𝓞 K) K α) < 0), c τ) := by
  classical
  refine ⟨fmod K L, fmod_ne_bot K L, ?_, ?_⟩
  ·
    intro v hv Q hQp hQ
    refine inertia_eq_bot_of_not_dvd K L (n := Nat.card (L ≃ₐ[K] L)) ?_ v hv Q hQ
    rw [fmod, mul_comm (Ideal.span _), mul_assoc]
    exact Dvd.intro _ rfl
  · intro α hα 𝔪 hc c h1 hconj
    rw [← raySymbol_principal_eq_artinSymbol K L α hα hc]
    set S := Finset.univ.filter (fun τ : K →+* ℝ => τ (algebraMap (𝓞 K) K α) < 0) with hS

    have hm : Ideal.absNorm (fmod K L) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact fmod_ne_bot K L
    choose a ha0 ha1 hasign using fun τ : K →+* ℝ =>
      NumberField.exists_ne_zero_dvd_sub_one_forall_lt_zero_iff K _ hm {τ' | τ' = τ}
    have ha1' : ∀ τ : K →+* ℝ, a τ - 1 ∈ fmod K L := fun τ => by
      obtain ⟨y, hy⟩ := ha1 τ
      rw [hy]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    have haneg : ∀ τ : K →+* ℝ, τ (a τ : K) < 0 := fun τ => (hasign τ τ).mpr rfl
    have hapos : ∀ τ τ' : K →+* ℝ, τ' ≠ τ → 0 < τ' (a τ : K) := by
      intro τ τ' h
      rcases lt_trichotomy (τ' (a τ : K)) 0 with h' | h' | h'
      · exact absurd ((hasign τ τ').mp h') h
      · exact absurd h' ((map_ne_zero τ').mpr (RingOfIntegers.coe_ne_zero_iff.mpr (ha0 τ)))
      · exact h'

    have hlaw : ∀ τ : K →+* ℝ, raySymbol K (artinFrob K L)
        (((Ideal.span {a τ} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) = c τ := by
      intro τ
      obtain ⟨φ, hφ, hφc⟩ := hconj τ
      exact raySymbol_eq_of_neg K L τ (a τ) (ha0 τ) (fmod_le_four K L (ha1' τ))
        (fmod_le_cmod K L (ha1' τ)) (fmod_le_cmod_Lp K L τ (ha1' τ)) (haneg τ) (hapos τ)
        (c τ) φ hφ hφc

    have key : ∀ T : Finset (K →+* ℝ), T ⊆ S →
        (α * ∏ τ ∈ T, a τ) ≠ 0 ∧ (α * ∏ τ ∈ T, a τ) - 1 ∈ fmod K L ∧
        (∀ τ' : K →+* ℝ, τ' (algebraMap (𝓞 K) K (α * ∏ τ ∈ T, a τ)) < 0 ↔ τ' ∈ S \ T) ∧
        raySymbol K (artinFrob K L)
          (((Ideal.span {α * ∏ τ ∈ T, a τ} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) =
          raySymbol K (artinFrob K L)
            (((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) * ∏ τ ∈ T, c τ := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        intro _
        simp only [Finset.prod_empty, mul_one, Finset.sdiff_empty]
        exact ⟨hα, h1, fun τ' => by rw [hS, Finset.mem_filter]; simp, trivial⟩
      | insert σ T hσT ih =>
        intro hsub
        obtain ⟨h0, h1', hsgn, hray⟩ := ih ((Finset.subset_insert σ T).trans hsub)
        have hσS : σ ∈ S := hsub (Finset.mem_insert_self σ T)
        rw [Finset.prod_insert hσT, mul_left_comm]
        refine ⟨mul_ne_zero (ha0 σ) h0, sub_one_mem_of_mul K (ha1' σ) h1', fun τ' => ?_, ?_⟩
        · rw [map_mul, map_mul]
          change τ' (a σ : K) * _ < 0 ↔ _
          by_cases hτ' : τ' = σ
          · subst hτ'
            have hneg1 := haneg τ'
            have hin : τ' ∈ S \ T := Finset.mem_sdiff.mpr ⟨hσS, hσT⟩
            have hneg2 := (hsgn τ').mpr hin
            constructor
            · intro h
              exact absurd h (mul_pos_of_neg_of_neg hneg1 hneg2).not_gt
            · intro h
              exact absurd h (by simp [Finset.mem_sdiff])
          · have hpos1 := hapos σ τ' hτ'
            rw [show τ' ∈ S \ insert σ T ↔ τ' ∈ S \ T by simp [Finset.mem_sdiff, hτ']]
            rw [← hsgn τ']
            constructor
            · intro h
              by_contra h'
              push Not at h'
              exact absurd h (not_lt.mpr (mul_nonneg hpos1.le h'))
            · intro h
              exact mul_neg_of_pos_of_neg hpos1 h
        · rw [raySymbol_span_mul K _ (a σ) _ (ha0 σ) h0, hray, hlaw σ, Finset.prod_insert hσT]
          simp only [mul_comm, mul_assoc]
    obtain ⟨hP0, hP1, hPsgn, hPray⟩ := key S subset_rfl
    have hPpos : ∀ τ' : K →+* ℝ, 0 < τ' (algebraMap (𝓞 K) K (α * ∏ τ ∈ S, a τ)) := by
      intro τ'
      have h := hPsgn τ'
      simp only [Finset.sdiff_self, Finset.notMem_empty, iff_false, not_lt] at h
      rcases h.lt_or_eq with h' | h'
      · exact h'
      · exfalso
        rw [eq_comm, map_eq_zero_iff _ τ'.injective] at h'
        exact hP0 (RingOfIntegers.coe_eq_zero_iff.mp h')
    have hone := raySymbol_eq_one_of_totallyPositive K L _ hP0 (fmod_le_cmod K L hP1) hPpos
    rw [hPray] at hone

    have hcc : ∀ τ : K →+* ℝ, c τ * c τ = 1 := by
      intro τ
      obtain ⟨φ, -, hφc⟩ := hconj τ
      exact AlgEquiv.ext fun x => ComplexEmbedding.isConj_apply_apply hφc x
    have hprod : (∏ τ ∈ S, c τ) * (∏ τ ∈ S, c τ) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun τ _ => hcc τ
    calc raySymbol K (artinFrob K L) (((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
        = raySymbol K (artinFrob K L) (((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
            * ((∏ τ ∈ S, c τ) * (∏ τ ∈ S, c τ)) := by rw [hprod, mul_one]
      _ = ∏ τ ∈ S, c τ := by rw [← mul_assoc, hone, one_mul]

end Main

end RecipSign
p2m_reactivate "P2MW.S_NumberField_exists_artinSymbol_principalUnit_eq_prod_of_isConj.RecipSign"

end
p2m_reactivate "P2MW.S_NumberField_exists_artinSymbol_principalUnit_eq_prod_of_isConj.RecipSign"

p2m_open "NumberField P2MW.S_NumberField_exists_artinSymbol_principalUnit_eq_prod_of_isConj.NumberField IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin"
open scoped IsMulCommutative

universe u v

theorem solution
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] :
    ∃ 𝔣 : Ideal (𝓞 K), 𝔣 ≠ ⊥ ∧
      (∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 →
        ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.under (𝓞 K) = v.asIdeal →
          Q.inertia (L ≃ₐ[K] L) = ⊥) ∧
      (∀ (α : 𝓞 K) (hα : α ≠ 0) (𝔪 : Ideal (𝓞 K))
        (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔪) (c : (K →+* ℝ) → (L ≃ₐ[K] L)),
        α - 1 ∈ 𝔣 →
        (∀ τ : K →+* ℝ, ∃ φ : L →+* ℂ,
          (∀ x : K, φ (algebraMap K L x) = τ x) ∧ ComplexEmbedding.IsConj φ (c τ)) →
        artinSymbol K L 𝔪 ⟨principalUnit K α hα, hc⟩ =
          ∏ τ ∈ Finset.univ.filter (fun τ : K →+* ℝ => τ (algebraMap (𝓞 K) K α) < 0), c τ) :=
  RecipSign.main K L

end S_NumberField_exists_artinSymbol_principalUnit_eq_prod_of_isConj
end P2MW
export P2MW.S_NumberField_exists_artinSymbol_principalUnit_eq_prod_of_isConj (solution)
