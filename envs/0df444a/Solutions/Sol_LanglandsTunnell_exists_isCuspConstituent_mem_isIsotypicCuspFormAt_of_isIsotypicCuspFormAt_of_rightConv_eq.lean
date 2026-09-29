-- Prove2me | solution 1 for LanglandsTunnell.exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/48f0f844-8eae-5f9b-81eb-4609e7f3cfc0

import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_subset_iSupIndep_iSup_eq_of_finset_isCuspConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_comp_mul_archRealGLAt_J_mem_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar
import Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe"
p2m_attr_erase "simp" "coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

noncomputable section

namespace P2M
namespace WPlusA

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

section Indep

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*} [Fintype ι]

theorem eq_zero_of_sum_eq_zero_of_iSupIndep [DecidableEq ι] (p : ι → Submodule ℂ M) (hp : iSupIndep p)
    (v : ι → M) (hv : ∀ i, v i ∈ p i) (h : ∑ i, v i = 0) : ∀ i, v i = 0 := by
  intro i
  have hdis := hp i
  have hsplit : v i + ∑ j ∈ Finset.univ.erase i, v j = 0 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]; exact h
  have hvi : v i = -∑ j ∈ Finset.univ.erase i, v j := eq_neg_of_add_eq_zero_left hsplit
  have hmem : v i ∈ ⨆ (j) (_ : j ≠ i), p j := by
    rw [hvi]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hji (hv j))
  have := (Submodule.disjoint_def.mp hdis) (v i) (hv i) hmem
  exact this

theorem apply_eq_smul_of_iSupIndep [DecidableEq ι] (p : ι → Submodule ℂ M) (hp : iSupIndep p)
    (μ : ι → M) (hμ : ∀ i, μ i ∈ p i) (T : M → M)
    (hadd : T (∑ i, μ i) = ∑ i, T (μ i)) (hT : ∀ i, T (μ i) ∈ p i) (c : ℂ)
    (h : T (∑ i, μ i) = c • ∑ i, μ i) : ∀ i, T (μ i) = c • μ i := by
  have hzero : ∑ i, (T (μ i) - c • μ i) = 0 := by
    rw [Finset.sum_sub_distrib, ← hadd, h, Finset.smul_sum, sub_self]
  have := eq_zero_of_sum_eq_zero_of_iSupIndep p hp (fun i => T (μ i) - c • μ i)
    (fun i => Submodule.sub_mem _ (hT i) (Submodule.smul_mem _ c (hμ i))) hzero
  intro i
  exact sub_eq_zero.mp (this i)

end Indep

theorem isReal_rat (w : InfinitePlace ℚ) : w.IsReal := IsTotallyReal.isReal w

theorem hcov_std : CoversModCentre ℚ
    (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2) :=
  AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat

def IsGood (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ) (tys : ArchTypeFamily ℚ) (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) : Prop :=
  IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V ∧
    CuspConstituentMeets ℚ (productionPinsGeneral ℚ) ξ N S Φ V ∧ V ⊓ archCutSubmodule ℚ tys ≠ ⊥

theorem exists_decomposition
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ w : InfinitePlace ℚ, HasArchCharacterAt₀ ℚ w (χ w) φ) :
    ∃ (𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) (μ : ↥𝒲 → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)),
      (∀ W ∈ 𝒲, IsGood ξ N S Φ (ArchTypeFamily.ofChar ℚ χ) W) ∧
      iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) ∧
      (∀ W : ↥𝒲, μ W ∈ (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) ∧
      φ = ∑ W, μ W := by
  classical
  obtain ⟨α, hα, hφα⟩ := hconv
  set tys : ArchTypeFamily ℚ := ArchTypeFamily.ofChar ℚ χ with htys

  have hcut : φ ∈ archCutSubmodule ℚ tys := by
    rw [mem_archCutSubmodule_iff]
    intro w
    have h0 : φ ∈ archTypeSubmoduleAt ℚ w (tys.rep w ⟨0, by simp [htys, ArchTypeFamily.ofChar]⟩) :=
      (mem_archTypeSubmoduleAt_ofChar_iff ℚ w (χ w) φ).2 (hχ w)
    exact Submodule.mem_iSup_of_mem _ h0
  have hisoS : φ ∈ isotypicCuspSubmodule ℚ (productionPinsGeneral ℚ) ξ N S Φ := hiso.mem_isotypicCuspSubmodule

  have hmem : φ ∈ ⨆ (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (_ : IsGood ξ N S Φ tys V), V :=
    AutomorphicForm.CuspidalConstituent.mem_iSup_isCuspConstituent_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_rightConv_eq_smul
      ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) hcov_std ξ N hN S tys Φ α hα 1 one_ne_zero φ
      ⟨hisoS, hcut⟩ (by rw [hφα, one_smul])

  rw [iSup_subtype'] at hmem
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hmem
  set 𝒱 : Finset (Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) := s.image Subtype.val with h𝒱
  have h𝒱good : ∀ V ∈ 𝒱, IsGood ξ N S Φ tys V := by
    intro V hV
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hV
    exact x.2
  have hle : (⨆ x ∈ s, (x : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) ≤ ⨆ V ∈ 𝒱, V := by
    refine iSup₂_le fun x hx => ?_
    have hxV : (x : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) ∈ 𝒱 := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    exact le_iSup₂ (f := fun (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (_ : V ∈ 𝒱) => V) (x : Submodule ℂ _) hxV
  have hmem𝒱 : φ ∈ ⨆ V ∈ 𝒱, V := hle hs

  obtain ⟨𝒲, h𝒲𝒱, hind, hsup⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_subset_iSupIndep_iSup_eq_of_finset_isCuspConstituent
      ℚ (productionPinsGeneral ℚ) ξ 𝒱 (fun V hV => (h𝒱good V hV).1)
  have hmem𝒲 : φ ∈ ⨆ W ∈ 𝒲, W := by rw [hsup]; exact hmem𝒱

  have hmem𝒲' : φ ∈ ⨆ W : ↥𝒲, (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) := by
    rw [iSup_subtype'] at hmem𝒲; exact hmem𝒲
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ φ).1 hmem𝒲'
  refine ⟨𝒲, fun W => (f W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ), fun W hW => h𝒱good W (h𝒲𝒱 hW), hind,
    fun W => (f W).2, ?_⟩
  rw [← hf, DFinsupp.sum]
  refine (Finset.sum_subset (Finset.subset_univ _) fun W _ hW => ?_)
  rw [DFinsupp.notMem_support_iff.mp hW]; rfl

def rT (g : AdelicGL2 (𝓞 ℚ) ℚ) : (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) where
  toFun := rightTranslate ℚ g
  map_add' := rightTranslate_add ℚ g
  map_smul' := fun c φ => rightTranslate_smul ℚ g c φ

theorem rT_apply (g : AdelicGL2 (𝓞 ℚ) ℚ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    rT g φ x = φ (x * g) := rfl

theorem hasArchCharacterAt₀_component
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) (μ : ↥𝒲 → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hcon : ∀ W ∈ 𝒲, IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ W)
    (hind : iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))))
    (hμ : ∀ W : ↥𝒲, μ W ∈ (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)))
    (w : InfinitePlace ℚ) (χw : rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hφ : HasArchCharacterAt₀ ℚ w χw (∑ W, μ W)) (W : ↥𝒲) :
    HasArchCharacterAt₀ ℚ w χw (μ W) := by
  classical
  intro k g
  have key := apply_eq_smul_of_iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) hind μ hμ
    (rT (adelicArchGLInclAt ℚ w (k : GL (Fin 2) w.Completion)))
    (by rw [map_sum])
    (fun W' => (hcon W' W'.2).1.rightTranslate_arch_mem w k (μ W') (hμ W'))
    ((χw k : ℂˣ) : ℂ)
    (by
      funext x
      rw [rT_apply, Finset.sum_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      have := hφ k x
      rw [Finset.sum_apply, Finset.sum_apply] at this
      exact this)
    W
  have := congrFun key g
  rw [rT_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this

theorem reflection_component
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ) (tys : ArchTypeFamily ℚ)
    (𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) (μ : ↥𝒲 → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hgood : ∀ W ∈ 𝒲, IsGood ξ N S Φ tys W)
    (hind : iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))))
    (hμ : ∀ W : ↥𝒲, μ W ∈ (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)))
    (w : InfinitePlace ℚ) (hw : w.IsReal) (e : ℂ)
    (hφ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, (∑ W, μ W) (g * archRealGLAt hw UpperHalfPlane.J) = e * (∑ W, μ W) g)
    (W : ↥𝒲) :
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, μ W (g * archRealGLAt hw UpperHalfPlane.J) = e * μ W g := by
  classical
  have hstab : ∀ W' : ↥𝒲, rT (archRealGLAt hw UpperHalfPlane.J) (μ W') ∈ (W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) := by
    intro W'
    have hg := hgood W' W'.2
    have hg1 : IsCuspConstituent ℚ (productionPinsOf ℚ
        (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ξ (W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) := hg.1
    have hg2 : CuspConstituentMeets ℚ (productionPinsOf ℚ
        (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ξ N S Φ (W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) := hg.2.1
    exact AutomorphicForm.CuspidalConstituent.comp_mul_archRealGLAt_J_mem_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
      ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) hcov_std ξ N S Φ (W' : Submodule ℂ _)
      hg1 hg2 w hw (μ W') (hμ W')
  have key := apply_eq_smul_of_iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) hind μ hμ
    (rT (archRealGLAt hw UpperHalfPlane.J)) (by rw [map_sum]) hstab e
    (by
      funext x
      rw [rT_apply, Pi.smul_apply, smul_eq_mul]
      exact hφ x)
    W
  intro g
  have := congrFun key g
  rw [rT_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this

theorem level_component
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ))
    (𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) (μ : ↥𝒲 → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hcon : ∀ W ∈ 𝒲, IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ W)
    (hind : iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))))
    (hμ : ∀ W : ↥𝒲, μ W ∈ (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)))
    (hφ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ u ∈ (productionPinsGeneral ℚ).U N, (∑ W, μ W) (g * u) = (∑ W, μ W) g)
    (W : ↥𝒲) :
    μ W ∈ levelInvariantSubmodule ℚ (productionPinsGeneral ℚ) N := by
  classical
  intro g u hu
  have hufin : u ∈ finiteAdelicGL2Subgroup ℚ := (Subgroup.mem_inf.mp hu).2
  have key := apply_eq_smul_of_iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) hind μ hμ
    (rT u) (by rw [map_sum]) (fun W' => (hcon W' W'.2).1.rightTranslate_fin_mem u hufin (μ W') (hμ W')) 1
    (by
      funext x
      rw [rT_apply, one_smul]
      exact hφ x u hu)
    W
  have := congrFun key g
  rw [rT_apply, one_smul] at this
  exact this

theorem mem_cut_component
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ))
    (𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) (μ : ↥𝒲 → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hcon : ∀ W ∈ 𝒲, IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ W)
    (hind : iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))))
    (hμ : ∀ W : ↥𝒲, μ W ∈ (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)))
    (hlev : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ u ∈ (productionPinsGeneral ℚ).U N, (∑ W, μ W) (g * u) = (∑ W, μ W) g)
    (χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ w : InfinitePlace ℚ, HasArchCharacterAt₀ ℚ w (χ w) (∑ W, μ W)) (W : ↥𝒲) :
    μ W ∈ (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) ⊓ levelInvariantSubmodule ℚ (productionPinsGeneral ℚ) N ⊓
      archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) := by
  classical
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hμ W, level_component ξ N 𝒲 μ hcon hind hμ hlev W⟩, ?_⟩
  rw [mem_archCutSubmodule_iff]
  intro w
  have hw : HasArchCharacterAt₀ ℚ w (χ w) (μ W) := hasArchCharacterAt₀_component ξ 𝒲 μ hcon hind hμ w (χ w) (hχ w) W
  have h0 : μ W ∈ archTypeSubmoduleAt ℚ w ((ArchTypeFamily.ofChar ℚ χ).rep w ⟨0, by simp [ArchTypeFamily.ofChar]⟩) :=
    (mem_archTypeSubmoduleAt_ofChar_iff ℚ w (χ w) (μ W)).2 hw
  exact Submodule.mem_iSup_of_mem _ h0

theorem isArchSmoothAt_sum_and_archCasimirAt_sum {ι : Type*} (s : Finset ι) {w : InfinitePlace ℚ} (hw : w.IsReal)
    (f : ι → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (hf : ∀ i ∈ s, IsArchSmoothAt hw (f i)) :
    IsArchSmoothAt hw (∑ i ∈ s, f i) ∧ archCasimirAt hw (∑ i ∈ s, f i) = ∑ i ∈ s, archCasimirAt hw (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · first | exact isArchSmoothAt_const (F := ℚ) hw (0 : ℂ) | simpa [Pi.zero_def] using isArchSmoothAt_const (F := ℚ) hw (0 : ℂ)
    · simp only [Finset.sum_empty]
      have := archCasimirAt_const (F := ℚ) hw (0 : ℂ)
      exact this
  | insert a s ha ih =>
    have hfa : IsArchSmoothAt hw (f a) := hf a (Finset.mem_insert_self a s)
    have ih' := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨hfa.add ih'.1, by rw [archCasimirAt_add hfa ih'.1, ih'.2]⟩

theorem casimir_component
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) (μ : ↥𝒲 → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hcon : ∀ W ∈ 𝒲, IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ W)
    (hind : iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))))
    (hμ : ∀ W : ↥𝒲, μ W ∈ (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)))
    (hlev : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ u ∈ (productionPinsGeneral ℚ).U N, (∑ W, μ W) (g * u) = (∑ W, μ W) g)
    (χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ w : InfinitePlace ℚ, HasArchCharacterAt₀ ℚ w (χ w) (∑ W, μ W))
    (w : InfinitePlace ℚ) (hw : w.IsReal) (lam : ℂ)
    (hφ : IsArchSmoothAt hw (∑ W, μ W) ∧ archCasimirAt hw (∑ W, μ W) = lam • ∑ W, μ W) (W : ↥𝒲) :
    IsArchSmoothAt hw (μ W) ∧ archCasimirAt hw (μ W) = lam • μ W := by
  classical

  have hsm : ∀ W' : ↥𝒲, IsArchSmoothAt hw (μ W') ∧
      archCasimirAt hw (μ W') ∈ (W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) := by
    intro W'
    by_cases h0 : μ W' = 0
    · refine ⟨?_, ?_⟩
      · rw [h0]; exact isArchSmoothAt_const (F := ℚ) hw (0 : ℂ)
      · rw [h0]
        have : archCasimirAt hw (0 : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) = 0 := archCasimirAt_const (F := ℚ) hw (0 : ℂ)
        rw [this]; exact Submodule.zero_mem _
    · have hcut := mem_cut_component ξ N 𝒲 μ hcon hind hμ hlev χ hχ W'
      have hX : (W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) ⊓ levelInvariantSubmodule ℚ (productionPinsGeneral ℚ) N ⊓
          archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) ≠ ⊥ := by
        intro hbot
        exact h0 ((Submodule.mem_bot ℂ).mp (hbot ▸ hcut))
      have hV : IsCuspConstituent ℚ (productionPinsOf ℚ
          (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          ξ (W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) := (hcon W' W'.2)
      have hX' : (W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) ⊓ levelInvariantSubmodule ℚ (productionPinsOf ℚ
          (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) N ⊓
          archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) ≠ ⊥ := hX
      obtain ⟨lamW, hlamW⟩ :=
        AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent
          ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov_std ξ
          (W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) hV N hN (ArchTypeFamily.ofChar ℚ χ) hX' w hw
      have h := hlamW (μ W') (hμ W')
      exact ⟨h.1, by rw [h.2.2.2]; exact Submodule.smul_mem _ lamW (hμ W')⟩
  have hadd := (isArchSmoothAt_sum_and_archCasimirAt_sum (Finset.univ : Finset ↥𝒲) hw μ fun W' _ => (hsm W').1).2
  have key := apply_eq_smul_of_iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) hind μ hμ
    (archCasimirAt hw) hadd (fun W' => (hsm W').2) lam hφ.2 W
  exact ⟨(hsm W).1, key⟩

def wtChar (n : InfinitePlace ℚ → ℤ) : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ :=
  fun w => archWeightCharAt (isReal_rat w) (n w)

def lowerAt {w : InfinitePlace ℚ} (hw : w.IsReal) (x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
  archDerivAt hw ArchDir.H x - Complex.I • (archDerivAt hw ArchDir.E x + archDerivAt hw ArchDir.Fm x)

theorem isArchSmoothAt_sum_and_archDerivAt_sum {ι : Type*} (s : Finset ι) {w : InfinitePlace ℚ} (hw : w.IsReal)
    (f : ι → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (hf : ∀ i ∈ s, IsArchSmoothAt hw (f i)) (d : ArchDir) :
    IsArchSmoothAt hw (∑ i ∈ s, f i) ∧ archDerivAt hw d (∑ i ∈ s, f i) = ∑ i ∈ s, archDerivAt hw d (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · first | exact isArchSmoothAt_const (F := ℚ) hw (0 : ℂ) | simpa [Pi.zero_def] using isArchSmoothAt_const (F := ℚ) hw (0 : ℂ)
    · simp only [Finset.sum_empty]
      exact archDerivAt_const (F := ℚ) hw d (0 : ℂ)
  | insert a s ha ih =>
    have hfa : IsArchSmoothAt hw (f a) := hf a (Finset.mem_insert_self a s)
    have ih' := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨hfa.add ih'.1, by rw [archDerivAt_add hfa ih'.1, ih'.2]⟩

theorem lowerAt_sum {ι : Type*} (s : Finset ι) {w : InfinitePlace ℚ} (hw : w.IsReal)
    (f : ι → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (hf : ∀ i ∈ s, IsArchSmoothAt hw (f i)) :
    lowerAt hw (∑ i ∈ s, f i) = ∑ i ∈ s, lowerAt hw (f i) := by
  simp only [lowerAt, (isArchSmoothAt_sum_and_archDerivAt_sum s hw f hf _).2, Finset.smul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

theorem isArchSmoothAt_component
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) (μ : ↥𝒲 → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hcon : ∀ W ∈ 𝒲, IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ W)
    (hind : iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))))
    (hμ : ∀ W : ↥𝒲, μ W ∈ (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)))
    (hlev : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ u ∈ (productionPinsGeneral ℚ).U N, (∑ W, μ W) (g * u) = (∑ W, μ W) g)
    (χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ w : InfinitePlace ℚ, HasArchCharacterAt₀ ℚ w (χ w) (∑ W, μ W))
    (w : InfinitePlace ℚ) (hw : w.IsReal) (W : ↥𝒲) : IsArchSmoothAt hw (μ W) := by
  classical
  by_cases h0 : μ W = 0
  · rw [h0]; exact isArchSmoothAt_const (F := ℚ) hw (0 : ℂ)
  · have hcut := mem_cut_component ξ N 𝒲 μ hcon hind hμ hlev χ hχ W
    have hX' : (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) ⊓ levelInvariantSubmodule ℚ (productionPinsOf ℚ
        (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) N ⊓
        archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) ≠ ⊥ := by
      intro hbot
      exact h0 ((Submodule.mem_bot ℂ).mp (hbot ▸ hcut))
    have hV : IsCuspConstituent ℚ (productionPinsOf ℚ
        (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ξ (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) := (hcon W W.2)
    obtain ⟨lamW, hlamW⟩ :=
      AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent
        ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov_std ξ
        (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) hV N hN (ArchTypeFamily.ofChar ℚ χ) hX' w hw
    exact (hlamW (μ W) (hμ W)).1

theorem lower_component
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) (μ : ↥𝒲 → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hcon : ∀ W ∈ 𝒲, IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ W)
    (hind : iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))))
    (hμ : ∀ W : ↥𝒲, μ W ∈ (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)))
    (hlev : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ u ∈ (productionPinsGeneral ℚ).U N, (∑ W, μ W) (g * u) = (∑ W, μ W) g)
    (n : InfinitePlace ℚ → ℤ)
    (hχ : ∀ w : InfinitePlace ℚ, HasArchCharacterAt₀ ℚ w (wtChar n w) (∑ W, μ W))
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (hφ : lowerAt hw (∑ W, μ W) = 0) (W : ↥𝒲) : lowerAt hw (μ W) = 0 := by
  classical
  have hsm : ∀ W' : ↥𝒲, IsArchSmoothAt hw (μ W') :=
    fun W' => isArchSmoothAt_component ξ N hN 𝒲 μ hcon hind hμ hlev (wtChar n) hχ w hw W'

  have hstab : ∀ W' : ↥𝒲, lowerAt hw (μ W') ∈ (W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) := by
    intro W'
    have hcut := mem_cut_component ξ N 𝒲 μ hcon hind hμ hlev (wtChar n) hχ W'
    have hy : μ W' ∈ (W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) ⊓ levelInvariantSubmodule ℚ (productionPinsOf ℚ
        (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) N ⊓
        archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ (wtChar n)) := hcut
    have hV : IsCuspConstituent ℚ (productionPinsOf ℚ
        (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ξ (W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) := (hcon W' W'.2)
    have h := AutomorphicForm.CuspidalConstituent.iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar
      ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov_std ξ
      (W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) hV isReal_rat N hN (wtChar n) w hw (n w) rfl
      (fun m v => archWeightCharAt (isReal_rat v) m)
      (fun m v hv => absurd (Subsingleton.elim v w) hv) (fun m => rfl) (μ W') hy
    have h1 := h.1 1
    simp only [Function.iterate_one] at h1
    exact (Submodule.mem_inf.mp (Submodule.mem_inf.mp h1).1).1
  have hadd : lowerAt hw (∑ W', μ W') = ∑ W', lowerAt hw (μ W') := lowerAt_sum _ hw μ fun W' _ => hsm W'
  have key := apply_eq_smul_of_iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) hind μ hμ
    (lowerAt hw) hadd hstab 0 (by rw [hφ, zero_smul]) W
  rw [key, zero_smul]

section SmoothCuspSpan

open FLT.SmoothVectors HeckeIntegralSeam

variable {F : Type} [Field F] [NumberField F]

theorem integrable_slice_cond {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ)
    (x : AdelicGL2 (𝓞 F) F) :
    @Integrable _ _ _ _ (adeleBorel (𝓞 F) F) (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * x))
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have hcont : Continuous fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * x) := by
    refine hφ.comp (Continuous.mul ?_ continuous_const)
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> fun_prop
    · have hinv : ∀ q : AdeleRing (𝓞 F) F, ((unipotentGL2 q)⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F))
          = unipotentGL2 (-q) := fun q =>
        inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
      simp_rw [hinv]
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp only [unipotentGL2_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
        fun_prop
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  have hIC : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * x)) C
      (adelicAddHaar (𝓞 F) F) := hcont.continuousOn.integrableOn_compact hC
  have hIB : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * x)) (adelicBox F)
      (adelicAddHaar (𝓞 F) F) := hIC.mono_set hsub
  unfold ProbabilityTheory.cond
  refine Integrable.smul_measure hIB ?_
  exact ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne'

theorem isCuspidalFn_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ : @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 φ)
    (hψ : @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 ψ) :
    @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 (φ + ψ) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  intro g
  have h1 := hφ g
  have h2 := hψ g
  unfold constantTerm constantTermIntegrand at h1 h2 ⊢
  simp only [Pi.add_apply]
  rw [integral_add (integrable_slice_cond hφc g) (integrable_slice_cond hψc g), h1, h2, add_zero]

theorem isCuspidalFn_smul {φ : AdelicGL2 (𝓞 F) F → ℂ} (a : ℂ)
    (hφ : @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 φ) :
    @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 (a • φ) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  intro g
  have h1 := hφ g
  unfold constantTerm constantTermIntegrand at h1 ⊢
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, h1, mul_zero]

theorem isKfSmooth_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) (hψ : IsKfSmooth F ψ) :
    IsKfSmooth F (φ + ψ) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup] at hφ hψ ⊢
  obtain ⟨V₁, hV₁o, hV₁⟩ := hφ
  obtain ⟨V₂, hV₂o, hV₂⟩ := hψ
  refine ⟨V₁ ⊓ V₂, ?_, fun u hu => ?_⟩
  · rw [Subgroup.coe_inf]
    exact hV₁o.inter hV₂o
  · obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    have h1 := fun y => congrArg (fun f => RightTranslationFn.toFun f y) (hV₁ u hu1)
    have h2 := fun y => congrArg (fun f => RightTranslationFn.toFun f y) (hV₂ u hu2)
    refine RightTranslationFn.ext fun y => ?_
    simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk,
      Pi.add_apply] at h1 h2 ⊢
    rw [h1 y, h2 y]

theorem isKfSmooth_smul {φ : AdelicGL2 (𝓞 F) F → ℂ} (a : ℂ) (hφ : IsKfSmooth F φ) :
    IsKfSmooth F (a • φ) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup] at hφ ⊢
  obtain ⟨V₁, hV₁o, hV₁⟩ := hφ
  refine ⟨V₁, hV₁o, fun u hu => ?_⟩
  have h1 := fun y => congrArg (fun f => RightTranslationFn.toFun f y) (hV₁ u hu)
  refine RightTranslationFn.ext fun y => ?_
  simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk,
    Pi.smul_apply] at h1 ⊢
  rw [h1 y]

variable (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
  (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)

abbrev pp : CarrierPins F := productionPinsOf F D U gen (adelicBox F)

theorem isSmoothCuspAutomorphicFnAt_add (ξ : (pp D U gen).Z →* ℂˣ)
    {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ : IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ φ)
    (hψ : IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ ψ) :
    IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ (φ + ψ) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  have hφm := (AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ φ).mp hφ.1.1
  have hψm := (AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ ψ).mp hψ.1.1
  have hLs : IsLsXiFunction (𝓞 F) F (pp D U gen).Z ξ (φ + ψ) := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · simp only [Pi.add_apply, hφm.1.left_invariant γ g, hψm.1.left_invariant γ g]
    · simp only [Pi.add_apply, hφm.1.central_transform z g, hψm.1.central_transform z g, mul_add]
  have hL2 : MemLp (φ + ψ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) := hφm.2.add hψm.2
  refine ⟨⟨(AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ (φ + ψ)).mpr ⟨hLs, hL2⟩, ?_⟩, ?_⟩
  · exact isCuspidalFn_add hφc hψc hφ.1.2 hψ.1.2
  · exact isKfSmooth_add hφ.2 hψ.2

theorem isSmoothCuspAutomorphicFnAt_smul (ξ : (pp D U gen).Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (a : ℂ)
    (hφ : IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ φ) :
    IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ (a • φ) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  have hφm := (AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ φ).mp hφ.1.1
  have hLs : IsLsXiFunction (𝓞 F) F (pp D U gen).Z ξ (a • φ) := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · simp only [Pi.smul_apply, hφm.1.left_invariant γ g]
    · simp only [Pi.smul_apply, smul_eq_mul, hφm.1.central_transform z g]
      ring
  have hL2 : MemLp (a • φ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) := by
    have := hφm.2.const_mul a
    exact this
  refine ⟨⟨(AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ (a • φ)).mpr ⟨hLs, hL2⟩, ?_⟩, ?_⟩
  · exact isCuspidalFn_smul a hφ.1.2
  · exact isKfSmooth_smul a hφ.2

theorem eq_zero_or_smoothCusp_of_mem_cuspKFiniteSubmodule (ξ : (pp D U gen).Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ CuspidalConstituent.cuspKFiniteSubmodule F (pp D U gen) ξ) :
    φ = 0 ∨ (IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ φ ∧ Continuous φ) := by
  refine Submodule.span_induction
    (p := fun φ _ => φ = 0 ∨ (IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ φ ∧ Continuous φ)) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨hsat, hcont, -⟩
    refine Or.inr ⟨?_, hcont⟩
    have h1 := hsat 1
    have hrt : CuspidalConstituent.rightTranslate F 1 φ = φ := by
      funext y; simp [CuspidalConstituent.rightTranslate]
    rwa [hrt] at h1
  · exact Or.inl rfl
  · intro φ ψ _ _ hφ hψ
    rcases hφ with rfl | hφ
    · simpa using hψ
    rcases hψ with rfl | hψ
    · simpa using Or.inr hφ
    exact Or.inr ⟨isSmoothCuspAutomorphicFnAt_add D U gen ξ hφ.2 hψ.2 hφ.1 hψ.1, hφ.2.add hψ.2⟩
  · intro a φ _ hφ
    rcases hφ with rfl | hφ
    · exact Or.inl (smul_zero a)
    exact Or.inr ⟨isSmoothCuspAutomorphicFnAt_smul D U gen ξ a hφ.1, hφ.2.const_smul a⟩

theorem glArch_eq_one_of_isHeckeCosetSystem {U : Subgroup (AdelicGL2 (𝓞 F) F)} (hU : U ≤ finiteAdelicGL2Subgroup F)
    {gv : AdelicGL2 (𝓞 F) F} (hgv : gv ∈ finiteAdelicGL2Subgroup F) {n : ℕ} {reps : Fin n → AdelicGL2 (𝓞 F) F}
    (hsys : IsHeckeCosetSystem U gv reps) (i : Fin n) :
    AdelicLevel.glArch (𝓞 F) F (reps i) = 1 := by
  have hmem := hsys.mem_doubleCoset i
  obtain ⟨u, hu, u', hu', heq⟩ := HeckePair.mem_doubleCoset_iff.mp hmem
  have : reps i ∈ finiteAdelicGL2Subgroup F := by
    rw [← heq]
    exact mul_mem (mul_mem (hU hu) hgv) (hU hu')
  exact this

theorem heckeGen_mem_finiteAdelicGL2Subgroup (v : HeightOneSpectrum (𝓞 F)) :
    heckeGen (𝓞 F) F v ∈ finiteAdelicGL2Subgroup F := by
  show AdelicLevel.glArch (𝓞 F) F (heckeGen (𝓞 F) F v) = 1
  apply Units.ext
  rw [Units.val_one]
  ext i j
  rw [glArch_apply]
  unfold heckeGen
  exact heckeGenAt_fst (uniformizerUnit F v) i j

end SmoothCuspSpan

theorem continuous_component
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) (μ : ↥𝒲 → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hcon : ∀ W ∈ 𝒲, IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ W)
    (hμ : ∀ W : ↥𝒲, μ W ∈ (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) (W : ↥𝒲) :
    Continuous (μ W) := by
  rcases eq_zero_or_smoothCusp_of_mem_cuspKFiniteSubmodule (classRepSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) ξ
      ((hcon W W.2).1.le (hμ W)) with h | h
  · rw [h]; exact continuous_const
  · exact h.2

theorem smoothCusp_component
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) (μ : ↥𝒲 → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hcon : ∀ W ∈ 𝒲, IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ W)
    (hμ : ∀ W : ↥𝒲, μ W ∈ (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) (W : ↥𝒲) (h0 : μ W ≠ 0) :
    IsSmoothCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ (μ W) ∧ Continuous (μ W) := by
  rcases eq_zero_or_smoothCusp_of_mem_cuspKFiniteSubmodule (classRepSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) ξ
      ((hcon W W.2).1.le (hμ W)) with h | h
  · exact absurd h h0
  · exact h

theorem hecke_component
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ))
    (𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) (μ : ↥𝒲 → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hcon : ∀ W ∈ 𝒲, IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ W)
    (hind : iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))))
    (hμ : ∀ W : ↥𝒲, μ W ∈ (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)))
    (v : HeightOneSpectrum (𝓞 ℚ)) {m : ℕ} (reps : Fin m → AdelicGL2 (𝓞 ℚ) ℚ)
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem ((productionPinsGeneral ℚ).U N)
      ((productionPinsGeneral ℚ).gen v) reps)
    (a : ℂ) (hφ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, SmoothCusp.heckeCosetSum ℚ reps (∑ W, μ W) g = a * (∑ W, μ W) g)
    (W : ↥𝒲) :
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, SmoothCusp.heckeCosetSum ℚ reps (μ W) g = a * μ W g := by
  classical

  have hT : ∀ ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
      (fun g => SmoothCusp.heckeCosetSum ℚ reps ψ g) = ∑ i, rT (reps i) ψ := by
    intro ψ; funext g
    simp only [SmoothCusp.heckeCosetSum, Finset.sum_apply]
    rfl
  have hreps : ∀ i, reps i ∈ finiteAdelicGL2Subgroup ℚ := fun i =>
    glArch_eq_one_of_isHeckeCosetSystem (fun u hu => (Subgroup.mem_inf.mp hu).2)
      (heckeGen_mem_finiteAdelicGL2Subgroup v) hsys i
  have hadd : (fun g => SmoothCusp.heckeCosetSum ℚ reps (∑ W', μ W') g)
      = ∑ W', (fun g => SmoothCusp.heckeCosetSum ℚ reps (μ W') g) := by
    rw [hT]
    simp only [hT, map_sum]
    rw [Finset.sum_comm]
  have hstab : ∀ W' : ↥𝒲, (fun g => SmoothCusp.heckeCosetSum ℚ reps (μ W') g)
      ∈ (W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) := fun W' => by
    rw [hT]
    exact Submodule.sum_mem _ fun i _ => (hcon W' W'.2).1.rightTranslate_fin_mem _ (hreps i) _ (hμ W')
  have key := apply_eq_smul_of_iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) hind μ hμ
    (fun ψ g => SmoothCusp.heckeCosetSum ℚ reps ψ g) hadd hstab a
    (by funext g; rw [Pi.smul_apply, smul_eq_mul]; exact hφ g) W
  intro g
  have := congrFun key g
  rw [Pi.smul_apply, smul_eq_mul] at this
  exact this

theorem central_value
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ) (hne : φ ≠ 0)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ S) :
    ((ξ ⟨Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)
      = Φ.toRawCentral.b v := by
  obtain ⟨g₀, hg₀⟩ : ∃ g, φ g ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  letI := (productionPinsGeneral ℚ).mS
  have hct : φ (centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen v)) * g₀)
      = ((ξ ⟨Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)
        * φ g₀ :=
    (((lsXiMemberAt_iff (𝓞 ℚ) ℚ (productionPinsGeneral ℚ).μ (productionPinsGeneral ℚ).Z ξ
      (productionPinsGeneral ℚ).D φ).mp hiso.smoothCusp.1.1).1).central_transform
      ⟨Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen v), Subgroup.mem_top _⟩ g₀
  rw [hiso.central_eigen v hv g₀] at hct
  exact (mul_right_cancel₀ hg₀ hct).symm

theorem isIsotypicCuspFormAt_component
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ) (hne : φ ≠ 0)
    (𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) (μ : ↥𝒲 → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hcon : ∀ W ∈ 𝒲, IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ W)
    (hind : iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))))
    (hμ : ∀ W : ↥𝒲, μ W ∈ (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)))
    (hsum : φ = ∑ W, μ W) (W : ↥𝒲) (h0 : μ W ≠ 0) :
    IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ (μ W) := by
  classical
  have hsc := smoothCusp_component ξ 𝒲 μ hcon hμ W h0
  refine ⟨hsc.1, hsc.2, ?_, ?_, ?_⟩
  ·
    exact level_component ξ N 𝒲 μ hcon hind hμ (by rw [← hsum]; exact hiso.level_invariant) W
  ·
    intro v hv
    obtain ⟨reps, hsys, heig⟩ := hiso.hecke_eigen v hv
    exact ⟨reps, hsys, hecke_component ξ N 𝒲 μ hcon hind hμ v reps hsys (Φ.a v)
      (by rw [← hsum]; exact heig) W⟩
  ·
    intro v hv g
    letI := (productionPinsGeneral ℚ).mS
    have hct : μ W (centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen v)) * g)
        = ((ξ ⟨Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)
          * μ W g :=
      (((lsXiMemberAt_iff (𝓞 ℚ) ℚ (productionPinsGeneral ℚ).μ (productionPinsGeneral ℚ).Z ξ
        (productionPinsGeneral ℚ).D (μ W)).mp hsc.1.1.1).1).central_transform
        ⟨Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen v), Subgroup.mem_top _⟩ g
    rw [central_value ξ N S Φ φ hiso hne v hv] at hct
    exact hct

theorem rightConv_finset_sum {ι : Type*} (s : Finset ι) (f : ι → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hf : ∀ i ∈ s, Continuous (f i)) {α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hα : Continuous α)
    (hαc : HasCompactSupport α) :
    rightConv ℚ (∑ i ∈ s, f i) α = ∑ i ∈ s, rightConv ℚ (f i) α := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact rightConv_zero_left ℚ α
  | insert a s ha ih =>
    have hfa : Continuous (f a) := hf a (Finset.mem_insert_self a s)
    have hf' : ∀ i ∈ s, Continuous (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsc : Continuous (∑ i ∈ s, f i) := by
      rw [Finset.sum_fn]
      exact continuous_finsetSum s fun i hi => hf' i hi
    rw [Finset.sum_insert ha, Finset.sum_insert ha, rightConv_add_left ℚ hfa hsc hα hαc, ih hf']

theorem reproduce_component
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) (μ : ↥𝒲 → (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hcon : ∀ W ∈ 𝒲, IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ W)
    (hind : iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))))
    (hμ : ∀ W : ↥𝒲, μ W ∈ (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)))
    (tys : ArchTypeFamily ℚ) (α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hα : IsFactorizableTestFn ℚ α)
    (hbf : IsArchBiFinite ℚ tys α)
    (hφ : rightConv ℚ (∑ W, μ W) α = ∑ W, μ W) (W : ↥𝒲) :
    rightConv ℚ (μ W) α = μ W := by
  classical
  obtain ⟨hαc, hαK⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn ℚ α hα
  have hcont : ∀ W' : ↥𝒲, Continuous (μ W') := continuous_component ξ 𝒲 μ hcon hμ
  have hadd : rightConv ℚ (∑ W', μ W') α = ∑ W', rightConv ℚ (μ W') α :=
    rightConv_finset_sum _ μ (fun W' _ => hcont W') hαc hαK
  have hstab : ∀ W' : ↥𝒲, rightConv ℚ (μ W') α ∈ (W' : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) :=
    fun W' => (hcon W' W'.2).1.rightConv_mem α tys hα hbf _ (hμ W')
  have key := apply_eq_smul_of_iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))) hind μ hμ
    (fun ψ => rightConv ℚ ψ α) hadd hstab 1 (by rw [one_smul]; exact hφ) W
  rw [one_smul] at key
  exact key

end P2M.WPlusA

end

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent P2M.WPlusA in
theorem solution
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ)
    (hne : φ ≠ 0)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ n : ℤ, HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ) :
    ∃ (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V ∧
      φ' ∈ V ∧
      IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ' ∧
      φ' ≠ 0 ∧
      (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ' α = φ') ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (n : ℤ),
        HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ → HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ') ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (lam : ℂ),
        (IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = lam • φ) →
          (IsArchSmoothAt hw φ' ∧ archCasimirAt hw φ' = lam • φ')) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (e : ℂ),
        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ (g * archRealGLAt hw UpperHalfPlane.J) = e * φ g) →
          ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ' (g * archRealGLAt hw UpperHalfPlane.J) = e * φ' g) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        archDerivAt hw ArchDir.H φ
            - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ) = 0 →
          archDerivAt hw ArchDir.H φ'
            - Complex.I • (archDerivAt hw ArchDir.E φ' + archDerivAt hw ArchDir.Fm φ') = 0) := by
  classical

  choose n hn using fun w : InfinitePlace ℚ => hwt w (isReal_rat w)
  have hχ : ∀ w : InfinitePlace ℚ, HasArchCharacterAt₀ ℚ w (wtChar n w) φ := hn

  obtain ⟨𝒲, μ, hgood, hind, hμ, hsum⟩ := exists_decomposition ξ N hN S Φ φ hiso hconv (wtChar n) hχ
  have hcon : ∀ W ∈ 𝒲, IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ W := fun W hW => (hgood W hW).1

  obtain ⟨W, hW0⟩ : ∃ W : ↥𝒲, μ W ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    rw [hsum]
    exact Finset.sum_eq_zero fun W _ => h W

  have hlev : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ u ∈ (productionPinsGeneral ℚ).U N, (∑ W, μ W) (g * u) = (∑ W, μ W) g := by
    rw [← hsum]; exact hiso.level_invariant
  have hχ' : ∀ w : InfinitePlace ℚ, HasArchCharacterAt₀ ℚ w (wtChar n w) (∑ W, μ W) := by
    rw [← hsum]; exact hχ

  obtain ⟨α, hα, hφα⟩ := hconv
  have hcut : φ ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ (wtChar n)) := by
    rw [mem_archCutSubmodule_iff]
    intro w
    have h0 : φ ∈ archTypeSubmoduleAt ℚ w
        ((ArchTypeFamily.ofChar ℚ (wtChar n)).rep w ⟨0, by simp [ArchTypeFamily.ofChar]⟩) :=
      (mem_archTypeSubmoduleAt_ofChar_iff ℚ w (wtChar n w) φ).2 (hχ w)
    exact Submodule.mem_iSup_of_mem _ h0
  obtain ⟨α', hα', hbf', hφα'⟩ :=
    AutomorphicForm.exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul ℚ
      (ArchTypeFamily.ofChar ℚ (wtChar n)) φ hiso.continuous hcut α hα 1 (by rw [hφα, one_smul])
  rw [one_smul, hsum] at hφα'
  refine ⟨(W : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)), μ W, hcon W W.2, hμ W,
    isIsotypicCuspFormAt_component ξ N S Φ φ hiso hne 𝒲 μ hcon hind hμ hsum W hW0, hW0,
    ⟨α', hα', reproduce_component ξ 𝒲 μ hcon hind hμ _ α' hα' hbf' hφα' W⟩, ?_, ?_, ?_, ?_⟩
  · intro w hw m h
    exact hasArchCharacterAt₀_component ξ 𝒲 μ hcon hind hμ w (archWeightCharAt hw m) (by rw [← hsum]; exact h) W
  · intro w hw lam h
    exact casimir_component ξ N hN 𝒲 μ hcon hind hμ hlev (wtChar n) hχ' w hw lam (by rw [← hsum]; exact h) W
  · intro w hw e h
    exact reflection_component ξ N S Φ (ArchTypeFamily.ofChar ℚ (wtChar n)) 𝒲 μ hgood hind hμ w hw e
      (by rw [← hsum]; exact h) W
  · intro w hw h
    show lowerAt hw (μ W) = 0
    exact lower_component ξ N hN 𝒲 μ hcon hind hμ hlev n hχ' w hw (by show lowerAt hw (∑ W, μ W) = 0; rw [← hsum]; exact h) W

end S_LanglandsTunnell_exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq
end P2MW
export P2MW.S_LanglandsTunnell_exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq (solution)
