-- Prove2me | solution 1 for LanglandsTunnell.exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/72da9498-d54c-5970-b680-764307033aea

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le
import Theorems.Thm_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_archOccursInClassOf_archWeightChar_of_coversModCentre_of_pos
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent
import Theorems.Thm_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_archCasimirAt_rightConv_eq_smul_of_archCasimirAt_eq_smul_of_isArchSmoothAt_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite
import Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_IsIsotypicCuspFormAt_of_le_of_subset
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite
import Theorems.Thm_AutomorphicForm_hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt
import Theorems.Thm_AutomorphicForm_continuous_whittakerCoefficient
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi"
p2m_attr_erase "simp" "LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply"
p2m_attr_erase "simp" "IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

noncomputable section
open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
section ModShells

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume NumberField.AdelicVolume
open scoped ENNReal

namespace SmwShell

variable (F : Type) [Field F] [NumberField F]

private theorem memLp_two_restrict_of_bound (D : Set (AdelicGL2 (𝓞 F) F))
    (hD : adelicGLHaar (Fin 2) (𝓞 F) F D < ⊤)
    (v : AdelicGL2 (𝓞 F) F → ℂ) (hv : Continuous v) (C : ℝ) (hC : ∀ g ∈ D, ‖v g‖ ≤ C) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hD⟩
  refine MemLp.of_bound hv.aestronglyMeasurable C ?_
  rw [ae_restrict_iff (isClosed_le hv.norm continuous_const).measurableSet]
  exact ae_of_all _ hC

private theorem rightConv_mul_left_of_forall {φ f : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F}
    (hφ : ∀ x, φ (h * x) = φ x) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (h * g) = rightConv F φ f g := by
  rw [← rightConv_comp_mul_left]
  simp only [hφ]

private theorem rightConv_mul_left_of_forall_mul {φ f : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F}
    {c : ℂ} (hφ : ∀ x, φ (h * x) = c * φ x) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (h * g) = c * rightConv F φ f g := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  rw [← rightConv_comp_mul_left, rightConv_apply, rightConv_apply]
  simp only [hφ, mul_assoc]
  exact MeasureTheory.integral_const_mul _ _

private theorem isLsXiFunction_rightConv_of_isLsXiFunction (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    IsLsXiFunction (𝓞 F) F Z ξ (rightConv F φ f) where
  left_invariant γ g := rightConv_mul_left_of_forall F (fun x => hφ.left_invariant γ x) g
  central_transform z g := rightConv_mul_left_of_forall_mul F (fun x => hφ.central_transform z x) g

private theorem memLp_rightConv_of_lt (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsSmoothCuspAutomorphicFnAt F
      ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))) ξ φ)
    (hφc : Continuous φ) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MemLp (rightConv F φ f) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
  have hcont : Continuous (rightConv F φ f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hφc f hf).1
  obtain ⟨C, hC⟩ :=
    AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
      F c u d₁ d₂ T hc hd₁ hd hcov ξ f hf
  have hbound := hC φ hφ hφc
  have hfin : adelicGLHaar (Fin 2) (𝓞 F) F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) < ⊤ := by
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    exact measure_biUnion_lt_top T.finite_toSet
      (fun x _ => adelicGLHaar_mul_right_centreCutSiegelSet_lt_top F hc u hd₁ d₂ x)
  exact memLp_two_restrict_of_bound F _ hfin (rightConv F φ f) hcont _ hbound

end SmwShell

end ModShells

section ModConvHalf

set_option autoImplicit false

namespace ArchFiniteVector
namespace ConvHalf

variable (F : Type) [Field F] [NumberField F]

private theorem isFactorizableTestFn_mk (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) :
    IsFactorizableTestFn F (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) :=
  ⟨fa, ff, hfa, hff, fun _ => rfl⟩

end ArchFiniteVector.ConvHalf

end ModConvHalf

section ModConvHalfR

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

namespace G1PrimeRat
namespace ConvHalf

variable (F : Type) [Field F] [NumberField F]

private theorem exists_ne_zero_of_rightConv_ne_zero (φ f : AdelicGL2 (𝓞 F) F → ℂ) (h : ∃ g, rightConv F φ f g ≠ 0) :
    ∃ y, f y ≠ 0 := by
  obtain ⟨g, hg⟩ := h
  by_contra hcon
  refine hg ?_
  have hf : f = fun _ => 0 := funext fun y => Classical.by_contradiction fun hy => hcon ⟨y, hy⟩
  rw [hf, rightConv_zero_right]

private theorem support_shape_of_finFactor (N : Ideal (𝓞 F)) (f₀ : AdelicGL2 (𝓞 F) F → ℂ)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hf₀ : ∀ g, f₀ g = fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) (hne : ∃ y₀, f₀ y₀ ≠ 0)
    (hsupp : ∀ x, f₀ x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ∧ x = a * k)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hf : ∀ g, f g = fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) :
    ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ∧ x = a * k := by
  intro x hx
  obtain ⟨y₀, hy₀⟩ := hne
  have hffx : ff (glFin (𝓞 F) F x) ≠ 0 := fun h => hx (by rw [hf x, h, mul_zero])
  have hfa₀ : fa₀ (glArch (𝓞 F) F y₀) ≠ 0 := fun h => hy₀ (by rw [hf₀ y₀, h, zero_mul])
  have hyA : glArch (𝓞 F) F
      (adelicArchGLIncl F (glArch (𝓞 F) F y₀) * (adelicArchGLIncl F (glArch (𝓞 F) F x))⁻¹ * x)
        = glArch (𝓞 F) F y₀ := by
    simp only [map_mul, map_inv, glArch_adelicArchGLIncl, inv_mul_cancel_right]
  have hyF : glFin (𝓞 F) F
      (adelicArchGLIncl F (glArch (𝓞 F) F y₀) * (adelicArchGLIncl F (glArch (𝓞 F) F x))⁻¹ * x)
        = glFin (𝓞 F) F x := by
    simp only [map_mul, map_inv, glFin_adelicArchGLIncl, inv_one, one_mul]
  have hy : f₀ (adelicArchGLIncl F (glArch (𝓞 F) F y₀) * (adelicArchGLIncl F (glArch (𝓞 F) F x))⁻¹ * x) ≠ 0 := by
    rw [hf₀, hyA, hyF]
    exact mul_ne_zero hfa₀ hffx
  obtain ⟨a', k, ha', hk, hyk⟩ := hsupp _ hy
  refine ⟨adelicArchGLIncl F (glArch (𝓞 F) F x) * (adelicArchGLIncl F (glArch (𝓞 F) F y₀))⁻¹ * a', k, ?_, hk, ?_⟩
  · simp only [map_mul, map_inv, glFin_adelicArchGLIncl, ha', inv_one, mul_one]
  · rw [mul_assoc, ← hyk]
    group

private theorem isIsotypicCuspFormAt_rightConv_of_memLp (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F ∧ x = a * k)
    (hmem : letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
      MemLp (rightConv F R.toFun f) 2
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))) :
    IsIsotypicCuspFormAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      R.centralChar Φ.level R.exceptionalSet Φ (rightConv F R.toFun f) := by
  obtain ⟨hcusp, hkf, hlev, hhecke⟩ :=
    AutomorphicForm.isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
      F c u d₁ d₂ T Φ.toRawCentral R hR f hf hfs
  have hcont : Continuous (rightConv F R.toFun f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F R.toFun hR f hf).1
  have hauto : IsAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      R.centralChar R.toFun := R.smoothCusp.1.1
  have hlsxi : IsLsXiFunction (𝓞 F) F ⊤ R.centralChar R.toFun :=
    ((@lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _ (glBorel (Fin 2) (𝓞 F) F) (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ R.centralChar
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) R.toFun).mp hauto).1
  have hauto' : IsAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      R.centralChar (rightConv F R.toFun f) :=
    (@lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _ (glBorel (Fin 2) (𝓞 F) F) (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ R.centralChar
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (rightConv F R.toFun f)).mpr
      ⟨SmwShell.isLsXiFunction_rightConv_of_isLsXiFunction F ⊤ R.centralChar hlsxi f, hmem⟩
  exact ⟨⟨⟨hauto', hcusp⟩, hkf⟩, hcont, hlev, hhecke,
    fun v hv g => SmwShell.rightConv_mul_left_of_forall_mul F (fun x => R.central_eigen v hv x) g⟩

private theorem exists_finFactor_forall_isIsotypicCuspFormAt_rightConv (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂) (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      Φ.toRawCentral)
    (hR : Continuous R.toFun)
    (f₀ : AdelicGL2 (𝓞 F) F → ℂ) (hf₀ : IsFactorizableTestFn F f₀) (hne : ∃ y₀, f₀ y₀ ≠ 0)
    (hsupp : ∀ x, f₀ x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F ∧ x = a * k) :
    ∃ (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ),
      IsArchTestFactor F fa₀ ∧ IsFinTestFactor F ff ∧
        (∀ g, f₀ g = fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∧
        ∀ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchTestFactor F fa →
          IsIsotypicCuspFormAt F
            (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
            R.centralChar Φ.level R.exceptionalSet Φ
            (rightConv F R.toFun (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g))) := by
  obtain ⟨fa₀, ff, hfa₀, hff, hf₀eq⟩ := hf₀
  refine ⟨fa₀, ff, hfa₀, hff, hf₀eq, fun fa hfa => ?_⟩
  have hf : IsFactorizableTestFn F (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) :=
    ArchFiniteVector.ConvHalf.isFactorizableTestFn_mk F fa hfa ff hff
  have hfs := support_shape_of_finFactor F Φ.level f₀ fa₀ ff hf₀eq hne hsupp _ fa (fun _ => rfl)
  exact isIsotypicCuspFormAt_rightConv_of_memLp F c u d₁ d₂ T Φ R hR _ hf hfs
    (SmwShell.memLp_rightConv_of_lt F c u d₁ d₂ T hd hc hd₁ hcov R.centralChar R.toFun R.smoothCusp hR _ hf)

end G1PrimeRat.ConvHalf

end ModConvHalfR
end

section BlockL1

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm IsDedekindDomain
open scoped Classical

noncomputable section

namespace Ws23
namespace CASD
namespace Interchange

noncomputable def integralCLM {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (ρ : Measure Y) [IsFiniteMeasure ρ] (e : C(Y, ℂ)) :
    C(Y, ℂ) →L[ℝ] ℂ :=
  haveI : IsFiniteMeasureOnCompacts ρ :=
    isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace.mp inferInstance
  have hint : ∀ F : C(Y, ℂ), Integrable (fun y => F y) ρ := fun F =>
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  LinearMap.mkContinuous
    { toFun := fun F => ∫ y, F y * e y ∂ρ
      map_add' := fun F₁ F₂ => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint (F₁ * e)) (hint (F₂ * e))
      map_smul' := fun r F => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply, smul_mul_assoc]
        exact integral_smul r fun y => F y * e y }
    (‖e‖ * ρ.real Set.univ) fun F => by
      refine (norm_integral_le_of_norm_le_const (μ := ρ) (C := ‖F‖ * ‖e‖)
        (Filter.Eventually.of_forall fun y => ?_)).trans (le_of_eq (by ring))
      rw [norm_mul]
      exact mul_le_mul (F.norm_coe_le_norm y) (e.norm_coe_le_norm y) (norm_nonneg _) (norm_nonneg _)

theorem integralCLM_apply {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (ρ : Measure Y) [IsFiniteMeasure ρ] (e : C(Y, ℂ))
    (F : C(Y, ℂ)) : integralCLM ρ e F = ∫ y, F y * e y ∂ρ :=
  rfl

section Slices

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {Q : Type*} [TopologicalSpace Q] (S : Set Q)
  {u : Q → G} (hu : Continuous u) {φ : G → ℂ} (hφ : Continuous φ) {f : G → ℂ} (hf : Continuous f)
  (g : G)

def sliceFn : C(G × S, ℂ) :=
  ⟨fun p => φ (u p.2 * g * p.1) * f p.1, by fun_prop⟩

noncomputable def slice (x : G) : C(S, ℂ) :=
  (sliceFn S hu hφ hf g).curry x

theorem slice_apply (x : G) (q : S) : slice S hu hφ hf g x q = φ (u q * g * x) * f x :=
  rfl

theorem continuous_slice : Continuous (slice S hu hφ hf g) :=
  (sliceFn S hu hφ hf g).curry.continuous

theorem hasCompactSupport_slice (hfs : HasCompactSupport f) :
    HasCompactSupport (slice S hu hφ hf g) := by
  refine hfs.mono fun x hx => ?_
  rw [Function.mem_support] at hx ⊢
  intro hfx
  apply hx
  ext q
  rw [slice_apply, hfx, mul_zero, ContinuousMap.zero_apply]

end Slices

theorem integral_integral_mul_comm
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {Q : Type*} [TopologicalSpace Q] [T2Space Q] [MeasurableSpace Q] [OpensMeasurableSpace Q]
    (ν : Measure Q) [IsFiniteMeasure ν] {S : Set Q} (hS : IsCompact S) (hνS : ∀ᵐ q ∂ν, q ∈ S)
    {u : Q → G} (hu : Continuous u) {φ : G → ℂ} (hφ : Continuous φ) {f : G → ℂ}
    (hf : Continuous f) (hfs : HasCompactSupport f) {e : Q → ℂ} (he : Continuous e) (g : G) :
    ∫ q, (∫ x, φ (u q * g * x) * f x ∂μ) * e q ∂ν = ∫ x, (∫ q, φ (u q * (g * x)) * e q ∂ν) * f x ∂μ := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hres : ν.restrict S = ν := Measure.restrict_eq_self_of_ae_mem hνS
  set eS : C(S, ℂ) := ⟨fun q => e q, he.comp continuous_subtype_val⟩ with heS
  have hsub : ∀ h : Q → ℂ, ∫ q : S, h q ∂(ν.comap Subtype.val) = ∫ q, h q ∂ν := fun h => by
    rw [integral_subtype_comap hSm, hres]
  have hΦi : Integrable (slice S hu hφ hf g) μ :=
    (continuous_slice S hu hφ hf g).integrable_of_hasCompactSupport
      (hasCompactSupport_slice S hu hφ hf g hfs)
  have hJΦ : ∀ x, integralCLM (ν.comap (Subtype.val : S → Q)) eS (slice S hu hφ hf g x) =
      (∫ q, φ (u q * (g * x)) * e q ∂ν) * f x := fun x => by
    rw [integralCLM_apply]
    simp only [slice_apply, heS, ContinuousMap.coe_mk]
    rw [hsub fun q => φ (u q * g * x) * f x * e q, ← integral_mul_const]
    congr 1
    funext q
    simp only [mul_assoc]
    ring
  have hev : ∀ q : S, (∫ x, slice S hu hφ hf g x ∂μ) q = ∫ x, φ (u q * g * x) * f x ∂μ :=
    fun q => by
      rw [ContinuousMap.integral_apply hΦi q]
      simp only [slice_apply]
  calc ∫ q, (∫ x, φ (u q * g * x) * f x ∂μ) * e q ∂ν
      = ∫ q : S, (∫ x, slice S hu hφ hf g x ∂μ) q * eS q ∂(ν.comap (Subtype.val : S → Q)) := by
        rw [← hsub fun q => (∫ x, φ (u q * g * x) * f x ∂μ) * e q]
        exact integral_congr_ae (Filter.Eventually.of_forall fun q => by
          show (∫ x, φ (u ↑q * g * x) * f x ∂μ) * e ↑q = (∫ x, slice S hu hφ hf g x ∂μ) q * eS q
          rw [hev q]
          rfl)
    _ = integralCLM (ν.comap (Subtype.val : S → Q)) eS (∫ x, slice S hu hφ hf g x ∂μ) :=
        (integralCLM_apply _ _ _).symm
    _ = ∫ x, integralCLM (ν.comap (Subtype.val : S → Q)) eS (slice S hu hφ hf g x) ∂μ :=
        (ContinuousLinearMap.integral_comp_comm _ hΦi).symm
    _ = ∫ x, (∫ q, φ (u q * (g * x)) * e q ∂ν) * f x ∂μ := by simp only [hJΦ]

end Ws23.CASD.Interchange

namespace Ws23
namespace CASD

open Ws23.CASD.Interchange

variable {K : Type} [Field K] [NumberField K]

variable (K) in

theorem continuous_unipotentGL2_adele :
    Continuous fun q : AdeleRing (𝓞 K) K => (unipotentGL2 q : AdelicGL2 (𝓞 K) K) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun q : AdeleRing (𝓞 K) K => ((unipotentGL2 q : AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [unipotentGL2_coe]
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    all_goals obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    all_goals simp
    all_goals fun_prop
  · show Continuous fun q : AdeleRing (𝓞 K) K => ((unipotentGL2 q : AdelicGL2 (𝓞 K) K).inv :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [unipotentGL2]
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    all_goals obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    all_goals simp
    all_goals fun_prop

theorem whittakerCoefficient_rightConv (D : Set (AdelicGL2 (𝓞 K) K))
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : Continuous ψ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfs : HasCompactSupport f) (α : K) :
    whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ψ (rightConv K φ f) α =
      rightConv K (whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ψ φ α) f := by
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := borelSpace_adeleBorel (𝓞 K) K
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set ν : Measure (AdeleRing (𝓞 K) K) := ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K) with hν

  have hBtop : ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (measure_adelicBox_pos K (adelicAddHaar (𝓞 K) K)).ne'
  haveI : IsFiniteMeasure ((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact adelicAddHaar_adelicBox_lt_top K⟩
  haveI : IsFiniteMeasure ν := Measure.smul_finite _ hBtop
  obtain ⟨C, hC, hsubC⟩ := exists_isCompact_adelicBox_subset K
  have hνC : ∀ᵐ q ∂ν, q ∈ C := by
    rw [ae_iff]
    show (((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • (adelicAddHaar (𝓞 K) K).restrict (adelicBox K)) {q | q ∉ C} = 0
    have hCm : MeasurableSet {q : AdeleRing (𝓞 K) K | q ∉ C} := hC.isClosed.measurableSet.compl
    rw [Measure.smul_apply, Measure.restrict_apply hCm, smul_eq_mul]
    have he : {q : AdeleRing (𝓞 K) K | q ∉ C} ∩ adelicBox K = ∅ :=
      Set.eq_empty_of_forall_notMem fun q hq => hq.1 (hsubC hq.2)
    rw [he, measure_empty, mul_zero]
  funext g
  show ∫ q, rightConv K φ f (unipotentGL2 q * g) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * q)) ∂ν =
    ∫ x, (∫ q, φ (unipotentGL2 q * (g * x)) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * q)) ∂ν) * f x
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
  simp only [rightConv_apply]
  exact integral_integral_mul_comm (adelicGLHaar (Fin 2) (𝓞 K) K) ν hC hνC
    (continuous_unipotentGL2_adele K) hφ hf hfs (hψ.comp ((continuous_const.mul continuous_id).neg)) g

end Ws23.CASD

end

end BlockL1

section BlockL3

open NumberField NumberField.AdelicLevel NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm Matrix
open scoped Classical

noncomputable section

namespace Ws23
namespace CASD

variable {K : Type} [Field K] [NumberField K]

def detWt (g : AdelicGL2 (𝓞 K) K) : ℝ :=
  (∏ v : InfinitePlace K, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ))

theorem det_archFlowMatrix (d : ArchDir) (t : ℝ) :
    ((archFlowMatrix d t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  cases d
  · show ((splitTorusGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
    simp [splitTorusGL2, Matrix.det_fin_two_of, ← Real.exp_add]
  · show ((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
    simp [unipotentGL2, Matrix.det_fin_two_of]
  · show ((lowerUnipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
    simp [lowerUnipotentGL2, Matrix.det_fin_two_of]

theorem archComponent_glArch_archRealGLAt_self {w : InfinitePlace K} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archComponent K w (glArch (𝓞 K) K (archRealGLAt hw m)) = glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m := by
  unfold archRealGLAt adelicArchGLInclAt
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
    archComponent_archGLIncl_self]

theorem archComponent_glArch_archRealGLAt_of_ne {v w : InfinitePlace K} (hvw : v ≠ w) (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archComponent K v (glArch (𝓞 K) K (archRealGLAt hw m)) = 1 := by
  unfold archRealGLAt adelicArchGLInclAt
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
    archComponent_archGLIncl_of_ne K hvw]

omit [NumberField K] in
theorem norm_det_glEquivOfRingEquiv_symm {w : InfinitePlace K} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    ‖((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det‖ = |((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| := by
  have e : ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) =
      ((ringEquivRealOfIsReal hw).symm.toRingHom).mapMatrix ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := rfl
  rw [e, ← RingHom.map_det]
  have h := norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det)
  rw [RingEquiv.apply_symm_apply] at h
  rw [show ((ringEquivRealOfIsReal hw).symm.toRingHom) ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det =
    (ringEquivRealOfIsReal hw).symm ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det from rfl, ← h, Real.norm_eq_abs]

theorem archDetNorm_mul_archRealGLAt {w : InfinitePlace K} (hw : w.IsReal) (m : GL (Fin 2) ℝ) (v : InfinitePlace K)
    (g : AdelicGL2 (𝓞 K) K) :
    NumberField.AdelicVolume.archDetNorm v (g * archRealGLAt hw m) =
      NumberField.AdelicVolume.archDetNorm v g * (if v = w then |((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| else 1) := by
  unfold NumberField.AdelicVolume.archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  by_cases hvw : v = w
  · subst hvw
    rw [if_pos rfl, archComponent_glArch_archRealGLAt_self, norm_det_glEquivOfRingEquiv_symm]
  · rw [if_neg hvw, archComponent_glArch_archRealGLAt_of_ne hvw, Units.val_one, Matrix.det_one, norm_one]

theorem detWt_mul_archFlowAt {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ) (g : AdelicGL2 (𝓞 K) K) :
    detWt (g * archFlowAt hw d t) = detWt g := by
  unfold detWt archFlowAt
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [archDetNorm_mul_archRealGLAt, det_archFlowMatrix, abs_one]
  simp only [ite_self, mul_one]

theorem detWt_mul_archRealGLAt {w : InfinitePlace K} (hw : w.IsReal) (m : GL (Fin 2) ℝ) (g : AdelicGL2 (𝓞 K) K) :
    detWt (g * archRealGLAt hw m) =
      detWt g * (|((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| ^ w.mult) ^ (-(1 / 2 : ℝ)) := by
  unfold detWt
  have hsplit : (∏ v : InfinitePlace K, NumberField.AdelicVolume.archDetNorm v (g * archRealGLAt hw m) ^ v.mult) =
      (∏ v : InfinitePlace K, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) *
        |((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| ^ w.mult := by
    simp_rw [archDetNorm_mul_archRealGLAt, mul_pow]
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_eq_single w]
    · rw [if_pos rfl]
    · intro v _ hvw; simp only [if_neg hvw, one_pow]
    · intro h; exact absurd (Finset.mem_univ w) h
  rw [hsplit, Real.mul_rpow]
  · exact Finset.prod_nonneg fun v _ => pow_nonneg (NumberField.AdelicVolume.archDetNorm_pos v g).le _
  · exact pow_nonneg (abs_nonneg _) _

theorem continuous_detWt : Continuous (detWt (K := K)) := by
  unfold detWt
  refine Continuous.rpow_const (continuous_finsetProd _ fun v _ => (NumberField.AdelicVolume.continuous_archDetNorm v).pow _)
    fun g => Or.inl ?_
  exact (Finset.prod_pos fun v _ => pow_pos (NumberField.AdelicVolume.archDetNorm_pos v g) _).ne'

def fibreModel (Warch : AdelicGL2 (𝓞 K) K → ℂ) (z : ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun g => ((detWt g : ℝ) : ℂ) * Warch g * z

theorem continuous_fibreModel {Warch : AdelicGL2 (𝓞 K) K → ℂ} (hWc : Continuous Warch) (z : ℂ) :
    Continuous (fibreModel Warch z) :=
  ((Complex.continuous_ofReal.comp continuous_detWt).mul hWc).mul continuous_const

theorem archDerivAt_fibreModel {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (Warch : AdelicGL2 (𝓞 K) K → ℂ) (z : ℂ) :
    archDerivAt hw d (fibreModel Warch z) = fun g => ((detWt g : ℝ) : ℂ) * z * archDerivAt hw d Warch g := by
  funext g
  show deriv (fun t : ℝ => ((detWt (g * archFlowAt hw d t) : ℝ) : ℂ) * Warch (g * archFlowAt hw d t) * z) 0 =
    ((detWt g : ℝ) : ℂ) * z * deriv (fun t : ℝ => Warch (g * archFlowAt hw d t)) 0
  have e : (fun t : ℝ => ((detWt (g * archFlowAt hw d t) : ℝ) : ℂ) * Warch (g * archFlowAt hw d t) * z) =
      fun t => (((detWt g : ℝ) : ℂ) * z) * Warch (g * archFlowAt hw d t) := by
    funext t; rw [detWt_mul_archFlowAt]; ring
  rw [e, deriv_const_mul_field]

theorem archDerivAt_fibreModel_eq {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (W : AdelicGL2 (𝓞 K) K → ℂ) (z : ℂ) :
    archDerivAt hw d (fibreModel W z) = fibreModel (archDerivAt hw d W) z := by
  rw [archDerivAt_fibreModel]; funext g; simp only [fibreModel]; ring

theorem archCasimirAt_fibreModel {w : InfinitePlace K} (hw : w.IsReal) (Warch : AdelicGL2 (𝓞 K) K → ℂ) (z : ℂ)
    (lam : ℂ) (hWΩ : archCasimirAt hw Warch = lam • Warch) :
    archCasimirAt hw (fibreModel Warch z) = lam • fibreModel Warch z := by
  funext g
  have hΩ := congrFun hWΩ g
  simp only [archCasimirAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hΩ ⊢
  simp only [archDerivAt_fibreModel_eq, fibreModel]
  linear_combination (((detWt g : ℝ) : ℂ) * z) * hΩ

theorem contDiff_det_of : ContDiff ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e).det) := by
  have h : (fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e).det) = fun e => e 0 0 * e 1 1 - e 0 1 * e 1 0 := by
    funext e; simp [Matrix.det_fin_two]
  rw [h]
  have hp : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => e i j) := fun i j =>
    (contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin 2 → ℝ) i)
  exact ((hp 0 0).mul (hp 1 1)).sub ((hp 0 1).mul (hp 1 0))

theorem isArchSmoothAt_fibreModel {w : InfinitePlace K} (hw : w.IsReal) {Warch : AdelicGL2 (𝓞 K) K → ℂ}
    (hWs : IsArchSmoothAt hw Warch) (z : ℂ) : IsArchSmoothAt hw (fibreModel Warch z) := by
  intro g
  have hform : ∀ e ∈ {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0},
      ((detWt (g * archRealLiftAt hw e) : ℝ) : ℂ) =
        (((detWt g * (‖(Matrix.of e).det‖ ^ w.mult) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) := by
    intro e he
    rw [archRealLiftAt_of_det_ne_zero hw he, detWt_mul_archRealGLAt, Real.norm_eq_abs]
    rfl
  have hreal : ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => detWt g * (‖(Matrix.of e).det‖ ^ w.mult) ^ (-(1 / 2 : ℝ)))
      {e | (Matrix.of e).det ≠ 0} := by
    intro e he
    have hne : (Matrix.of e).det ≠ 0 := he
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => ‖(Matrix.of e).det‖) e :=
      (contDiffAt_norm ℝ hne).comp e contDiff_det_of.contDiffAt
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => ‖(Matrix.of e).det‖ ^ w.mult) e := h1.pow _
    have hne' : ‖(Matrix.of e).det‖ ^ w.mult ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hne)
    have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => (‖(Matrix.of e).det‖ ^ w.mult) ^ (-(1 / 2 : ℝ))) e :=
      h2.rpow_const_of_ne hne'
    exact (contDiffAt_const.mul h3).contDiffWithinAt
  have hdet : ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => ((detWt (g * archRealLiftAt hw e) : ℝ) : ℂ))
      {e | (Matrix.of e).det ≠ 0} := by
    refine (Complex.ofRealCLM.contDiff.comp_contDiffOn hreal).congr fun e he => ?_
    simp only [Function.comp_apply, Complex.ofRealCLM_apply]
    exact hform e he
  exact ((hdet.mul (hWs g)).mul contDiffOn_const)

end Ws23.CASD

end

end BlockL3

section BlockL4

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open LanglandsTunnell LanglandsTunnell.RealArchParam

noncomputable section

namespace Ws23
namespace CASD

variable (K : Type) [Field K] [NumberField K] (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsReal)
  (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφc : Continuous φ) (hφs : IsArchSmoothAt hw φ)
  (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d φ))
  (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' φ)))

include hφc hφs hD1 hD2

theorem archDerivAt_whittakerCoefficient (d : ArchDir) :
    archDerivAt hw d (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1) = whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw d φ) 1 := by
  funext g
  have h := ((AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt K D w hw φ hφc hφs
    hD1 hD2 g).1 d 1)
  simp only [one_mul, map_one, mul_one] at h
  exact h.deriv

theorem archDerivAt_archDerivAt_whittakerCoefficient (d d' : ArchDir) :
    archDerivAt hw d (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw d' φ) 1) = whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw d (archDerivAt hw d' φ)) 1 := by
  funext g
  have h := ((AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt K D w hw φ hφc hφs
    hD1 hD2 g).2.1 d d' 1)
  simp only [one_mul, map_one, mul_one] at h
  exact h.deriv

theorem archCasimirAt_whittakerCoefficient :
    archCasimirAt hw (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1) = whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archCasimirAt hw φ) 1 := by
  funext g
  have h3 := (AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt K D w hw φ hφc hφs
    hD1 hD2 g).2.2 1
  simp only [map_one, mul_one] at h3
  rw [h3, archCasimirAt, archDerivAt_whittakerCoefficient K D hw φ hφc hφs hD1 hD2 .H,
    archDerivAt_archDerivAt_whittakerCoefficient K D hw φ hφc hφs hD1 hD2 .H .H,
    archDerivAt_whittakerCoefficient K D hw φ hφc hφs hD1 hD2 .Fm,
    archDerivAt_archDerivAt_whittakerCoefficient K D hw φ hφc hφs hD1 hD2 .E .Fm]
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

omit hφs hD1 hD2 in

theorem continuous_whittakerCoefficient_std :
    Continuous (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1) :=
  AutomorphicForm.continuous_whittakerCoefficient K D _ _ (NumberField.StandardAddChar.stdAddChar K)
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).continuous φ hφc 1

end Ws23.CASD

end

end BlockL4

section CASD_new

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm.CuspidalConstituent AutomorphicForm.TranslateSpanOccurrence
open LanglandsTunnell LanglandsTunnell.RealArchParam
open scoped Classical

noncomputable section

namespace Ws23
namespace CASD

variable {K : Type} [Field K] [NumberField K]

theorem whittakerCoefficient_smul (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ) (α : K) :
    whittakerCoefficient K pins ψ (c • φ) α = c • whittakerCoefficient K pins ψ φ α := by
  funext g
  letI := pins.nS
  simp only [whittakerCoefficient, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact MeasureTheory.integral_const_mul _ _

theorem whittakerCoefficient_translate (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (k g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ (fun y => φ (y * k)) α g = whittakerCoefficient K pins ψ φ α (g * k) := by
  letI := pins.nS
  simp only [whittakerCoefficient, mul_assoc]

theorem whittakerCoefficient_mul_right_of_forall (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} {k : AdelicGL2 (𝓞 K) K} (h : ∀ y, φ (y * k) = φ y) (α : K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (g * k) = whittakerCoefficient K pins ψ φ α g := by
  rw [← whittakerCoefficient_translate]
  simp only [h]

theorem whittakerCoefficient_fun_zero (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (α : K) :
    whittakerCoefficient K pins ψ (0 : AdelicGL2 (𝓞 K) K → ℂ) α = 0 := by
  funext g
  exact whittakerCoefficient_zero K pins ψ α g

def finPart (g : AdelicGL2 (𝓞 K) K) : AdelicGL2 (𝓞 K) K := (adelicArchGLIncl K (glArch (𝓞 K) K g))⁻¹ * g

theorem glArch_finPart (g : AdelicGL2 (𝓞 K) K) : glArch (𝓞 K) K (finPart g) = 1 := by
  simp only [finPart, map_mul, map_inv, glArch_adelicArchGLIncl, inv_mul_cancel]

theorem glFin_finPart (g : AdelicGL2 (𝓞 K) K) : glFin (𝓞 K) K (finPart g) = glFin (𝓞 K) K g := by
  simp only [finPart, map_mul, map_inv, glFin_adelicArchGLIncl, inv_one, one_mul]

theorem glFin_archFlowAt {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    glFin (𝓞 K) K (archFlowAt hw d t) = 1 :=
  glFin_adelicArchGLIncl K _

theorem glFin_archRealGLAt {w : InfinitePlace K} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    glFin (𝓞 K) K (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl K _

theorem glArch_eq_one_of_mem_inf {N : Ideal (𝓞 K)} {k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) : glArch (𝓞 K) K k = 1 :=
  (Subgroup.mem_inf.1 hk).2

theorem glFin_mem_finiteLevelOne_of_mem_inf {N : Ideal (𝓞 K)} {k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) : glFin (𝓞 K) K k ∈ finiteLevelOne (𝓞 K) K N :=
  mem_levelOne_iff.1 (Subgroup.mem_inf.1 hk).1

theorem rightConv_congr_fibre (N : Ideal (𝓞 K)) {f Φ Ψ : AdelicGL2 (𝓞 K) K → ℂ} (g₀ : AdelicGL2 (𝓞 K) K)
    (hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K,
      glFin (𝓞 K) K a = 1 ∧ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * k)
    (h : ∀ g', glFin (𝓞 K) K g' = glFin (𝓞 K) K g₀ →
      ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, Φ (g' * k) = Ψ (g' * k))
    (g : AdelicGL2 (𝓞 K) K) (hg : glFin (𝓞 K) K g = glFin (𝓞 K) K g₀) :
    rightConv K Φ f g = rightConv K Ψ f g := by
  rw [rightConv_apply, rightConv_apply]
  congr 1
  funext x
  by_cases hx : f x = 0
  · simp only [hx, mul_zero]
  · obtain ⟨a, k, ha, hk, rfl⟩ := hfs x hx
    rw [← mul_assoc, h (g * a) (by rw [map_mul, ha, mul_one, hg]) k hk]

theorem archDerivAt_congr_fibre {w : InfinitePlace K} (hw : w.IsReal) {Φ Ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (g₀ : AdelicGL2 (𝓞 K) K) (h : ∀ g, glFin (𝓞 K) K g = glFin (𝓞 K) K g₀ → Φ g = Ψ g) (d : ArchDir) :
    ∀ g, glFin (𝓞 K) K g = glFin (𝓞 K) K g₀ → archDerivAt hw d Φ g = archDerivAt hw d Ψ g := by
  intro g hg
  unfold archDerivAt
  congr 1
  funext t
  exact h _ (by rw [map_mul, glFin_archFlowAt, mul_one, hg])

theorem archCasimirAt_congr_fibre {w : InfinitePlace K} (hw : w.IsReal) {Φ Ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (g₀ : AdelicGL2 (𝓞 K) K) (h : ∀ g, glFin (𝓞 K) K g = glFin (𝓞 K) K g₀ → Φ g = Ψ g)
    (g : AdelicGL2 (𝓞 K) K) (hg : glFin (𝓞 K) K g = glFin (𝓞 K) K g₀) :
    archCasimirAt hw Φ g = archCasimirAt hw Ψ g := by
  have hH := archDerivAt_congr_fibre hw g₀ h .H
  have hFm := archDerivAt_congr_fibre hw g₀ h .Fm
  have hHH := archDerivAt_congr_fibre hw g₀ hH .H
  have hEF := archDerivAt_congr_fibre hw g₀ hFm .E
  simp only [archCasimirAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hHH g hg, hH g hg, hEF g hg]

theorem detWt_mul_of_glArch_eq_one {k : AdelicGL2 (𝓞 K) K} (hk : glArch (𝓞 K) K k = 1) (g : AdelicGL2 (𝓞 K) K) :
    detWt (g * k) = detWt g := by
  simp only [detWt, NumberField.AdelicVolume.archDetNorm, map_mul, hk, mul_one]

theorem fibreModel_mul_of_glArch_eq_one {Warch : AdelicGL2 (𝓞 K) K → ℂ}
    (hWfin : ∀ g k : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K k = 1 → Warch (g * k) = Warch g) (z : ℂ)
    {k : AdelicGL2 (𝓞 K) K} (hk : glArch (𝓞 K) K k = 1) (g : AdelicGL2 (𝓞 K) K) :
    fibreModel Warch z (g * k) = fibreModel Warch z g := by
  simp only [fibreModel, detWt_mul_of_glArch_eq_one hk, hWfin g k hk]

def fibreNbhd (N : Ideal (𝓞 K)) (g₀ : AdelicGL2 (𝓞 K) K) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | (glFin (𝓞 K) K g₀)⁻¹ * glFin (𝓞 K) K g ∈ finiteLevelOne (𝓞 K) K N}

theorem isClopen_fibreNbhd {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) (g₀ : AdelicGL2 (𝓞 K) K) : IsClopen (fibreNbhd N g₀) :=
  ⟨(isClosed_finiteLevelOne (𝓞 K) K (N := N)).preimage (continuous_const.mul (continuous_glFin (𝓞 K) K)),
   (isOpen_finiteLevelOne (𝓞 K) K hN).preimage (continuous_const.mul (continuous_glFin (𝓞 K) K))⟩

theorem mem_fibreNbhd_iff {N : Ideal (𝓞 K)} {g₀ g : AdelicGL2 (𝓞 K) K} :
    g ∈ fibreNbhd N g₀ ↔ (glFin (𝓞 K) K g₀)⁻¹ * glFin (𝓞 K) K g ∈ finiteLevelOne (𝓞 K) K N := Iff.rfl

theorem mem_fibreNbhd_of_glFin_eq {N : Ideal (𝓞 K)} {g₀ g : AdelicGL2 (𝓞 K) K} (hg : glFin (𝓞 K) K g = glFin (𝓞 K) K g₀) :
    g ∈ fibreNbhd N g₀ := by
  rw [mem_fibreNbhd_iff, hg, inv_mul_cancel]
  exact Subgroup.one_mem _

theorem mem_fibreNbhd_mul_iff {N : Ideal (𝓞 K)} {g₀ g k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) : g * k ∈ fibreNbhd N g₀ ↔ g ∈ fibreNbhd N g₀ := by
  rw [mem_fibreNbhd_iff, mem_fibreNbhd_iff, map_mul, ← mul_assoc]
  exact Subgroup.mul_mem_cancel_right _ (glFin_mem_finiteLevelOne_of_mem_inf hk)

theorem mem_fibreNbhd_congr {N : Ideal (𝓞 K)} {g₀ g g' : AdelicGL2 (𝓞 K) K} (hgg : glFin (𝓞 K) K g = glFin (𝓞 K) K g') :
    g ∈ fibreNbhd N g₀ ↔ g' ∈ fibreNbhd N g₀ := by
  rw [mem_fibreNbhd_iff, mem_fibreNbhd_iff, hgg]

theorem rightConv_mul_right (φ f : AdelicGL2 (𝓞 K) K → ℂ) (k g : AdelicGL2 (𝓞 K) K) :
    rightConv K φ f (g * k) = rightConv K φ (fun y => f (k⁻¹ * y)) g := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  rw [rightConv_apply, rightConv_apply]
  have key : (fun x => φ (g * k * x) * f x) = fun x => (fun y => φ (g * y) * f (k⁻¹ * y)) (k * x) := by
    funext x
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [key]
  exact MeasureTheory.integral_mul_left_eq_self (fun y => φ (g * y) * f (k⁻¹ * y)) k

theorem exists_seed (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (W : AdelicGL2 (𝓞 K) K → ℂ) (hWc : Continuous W)
    (hWU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, W (g * k) = W g)
    (g₀ g₁ : AdelicGL2 (𝓞 K) K) (hg₁ : glFin (𝓞 K) K g₁ = glFin (𝓞 K) K g₀) (hne : W g₁ ≠ 0) :
    ∃ f₀ : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K f₀ ∧
      (∀ x, f₀ x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K,
        glFin (𝓞 K) K a = 1 ∧ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * k) ∧
      (∃ y, f₀ y ≠ 0) ∧
      ∃ g₂ : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g₂ = glFin (𝓞 K) K g₀ ∧ rightConv K W f₀ g₂ ≠ 0 := by
  set S : Set (AdelicGL2 (𝓞 K) K) := fibreNbhd N g₀ with hS
  set ψ₁ : AdelicGL2 (𝓞 K) K → ℂ := S.indicator W with hψ₁
  have hψc : Continuous ψ₁ := (isClopen_fibreNbhd hN g₀).continuous_indicator hWc
  have hψU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψ₁ (g * k) = ψ₁ g := by
    intro g k hk
    by_cases hg : g ∈ S
    · rw [hψ₁, Set.indicator_of_mem hg, Set.indicator_of_mem ((mem_fibreNbhd_mul_iff hk).2 hg), hWU g k hk]
    · rw [hψ₁, Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg ((mem_fibreNbhd_mul_iff hk).1 h))]
  have hψ1 : ψ₁ g₁ ≠ 0 := by
    rw [hψ₁, Set.indicator_of_mem (mem_fibreNbhd_of_glFin_eq hg₁)]
    exact hne
  obtain ⟨f₀, hf₀, hlinv, hsupp, g₂, hg₂⟩ :=
    AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant K N hN ψ₁ hψc ⟨g₁, hψ1⟩ hψU

  have hg₂S : g₂ ∈ S := by
    by_contra hS'
    apply hg₂
    rw [rightConv_apply]
    have h0 : (fun x => ψ₁ (g₂ * x) * f₀ x) = fun _ => 0 := by
      funext x
      by_cases hx : f₀ x = 0
      · rw [hx, mul_zero]
      · obtain ⟨a, k, ha, hk, rfl⟩ := hsupp x hx
        have hnot : g₂ * (a * k) ∉ S := fun hmem => hS' <| by
          rw [← mul_assoc, mem_fibreNbhd_mul_iff hk] at hmem
          exact (mem_fibreNbhd_congr (by rw [map_mul, ha, mul_one])).1 hmem
        rw [hψ₁, Set.indicator_of_notMem hnot, zero_mul]
    rw [h0, integral_const, smul_zero]
  have hne0 : ∃ y, f₀ y ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hg₂
    have : f₀ = fun _ => 0 := funext hall
    rw [this, rightConv_zero_right]

  set k₀ : AdelicGL2 (𝓞 K) K := (finPart g₀)⁻¹ * finPart g₂ with hk₀
  have hk₀A : glArch (𝓞 K) K k₀ = 1 := by
    rw [hk₀, map_mul, map_inv, glArch_finPart, glArch_finPart, inv_one, one_mul]
  have hk₀F : glFin (𝓞 K) K k₀ = (glFin (𝓞 K) K g₀)⁻¹ * glFin (𝓞 K) K g₂ := by
    rw [hk₀, map_mul, map_inv, glFin_finPart, glFin_finPart]
  have hk₀U : k₀ ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K :=
    Subgroup.mem_inf.2 ⟨mem_levelOne_iff.2 (hk₀F ▸ hg₂S), hk₀A⟩
  refine ⟨f₀, hf₀, hsupp, hne0, g₂ * k₀⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, hk₀F, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  · have hfib : glFin (𝓞 K) K (g₂ * k₀⁻¹) = glFin (𝓞 K) K g₀ := by
      rw [map_mul, map_inv, hk₀F, mul_inv_rev, inv_inv, mul_inv_cancel_left]
    rw [rightConv_congr_fibre N g₀ hsupp (Φ := W) (Ψ := ψ₁) (fun g' hg' k hk => ?_) _ hfib]
    · rw [rightConv_mul_right, inv_inv]
      have e : (fun y => f₀ (k₀ * y)) = f₀ := funext fun y => hlinv k₀ hk₀U y
      rw [e]
      exact hg₂
    · rw [hψ₁, Set.indicator_of_mem ((mem_fibreNbhd_mul_iff hk).2 (mem_fibreNbhd_of_glFin_eq hg'))]

theorem exists_of_mem_iSup₂ {M : Type*} [AddCommGroup M] [Module ℂ M] {p : Submodule ℂ M → Prop} {x : M}
    (hx : x ∈ ⨆ (V : Submodule ℂ M) (_ : p V), V) (hx0 : x ≠ 0)
    (huniq : ∀ V₁ V₂, p V₁ → p V₂ → V₁ = V₂) : ∃ V, p V ∧ x ∈ V := by
  by_cases h : ∃ V, p V
  · obtain ⟨V₀, hV₀⟩ := h
    refine ⟨V₀, hV₀, ?_⟩
    have hle : (⨆ (V : Submodule ℂ M) (_ : p V), V) ≤ V₀ := iSup₂_le fun V hV => (huniq V V₀ hV hV₀).le
    exact hle hx
  · push Not at h
    have hbot : (⨆ (V : Submodule ℂ M) (_ : p V), V) = ⊥ := by
      simp only [iSup_eq_bot]
      exact fun V hV => absurd hV (h V)
    rw [hbot, Submodule.mem_bot] at hx
    exact absurd hx hx0

variable {F : Type} [Field F] [NumberField F]

theorem isIsotypicCuspFormAt_congr {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 F)}
    {S : Finset (HeightOneSpectrum (𝓞 F))} {Ψ Ψ' : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hab : ∀ v, v ∉ S → Ψ.a v = Ψ'.a v ∧ Ψ.b v = Ψ'.b v) (h : IsIsotypicCuspFormAt F pins ξ N S Ψ φ) :
    IsIsotypicCuspFormAt F pins ξ N S Ψ' φ where
  smoothCusp := h.smoothCusp
  continuous := h.continuous
  level_invariant := h.level_invariant
  hecke_eigen := fun v hv => (hab v hv).1 ▸ h.hecke_eigen v hv
  central_eigen := fun v hv g => by
    rw [h.central_eigen v hv g, HeckeEigensystem.toRawCentral_b, HeckeEigensystem.toRawCentral_b, (hab v hv).2]

theorem mem_of_sameConstituent (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) (Θ : HeckeEigensystem F ℂ)
    (Θ₀ : HeckeEigensystem F ℂ) (hΘ₀ : Θ₀.AgreesAwayFromFinite Θ)
    (R₀ : SmoothCuspRealizationAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Θ₀.toRawCentral) (hR₀ : Continuous R₀.toFun)
    (V₀ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV₀ : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R₀.centralChar V₀)
    (φ₀ : AdelicGL2 (𝓞 F) F → ℂ) (hφ₀V : φ₀ ∈ V₀) (hφ₀0 : φ₀ ≠ 0) (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (hφ₀ : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R₀.centralChar Θ₀.level S₀ Θ₀ φ₀)
    (Θ' : HeckeEigensystem F ℂ) (hΘ' : Θ'.AgreesAwayFromFinite Θ)
    (R' : SmoothCuspRealizationAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Θ'.toRawCentral) (hR' : Continuous R'.toFun)
    (S' : Finset (HeightOneSpectrum (𝓞 F))) (tys' : ArchTypeFamily F) (φ' : AdelicGL2 (𝓞 F) F → ℂ) (hφ'0 : φ' ≠ 0)
    (hφ'iso : φ' ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R'.centralChar Θ'.level S' Θ')
    (hφ'cut : φ' ∈ archCutSubmodule F tys') :
    φ' ∈ V₀ := by
  classical

  have hag : Θ'.AgreesAwayFromFinite Θ₀ := agrees_trans hΘ' (agrees_symm hΘ₀)
  have hξ : R'.centralChar = R₀.centralChar :=
    AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite F _ Θ' Θ₀ hag R' hR' R₀ hR₀
  have hφ' : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R₀.centralChar Θ'.level S' Θ' φ' := by
    rw [← hξ]
    exact AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule F _ _ _ R'.centralChar Θ'.level S' Θ' φ' hφ'iso hφ'0

  obtain ⟨Sag, hSag⟩ := hag
  set Nst : Ideal (𝓞 F) := Θ₀.level * Θ'.level with hNst
  have hN0 : Nst ≠ ⊥ := fun h => (Ideal.mul_eq_bot.1 h).elim Θ₀.level_ne_bot Θ'.level_ne_bot
  set Sst : Finset (HeightOneSpectrum (𝓞 F)) := S₀ ∪ S' ∪ Sag ∪ (Ideal.finite_factors hN0).toFinset with hSst
  have hS₀ : S₀ ⊆ Sst := fun v hv => by simp [hSst, hv]
  have hS' : S' ⊆ Sst := fun v hv => by simp [hSst, hv]
  have hSag' : ∀ v, v ∉ Sst → v ∉ Sag := fun v hv h => hv (by simp [hSst, h])
  have hdiv : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sst → ¬ v.asIdeal ∣ Nst := fun v hv h =>
    hv (by simp [hSst, Set.Finite.mem_toFinset, h])
  have h₀ : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R₀.centralChar Nst Sst Θ₀ φ₀ :=
    AutomorphicForm.IsIsotypicCuspFormAt.of_le_of_subset F _ R₀.centralChar Ideal.mul_le_left hN0 hS₀ hdiv Θ₀ hφ₀
  have h₁ : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R₀.centralChar Nst Sst Θ₀ φ' :=
    isIsotypicCuspFormAt_congr (fun v hv => hSag v (hSag' v hv))
      (AutomorphicForm.IsIsotypicCuspFormAt.of_le_of_subset F _ R₀.centralChar Ideal.mul_le_right hN0 hS' hdiv Θ' hφ')

  have hsup := AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent F c u d₁ d₂ T hd hcov R₀.centralChar Nst Sst tys' Θ₀
    (Submodule.mem_inf.2 ⟨h₁.mem_isotypicCuspSubmodule, hφ'cut⟩)
  obtain ⟨V₁, ⟨hV₁, hm₁, -⟩, hφ'V₁⟩ := exists_of_mem_iSup₂ hsup hφ'0 fun V₁ V₂ h₁' h₂' =>
    AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre F c u d₁ d₂ T hd hcov R₀.centralChar Nst Sst Θ₀ V₁ V₂ h₁'.1 h₂'.1 h₁'.2.1 h₂'.2.1
  have hm₀ : CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R₀.centralChar Nst Sst Θ₀ V₀ := ⟨φ₀, hφ₀V, hφ₀0, h₀⟩
  have hVV : V₁ = V₀ :=
    AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre F c u d₁ d₂ T hd hcov R₀.centralChar Nst Sst Θ₀ V₁ V₀ hV₁ hV₀ hm₁ hm₀
  exact hVV ▸ hφ'V₁

theorem casdPos (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ) (w : InfinitePlace K) (hw : w.IsReal) (P : RealArchParam)
    (Warch : AdelicGL2 (𝓞 K) K → ℂ) (hWc : Continuous Warch)
    (hWfin : ∀ (g k : AdelicGL2 (𝓞 K) K), glArch (𝓞 K) K k = 1 → Warch (g * k) = Warch g)
    (hWs : IsArchSmoothAt hw Warch) (hWΩ : archCasimirAt hw Warch = (laplaceEigenvalue P) • Warch)
    (D' : Set (AdelicGL2 (𝓞 K) K))
    (hWF : ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) Θ
        (fun φ => ∃ g₀ : AdelicGL2 (𝓞 K) K,
          (∃ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = glFin (𝓞 K) K g₀ ∧
            whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) φ 1 g ≠ 0) ∧
          ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = glFin (𝓞 K) K g₀ →
            whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) φ 1 g = (((∏ v : InfinitePlace K, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Warch g * z)) :
    ∃ n : ℤ, ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ K w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (laplaceEigenvalue P) • φ) := by

  have hex : ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) Θ (fun _ => True) := hWF.mono fun _ _ => trivial
  obtain ⟨n₀, Θ₀, hΘ₀, R₀, hR₀, hn₀⟩ :=
    AutomorphicForm.exists_archOccursInClassOf_archWeightChar_of_coversModCentre_of_pos K c u d₁ d₂ T hd hc hd₁ hcov Θ hex w hw
  obtain ⟨S₀, tys₀, f₀', -, -, -, hne₀, hiso₀, hcut₀, htyp₀, hsm₀, -⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal
      K c u d₁ d₂ T hc hd₁ hd hcov Θ₀ R₀ hR₀ w hw n₀ hn₀
  have hform₀ := AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule K _ _ _ R₀.centralChar Θ₀.level S₀ Θ₀ _ hiso₀ hne₀
  have hsup₀ := AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent K c u d₁ d₂ T hd hcov
    R₀.centralChar Θ₀.level S₀ tys₀ Θ₀ (Submodule.mem_inf.2 ⟨hiso₀, hcut₀⟩)
  obtain ⟨V₀, ⟨hV₀, -, -⟩, hφ₀V⟩ := exists_of_mem_iSup₂ hsup₀ hne₀ fun V₁ V₂ h₁ h₂ =>
    AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre K c u d₁ d₂ T hd hcov R₀.centralChar
      Θ₀.level S₀ Θ₀ V₁ V₂ h₁.1 h₂.1 h₁.2.1 h₂.2.1
  have hX : V₀ ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) Θ₀.level ⊓ archCutSubmodule K tys₀ ≠ ⊥ := by
    intro hbot
    have hmem : rightConv K R₀.toFun f₀' ∈
        V₀ ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) Θ₀.level ⊓ archCutSubmodule K tys₀ :=
      Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hφ₀V, hform₀.level_invariant⟩, hcut₀⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hne₀ hmem
  obtain ⟨lam₁, hlamV⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent K c u d₁ d₂ T
      hc hd₁ hd hcov R₀.centralChar V₀ hV₀ Θ₀.level Θ₀.level_ne_bot tys₀ hX w hw
  have key := mem_of_sameConstituent c u d₁ d₂ T hd hcov Θ Θ₀ hΘ₀ R₀ hR₀ V₀ hV₀ _ hφ₀V hne₀ S₀ hform₀

  obtain ⟨Θ', hΘ', R, hR, g₀, ⟨g₁, hg₁, hWne⟩, z, hWz⟩ := hWF
  have hψK : Continuous (NumberField.StandardAddChar.stdAddChar K) := (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).continuous
  have hWcR : Continuous (whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) R.toFun 1) :=
    continuous_whittakerCoefficient_std K D' R.toFun hR
  have hWU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K Θ'.level ⊓ finiteAdelicGL2Subgroup K,
      whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) R.toFun 1 (g * k) =
        whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) R.toFun 1 g := fun g k hk =>
    whittakerCoefficient_mul_right_of_forall _ _ (fun y => R.level_invariant y k hk) 1 g

  obtain ⟨f₀, hf₀, hsupp, hne', g₂, hg₂, hg₂ne⟩ :=
    exists_seed Θ'.level Θ'.level_ne_bot _ hWcR hWU g₀ g₁ hg₁ hWne
  obtain ⟨fa₀, ff, hfa₀, hff, hf₀eq, hisoAll⟩ :=
    G1PrimeRat.ConvHalf.exists_finFactor_forall_isIsotypicCuspFormAt_rightConv K c u d₁ d₂ T hd hc hd₁ hcov Θ' R hR f₀ hf₀ hne' hsupp
  have hg₂ne' : rightConv K (whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) R.toFun 1)
      (fun g => fa₀ (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) g₂ ≠ 0 := by
    have e : (fun g => fa₀ (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) = f₀ := funext fun g => (hf₀eq g).symm
    rw [e]
    exact hg₂ne
  have hηpos : 0 < ‖rightConv K (whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) R.toFun 1)
      (fun g => fa₀ (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) g₂‖ / 2 := half_pos (norm_pos_iff.2 hg₂ne')
  obtain ⟨tys, fa, hfa, hbifin, -, -, hclose⟩ :=
    AutomorphicForm.exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact K _ hWcR fa₀ hfa₀ ff hff g₂
      hg₂ne' {g₂} isCompact_singleton _ hηpos

  have hfact : IsFactorizableTestFn K (fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) :=
    ⟨fa, ff, hfa, hff, fun _ => rfl⟩
  have hfs := G1PrimeRat.ConvHalf.support_shape_of_finFactor K Θ'.level f₀ fa₀ ff hf₀eq hne' hsupp
    (fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) fa (fun _ => rfl)
  have hfne : rightConv K (whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) R.toFun 1)
      (fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) g₂ ≠ 0 := by
    intro h0
    have hle := hclose g₂ (Set.mem_singleton g₂)
    rw [h0, zero_sub, norm_neg] at hle
    linarith [norm_pos_iff.2 hg₂ne']
  have hiso := hisoAll fa hfa
  have hfc := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ hfact
  have hcut : rightConv K R.toFun (fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) ∈ archCutSubmodule K tys :=
    AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite K tys R.toFun hR _ hfact
      (IsArchBiFinite.of_factorization K (fun _ => rfl) hbifin)

  have hWx₀ : whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
      (rightConv K R.toFun (fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))) 1 =
      rightConv K (whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) R.toFun 1)
        (fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) :=
    whittakerCoefficient_rightConv D' (NumberField.StandardAddChar.stdAddChar K) hψK R.toFun hR _ hfc.1 hfc.2 1
  have hx₀ne : rightConv K R.toFun (fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) ≠ 0 := by
    intro h0
    apply hfne
    rw [← hWx₀, h0, whittakerCoefficient_fun_zero]
    rfl
  have hx₀V := key Θ' hΘ' R hR R.exceptionalSet tys _ hx₀ne hiso.mem_isotypicCuspSubmodule hcut
  obtain ⟨hxsm, hxD1, hxD2, hxΩ⟩ := hlamV _ hx₀V

  have hΩW : archCasimirAt hw (whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
      (rightConv K R.toFun (fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))) 1) =
      lam₁ • whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
        (rightConv K R.toFun (fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))) 1 := by
    rw [archCasimirAt_whittakerCoefficient K D' hw _ hiso.continuous hxsm hxD1 hxD2, hxΩ, whittakerCoefficient_smul]

  have hφtc : Continuous (fibreModel Warch z) := continuous_fibreModel hWc z
  have hφts : IsArchSmoothAt hw (fibreModel Warch z) := isArchSmoothAt_fibreModel hw hWs z
  have hφtΩ : archCasimirAt hw (fibreModel Warch z) = (laplaceEigenvalue P) • fibreModel Warch z :=
    archCasimirAt_fibreModel hw Warch z _ hWΩ
  obtain ⟨-, hconvΩ⟩ :=
    AutomorphicForm.archCasimirAt_rightConv_eq_smul_of_archCasimirAt_eq_smul_of_isArchSmoothAt_of_isFactorizableTestFn K w hw
      (fibreModel Warch z) hφtc hφts (laplaceEigenvalue P) hφtΩ _ hfact
  have hfibre : ∀ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = glFin (𝓞 K) K g₀ →
      whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
        (rightConv K R.toFun (fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))) 1 g =
      rightConv K (fibreModel Warch z) (fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) g := by
    intro g hg
    rw [hWx₀]
    refine rightConv_congr_fibre Θ'.level g₀ hfs (fun g' hg' k hk => ?_) g hg
    rw [hWU g' k hk, fibreModel_mul_of_glArch_eq_one hWfin z (glArch_eq_one_of_mem_inf hk), hWz g' hg']
    rfl
  have h1 := congrFun hΩW g₂
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  have h2 : archCasimirAt hw (whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
      (rightConv K R.toFun (fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))) 1) g₂ =
      (laplaceEigenvalue P) * whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
        (rightConv K R.toFun (fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))) 1 g₂ := by
    rw [archCasimirAt_congr_fibre hw g₀ hfibre g₂ hg₂, hconvΩ, Pi.smul_apply, smul_eq_mul, ← hfibre g₂ hg₂]
  have hval : whittakerCoefficient K (productionPinsOf K D' (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
      (rightConv K R.toFun (fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))) 1 g₂ ≠ 0 := by
    rw [hWx₀]
    exact hfne
  have hlam : lam₁ = laplaceEigenvalue P := mul_right_cancel₀ hval (h1.symm.trans h2)

  have hΩ₀ := (hlamV _ hφ₀V).2.2.2
  rw [hlam] at hΩ₀
  exact ⟨n₀, Θ₀, hΘ₀, hform₀.toRealization hne₀, hform₀.continuous, htyp₀, hsm₀, hΩ₀⟩

theorem main (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ) (w : InfinitePlace K) (hw : w.IsReal) (P : RealArchParam)
    (Warch : AdelicGL2 (𝓞 K) K → ℂ) (hWc : Continuous Warch)
    (hWfin : ∀ (g k : AdelicGL2 (𝓞 K) K), glArch (𝓞 K) K k = 1 → Warch (g * k) = Warch g)
    (hWs : IsArchSmoothAt hw Warch) (hWΩ : archCasimirAt hw Warch = (laplaceEigenvalue P) • Warch)
    (hWF : ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) Θ
        (fun φ => ∃ g₀ : AdelicGL2 (𝓞 K) K,
          (∃ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = glFin (𝓞 K) K g₀ ∧
            whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) φ 1 g ≠ 0) ∧
          ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = glFin (𝓞 K) K g₀ →
            whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) φ 1 g = (((∏ v : InfinitePlace K, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Warch g * z)) :
    ∃ n : ℤ, ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ K w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (laplaceEigenvalue P) • φ) := by
  by_cases hc : 0 < c
  swap
  · exfalso
    obtain ⟨Θ', -, hreal⟩ := hWF.isArithGenuineCuspRealizable
    exact AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre K c u d₁ d₂ T (not_lt.1 hc) hd
      hcov Θ' hreal
  have hd₂ : 0 < d₂ := by
    by_contra hle
    push Not at hle
    obtain ⟨γ, zc, hmem⟩ := hcov 1
    simp only [Set.mem_iUnion, Set.mem_image] at hmem
    obtain ⟨x, -, y, hy, -⟩ := hmem
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
    have h4 := (mem_centreCutSiegelSet_iff.mp hy).2.2.2 w₀
    linarith [NumberField.AdelicVolume.archDetNorm_pos w₀ y, h4.2]
  have hdp0 : 0 < max d₁ (d₂ / 2) := lt_max_of_lt_right (by linarith)
  have hdp2 : max d₁ (d₂ / 2) < d₂ := max_lt hd (by linarith)
  have hex : ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) Θ (fun _ => True) := hWF.mono fun _ _ => trivial
  obtain ⟨hcov', hiff⟩ := AutomorphicForm.coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le K c u d₁ d₂
    (max d₁ (d₂ / 2)) T hc hdp0 hdp2 (le_max_left _ _) hcov Θ hex
  obtain ⟨n, h⟩ := casdPos c u (max d₁ (d₂ / 2)) d₂ T hc hdp0 hdp2 hcov' Θ w hw P Warch hWc hWfin hWs hWΩ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
    ((hiff _).1 hWF)
  exact ⟨n, (hiff _).2 h⟩

end Ws23.CASD

end

end CASD_new

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion LanglandsTunnell LanglandsTunnell.RealArchParam IsDedekindDomain in

theorem solution
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ) (w : InfinitePlace K) (hw : w.IsReal) (P : RealArchParam)
    (Warch : AdelicGL2 (𝓞 K) K → ℂ) (hWc : Continuous Warch)
    (hWfin : ∀ (g k : AdelicGL2 (𝓞 K) K), glArch (𝓞 K) K k = 1 → Warch (g * k) = Warch g)
    (hWs : IsArchSmoothAt hw Warch) (hWΩ : archCasimirAt hw Warch = (laplaceEigenvalue P) • Warch)
    (hWF : ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) Θ
        (fun φ => ∃ g₀ : AdelicGL2 (𝓞 K) K,
          (∃ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = glFin (𝓞 K) K g₀ ∧
            whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) φ 1 g ≠ 0) ∧
          ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = glFin (𝓞 K) K g₀ →
            whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) φ 1 g =
              (((∏ v : InfinitePlace K, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                Warch g * z)) :
    ∃ n : ℤ,
      ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ K w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
          IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (laplaceEigenvalue P) • φ) :=
  Ws23.CASD.main K c u d₁ d₂ T hd hcov Θ w hw P Warch hWc hWfin hWs hWΩ hWF

end S_LanglandsTunnell_exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq
end P2MW
export P2MW.S_LanglandsTunnell_exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq (solution)
