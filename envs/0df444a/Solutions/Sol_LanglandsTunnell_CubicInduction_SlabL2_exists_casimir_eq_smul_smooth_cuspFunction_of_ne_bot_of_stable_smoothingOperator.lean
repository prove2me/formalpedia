-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/675049c5-5387-5e4f-af6e-2d7d96d239d5

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_SpectralOperators3
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isCompactOperator_cuspidalSubspace_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_isSmoothingKernel_isCompactOperator_isCuspLift3_apply_ne_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_toL2_eq_zero_of_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_isSmoothingKernel_star_inv_and_inner_toL2_smoothingOperator_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_archDeriv_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_archDeriv_and_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one"
p2m_attr_erase "simp" "AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.CubicInduction.fnTwist3_apply LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply"

set_option autoImplicit false

section ClassActionBlock

noncomputable section

open Submodule
open scoped InnerProductSpace

namespace DenseUnitaryExtension

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {C : Type*} [AddCommGroup C] [Module ℂ C]
variable {Hc : Type*} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]

private structure IsDenseIsometricAction (T : C →ₗ[ℂ] Hc) (D : Submodule ℂ Hc) (a : G →* Module.End ℂ C) : Prop where
  mem : ∀ c, T c ∈ D
  dense : (D : Set Hc) ⊆ closure (LinearMap.range T : Set Hc)
  norm_eq : ∀ g c, ‖T (a g c)‖ = ‖T c‖
  cont : ∀ c, Continuous fun g => T (a g c)

variable {T : C →ₗ[ℂ] Hc} {D : Submodule ℂ Hc} {a : G →* Module.End ℂ C}

namespace IsDenseIsometricAction

private def gen (h : IsDenseIsometricAction T D a) : C →ₗ[ℂ] D :=
  LinearMap.codRestrict D T h.mem

@[scoped simp]
private theorem coe_gen (h : IsDenseIsometricAction T D a) (c : C) : (h.gen c : Hc) = T c :=
  rfl

private theorem norm_gen (h : IsDenseIsometricAction T D a) (c : C) : ‖h.gen c‖ = ‖T c‖ :=
  rfl

private theorem denseRange_gen (h : IsDenseIsometricAction T D a) : DenseRange h.gen := by
  have h1 : (LinearMap.range T : Set Hc) ⊆ D := by
    rintro _ ⟨c, rfl⟩
    exact h.mem c
  have h2 : DenseRange (Set.inclusion h1) := (denseRange_inclusion_iff h1).2 h.dense
  have h3 : Function.Surjective fun c : C => (⟨T c, LinearMap.mem_range_self T c⟩ : LinearMap.range T) := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.1 hx
    exact ⟨c, rfl⟩
  have h4 : (h.gen : C → D) =
      Set.inclusion h1 ∘ fun c : C => (⟨T c, LinearMap.mem_range_self T c⟩ : LinearMap.range T) := by
    funext c
    rfl
  rw [h4]
  exact h2.comp h3.denseRange (continuous_inclusion h1)

private theorem norm_bound (h : IsDenseIsometricAction T D a) (g : G) (c : C) :
    ‖(h.gen ∘ₗ a g) c‖ ≤ 1 * ‖h.gen c‖ := by
  rw [one_mul, LinearMap.comp_apply, norm_gen, norm_gen, h.norm_eq]

private theorem norm_bound' (h : IsDenseIsometricAction T D a) (g : G) :
    ∃ M : ℝ, ∀ c : C, ‖(h.gen ∘ₗ a g) c‖ ≤ M * ‖h.gen c‖ :=
  ⟨1, h.norm_bound g⟩

variable [CompleteSpace D]

private def U (h : IsDenseIsometricAction T D a) (g : G) : D →L[ℂ] D :=
  (h.gen ∘ₗ a g).extendOfNorm h.gen

private theorem U_gen (h : IsDenseIsometricAction T D a) (g : G) (c : C) : h.U g (h.gen c) = h.gen (a g c) :=
  LinearMap.extendOfNorm_eq h.denseRange_gen (h.norm_bound' g) c

private theorem U_one (h : IsDenseIsometricAction T D a) : h.U 1 = ContinuousLinearMap.id ℂ D := by
  refine LinearMap.extendOfNorm_unique h.denseRange_gen 1 (h.norm_bound 1) _ ?_
  ext c
  rw [map_one]
  rfl

private theorem U_mul (h : IsDenseIsometricAction T D a) (g g' : G) : h.U (g * g') = (h.U g).comp (h.U g') := by
  refine LinearMap.extendOfNorm_unique h.denseRange_gen 1 (h.norm_bound (g * g')) _ ?_
  ext c
  show ((h.U g (h.U g' (h.gen c)) : D) : Hc) = ((h.gen ∘ₗ a (g * g')) c : Hc)
  rw [U_gen, U_gen, map_mul]
  rfl

private theorem U_inv_U (h : IsDenseIsometricAction T D a) (g : G) (x : D) : h.U g⁻¹ (h.U g x) = x := by
  rw [← ContinuousLinearMap.comp_apply, ← U_mul, inv_mul_cancel, U_one]
  rfl

private theorem U_U_inv (h : IsDenseIsometricAction T D a) (g : G) (x : D) : h.U g (h.U g⁻¹ x) = x := by
  simpa using h.U_inv_U g⁻¹ x

private theorem norm_U_le (h : IsDenseIsometricAction T D a) (g : G) (x : D) : ‖h.U g x‖ ≤ ‖x‖ := by
  have h__af := LinearMap.norm_extendOfNorm_apply_le h.denseRange_gen 1 (h.norm_bound g) x
  simp at h__af
  exact h__af

private theorem norm_U (h : IsDenseIsometricAction T D a) (g : G) (x : D) : ‖h.U g x‖ = ‖x‖ :=
  le_antisymm (h.norm_U_le g x) (by simpa [U_inv_U] using h.norm_U_le g⁻¹ (h.U g x))

private def isometry (h : IsDenseIsometricAction T D a) (g : G) : D →ₗᵢ[ℂ] D :=
  { (h.U g : D →ₗ[ℂ] D) with norm_map' := h.norm_U g }

private theorem inner_U_U (h : IsDenseIsometricAction T D a) (g : G) (x y : D) :
    ⟪h.U g x, h.U g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (h.isometry g).inner_map_map x y

private theorem adjoint_U (h : IsDenseIsometricAction T D a) (g : G) :
    ContinuousLinearMap.adjoint (h.U g) = h.U g⁻¹ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [← h.inner_U_U g (h.U g⁻¹ x) y, U_U_inv]

private def hom (h : IsDenseIsometricAction T D a) : G →* (D →L[ℂ] D) where
  toFun := h.U
  map_one' := h.U_one
  map_mul' g g' := by
    rw [ContinuousLinearMap.mul_def]
    exact h.U_mul g g'

private theorem hom_apply (h : IsDenseIsometricAction T D a) (g : G) : h.hom g = h.U g :=
  rfl

end IsDenseIsometricAction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction"

end DenseUnitaryExtension
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 IsCuspidalAlongP21 IsCuspidalAlongP12 WhittakerBlock.archDeriv WhittakerBlock.casimir1 WhittakerBlock.casimir2 WhittakerBlock.casimir3 exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace eq_zero_of_toL2_eq_zero_of_continuous WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate WhittakerBlock.casimir_archDeriv_and_comm"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open Matrix IsDedekindDomain NumberField AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

section Unipotent

private theorem upperUnipotent3_inv_coe' (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    (((upperUnipotent3 x y z)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] :=
  rfl

private theorem continuous_upperUnipotent3 :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (upperUnipotent3 p.1 p.2.1 p.2.2 : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_apply, upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    simp only [upperUnipotent3_inv_coe']
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_radicalP21_pair :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (radicalP21 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  show Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => upperUnipotent3 0 p.2 p.1
  exact continuous_upperUnipotent3.comp
    (f := fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => ((0 : AdeleRing (𝓞 ℚ) ℚ), p.2, p.1)) (by fun_prop)

private theorem continuous_radicalP12_pair :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (radicalP12 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  show Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => upperUnipotent3 p.1 0 p.2
  exact continuous_upperUnipotent3.comp
    (f := fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (p.1, (0 : AdeleRing (𝓞 ℚ) ℚ), p.2)) (by fun_prop)

end Unipotent
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension"

section Box

private scoped instance secondCountable_adeleRing : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdeleRing.secondCountableTopology ℚ

private abbrev boxMeasure : MeasureTheory.Measure (AdeleRing (𝓞 ℚ) ℚ) :=
  ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

private scoped instance isProbabilityMeasure_boxMeasure : MeasureTheory.IsProbabilityMeasure boxMeasure :=
  AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ

private theorem integrable_boxMeasure_of_continuous {f : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f) :
    MeasureTheory.Integrable f boxMeasure := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have h1 : MeasureTheory.IntegrableOn f C (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
    hf.continuousOn.integrableOn_compact hC
  have h2 : MeasureTheory.IntegrableOn f (AdelicBox.adelicBox ℚ) (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
    h1.mono_set hsub
  exact MeasureTheory.Integrable.smul_measure h2
    (ENNReal.inv_ne_top.mpr (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne')

private theorem continuous_integral_boxMeasure {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [LocallyCompactSpace X] {f : X → AdeleRing (𝓞 ℚ) ℚ → ℂ} (hf : Continuous (Function.uncurry f)) :
    Continuous fun x => ∫ y, f x y ∂boxMeasure := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := (hK.prod hC).exists_bound_of_continuousOn hf.continuousOn
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (MeasureTheory.integrable_const M) ?_
  · exact Filter.Eventually.of_forall fun x =>
      (hf.comp (f := fun y => (x, y)) (by fun_prop)).aestronglyMeasurable
  · refine Filter.mem_of_superset hKn fun x hx => ?_
    exact (ProbabilityTheory.ae_cond_mem (AdelicBox.measurableSet_adelicBox ℚ)).mono fun y hy =>
      hM (x, y) ⟨hx, hsub hy⟩
  · exact Filter.Eventually.of_forall fun y => (hf.comp (f := fun x => (x, y)) (by fun_prop)).continuousAt

private theorem integral2_boxMeasure_add {φ φ' : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hφ : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => φ p.1 p.2)
    (hφ' : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => φ' p.1 p.2) :
    (∫ x, ∫ y, (φ x y + φ' x y) ∂boxMeasure ∂boxMeasure) =
      (∫ x, ∫ y, φ x y ∂boxMeasure ∂boxMeasure) + ∫ x, ∫ y, φ' x y ∂boxMeasure ∂boxMeasure := by
  have hy : ∀ x, Continuous fun y => φ x y := fun x => hφ.comp (f := fun y => (x, y)) (by fun_prop)
  have hy' : ∀ x, Continuous fun y => φ' x y := fun x => hφ'.comp (f := fun y => (x, y)) (by fun_prop)
  have hx : Continuous fun x => ∫ y, φ x y ∂boxMeasure := continuous_integral_boxMeasure (f := φ) hφ
  have hx' : Continuous fun x => ∫ y, φ' x y ∂boxMeasure := continuous_integral_boxMeasure (f := φ') hφ'
  have hyadd : ∀ x, (∫ y, (φ x y + φ' x y) ∂boxMeasure) =
      (∫ y, φ x y ∂boxMeasure) + ∫ y, φ' x y ∂boxMeasure := fun x =>
    MeasureTheory.integral_add (integrable_boxMeasure_of_continuous (hy x))
      (integrable_boxMeasure_of_continuous (hy' x))
  simp_rw [hyadd]
  exact MeasureTheory.integral_add (integrable_boxMeasure_of_continuous hx) (integrable_boxMeasure_of_continuous hx')

end Box
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension"

section Pins

variable (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
  (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)

private abbrev prodPins : CarrierPins ℚ := productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)

variable {D U gen}

section Cuspidal

variable {F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}

private theorem isCuspidalAlongP21_prodPins_add (hF : Continuous F) (hF' : Continuous F')
    (h1 : IsCuspidalAlongP21 (prodPins D U gen) F) (h2 : IsCuspidalAlongP21 (prodPins D U gen) F') :
    IsCuspidalAlongP21 (prodPins D U gen) (F + F') := by
  intro g
  have hc : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => F (radicalP21 ![p.1, p.2] * g) :=
    hF.comp (continuous_radicalP21_pair.mul continuous_const)
  have hc' : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => F' (radicalP21 ![p.1, p.2] * g) :=
    hF'.comp (continuous_radicalP21_pair.mul continuous_const)
  have h := integral2_boxMeasure_add (φ := fun x y => F (radicalP21 ![x, y] * g))
    (φ' := fun x y => F' (radicalP21 ![x, y] * g)) hc hc'
  simp only [Pi.add_apply]
  exact h.trans ((congrArg₂ (· + ·) (h1 g) (h2 g)).trans (add_zero (0 : ℂ)))

private theorem isCuspidalAlongP12_prodPins_add (hF : Continuous F) (hF' : Continuous F')
    (h1 : IsCuspidalAlongP12 (prodPins D U gen) F) (h2 : IsCuspidalAlongP12 (prodPins D U gen) F') :
    IsCuspidalAlongP12 (prodPins D U gen) (F + F') := by
  intro g
  have hc : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => F (radicalP12 ![p.1, p.2] * g) :=
    hF.comp (continuous_radicalP12_pair.mul continuous_const)
  have hc' : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => F' (radicalP12 ![p.1, p.2] * g) :=
    hF'.comp (continuous_radicalP12_pair.mul continuous_const)
  have h := integral2_boxMeasure_add (φ := fun x y => F (radicalP12 ![x, y] * g))
    (φ' := fun x y => F' (radicalP12 ![x, y] * g)) hc hc'
  simp only [Pi.add_apply]
  exact h.trans ((congrArg₂ (· + ·) (h1 g) (h2 g)).trans (add_zero (0 : ℂ)))

private theorem isCuspidalAlongP21_smul (pins : CarrierPins ℚ) (c : ℂ) (hF : IsCuspidalAlongP21 pins F) :
    IsCuspidalAlongP21 pins (c • F) := by
  intro g
  simp only [Pi.smul_apply, smul_eq_mul, MeasureTheory.integral_const_mul, hF g, mul_zero]

private theorem isCuspidalAlongP12_smul (pins : CarrierPins ℚ) (c : ℂ) (hF : IsCuspidalAlongP12 pins F) :
    IsCuspidalAlongP12 pins (c • F) := by
  intro g
  simp only [Pi.smul_apply, smul_eq_mul, MeasureTheory.integral_const_mul, hF g, mul_zero]

private theorem isCuspidalAlongP21_zero (pins : CarrierPins ℚ) :
    IsCuspidalAlongP21 pins (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := by
  intro g
  simp

private theorem isCuspidalAlongP12_zero (pins : CarrierPins ℚ) :
    IsCuspidalAlongP12 pins (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := by
  intro g
  simp

end Cuspidal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension"

end Pins
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 IsCuspidalAlongP21 IsCuspidalAlongP12 WhittakerBlock.archDeriv WhittakerBlock.casimir1 WhittakerBlock.casimir2 WhittakerBlock.casimir3 exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace eq_zero_of_toL2_eq_zero_of_continuous WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate WhittakerBlock.casimir_archDeriv_and_comm"
namespace CuspClassAction
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2

variable (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))

private def cuspSubmodule : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) where
  carrier := cuspFunctions ω a b Φ₀
  zero_mem' := ⟨Submodule.zero_mem _, continuous_zero, isCuspidalAlongP21_zero _, isCuspidalAlongP12_zero _⟩
  add_mem' := fun {_ _} hF hF' =>
    ⟨Submodule.add_mem _ hF.1 hF'.1, hF.2.1.add hF'.2.1,
      isCuspidalAlongP21_prodPins_add (D := ∅) (U := fun _ => ⊥) (gen := fun _ => 1) hF.2.1 hF'.2.1 hF.2.2.1
        hF'.2.2.1,
      isCuspidalAlongP12_prodPins_add (D := ∅) (U := fun _ => ⊥) (gen := fun _ => 1) hF.2.1 hF'.2.1 hF.2.2.2
        hF'.2.2.2⟩
  smul_mem' := fun c {_} hF =>
    ⟨Submodule.smul_mem _ c hF.1, hF.2.1.const_smul c, isCuspidalAlongP21_smul _ c hF.2.2.1,
      isCuspidalAlongP12_smul _ c hF.2.2.2⟩

private theorem mem_cuspSubmodule_iff (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    F ∈ cuspSubmodule ω a b Φ₀ ↔ F ∈ cuspFunctions ω a b Φ₀ :=
  Iff.rfl

private def cuspMemberSubmodule : Submodule ℂ ↥(automorphicSubmodule ω a b Φ₀) :=
  (cuspSubmodule ω a b Φ₀).comap (automorphicSubmodule ω a b Φ₀).subtype

private theorem mem_cuspMemberSubmodule_iff (f : ↥(automorphicSubmodule ω a b Φ₀)) :
    f ∈ cuspMemberSubmodule ω a b Φ₀ ↔ (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ cuspFunctions ω a b Φ₀ :=
  Iff.rfl

private theorem span_cuspMembers : Submodule.span ℂ (cuspMembers ω a b Φ₀) = cuspMemberSubmodule ω a b Φ₀ :=
  Submodule.span_eq (cuspMemberSubmodule ω a b Φ₀)

private scoped instance completeSpace_cuspidalSubspace : CompleteSpace ↥(cuspidalSubspace ω a b Φ₀) :=
  (isClosed_cuspidalSubspace ω a b Φ₀).isComplete.completeSpace_coe

private def RightTranslationLaw : Prop :=
  ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀),
    ∃ hmem : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, translateRight g F ∈ cuspFunctions ω a b Φ₀,
      (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩‖ = ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖) ∧
      Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => toL2 ω a b Φ₀ ⟨translateRight g F, (hmem g).1⟩

variable {ω a b Φ₀}

private def act (hR : RightTranslationLaw ω a b Φ₀) :
    AdelicGL 3 (𝓞 ℚ) ℚ →* Module.End ℂ ↥(cuspMemberSubmodule ω a b Φ₀) where
  toFun g :=
    { toFun := fun f =>
        ⟨⟨translateRight g (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ((hR _ f.2).fst g).1⟩, (hR _ f.2).fst g⟩
      map_add' := fun f f' => rfl
      map_smul' := fun c f => rfl }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    exact translateRight_one _
  map_mul' g g' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    exact translateRight_mul g g' _

private theorem coe_coe_act (hR : RightTranslationLaw ω a b Φ₀) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (f : ↥(cuspMemberSubmodule ω a b Φ₀)) :
    ((act hR g f : ↥(automorphicSubmodule ω a b Φ₀)) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) =
      translateRight g (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
  rfl

private def classOf : ↥(cuspMemberSubmodule ω a b Φ₀) →ₗ[ℂ] Carrier a b Φ₀ :=
  (toL2 ω a b Φ₀).comp (cuspMemberSubmodule ω a b Φ₀).subtype

private theorem classOf_apply (f : ↥(cuspMemberSubmodule ω a b Φ₀)) :
    classOf f = toL2 ω a b Φ₀ (f : ↥(automorphicSubmodule ω a b Φ₀)) :=
  rfl

private theorem isDenseIsometricAction (hR : RightTranslationLaw ω a b Φ₀) :
    DenseUnitaryExtension.IsDenseIsometricAction (G := AdelicGL 3 (𝓞 ℚ) ℚ) (C := ↥(cuspMemberSubmodule ω a b Φ₀))
      (Hc := Carrier a b Φ₀) classOf (cuspidalSubspace ω a b Φ₀) (act hR) where
  mem f := toL2_mem_cuspidalSubspace ω a b Φ₀ f.2
  dense := by
    rw [cuspidalSubspace_def, Submodule.topologicalClosure_coe, classOf, LinearMap.range_comp,
      Submodule.range_subtype, Submodule.span_image, span_cuspMembers]
  norm_eq g f := (hR _ f.2).snd.1 g
  cont f := (hR _ f.2).snd.2

private def rbar (hR : RightTranslationLaw ω a b Φ₀) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀) :=
  (isDenseIsometricAction hR).U g

private theorem rbar_toL2 (hR : RightTranslationLaw ω a b Φ₀) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀) :
    (rbar hR g ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ :
        Carrier a b Φ₀) = toL2 ω a b Φ₀ ⟨translateRight g F, ((hR F hF).fst g).1⟩ := by
  have h := (isDenseIsometricAction hR).U_gen g ⟨⟨F, hF.1⟩, hF⟩
  exact congrArg Subtype.val h

private theorem rbar_one (hR : RightTranslationLaw ω a b Φ₀) : rbar hR 1 = ContinuousLinearMap.id ℂ _ :=
  (isDenseIsometricAction hR).U_one

private theorem rbar_mul (hR : RightTranslationLaw ω a b Φ₀) (g g' : AdelicGL 3 (𝓞 ℚ) ℚ) :
    rbar hR (g * g') = (rbar hR g).comp (rbar hR g') :=
  (isDenseIsometricAction hR).U_mul g g'

private theorem norm_rbar (hR : RightTranslationLaw ω a b Φ₀) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (x : ↥(cuspidalSubspace ω a b Φ₀)) : ‖rbar hR g x‖ = ‖x‖ :=
  (isDenseIsometricAction hR).norm_U g x

private theorem adjoint_rbar (hR : RightTranslationLaw ω a b Φ₀) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ContinuousLinearMap.adjoint (rbar hR g) = rbar hR g⁻¹ :=
  (isDenseIsometricAction hR).adjoint_U g

end LanglandsTunnell.CubicInduction.CuspClassAction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 IsCuspidalAlongP21 IsCuspidalAlongP12 WhittakerBlock.archDeriv WhittakerBlock.casimir1 WhittakerBlock.casimir2 WhittakerBlock.casimir3 exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace eq_zero_of_toL2_eq_zero_of_continuous WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate WhittakerBlock.casimir_archDeriv_and_comm"
namespace SlabL2SEED
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2"
open LanglandsTunnell.CubicInduction.CuspClassAction
open scoped InnerProductSpace ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

local notation "GA" => AdelicGL 3 (𝓞 ℚ) ℚ

section Generic

theorem comap_subtype_topologicalClosure_span {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (D : Submodule ℂ E) (S : Set E) (hS : S ⊆ D) :
    ((Submodule.span ℂ S).topologicalClosure).comap D.subtype =
      (Submodule.span ℂ (D.subtype ⁻¹' S)).topologicalClosure := by
  have hrange : Set.range (D.subtype : D → E) = D := by
    rw [Submodule.coe_subtype, Subtype.range_coe_subtype]; rfl
  have hspan : Submodule.span ℂ (D.subtype ⁻¹' S) = (Submodule.span ℂ S).comap D.subtype := by
    apply le_antisymm
    · exact Submodule.span_le.2 fun x hx => Submodule.subset_span hx
    · intro x hx
      have hS' : D.subtype '' (D.subtype ⁻¹' S) = S := Set.image_preimage_eq_of_subset (by rw [hrange]; exact hS)
      rw [Submodule.mem_comap, ← hS', ← Submodule.map_span] at hx
      obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx
      have : y = x := Subtype.ext (by simpa using hyx)
      exact this ▸ hy
  ext x
  rw [Submodule.mem_comap, ← SetLike.mem_coe, ← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Submodule.topologicalClosure_coe, hspan, Submodule.comap_coe, Submodule.coe_subtype, closure_subtype]
  constructor
  · intro hx
    refine closure_mono ?_ hx
    intro y hy
    exact ⟨⟨y, Submodule.span_le.2 hS hy⟩, hy, rfl⟩
  · intro hx
    exact closure_mono (Set.image_preimage_subset _ _) hx

theorem exists_common_eigenvector {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    [Nontrivial M] (f g h : M →ₗ[ℂ] M) (hfg : f ∘ₗ g = g ∘ₗ f) (hfh : f ∘ₗ h = h ∘ₗ f) (hgh : g ∘ₗ h = h ∘ₗ g) :
    ∃ v : M, v ≠ 0 ∧ ∃ a b c : ℂ, f v = a • v ∧ g v = b • v ∧ h v = c • v := by
  classical

  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue f
  let E₁ : Submodule ℂ M := Module.End.eigenspace f a
  have hE₁ : ∀ v ∈ E₁, f v = a • v := fun v hv => Module.End.mem_eigenspace_iff.1 hv
  have hgE₁ : ∀ v ∈ E₁, g v ∈ E₁ := fun v hv => by
    rw [Module.End.mem_eigenspace_iff]
    have : f (g v) = g (f v) := congrFun (congrArg DFunLike.coe hfg) v
    rw [this, hE₁ v hv, map_smul]
  have hhE₁ : ∀ v ∈ E₁, h v ∈ E₁ := fun v hv => by
    rw [Module.End.mem_eigenspace_iff]
    have : f (h v) = h (f v) := congrFun (congrArg DFunLike.coe hfh) v
    rw [this, hE₁ v hv, map_smul]
  haveI : Nontrivial E₁ := Submodule.nontrivial_iff_ne_bot.2 (Module.End.hasEigenvalue_iff.1 ha)
  let g₁ : E₁ →ₗ[ℂ] E₁ := g.restrict hgE₁
  let h₁ : E₁ →ₗ[ℂ] E₁ := h.restrict hhE₁

  obtain ⟨b, hb⟩ := Module.End.exists_eigenvalue g₁
  let E₂ : Submodule ℂ E₁ := Module.End.eigenspace g₁ b
  have hE₂ : ∀ v ∈ E₂, g₁ v = b • v := fun v hv => Module.End.mem_eigenspace_iff.1 hv
  have hhE₂ : ∀ v ∈ E₂, h₁ v ∈ E₂ := fun v hv => by
    rw [Module.End.mem_eigenspace_iff]
    have hcomm : g₁ (h₁ v) = h₁ (g₁ v) := by
      apply Subtype.ext
      exact congrFun (congrArg DFunLike.coe hgh) (v : M)
    rw [hcomm, hE₂ v hv, map_smul]
  haveI : Nontrivial E₂ := Submodule.nontrivial_iff_ne_bot.2 (Module.End.hasEigenvalue_iff.1 hb)
  let h₂ : E₂ →ₗ[ℂ] E₂ := h₁.restrict hhE₂
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue h₂
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 (Module.End.hasEigenvalue_iff.1 hc)
  have hcu : h₂ u = c • u := Module.End.mem_eigenspace_iff.1 hu
  refine ⟨((u : E₁) : M), fun h0 => hu0 (Subtype.ext (Subtype.ext h0)), a, b, c, ?_, ?_, ?_⟩
  · exact hE₁ _ (u : E₁).2
  · have := hE₂ u u.2
    exact congrArg Subtype.val this
  · exact congrArg (fun w : E₂ => ((w : E₁) : M)) hcu

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction.CuspClassAction"

variable {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} {a b : ℝ} {Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}

def genSet (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (V : Submodule ℂ (Carrier a b Φ₀)) : Set ↥(automorphicSubmodule ω a b Φ₀) :=
  {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V}

def Kof (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (V : Submodule ℂ (Carrier a b Φ₀)) : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀) :=
  V.comap (cuspidalSubspace ω a b Φ₀).subtype

theorem Kof_eq {V : Submodule ℂ (Carrier a b Φ₀)}
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure) :
    Kof ω a b Φ₀ V = (Submodule.span ℂ ((cuspidalSubspace ω a b Φ₀).subtype ⁻¹'
      (toL2 ω a b Φ₀ '' genSet ω a b Φ₀ V))).topologicalClosure := by
  have hsubD : toL2 ω a b Φ₀ '' genSet ω a b Φ₀ V ⊆ cuspidalSubspace ω a b Φ₀ := by
    rintro _ ⟨f, hf, rfl⟩
    exact toL2_mem_cuspidalSubspace ω a b Φ₀ hf.1
  rw [← comap_subtype_topologicalClosure_span (cuspidalSubspace ω a b Φ₀) _ hsubD]
  unfold Kof
  exact congrArg (fun W : Submodule ℂ (Carrier a b Φ₀) => W.comap (cuspidalSubspace ω a b Φ₀).subtype) hgen

theorem isClosed_Kof {V : Submodule ℂ (Carrier a b Φ₀)}
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure) :
    IsClosed (Kof ω a b Φ₀ V : Set ↥(cuspidalSubspace ω a b Φ₀)) := by
  rw [Kof_eq hgen]
  exact Submodule.isClosed_topologicalClosure _

theorem le_cuspidalSubspace {V : Submodule ℂ (Carrier a b Φ₀)}
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure) :
    V ≤ cuspidalSubspace ω a b Φ₀ := by
  rw [hgen]
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) (isClosed_cuspidalSubspace ω a b Φ₀)
  rintro _ ⟨f, hf, rfl⟩
  exact toL2_mem_cuspidalSubspace ω a b Φ₀ hf.1

theorem lifts_stable {V : Submodule ℂ (Carrier a b Φ₀)}
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    {op : (GA → ℂ) → (GA → ℂ)} {T : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)}
    (hT : IsCuspLift3 ω a b Φ₀ op T)
    (hop : ∀ (f : GA → ℂ) (hf : f ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨f, hf.1⟩ ∈ V →
      ∀ h : op f ∈ cuspFunctions ω a b Φ₀, toL2 ω a b Φ₀ ⟨op f, h.1⟩ ∈ V) :
    ∀ x ∈ Kof ω a b Φ₀ V, T x ∈ Kof ω a b Φ₀ V := by
  intro x hx
  rw [Kof_eq hgen] at hx ⊢
  have hZc : IsClosed (((Submodule.span ℂ ((cuspidalSubspace ω a b Φ₀).subtype ⁻¹'
      (toL2 ω a b Φ₀ '' genSet ω a b Φ₀ V))).topologicalClosure.comap
        (T : ↥(cuspidalSubspace ω a b Φ₀) →ₗ[ℂ] ↥(cuspidalSubspace ω a b Φ₀))) :
          Set ↥(cuspidalSubspace ω a b Φ₀)) := by
    rw [Submodule.comap_coe]
    exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  have hle : Submodule.span ℂ ((cuspidalSubspace ω a b Φ₀).subtype ⁻¹'
      (toL2 ω a b Φ₀ '' genSet ω a b Φ₀ V)) ≤
      (Submodule.span ℂ ((cuspidalSubspace ω a b Φ₀).subtype ⁻¹'
        (toL2 ω a b Φ₀ '' genSet ω a b Φ₀ V))).topologicalClosure.comap
          (T : ↥(cuspidalSubspace ω a b Φ₀) →ₗ[ℂ] ↥(cuspidalSubspace ω a b Φ₀)) := by
    refine Submodule.span_le.2 fun y hy => ?_
    obtain ⟨⟨f, hf0⟩, hf, hfy⟩ := hy
    have hfc : f ∈ cuspFunctions ω a b Φ₀ := hf.1
    have hfV : toL2 ω a b Φ₀ ⟨f, hfc.1⟩ ∈ V := hf.2
    obtain ⟨hRF, hTy⟩ := hT f hfc
    have hy' : y = ⟨toL2 ω a b Φ₀ ⟨f, hfc.1⟩,
        toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hfc⟩ := Subtype.ext hfy.symm
    show T y ∈ (Submodule.span ℂ ((cuspidalSubspace ω a b Φ₀).subtype ⁻¹'
      (toL2 ω a b Φ₀ '' genSet ω a b Φ₀ V))).topologicalClosure
    refine Submodule.le_topologicalClosure _ (Submodule.subset_span ?_)
    show ((T y : ↥(cuspidalSubspace ω a b Φ₀)) : Carrier a b Φ₀) ∈ toL2 ω a b Φ₀ '' genSet ω a b Φ₀ V
    rw [hy', hTy]
    exact ⟨⟨op f, hRF.1⟩, ⟨hRF, hop f hfc hfV hRF⟩, rfl⟩
  exact Submodule.topologicalClosure_minimal _ hle hZc hx

theorem smoothing_mem_Kof {V : Submodule ℂ (Carrier a b Φ₀)}
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (hsm : ∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ φ : GA → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V)
    {φ : GA → ℂ} (hφ : IsSmoothingKernel φ)
    {T : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)}
    (hT : IsCuspLift3 ω a b Φ₀ (smoothingOperator φ) T) :
    ∀ x ∈ Kof ω a b Φ₀ V, T x ∈ Kof ω a b Φ₀ V :=
  lifts_stable hgen hT fun f hf hfV h => hsm f hf hfV φ hφ h

theorem smoothingOperator_smul (φ H : GA → ℂ) (c : ℂ) :
    smoothingOperator φ (c • H) = c • smoothingOperator φ H := by
  funext x
  simp only [smoothingOperator_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext g
  ring

theorem locallyIntegrable_of_continuous {F : GA → ℂ} (hF : Continuous F) :
    LocallyIntegrable F (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  exact hF.locallyIntegrable

theorem exists_kernel_foldr (φ : GA → ℂ) (hφ : IsSmoothingKernel φ) (l : List (Fin 3 × Fin 3)) :
    ∃ ψ : GA → ℂ, IsSmoothingKernel ψ ∧ ∀ H : GA → ℂ,
      LocallyIntegrable H (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) →
        l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (smoothingOperator φ H) = smoothingOperator ψ H := by
  induction l with
  | nil => exact ⟨φ, hφ, fun H _ => rfl⟩
  | cons p l ih =>
    obtain ⟨ψ, hψ, h⟩ := ih
    have h0 : LocallyIntegrable (0 : GA → ℂ) (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
      locallyIntegrable_of_continuous continuous_zero
    refine ⟨_, (archDeriv_smoothingOperator ψ 0 hψ h0 p.1 p.2).1, fun H hH => ?_⟩
    rw [List.foldr_cons, h H hH]
    exact (archDeriv_smoothingOperator ψ H hψ hH p.1 p.2).2

theorem continuous_smoothingOperator {φ H : GA → ℂ} (hφ : IsSmoothingKernel φ) (hH : Continuous H) :
    Continuous (smoothingOperator φ H) :=
  (continuous_and_isArchSmooth3_smoothingOperator φ H hφ (locallyIntegrable_of_continuous hH)).1

theorem isArchSmooth3_smoothingOperator {φ H : GA → ℂ} (hφ : IsSmoothingKernel φ) (hH : Continuous H) :
    WhittakerBlock.IsArchSmooth3 (smoothingOperator φ H) :=
  (continuous_and_isArchSmooth3_smoothingOperator φ H hφ (locallyIntegrable_of_continuous hH)).2

theorem continuous_foldr_smoothingOperator {φ H : GA → ℂ} (hφ : IsSmoothingKernel φ) (hH : Continuous H)
    (l : List (Fin 3 × Fin 3)) :
    Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (smoothingOperator φ H)) := by
  obtain ⟨ψ, hψ, h⟩ := exists_kernel_foldr φ hφ l
  rw [h H (locallyIntegrable_of_continuous hH)]
  exact continuous_smoothingOperator hψ hH

theorem archDeriv_smul (c : ℂ) (G : GA → ℂ) (i j : Fin 3) :
    WhittakerBlock.archDeriv i j (c • G) = c • WhittakerBlock.archDeriv i j G :=
  WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.2.2.1 c G i j

theorem isArchSmooth3_archDeriv {G : GA → ℂ} (hG : WhittakerBlock.IsArchSmooth3 G) (i j : Fin 3) :
    WhittakerBlock.IsArchSmooth3 (WhittakerBlock.archDeriv i j G) :=
  WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.1 G hG i j

theorem archDeriv_add {G G' : GA → ℂ} (hG : WhittakerBlock.IsArchSmooth3 G) (hG' : WhittakerBlock.IsArchSmooth3 G')
    (i j : Fin 3) :
    WhittakerBlock.archDeriv i j (G + G') = WhittakerBlock.archDeriv i j G + WhittakerBlock.archDeriv i j G' :=
  WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.2.1 G G' hG hG' i j

theorem isArchSmooth3_foldr {G : GA → ℂ} (hG : WhittakerBlock.IsArchSmooth3 G) (l : List (Fin 3 × Fin 3)) :
    WhittakerBlock.IsArchSmooth3 (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G) := by
  induction l with
  | nil => exact hG
  | cons p l ih =>
    rw [List.foldr_cons]
    exact isArchSmooth3_archDeriv ih p.1 p.2

theorem foldr_smul (c : ℂ) (G : GA → ℂ) (l : List (Fin 3 × Fin 3)) :
    l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (c • G) =
      c • l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [List.foldr_cons, List.foldr_cons, ih, archDeriv_smul]

theorem foldr_add {G G' : GA → ℂ} (hG : WhittakerBlock.IsArchSmooth3 G) (hG' : WhittakerBlock.IsArchSmooth3 G')
    (l : List (Fin 3 × Fin 3)) :
    l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (G + G') =
      l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G +
        l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G' := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih,
      archDeriv_add (isArchSmooth3_foldr hG l) (isArchSmooth3_foldr hG' l)]

private theorem _root_.LanglandsTunnell.CubicInduction.SlabL2SEED.foldr_append (G : GA → ℂ) (l l' : List (Fin 3 × Fin 3)) :
    l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (l'.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G) =
      (l ++ l').foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G := by
  rw [List.foldr_append]

p2m_export "LanglandsTunnell.CubicInduction.SlabL2SEED" "foldr_append"
theorem isArchSmooth3_add {G G' : GA → ℂ} (hG : WhittakerBlock.IsArchSmooth3 G) (hG' : WhittakerBlock.IsArchSmooth3 G') :
    WhittakerBlock.IsArchSmooth3 (G + G') := fun g => (hG g).add (hG' g)

theorem isArchSmooth3_smul (c : ℂ) {G : GA → ℂ} (hG : WhittakerBlock.IsArchSmooth3 G) :
    WhittakerBlock.IsArchSmooth3 (c • G) := fun g => (hG g).const_smul c

theorem isArchSmooth3_zero : WhittakerBlock.IsArchSmooth3 (0 : GA → ℂ) := fun _ => contDiffOn_const

theorem isArchSmooth3_sum {ι : Type} (s : Finset ι) {G : ι → GA → ℂ}
    (hG : ∀ i ∈ s, WhittakerBlock.IsArchSmooth3 (G i)) :
    WhittakerBlock.IsArchSmooth3 (∑ i ∈ s, G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isArchSmooth3_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact isArchSmooth3_add (hG i (Finset.mem_insert_self i s))
      (ih fun j hj => hG j (Finset.mem_insert_of_mem hj))

theorem foldr_sum {ι : Type} (s : Finset ι) {G : ι → GA → ℂ} (hG : ∀ i ∈ s, WhittakerBlock.IsArchSmooth3 (G i))
    (l : List (Fin 3 × Fin 3)) :
    l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (∑ i ∈ s, G i) =
      ∑ i ∈ s, l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    simpa only [zero_smul] using foldr_smul (0 : ℂ) (0 : GA → ℂ) l
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      foldr_add (hG i (Finset.mem_insert_self i s)) (isArchSmooth3_sum s fun j hj => hG j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hG j (Finset.mem_insert_of_mem hj)]

structure WordSum where
  ι : Type
  inst : Fintype ι
  w : ι → List (Fin 3 × Fin 3)
  op : (GA → ℂ) → (GA → ℂ)
  op_eq : ∀ X : GA → ℂ, op X = ∑ i : ι, (w i).foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) X

attribute [scoped instance] WordSum.inst

def ws1 : WordSum where
  ι := Fin 3
  inst := inferInstance
  w := fun i => [(i, i)]
  op := WhittakerBlock.casimir1
  op_eq := fun X => by
    funext g
    rw [Finset.sum_apply]
    rfl

def ws2 : WordSum where
  ι := Fin 3 × Fin 3
  inst := inferInstance
  w := fun p => [(p.1, p.2), (p.2, p.1)]
  op := WhittakerBlock.casimir2
  op_eq := fun X => by
    funext g
    rw [Finset.sum_apply, Fintype.sum_prod_type]
    rfl

def ws3 : WordSum where
  ι := Fin 3 × Fin 3 × Fin 3
  inst := inferInstance
  w := fun p => [(p.1, p.2.1), (p.2.1, p.2.2), (p.2.2, p.1)]
  op := WhittakerBlock.casimir3
  op_eq := fun X => by
    funext g
    rw [Finset.sum_apply, Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rfl

namespace WordSum

variable (W : WordSum)

theorem op_add {G G' : GA → ℂ} (hG : WhittakerBlock.IsArchSmooth3 G) (hG' : WhittakerBlock.IsArchSmooth3 G') :
    W.op (G + G') = W.op G + W.op G' := by
  rw [W.op_eq, W.op_eq, W.op_eq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => foldr_add hG hG' (W.w i)

theorem op_smul (c : ℂ) (G : GA → ℂ) : W.op (c • G) = c • W.op G := by
  rw [W.op_eq, W.op_eq, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => foldr_smul c G (W.w i)

theorem isArchSmooth3_op {G : GA → ℂ} (hG : WhittakerBlock.IsArchSmooth3 G) :
    WhittakerBlock.IsArchSmooth3 (W.op G) := by
  rw [W.op_eq]
  exact isArchSmooth3_sum _ fun i _ => isArchSmooth3_foldr hG (W.w i)

theorem foldr_op {G : GA → ℂ} (hG : WhittakerBlock.IsArchSmooth3 G) (l : List (Fin 3 × Fin 3)) :
    l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (W.op G) =
      ∑ i : W.ι, (l ++ W.w i).foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G := by
  rw [W.op_eq, foldr_sum _ (fun i _ => isArchSmooth3_foldr hG (W.w i))]
  exact Finset.sum_congr rfl fun i _ => foldr_append G l (W.w i)

theorem continuous_foldr_op {G : GA → ℂ} (hG : WhittakerBlock.IsArchSmooth3 G)
    (hGr : ∀ l : List (Fin 3 × Fin 3), Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G))
    (l : List (Fin 3 × Fin 3)) :
    Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (W.op G)) := by
  rw [W.foldr_op hG]
  have : (∑ i : W.ι, (l ++ W.w i).foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G) =
      fun g => ∑ i : W.ι, (l ++ W.w i).foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G g := by
    funext g
    exact Finset.sum_apply g _ _
  rw [this]
  exact continuous_finsetSum _ fun i _ => hGr (l ++ W.w i)

theorem exists_kernels (φ : GA → ℂ) (hφ : IsSmoothingKernel φ) :
    ∃ ψ : W.ι → GA → ℂ, (∀ i, IsSmoothingKernel (ψ i)) ∧
      ∀ H : GA → ℂ, Continuous H → W.op (smoothingOperator φ H) = ∑ i, smoothingOperator (ψ i) H := by
  have hk := fun i => exists_kernel_foldr φ hφ (W.w i)
  choose ψ hψ hψw using hk
  refine ⟨ψ, hψ, fun H hH => ?_⟩
  rw [W.op_eq]
  exact Finset.sum_congr rfl fun i _ => hψw i H (locallyIntegrable_of_continuous hH)

end WordSum
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction.CuspClassAction"

theorem op_smoothingOperator (W : WordSum) (hW : W = ws1 ∨ W = ws2 ∨ W = ws3) (φ H : GA → ℂ)
    (hφ : IsSmoothingKernel φ) (hH : WhittakerBlock.IsArchSmooth3 H)
    (hreg : ∀ l : List (Fin 3 × Fin 3), Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) H)) :
    W.op (smoothingOperator φ H) = smoothingOperator φ (W.op H) := by
  have h := casimir_smoothingOperator φ H hφ hH hreg
  rcases hW with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem op_comm (W W' : WordSum) (hW : W = ws1 ∨ W = ws2 ∨ W = ws3) (hW' : W' = ws1 ∨ W' = ws2 ∨ W' = ws3)
    (H : GA → ℂ) (hH : WhittakerBlock.IsArchSmooth3 H) : W.op (W'.op H) = W'.op (W.op H) := by
  have h := (WhittakerBlock.casimir_archDeriv_and_comm H hH).2
  rcases hW with rfl | rfl | rfl <;> rcases hW' with rfl | rfl | rfl
  · rfl
  · exact h.1
  · exact h.2.1
  · exact h.1.symm
  · rfl
  · exact h.2.2
  · exact h.2.1.symm
  · exact h.2.2.symm
  · rfl

def cls (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (G : GA → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀) : ↥(cuspidalSubspace ω a b Φ₀) :=
  ⟨toL2 ω a b Φ₀ ⟨G, hG.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hG⟩

theorem coe_cls (G : GA → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀) :
    ((cls ω a b Φ₀ G hG : ↥(cuspidalSubspace ω a b Φ₀)) : Carrier a b Φ₀) = toL2 ω a b Φ₀ ⟨G, hG.1⟩ := rfl

theorem cls_add (G G' : GA → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀) (hG' : G' ∈ cuspFunctions ω a b Φ₀)
    (hGG' : G + G' ∈ cuspFunctions ω a b Φ₀) :
    cls ω a b Φ₀ (G + G') hGG' = cls ω a b Φ₀ G hG + cls ω a b Φ₀ G' hG' := by
  apply Subtype.ext
  rw [Submodule.coe_add, coe_cls, coe_cls, coe_cls, ← map_add]
  rfl

theorem cls_smul (c : ℂ) (G : GA → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀) (hcG : c • G ∈ cuspFunctions ω a b Φ₀) :
    cls ω a b Φ₀ (c • G) hcG = c • cls ω a b Φ₀ G hG := by
  apply Subtype.ext
  rw [Submodule.coe_smul, coe_cls, coe_cls, ← map_smul]
  rfl

theorem cls_zero (h0 : (0 : GA → ℂ) ∈ cuspFunctions ω a b Φ₀) : cls ω a b Φ₀ 0 h0 = 0 := by
  apply Subtype.ext
  rw [coe_cls, Submodule.coe_zero]
  exact map_zero (toL2 ω a b Φ₀)

theorem eq_of_cls_eq (hΦ : IsSlabDomain a b Φ₀) (G G' : GA → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀)
    (hG' : G' ∈ cuspFunctions ω a b Φ₀) (h : cls ω a b Φ₀ G hG = cls ω a b Φ₀ G' hG') : G = G' := by
  have hmem : G - G' ∈ automorphicSubmodule ω a b Φ₀ := Submodule.sub_mem _ hG.1 hG'.1
  have h0 : toL2 ω a b Φ₀ ⟨G - G', hmem⟩ = 0 := by
    have : (⟨G - G', hmem⟩ : ↥(automorphicSubmodule ω a b Φ₀)) = ⟨G, hG.1⟩ - ⟨G', hG'.1⟩ := rfl
    rw [this, map_sub, sub_eq_zero]
    exact congrArg Subtype.val h
  exact sub_eq_zero.1 (eq_zero_of_toL2_eq_zero_of_continuous ω a b Φ₀ hΦ _ hmem (hG.2.1.sub hG'.2.1) h0)

def Mspace (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (E' : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)) : Submodule ℂ (GA → ℂ) where
  carrier := {G | ∃ hG : G ∈ cuspFunctions ω a b Φ₀, WhittakerBlock.IsArchSmooth3 G ∧
    (∀ l : List (Fin 3 × Fin 3), Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G)) ∧
    cls ω a b Φ₀ G hG ∈ E'}
  zero_mem' := ⟨(cuspSubmodule ω a b Φ₀).zero_mem, isArchSmooth3_zero, fun l => by
      have h0 : l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (0 : GA → ℂ) = 0 := by
        simpa only [zero_smul] using foldr_smul (0 : ℂ) (0 : GA → ℂ) l
      rw [h0]
      exact continuous_zero, by
      rw [cls_zero]
      exact E'.zero_mem⟩
  add_mem' := fun {G G'} hG hG' => by
    obtain ⟨hGc, hGs, hGr, hGE⟩ := hG
    obtain ⟨hGc', hGs', hGr', hGE'⟩ := hG'
    refine ⟨(cuspSubmodule ω a b Φ₀).add_mem hGc hGc', isArchSmooth3_add hGs hGs', fun l => ?_, ?_⟩
    · rw [foldr_add hGs hGs']
      exact (hGr l).add (hGr' l)
    · rw [cls_add G G' hGc hGc']
      exact E'.add_mem hGE hGE'
  smul_mem' := fun c {G} hG => by
    obtain ⟨hGc, hGs, hGr, hGE⟩ := hG
    refine ⟨(cuspSubmodule ω a b Φ₀).smul_mem c hGc, isArchSmooth3_smul c hGs, fun l => ?_, ?_⟩
    · rw [foldr_smul]
      exact (hGr l).const_smul c
    · rw [cls_smul c G hGc]
      exact E'.smul_mem c hGE

theorem mem_Mspace {E' : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)} {G : GA → ℂ} :
    G ∈ Mspace ω a b Φ₀ E' ↔ ∃ hG : G ∈ cuspFunctions ω a b Φ₀, WhittakerBlock.IsArchSmooth3 G ∧
      (∀ l : List (Fin 3 × Fin 3), Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G)) ∧
      cls ω a b Φ₀ G hG ∈ E' := Iff.rfl

def opLin (W : WordSum) (E' : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀))
    (h : ∀ G ∈ Mspace ω a b Φ₀ E', W.op G ∈ Mspace ω a b Φ₀ E') :
    ↥(Mspace ω a b Φ₀ E') →ₗ[ℂ] ↥(Mspace ω a b Φ₀ E') where
  toFun G := ⟨W.op (G : GA → ℂ), h _ G.2⟩
  map_add' G G' := by
    apply Subtype.ext
    show W.op ((G : GA → ℂ) + G') = W.op G + W.op G'
    exact W.op_add (mem_Mspace.1 G.2).snd.1 (mem_Mspace.1 G'.2).snd.1
  map_smul' c G := by
    apply Subtype.ext
    show W.op (c • (G : GA → ℂ)) = c • W.op G
    exact W.op_smul c G

theorem coe_opLin (W : WordSum) (E' : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀))
    (h : ∀ G ∈ Mspace ω a b Φ₀ E', W.op G ∈ Mspace ω a b Φ₀ E') (G : ↥(Mspace ω a b Φ₀ E')) :
    ((opLin W E' h G : ↥(Mspace ω a b Φ₀ E')) : GA → ℂ) = W.op (G : GA → ℂ) := rfl

theorem adjoint_eq_of_lifts (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (hΦ : IsSlabDomain a b Φ₀)
    {φ : GA → ℂ} (hφ : IsSmoothingKernel φ)
    {T Ts : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)}
    (hT : IsCuspLift3 ω a b Φ₀ (smoothingOperator φ) T)
    (hTs : IsCuspLift3 ω a b Φ₀ (smoothingOperator (fun g => star (φ g⁻¹))) Ts) :
    ContinuousLinearMap.adjoint T = Ts := by
  have hR : RightTranslationLaw ω a b Φ₀ := fun H hH =>
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ H hH
  obtain ⟨_, hadj0⟩ := isSmoothingKernel_star_inv_and_inner_toL2_smoothingOperator_eq ω hω a b Φ₀ hΦ φ hφ
  have hadj : ∀ x y : ↥(cuspidalSubspace ω a b Φ₀), ⟪T x, y⟫_ℂ = ⟪x, Ts y⟫_ℂ := by
    have hD := (isDenseIsometricAction hR).denseRange_gen
    have hgen_eq : ∀ c : ↥(cuspMemberSubmodule ω a b Φ₀), (isDenseIsometricAction hR).gen c =
        ⟨toL2 ω a b Φ₀ ⟨((c : ↥(automorphicSubmodule ω a b Φ₀)) : GA → ℂ), c.2.1⟩,
          toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ c.2⟩ := by
      intro c
      apply Subtype.ext
      exact classOf_apply c
    have hcc : ∀ c c' : ↥(cuspMemberSubmodule ω a b Φ₀),
        ⟪T ((isDenseIsometricAction hR).gen c), (isDenseIsometricAction hR).gen c'⟫_ℂ =
          ⟪(isDenseIsometricAction hR).gen c, Ts ((isDenseIsometricAction hR).gen c')⟫_ℂ := by
      intro c c'
      obtain ⟨hRc, hTc'⟩ := hT (((c : ↥(automorphicSubmodule ω a b Φ₀)) : GA → ℂ)) c.2
      obtain ⟨hRc', hTsc'⟩ := hTs (((c' : ↥(automorphicSubmodule ω a b Φ₀)) : GA → ℂ)) c'.2
      rw [hgen_eq c, hgen_eq c', Submodule.coe_inner, Submodule.coe_inner, hTc', hTsc']
      exact hadj0 (((c : ↥(automorphicSubmodule ω a b Φ₀)) : GA → ℂ))
        (((c' : ↥(automorphicSubmodule ω a b Φ₀)) : GA → ℂ)) c.2 c'.2 hRc hRc'
    have step1 : ∀ c' : ↥(cuspMemberSubmodule ω a b Φ₀), ∀ x : ↥(cuspidalSubspace ω a b Φ₀),
        ⟪T x, (isDenseIsometricAction hR).gen c'⟫_ℂ = ⟪x, Ts ((isDenseIsometricAction hR).gen c')⟫_ℂ := by
      intro c'
      have := hD.equalizer ((T.continuous).inner continuous_const) (continuous_id.inner continuous_const)
        (funext fun c => hcc c c')
      exact fun x => congrFun this x
    intro x y
    have := hD.equalizer (continuous_const.inner continuous_id) (continuous_const.inner (Ts.continuous))
      (funext fun c' => step1 c' x)
    exact congrFun this y
  refine ((ContinuousLinearMap.eq_adjoint_iff Ts T).2 fun x y => ?_).symm
  rw [← inner_conj_symm, ← hadj y x]
  exact inner_conj_symm x (T y)

theorem spectral_step (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (hΦ : IsSlabDomain a b Φ₀)
    (V : Submodule ℂ (Carrier a b Φ₀))
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (hne : V ≠ ⊥)
    (hsm : ∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ φ : GA → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V) :
    ∃ (φ : GA → ℂ) (_ : IsSmoothingKernel φ)
      (T : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀))
      (_ : IsCuspLift3 ω a b Φ₀ (smoothingOperator φ) T)
      (Ts : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀))
      (_ : IsCuspLift3 ω a b Φ₀ (smoothingOperator (fun g => star (φ g⁻¹))) Ts)
      (lam : ℂ) (E' : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)),
      lam ≠ 0 ∧ FiniteDimensional ℂ ↥E' ∧ (∀ x ∈ E', Ts (T x) = lam • x) ∧
        (∀ x ∈ E', (x : Carrier a b Φ₀) ∈ V) ∧
        (∀ x : ↥(cuspidalSubspace ω a b Φ₀), (x : Carrier a b Φ₀) ∈ V → Ts (T x) = lam • x → x ∈ E') ∧
        ∃ v ∈ E', v ≠ 0 := by
  classical
  set K : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀) := Kof ω a b Φ₀ V with hKdef
  have hKV : ∀ x : ↥(cuspidalSubspace ω a b Φ₀), x ∈ K ↔ (x : Carrier a b Φ₀) ∈ V := fun x => Iff.rfl
  have hKc : IsClosed (K : Set ↥(cuspidalSubspace ω a b Φ₀)) := isClosed_Kof hgen
  haveI : CompleteSpace K := hKc.completeSpace_coe

  obtain ⟨v₀, hv₀V, hv₀0⟩ := (Submodule.ne_bot_iff V).1 hne
  let x₀ : ↥(cuspidalSubspace ω a b Φ₀) := ⟨v₀, le_cuspidalSubspace hgen hv₀V⟩
  have hx₀K : x₀ ∈ K := (hKV x₀).2 hv₀V
  have hx₀0 : x₀ ≠ 0 := fun h => hv₀0 (congrArg Subtype.val h)

  obtain ⟨φ, hφ, T, hTc, hT, hTx₀⟩ :=
    exists_isSmoothingKernel_isCompactOperator_isCuspLift3_apply_ne_zero ω hω a b Φ₀ hΦ x₀ hx₀0
  have hφs : IsSmoothingKernel (fun g => star (φ g⁻¹)) :=
    (isSmoothingKernel_star_inv_and_inner_toL2_smoothingOperator_eq ω hω a b Φ₀ hΦ φ hφ).1
  obtain ⟨Ts, _, hTs⟩ := exists_isCompactOperator_cuspidalSubspace_smoothingOperator ω a b Φ₀ hΦ
    exists_mul_eq_unipotent_mul_diagonal_mul_compact _ hφs
  have hTadj : ContinuousLinearMap.adjoint T = Ts := adjoint_eq_of_lifts hω hΦ hφ hT hTs

  have hKT : ∀ x ∈ K, T x ∈ K := smoothing_mem_Kof hgen hsm hφ hT
  have hKTs : ∀ x ∈ K, Ts x ∈ K := smoothing_mem_Kof hgen hsm hφs hTs

  set B : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀) := star T * T with hBdef
  have hBapply : ∀ x, B x = Ts (T x) := fun x => by
    show ContinuousLinearMap.adjoint T (T x) = Ts (T x)
    rw [hTadj]
  have hBc : IsCompactOperator B := hTc.clm_comp (ContinuousLinearMap.adjoint T)
  have hBsa : IsSelfAdjoint B := IsSelfAdjoint.star_mul_self T
  have hBK : ∀ x ∈ K, B x ∈ K := fun x hx => by rw [hBapply]; exact hKTs _ (hKT x hx)
  set P : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀) := K.starProjection with hPdef
  have hPsa : IsSelfAdjoint P := (isStarProjection_starProjection (U := K)).isSelfAdjoint
  set C : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀) := P * B * P with hCdef
  have hCapply : ∀ x, C x = P (B (P x)) := fun x => by
    rw [hCdef, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  have hCc : IsCompactOperator C := by
    have h := (hBc.comp_clm P).clm_comp P
    have e : (C : ↥(cuspidalSubspace ω a b Φ₀) → ↥(cuspidalSubspace ω a b Φ₀)) =
        (P : ↥(cuspidalSubspace ω a b Φ₀) → ↥(cuspidalSubspace ω a b Φ₀)) ∘
          ((B : ↥(cuspidalSubspace ω a b Φ₀) → ↥(cuspidalSubspace ω a b Φ₀)) ∘
            (P : ↥(cuspidalSubspace ω a b Φ₀) → ↥(cuspidalSubspace ω a b Φ₀))) := by
      funext x
      simp only [Function.comp_apply, hCapply]
    rw [e]
    exact h
  have hPadj : ContinuousLinearMap.adjoint P = P := (ContinuousLinearMap.isSelfAdjoint_iff').mp hPsa
  have hBadj : ContinuousLinearMap.adjoint B = B := (ContinuousLinearMap.isSelfAdjoint_iff').mp hBsa
  have hCsa : IsSelfAdjoint C := by
    refine (ContinuousLinearMap.isSelfAdjoint_iff').mpr ((ContinuousLinearMap.eq_adjoint_iff C C).mpr ?_).symm
    intro x y
    rw [hCapply, hCapply]
    have s1 : ⟪P (B (P x)), y⟫_ℂ = ⟪B (P x), P y⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right P (B (P x)) y, hPadj]
    have s2 : ⟪B (P x), P y⟫_ℂ = ⟪P x, B (P y)⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right B (P x) (P y), hBadj]
    have s3 : ⟪P x, B (P y)⟫_ℂ = ⟪x, P (B (P y))⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right P x (B (P y)), hPadj]
    rw [s1, s2, s3]
  have hC0 : C ≠ 0 := by
    intro h
    have hPx : P x₀ = x₀ := Submodule.starProjection_eq_self_iff.mpr hx₀K
    have hPBx : P (B x₀) = B x₀ := Submodule.starProjection_eq_self_iff.mpr (hBK x₀ hx₀K)
    have h3 : ⟪C x₀, x₀⟫_ℂ = 0 := by rw [h, ContinuousLinearMap.zero_apply, inner_zero_left]
    have hBapply' : B x₀ = ContinuousLinearMap.adjoint T (T x₀) := rfl
    rw [hCapply, hPx, hPBx, hBapply', ContinuousLinearMap.adjoint_inner_left, inner_self_eq_zero] at h3
    exact hTx₀ h3
  obtain ⟨lam, hlamE, hlam0⟩ : ∃ lam : ℂ,
      Module.End.HasEigenvalue (C : Module.End ℂ ↥(cuspidalSubspace ω a b Φ₀)) lam ∧ lam ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hC0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hCc hCsa.isSymmetric).mp hno)

  set E : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀) :=
    Module.End.eigenspace (B : Module.End ℂ ↥(cuspidalSubspace ω a b Φ₀)) lam with hE
  haveI hEfd : FiniteDimensional ℂ ↥E := ContinuousLinearMap.finite_dimensional_eigenspace hBc lam hlam0
  have hE'fd : FiniteDimensional ℂ ↥(K ⊓ E) := Submodule.finiteDimensional_of_le (inf_le_right : K ⊓ E ≤ E)
  refine ⟨φ, hφ, T, hT, Ts, hTs, lam, K ⊓ E, hlam0, hE'fd, fun x hx => ?_, fun x hx => (hKV x).1 hx.1,
    fun x h1 h2 => ⟨(hKV x).2 h1, Module.End.mem_eigenspace_iff.mpr ((hBapply x).trans h2)⟩, ?_⟩
  · rw [← hBapply]
    exact Module.End.mem_eigenspace_iff.mp hx.2
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp (Module.End.hasEigenvalue_iff.mp hlamE)
    have hCv : C v = lam • v := Module.End.mem_eigenspace_iff.mp hv
    have hvK : v ∈ K := by
      have h1 : lam • v ∈ K := by
        rw [← hCv, hCapply]
        exact Submodule.starProjection_apply_mem K _
      have h2 : v = lam⁻¹ • (lam • v) := (inv_smul_smul₀ hlam0 v).symm
      rw [h2]
      exact K.smul_mem _ h1
    have hPv : P v = v := Submodule.starProjection_eq_self_iff.mpr hvK
    have hBv : B v = lam • v := by
      have hPBv : P (B v) = B v := Submodule.starProjection_eq_self_iff.mpr (hBK v hvK)
      rw [← hCv, hCapply, hPv, hPBv]
    exact ⟨v, ⟨hvK, Module.End.mem_eigenspace_iff.mpr hBv⟩, hv0⟩

theorem op_mem_Mspace (hΦ : IsSlabDomain a b Φ₀) (V : Submodule ℂ (Carrier a b Φ₀))
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (hsm : ∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ φ : GA → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V)
    {φ : GA → ℂ} (hφ : IsSmoothingKernel φ) (hφs : IsSmoothingKernel (fun g => star (φ g⁻¹)))
    {T Ts : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)}
    (hT : IsCuspLift3 ω a b Φ₀ (smoothingOperator φ) T)
    (hTs : IsCuspLift3 ω a b Φ₀ (smoothingOperator (fun g => star (φ g⁻¹))) Ts)
    {lam : ℂ} (hlam0 : lam ≠ 0) {E' : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)}
    (hE'B : ∀ x ∈ E', Ts (T x) = lam • x) (hE'K : ∀ x ∈ E', (x : Carrier a b Φ₀) ∈ V)
    (hE'mk : ∀ x : ↥(cuspidalSubspace ω a b Φ₀), (x : Carrier a b Φ₀) ∈ V → Ts (T x) = lam • x → x ∈ E')
    (W : WordSum) (hW : W = ws1 ∨ W = ws2 ∨ W = ws3) :
    ∀ G ∈ Mspace ω a b Φ₀ E', W.op G ∈ Mspace ω a b Φ₀ E' := by
  classical
  intro G hG
  obtain ⟨hGc, hGs, hGr, hGE⟩ := mem_Mspace.1 hG
  have hKT : ∀ x ∈ Kof ω a b Φ₀ V, T x ∈ Kof ω a b Φ₀ V := smoothing_mem_Kof hgen hsm hφ hT

  obtain ⟨h1, hT1c⟩ := hT G hGc
  have hT1 : T (cls ω a b Φ₀ G hGc) = cls ω a b Φ₀ _ h1 := Subtype.ext hT1c
  obtain ⟨h2, hT2c⟩ := hTs _ h1
  have hT2 : Ts (cls ω a b Φ₀ _ h1) = cls ω a b Φ₀ _ h2 := Subtype.ext hT2c

  have hlamG : lam • G = smoothingOperator (fun g => star (φ g⁻¹)) (smoothingOperator φ G) := by
    apply eq_of_cls_eq hΦ _ _ ((cuspSubmodule ω a b Φ₀).smul_mem lam hGc) h2
    rw [cls_smul lam G hGc, ← hE'B _ hGE, hT1, hT2]
  have h1K : ((cls ω a b Φ₀ _ h1 : ↥(cuspidalSubspace ω a b Φ₀)) : Carrier a b Φ₀) ∈ V := by
    rw [← hT1]
    exact hKT _ (hE'K _ hGE)
  have hH1c : Continuous (smoothingOperator φ G) := h1.2.1
  have hH1s : WhittakerBlock.IsArchSmooth3 (smoothingOperator φ G) := isArchSmooth3_smoothingOperator hφ hGc.2.1
  have hH1r := continuous_foldr_smoothingOperator hφ hGc.2.1

  obtain ⟨ψ, hψ, hψsum⟩ := W.exists_kernels (fun g => star (φ g⁻¹)) hφs
  have hTi := fun i => exists_isCompactOperator_cuspidalSubspace_smoothingOperator ω a b Φ₀ hΦ
    exists_mul_eq_unipotent_mul_diagonal_mul_compact (ψ i) (hψ i)
  choose Ti _hTic hTi using hTi
  have hmi : ∀ i, smoothingOperator (ψ i) (smoothingOperator φ G) ∈ cuspFunctions ω a b Φ₀ :=
    fun i => ((hTi i) _ h1).fst
  have hsumc : (∑ i, smoothingOperator (ψ i) (smoothingOperator φ G)) ∈ cuspFunctions ω a b Φ₀ :=
    (cuspSubmodule ω a b Φ₀).sum_mem fun i _ => hmi i
  have hopG : W.op G = lam⁻¹ • ∑ i, smoothingOperator (ψ i) (smoothingOperator φ G) := by
    rw [← hψsum _ hH1c, ← hlamG, W.op_smul, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
  have hopc : W.op G ∈ cuspFunctions ω a b Φ₀ := by
    rw [hopG]
    exact (cuspSubmodule ω a b Φ₀).smul_mem _ hsumc
  have hTicls : ∀ i, Ti i (cls ω a b Φ₀ _ h1) = cls ω a b Φ₀ _ (hmi i) := fun i =>
    Subtype.ext ((hTi i) _ h1).snd
  refine mem_Mspace.2 ⟨hopc, W.isArchSmooth3_op hGs, W.continuous_foldr_op hGs hGr, hE'mk _ ?_ ?_⟩
  ·
    have hsumcls : cls ω a b Φ₀ _ hsumc = ∑ i, Ti i (cls ω a b Φ₀ _ h1) := by
      apply Subtype.ext
      rw [coe_cls, Submodule.coe_sum]
      simp_rw [hTicls, coe_cls]
      rw [← map_sum]
      congr 1
      apply Subtype.ext
      rw [Submodule.coe_sum]
    have hcls : cls ω a b Φ₀ _ hopc =
        cls ω a b Φ₀ _ ((cuspSubmodule ω a b Φ₀).smul_mem lam⁻¹ hsumc) := by
      apply Subtype.ext
      rw [coe_cls, coe_cls]
      congr 1
      exact Subtype.ext hopG
    show ((cls ω a b Φ₀ _ hopc : ↥(cuspidalSubspace ω a b Φ₀)) : Carrier a b Φ₀) ∈ V
    rw [hcls, cls_smul lam⁻¹ _ hsumc, hsumcls, Submodule.coe_smul, Submodule.coe_sum]
    refine V.smul_mem _ (V.sum_mem fun i _ => ?_)
    exact smoothing_mem_Kof hgen hsm (hψ i) (hTi i) _ h1K
  ·
    obtain ⟨h3, hT3c⟩ := hT _ hopc
    have hT3 : T (cls ω a b Φ₀ _ hopc) = cls ω a b Φ₀ _ h3 := Subtype.ext hT3c
    obtain ⟨h4, hT4c⟩ := hTs _ h3
    have hT4 : Ts (cls ω a b Φ₀ _ h3) = cls ω a b Φ₀ _ h4 := Subtype.ext hT4c
    rw [hT3, hT4, ← cls_smul lam _ hopc ((cuspSubmodule ω a b Φ₀).smul_mem lam hopc)]
    apply Subtype.ext
    rw [coe_cls, coe_cls]
    congr 1
    apply Subtype.ext
    show smoothingOperator (fun g => star (φ g⁻¹)) (smoothingOperator φ (W.op G)) = lam • W.op G
    rw [← op_smoothingOperator W hW φ G hφ hGs hGr,
      ← op_smoothingOperator W hW (fun g => star (φ g⁻¹)) (smoothingOperator φ G) hφs hH1s hH1r,
      ← hlamG, W.op_smul]

theorem main (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (hΦ : IsSlabDomain a b Φ₀)
    (V : Submodule ℂ (Carrier a b Φ₀))
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (hne : V ≠ ⊥)
    (hsm : ∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ φ : GA → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V) :
    ∃ (c₁ c₂ c₃ : ℂ) (G : GA → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀),
      toL2 ω a b Φ₀ ⟨G, hG.1⟩ ∈ V ∧ toL2 ω a b Φ₀ ⟨G, hG.1⟩ ≠ 0 ∧
        WhittakerBlock.IsArchSmooth3 G ∧
        (∀ l : List (Fin 3 × Fin 3), Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G)) ∧
        WhittakerBlock.casimir1 G = c₁ • G ∧ WhittakerBlock.casimir2 G = c₂ • G ∧
          WhittakerBlock.casimir3 G = c₃ • G := by
  classical
  obtain ⟨φ, hφ, T, hT, Ts, hTs, lam, E', hlam0, hE'fd, hE'B, hE'K, hE'mk, v, hvE', hv0⟩ :=
    spectral_step hω hΦ V hgen hne hsm
  haveI := hE'fd
  have hφs : IsSmoothingKernel (fun g => star (φ g⁻¹)) :=
    (isSmoothingKernel_star_inv_and_inner_toL2_smoothingOperator_eq ω hω a b Φ₀ hΦ φ hφ).1

  have hMle : Mspace ω a b Φ₀ E' ≤ automorphicSubmodule ω a b Φ₀ := fun G hG => (mem_Mspace.1 hG).fst.1
  let ιM : ↥(Mspace ω a b Φ₀ E') →ₗ[ℂ] Carrier a b Φ₀ := (toL2 ω a b Φ₀).comp (Submodule.inclusion hMle)
  have hιM_apply : ∀ G : ↥(Mspace ω a b Φ₀ E'), ιM G = toL2 ω a b Φ₀ ⟨(G : GA → ℂ), hMle G.2⟩ := fun G => rfl
  let Pfin : Submodule ℂ (Carrier a b Φ₀) := E'.map (cuspidalSubspace ω a b Φ₀).subtype
  haveI : FiniteDimensional ℂ ↥Pfin := Module.Finite.map E' _
  have hιM_mem : ∀ G : ↥(Mspace ω a b Φ₀ E'), ιM G ∈ Pfin := fun G =>
    ⟨cls ω a b Φ₀ _ (mem_Mspace.1 G.2).fst, (mem_Mspace.1 G.2).snd.2.2, (hιM_apply G).symm⟩
  haveI : FiniteDimensional ℂ ↥(Mspace ω a b Φ₀ E') := by
    refine Module.Finite.of_injective (ιM.codRestrict Pfin hιM_mem) fun G G' h => ?_
    apply Subtype.ext
    have h' : ιM G = ιM G' := congrArg Subtype.val h
    rw [hιM_apply, hιM_apply] at h'
    exact eq_of_cls_eq hΦ _ _ (mem_Mspace.1 G.2).fst (mem_Mspace.1 G'.2).fst (Subtype.ext h')

  obtain ⟨F₁, hF₁, hF₁eq⟩ : ∃ (F₁ : GA → ℂ) (hF₁ : F₁ ∈ cuspFunctions ω a b Φ₀), T v = cls ω a b Φ₀ F₁ hF₁ := by
    obtain ⟨CN, hrep⟩ := exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace ω hω a b Φ₀ hΦ φ hφ
      T hT
    obtain ⟨F₁, hF₁, h, _⟩ := hrep v
    exact ⟨F₁, hF₁, Subtype.ext h⟩
  obtain ⟨hG₀c, hG₀eqc⟩ := hTs F₁ hF₁
  have hG₀eq : Ts (cls ω a b Φ₀ F₁ hF₁) = cls ω a b Φ₀ _ hG₀c := Subtype.ext hG₀eqc
  have hG₀cls : cls ω a b Φ₀ _ hG₀c = lam • v := by
    rw [← hG₀eq, ← hF₁eq]
    exact hE'B v hvE'
  have hG₀M : smoothingOperator (fun g => star (φ g⁻¹)) F₁ ∈ Mspace ω a b Φ₀ E' := by
    refine mem_Mspace.2 ⟨hG₀c, isArchSmooth3_smoothingOperator hφs hF₁.2.1,
      continuous_foldr_smoothingOperator hφs hF₁.2.1, ?_⟩
    rw [hG₀cls]
    exact E'.smul_mem lam hvE'
  haveI : Nontrivial ↥(Mspace ω a b Φ₀ E') := by
    refine ⟨⟨⟨_, hG₀M⟩, 0, fun h => ?_⟩⟩
    have h0 : smoothingOperator (fun g => star (φ g⁻¹)) F₁ = 0 := congrArg Subtype.val h
    have : lam • v = 0 := by
      rw [← hG₀cls]
      have : cls ω a b Φ₀ _ hG₀c = cls ω a b Φ₀ 0 (cuspSubmodule ω a b Φ₀).zero_mem := by
        apply Subtype.ext
        rw [coe_cls, coe_cls]
        congr 1
        exact Subtype.ext h0
      rw [this, cls_zero]
    exact hv0 ((smul_eq_zero.1 this).resolve_left hlam0)

  have hmem : ∀ (W : WordSum), (W = ws1 ∨ W = ws2 ∨ W = ws3) →
      ∀ G ∈ Mspace ω a b Φ₀ E', W.op G ∈ Mspace ω a b Φ₀ E' := fun W hW =>
    op_mem_Mspace hΦ V hgen hsm hφ hφs hT hTs hlam0 hE'B hE'K hE'mk W hW
  have h1m := hmem ws1 (Or.inl rfl)
  have h2m := hmem ws2 (Or.inr (Or.inl rfl))
  have h3m := hmem ws3 (Or.inr (Or.inr rfl))
  have hcomm : ∀ (W W' : WordSum) (hW : W = ws1 ∨ W = ws2 ∨ W = ws3) (hW' : W' = ws1 ∨ W' = ws2 ∨ W' = ws3)
      (h : ∀ G ∈ Mspace ω a b Φ₀ E', W.op G ∈ Mspace ω a b Φ₀ E')
      (h' : ∀ G ∈ Mspace ω a b Φ₀ E', W'.op G ∈ Mspace ω a b Φ₀ E'),
      opLin W E' h ∘ₗ opLin W' E' h' = opLin W' E' h' ∘ₗ opLin W E' h := by
    intro W W' hW hW' h h'
    apply LinearMap.ext
    intro G
    apply Subtype.ext
    show W.op (W'.op (G : GA → ℂ)) = W'.op (W.op (G : GA → ℂ))
    exact op_comm W W' hW hW' _ (mem_Mspace.1 G.2).snd.1
  obtain ⟨Gm, hGm0, c₁, c₂, c₃, hc1, hc2, hc3⟩ :=
    exists_common_eigenvector (opLin ws1 E' h1m) (opLin ws2 E' h2m) (opLin ws3 E' h3m)
      (hcomm _ _ (Or.inl rfl) (Or.inr (Or.inl rfl)) _ _) (hcomm _ _ (Or.inl rfl) (Or.inr (Or.inr rfl)) _ _)
      (hcomm _ _ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) _ _)

  obtain ⟨hGc, hGs, hGr, hGE⟩ := mem_Mspace.1 Gm.2
  have hV : toL2 ω a b Φ₀ ⟨(Gm : GA → ℂ), hGc.1⟩ ∈ V := hE'K _ hGE
  have hne0 : toL2 ω a b Φ₀ ⟨(Gm : GA → ℂ), hGc.1⟩ ≠ 0 := by
    intro h0
    apply hGm0
    apply Subtype.ext
    show (Gm : GA → ℂ) = 0
    have : cls ω a b Φ₀ _ hGc = cls ω a b Φ₀ 0 (cuspSubmodule ω a b Φ₀).zero_mem := by
      rw [cls_zero]
      exact Subtype.ext h0
    exact eq_of_cls_eq hΦ _ _ hGc (cuspSubmodule ω a b Φ₀).zero_mem this
  have e1 : WhittakerBlock.casimir1 (Gm : GA → ℂ) = c₁ • (Gm : GA → ℂ) := congrArg Subtype.val hc1
  have e2 : WhittakerBlock.casimir2 (Gm : GA → ℂ) = c₂ • (Gm : GA → ℂ) := congrArg Subtype.val hc2
  have e3 : WhittakerBlock.casimir3 (Gm : GA → ℂ) = c₃ • (Gm : GA → ℂ) := congrArg Subtype.val hc3
  exact ⟨c₁, c₂, c₃, (Gm : GA → ℂ), hGc, hV, hne0, hGs, hGr, e1, e2, e3⟩

end LanglandsTunnell.CubicInduction.SlabL2SEED
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction.SlabL2SEED"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction.CuspClassAction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction.SlabL2SEED"

end ClassActionBlock
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction.CuspClassAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction.SlabL2SEED"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.LanglandsTunnell.CubicInduction"

theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ : IsSlabDomain a b Φ₀)
    (V : Submodule ℂ (Carrier a b Φ₀))
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (hne : V ≠ ⊥)
    (hsm : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V) :
    ∃ (c₁ c₂ c₃ : ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀),
      toL2 ω a b Φ₀ ⟨G, hG.1⟩ ∈ V ∧ toL2 ω a b Φ₀ ⟨G, hG.1⟩ ≠ 0 ∧
        WhittakerBlock.IsArchSmooth3 G ∧
        (∀ l : List (Fin 3 × Fin 3), Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G)) ∧
        WhittakerBlock.casimir1 G = c₁ • G ∧ WhittakerBlock.casimir2 G = c₂ • G ∧
          WhittakerBlock.casimir3 G = c₃ • G :=
  SlabL2SEED.main hω hΦ V hgen hne hsm

end S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator (solution)
