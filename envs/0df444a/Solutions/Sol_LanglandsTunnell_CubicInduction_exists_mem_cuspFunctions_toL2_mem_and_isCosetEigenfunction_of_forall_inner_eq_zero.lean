-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f1088c22-e0db-52f4-92f5-ddbf971eb425

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_SpectralOperators3
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.Matrix
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isCompactOperator_cuspidalSubspace_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_isSmoothingKernel_isCompactOperator_isCuspLift3_apply_ne_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_toL2_eq_zero_of_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_isSmoothingKernel_star_inv_and_inner_toL2_smoothingOperator_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one"
p2m_attr_erase "simp" "AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.CubicInduction.fnTwist3_apply"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction"

end DenseUnitaryExtension
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 localMaximalCompact3 componentAt3 IsCuspidalAlongP21 IsCuspidalAlongP12 heckeGen1 heckeGen2 IsCosetEigenfunction IsRightInvariant localToAdelic3 exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace eq_zero_of_toL2_eq_zero_of_continuous isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension"

end Pins
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 localMaximalCompact3 componentAt3 IsCuspidalAlongP21 IsCuspidalAlongP12 heckeGen1 heckeGen2 IsCosetEigenfunction IsRightInvariant localToAdelic3 exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace eq_zero_of_toL2_eq_zero_of_continuous isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 localMaximalCompact3 componentAt3 IsCuspidalAlongP21 IsCuspidalAlongP12 heckeGen1 heckeGen2 IsCosetEigenfunction IsRightInvariant localToAdelic3 exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace eq_zero_of_toL2_eq_zero_of_continuous isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator"
namespace SlabL2ER
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2"
open LanglandsTunnell.CubicInduction.CuspClassAction
open scoped InnerProductSpace

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

theorem starProjection_comm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (K : Submodule ℂ E)
    [K.HasOrthogonalProjection] (T : E →L[ℂ] E) (hK : ∀ x ∈ K, T x ∈ K) (hKo : ∀ x ∈ Kᗮ, T x ∈ Kᗮ) (x : E) :
    K.starProjection (T x) = T (K.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal (hK _ (K.starProjection_apply_mem x)) ?_
  rw [← map_sub]
  exact hKo _ (K.sub_starProjection_mem_orthogonal x)

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction.CuspClassAction"

variable {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} {a b : ℝ} {Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}

def genSet (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (V : Submodule ℂ (Carrier a b Φ₀)) : Set ↥(automorphicSubmodule ω a b Φ₀) :=
  {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V}

def Kof (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (V : Submodule ℂ (Carrier a b Φ₀)) : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀) :=
  V.comap (cuspidalSubspace ω a b Φ₀).subtype

theorem mem_Kof {V : Submodule ℂ (Carrier a b Φ₀)} {x : ↥(cuspidalSubspace ω a b Φ₀)} :
    x ∈ Kof ω a b Φ₀ V ↔ (x : Carrier a b Φ₀) ∈ V := Iff.rfl

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

theorem isCuspLift3_rbar (hR : RightTranslationLaw ω a b Φ₀) (g : GA) :
    IsCuspLift3 ω a b Φ₀ (translateRight g) (rbar hR g) :=
  fun F hF => ⟨(hR F hF).fst g, rbar_toL2 hR g F hF⟩

theorem rbar_mem_Kof {V : Submodule ℂ (Carrier a b Φ₀)}
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (htr : ∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ (g : GA) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V)
    (hR : RightTranslationLaw ω a b Φ₀) (g : GA) :
    ∀ x ∈ Kof ω a b Φ₀ V, rbar hR g x ∈ Kof ω a b Φ₀ V :=
  lifts_stable hgen (isCuspLift3_rbar hR g) fun f hf hfV h => htr f hf hfV g h

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

theorem rbar_mem_Kof_orthogonal {V : Submodule ℂ (Carrier a b Φ₀)}
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (htr : ∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ (g : GA) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V)
    (hR : RightTranslationLaw ω a b Φ₀) (g : GA) :
    ∀ y ∈ (Kof ω a b Φ₀ V)ᗮ, rbar hR g y ∈ (Kof ω a b Φ₀ V)ᗮ := by
  intro y hy
  rw [Submodule.mem_orthogonal]
  intro x hx
  rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_rbar]
  exact Submodule.inner_right_of_mem_orthogonal (rbar_mem_Kof hgen htr hR g⁻¹ x hx) hy

theorem rbar_sum_eq_smul_of_sum_translateRight_eq_smul (hR : RightTranslationLaw ω a b Φ₀)
    {ι : Type} [Fintype ι] (r : ι → GA) (lam : ℂ)
    (G : GA → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀)
    (hrel : (∑ i, translateRight (r i) G) = lam • G) :
    (∑ i, rbar hR (r i) ⟨toL2 ω a b Φ₀ ⟨G, hG.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hG⟩) =
      lam • ⟨toL2 ω a b Φ₀ ⟨G, hG.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hG⟩ := by
  have hmi : ∀ i, translateRight (r i) G ∈ automorphicSubmodule ω a b Φ₀ := fun i => ((hR G hG).fst (r i)).1
  apply Subtype.ext
  rw [Submodule.coe_sum, Submodule.coe_smul]
  have h1 : ∀ i, ((rbar hR (r i) ⟨toL2 ω a b Φ₀ ⟨G, hG.1⟩,
      toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hG⟩ : ↥(cuspidalSubspace ω a b Φ₀)) :
        Carrier a b Φ₀) = toL2 ω a b Φ₀ ⟨translateRight (r i) G, hmi i⟩ := fun i => rbar_toL2 hR (r i) G hG
  simp_rw [h1]
  rw [← map_sum, ← map_smul]
  congr 1
  apply Subtype.ext
  rw [Submodule.coe_sum, Submodule.coe_smul]
  exact hrel

theorem sum_translateRight_eq_smul_of_rbar_sum_eq_smul (hΦ : IsSlabDomain a b Φ₀) (hR : RightTranslationLaw ω a b Φ₀)
    {ι : Type} [Fintype ι] (r : ι → GA) (lam : ℂ)
    (G : GA → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀)
    (hrel : (∑ i, rbar hR (r i) ⟨toL2 ω a b Φ₀ ⟨G, hG.1⟩,
        toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hG⟩) =
      lam • ⟨toL2 ω a b Φ₀ ⟨G, hG.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hG⟩) :
    (∑ i, translateRight (r i) G) = lam • G := by
  have hmi : ∀ i, translateRight (r i) G ∈ cuspFunctions ω a b Φ₀ := fun i => (hR G hG).fst (r i)
  have hmem : (∑ i, translateRight (r i) G) - lam • G ∈ automorphicSubmodule ω a b Φ₀ :=
    Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ => (hmi i).1) (Submodule.smul_mem _ lam hG.1)
  have hcont : Continuous ((∑ i, translateRight (r i) G) - lam • G) := by
    have hs : Continuous (∑ i, translateRight (r i) G) := by
      have : (∑ i, translateRight (r i) G) = fun g => ∑ i, translateRight (r i) G g := by
        funext g
        exact Finset.sum_apply g _ _
      rw [this]
      exact continuous_finsetSum _ fun i _ => (hmi i).2.1
    exact hs.sub (hG.2.1.const_smul lam)
  have hclass : toL2 ω a b Φ₀ ⟨(∑ i, translateRight (r i) G) - lam • G, hmem⟩ = 0 := by
    have hcoe := congrArg Subtype.val hrel
    rw [Submodule.coe_sum, Submodule.coe_smul] at hcoe
    have h1 : ∀ i, ((rbar hR (r i) ⟨toL2 ω a b Φ₀ ⟨G, hG.1⟩,
        toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hG⟩ : ↥(cuspidalSubspace ω a b Φ₀)) :
          Carrier a b Φ₀) = toL2 ω a b Φ₀ ⟨translateRight (r i) G, (hmi i).1⟩ := fun i => rbar_toL2 hR (r i) G hG
    simp_rw [h1] at hcoe
    have hmk : (⟨(∑ i, translateRight (r i) G) - lam • G, hmem⟩ : ↥(automorphicSubmodule ω a b Φ₀)) =
        (∑ i, (⟨translateRight (r i) G, (hmi i).1⟩ : ↥(automorphicSubmodule ω a b Φ₀))) -
          lam • (⟨G, hG.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) := by
      apply Subtype.ext
      rw [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul]
    rw [hmk, map_sub, map_sum, map_smul, sub_eq_zero]
    exact hcoe
  have hzero := eq_zero_of_toL2_eq_zero_of_continuous ω a b Φ₀ hΦ _ hmem hcont hclass
  exact sub_eq_zero.1 hzero

theorem main
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ) (hΦ : IsSlabDomain a b Φ₀)
    (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀) (hF0 : toL2 ω a b Φ₀ ⟨F, hF.1⟩ ≠ 0)
    (hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F)
    (hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) F (lam1 p))
    (hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) F (lam2 p))
    (V : Submodule ℂ (Carrier a b Φ₀))
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (hne : V ≠ ⊥)
    (htr : ∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ (g : GA) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V)
    (hsm : ∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ φ : GA → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V)
    (hVF : ∀ (G : GA → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨G, hG.1⟩ ∈ V →
      ∀ (F' : GA → ℂ) (hF' : F' ∈ cuspFunctions ω a b Φ₀),
        (∀ (g : GA) (hg : translateRight g F ∈ automorphicSubmodule ω a b Φ₀),
          ⟪toL2 ω a b Φ₀ ⟨translateRight g F, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0) →
        ∀ (g : GA) (hg : translateRight g G ∈ automorphicSubmodule ω a b Φ₀),
          ⟪toL2 ω a b Φ₀ ⟨translateRight g G, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 ℚ)), S ⊆ S' ∧
      ∃ (F₁ : GA → ℂ) (hF₁ : F₁ ∈ cuspFunctions ω a b Φ₀),
        toL2 ω a b Φ₀ ⟨F₁, hF₁.1⟩ ∈ V ∧ toL2 ω a b Φ₀ ⟨F₁, hF₁.1⟩ ≠ 0 ∧
        (∀ p, p ∉ S' → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F₁) ∧
        (∀ p, p ∉ S' → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen1 p)) F₁ (lam1 p)) ∧
        (∀ p, p ∉ S' → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen2 p)) F₁ (lam2 p)) := by
  classical

  have hR : RightTranslationLaw ω a b Φ₀ := fun G hG =>
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ G hG

  let K : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀) := Kof ω a b Φ₀ V
  have hKc : IsClosed (K : Set ↥(cuspidalSubspace ω a b Φ₀)) := isClosed_Kof hgen
  haveI : CompleteSpace K := hKc.completeSpace_coe

  let xF : ↥(cuspidalSubspace ω a b Φ₀) :=
    ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩
  have hPU : ∀ (g : GA) (x : ↥(cuspidalSubspace ω a b Φ₀)),
      K.starProjection (rbar hR g x) = rbar hR g (K.starProjection x) := fun g x =>
    starProjection_comm K (rbar hR g) (rbar_mem_Kof hgen htr hR g) (rbar_mem_Kof_orthogonal hgen htr hR g) x

  have hu0 : K.starProjection xF ≠ 0 := by
    intro hu
    have hxF : xF ∈ Kᗮ := by
      rw [Submodule.starProjection_apply] at hu
      exact Submodule.orthogonalProjection_eq_zero_iff.1 (Subtype.ext (by simpa using hu))
    have hgen0 : ∀ (G : GA → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨G, hG.1⟩ ∈ V →
        toL2 ω a b Φ₀ ⟨G, hG.1⟩ = 0 := by
      intro G hG hGV
      have horth : ∀ (g : GA) (hg : translateRight g F ∈ automorphicSubmodule ω a b Φ₀),
          ⟪toL2 ω a b Φ₀ ⟨translateRight g F, hg⟩, toL2 ω a b Φ₀ ⟨G, hG.1⟩⟫_ℂ = 0 := by
        intro g hg
        have h1 : toL2 ω a b Φ₀ ⟨translateRight g F, hg⟩ = ((rbar hR g xF : ↥(cuspidalSubspace ω a b Φ₀)) :
            Carrier a b Φ₀) := (rbar_toL2 hR g F hF).symm
        let xG : ↥(cuspidalSubspace ω a b Φ₀) :=
          ⟨toL2 ω a b Φ₀ ⟨G, hG.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hG⟩
        have hxG : xG ∈ K := hGV
        have h2 : toL2 ω a b Φ₀ ⟨G, hG.1⟩ = ((xG : ↥(cuspidalSubspace ω a b Φ₀)) : Carrier a b Φ₀) := rfl
        rw [h1, h2, ← Submodule.coe_inner]
        exact Submodule.inner_left_of_mem_orthogonal hxG (rbar_mem_Kof_orthogonal hgen htr hR g xF hxF)
      have h1G : translateRight 1 G ∈ automorphicSubmodule ω a b Φ₀ := by
        rw [translateRight_one]; exact hG.1
      have h := hVF G hG hGV G hG horth 1 h1G
      have h' : toL2 ω a b Φ₀ ⟨translateRight 1 G, h1G⟩ = toL2 ω a b Φ₀ ⟨G, hG.1⟩ := by
        congr 1
        exact Subtype.ext (translateRight_one G)
      rw [h'] at h
      exact inner_self_eq_zero.1 h
    apply hne
    rw [hgen]
    have hspan : Submodule.span ℂ (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V}) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨⟨G, hG0⟩, hG, rfl⟩
      exact hgen0 G hG.1 hG.2
    rw [hspan]
    exact IsClosed.submodule_topologicalClosure_eq (by
      rw [Submodule.bot_coe]
      exact isClosed_singleton)

  have hu0' : (K.starProjection xF : ↥(cuspidalSubspace ω a b Φ₀)) ≠ 0 := hu0
  obtain ⟨φ, hφ, T, _, hT, hTu⟩ :=
    exists_isSmoothingKernel_isCompactOperator_isCuspLift3_apply_ne_zero ω hω a b Φ₀ hΦ _ hu0'

  obtain ⟨α, K', hα, hK', hcof, hφeq⟩ := hφ
  have hfin : Set.Finite {p : HeightOneSpectrum (𝓞 ℚ) | ¬ (K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p)} :=
    Filter.eventually_cofinite.1 hcof
  refine ⟨S ∪ hfin.toFinset, Finset.subset_union_left, ?_⟩
  have hS' : ∀ p, p ∉ S ∪ hfin.toFinset → p ∉ S ∧ K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p := by
    intro p hp
    rw [Finset.mem_union, not_or] at hp
    refine ⟨hp.1, ?_⟩
    by_contra hne'
    exact hp.2 (hfin.mem_toFinset.2 hne')
  have hφp : ∀ p, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p →
      ∀ g : GA, φ g ≠ 0 → componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
    intro p hp g hg
    rw [hφeq g] at hg
    have hind : Set.indicator {x : GA | ∀ q, componentAt3 (𝓞 ℚ) ℚ q x ∈ K' q} (fun _ => (1 : ℂ)) g ≠ 0 :=
      fun h0 => hg (by rw [h0, mul_zero])
    have hmem : g ∈ {x : GA | ∀ q, componentAt3 (𝓞 ℚ) ℚ q x ∈ K' q} := by
      by_contra hn
      exact hind (Set.indicator_of_notMem hn _)
    rw [← hp]
    exact hmem p
  have hφ' : IsSmoothingKernel φ := ⟨α, K', hα, hK', hcof, hφeq⟩

  obtain ⟨hφs, hadj0⟩ := isSmoothingKernel_star_inv_and_inner_toL2_smoothingOperator_eq ω hω a b Φ₀ hΦ φ hφ'
  obtain ⟨Ts, _, hTs⟩ := exists_isCompactOperator_cuspidalSubspace_smoothingOperator ω a b Φ₀ hΦ
    exists_mul_eq_unipotent_mul_diagonal_mul_compact _ hφs
  have hadj : ∀ x y : ↥(cuspidalSubspace ω a b Φ₀), ⟪T x, y⟫_ℂ = ⟪x, Ts y⟫_ℂ := by
    have hD := (isDenseIsometricAction hR).denseRange_gen
    have hgen_eq : ∀ c : ↥(cuspMemberSubmodule ω a b Φ₀), (isDenseIsometricAction hR).gen c =
        ⟨toL2 ω a b Φ₀ ⟨((c : ↥(automorphicSubmodule ω a b Φ₀)) : GA → ℂ), c.2.1⟩,
          toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ c.2⟩ := by
      intro c
      apply Subtype.ext
      show classOf c = toL2 ω a b Φ₀ ⟨((c : ↥(automorphicSubmodule ω a b Φ₀)) : GA → ℂ), c.2.1⟩
      exact classOf_apply c
    have hcc : ∀ c c' : ↥(cuspMemberSubmodule ω a b Φ₀),
        ⟪T ((isDenseIsometricAction hR).gen c), (isDenseIsometricAction hR).gen c'⟫_ℂ =
          ⟪(isDenseIsometricAction hR).gen c, Ts ((isDenseIsometricAction hR).gen c')⟫_ℂ := by
      intro c c'
      obtain ⟨hRc, hTc⟩ := hT (((c : ↥(automorphicSubmodule ω a b Φ₀)) : GA → ℂ)) c.2
      obtain ⟨hRc', hTc'⟩ := hTs (((c' : ↥(automorphicSubmodule ω a b Φ₀)) : GA → ℂ)) c'.2
      rw [hgen_eq c, hgen_eq c', Submodule.coe_inner, Submodule.coe_inner, hTc, hTc']
      exact hadj0 (((c : ↥(automorphicSubmodule ω a b Φ₀)) : GA → ℂ))
        (((c' : ↥(automorphicSubmodule ω a b Φ₀)) : GA → ℂ)) c.2 c'.2 hRc hRc'
    have step1 : ∀ c' : ↥(cuspMemberSubmodule ω a b Φ₀), ∀ x : ↥(cuspidalSubspace ω a b Φ₀),
        ⟪T x, (isDenseIsometricAction hR).gen c'⟫_ℂ = ⟪x, Ts ((isDenseIsometricAction hR).gen c')⟫_ℂ := by
      intro c'
      have := hD.equalizer
        ((T.continuous).inner continuous_const)
        (continuous_id.inner continuous_const)
        (funext fun c => hcc c c')
      exact fun x => congrFun this x
    intro x y
    have := hD.equalizer
      (continuous_const.inner continuous_id)
      (continuous_const.inner (Ts.continuous))
      (funext fun c' => step1 c' x)
    exact congrFun this y
  have hKT : ∀ x ∈ K, T x ∈ K := smoothing_mem_Kof hgen hsm hφ' hT
  have hKTs : ∀ x ∈ K, Ts x ∈ K := smoothing_mem_Kof hgen hsm hφs hTs
  have hKoT : ∀ y ∈ Kᗮ, T y ∈ Kᗮ := by
    intro y hy
    rw [Submodule.mem_orthogonal]
    intro x hx
    apply inner_eq_zero_symm.1
    rw [hadj]
    exact Submodule.inner_left_of_mem_orthogonal (hKTs x hx) hy
  have hPT : ∀ x : ↥(cuspidalSubspace ω a b Φ₀), K.starProjection (T x) = T (K.starProjection x) := fun x =>
    starProjection_comm K T hKT hKoT x

  set F₂ : GA → ℂ := smoothingOperator φ F with hF₂def
  obtain ⟨hF₂, hTF⟩ := hT F hF
  obtain ⟨CN, hrep⟩ := exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace ω hω a b Φ₀ hΦ φ hφ'
    T hT
  obtain ⟨F₁, hF₁, hF₁eq, _⟩ := hrep (K.starProjection xF)
  let xF₂ : ↥(cuspidalSubspace ω a b Φ₀) :=
    ⟨toL2 ω a b Φ₀ ⟨F₂, hF₂.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF₂⟩
  let xF₁ : ↥(cuspidalSubspace ω a b Φ₀) :=
    ⟨toL2 ω a b Φ₀ ⟨F₁, hF₁.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF₁⟩
  have hTxF : T xF = xF₂ := Subtype.ext hTF
  have hx₁ : xF₁ = K.starProjection xF₂ := by
    apply Subtype.ext
    show toL2 ω a b Φ₀ ⟨F₁, hF₁.1⟩ = ((K.starProjection xF₂ : ↥(cuspidalSubspace ω a b Φ₀)) : Carrier a b Φ₀)
    rw [← hF₁eq, ← hTxF, hPT]
  refine ⟨F₁, hF₁, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have : T (K.starProjection xF) ∈ K := hKT _ (K.starProjection_apply_mem xF)
    rw [← hF₁eq]
    exact this
  ·
    rw [← hF₁eq]
    intro h0
    exact hTu (Subtype.ext h0)

  · intro p hp g k hk
    obtain ⟨hpS, hpK⟩ := hS' p hp
    have h2 := (isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator p (lam1 p) (lam2 p)
      φ hφ' (hφp p hpK) 1 (map_one _) F hF.2.1 (hK p hpS) (hT1 p hpS) (hT2 p hpS)).1
    rw [translateRight_one] at h2
    have hrel2 : (∑ _i : Unit, translateRight k F₂) = (1 : ℂ) • F₂ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul, one_smul]
      funext x
      exact h2 x k hk
    have hc2 := rbar_sum_eq_smul_of_sum_translateRight_eq_smul hR (fun _ : Unit => k) 1 F₂ hF₂ hrel2
    have hc1 : (∑ _i : Unit, rbar hR k xF₁) = (1 : ℂ) • xF₁ := by
      rw [hx₁, ← hPU, ← map_smul, ← hc2, map_sum]
    have hrel1 := sum_translateRight_eq_smul_of_rbar_sum_eq_smul hΦ hR (fun _ : Unit => k) 1 F₁ hF₁ hc1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul, one_smul] at hrel1
    exact congrFun hrel1 g
  · intro p hp ι _ reps hreps g
    obtain ⟨hpS, hpK⟩ := hS' p hp
    have h2 := (isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator p (lam1 p) (lam2 p)
      φ hφ' (hφp p hpK) 1 (map_one _) F hF.2.1 (hK p hpS) (hT1 p hpS) (hT2 p hpS)).2.1
    rw [translateRight_one] at h2
    have h2' := h2 ι reps hreps
    have hrel2 : (∑ i, translateRight (reps i) F₂) = lam1 p • F₂ := by
      funext x
      rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact h2' x
    have hc2 := rbar_sum_eq_smul_of_sum_translateRight_eq_smul hR reps (lam1 p) F₂ hF₂ hrel2
    have hc1 : (∑ i, rbar hR (reps i) xF₁) = lam1 p • xF₁ := by
      rw [hx₁, ← map_smul, ← hc2, map_sum]
      exact Finset.sum_congr rfl fun i _ => (hPU (reps i) xF₂).symm
    have hrel1 := sum_translateRight_eq_smul_of_rbar_sum_eq_smul hΦ hR reps (lam1 p) F₁ hF₁ hc1
    have := congrFun hrel1 g
    rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this
  · intro p hp ι _ reps hreps g
    obtain ⟨hpS, hpK⟩ := hS' p hp
    have h2 := (isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator p (lam1 p) (lam2 p)
      φ hφ' (hφp p hpK) 1 (map_one _) F hF.2.1 (hK p hpS) (hT1 p hpS) (hT2 p hpS)).2.2
    rw [translateRight_one] at h2
    have h2' := h2 ι reps hreps
    have hrel2 : (∑ i, translateRight (reps i) F₂) = lam2 p • F₂ := by
      funext x
      rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact h2' x
    have hc2 := rbar_sum_eq_smul_of_sum_translateRight_eq_smul hR reps (lam2 p) F₂ hF₂ hrel2
    have hc1 : (∑ i, rbar hR (reps i) xF₁) = lam2 p • xF₁ := by
      rw [hx₁, ← map_smul, ← hc2, map_sum]
      exact Finset.sum_congr rfl fun i _ => (hPU (reps i) xF₂).symm
    have hrel1 := sum_translateRight_eq_smul_of_rbar_sum_eq_smul hΦ hR reps (lam2 p) F₁ hF₁ hc1
    have := congrFun hrel1 g
    rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this

end LanglandsTunnell.CubicInduction.SlabL2ER
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction.CuspClassAction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction.CuspClassAction"

end ClassActionBlock
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction.CuspClassAction"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.LanglandsTunnell.CubicInduction"
open scoped InnerProductSpace

theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀) (_hF0 : toL2 ω a b Φ₀ ⟨F, hF.1⟩ ≠ 0)
    (_hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F)
    (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) F (lam1 p))
    (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) F (lam2 p))
    (V : Submodule ℂ (Carrier a b Φ₀))
    (_hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (_hne : V ≠ ⊥)
    (_htr : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
        toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V)
    (_hsm : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V)
    (_hVF : ∀ (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨G, hG.1⟩ ∈ V →
      ∀ (F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF' : F' ∈ cuspFunctions ω a b Φ₀),
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ automorphicSubmodule ω a b Φ₀),
          ⟪toL2 ω a b Φ₀ ⟨translateRight g F, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0) →
        ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g G ∈ automorphicSubmodule ω a b Φ₀),
          ⟪toL2 ω a b Φ₀ ⟨translateRight g G, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 ℚ)), S ⊆ S' ∧
      ∃ (F₁ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF₁ : F₁ ∈ cuspFunctions ω a b Φ₀),
        toL2 ω a b Φ₀ ⟨F₁, hF₁.1⟩ ∈ V ∧ toL2 ω a b Φ₀ ⟨F₁, hF₁.1⟩ ≠ 0 ∧
        (∀ p, p ∉ S' → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F₁) ∧
        (∀ p, p ∉ S' → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen1 p)) F₁ (lam1 p)) ∧
        (∀ p, p ∉ S' → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen2 p)) F₁ (lam2 p)) :=
  SlabL2ER.main S _hω lam1 lam2 _hΦ₀ F hF _hF0 _hK _hT1 _hT2 V _hgen _hne _htr _hsm _hVF

end S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero (solution)
