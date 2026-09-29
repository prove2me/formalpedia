-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/359486d6-2c5d-5a4c-abda-451f84190852

import Definitions.Def_LanglandsTunnell_CubicInduction_SpectralOperators3
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_toL2_translateRight_mem_of_mem_of_isClosed
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_isSmoothingKernel_isCompactOperator_isCuspLift3_apply_ne_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isCompactOperator_cuspidalSubspace_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one"
p2m_attr_erase "simp" "AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

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

end IsDenseIsometricAction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction"

end DenseUnitaryExtension
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous toL2_translateRight_mem_of_mem_of_isClosed exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace SlabL2.exists_isSmoothingKernel_isCompactOperator_isCuspLift3_apply_ne_zero SlabL2.le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension"

end Pins
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous toL2_translateRight_mem_of_mem_of_isClosed exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace SlabL2.exists_isSmoothingKernel_isCompactOperator_isCuspLift3_apply_ne_zero SlabL2.le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact"
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

end LanglandsTunnell.CubicInduction.CuspClassAction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction.CuspClassAction"

end ClassActionBlock
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction.CuspClassAction"

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous toL2_translateRight_mem_of_mem_of_isClosed exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace SlabL2.exists_isSmoothingKernel_isCompactOperator_isCuspLift3_apply_ne_zero SlabL2.le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact"
namespace B2bBody
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2
open LanglandsTunnell.CubicInduction.CuspClassAction
open scoped InnerProductSpace

variable {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} {a b : ℝ} {Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}

theorem exists_translate_lift_mem (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (hΦ₀ : IsSlabDomain a b Φ₀)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : archComponent3 (𝓞 ℚ) ℚ g = 1) :
    ∃ u ∈ spectralOperators3 ω a b Φ₀,
      ∀ (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀),
        ∃ hGg : translateRight g G ∈ cuspFunctions ω a b Φ₀,
          u ⟨toL2 ω a b Φ₀ ⟨G, hG.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hG⟩ =
            ⟨toL2 ω a b Φ₀ ⟨translateRight g G, hGg.1⟩,
              toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hGg⟩ := by
  have hR : RightTranslationLaw ω a b Φ₀ := fun F hF =>
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ F hF
  refine ⟨rbar hR g, ?_, fun G hG => ⟨(hR G hG).fst g, Subtype.ext (rbar_toL2 hR g G hG)⟩⟩
  left
  left
  exact ⟨g, Or.inl hg, fun F hF => ⟨(hR F hF).fst g, rbar_toL2 hR g F hF⟩⟩

theorem exists_smoothing_lift_mem (hΦ₀ : IsSlabDomain a b Φ₀)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ) :
    ∃ r ∈ spectralOperators3 ω a b Φ₀,
      ∀ (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀),
        ∃ hGφ : smoothingOperator φ G ∈ cuspFunctions ω a b Φ₀,
          r ⟨toL2 ω a b Φ₀ ⟨G, hG.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hG⟩ =
            ⟨toL2 ω a b Φ₀ ⟨smoothingOperator φ G, hGφ.1⟩,
              toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hGφ⟩ := by
  obtain ⟨T, -, hT⟩ := exists_isCompactOperator_cuspidalSubspace_smoothingOperator ω a b Φ₀ hΦ₀
    exists_mul_eq_unipotent_mul_diagonal_mul_compact φ hφ
  refine ⟨T, Or.inl (Or.inr ⟨φ, hφ, hT⟩), fun G hG => ?_⟩
  obtain ⟨hRG, e⟩ := hT G hG
  exact ⟨hRG, Subtype.ext e⟩

end LanglandsTunnell.CubicInduction.B2bBody
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction.CuspClassAction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction.CuspClassAction"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.LanglandsTunnell.CubicInduction.B2bBody"
open scoped InnerProductSpace

theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (W : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)) (_hWc : IsClosed (W : Set ↥(cuspidalSubspace ω a b Φ₀)))
    (_hWi : ∀ r ∈ spectralOperators3 ω a b Φ₀, ∀ x ∈ W, r x ∈ W)
    (V : Submodule ℂ (Carrier a b Φ₀)) (_hV : V = W.map (cuspidalSubspace ω a b Φ₀).subtype) :
      V = (Submodule.span ℂ
        (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure ∧
      (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
        ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
          toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V) ∧
      (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
        ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
          toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V) := by
  classical
  subst _hV

  have htr : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀),
      toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ W.map (cuspidalSubspace ω a b Φ₀).subtype →
      ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
        toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ W.map (cuspidalSubspace ω a b Φ₀).subtype := by
    intro F hF hFV g hg
    obtain ⟨w, hw, hwF⟩ := Submodule.mem_map.mp hFV
    have hw' : (⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ :
        ↥(cuspidalSubspace ω a b Φ₀)) ∈ W := by
      have : w = ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ :=
        Subtype.ext hwF
      exact this ▸ hw
    have hmem := toL2_translateRight_mem_of_mem_of_isClosed ω _hω a b Φ₀ _hΦ₀ (spectralOperators3 ω a b Φ₀)
      (fun g hg => exists_translate_lift_mem _hω _hΦ₀ g hg) (fun φ hφ => exists_smoothing_lift_mem _hΦ₀ φ hφ)
      W _hWc _hWi F hF hw' g hg
    exact Submodule.mem_map.mpr ⟨_, hmem, rfl⟩

  have hsm : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀),
      toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ W.map (cuspidalSubspace ω a b Φ₀).subtype →
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ W.map (cuspidalSubspace ω a b Φ₀).subtype := by
    intro F hF hFV φ hφ hφF
    obtain ⟨w, hw, hwF⟩ := Submodule.mem_map.mp hFV
    obtain ⟨r, hr, hrl⟩ := exists_smoothing_lift_mem (ω := ω) _hΦ₀ φ hφ
    obtain ⟨hRF, e⟩ := hrl F hF
    have hw' : (⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ :
        ↥(cuspidalSubspace ω a b Φ₀)) ∈ W := by
      have : w = ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ :=
        Subtype.ext hwF
      exact this ▸ hw
    have hmem := _hWi r hr _ hw'
    rw [e] at hmem
    exact Submodule.mem_map.mpr ⟨_, hmem, rfl⟩
  refine ⟨?_, htr, hsm⟩

  set V : Submodule ℂ (Carrier a b Φ₀) := W.map (cuspidalSubspace ω a b Φ₀).subtype with hVdef
  set S : Set (Carrier a b Φ₀) := toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V} with hSdef
  set V' : Submodule ℂ (Carrier a b Φ₀) := (Submodule.span ℂ S).topologicalClosure with hV'def

  have hVc : IsClosed (V : Set (Carrier a b Φ₀)) := by
    rw [hVdef, Submodule.map_coe]
    exact (IsClosed.isClosedEmbedding_subtypeVal (isClosed_cuspidalSubspace ω a b Φ₀)).isClosedMap _ _hWc

  have hSV : S ⊆ V := by
    rintro _ ⟨f, hf, rfl⟩
    exact hf.2
  have hV'V : V' ≤ V := Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 hSV) hVc

  have hcuspV' : ∀ (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀),
      toL2 ω a b Φ₀ ⟨G, hG.1⟩ ∈ V → toL2 ω a b Φ₀ ⟨G, hG.1⟩ ∈ V' := fun G hG hGV =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨G, hG.1⟩, ⟨hG, hGV⟩, rfl⟩)

  have hgen' : V' = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V'})).topologicalClosure := by
    apply le_antisymm
    · refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨f, ⟨hf.1, hcuspV' _ hf.1 hf.2⟩, rfl⟩
    · refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) (Submodule.isClosed_topologicalClosure _)
      rintro _ ⟨f, hf, rfl⟩
      exact hf.2
  have htr' : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V' →
      ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
        toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V' := fun F hF hFV' g hg =>
    hcuspV' _ hg (htr F hF (hV'V hFV') g hg)
  have hsm' : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V' →
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V' := fun F hF hFV' φ hφ hφF =>
    hcuspV' _ hφF (hsm F hF (hV'V hFV') φ hφ hφF)

  obtain ⟨-, hW'c, hW'i⟩ :=
    SlabL2.le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap ω _hω a b Φ₀ _hΦ₀ V'
      hgen' htr' hsm' (V'.comap (cuspidalSubspace ω a b Φ₀).subtype) rfl
  set W' : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀) := V'.comap (cuspidalSubspace ω a b Φ₀).subtype with hW'def
  have hW'W : W' ≤ W := by
    intro w hw
    obtain ⟨w₀, hw₀, heq⟩ := Submodule.mem_map.mp (hV'V hw)
    have hww : w₀ = w := Subtype.ext heq
    exact hww ▸ hw₀

  haveI : CompleteSpace ↥W' := hW'c.completeSpace_coe
  haveI : W'.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace W'
  have hWW' : W ≤ W' := by
    intro w hw
    set u : ↥(cuspidalSubspace ω a b Φ₀) := w - W'.starProjection w with hudef
    have huo : u ∈ W'ᗮ := Submodule.sub_starProjection_mem_orthogonal w
    have hPw : W'.starProjection w ∈ W' := Submodule.starProjection_apply_mem W' w
    have huW : u ∈ W := W.sub_mem hw (hW'W hPw)
    have hu0 : u = 0 := by
      by_contra hu
      obtain ⟨φ, hφ, T, -, hT, hTu⟩ :=
        SlabL2.exists_isSmoothingKernel_isCompactOperator_isCuspLift3_apply_ne_zero ω _hω a b Φ₀ _hΦ₀ u hu

      have hTuW : T u ∈ W := _hWi T (Or.inl (Or.inr ⟨φ, hφ, hT⟩)) u huW
      obtain ⟨CN, hrep⟩ :=
        exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace ω _hω a b Φ₀ _hΦ₀ φ hφ T hT
      obtain ⟨F, hF, hTuF, -⟩ := hrep u
      have hTuW' : T u ∈ W' := by
        show ((T u : ↥(cuspidalSubspace ω a b Φ₀)) : Carrier a b Φ₀) ∈ V'
        rw [hTuF]
        refine hcuspV' F hF ?_
        rw [← hTuF]
        exact Submodule.mem_map.mpr ⟨T u, hTuW, rfl⟩

      have hadjR : ContinuousLinearMap.adjoint T ∈ spectralOperators3 ω a b Φ₀ :=
        Or.inr ⟨T, Or.inr ⟨φ, hφ, hT⟩, fun x y => ContinuousLinearMap.adjoint_inner_left T y x⟩
      have hTTu : ContinuousLinearMap.adjoint T (T u) ∈ W' := hW'i _ hadjR _ hTuW'
      have h0 : ⟪T u, T u⟫_ℂ = 0 := by
        rw [← ContinuousLinearMap.adjoint_inner_left]
        exact (Submodule.mem_orthogonal W' u).mp huo _ hTTu
      exact hTu (inner_self_eq_zero.mp h0)
    have : w = W'.starProjection w := by
      rw [← sub_eq_zero]
      exact hu0
    rw [this]
    exact hPw

  apply le_antisymm _ hV'V
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
  exact hWW' hw

end S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3 (solution)
