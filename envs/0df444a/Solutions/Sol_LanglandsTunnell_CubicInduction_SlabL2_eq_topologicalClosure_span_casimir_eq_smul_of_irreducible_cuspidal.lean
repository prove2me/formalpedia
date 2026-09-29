-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2b5bbc1c-f4ee-5076-806e-4d746c8f0fb1

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.Matrix
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_LanglandsTunnell_CubicInduction_toL2_translateRight_mem_of_mem_of_isClosed
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_translateRight
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_archDeriv_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isCompactOperator_cuspidalSubspace_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction"

end DenseUnitaryExtension
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 WhittakerBlock.archDeriv WhittakerBlock.casimir1 WhittakerBlock.casimir2 WhittakerBlock.casimir3 toL2_translateRight_mem_of_mem_of_isClosed exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous WhittakerBlock.casimir_translateRight exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension"

end Pins
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 WhittakerBlock.archDeriv WhittakerBlock.casimir1 WhittakerBlock.casimir2 WhittakerBlock.casimir3 toL2_translateRight_mem_of_mem_of_isClosed exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous WhittakerBlock.casimir_translateRight exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 WhittakerBlock.archDeriv WhittakerBlock.casimir1 WhittakerBlock.casimir2 WhittakerBlock.casimir3 toL2_translateRight_mem_of_mem_of_isClosed exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous WhittakerBlock.casimir_translateRight exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact"
namespace SlabL2B1
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2"
open LanglandsTunnell.CubicInduction.CuspClassAction

attribute [local instance] NumberField.AdelicHaar.glBorel

local notation "GA" => AdelicGL 3 (𝓞 ℚ) ℚ

variable (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))

theorem comm_archRealLift3 {t : GA} (ht : archComponent3 (𝓞 ℚ) ℚ t = 1)
    (e : Fin 3 → Fin 3 → ℝ) : t * WhittakerBlock.archRealLift3 e = WhittakerBlock.archRealLift3 e * t := by
  have hfin : ((t : GA) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      AutomorphicForm.finMatrixInclN (Fin 3) ℚ
        ((t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)) := by
    ext i j
    refine Prod.ext ?_ rfl
    exact congrArg (fun u : GL (Fin 3) (InfiniteAdeleRing ℚ) => (u : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j)
      ht
  by_cases hu : IsUnit (WhittakerBlock.archRealMat3 e)
  · refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, WhittakerBlock.archRealLift3, dif_pos hu, IsUnit.unit_spec, hfin]
    exact (AutomorphicForm.archMatrixInclN_mul_finMatrixInclN (Fin 3) ℚ _ _).symm
  · rw [WhittakerBlock.archRealLift3, dif_neg hu, mul_one, one_mul]

theorem isArchSmooth3_translateRight {k : GA} (hk : archComponent3 (𝓞 ℚ) ℚ k = 1) {f : GA → ℂ}
    (hf : WhittakerBlock.IsArchSmooth3 f) : WhittakerBlock.IsArchSmooth3 (translateRight k f) := by
  intro g
  have : (fun e : Fin 3 → Fin 3 → ℝ => translateRight k f (g * WhittakerBlock.archRealLift3 e)) =
      fun e => f (g * k * WhittakerBlock.archRealLift3 e) := by
    funext e
    rw [translateRight_apply, mul_assoc, mul_assoc, comm_archRealLift3 hk]
  rw [this]
  exact hf (g * k)

theorem archDeriv_translateRight {k : GA} (hk : archComponent3 (𝓞 ℚ) ℚ k = 1) (f : GA → ℂ) (i j : Fin 3) :
    WhittakerBlock.archDeriv i j (translateRight k f) = translateRight k (WhittakerBlock.archDeriv i j f) := by
  funext g
  simp only [WhittakerBlock.archDeriv, translateRight]
  congr 1
  funext s
  rw [mul_assoc, mul_assoc, comm_archRealLift3 hk]

theorem foldr_archDeriv_translateRight {k : GA} (hk : archComponent3 (𝓞 ℚ) ℚ k = 1) (f : GA → ℂ)
    (l : List (Fin 3 × Fin 3)) :
    l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (translateRight k f) =
      translateRight k (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) f) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.foldr_cons, ih, archDeriv_translateRight hk]

theorem continuous_translateRight (k : GA) {H : GA → ℂ} (hH : Continuous H) : Continuous (translateRight k H) :=
  hH.comp (continuous_id.mul continuous_const)

theorem translateRight_smul (k : GA) (c : ℂ) (f : GA → ℂ) : translateRight k (c • f) = c • translateRight k f :=
  rfl

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

theorem exists_foldr_archDeriv_smoothingOperator (φ F : GA → ℂ) (hφ : IsSmoothingKernel φ)
    (hF : LocallyIntegrable F (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (l : List (Fin 3 × Fin 3)) :
    ∃ ψ : GA → ℂ, IsSmoothingKernel ψ ∧
      l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (smoothingOperator φ F) = smoothingOperator ψ F := by
  induction l with
  | nil => exact ⟨φ, hφ, rfl⟩
  | cons p l ih =>
    obtain ⟨ψ, hψ, h⟩ := ih
    obtain ⟨hψ', h'⟩ := archDeriv_smoothingOperator ψ F hψ hF p.1 p.2
    exact ⟨_, hψ', by rw [List.foldr_cons, h, h']⟩

def eigSet (V : Submodule ℂ (Carrier a b Φ₀)) (c₁ c₂ c₃ : ℂ) : Set ↥(automorphicSubmodule ω a b Φ₀) :=
  {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V ∧
    WhittakerBlock.IsArchSmooth3 (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∧
    (∀ l : List (Fin 3 × Fin 3),
      Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
    WhittakerBlock.casimir1 (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = c₁ • (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∧
    WhittakerBlock.casimir2 (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = c₂ • (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∧
    WhittakerBlock.casimir3 (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = c₃ • (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)}

def Wsp (V : Submodule ℂ (Carrier a b Φ₀)) (c₁ c₂ c₃ : ℂ) : Submodule ℂ (Carrier a b Φ₀) :=
  (Submodule.span ℂ (toL2 ω a b Φ₀ '' eigSet ω a b Φ₀ V c₁ c₂ c₃)).topologicalClosure

variable {ω a b Φ₀}

theorem toL2_mk_coe (f : ↥(automorphicSubmodule ω a b Φ₀)) (h : (f : GA → ℂ) ∈ automorphicSubmodule ω a b Φ₀) :
    toL2 ω a b Φ₀ ⟨(f : GA → ℂ), h⟩ = toL2 ω a b Φ₀ f := rfl

theorem translateRight_mem_eigSet {V : Submodule ℂ (Carrier a b Φ₀)}
    (htr : ∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ (g : GA) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V)
    {c₁ c₂ c₃ : ℂ} {k : GA} (hk : archComponent3 (𝓞 ℚ) ℚ k = 1)
    {f : GA → ℂ} {hf0 : f ∈ automorphicSubmodule ω a b Φ₀}
    (hf : (⟨f, hf0⟩ : ↥(automorphicSubmodule ω a b Φ₀)) ∈ eigSet ω a b Φ₀ V c₁ c₂ c₃)
    (h : translateRight k f ∈ cuspFunctions ω a b Φ₀) :
    (⟨translateRight k f, h.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) ∈ eigSet ω a b Φ₀ V c₁ c₂ c₃ := by
  obtain ⟨hfc, hfV, hfs, hfr, h1, h2, h3⟩ := hf
  have hfc' : f ∈ cuspFunctions ω a b Φ₀ := hfc
  have hfs' : WhittakerBlock.IsArchSmooth3 f := hfs
  have hfr' : ∀ l : List (Fin 3 × Fin 3),
      Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) f) := hfr
  have h1' : WhittakerBlock.casimir1 f = c₁ • f := h1
  have h2' : WhittakerBlock.casimir2 f = c₂ • f := h2
  have h3' : WhittakerBlock.casimir3 f = c₃ • f := h3
  have hcas := WhittakerBlock.casimir_translateRight f hfs' k
  have hmem : (⟨translateRight k f, h.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) ∈ cuspMembers ω a b Φ₀ :=
    (mem_cuspMembers_iff ω a b Φ₀ _).2 h
  have hV' : toL2 ω a b Φ₀ ⟨translateRight k f, h.1⟩ ∈ V := htr f hfc' hfV k h
  have hs' : WhittakerBlock.IsArchSmooth3 (translateRight k f) := isArchSmooth3_translateRight hk hfs'
  have hr' : ∀ l : List (Fin 3 × Fin 3),
      Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (translateRight k f)) := fun l => by
    rw [foldr_archDeriv_translateRight hk]
    exact continuous_translateRight k (hfr' l)
  have hc1 : WhittakerBlock.casimir1 (translateRight k f) = c₁ • translateRight k f := by
    rw [hcas.1, h1', translateRight_smul]
  have hc2 : WhittakerBlock.casimir2 (translateRight k f) = c₂ • translateRight k f := by
    rw [hcas.2.1, h2', translateRight_smul]
  have hc3 : WhittakerBlock.casimir3 (translateRight k f) = c₃ • translateRight k f := by
    rw [hcas.2.2, h3', translateRight_smul]
  exact ⟨hmem, hV', hs', hr', hc1, hc2, hc3⟩

theorem smoothingOperator_mem_eigSet {V : Submodule ℂ (Carrier a b Φ₀)}
    (hsm : ∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ φ : GA → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V)
    {c₁ c₂ c₃ : ℂ} {φ : GA → ℂ} (hφ : IsSmoothingKernel φ)
    {f : GA → ℂ} {hf0 : f ∈ automorphicSubmodule ω a b Φ₀}
    (hf : (⟨f, hf0⟩ : ↥(automorphicSubmodule ω a b Φ₀)) ∈ eigSet ω a b Φ₀ V c₁ c₂ c₃)
    (h : smoothingOperator φ f ∈ cuspFunctions ω a b Φ₀) :
    (⟨smoothingOperator φ f, h.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) ∈ eigSet ω a b Φ₀ V c₁ c₂ c₃ := by
  obtain ⟨hfc, hfV, hfs, hfr, h1, h2, h3⟩ := hf
  have hfc' : f ∈ cuspFunctions ω a b Φ₀ := hfc
  have hfs' : WhittakerBlock.IsArchSmooth3 f := hfs
  have hfr' : ∀ l : List (Fin 3 × Fin 3),
      Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) f) := hfr
  have h1' : WhittakerBlock.casimir1 f = c₁ • f := h1
  have h2' : WhittakerBlock.casimir2 f = c₂ • f := h2
  have h3' : WhittakerBlock.casimir3 f = c₃ • f := h3
  have hli := locallyIntegrable_of_continuous hfc'.2.1
  have hcas := casimir_smoothingOperator φ f hφ hfs' hfr'
  have hmem : (⟨smoothingOperator φ f, h.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) ∈ cuspMembers ω a b Φ₀ :=
    (mem_cuspMembers_iff ω a b Φ₀ _).2 h
  have hV' : toL2 ω a b Φ₀ ⟨smoothingOperator φ f, h.1⟩ ∈ V := hsm f hfc' hfV φ hφ h
  have hs' : WhittakerBlock.IsArchSmooth3 (smoothingOperator φ f) :=
    (continuous_and_isArchSmooth3_smoothingOperator φ f hφ hli).2
  have hr' : ∀ l : List (Fin 3 × Fin 3),
      Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (smoothingOperator φ f)) := fun l => by
    obtain ⟨ψ, hψ, hl⟩ := exists_foldr_archDeriv_smoothingOperator φ f hφ hli l
    rw [hl]
    exact (continuous_and_isArchSmooth3_smoothingOperator ψ f hψ hli).1
  have hc1 : WhittakerBlock.casimir1 (smoothingOperator φ f) = c₁ • smoothingOperator φ f := by
    rw [hcas.1, h1', smoothingOperator_smul]
  have hc2 : WhittakerBlock.casimir2 (smoothingOperator φ f) = c₂ • smoothingOperator φ f := by
    rw [hcas.2.1, h2', smoothingOperator_smul]
  have hc3 : WhittakerBlock.casimir3 (smoothingOperator φ f) = c₃ • smoothingOperator φ f := by
    rw [hcas.2.2, h3', smoothingOperator_smul]
  exact ⟨hmem, hV', hs', hr', hc1, hc2, hc3⟩

def Lifts (op : (GA → ℂ) → (GA → ℂ)) (T : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)) :
    Prop :=
  ∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), ∃ hRF : op F ∈ cuspFunctions ω a b Φ₀,
    (T ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ : Carrier a b Φ₀) =
      toL2 ω a b Φ₀ ⟨op F, hRF.1⟩

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

theorem lifts_stable {V : Submodule ℂ (Carrier a b Φ₀)} {c₁ c₂ c₃ : ℂ}
    {op : (GA → ℂ) → (GA → ℂ)} {T : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)}
    (hT : Lifts op T)
    (hop : ∀ (f : GA → ℂ) (hf0 : f ∈ automorphicSubmodule ω a b Φ₀),
      (⟨f, hf0⟩ : ↥(automorphicSubmodule ω a b Φ₀)) ∈ eigSet ω a b Φ₀ V c₁ c₂ c₃ →
      ∀ h : op f ∈ cuspFunctions ω a b Φ₀,
        (⟨op f, h.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) ∈ eigSet ω a b Φ₀ V c₁ c₂ c₃) :
    ∀ x ∈ (Wsp ω a b Φ₀ V c₁ c₂ c₃).comap (cuspidalSubspace ω a b Φ₀).subtype,
      T x ∈ (Wsp ω a b Φ₀ V c₁ c₂ c₃).comap (cuspidalSubspace ω a b Φ₀).subtype := by
  have hsubD : toL2 ω a b Φ₀ '' eigSet ω a b Φ₀ V c₁ c₂ c₃ ⊆ cuspidalSubspace ω a b Φ₀ := by
    rintro _ ⟨f, hf, rfl⟩
    exact toL2_mem_cuspidalSubspace ω a b Φ₀ hf.1
  have key := comap_subtype_topologicalClosure_span (cuspidalSubspace ω a b Φ₀) _ hsubD
  intro x hx
  unfold Wsp at hx ⊢
  rw [key] at hx ⊢
  have hZc : IsClosed (((Submodule.span ℂ ((cuspidalSubspace ω a b Φ₀).subtype ⁻¹'
      (toL2 ω a b Φ₀ '' eigSet ω a b Φ₀ V c₁ c₂ c₃))).topologicalClosure.comap
        (T : ↥(cuspidalSubspace ω a b Φ₀) →ₗ[ℂ] ↥(cuspidalSubspace ω a b Φ₀))) :
          Set ↥(cuspidalSubspace ω a b Φ₀)) := by
    rw [Submodule.comap_coe]
    exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  have hle : Submodule.span ℂ ((cuspidalSubspace ω a b Φ₀).subtype ⁻¹'
      (toL2 ω a b Φ₀ '' eigSet ω a b Φ₀ V c₁ c₂ c₃)) ≤
      (Submodule.span ℂ ((cuspidalSubspace ω a b Φ₀).subtype ⁻¹'
        (toL2 ω a b Φ₀ '' eigSet ω a b Φ₀ V c₁ c₂ c₃))).topologicalClosure.comap
          (T : ↥(cuspidalSubspace ω a b Φ₀) →ₗ[ℂ] ↥(cuspidalSubspace ω a b Φ₀)) := by
    refine Submodule.span_le.2 fun y hy => ?_
    obtain ⟨⟨f, hf0⟩, hf, hfy⟩ := hy
    have hfc : f ∈ cuspFunctions ω a b Φ₀ := hf.1
    obtain ⟨hRF, hTy⟩ := hT f hfc
    have hy' : y = ⟨toL2 ω a b Φ₀ ⟨f, hfc.1⟩,
        toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hfc⟩ := Subtype.ext hfy.symm
    show T y ∈ (Submodule.span ℂ ((cuspidalSubspace ω a b Φ₀).subtype ⁻¹'
      (toL2 ω a b Φ₀ '' eigSet ω a b Φ₀ V c₁ c₂ c₃))).topologicalClosure
    refine Submodule.le_topologicalClosure _ (Submodule.subset_span ?_)
    show ((T y : ↥(cuspidalSubspace ω a b Φ₀)) : Carrier a b Φ₀) ∈ toL2 ω a b Φ₀ '' eigSet ω a b Φ₀ V c₁ c₂ c₃
    rw [hy', hTy]
    exact ⟨⟨op f, hRF.1⟩, hop f hf0 hf hRF, rfl⟩
  exact Submodule.topologicalClosure_minimal _ hle hZc hx

theorem exists_lifts_translateRight (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (hΦ : IsSlabDomain a b Φ₀)
    (k : GA) : ∃ u : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀), Lifts (translateRight k) u := by
  have hR : RightTranslationLaw ω a b Φ₀ := fun F hF =>
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ F hF
  exact ⟨rbar hR k, fun F hF => ⟨(hR F hF).fst k, rbar_toL2 hR k F hF⟩⟩

theorem exists_lifts_smoothingOperator (hΦ : IsSlabDomain a b Φ₀) {φ : GA → ℂ} (hφ : IsSmoothingKernel φ) :
    ∃ T : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀), Lifts (smoothingOperator φ) T := by
  obtain ⟨T, _, hT⟩ := exists_isCompactOperator_cuspidalSubspace_smoothingOperator ω a b Φ₀ hΦ
    exists_mul_eq_unipotent_mul_diagonal_mul_compact φ hφ
  exact ⟨T, hT⟩

theorem main
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (hΦ : IsSlabDomain a b Φ₀)
    (V : Submodule ℂ (Carrier a b Φ₀))
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (htr : ∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ (g : GA) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V)
    (hsm : ∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ φ : GA → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V)
    (hmin : ∀ W : Submodule ℂ (Carrier a b Φ₀), W ≤ V →
      W = (Submodule.span ℂ
        (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ W})).topologicalClosure →
      (∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ W →
        ∀ (g : GA) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ W) →
      (∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ W →
        ∀ φ : GA → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
          toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ W) →
      W = ⊥ ∨ W = V)
    (c₁ c₂ c₃ : ℂ) (G : GA → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀)
    (hGV : toL2 ω a b Φ₀ ⟨G, hG.1⟩ ∈ V) (hG0 : toL2 ω a b Φ₀ ⟨G, hG.1⟩ ≠ 0)
    (hGs : WhittakerBlock.IsArchSmooth3 G)
    (hGreg : (∀ l : List (Fin 3 × Fin 3), Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G)))
    (hGc : WhittakerBlock.casimir1 G = c₁ • G ∧ WhittakerBlock.casimir2 G = c₂ • G ∧
          WhittakerBlock.casimir3 G = c₃ • G) :
    V = Wsp ω a b Φ₀ V c₁ c₂ c₃ := by
  have hVc : IsClosed (V : Set (Carrier a b Φ₀)) := by
    rw [hgen]
    exact Submodule.isClosed_topologicalClosure _
  have hUV : toL2 ω a b Φ₀ '' eigSet ω a b Φ₀ V c₁ c₂ c₃ ⊆ V := by
    rintro _ ⟨f, hf, rfl⟩
    exact hf.2.1
  have hWV : Wsp ω a b Φ₀ V c₁ c₂ c₃ ≤ V := Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 hUV) hVc
  have hGU : (⟨G, hG.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) ∈ eigSet ω a b Φ₀ V c₁ c₂ c₃ :=
    ⟨hG, hGV, hGs, hGreg, hGc.1, hGc.2.1, hGc.2.2⟩
  have hGW : toL2 ω a b Φ₀ ⟨G, hG.1⟩ ∈ Wsp ω a b Φ₀ V c₁ c₂ c₃ :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, hGU, rfl⟩)
  have hWne : Wsp ω a b Φ₀ V c₁ c₂ c₃ ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hGW
    exact hG0 hGW
  have hgenW : Wsp ω a b Φ₀ V c₁ c₂ c₃ = (Submodule.span ℂ (toL2 ω a b Φ₀ ''
      {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ Wsp ω a b Φ₀ V c₁ c₂ c₃})).topologicalClosure := by
    apply le_antisymm
    · refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨f, ⟨hf.1, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, rfl⟩)⟩, rfl⟩
    · refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) (Submodule.isClosed_topologicalClosure _)
      rintro _ ⟨f, hf, rfl⟩
      exact hf.2

  let R₀ : Set (↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)) :=
    {T | (∃ k : GA, archComponent3 (𝓞 ℚ) ℚ k = 1 ∧ Lifts (translateRight k) T) ∨
      (∃ φ : GA → ℂ, IsSmoothingKernel φ ∧ Lifts (smoothingOperator φ) T)}
  have hWcC : IsClosed (((Wsp ω a b Φ₀ V c₁ c₂ c₃).comap (cuspidalSubspace ω a b Φ₀).subtype) :
      Set ↥(cuspidalSubspace ω a b Φ₀)) := by
    rw [Submodule.comap_coe]
    exact (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  have hWcS : ∀ r ∈ R₀, ∀ x ∈ (Wsp ω a b Φ₀ V c₁ c₂ c₃).comap (cuspidalSubspace ω a b Φ₀).subtype,
      r x ∈ (Wsp ω a b Φ₀ V c₁ c₂ c₃).comap (cuspidalSubspace ω a b Φ₀).subtype := by
    rintro r (⟨k, hk, hr⟩ | ⟨φ, hφ, hr⟩) x hx
    · exact lifts_stable hr (fun f hf0 hf h => translateRight_mem_eigSet htr hk hf h) x hx
    · exact lifts_stable hr (fun f hf0 hf h => smoothingOperator_mem_eigSet hsm hφ hf h) x hx
  have hU0 : ∀ g : GA, archComponent3 (𝓞 ℚ) ℚ g = 1 → ∃ u ∈ R₀,
      ∀ (G : GA → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀),
        ∃ hGg : translateRight g G ∈ cuspFunctions ω a b Φ₀,
          u ⟨toL2 ω a b Φ₀ ⟨G, hG.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hG⟩ =
            ⟨toL2 ω a b Φ₀ ⟨translateRight g G, hGg.1⟩,
              toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hGg⟩ := by
    intro g hg
    obtain ⟨u, hu⟩ := exists_lifts_translateRight (ω := ω) hω hΦ g
    refine ⟨u, Or.inl ⟨g, hg, hu⟩, fun G hG => ?_⟩
    obtain ⟨hGg, h⟩ := hu G hG
    exact ⟨hGg, Subtype.ext h⟩
  have hS0 : ∀ φ : GA → ℂ, IsSmoothingKernel φ → ∃ r ∈ R₀,
      ∀ (G : GA → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀),
        ∃ hGφ : smoothingOperator φ G ∈ cuspFunctions ω a b Φ₀,
          r ⟨toL2 ω a b Φ₀ ⟨G, hG.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hG⟩ =
            ⟨toL2 ω a b Φ₀ ⟨smoothingOperator φ G, hGφ.1⟩,
              toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hGφ⟩ := by
    intro φ hφ
    obtain ⟨r, hr⟩ := exists_lifts_smoothingOperator (ω := ω) hΦ hφ
    refine ⟨r, Or.inr ⟨φ, hφ, hr⟩, fun G hG => ?_⟩
    obtain ⟨hGφ, h⟩ := hr G hG
    exact ⟨hGφ, Subtype.ext h⟩
  have htrW : ∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ Wsp ω a b Φ₀ V c₁ c₂ c₃ →
      ∀ (g : GA) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
        toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ Wsp ω a b Φ₀ V c₁ c₂ c₃ := by
    intro F hF hFW g hg
    exact toL2_translateRight_mem_of_mem_of_isClosed ω hω a b Φ₀ hΦ R₀ hU0 hS0
      ((Wsp ω a b Φ₀ V c₁ c₂ c₃).comap (cuspidalSubspace ω a b Φ₀).subtype) hWcC hWcS F hF hFW g hg
  have hsmW : ∀ (F : GA → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ Wsp ω a b Φ₀ V c₁ c₂ c₃ →
      ∀ φ : GA → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ Wsp ω a b Φ₀ V c₁ c₂ c₃ := by
    intro F hF hFW φ hφk hφ
    obtain ⟨T, hT⟩ := exists_lifts_smoothingOperator (ω := ω) hΦ hφk
    obtain ⟨hRF, hTF⟩ := hT F hF
    have hx := hWcS T (Or.inr ⟨φ, hφk, hT⟩) _ (show (⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩,
      toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ : ↥(cuspidalSubspace ω a b Φ₀)) ∈
        (Wsp ω a b Φ₀ V c₁ c₂ c₃).comap (cuspidalSubspace ω a b Φ₀).subtype from hFW)
    rw [Submodule.mem_comap, Submodule.subtype_apply, hTF] at hx
    exact hx
  rcases hmin (Wsp ω a b Φ₀ V c₁ c₂ c₃) hWV hgenW htrW hsmW with h | h
  · exact absurd h hWne
  · exact h.symm

end LanglandsTunnell.CubicInduction.SlabL2B1
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction.CuspClassAction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction.CuspClassAction"

end ClassActionBlock
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension.IsDenseIsometricAction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.DenseUnitaryExtension P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction.CuspClassAction"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal.LanglandsTunnell.CubicInduction"

theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ : IsSlabDomain a b Φ₀)
    (V : Submodule ℂ (Carrier a b Φ₀))
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (hne : V ≠ ⊥)
    (htr : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
        toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V)
    (hsm : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V)
    (hmin : ∀ W : Submodule ℂ (Carrier a b Φ₀), W ≤ V →
      W = (Submodule.span ℂ
        (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ W})).topologicalClosure →
      (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ W →
        ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
          toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ W) →
      (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ W →
        ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
          toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ W) →
      W = ⊥ ∨ W = V)
    (c₁ c₂ c₃ : ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀)
    (hGV : toL2 ω a b Φ₀ ⟨G, hG.1⟩ ∈ V) (hG0 : toL2 ω a b Φ₀ ⟨G, hG.1⟩ ≠ 0)
    (hGs : WhittakerBlock.IsArchSmooth3 G)
    (hGreg : (∀ l : List (Fin 3 × Fin 3), Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G)))
    (hGc : WhittakerBlock.casimir1 G = c₁ • G ∧ WhittakerBlock.casimir2 G = c₂ • G ∧
          WhittakerBlock.casimir3 G = c₃ • G) :
    V = (Submodule.span ℂ (toL2 ω a b Φ₀ ''
        {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V ∧
          WhittakerBlock.IsArchSmooth3 (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∧
          (∀ l : List (Fin 3 × Fin 3),
            Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
          WhittakerBlock.casimir1 (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = c₁ • (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∧
          WhittakerBlock.casimir2 (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = c₂ • (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∧
          WhittakerBlock.casimir3 (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = c₃ • (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)})).topologicalClosure :=
  SlabL2B1.main hω hΦ V hgen htr hsm hmin c₁ c₂ c₃ G hG hGV hG0 hGs hGreg hGc

end S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_span_casimir_eq_smul_of_irreducible_cuspidal (solution)
