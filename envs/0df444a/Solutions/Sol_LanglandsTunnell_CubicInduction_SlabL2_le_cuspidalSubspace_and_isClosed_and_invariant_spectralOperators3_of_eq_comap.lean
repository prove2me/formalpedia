-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2506121c-a93f-5353-b769-5ea05fdf5d59

import Definitions.Def_LanglandsTunnell_CubicInduction_SpectralOperators3
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_isSmoothingKernel_star_inv_and_inner_toL2_smoothingOperator_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_continuousLinearMap_eq_of_forall_toL2_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isCompactOperator_cuspidalSubspace_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one"
p2m_attr_erase "simp" "AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 IsCuspidalAlongP21 IsCuspidalAlongP12 exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous SlabL2.isSmoothingKernel_star_inv_and_inner_toL2_smoothingOperator_eq SlabL2.continuousLinearMap_eq_of_forall_toL2_eq exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact"
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

end Pins

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 IsCuspidalAlongP21 IsCuspidalAlongP12 exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous SlabL2.isSmoothingKernel_star_inv_and_inner_toL2_smoothingOperator_eq SlabL2.continuousLinearMap_eq_of_forall_toL2_eq exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact"
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

end LanglandsTunnell.CubicInduction.CuspClassAction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 IsCuspidalAlongP21 IsCuspidalAlongP12 exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous SlabL2.isSmoothingKernel_star_inv_and_inner_toL2_smoothingOperator_eq SlabL2.continuousLinearMap_eq_of_forall_toL2_eq exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact"
namespace B2aBody
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2
open LanglandsTunnell.CubicInduction.CuspClassAction
open scoped InnerProductSpace

variable {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} {a b : ℝ} {Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}

theorem inner_eq_inner_of_forall_norm_add_smul_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {X Y X' Y' : E} (h : ∀ c : ℂ, ‖X' + c • Y'‖ = ‖X + c • Y‖) : ⟪X', Y'⟫_ℂ = ⟪X, Y⟫_ℂ := by
  have h₁ : ‖X' + Y'‖ = ‖X + Y‖ := by simpa using h 1
  have h₂ : ‖X' - Y'‖ = ‖X - Y‖ := by simpa [sub_eq_add_neg] using h (-1)
  have h₃ : ‖X' - (RCLike.I : ℂ) • Y'‖ = ‖X - (RCLike.I : ℂ) • Y‖ := by
    simpa [sub_eq_add_neg] using h (-(RCLike.I : ℂ))
  have h₄ : ‖X' + (RCLike.I : ℂ) • Y'‖ = ‖X + (RCLike.I : ℂ) • Y‖ := h (RCLike.I : ℂ)
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  simp only [h₁, h₂, h₃, h₄]

theorem inner_toL2_translateRight_translateRight
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (hΦ₀ : IsSlabDomain a b Φ₀)
    {x y : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hx : x ∈ cuspFunctions ω a b Φ₀)
    (hy : y ∈ cuspFunctions ω a b Φ₀) (v : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hxv : translateRight v x ∈ automorphicSubmodule ω a b Φ₀)
    (hyv : translateRight v y ∈ automorphicSubmodule ω a b Φ₀) :
    ⟪toL2 ω a b Φ₀ ⟨translateRight v x, hxv⟩, toL2 ω a b Φ₀ ⟨translateRight v y, hyv⟩⟫_ℂ =
      ⟪toL2 ω a b Φ₀ ⟨x, hx.1⟩, toL2 ω a b Φ₀ ⟨y, hy.1⟩⟫_ℂ := by
  refine inner_eq_inner_of_forall_norm_add_smul_eq fun c => ?_
  have hxy : x + c • y ∈ cuspFunctions ω a b Φ₀ :=
    (cuspSubmodule ω a b Φ₀).add_mem hx ((cuspSubmodule ω a b Φ₀).smul_mem c hy)
  obtain ⟨hmem, hnorm, -⟩ :=
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ (x + c • y) hxy
  have hv : translateRight v (x + c • y) ∈ automorphicSubmodule ω a b Φ₀ := (hmem v).1
  have e : toL2 ω a b Φ₀ ⟨translateRight v (x + c • y), hv⟩ =
      toL2 ω a b Φ₀ ⟨translateRight v x, hxv⟩ + c • toL2 ω a b Φ₀ ⟨translateRight v y, hyv⟩ := by
    have e' : (⟨translateRight v (x + c • y), hv⟩ : ↥(automorphicSubmodule ω a b Φ₀)) =
        ⟨translateRight v x, hxv⟩ + c • ⟨translateRight v y, hyv⟩ :=
      Subtype.ext (by funext g; simp [translateRight])
    rw [e', map_add, map_smul]
  have e₀ : toL2 ω a b Φ₀ ⟨x + c • y, hxy.1⟩ = toL2 ω a b Φ₀ ⟨x, hx.1⟩ + c • toL2 ω a b Φ₀ ⟨y, hy.1⟩ := by
    have e' : (⟨x + c • y, hxy.1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) = ⟨x, hx.1⟩ + c • ⟨y, hy.1⟩ := rfl
    rw [e', map_add, map_smul]
  rw [← e, ← e₀]
  exact hnorm v

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

theorem comap_stable (V : Submodule ℂ (Carrier a b Φ₀))
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (T : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀))
    (hT : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ((T ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ :
        ↥(cuspidalSubspace ω a b Φ₀)) : Carrier a b Φ₀) ∈ V) :
    ∀ x ∈ V.comap (cuspidalSubspace ω a b Φ₀).subtype, T x ∈ V.comap (cuspidalSubspace ω a b Φ₀).subtype := by
  have hsubD : toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V} ⊆ cuspidalSubspace ω a b Φ₀ := by
    rintro _ ⟨f, hf, rfl⟩
    exact toL2_mem_cuspidalSubspace ω a b Φ₀ hf.1
  have key := comap_subtype_topologicalClosure_span (cuspidalSubspace ω a b Φ₀) _ hsubD
  set S : Set ↥(cuspidalSubspace ω a b Φ₀) :=
    (cuspidalSubspace ω a b Φ₀).subtype ⁻¹' (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})
    with hSdef
  have hW : V.comap (cuspidalSubspace ω a b Φ₀).subtype = (Submodule.span ℂ S).topologicalClosure := by
    conv_lhs => rw [hgen]
    exact key
  intro x hx
  rw [hW] at hx ⊢
  have hZc : IsClosed (((Submodule.span ℂ S).topologicalClosure.comap
      (T : ↥(cuspidalSubspace ω a b Φ₀) →ₗ[ℂ] ↥(cuspidalSubspace ω a b Φ₀))) : Set ↥(cuspidalSubspace ω a b Φ₀)) := by
    rw [Submodule.comap_coe]
    exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  have hle : Submodule.span ℂ S ≤ (Submodule.span ℂ S).topologicalClosure.comap
      (T : ↥(cuspidalSubspace ω a b Φ₀) →ₗ[ℂ] ↥(cuspidalSubspace ω a b Φ₀)) := by
    refine Submodule.span_le.2 fun y hy => ?_
    rw [hSdef] at hy
    obtain ⟨f, ⟨hf, hfV⟩, hfy⟩ := hy
    have hfc : (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ cuspFunctions ω a b Φ₀ := hf
    have hy' : y = ⟨toL2 ω a b Φ₀ ⟨(f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), hfc.1⟩,
        toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hfc⟩ := Subtype.ext hfy.symm
    have hTy : ((T y : ↥(cuspidalSubspace ω a b Φ₀)) : Carrier a b Φ₀) ∈ V := by
      rw [hy']
      exact hT _ hfc hfV
    show T y ∈ (Submodule.span ℂ S).topologicalClosure
    rw [← hW]
    exact hTy
  exact Submodule.topologicalClosure_minimal _ hle hZc hx

end LanglandsTunnell.CubicInduction.B2aBody
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell.CubicInduction.CuspClassAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell.CubicInduction.CuspClassAction"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.LanglandsTunnell.CubicInduction.B2aBody"
open scoped InnerProductSpace

theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (V : Submodule ℂ (Carrier a b Φ₀))
    (_hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (_htr : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
        toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V)
    (_hsm : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V)
    (W : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)) (_hW : W = V.comap (cuspidalSubspace ω a b Φ₀).subtype) :
    V ≤ cuspidalSubspace ω a b Φ₀ ∧ IsClosed (W : Set ↥(cuspidalSubspace ω a b Φ₀)) ∧
      ∀ r ∈ spectralOperators3 ω a b Φ₀, ∀ x ∈ W, r x ∈ W := by
  subst _hW
  have hle : V ≤ cuspidalSubspace ω a b Φ₀ := by
    rw [_hgen, cuspidalSubspace_def]
    exact Submodule.topologicalClosure_mono (Submodule.span_mono (Set.image_mono fun f hf => hf.1))
  have hVc : IsClosed (V : Set (Carrier a b Φ₀)) := by
    rw [_hgen]
    exact Submodule.isClosed_topologicalClosure _
  refine ⟨hle, ?_, ?_⟩
  · rw [Submodule.comap_coe]
    exact hVc.preimage continuous_subtype_val
  intro r hr
  rcases hr with hr | ⟨S, hS, hadj⟩
  · rcases hr with ⟨h, -, hlift⟩ | ⟨φ, hφ, hlift⟩
    · refine comap_stable V _hgen r fun F hF hFV => ?_
      obtain ⟨hRF, e⟩ := hlift F hF
      rw [e]
      exact _htr F hF hFV h hRF
    · refine comap_stable V _hgen r fun F hF hFV => ?_
      obtain ⟨hRF, e⟩ := hlift F hF
      rw [e]
      exact _hsm F hF hFV φ hφ hRF
  ·
    rcases hS with ⟨h, -, hlift⟩ | ⟨φ, hφ, hlift⟩
    ·
      refine comap_stable V _hgen r fun F hF hFV => ?_
      obtain ⟨hmemF, -, -⟩ :=
        exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω _hω a b Φ₀ _hΦ₀ F hF
      have hRR : translateRight h (translateRight h⁻¹ F) = F := by
        rw [← translateRight_mul, mul_inv_cancel, translateRight_one]
      have hRRm : translateRight h (translateRight h⁻¹ F) ∈ automorphicSubmodule ω a b Φ₀ := by
        rw [hRR]; exact hF.1
      have key : r ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ =
          ⟨toL2 ω a b Φ₀ ⟨translateRight h⁻¹ F, (hmemF h⁻¹).1⟩,
            toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ (hmemF h⁻¹)⟩ := by
        apply ext_inner_right ℂ
        intro z
        rw [hadj]
        have hfun := SlabL2.continuousLinearMap_eq_of_forall_toL2_eq ω a b Φ₀
          ((innerSL ℂ (⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩,
            toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ : ↥(cuspidalSubspace ω a b Φ₀))).comp S)
          (innerSL ℂ (⟨toL2 ω a b Φ₀ ⟨translateRight h⁻¹ F, (hmemF h⁻¹).1⟩,
            toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ (hmemF h⁻¹)⟩ : ↥(cuspidalSubspace ω a b Φ₀)))
          (fun G hG => by
            obtain ⟨hRG, e⟩ := hlift G hG
            simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
            rw [Submodule.coe_inner, Submodule.coe_inner, e]
            have e2 := inner_toL2_translateRight_translateRight _hω _hΦ₀ (hmemF h⁻¹) hG h hRRm hRG.1
            have e3 : toL2 ω a b Φ₀ ⟨translateRight h (translateRight h⁻¹ F), hRRm⟩ = toL2 ω a b Φ₀ ⟨F, hF.1⟩ := by
              congr 1
              exact Subtype.ext hRR
            rw [e3] at e2
            exact e2)
        simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using congrArg (fun f => f z) hfun
      rw [key]
      exact _htr F hF hFV h⁻¹ (hmemF h⁻¹)
    ·
      obtain ⟨hφs, hadjφ⟩ :=
        SlabL2.isSmoothingKernel_star_inv_and_inner_toL2_smoothingOperator_eq ω _hω a b Φ₀ _hΦ₀ φ hφ
      obtain ⟨Ts, -, hTs⟩ := exists_isCompactOperator_cuspidalSubspace_smoothingOperator ω a b Φ₀ _hΦ₀
        exists_mul_eq_unipotent_mul_diagonal_mul_compact (fun g => star (φ g⁻¹)) hφs
      refine comap_stable V _hgen r fun F hF hFV => ?_
      obtain ⟨hRF, -⟩ := hTs F hF
      have key : r ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ =
          ⟨toL2 ω a b Φ₀ ⟨smoothingOperator (fun g => star (φ g⁻¹)) F, hRF.1⟩,
            toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hRF⟩ := by
        apply ext_inner_right ℂ
        intro z
        rw [hadj]
        have hfun := SlabL2.continuousLinearMap_eq_of_forall_toL2_eq ω a b Φ₀
          ((innerSL ℂ (⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩,
            toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ : ↥(cuspidalSubspace ω a b Φ₀))).comp S)
          (innerSL ℂ (⟨toL2 ω a b Φ₀ ⟨smoothingOperator (fun g => star (φ g⁻¹)) F, hRF.1⟩,
            toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hRF⟩ : ↥(cuspidalSubspace ω a b Φ₀)))
          (fun G hG => by
            obtain ⟨hRG, e⟩ := hlift G hG
            simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
            rw [Submodule.coe_inner, Submodule.coe_inner, e, ← inner_conj_symm, hadjφ G F hG hF hRG hRF,
              inner_conj_symm])
        simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using congrArg (fun f => f z) hfun
      rw [key]
      exact _hsm F hF hFV _ hφs hRF

end
end S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap (solution)
