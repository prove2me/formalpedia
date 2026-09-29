-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e398fc39-8866-5ef9-a150-85b119d1ff65

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_gauge3_le_mul_archRoot_mul_archRoot_sq_of_siegel_of_ideleNorm_det_mem_Icc
import Theorems.Thm_LanglandsTunnell_CubicInduction_norm_le_of_isCuspidalAlong_of_arch_oscillation_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_level_forall_foldr_archDeriv_invariant_cuspidal_archSmooth
import Theorems.Thm_LanglandsTunnell_CubicInduction_gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.CubicInduction.fnTwist3_apply"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2"

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv AdelicGL globalPointsGL localMaximalCompact3 componentAt3 localToAdelic3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 IsRightInvariant archPlaceComponent3 gauge3 gauge3_pos archRoot₁ archRoot₂ exists_gauge3_le_mul_archRoot_mul_archRoot_sq_of_siegel_of_ideleNorm_det_mem_Icc norm_le_of_isCuspidalAlong_of_arch_oscillation_le exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel exists_level_forall_foldr_archDeriv_invariant_cuspidal_archSmooth gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow"
namespace SDAux
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open _root_.WhittakerBlock AutomorphicForm.StandardKernel

abbrev G3 : Type := AdelicGL 3 (𝓞 ℚ) ℚ
abbrev M3 : Type := Matrix (Fin 3) (Fin 3) ℝ
abbrev A : Type := AdeleRing (𝓞 ℚ) ℚ

def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

theorem ofRealHom_apply (r : ℝ) : ofRealHom r = ofReal r := rfl

def liftR : GL (Fin 3) ℝ →* GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  Units.map (ofRealHom.mapMatrix (m := Fin 3)).toMonoidHom

def E : GL (Fin 3) ℝ →* G3 := (archInclN (Fin 3) ℚ).comp liftR

def toGL (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) : GL (Fin 3) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h

@[scoped simp] theorem coe_toGL (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) : (toGL e h : M3) = Matrix.of e := rfl

theorem archRealLift3_eq_E (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) :
    archRealLift3 e = E (toGL e h) := by
  have hmat : archRealMat3 e = ((E (toGL e h) : G3) : Matrix (Fin 3) (Fin 3) A) := rfl
  have hu : IsUnit (archRealMat3 e) := by rw [hmat]; exact Units.isUnit _
  unfold archRealLift3
  rw [dif_pos hu]
  exact Units.ext (by rw [IsUnit.unit_spec, hmat])

def idArr : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then (1 : ℝ) else 0

theorem of_idArr : Matrix.of idArr = (1 : M3) := by
  ext i j; simp [idArr, Matrix.one_apply]

theorem det_idArr : (Matrix.of idArr).det ≠ 0 := by rw [of_idArr, Matrix.det_one]; exact one_ne_zero

theorem archRealLift3_idArr : archRealLift3 idArr = 1 := by
  rw [archRealLift3_eq_E _ det_idArr, ← map_one E]
  congr 1
  refine Units.ext ?_
  ext i j
  simp [toGL, of_idArr]

theorem continuous_liftR : Continuous (liftR : GL (Fin 3) ℝ → GL (Fin 3) (InfiniteAdeleRing ℚ)) := by
  refine Continuous.units_map _ ?_
  show Continuous fun M : Matrix (Fin 3) (Fin 3) ℝ => ofRealHom.mapMatrix M
  refine continuous_matrix fun i j => ?_
  exact continuous_ofReal.comp (continuous_id.matrix_elem i j)

theorem continuous_archInclN : Continuous (archInclN (Fin 3) ℚ : GL (Fin 3) (InfiniteAdeleRing ℚ) → G3) := by
  refine Continuous.units_map _ ?_
  show Continuous fun M : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) => archMatrixInclN (Fin 3) ℚ M
  refine continuous_matrix fun i j => ?_
  show Continuous fun M : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) =>
    (((M i j, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
      InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) : A)
  exact (continuous_id.matrix_elem i j).prodMk continuous_const

theorem continuous_E : Continuous (E : GL (Fin 3) ℝ → G3) :=
  continuous_archInclN.comp continuous_liftR

theorem continuousOn_archRealLift3 : ContinuousOn archRealLift3 {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.domRestrict {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} archRealLift3) =
      fun e => E (toGL e.1 e.2) := by
    funext e; exact archRealLift3_eq_E e.1 e.2
  rw [heq]
  refine continuous_E.comp ?_
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} => Matrix.of e.1
    exact continuous_subtype_val
  · show Continuous fun e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} =>
      (((toGL e.1 e.2)⁻¹ : GL (Fin 3) ℝ) : M3)
    have : (fun e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} => (((toGL e.1 e.2)⁻¹ : GL (Fin 3) ℝ) : M3)) =
        fun e => (Matrix.of e.1)⁻¹ := by
      funext e; rw [Matrix.coe_units_inv, coe_toGL]
    rw [this]
    have hof : Continuous fun e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} => Matrix.of e.1 :=
      continuous_subtype_val
    refine continuous_iff_continuousAt.mpr fun e => ?_
    have hdet : ContinuousAt Ring.inverse (Matrix.of e.1).det := by
      rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ e.2
    show ContinuousAt ((fun M : M3 => M⁻¹) ∘ fun e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} => Matrix.of e.1) e
    exact ContinuousAt.comp (f := fun e : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} => Matrix.of e.1) (x := e)
      (continuousAt_matrix_inv (Matrix.of e.1) hdet) hof.continuousAt

end LanglandsTunnell.CubicInduction.SDAux
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth.LanglandsTunnell.CubicInduction.SDAux"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth.LanglandsTunnell.CubicInduction.SDAux"

open LanglandsTunnell.CubicInduction.SDAux in
theorem solution
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous φ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) φ)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) φ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) φ)
    (hsm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ (g * localToAdelic3 v k) = φ g)
    (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hcw : ∀ w : List (Fin 3 × Fin 3),
      Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ w))
    (N : ℕ) (hgr : ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ w g‖ ≤ C * gauge3 ℚ g ^ N)
    (c C a b : ℝ) (hc0 : 0 < c) (ha : 0 < a) (hab : a < b) :
    ∀ M : ℕ, ∃ C' : ℝ, ∀ n t k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) →
        (∀ w : InfinitePlace ℚ,
          (∀ i j : Fin 3,
            (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
            (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
          (∀ i j : Fin 3, i ≠ j →
            (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
          (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
              (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1) →
        NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (n * t * k)) ∈ Set.Icc a b →
        ‖φ (n * t * k)‖ * gauge3 ℚ (n * t * k) ^ M ≤ C' := by
  classical
  intro M
  obtain ⟨W, hW0, hW⟩ :=
    exists_gauge3_le_mul_archRoot_mul_archRoot_sq_of_siegel_of_ideleNorm_det_mem_Icc c C a b hc0 ha hab
  obtain ⟨m, hm0, hδ⟩ :=
    exists_level_forall_foldr_archDeriv_invariant_cuspidal_archSmooth φ hc haut hP21 hP12 S hK hsm hsa hcw

  have hbox : ∃ M' : ℝ, 0 ≤ M' ∧ ∀ x : AdeleRing (𝓞 ℚ) ℚ,
      algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ m)⁻¹ * x ∈ AdelicBox.adelicBox ℚ →
      ∀ w : InfinitePlace ℚ, ‖x.1 w‖ ≤ M' := by
    obtain ⟨Kc, hKc, hboxKc⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset (K := ℚ)
    set mQ : ℚ := algebraMap (𝓞 ℚ) ℚ m with hmQ
    have hmQ0 : mQ ≠ 0 := by
      rw [hmQ]; exact (map_ne_zero_iff _ NumberField.RingOfIntegers.coe_injective).mpr hm0
    have hg : ∀ w : InfinitePlace ℚ, Continuous fun y : AdeleRing (𝓞 ℚ) ℚ =>
        ‖(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) mQ * y).1 w‖ :=
      fun w => ((continuous_apply w).comp (continuous_const.mul continuous_id).fst).norm
    have hBw : ∀ w : InfinitePlace ℚ, ∃ Bw : ℝ, ∀ y ∈ Kc, ‖(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) mQ * y).1 w‖ ≤ Bw := by
      intro w
      obtain ⟨Bw, hBw⟩ := hKc.exists_bound_of_continuousOn (hg w).continuousOn
      exact ⟨Bw, fun y hy => by simpa only [Real.norm_eq_abs, abs_norm] using hBw y hy⟩
    choose Bw hBw' using hBw
    refine ⟨∑ w, |Bw w|, Finset.sum_nonneg fun w _ => abs_nonneg _, fun x hx w => ?_⟩
    have hy := hBw' w _ (hboxKc hx)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hmQ0, map_one, one_mul] at hy
    calc ‖x.1 w‖ ≤ Bw w := hy
      _ ≤ |Bw w| := le_abs_self _
      _ ≤ ∑ w', |Bw w'| := Finset.single_le_sum (fun w' _ => abs_nonneg (Bw w')) (Finset.mem_univ w)
  obtain ⟨M', hM'0, hM'⟩ := hbox

  have P : ∀ (kk : ℕ) (Dc : Set (Fin 3 → Fin 3 → ℝ)), IsCompact Dc → Dc ⊆ {e | (Matrix.of e).det ≠ 0} →
      ∀ wd : List (Fin 3 × Fin 3), ∃ Cst : ℝ, ∀ n t k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) →
        (∀ w : InfinitePlace ℚ,
          (∀ i j : Fin 3,
            (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
            (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
          (∀ i j : Fin 3, i ≠ j →
            (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
          (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
              (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1) →
        NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (n * t * k)) ∈ Set.Icc a b →
        ∀ e ∈ Dc, ∀ w : InfinitePlace ℚ,
          ‖List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ wd (n * t * k * WhittakerBlock.archRealLift3 e)‖ ≤
            Cst * (archRoot₁ ℚ w t * archRoot₂ ℚ w t) ^ (2 * N) / (max (archRoot₁ ℚ w t) (archRoot₂ ℚ w t)) ^ kk := by
    intro kk
    induction kk with
    | zero =>
      intro Dc hDc hDcU wd
      obtain ⟨Cw, hCw⟩ := hgr wd
      have hKc : IsCompact (WhittakerBlock.archRealLift3 '' Dc) :=
        hDc.image_of_continuousOn (continuousOn_archRealLift3.mono hDcU)
      obtain ⟨CK, hCK⟩ := gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow.1 _ hKc
      refine ⟨|Cw| * (|CK| * W) ^ N, fun n t k hn ht hk harch hslab e he w => ?_⟩
      have hw : w = Rat.infinitePlace := Subsingleton.elim _ _
      subst hw
      have hα := hW n t k hn ht hk harch hslab Rat.infinitePlace
      have hg1 := hCK _ (Set.mem_image_of_mem _ he) (n * t * k)
      have hH0 : 0 ≤ gauge3 ℚ (n * t * k * WhittakerBlock.archRealLift3 e) := (gauge3_pos ℚ _).le
      have hH0' : 0 ≤ gauge3 ℚ (n * t * k) := (gauge3_pos ℚ _).le
      have hroots : 0 ≤ archRoot₁ ℚ Rat.infinitePlace t * archRoot₂ ℚ Rat.infinitePlace t :=
        mul_nonneg (hc0.le.trans (harch Rat.infinitePlace).2.2.1) (hc0.le.trans (harch Rat.infinitePlace).2.2.2.1)
      rw [pow_zero, div_one]
      set X := gauge3 ℚ (n * t * k * WhittakerBlock.archRealLift3 e) with hX
      set Y := gauge3 ℚ (n * t * k) with hY
      set ρ := archRoot₁ ℚ Rat.infinitePlace t * archRoot₂ ℚ Rat.infinitePlace t with hρ
      have hXY : X ≤ |CK| * W * ρ ^ 2 :=
        calc X ≤ CK * Y := hg1
          _ ≤ |CK| * Y := mul_le_mul_of_nonneg_right (le_abs_self _) hH0'
          _ ≤ |CK| * (W * ρ ^ 2) := mul_le_mul_of_nonneg_left hα (abs_nonneg _)
          _ = |CK| * W * ρ ^ 2 := (mul_assoc _ _ _).symm
      calc ‖List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ wd (n * t * k * WhittakerBlock.archRealLift3 e)‖
          ≤ Cw * X ^ N := hCw _
        _ ≤ |Cw| * X ^ N := mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 N)
        _ ≤ |Cw| * (|CK| * W * ρ ^ 2) ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0 hXY N) (abs_nonneg _)
        _ = |Cw| * (|CK| * W) ^ N * ρ ^ (2 * N) := by rw [mul_pow, ← pow_mul, mul_assoc]
    | succ kk ih =>
      intro Dc hDc hDcU wd
      obtain ⟨Dc', hDc', hDc'U, hDcDc', κ, hκ, hγ⟩ :=
        exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel c C M' hc0 hM'0 Dc hDc hDcU

      have IH9 : ∀ ij : Fin 3 × Fin 3, ∃ Cst : ℝ, ∀ n t k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) →
        (∀ w : InfinitePlace ℚ,
          (∀ i j : Fin 3,
            (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
            (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
          (∀ i j : Fin 3, i ≠ j →
            (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
          (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
              (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1) →
          NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (n * t * k)) ∈ Set.Icc a b →
          ∀ e ∈ Dc', ∀ w : InfinitePlace ℚ,
            ‖List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ (ij :: wd)
                (n * t * k * WhittakerBlock.archRealLift3 e)‖ ≤
              Cst * (archRoot₁ ℚ w t * archRoot₂ ℚ w t) ^ (2 * N) / (max (archRoot₁ ℚ w t) (archRoot₂ ℚ w t)) ^ kk :=
        fun ij => ih Dc' hDc' hDc'U (ij :: wd)
      choose Cw hCw using IH9
      set F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ wd with hF
      obtain ⟨hFaut, hFP21, hFP12, hFsm, hFinv⟩ := hδ wd
      have hFc : Continuous F := hcw wd
      set Bsum : ℝ := ∑ ij : Fin 3 × Fin 3, |Cw ij| with hBsum
      have hBsum0 : 0 ≤ Bsum := Finset.sum_nonneg fun _ _ => abs_nonneg _
      refine ⟨κ * Bsum, fun n t k hn ht hk harch hslab e he w => ?_⟩
      have hw : w = Rat.infinitePlace := Subsingleton.elim _ _
      subst hw
      set r₁ := archRoot₁ ℚ Rat.infinitePlace t with hr₁
      set r₂ := archRoot₂ ℚ Rat.infinitePlace t with hr₂
      have hc1 : c ≤ r₁ := (harch Rat.infinitePlace).2.2.1
      have hc2 : c ≤ r₂ := (harch Rat.infinitePlace).2.2.2.1
      have hr₁0 : 0 < r₁ := hc0.trans_le hc1
      have hr₂0 : 0 < r₂ := hc0.trans_le hc2
      have hmx0 : 0 < max r₁ r₂ := lt_max_of_lt_left hr₁0
      have hρ0 : 0 ≤ (r₁ * r₂) ^ (2 * N) / (max r₁ r₂) ^ kk :=
        div_nonneg (pow_nonneg (mul_pos hr₁0 hr₂0).le _) (pow_nonneg hmx0.le _)

      set B : ℝ := Bsum * ((r₁ * r₂) ^ (2 * N) / (max r₁ r₂) ^ kk) with hB
      have hBd : ∀ e' ∈ Dc', ∀ i j : Fin 3,
          ‖WhittakerBlock.archDeriv i j F (n * t * k * WhittakerBlock.archRealLift3 e')‖ ≤ B := by
        intro e' he' i j
        have h1 := hCw (i, j) n t k hn ht hk harch hslab e' he' Rat.infinitePlace
        rw [List.foldr_cons] at h1
        calc ‖WhittakerBlock.archDeriv i j F (n * t * k * WhittakerBlock.archRealLift3 e')‖
            ≤ Cw (i, j) * (r₁ * r₂) ^ (2 * N) / (max r₁ r₂) ^ kk := h1
          _ = Cw (i, j) * ((r₁ * r₂) ^ (2 * N) / (max r₁ r₂) ^ kk) := mul_div_assoc _ _ _
          _ ≤ |Cw (i, j)| * ((r₁ * r₂) ^ (2 * N) / (max r₁ r₂) ^ kk) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) hρ0
          _ ≤ Bsum * ((r₁ * r₂) ^ (2 * N) / (max r₁ r₂) ^ kk) :=
              mul_le_mul_of_nonneg_right
                (Finset.single_le_sum (f := fun ij : Fin 3 × Fin 3 => |Cw ij|) (fun ij _ => abs_nonneg _)
                  (Finset.mem_univ (i, j))) hρ0

      have hosc := fun (x y : AdeleRing (𝓞 ℚ) ℚ) (hx : ∀ w : InfinitePlace ℚ, ‖x.1 w‖ ≤ M')
          (hy : ∀ w : InfinitePlace ℚ, ‖y.1 w‖ ≤ M') =>
        hγ F hFsm n t k hn ht hk harch B hBd e he x y hx hy Rat.infinitePlace

      have hLe : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p (WhittakerBlock.archRealLift3 e) = 1 := by
        intro p
        rw [archRealLift3_eq_E e (hDcU he)]
        exact componentAtN_archInclN (Fin 3) ℚ p (liftR (toGL e (hDcU he)))
      have hg : ∀ p : HeightOneSpectrum (𝓞 ℚ),
          componentAt3 (𝓞 ℚ) ℚ p (n * t * k * WhittakerBlock.archRealLift3 e) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
        intro p
        rw [map_mul, map_mul, map_mul, hn p, ht p, hLe p, one_mul, one_mul, mul_one]
        exact hk p
      have hβ := norm_le_of_isCuspidalAlong_of_arch_oscillation_le m hm0 F hFc hFaut hFP21 hFP12 hFinv
        (n * t * k * WhittakerBlock.archRealLift3 e) hg

      have h21 : ‖F (n * t * k * WhittakerBlock.archRealLift3 e)‖ ≤ κ * B / r₂ := by
        refine (hβ (κ * B / r₂)).1 fun x y hx hy => ?_
        have := (hosc x y (hM' x hx) (hM' y hy)).1
        simpa only [mul_assoc] using this
      have h12 : ‖F (n * t * k * WhittakerBlock.archRealLift3 e)‖ ≤ κ * B / r₁ := by
        refine (hβ (κ * B / r₁)).2 fun x y hx hy => ?_
        have := (hosc x y (hM' x hx) (hM' y hy)).2
        simpa only [mul_assoc] using this
      have hmax : ‖F (n * t * k * WhittakerBlock.archRealLift3 e)‖ ≤ κ * B / max r₁ r₂ := by
        rcases le_total r₁ r₂ with h | h
        · rw [max_eq_right h]; exact h21
        · rw [max_eq_left h]; exact h12
      calc ‖F (n * t * k * WhittakerBlock.archRealLift3 e)‖ ≤ κ * B / max r₁ r₂ := hmax
        _ = κ * Bsum * (r₁ * r₂) ^ (2 * N) / max r₁ r₂ ^ (kk + 1) := by
            rw [hB, pow_succ]
            field_simp

  obtain ⟨Cst, hCst⟩ := P (4 * N + 4 * M) {idArr} isCompact_singleton
    (by intro e he; rw [Set.mem_singleton_iff.mp he]; exact det_idArr) []
  refine ⟨|Cst| * W ^ M, fun n t k hn ht hk harch hslab => ?_⟩
  have hP := hCst n t k hn ht hk harch hslab idArr (Set.mem_singleton _) Rat.infinitePlace
  simp only [List.foldr_nil, archRealLift3_idArr, mul_one] at hP
  have hα := hW n t k hn ht hk harch hslab Rat.infinitePlace

  set r₁ := archRoot₁ ℚ Rat.infinitePlace t with hr₁
  set r₂ := archRoot₂ ℚ Rat.infinitePlace t with hr₂
  have hc1 : c ≤ r₁ := (harch Rat.infinitePlace).2.2.1
  have hc2 : c ≤ r₂ := (harch Rat.infinitePlace).2.2.2.1
  have hr₁0 : 0 < r₁ := hc0.trans_le hc1
  have hr₂0 : 0 < r₂ := hc0.trans_le hc2
  set mx := max r₁ r₂ with hmx
  have hmx0 : 0 < mx := lt_max_of_lt_left hr₁0
  have hh : r₁ * r₂ ≤ mx ^ 2 := by
    rw [pow_two]; exact mul_le_mul (le_max_left _ _) (le_max_right _ _) hr₂0.le hmx0.le
  have hh0 : 0 ≤ r₁ * r₂ := (mul_pos hr₁0 hr₂0).le
  have hH0 : 0 ≤ gauge3 ℚ (n * t * k) := (gauge3_pos ℚ _).le

  have h1 : ‖φ (n * t * k)‖ * gauge3 ℚ (n * t * k) ^ M ≤
      (Cst * (r₁ * r₂) ^ (2 * N) / mx ^ (4 * N + 4 * M)) * (W * (r₁ * r₂) ^ 2) ^ M :=
    mul_le_mul hP (pow_le_pow_left₀ hH0 hα M) (pow_nonneg hH0 M) ((norm_nonneg _).trans hP)
  refine h1.trans ?_
  have hCst : Cst ≤ |Cst| := le_abs_self Cst
  have key : (r₁ * r₂) ^ (2 * N) / mx ^ (4 * N + 4 * M) * ((r₁ * r₂) ^ 2) ^ M ≤ 1 := by
    rw [← pow_mul, div_mul_eq_mul_div, ← pow_add, div_le_one (pow_pos hmx0 _)]
    calc (r₁ * r₂) ^ (2 * N + 2 * M) ≤ (mx ^ 2) ^ (2 * N + 2 * M) := pow_le_pow_left₀ hh0 hh _
      _ = mx ^ (4 * N + 4 * M) := by rw [← pow_mul]; ring_nf
  calc Cst * (r₁ * r₂) ^ (2 * N) / mx ^ (4 * N + 4 * M) * (W * (r₁ * r₂) ^ 2) ^ M
      = Cst * W ^ M * ((r₁ * r₂) ^ (2 * N) / mx ^ (4 * N + 4 * M) * ((r₁ * r₂) ^ 2) ^ M) := by
        rw [mul_pow]; ring
    _ ≤ |Cst| * W ^ M * ((r₁ * r₂) ^ (2 * N) / mx ^ (4 * N + 4 * M) * ((r₁ * r₂) ^ 2) ^ M) := by
        gcongr
    _ ≤ |Cst| * W ^ M * 1 := by
        gcongr
    _ = |Cst| * W ^ M := mul_one _

end S_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth (solution)
