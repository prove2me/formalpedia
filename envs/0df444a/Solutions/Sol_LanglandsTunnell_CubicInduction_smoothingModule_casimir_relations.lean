-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.smoothingModule_casimir_relations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d41c2f1f-608e-527c-b343-216227c5b38a

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_archDeriv_and_comm
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_translateRight
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_archDeriv_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_hasCompactSupport_of_isSmoothingKernel
import Theorems.Thm_LanglandsTunnell_CubicInduction_continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum
import Theorems.Thm_LanglandsTunnell_CubicInduction_isArchSmooth3_mul_right
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_smoothingModule_casimir_relations
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply IsLocalization.map_moduleTensorEquiv_symm_tmul"
p2m_attr_erase "simp" "IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.CubicInduction.fnTwist3_apply"

set_option autoImplicit false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace R1CuspDeriv

open MeasureTheory Filter Metric Topology
open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

section Engine

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable (ν : Measure X) [IsFiniteMeasure ν] {C : Set X}

theorem integrable_of_continuous (hC : IsCompact C) (hνC : ∀ᵐ y ∂ν, y ∈ C) (φ : X → ℂ)
    (hφ : Continuous φ) : Integrable φ ν := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hφ.continuousOn
  exact Integrable.of_bound hφ.aestronglyMeasurable M (hνC.mono fun y hy => hM y hy)

theorem continuous_integral_of_continuous (hC : IsCompact C) (hνC : ∀ᵐ y ∂ν, y ∈ C)
    {P : Type*} [TopologicalSpace P] [LocallyCompactSpace P] [FirstCountableTopology P]
    (f : P → X → ℂ) (hf : Continuous fun q : P × X => f q.1 q.2) :
    Continuous fun p => ∫ y, f p y ∂ν := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨N, hN, hNp⟩ := exists_compact_mem_nhds p₀
  obtain ⟨M, hM⟩ := (hN.prod hC).exists_bound_of_continuousOn hf.continuousOn
  have hcont : ∀ p : P, Continuous fun y => f p y := fun p =>
    hf.comp (continuous_const.prodMk continuous_id)
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
  · exact Eventually.of_forall fun p => (hcont p).aestronglyMeasurable
  · filter_upwards [hNp] with p hp
    exact hνC.mono fun y hy => hM (p, y) ⟨hp, hy⟩
  · exact ae_of_all _ fun y => (hf.comp (continuous_id.prodMk continuous_const)).continuousAt

theorem hasDerivAt_integral_of_continuous (hC : IsCompact C) (hνC : ∀ᵐ y ∂ν, y ∈ C)
    (F F' : ℝ → X → ℂ) {r : ℝ} (hr : 0 < r)
    (hF : Continuous fun q : closedBall (0 : ℝ) r × X => F q.1 q.2)
    (hF' : Continuous fun q : closedBall (0 : ℝ) r × X => F' q.1 q.2)
    (hd : ∀ y, ∀ s ∈ ball (0 : ℝ) r, HasDerivAt (fun σ => F σ y) (F' s y) s) :
    ∀ s₀ ∈ ball (0 : ℝ) r, HasDerivAt (fun s => ∫ y, F s y ∂ν) (∫ y, F' s₀ y ∂ν) s₀ := by
  intro s₀ hs₀
  haveI : CompactSpace (closedBall (0 : ℝ) r) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := (isCompact_univ.prod hC).exists_bound_of_continuousOn hF'.continuousOn
  have hcF : ∀ s (hs : s ∈ closedBall (0 : ℝ) r), Continuous fun y => F s y := fun s hs =>
    hF.comp ((continuous_const (y := (⟨s, hs⟩ : closedBall (0 : ℝ) r))).prodMk continuous_id)
  have hcF' : ∀ s (hs : s ∈ closedBall (0 : ℝ) r), Continuous fun y => F' s y := fun s hs =>
    hF'.comp ((continuous_const (y := (⟨s, hs⟩ : closedBall (0 : ℝ) r))).prodMk continuous_id)
  have hball : ball (0 : ℝ) r ∈ 𝓝 s₀ := isOpen_ball.mem_nhds hs₀
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (F := F) (F' := F') (x₀ := s₀)
    (bound := fun _ => M) hball ?_ ?_ ?_ ?_ (integrable_const M) ?_).2
  · filter_upwards [hball] with s hs using (hcF s (ball_subset_closedBall hs)).aestronglyMeasurable
  · exact integrable_of_continuous ν hC hνC _ (hcF s₀ (ball_subset_closedBall hs₀))
  · exact (hcF' s₀ (ball_subset_closedBall hs₀)).aestronglyMeasurable
  · exact hνC.mono fun y hy s hs => hM (⟨s, ball_subset_closedBall hs⟩, y) ⟨Set.mem_univ _, hy⟩
  · exact ae_of_all _ fun y s hs => hd y s hs

end Engine

section Arch

def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

theorem ofRealHom_apply (r : ℝ) : ofRealHom r = StandardKernel.ofReal r := rfl

theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r := by
  show (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
    ((InfinitePlace.Completion.ringEquivRealOfIsReal _).symm r) = r
  exact RingEquiv.apply_symm_apply _ _

def rho : Matrix (Fin 3) (Fin 3) ℝ →+* Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) := ofRealHom.mapMatrix

def psi : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) →+* Matrix (Fin 3) (Fin 3) ℝ :=
  (StandardKernel.realCoord.comp (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)).mapMatrix

theorem archRealMat3_eq (e : Matrix (Fin 3) (Fin 3) ℝ) :
    WhittakerBlock.archRealMat3 e = archMatrixInclN (Fin 3) ℚ (rho e) := rfl

theorem psi_archRealMat3 (e : Matrix (Fin 3) (Fin 3) ℝ) : psi (WhittakerBlock.archRealMat3 e) = e := by
  ext i j
  change StandardKernel.realCoord (AdelicLevel.adeleArch (𝓞 ℚ) ℚ (archMatrixInclN (Fin 3) ℚ (rho e) i j)) = e i j
  rw [adeleArch_archMatrixInclN]
  exact realCoord_ofReal (e i j)

theorem isUnit_archRealMat3_iff (e : Matrix (Fin 3) (Fin 3) ℝ) :
    IsUnit (WhittakerBlock.archRealMat3 e) ↔ e.det ≠ 0 := by
  constructor
  · intro h
    have h' := h.map psi
    rw [psi_archRealMat3, Matrix.isUnit_iff_isUnit_det] at h'
    exact h'.ne_zero
  · intro h
    have hu : IsUnit e := (Matrix.isUnit_iff_isUnit_det e).mpr (isUnit_iff_ne_zero.mpr h)
    exact hu.map ((archMatrixInclHomN (Fin 3) ℚ).comp rho.toMonoidHom)

def liftGL : GL (Fin 3) ℝ →* AdelicGL 3 (𝓞 ℚ) ℚ := (archInclN (Fin 3) ℚ).comp (Units.map rho.toMonoidHom)

def toGL (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) : GL (Fin 3) ℝ :=
  Matrix.nonsingInvUnit e (isUnit_iff_ne_zero.mpr h)

@[scoped simp] theorem coe_toGL (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) : (toGL e h : Matrix (Fin 3) (Fin 3) ℝ) = e :=
  rfl

theorem archRealLift3_eq (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) :
    WhittakerBlock.archRealLift3 e = liftGL (toGL e h) := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos ((isUnit_archRealMat3_iff e).mpr h)]
  exact Units.ext (by rw [IsUnit.unit_spec]; rfl)

theorem archRealLift3_of_det (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det = 0) : WhittakerBlock.archRealLift3 e = 1 := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_neg]
  rw [isUnit_archRealMat3_iff]
  exact fun h' => h' h

theorem coe_archRealLift3 (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) :
    ((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  rw [archRealLift3_eq e h]; rfl

theorem archRealLift3_mul (e e' : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) (h' : (Matrix.of e').det ≠ 0) :
    WhittakerBlock.archRealLift3 (Matrix.of e * Matrix.of e') =
      WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 e' := by
  have hm : (Matrix.of e * Matrix.of e').det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero h h'
  have h1 : WhittakerBlock.archRealLift3 e = liftGL (toGL (Matrix.of e) h) := archRealLift3_eq (Matrix.of e) h
  have h2 : WhittakerBlock.archRealLift3 e' = liftGL (toGL (Matrix.of e') h') := archRealLift3_eq (Matrix.of e') h'
  rw [archRealLift3_eq _ hm, h1, h2, ← map_mul liftGL]
  congr 1
  exact Units.ext rfl

theorem archRealLift3_one : WhittakerBlock.archRealLift3 (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  rw [archRealLift3_eq _ (by simp)]
  have : toGL 1 (by simp) = 1 := Units.ext rfl
  rw [this, map_one]

theorem commute_archInclN (t : AdelicGL 3 (𝓞 ℚ) ℚ) (ht : archComponent3 (𝓞 ℚ) ℚ t = 1)
    (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : t * archInclN (Fin 3) ℚ h = archInclN (Fin 3) ℚ h * t := by
  set A : AdelicGL 3 (𝓞 ℚ) ℚ := archInclN (Fin 3) ℚ h with hAdef
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  have hA1 : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      (h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :=
    Matrix.ext fun a b => adeleArch_archMatrixInclN (Fin 3) ℚ (h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b
  have hA2 : (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 :=
    Matrix.ext fun a b => adeleFin_archMatrixInclN (Fin 3) ℚ (h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b
  have hT : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
    rw [← Units.val_one, ← ht]; rfl
  refine Matrix.ext fun i j => Prod.ext ?_ ?_
  · change ((AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        ((t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * (A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))) i j =
      ((AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        ((A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * (t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))) i j
    rw [map_mul, map_mul, hA1, hT, one_mul, mul_one]
  · change ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
        ((t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * (A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))) i j =
      ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
        ((A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * (t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))) i j
    rw [map_mul, map_mul, hA2, one_mul, mul_one]

theorem commute_archRealLift3 (t : AdelicGL 3 (𝓞 ℚ) ℚ) (ht : archComponent3 (𝓞 ℚ) ℚ t = 1)
    (e : Matrix (Fin 3) (Fin 3) ℝ) :
    t * WhittakerBlock.archRealLift3 e = WhittakerBlock.archRealLift3 e * t := by
  by_cases h : e.det = 0
  · rw [archRealLift3_of_det e h, mul_one, one_mul]
  · rw [archRealLift3_eq e h]
    exact commute_archInclN t ht _

def cfun (i j : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

def efun (i j : Fin 3) : Fin 3 → Fin 3 → ℝ := fun a b => if a = i ∧ b = j then 1 else 0

def kap (i j : Fin 3) (s : ℝ) : ℝ := 1 + if i = j then s else 0

theorem cfun_eq (i j : Fin 3) (s : ℝ) : cfun i j s = (fun a b => if a = b then (1 : ℝ) else 0) + s • efun i j := by
  funext a b
  simp only [cfun, efun, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem of_cfun (i j : Fin 3) (s : ℝ) : Matrix.of (cfun i j s) = 1 + s • Matrix.single i j (1 : ℝ) := by
  ext a b
  simp only [cfun, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  congr 1
  by_cases h : a = i ∧ b = j
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]

theorem det_cfun (i j : Fin 3) (s : ℝ) : (Matrix.of (cfun i j s)).det = kap i j s := by
  unfold cfun kap
  fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_three]

theorem kap_pos (i j : Fin 3) {s : ℝ} (hs : |s| < 1) : 0 < kap i j s := by
  unfold kap
  split_ifs
  · have := (abs_lt.mp hs).1; linarith
  · norm_num

theorem continuous_kap (i j : Fin 3) : Continuous (kap i j) := by
  by_cases h : i = j
  · have : kap i j = fun s => 1 + s := funext fun s => by simp [kap, h]
    rw [this]; fun_prop
  · have : kap i j = fun _ => 1 := funext fun s => by simp [kap, h]
    rw [this]; fun_prop

theorem det_cfun_ne (i j : Fin 3) {s : ℝ} (hs : |s| < 1) : (Matrix.of (cfun i j s)).det ≠ 0 := by
  rw [det_cfun]; exact (kap_pos i j hs).ne'

theorem cfun_zero (i j : Fin 3) : Matrix.of (cfun i j 0) = 1 := by
  rw [of_cfun, zero_smul, add_zero]

theorem of_cfun_mul (i j : Fin 3) (s τ : ℝ) :
    Matrix.of (cfun i j s) * Matrix.of (cfun i j τ) = Matrix.of (cfun i j (s + kap i j s * τ)) := by
  rw [of_cfun, of_cfun, of_cfun]
  by_cases h : i = j
  · subst h
    have hE : Matrix.single i i (1 : ℝ) * Matrix.single i i (1 : ℝ) = Matrix.single i i (1 : ℝ) := by
      rw [Matrix.single_mul_single_same, one_mul]
    have hk : kap i i s = 1 + s := by simp [kap]
    rw [hk, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hE, smul_smul]
    module
  · have hE : Matrix.single i j (1 : ℝ) * Matrix.single i j (1 : ℝ) = 0 :=
      Matrix.single_mul_single_of_ne 1 i j i (Ne.symm h) 1
    have hk : kap i j s = 1 := by simp [kap, h]
    rw [hk, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hE]
    module

theorem continuous_cfun (i j : Fin 3) : Continuous (cfun i j) := by
  rw [show cfun i j = fun s => (fun a b => if a = b then (1 : ℝ) else 0) + s • efun i j from funext (cfun_eq i j)]
  fun_prop

theorem hasDerivAt_cfun (i j : Fin 3) (s : ℝ) : HasDerivAt (cfun i j) (efun i j) s := by
  rw [show cfun i j = fun s => (fun a b => if a = b then (1 : ℝ) else 0) + s • efun i j from funext (cfun_eq i j)]
  have h := ((hasDerivAt_id s).smul_const (efun i j)).const_add (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0)
  rw [one_smul] at h
  exact h

def U : Set (Fin 3 → Fin 3 → ℝ) := {e | (Matrix.of e).det ≠ 0}

theorem isOpen_U : IsOpen U := by
  have hc : Continuous fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det :=
    (continuous_id : Continuous fun e : Fin 3 → Fin 3 → ℝ => Matrix.of e).matrix_det
  exact isOpen_compl_singleton.preimage hc

theorem cfun_mem_U (i j : Fin 3) {s : ℝ} (hs : |s| < 1) : cfun i j s ∈ U := det_cfun_ne i j hs

def L (i j : Fin 3) (s : ℝ) : AdelicGL 3 (𝓞 ℚ) ℚ := WhittakerBlock.archRealLift3 (cfun i j s)

theorem L_zero (i j : Fin 3) : L i j 0 = 1 := by
  show WhittakerBlock.archRealLift3 (Matrix.of (cfun i j 0)) = 1
  rw [cfun_zero]
  exact archRealLift3_one

theorem L_mul_L (i j : Fin 3) {s τ : ℝ} (hs : |s| < 1) (hτ : |τ| < 1) :
    L i j s * L i j τ = L i j (s + kap i j s * τ) := by
  have h := archRealLift3_mul (cfun i j s) (cfun i j τ) (det_cfun_ne i j hs) (det_cfun_ne i j hτ)
  rw [of_cfun_mul] at h
  exact h.symm

theorem archDeriv_apply (i j : Fin 3) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.archDeriv i j φ g = deriv (fun s => φ (g * L i j s)) 0 := rfl

variable {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}

theorem differentiableAt_slice (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ)
    {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ U) :
    DifferentiableAt ℝ (fun e : Fin 3 → Fin 3 → ℝ => Φ (h * WhittakerBlock.archRealLift3 e)) e :=
  ((hΦ h).differentiableOn (by simp)).differentiableAt (isOpen_U.mem_nhds he)

theorem differentiableAt_comp_L (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3)
    {s : ℝ} (hs : |s| < 1) : DifferentiableAt ℝ (fun σ => Φ (h * L i j σ)) s :=
  (differentiableAt_slice hΦ h (cfun_mem_U i j hs)).comp s (hasDerivAt_cfun i j s).differentiableAt

theorem archDeriv_apply_mul_L (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3)
    {s : ℝ} (hs : |s| < 1) :
    WhittakerBlock.archDeriv i j Φ (h * L i j s) = (kap i j s : ℂ) * deriv (fun σ => Φ (h * L i j σ)) s := by
  rw [archDeriv_apply]

  have hev : (fun τ => Φ (h * L i j s * L i j τ)) =ᶠ[𝓝 0] fun τ => (fun σ => Φ (h * L i j σ)) (s + kap i j s * τ) := by
    have hnb : ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := isOpen_ball.mem_nhds (by simp)
    filter_upwards [hnb] with τ hτ
    have hτ' : |τ| < 1 := by simpa [Real.dist_eq] using hτ
    rw [mul_assoc, L_mul_L i j hs hτ']
  rw [hev.deriv_eq]
  rw [show (fun τ => (fun σ => Φ (h * L i j σ)) (s + kap i j s * τ)) =
      fun τ => (fun σ' => (fun σ => Φ (h * L i j σ)) (s + σ')) (kap i j s * τ) from rfl]
  rw [deriv_comp_mul_left (kap i j s) (fun σ' => (fun σ => Φ (h * L i j σ)) (s + σ')) 0, mul_zero,
    deriv_comp_const_add (fun σ => Φ (h * L i j σ)) s 0, add_zero, Complex.real_smul]

theorem hasDerivAt_comp_L (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3)
    {s : ℝ} (hs : |s| < 1) :
    HasDerivAt (fun σ => Φ (h * L i j σ)) ((kap i j s : ℂ)⁻¹ * WhittakerBlock.archDeriv i j Φ (h * L i j s)) s := by
  have hk : (kap i j s : ℂ) ≠ 0 := by exact_mod_cast (kap_pos i j hs).ne'
  rw [archDeriv_apply_mul_L hΦ h i j hs, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]
  exact (differentiableAt_comp_L hΦ h i j hs).hasDerivAt

def mulE (i j : Fin 3) (e : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (Matrix.of e * Matrix.single i j (1 : ℝ)) a b

theorem mulE_eq (i j : Fin 3) : mulE i j = fun e a b => if b = j then e a i else 0 := by
  funext e a b
  simp only [mulE, Matrix.mul_apply, Matrix.of_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero]
  by_cases hb : b = j
  · rw [if_pos hb, Finset.sum_eq_single i (fun k _ hk => if_neg (fun h => hk h.1.symm)) (by simp)]
    rw [if_pos ⟨rfl, hb.symm⟩]
  · rw [if_neg hb]
    exact Finset.sum_eq_zero fun k _ => if_neg fun h => hb h.2.symm

theorem contDiff_mulE (i j : Fin 3) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mulE i j) := by
  rw [mulE_eq]
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  by_cases hb : b = j
  · simp only [if_pos hb]; exact contDiff_apply_apply ℝ ℝ a i
  · simp only [if_neg hb]; exact contDiff_const

theorem of_mul_of_cfun (i j : Fin 3) (e : Fin 3 → Fin 3 → ℝ) (τ : ℝ) :
    Matrix.of e * Matrix.of (cfun i j τ) = Matrix.of (e + τ • mulE i j e) := by
  rw [of_cfun, mul_add, mul_one, Matrix.mul_smul]
  rfl

theorem hasDerivAt_mul_cfun (i j : Fin 3) (e : Fin 3 → Fin 3 → ℝ) :
    HasDerivAt (fun τ : ℝ => e + τ • mulE i j e) (mulE i j e) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const (mulE i j e)).const_add e
  rw [one_smul] at h
  exact h

theorem archDeriv_slice_eq (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3)
    {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ U) :
    WhittakerBlock.archDeriv i j Φ (g * WhittakerBlock.archRealLift3 e) =
      fderiv ℝ (fun e' : Fin 3 → Fin 3 → ℝ => Φ (g * WhittakerBlock.archRealLift3 e')) e (mulE i j e) := by
  rw [archDeriv_apply]
  have hev : (fun τ => Φ (g * WhittakerBlock.archRealLift3 e * L i j τ)) =ᶠ[𝓝 0]
      (fun e' : Fin 3 → Fin 3 → ℝ => Φ (g * WhittakerBlock.archRealLift3 e')) ∘ fun τ => e + τ • mulE i j e := by
    have hnb : ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := isOpen_ball.mem_nhds (by simp)
    filter_upwards [hnb] with τ hτ
    have hτ' : |τ| < 1 := by simpa [Real.dist_eq] using hτ
    simp only [Function.comp_apply, L]
    rw [mul_assoc, ← archRealLift3_mul e (cfun i j τ) he (det_cfun_ne i j hτ'), of_mul_of_cfun]
    rfl
  rw [hev.deriv_eq]
  exact ((differentiableAt_slice hΦ g he).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (hasDerivAt_mul_cfun i j e) (by simp)).deriv

theorem isArchSmooth3_archDeriv (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (i j : Fin 3) :
    WhittakerBlock.IsArchSmooth3 (WhittakerBlock.archDeriv i j Φ) := by
  intro g
  have hψ := hΦ g
  have hU : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} = U := rfl
  rw [hU] at hψ ⊢
  have hd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun e => fderiv ℝ (fun e' : Fin 3 → Fin 3 → ℝ => Φ (g * WhittakerBlock.archRealLift3 e')) e (mulE i j e))
      U :=
    (hψ.fderiv_of_isOpen isOpen_U (by simp)).clm_apply (contDiff_mulE i j).contDiffOn
  exact hd.congr fun e he => archDeriv_slice_eq hΦ g i j he

theorem continuous_archRealMat3_cfun (i j : Fin 3) :
    Continuous fun s => WhittakerBlock.archRealMat3 (cfun i j s) := by
  have h1 : Continuous fun s => rho (Matrix.of (cfun i j s)) :=
    (continuous_cfun i j).matrix_map StandardKernel.continuous_ofReal
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact ((continuous_apply_apply a b).comp h1).prodMk continuous_const

theorem abs_neg_div_kap_lt (i j : Fin 3) {s : ℝ} (hs : |s| ≤ 1 / 3) : |-(s / kap i j s)| < 1 := by
  have hs1 : |s| < 1 := lt_of_le_of_lt hs (by norm_num)
  have hk := kap_pos i j hs1
  rw [abs_neg, abs_div, abs_of_pos hk, div_lt_one hk]
  unfold kap
  split_ifs with h
  · have := (abs_le.mp hs).1; have := (abs_le.mp hs).2
    rw [abs_lt]; constructor <;> linarith
  · simpa using hs1

theorem L_inv_eq (i j : Fin 3) {s : ℝ} (hs : |s| ≤ 1 / 3) :
    (L i j s)⁻¹ = L i j (-(s / kap i j s)) := by
  have hs1 : |s| < 1 := lt_of_le_of_lt hs (by norm_num)
  have hk := kap_pos i j hs1
  rw [inv_eq_iff_mul_eq_one, L_mul_L i j hs1 (abs_neg_div_kap_lt i j hs)]
  have : s + kap i j s * -(s / kap i j s) = 0 := by field_simp; ring
  rw [this, L_zero]

theorem continuousOn_L (i j : Fin 3) : ContinuousOn (L i j) (closedBall (0 : ℝ) (1 / 3)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hmem : ∀ s : closedBall (0 : ℝ) (1 / 3), |(s : ℝ)| ≤ 1 / 3 := fun s => by
    have := s.2; simpa [Real.dist_eq] using this
  have hmem1 : ∀ s : closedBall (0 : ℝ) (1 / 3), |(s : ℝ)| < 1 := fun s => lt_of_le_of_lt (hmem s) (by norm_num)
  rw [Units.continuous_iff]
  constructor
  · have : (Units.val ∘ (closedBall (0 : ℝ) (1 / 3)).domRestrict (L i j)) =
        fun s : closedBall (0 : ℝ) (1 / 3) => WhittakerBlock.archRealMat3 (cfun i j s) := by
      funext s
      exact coe_archRealLift3 _ (det_cfun_ne i j (hmem1 s))
    rw [this]
    exact (continuous_archRealMat3_cfun i j).comp continuous_subtype_val
  · have : (fun s : closedBall (0 : ℝ) (1 / 3) => Units.val (((closedBall (0 : ℝ) (1 / 3)).domRestrict (L i j) s)⁻¹)) =
        fun s : closedBall (0 : ℝ) (1 / 3) => WhittakerBlock.archRealMat3 (cfun i j (-(s / kap i j s))) := by
      funext s
      show Units.val (L i j s)⁻¹ = _
      rw [L_inv_eq i j (hmem s)]
      exact coe_archRealLift3 _ (det_cfun_ne i j (abs_neg_div_kap_lt i j (hmem s)))
    rw [this]
    refine (continuous_archRealMat3_cfun i j).comp ?_
    have hk : ∀ s : closedBall (0 : ℝ) (1 / 3), kap i j s ≠ 0 := fun s => (kap_pos i j (hmem1 s)).ne'
    have hkc : Continuous fun s : closedBall (0 : ℝ) (1 / 3) => kap i j s :=
      (continuous_kap i j).comp continuous_subtype_val
    exact (continuous_subtype_val.div hkc hk).neg

end Arch

section Cusp

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

def ν0 : Measure (AdeleRing (𝓞 ℚ) ℚ) :=
  ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

scoped instance : IsProbabilityMeasure ν0 := AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ

scoped instance : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdeleRing.secondCountableTopology ℚ

theorem exists_compact_ae : ∃ C : Set (AdeleRing (𝓞 ℚ) ℚ), IsCompact C ∧ ∀ᵐ y ∂ν0, y ∈ C := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  exact ⟨C, hC, (ProbabilityTheory.ae_cond_mem (AdelicBox.measurableSet_adelicBox ℚ)).mono fun y hy => hsub hy⟩

variable (u : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ)
  (hu : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => u p.1 p.2)

include hu

theorem integral_integral_sum_translate (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∫ x, ∫ y, (∑ i, c i * f (u x y * g * t i)) ∂ν0 ∂ν0 = ∑ i, c i * ∫ x, ∫ y, f (u x y * (g * t i)) ∂ν0 ∂ν0 := by
  obtain ⟨C, hC, hνC⟩ := exists_compact_ae
  have hjc : ∀ i, Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => f (u q.1 q.2 * (g * t i)) :=
    fun i => hc.comp (hu.mul continuous_const)
  have hin : ∀ i x, Integrable (fun y => f (u x y * (g * t i))) ν0 := fun i x =>
    integrable_of_continuous ν0 hC hνC _ (hc.comp ((hu.comp (Continuous.prodMk_right x)).mul continuous_const))
  have hout : ∀ i, Integrable (fun x => ∫ y, f (u x y * (g * t i)) ∂ν0) ν0 := fun i =>
    integrable_of_continuous ν0 hC hνC _ (continuous_integral_of_continuous ν0 hC hνC _ (hjc i))
  have hinner : ∀ x, ∫ y, (∑ i, c i * f (u x y * g * t i)) ∂ν0 = ∑ i, c i * ∫ y, f (u x y * (g * t i)) ∂ν0 := by
    intro x
    simp_rw [mul_assoc]
    rw [integral_finsetSum _ fun i _ => (hin i x).const_mul (c i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  simp_rw [hinner]
  rw [integral_finsetSum _ fun i _ => (hout i).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem integral_integral_archDeriv_eq_zero {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦc : Continuous Φ)
    (hΦs : WhittakerBlock.IsArchSmooth3 Φ) (i j : Fin 3)
    (hΦ'c : Continuous (WhittakerBlock.archDeriv i j Φ))
    (hcusp : ∀ g, ∫ x, ∫ y, Φ (u x y * g) ∂ν0 ∂ν0 = 0) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∫ x, ∫ y, WhittakerBlock.archDeriv i j Φ (u x y * g) ∂ν0 ∂ν0 = 0 := by
  obtain ⟨C, hC, hνC⟩ := exists_compact_ae

  set F : ℝ → AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ := fun s x y => Φ (u x y * g * L i j s) with hF
  set F' : ℝ → AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ :=
    fun s x y => ((kap i j s : ℂ)⁻¹) * WhittakerBlock.archDeriv i j Φ (u x y * g * L i j s) with hF'
  have hr : (0 : ℝ) < 1 / 3 := by norm_num
  have hI : ∀ s : closedBall (0 : ℝ) (1 / 3), |(s : ℝ)| < 1 := fun s => by
    have := s.2; have h' : |(s : ℝ)| ≤ 1 / 3 := by simpa [Real.dist_eq] using this
    exact lt_of_le_of_lt h' (by norm_num)
  have hball : ∀ s ∈ ball (0 : ℝ) (1 / 3), |s| < 1 := fun s hs => by
    have h' : |s| < 1 / 3 := by simpa [Real.dist_eq] using hs
    exact lt_trans h' (by norm_num)

  have hLc : Continuous fun s : closedBall (0 : ℝ) (1 / 3) => L i j s :=
    continuousOn_iff_continuous_restrict.mp (continuousOn_L i j)
  have huq : Continuous fun q : closedBall (0 : ℝ) (1 / 3) × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      u q.2.1 q.2.2 * g * L i j q.1 :=
    (((hu.comp (continuous_snd (X := closedBall (0 : ℝ) (1 / 3))) :)).mul continuous_const).mul
      (hLc.comp (continuous_fst (Y := (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))) :)
  have hFc : Continuous fun q : closedBall (0 : ℝ) (1 / 3) × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      F q.1 q.2.1 q.2.2 :=
    hΦc.comp huq
  have hkc : Continuous fun s : closedBall (0 : ℝ) (1 / 3) => ((kap i j s : ℂ)⁻¹) := by
    refine Continuous.inv₀ (Complex.continuous_ofReal.comp ((continuous_kap i j).comp continuous_subtype_val))
      fun s => ?_
    exact_mod_cast (kap_pos i j (hI s)).ne'
  have hF'c : Continuous fun q : closedBall (0 : ℝ) (1 / 3) × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      F' q.1 q.2.1 q.2.2 :=
    ((hkc.comp (continuous_fst (Y := (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))) :)).mul (hΦ'c.comp huq)

  have hd : ∀ x y, ∀ s ∈ ball (0 : ℝ) (1 / 3), HasDerivAt (fun σ => F σ x y) (F' s x y) s :=
    fun x y s hs => hasDerivAt_comp_L hΦs (u x y * g) i j (hball s hs)

  have hG : ∀ x, ∀ s₀ ∈ ball (0 : ℝ) (1 / 3),
      HasDerivAt (fun s => ∫ y, F s x y ∂ν0) (∫ y, F' s₀ x y ∂ν0) s₀ := fun x =>
    hasDerivAt_integral_of_continuous ν0 hC hνC (fun s y => F s x y) (fun s y => F' s x y) hr
      (hFc.comp (continuous_fst.prodMk ((continuous_const (y := x)).prodMk continuous_snd)) :)
      (hF'c.comp (continuous_fst.prodMk ((continuous_const (y := x)).prodMk continuous_snd)) :) (fun y => hd x y)

  have hGc : Continuous fun q : closedBall (0 : ℝ) (1 / 3) × AdeleRing (𝓞 ℚ) ℚ => ∫ y, F q.1 q.2 y ∂ν0 :=
    continuous_integral_of_continuous ν0 hC hνC (fun q : closedBall (0 : ℝ) (1 / 3) × AdeleRing (𝓞 ℚ) ℚ =>
      fun y => F q.1 q.2 y) (hFc.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)) :)
  have hG'c : Continuous fun q : closedBall (0 : ℝ) (1 / 3) × AdeleRing (𝓞 ℚ) ℚ => ∫ y, F' q.1 q.2 y ∂ν0 :=
    continuous_integral_of_continuous ν0 hC hνC (fun q : closedBall (0 : ℝ) (1 / 3) × AdeleRing (𝓞 ℚ) ℚ =>
      fun y => F' q.1 q.2 y) (hF'c.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)) :)
  have hH : HasDerivAt (fun s => ∫ x, ∫ y, F s x y ∂ν0 ∂ν0) (∫ x, ∫ y, F' 0 x y ∂ν0 ∂ν0) 0 :=
    hasDerivAt_integral_of_continuous ν0 hC hνC (fun s x => ∫ y, F s x y ∂ν0) (fun s x => ∫ y, F' s x y ∂ν0)
      hr hGc hG'c hG 0 (mem_ball_self hr)

  have hzero : (fun s => ∫ x, ∫ y, F s x y ∂ν0 ∂ν0) = fun _ => 0 := by
    funext s
    have := hcusp (g * L i j s)
    simp only [hF, mul_assoc] at this ⊢
    exact this
  rw [hzero] at hH
  have h0 : (∫ x, ∫ y, F' 0 x y ∂ν0 ∂ν0) = 0 := hH.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ)) ▸ rfl
  have hF'0 : ∀ x y, F' 0 x y = WhittakerBlock.archDeriv i j Φ (u x y * g) := fun x y => by
    simp only [hF', L_zero, mul_one, kap, ite_self, add_zero]
    simp
  simp_rw [hF'0] at h0
  exact h0

end Cusp

section Words

theorem isArchSmooth3_sum_translate (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 f)
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1) :
    WhittakerBlock.IsArchSmooth3 (fun x => ∑ i, c i * f (x * t i)) := by
  intro g
  have heq : (fun e : Fin 3 → Fin 3 → ℝ => ∑ i, c i * f (g * WhittakerBlock.archRealLift3 e * t i)) =
      fun e => ∑ i, c i * f (g * t i * WhittakerBlock.archRealLift3 e) := by
    funext e
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcomm : t i * WhittakerBlock.archRealLift3 e = WhittakerBlock.archRealLift3 e * t i :=
      commute_archRealLift3 (t i) (ht i) (Matrix.of e)
    rw [mul_assoc, ← hcomm, ← mul_assoc]
  rw [heq]
  exact ContDiffOn.sum fun i _ => contDiffOn_const.mul (hsa (g * t i))

theorem isArchSmooth3_foldr (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : WhittakerBlock.IsArchSmooth3 v)
    (w : List (Fin 3 × Fin 3)) :
    WhittakerBlock.IsArchSmooth3 (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) v w) := by
  induction w with
  | nil => exact hv
  | cons ij w ih => exact isArchSmooth3_archDeriv ih ij.1 ij.2

end Words

section Radicals

theorem continuous_radicalP21 :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (radicalP21 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Function.comp_apply, radicalP21_coe]
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop
  · have : (fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
        (((radicalP21 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) :
          Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) =
        fun p => !![1, -0, 0 * p.2 - p.1; 0, 1, -p.2; 0, 0, 1] := by
      funext p; rfl
    rw [this]
    refine continuous_pi fun a => continuous_pi fun b => ?_
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop

theorem continuous_radicalP12 :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (radicalP12 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Function.comp_apply, radicalP12_coe]
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop
  · have : (fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
        (((radicalP12 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) :
          Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) =
        fun p => !![1, -p.1, p.1 * 0 - p.2; 0, 1, -0; 0, 0, 1] := by
      funext p; rfl
    rw [this]
    refine continuous_pi fun a => continuous_pi fun b => ?_
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop

end Radicals

end R1CuspDeriv
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_smoothingModule_casimir_relations.R1CuspDeriv"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_smoothingModule_casimir_relations.R1CuspDeriv"

section CasA

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

local notation "GA" => AdelicGL 3 (𝓞 ℚ) ℚ

def CA.Good (T : (GA → ℂ) → (GA → ℂ)) : Prop :=
  (∀ x, WhittakerBlock.IsArchSmooth3 x → WhittakerBlock.IsArchSmooth3 (T x)) ∧
  (∀ x y, WhittakerBlock.IsArchSmooth3 x → WhittakerBlock.IsArchSmooth3 y → T (x + y) = T x + T y) ∧
  (∀ (a : ℂ) x, WhittakerBlock.IsArchSmooth3 x → T (a • x) = a • T x) ∧ T 0 = 0

theorem CA.sm_zero : WhittakerBlock.IsArchSmooth3 (0 : GA → ℂ) := fun _ => contDiffOn_const

theorem CA.sm_add {x y : GA → ℂ} (hx : WhittakerBlock.IsArchSmooth3 x) (hy : WhittakerBlock.IsArchSmooth3 y) :
    WhittakerBlock.IsArchSmooth3 (x + y) := fun g => (hx g).add (hy g)

theorem CA.sm_smul (a : ℂ) {x : GA → ℂ} (hx : WhittakerBlock.IsArchSmooth3 x) :
    WhittakerBlock.IsArchSmooth3 (a • x) := fun g => (hx g).const_smul a

theorem CA.sm_sum {ι : Type*} (s : Finset ι) (F : ι → GA → ℂ) (h : ∀ i ∈ s, WhittakerBlock.IsArchSmooth3 (F i)) :
    WhittakerBlock.IsArchSmooth3 (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact CA.sm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact CA.sm_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem CA.good_archDeriv (i j : Fin 3) : CA.Good (WhittakerBlock.archDeriv i j) := by
  obtain ⟨hsm, hadd, hsmul, -, -⟩ :=
    LanglandsTunnell.CubicInduction.WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
  refine ⟨fun x hx => hsm x hx i j, fun x y hx hy => hadd x y hx hy i j, fun a x _ => hsmul a x i j, ?_⟩
  have h := hsmul 0 (0 : GA → ℂ) i j
  simpa using h

theorem CA.good_id : CA.Good (fun x : GA → ℂ => x) := ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ _ => rfl, rfl⟩

theorem CA.good_comp {T U : (GA → ℂ) → (GA → ℂ)} (hT : CA.Good T) (hU : CA.Good U) :
    CA.Good (fun x => T (U x)) := by
  refine ⟨fun x hx => hT.1 _ (hU.1 x hx), fun x y hx hy => ?_, fun a x hx => ?_, ?_⟩
  · show T (U (x + y)) = T (U x) + T (U y)
    rw [hU.2.1 x y hx hy, hT.2.1 _ _ (hU.1 x hx) (hU.1 y hy)]
  · show T (U (a • x)) = a • T (U x)
    rw [hU.2.2.1 a x hx, hT.2.2.1 a _ (hU.1 x hx)]
  · show T (U 0) = 0; rw [hU.2.2.2, hT.2.2.2]

theorem CA.good_sum {ι : Type*} (s : Finset ι) (T : ι → (GA → ℂ) → (GA → ℂ)) (h : ∀ i ∈ s, CA.Good (T i)) :
    CA.Good (fun x => ∑ i ∈ s, T i x) := by
  refine ⟨fun x hx => CA.sm_sum s _ fun i hi => (h i hi).1 x hx, fun x y hx hy => ?_, fun a x hx => ?_, ?_⟩
  · show ∑ i ∈ s, T i (x + y) = ∑ i ∈ s, T i x + ∑ i ∈ s, T i y
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i hi => (h i hi).2.1 x y hx hy
  · show ∑ i ∈ s, T i (a • x) = a • ∑ i ∈ s, T i x
    rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i hi => (h i hi).2.2.1 a x hx
  · exact Finset.sum_eq_zero fun i hi => (h i hi).2.2.2

theorem CA.good_smul_const (a : ℂ) {T : (GA → ℂ) → (GA → ℂ)} (hT : CA.Good T) : CA.Good (fun x => a • T x) := by
  refine ⟨fun x hx => CA.sm_smul a (hT.1 x hx), fun x y hx hy => ?_, fun b x hx => ?_, ?_⟩
  · show a • T (x + y) = a • T x + a • T y
    rw [hT.2.1 x y hx hy, smul_add]
  · show a • T (b • x) = b • (a • T x)
    rw [hT.2.2.1 b x hx, smul_comm]
  · show a • T 0 = 0; rw [hT.2.2.2, smul_zero]

theorem CA.good_iterate {T : (GA → ℂ) → (GA → ℂ)} (hT : CA.Good T) : ∀ l : ℕ, CA.Good (T^[l])
  | 0 => CA.good_id
  | l + 1 => by
    have h := CA.good_comp hT (CA.good_iterate hT l)
    refine ⟨fun x hx => ?_, fun x y hx hy => ?_, fun a x hx => ?_, ?_⟩
    · rw [Function.iterate_succ_apply']; exact h.1 x hx
    · simp only [Function.iterate_succ_apply']; exact h.2.1 x y hx hy
    · simp only [Function.iterate_succ_apply']; exact h.2.2.1 a x hx
    · rw [Function.iterate_succ_apply']; exact h.2.2.2

theorem CA.good_poly {T : (GA → ℂ) → (GA → ℂ)} (hT : CA.Good T) {N : ℕ} (a : Fin (N + 1) → ℂ) :
    CA.Good (fun x => ∑ l : Fin (N + 1), a l • (T^[(l : ℕ)] x)) :=
  CA.good_sum _ _ fun l _ => CA.good_smul_const (a l) (CA.good_iterate hT l)

theorem CA.good_foldr : ∀ w : List (Fin 3 × Fin 3),
    CA.Good (fun x : GA → ℂ => List.foldr (fun (ij : Fin 3 × Fin 3) (φ : GA → ℂ) => WhittakerBlock.archDeriv ij.1 ij.2 φ) x w)
  | [] => CA.good_id
  | ij :: w => by
    have h := CA.good_comp (CA.good_archDeriv ij.1 ij.2) (CA.good_foldr w)
    simpa only [List.foldr_cons] using h

theorem CA.casimir1_eq (x : GA → ℂ) : WhittakerBlock.casimir1 x = ∑ i : Fin 3, WhittakerBlock.archDeriv i i x := by
  funext g; simp only [WhittakerBlock.casimir1, Finset.sum_apply]

theorem CA.casimir2_eq (x : GA → ℂ) :
    WhittakerBlock.casimir2 x = ∑ i : Fin 3, ∑ j : Fin 3, WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i x) := by
  funext g; simp only [WhittakerBlock.casimir2, Finset.sum_apply]

theorem CA.casimir3_eq (x : GA → ℂ) :
    WhittakerBlock.casimir3 x = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i x)) := by
  funext g; simp only [WhittakerBlock.casimir3, Finset.sum_apply]

theorem CA.good_casimir1 : CA.Good (WhittakerBlock.casimir1 : (GA → ℂ) → (GA → ℂ)) := by
  have h := CA.good_sum (Finset.univ : Finset (Fin 3)) (fun i x => WhittakerBlock.archDeriv i i x)
    fun i _ => CA.good_archDeriv i i
  have heq : (WhittakerBlock.casimir1 : (GA → ℂ) → (GA → ℂ)) = fun x => ∑ i : Fin 3, WhittakerBlock.archDeriv i i x :=
    funext CA.casimir1_eq
  rw [heq]; exact h

theorem CA.good_casimir2 : CA.Good (WhittakerBlock.casimir2 : (GA → ℂ) → (GA → ℂ)) := by
  have h := CA.good_sum (Finset.univ : Finset (Fin 3))
    (fun i x => ∑ j : Fin 3, WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i x))
    fun i _ => CA.good_sum (Finset.univ : Finset (Fin 3)) _
      fun j _ => CA.good_comp (CA.good_archDeriv i j) (CA.good_archDeriv j i)
  have heq : (WhittakerBlock.casimir2 : (GA → ℂ) → (GA → ℂ)) =
      fun x => ∑ i : Fin 3, ∑ j : Fin 3, WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i x) :=
    funext CA.casimir2_eq
  rw [heq]; exact h

theorem CA.good_casimir3 : CA.Good (WhittakerBlock.casimir3 : (GA → ℂ) → (GA → ℂ)) := by
  have h := CA.good_sum (Finset.univ : Finset (Fin 3))
    (fun i x => ∑ j : Fin 3, ∑ k : Fin 3,
      WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i x)))
    fun i _ => CA.good_sum (Finset.univ : Finset (Fin 3)) _
      fun j _ => CA.good_sum (Finset.univ : Finset (Fin 3)) _
        fun k _ => CA.good_comp (CA.good_archDeriv i j) (CA.good_comp (CA.good_archDeriv j k) (CA.good_archDeriv k i))
  have heq : (WhittakerBlock.casimir3 : (GA → ℂ) → (GA → ℂ)) =
      fun x => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i x)) :=
    funext CA.casimir3_eq
  rw [heq]; exact h

theorem CA.comm_poly (S : Submodule ℂ (GA → ℂ))
    {T : (GA → ℂ) → (GA → ℂ)} (hST : ∀ x ∈ S, T x ∈ S)
    (R : (GA → ℂ) → (GA → ℂ)) (hRadd : ∀ x ∈ S, ∀ y ∈ S, R (x + y) = R x + R y)
    (hRsmul : ∀ (a : ℂ), ∀ x ∈ S, R (a • x) = a • R x)
    (hcomm : ∀ x ∈ S, R (T x) = T (R x))
    {N : ℕ} (a : Fin (N + 1) → ℂ) :
    ∀ x ∈ S, R (∑ l : Fin (N + 1), a l • (T^[(l : ℕ)] x)) = ∑ l : Fin (N + 1), a l • (T^[(l : ℕ)] (R x)) := by
  intro x hx
  have hiterS : ∀ l : ℕ, T^[l] x ∈ S := fun l => by
    induction l with
    | zero => exact hx
    | succ l ih => rw [Function.iterate_succ_apply']; exact hST _ ih
  have hiter : ∀ l : ℕ, R (T^[l] x) = T^[l] (R x) := fun l => by
    induction l with
    | zero => rfl
    | succ l ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hcomm _ (hiterS l), ih]

  have hsum : ∀ s : Finset (Fin (N + 1)),
      R (∑ l ∈ s, a l • (T^[(l : ℕ)] x)) = ∑ l ∈ s, a l • (T^[(l : ℕ)] (R x)) ∧
        (∑ l ∈ s, a l • (T^[(l : ℕ)] x)) ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      refine ⟨?_, Submodule.zero_mem _⟩
      have h := hRsmul 0 0 (Submodule.zero_mem _)
      simpa using h
    | insert l s hl ih =>
      rw [Finset.sum_insert hl, Finset.sum_insert hl]
      have hmem : a l • T^[(l : ℕ)] x ∈ S := Submodule.smul_mem _ _ (hiterS l)
      refine ⟨?_, Submodule.add_mem _ hmem ih.2⟩
      rw [hRadd _ hmem _ ih.2, ih.1, hRsmul _ _ (hiterS l), hiter]
  exact (hsum Finset.univ).1

end CasA
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_smoothingModule_casimir_relations.R1CuspDeriv"

section CasB

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory Filter Topology
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2 R1CuspDeriv

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

local notation "GA" => AdelicGL 3 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "μG" => NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
local notation "Dw" => List.foldr (fun (ij : Fin 3 × Fin 3) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) => WhittakerBlock.archDeriv (Prod.fst ij) (Prod.snd ij) φ)
local notation "Wh" => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
  NumberField.StandardAddChar.psiQ

theorem CB.Dw_add (w : List (Fin 3 × Fin 3)) {x y : GA → ℂ} (hx : WhittakerBlock.IsArchSmooth3 x)
    (hy : WhittakerBlock.IsArchSmooth3 y) : Dw (x + y) w = Dw x w + Dw y w := (CA.good_foldr w).2.1 x y hx hy

theorem CB.Dw_smul (w : List (Fin 3 × Fin 3)) (a : ℂ) {x : GA → ℂ} (hx : WhittakerBlock.IsArchSmooth3 x) :
    Dw (a • x) w = a • Dw x w := (CA.good_foldr w).2.2.1 a x hx

theorem CB.Dw_zero (w : List (Fin 3 × Fin 3)) : Dw (0 : GA → ℂ) w = 0 := (CA.good_foldr w).2.2.2

def CB.reg : Submodule ℂ (GA → ℂ) where
  carrier := {x | WhittakerBlock.IsArchSmooth3 x ∧ ∀ w : List (Fin 3 × Fin 3), Continuous (Dw x w)}
  zero_mem' := ⟨CA.sm_zero, fun w => by rw [CB.Dw_zero]; exact continuous_const⟩
  add_mem' := fun {x y} hx hy => ⟨CA.sm_add hx.1 hy.1, fun w => by
    rw [CB.Dw_add w hx.1 hy.1]; exact (hx.2 w).add (hy.2 w)⟩
  smul_mem' := fun a {x} hx => ⟨CA.sm_smul a hx.1, fun w => by
    rw [CB.Dw_smul w a hx.1]; exact (hx.2 w).const_smul a⟩

theorem CB.mem_reg {x : GA → ℂ} : x ∈ CB.reg ↔ WhittakerBlock.IsArchSmooth3 x ∧ ∀ w : List (Fin 3 × Fin 3), Continuous (Dw x w) :=
  Iff.rfl

theorem CB.continuous_of_mem_reg {x : GA → ℂ} (hx : x ∈ CB.reg) : Continuous x := by
  have h := hx.2 []; simpa only [List.foldr_nil] using h

theorem CB.cont_sum {ι : Type} (s : Finset ι) (f : ι → GA → ℂ) (h : ∀ i ∈ s, Continuous (f i)) :
    Continuous (∑ i ∈ s, f i) := by
  have : (∑ i ∈ s, f i) = fun a => ∑ i ∈ s, f i a := by funext a; simp only [Finset.sum_apply]
  rw [this]; exact continuous_finset_sum s h

theorem CB.archDeriv_mem_reg {x : GA → ℂ} (hx : x ∈ CB.reg) (i j : Fin 3) : WhittakerBlock.archDeriv i j x ∈ CB.reg :=
  ⟨(CA.good_archDeriv i j).1 x hx.1, fun w => by
    have : Dw (WhittakerBlock.archDeriv i j x) w = Dw x (w ++ [(i, j)]) := by
      rw [List.foldr_append]; rfl
    rw [this]; exact hx.2 _⟩

theorem CB.Dw_mem_reg {x : GA → ℂ} (hx : x ∈ CB.reg) : ∀ w : List (Fin 3 × Fin 3), Dw x w ∈ CB.reg
  | [] => hx
  | ij :: w => CB.archDeriv_mem_reg (CB.Dw_mem_reg hx w) ij.1 ij.2

theorem CB.casimir1_mem_reg {x : GA → ℂ} (hx : x ∈ CB.reg) : WhittakerBlock.casimir1 x ∈ CB.reg := by
  rw [CA.casimir1_eq]; exact Submodule.sum_mem _ fun i _ => CB.archDeriv_mem_reg hx i i

theorem CB.casimir2_mem_reg {x : GA → ℂ} (hx : x ∈ CB.reg) : WhittakerBlock.casimir2 x ∈ CB.reg := by
  rw [CA.casimir2_eq]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    CB.archDeriv_mem_reg (CB.archDeriv_mem_reg hx j i) i j

theorem CB.casimir3_mem_reg {x : GA → ℂ} (hx : x ∈ CB.reg) : WhittakerBlock.casimir3 x ∈ CB.reg := by
  rw [CA.casimir3_eq]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ =>
    CB.archDeriv_mem_reg (CB.archDeriv_mem_reg (CB.archDeriv_mem_reg hx k i) j k) i j

theorem CB.Dw_casimir_comm {x : GA → ℂ} (hx : x ∈ CB.reg) : ∀ w : List (Fin 3 × Fin 3),
    Dw (WhittakerBlock.casimir1 x) w = WhittakerBlock.casimir1 (Dw x w) ∧
    Dw (WhittakerBlock.casimir2 x) w = WhittakerBlock.casimir2 (Dw x w) ∧
    Dw (WhittakerBlock.casimir3 x) w = WhittakerBlock.casimir3 (Dw x w)
  | [] => ⟨rfl, rfl, rfl⟩
  | ij :: w => by
    obtain ⟨h1, h2, h3⟩ := CB.Dw_casimir_comm hx w
    have hc := (LanglandsTunnell.CubicInduction.WhittakerBlock.casimir_archDeriv_and_comm (Dw x w)
      (CB.Dw_mem_reg hx w).1).1 ij.1 ij.2
    simp only [List.foldr_cons]
    rw [h1, h2, h3]
    exact ⟨(hc.1).symm, (hc.2.1).symm, (hc.2.2).symm⟩

theorem CB.continuous_upperUnipotent3 :
    Continuous fun q : 𝔸 × 𝔸 × 𝔸 => (upperUnipotent3 q.1 q.2.1 q.2.2 : GA) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_apply, upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    have hinv : ∀ x y z : 𝔸, (((upperUnipotent3 x y z)⁻¹ : GA) : Matrix (Fin 3) (Fin 3) 𝔸) =
        !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := fun _ _ _ => rfl
    simp only [hinv]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem CB.W_layers {H : GA → ℂ} (hH : Continuous H) (g : GA) {C : Set 𝔸} (hC : IsCompact C)
    (hνC : ∀ᵐ y ∂ν0, y ∈ C) :
    (∀ x y : 𝔸, Integrable (fun z => H (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y))) ν0) ∧
    (∀ x : 𝔸, Integrable (fun y => ∫ z, H (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) ∂ν0) ν0) ∧
    Integrable (fun x => ∫ y, ∫ z, H (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) ∂ν0 ∂ν0) ν0 ∧
    Continuous (fun x => ∫ y, ∫ z, H (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) ∂ν0 ∂ν0) := by
  obtain ⟨K, hK⟩ : ∃ K : 𝔸 → 𝔸 → 𝔸 → ℂ,
      ∀ x y z, K x y z = H (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hψ : Continuous fun a : 𝔸 => NumberField.StandardAddChar.psiQ a := NumberField.StandardAddChar.continuous_psiQ
  have hKc : Continuous fun q : 𝔸 × 𝔸 × 𝔸 => K q.1 q.2.1 q.2.2 := by
    simp only [hK]
    exact (hH.comp (CB.continuous_upperUnipotent3.mul continuous_const)).mul
      (hψ.comp (continuous_fst.add (continuous_fst.comp continuous_snd)).neg)
  have h3 : Continuous fun q : 𝔸 × 𝔸 => ∫ z, K q.1 q.2 z ∂ν0 :=
    continuous_integral_of_continuous ν0 hC hνC (fun q : 𝔸 × 𝔸 => fun z => K q.1 q.2 z)
      (hKc.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
  have h2 : Continuous fun x : 𝔸 => ∫ y, ∫ z, K x y z ∂ν0 ∂ν0 :=
    continuous_integral_of_continuous ν0 hC hνC (fun x : 𝔸 => fun y => ∫ z, K x y z ∂ν0) h3
  have i3 : ∀ x y : 𝔸, Integrable (fun z => K x y z) ν0 := fun x y =>
    integrable_of_continuous ν0 hC hνC _ (hKc.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
  have i2 : ∀ x : 𝔸, Integrable (fun y => ∫ z, K x y z ∂ν0) ν0 := fun x =>
    integrable_of_continuous ν0 hC hνC _ (h3.comp (continuous_const.prodMk continuous_id))
  have i1 : Integrable (fun x => ∫ y, ∫ z, K x y z ∂ν0 ∂ν0) ν0 := integrable_of_continuous ν0 hC hνC _ h2
  simp only [hK] at i3 i2 i1 h2
  exact ⟨i3, i2, i1, h2⟩

theorem CB.W_add {F G : GA → ℂ} (hF : Continuous F) (hG : Continuous G) : Wh (F + G) = Wh F + Wh G := by
  funext g
  obtain ⟨C, hC, hνC⟩ := exists_compact_ae
  obtain ⟨hF3, hF2, hF1, -⟩ := CB.W_layers hF g hC hνC
  obtain ⟨hG3, hG2, hG1, -⟩ := CB.W_layers hG g hC hνC
  show ∫ x, ∫ y, ∫ z, (F + G) (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) ∂ν0 ∂ν0 ∂ν0 =
    (∫ x, ∫ y, ∫ z, F (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) ∂ν0 ∂ν0 ∂ν0) +
    ∫ x, ∫ y, ∫ z, G (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) ∂ν0 ∂ν0 ∂ν0
  have e3 : ∀ x y : 𝔸, ∫ z, (F + G) (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) ∂ν0 =
      (∫ z, F (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) ∂ν0) +
      ∫ z, G (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) ∂ν0 := by
    intro x y
    simp only [Pi.add_apply, add_mul]
    exact integral_add (hF3 x y) (hG3 x y)
  simp_rw [e3]
  have e2 : ∀ x : 𝔸, ∫ y, ((∫ z, F (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) ∂ν0) +
      ∫ z, G (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) ∂ν0) ∂ν0 =
      (∫ y, ∫ z, F (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) ∂ν0 ∂ν0) +
      ∫ y, ∫ z, G (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) ∂ν0 ∂ν0 := by
    intro x
    exact integral_add (hF2 x) (hG2 x)
  simp_rw [e2]
  exact integral_add hF1 hG1

theorem CB.W_smul (a : ℂ) (F : GA → ℂ) : Wh (a • F) = a • Wh F := by
  funext g
  show ∫ x, ∫ y, ∫ z, (a • F) (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) ∂ν0 ∂ν0 ∂ν0 =
    a * ∫ x, ∫ y, ∫ z, F (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y)) ∂ν0 ∂ν0 ∂ν0
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem CB.W_casimir_comm {x : GA → ℂ} (hx : x ∈ CB.reg) :
    Wh (WhittakerBlock.casimir1 x) = WhittakerBlock.casimir1 (Wh x) ∧
    Wh (WhittakerBlock.casimir2 x) = WhittakerBlock.casimir2 (Wh x) ∧
    Wh (WhittakerBlock.casimir3 x) = WhittakerBlock.casimir3 (Wh x) := by
  have hA := (LanglandsTunnell.CubicInduction.whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3 x hx.1 hx.2).1

  have hsum : ∀ {ι : Type} (s : Finset ι) (F : ι → GA → ℂ), (∀ i ∈ s, Continuous (F i)) →
      Wh (∑ i ∈ s, F i) = ∑ i ∈ s, Wh (F i) := by
    intro ι s F hF
    classical
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      have h := CB.W_smul 0 (0 : GA → ℂ)
      simpa using h
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        CB.W_add (hF a (Finset.mem_insert_self _ _))
          (CB.cont_sum _ _ fun i hi => hF i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]
  have hc1 : ∀ i j : Fin 3, ∀ {y : GA → ℂ}, y ∈ CB.reg → Continuous (WhittakerBlock.archDeriv i j y) :=
    fun i j y hy => CB.continuous_of_mem_reg (CB.archDeriv_mem_reg hy i j)
  refine ⟨?_, ?_, ?_⟩
  · rw [CA.casimir1_eq, CA.casimir1_eq,
      hsum Finset.univ (fun i => WhittakerBlock.archDeriv i i x) fun i _ => hc1 i i hx]
    exact Finset.sum_congr rfl fun i _ => hA [(i, i)]
  · rw [CA.casimir2_eq, CA.casimir2_eq,
      hsum Finset.univ (fun i => ∑ j : Fin 3, WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i x))
        fun i _ => CB.cont_sum _ _ fun j _ => hc1 i j (CB.archDeriv_mem_reg hx j i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsum Finset.univ (fun j => WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i x))
        fun j _ => hc1 i j (CB.archDeriv_mem_reg hx j i)]
    exact Finset.sum_congr rfl fun j _ => hA [(i, j), (j, i)]
  · rw [CA.casimir3_eq, CA.casimir3_eq,
      hsum Finset.univ (fun i => ∑ j : Fin 3, ∑ k : Fin 3,
        WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i x)))
        fun i _ => CB.cont_sum _ _ fun j _ => CB.cont_sum _ _ fun k _ =>
          hc1 i j (CB.archDeriv_mem_reg (CB.archDeriv_mem_reg hx k i) j k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsum Finset.univ (fun j => ∑ k : Fin 3,
        WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i x)))
        fun j _ => CB.cont_sum _ _ fun k _ => hc1 i j (CB.archDeriv_mem_reg (CB.archDeriv_mem_reg hx k i) j k)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsum Finset.univ (fun k => WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i x)))
        fun k _ => hc1 i j (CB.archDeriv_mem_reg (CB.archDeriv_mem_reg hx k i) j k)]
    exact Finset.sum_congr rfl fun k _ => hA [(i, j), (j, k), (k, i)]

theorem CB.smoothing_add {φ : GA → ℂ} (hφ : IsSmoothingKernel φ) {F G : GA → ℂ} (hF : Continuous F)
    (hG : Continuous G) : smoothingOperator φ (F + G) = smoothingOperator φ F + smoothingOperator φ G := by
  obtain ⟨hφc, hφs⟩ := LanglandsTunnell.CubicInduction.SlabL2.continuous_and_hasCompactSupport_of_isSmoothingKernel φ hφ
  funext x
  simp only [smoothingOperator_apply, Pi.add_apply, mul_add]
  have hint : ∀ {H : GA → ℂ}, Continuous H → Integrable (fun g => φ g * H (x * g)) μG := fun hH =>
    (hφc.mul (hH.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport hφs.mul_right
  exact integral_add (hint hF) (hint hG)

theorem CB.smoothing_smul (φ : GA → ℂ) (a : ℂ) (F : GA → ℂ) :
    smoothingOperator φ (a • F) = a • smoothingOperator φ F := by
  funext x
  simp only [smoothingOperator_apply, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr 1; funext g; ring

theorem CB.smoothing_zero (φ : GA → ℂ) : smoothingOperator φ (0 : GA → ℂ) = 0 := by
  funext x; simp [smoothingOperator_apply]

theorem CB.W_zero : Wh (0 : GA → ℂ) = 0 := by
  have h := CB.W_smul 0 (0 : GA → ℂ); simpa using h

end CasB
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_smoothingModule_casimir_relations.R1CuspDeriv"

section CasC

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory Filter Topology
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2 R1CuspDeriv
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

local notation "GA" => AdelicGL 3 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "μG" => NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
local notation "Dw" => List.foldr (fun (ij : Fin 3 × Fin 3) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) => WhittakerBlock.archDeriv (Prod.fst ij) (Prod.snd ij) φ)
local notation "Wh" => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
  NumberField.StandardAddChar.psiQ

noncomputable def CC.P (T : (GA → ℂ) → (GA → ℂ)) {N : ℕ} (a : Fin (N + 1) → ℂ) (x : GA → ℂ) : GA → ℂ :=
  ∑ l : Fin (N + 1), a l • (T^[(l : ℕ)] x)

theorem CC.P_comm (T : (GA → ℂ) → (GA → ℂ)) (hT : ∀ x ∈ CB.reg, T x ∈ CB.reg) {N : ℕ} (a : Fin (N + 1) → ℂ)
    (R : (GA → ℂ) → (GA → ℂ)) (hRadd : ∀ x ∈ CB.reg, ∀ y ∈ CB.reg, R (x + y) = R x + R y)
    (hRsmul : ∀ (c : ℂ), ∀ x ∈ CB.reg, R (c • x) = c • R x) (hcomm : ∀ x ∈ CB.reg, R (T x) = T (R x))
    {x : GA → ℂ} (hx : x ∈ CB.reg) : R (CC.P T a x) = CC.P T a (R x) :=
  CA.comm_poly CB.reg hT R hRadd hRsmul hcomm a x hx

theorem CC.P_add {T : (GA → ℂ) → (GA → ℂ)} (hT : CA.Good T) {N : ℕ} (a : Fin (N + 1) → ℂ) {x y : GA → ℂ}
    (hx : WhittakerBlock.IsArchSmooth3 x) (hy : WhittakerBlock.IsArchSmooth3 y) :
    CC.P T a (x + y) = CC.P T a x + CC.P T a y := (CA.good_poly hT a).2.1 x y hx hy

theorem CC.P_smul {T : (GA → ℂ) → (GA → ℂ)} (hT : CA.Good T) {N : ℕ} (a : Fin (N + 1) → ℂ) (c : ℂ) {x : GA → ℂ}
    (hx : WhittakerBlock.IsArchSmooth3 x) : CC.P T a (c • x) = c • CC.P T a x := (CA.good_poly hT a).2.2.1 c x hx

theorem CC.P_zero {T : (GA → ℂ) → (GA → ℂ)} (hT : CA.Good T) {N : ℕ} (a : Fin (N + 1) → ℂ) :
    CC.P T a 0 = 0 := (CA.good_poly hT a).2.2.2

theorem CC.Dw_smoothing {φ : GA → ℂ} (hφ : IsSmoothingKernel φ) {u : GA → ℂ} (hu : LocallyIntegrable u μG) :
    ∀ wd : List (Fin 3 × Fin 3), ∃ ψ : GA → ℂ, IsSmoothingKernel ψ ∧ Dw (smoothingOperator φ u) wd = smoothingOperator ψ u
  | [] => ⟨φ, hφ, rfl⟩
  | ij :: wd => by
    obtain ⟨ψ, hψ, heq⟩ := CC.Dw_smoothing hφ hu wd
    obtain ⟨hψ', heq'⟩ := LanglandsTunnell.CubicInduction.SlabL2.archDeriv_smoothingOperator ψ u hψ hu ij.1 ij.2
    refine ⟨_, hψ', ?_⟩
    simp only [List.foldr_cons]
    rw [heq, heq']

theorem CC.smoothing_mem_reg {φ : GA → ℂ} (hφ : IsSmoothingKernel φ) {u : GA → ℂ} (hu : LocallyIntegrable u μG) :
    smoothingOperator φ u ∈ CB.reg := by
  refine ⟨(LanglandsTunnell.CubicInduction.SlabL2.continuous_and_isArchSmooth3_smoothingOperator φ u hφ hu).2, fun wd => ?_⟩
  obtain ⟨ψ, hψ, heq⟩ := CC.Dw_smoothing hφ hu wd
  rw [heq]
  exact (LanglandsTunnell.CubicInduction.SlabL2.continuous_and_isArchSmooth3_smoothingOperator ψ u hψ hu).1

theorem CC.main
    (ω : (𝔸)ˣ →* ℂˣ)
    (f : GA → ℂ) (hc : Continuous f)
    (hmg : IsModerateGrowth3 ℚ f)
    (hsa : WhittakerBlock.IsArchSmooth3 f)
    (hKf : ∃ s : Finset (GA → ℂ), ∀ k : GA,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (GA → ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → GA) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite fun x => ∑ i, c i * f (x * t i))
    (u : GA → ℂ)
    (hu : u ∈ Submodule.span ℂ {φ : GA → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : GA),
          φ = Dw (fun g => ∑ i, c i * f (g * h * t i)) w})
    (M : Submodule ℂ (GA → ℂ))
    (hM : M = Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : GA → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (GA → ℂ), ∀ k : GA,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (GA → ℂ))})) :
    (∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ M,
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l] (Wh w))) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] (Wh w))) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] (Wh w))) = 0) ∧
    (∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ M,
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l] w)) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0) := by
  classical
  obtain ⟨⟨N₁, a₁, ha₁, hv₁⟩, ⟨N₂, a₂, ha₂, hv₂⟩, ⟨N₃, a₃, ha₃, hv₃⟩⟩ := hz
  set v : GA → ℂ := fun x => ∑ i, c i * f (x * t i) with hv
  have hvsa : WhittakerBlock.IsArchSmooth3 v := isArchSmooth3_sum_translate f hsa n c t ht
  obtain ⟨hvw, -⟩ :=
    LanglandsTunnell.CubicInduction.continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
      f hc hmg hsa hKf n c t ht ⟨⟨N₁, a₁, ha₁, hv₁⟩, ⟨N₂, a₂, ha₂, hv₂⟩, ⟨N₃, a₃, ha₃, hv₃⟩⟩
  have hvreg : v ∈ CB.reg := ⟨hvsa, hvw⟩

  have hPv : CC.P WhittakerBlock.casimir1 a₁ v = 0 ∧ CC.P WhittakerBlock.casimir2 a₂ v = 0 ∧
      CC.P WhittakerBlock.casimir3 a₃ v = 0 := ⟨hv₁, hv₂, hv₃⟩

  have hT1 : ∀ x ∈ CB.reg, WhittakerBlock.casimir1 x ∈ CB.reg := fun x hx => CB.casimir1_mem_reg hx
  have hT2 : ∀ x ∈ CB.reg, WhittakerBlock.casimir2 x ∈ CB.reg := fun x hx => CB.casimir2_mem_reg hx
  have hT3 : ∀ x ∈ CB.reg, WhittakerBlock.casimir3 x ∈ CB.reg := fun x hx => CB.casimir3_mem_reg hx

  have htrans_reg : ∀ (w : List (Fin 3 × Fin 3)) (h : GA), (fun g => Dw v w (g * h)) ∈ CB.reg := by
    intro w h
    have hFsm : WhittakerBlock.IsArchSmooth3 (Dw v w) := isArchSmooth3_foldr v hvsa w
    refine ⟨LanglandsTunnell.CubicInduction.isArchSmooth3_mul_right _ hFsm h, fun wd => ?_⟩
    obtain ⟨coeff, hcoeffc, hcoeff⟩ :=
      LanglandsTunnell.CubicInduction.exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum wd
    have heq : Dw (fun x => Dw v w (x * h)) wd =
        fun g => ∑ fw : Fin wd.length → Fin 3 × Fin 3, coeff h fw * Dw v (List.ofFn fw ++ w) (g * h) := by
      funext g
      rw [hcoeff (Dw v w) hFsm h g]
      simp only [List.foldr_append]
    rw [heq]
    exact continuous_finset_sum _ fun fw _ => continuous_const.mul ((hvw _).comp (continuous_id.mul continuous_const))

  have hureg : u ∈ CB.reg := by
    refine (Submodule.span_le.2 ?_) hu
    rintro φ ⟨w, h, rfl⟩
    have h1 : (fun g => ∑ i, c i * f (g * h * t i)) = fun x => v (x * h) := by
      funext x; simp only [hv, mul_assoc]
    rw [h1]

    obtain ⟨coeff, hcoeffc, hcoeff⟩ :=
      LanglandsTunnell.CubicInduction.exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum w
    have heq : Dw (fun x => v (x * h)) w =
        ∑ fw : Fin w.length → Fin 3 × Fin 3, coeff h fw • (fun g => Dw v (List.ofFn fw) (g * h)) := by
      funext g
      rw [hcoeff v hvsa h g]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [heq]
    exact Submodule.sum_mem _ fun fw _ => Submodule.smul_mem _ _ (htrans_reg _ h)

  have hPu : CC.P WhittakerBlock.casimir1 a₁ u = 0 ∧ CC.P WhittakerBlock.casimir2 a₂ u = 0 ∧
      CC.P WhittakerBlock.casimir3 a₃ u = 0 := by

    have hgen : ∀ (w : List (Fin 3 × Fin 3)) (h : GA),
        CC.P WhittakerBlock.casimir1 a₁ (fun g => Dw v w (g * h)) = 0 ∧
        CC.P WhittakerBlock.casimir2 a₂ (fun g => Dw v w (g * h)) = 0 ∧
        CC.P WhittakerBlock.casimir3 a₃ (fun g => Dw v w (g * h)) = 0 := by
      intro w h

      set Rh : (GA → ℂ) → (GA → ℂ) := fun y => fun g => y (g * h) with hRh
      have hRadd : ∀ x ∈ CB.reg, ∀ y ∈ CB.reg, Rh (x + y) = Rh x + Rh y := fun _ _ _ _ => rfl
      have hRsmul : ∀ (a : ℂ), ∀ x ∈ CB.reg, Rh (a • x) = a • Rh x := fun _ _ _ => rfl
      have hRcomm : ∀ y ∈ CB.reg,
          Rh (WhittakerBlock.casimir1 y) = WhittakerBlock.casimir1 (Rh y) ∧
          Rh (WhittakerBlock.casimir2 y) = WhittakerBlock.casimir2 (Rh y) ∧
          Rh (WhittakerBlock.casimir3 y) = WhittakerBlock.casimir3 (Rh y) := by
        intro y hy
        have hh := LanglandsTunnell.CubicInduction.WhittakerBlock.casimir_translateRight y hy.1 h
        exact ⟨hh.1.symm, hh.2.1.symm, hh.2.2.symm⟩

      set Rw : (GA → ℂ) → (GA → ℂ) := fun y => Dw y w with hRw
      have hWadd : ∀ x ∈ CB.reg, ∀ y ∈ CB.reg, Rw (x + y) = Rw x + Rw y := fun x hx y hy => CB.Dw_add w hx.1 hy.1
      have hWsmul : ∀ (a : ℂ), ∀ x ∈ CB.reg, Rw (a • x) = a • Rw x := fun a x hx => CB.Dw_smul w a hx.1
      have hWcomm : ∀ y ∈ CB.reg,
          Rw (WhittakerBlock.casimir1 y) = WhittakerBlock.casimir1 (Rw y) ∧
          Rw (WhittakerBlock.casimir2 y) = WhittakerBlock.casimir2 (Rw y) ∧
          Rw (WhittakerBlock.casimir3 y) = WhittakerBlock.casimir3 (Rw y) := fun y hy => CB.Dw_casimir_comm hy w
      have hvw_reg : Dw v w ∈ CB.reg := CB.Dw_mem_reg hvreg w
      have hRw0 : Rw 0 = 0 := CB.Dw_zero w
      have hRh0 : Rh 0 = 0 := rfl
      refine ⟨?_, ?_, ?_⟩
      · have e1 := CC.P_comm _ hT1 a₁ Rw hWadd hWsmul (fun y hy => (hWcomm y hy).1) hvreg
        have e2 := CC.P_comm _ hT1 a₁ Rh hRadd hRsmul (fun y hy => (hRcomm y hy).1) hvw_reg
        rw [hPv.1, hRw0] at e1
        show CC.P WhittakerBlock.casimir1 a₁ (Rh (Rw v)) = 0
        rw [← e2, ← e1, hRh0]
      · have e1 := CC.P_comm _ hT2 a₂ Rw hWadd hWsmul (fun y hy => (hWcomm y hy).2.1) hvreg
        have e2 := CC.P_comm _ hT2 a₂ Rh hRadd hRsmul (fun y hy => (hRcomm y hy).2.1) hvw_reg
        rw [hPv.2.1, hRw0] at e1
        show CC.P WhittakerBlock.casimir2 a₂ (Rh (Rw v)) = 0
        rw [← e2, ← e1, hRh0]
      · have e1 := CC.P_comm _ hT3 a₃ Rw hWadd hWsmul (fun y hy => (hWcomm y hy).2.2) hvreg
        have e2 := CC.P_comm _ hT3 a₃ Rh hRadd hRsmul (fun y hy => (hRcomm y hy).2.2) hvw_reg
        rw [hPv.2.2, hRw0] at e1
        show CC.P WhittakerBlock.casimir3 a₃ (Rh (Rw v)) = 0
        rw [← e2, ← e1, hRh0]

    have key : ∀ x ∈ Submodule.span ℂ {φ : GA → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : GA),
        φ = Dw (fun g => ∑ i, c i * f (g * h * t i)) w},
        x ∈ CB.reg → (CC.P WhittakerBlock.casimir1 a₁ x = 0 ∧ CC.P WhittakerBlock.casimir2 a₂ x = 0 ∧
          CC.P WhittakerBlock.casimir3 a₃ x = 0) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        intro _
        obtain ⟨w, h, rfl⟩ := hx
        have h1 : (fun g => ∑ i, c i * f (g * h * t i)) = fun x => v (x * h) := by
          funext x; simp only [hv, mul_assoc]
        rw [h1]
        obtain ⟨coeff, -, hcoeff⟩ :=
          LanglandsTunnell.CubicInduction.exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum w
        have heq : Dw (fun x => v (x * h)) w =
            ∑ fw : Fin w.length → Fin 3 × Fin 3, coeff h fw • (fun g => Dw v (List.ofFn fw) (g * h)) := by
          funext g
          rw [hcoeff v hvsa h g]
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [heq]

        have hfin : ∀ s : Finset (Fin w.length → Fin 3 × Fin 3),
            (∑ fw ∈ s, coeff h fw • (fun g => Dw v (List.ofFn fw) (g * h))) ∈ CB.reg ∧
            CC.P WhittakerBlock.casimir1 a₁ (∑ fw ∈ s, coeff h fw • (fun g => Dw v (List.ofFn fw) (g * h))) = 0 ∧
            CC.P WhittakerBlock.casimir2 a₂ (∑ fw ∈ s, coeff h fw • (fun g => Dw v (List.ofFn fw) (g * h))) = 0 ∧
            CC.P WhittakerBlock.casimir3 a₃ (∑ fw ∈ s, coeff h fw • (fun g => Dw v (List.ofFn fw) (g * h))) = 0 := by
          intro s
          induction s using Finset.induction_on with
          | empty =>
            simp only [Finset.sum_empty]
            exact ⟨Submodule.zero_mem _, CC.P_zero CA.good_casimir1 a₁, CC.P_zero CA.good_casimir2 a₂,
              CC.P_zero CA.good_casimir3 a₃⟩
          | insert fw s hfw ih =>
            rw [Finset.sum_insert hfw]
            have hm : coeff h fw • (fun g => Dw v (List.ofFn fw) (g * h)) ∈ CB.reg :=
              Submodule.smul_mem _ _ (htrans_reg _ h)
            have hg := hgen (List.ofFn fw) h
            refine ⟨Submodule.add_mem _ hm ih.1, ?_, ?_, ?_⟩
            · rw [CC.P_add CA.good_casimir1 a₁ hm.1 ih.1.1, ih.2.1,
                CC.P_smul CA.good_casimir1 a₁ _ (htrans_reg _ h).1, hg.1, smul_zero, add_zero]
            · rw [CC.P_add CA.good_casimir2 a₂ hm.1 ih.1.1, ih.2.2.1,
                CC.P_smul CA.good_casimir2 a₂ _ (htrans_reg _ h).1, hg.2.1, smul_zero, add_zero]
            · rw [CC.P_add CA.good_casimir3 a₃ hm.1 ih.1.1, ih.2.2.2,
                CC.P_smul CA.good_casimir3 a₃ _ (htrans_reg _ h).1, hg.2.2, smul_zero, add_zero]
        exact (hfin Finset.univ).2
      | zero => intro _; exact ⟨CC.P_zero CA.good_casimir1 a₁, CC.P_zero CA.good_casimir2 a₂, CC.P_zero CA.good_casimir3 a₃⟩
      | add x y hx' hy' hx hy =>
        intro hxy
        have hxr : x ∈ CB.reg := (Submodule.span_le.2 ?_) hx'
        have hyr : y ∈ CB.reg := (Submodule.span_le.2 ?_) hy'
        · obtain ⟨h1, h2, h3⟩ := hx hxr
          obtain ⟨k1, k2, k3⟩ := hy hyr
          exact ⟨by rw [CC.P_add CA.good_casimir1 a₁ hxr.1 hyr.1, h1, k1, add_zero],
            by rw [CC.P_add CA.good_casimir2 a₂ hxr.1 hyr.1, h2, k2, add_zero],
            by rw [CC.P_add CA.good_casimir3 a₃ hxr.1 hyr.1, h3, k3, add_zero]⟩
        all_goals
          rintro φ ⟨w, h, rfl⟩
          have h1 : (fun g => ∑ i, c i * f (g * h * t i)) = fun x => v (x * h) := by
            funext x; simp only [hv, mul_assoc]
          rw [h1]
          obtain ⟨coeff, -, hcoeff⟩ :=
            LanglandsTunnell.CubicInduction.exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum w
          have heq : Dw (fun x => v (x * h)) w =
              ∑ fw : Fin w.length → Fin 3 × Fin 3, coeff h fw • (fun g => Dw v (List.ofFn fw) (g * h)) := by
            funext g
            rw [hcoeff v hvsa h g]
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [heq]
          exact Submodule.sum_mem _ fun fw _ => Submodule.smul_mem _ _ (htrans_reg _ h)
      | smul a x hx' hx =>
        intro haxr
        have hxr : x ∈ CB.reg := by
          refine (Submodule.span_le.2 ?_) hx'
          rintro φ ⟨w, h, rfl⟩
          have h1 : (fun g => ∑ i, c i * f (g * h * t i)) = fun x => v (x * h) := by
            funext x; simp only [hv, mul_assoc]
          rw [h1]
          obtain ⟨coeff, -, hcoeff⟩ :=
            LanglandsTunnell.CubicInduction.exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum w
          have heq : Dw (fun x => v (x * h)) w =
              ∑ fw : Fin w.length → Fin 3 × Fin 3, coeff h fw • (fun g => Dw v (List.ofFn fw) (g * h)) := by
            funext g
            rw [hcoeff v hvsa h g]
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [heq]
          exact Submodule.sum_mem _ fun fw _ => Submodule.smul_mem _ _ (htrans_reg _ h)
        obtain ⟨h1, h2, h3⟩ := hx hxr
        exact ⟨by rw [CC.P_smul CA.good_casimir1 a₁ a hxr.1, h1, smul_zero],
          by rw [CC.P_smul CA.good_casimir2 a₂ a hxr.1, h2, smul_zero],
          by rw [CC.P_smul CA.good_casimir3 a₃ a hxr.1, h3, smul_zero]⟩
    exact key u hu hureg

  have huli : LocallyIntegrable u μG := (CB.continuous_of_mem_reg hureg).locallyIntegrable

  have hMreg : M ≤ CB.reg := by
    rw [hM]
    refine Submodule.span_le.2 ?_
    rintro w ⟨φ, ⟨hφ, -⟩, rfl⟩
    exact CC.smoothing_mem_reg hφ huli

  have hgenM : ∀ φ : GA → ℂ, IsSmoothingKernel φ →
      CC.P WhittakerBlock.casimir1 a₁ (smoothingOperator φ u) = 0 ∧
      CC.P WhittakerBlock.casimir2 a₂ (smoothingOperator φ u) = 0 ∧
      CC.P WhittakerBlock.casimir3 a₃ (smoothingOperator φ u) = 0 := by
    intro φ hφ
    set Rφ : (GA → ℂ) → (GA → ℂ) := fun y => smoothingOperator φ y with hRφ
    have hRadd : ∀ x ∈ CB.reg, ∀ y ∈ CB.reg, Rφ (x + y) = Rφ x + Rφ y :=
      fun x hx y hy => CB.smoothing_add hφ (CB.continuous_of_mem_reg hx) (CB.continuous_of_mem_reg hy)
    have hRsmul : ∀ (a : ℂ), ∀ x ∈ CB.reg, Rφ (a • x) = a • Rφ x := fun a x _ => CB.smoothing_smul φ a x
    have hRcomm : ∀ y ∈ CB.reg,
        Rφ (WhittakerBlock.casimir1 y) = WhittakerBlock.casimir1 (Rφ y) ∧
        Rφ (WhittakerBlock.casimir2 y) = WhittakerBlock.casimir2 (Rφ y) ∧
        Rφ (WhittakerBlock.casimir3 y) = WhittakerBlock.casimir3 (Rφ y) := by
      intro y hy
      have hh := LanglandsTunnell.CubicInduction.SlabL2.casimir_smoothingOperator φ y hφ hy.1 hy.2
      exact ⟨hh.1.symm, hh.2.1.symm, hh.2.2.symm⟩
    have hR0 : Rφ 0 = 0 := CB.smoothing_zero φ
    refine ⟨?_, ?_, ?_⟩
    · have e := CC.P_comm _ hT1 a₁ Rφ hRadd hRsmul (fun y hy => (hRcomm y hy).1) hureg
      rw [hPu.1, hR0] at e; exact e.symm
    · have e := CC.P_comm _ hT2 a₂ Rφ hRadd hRsmul (fun y hy => (hRcomm y hy).2.1) hureg
      rw [hPu.2.1, hR0] at e; exact e.symm
    · have e := CC.P_comm _ hT3 a₃ Rφ hRadd hRsmul (fun y hy => (hRcomm y hy).2.2) hureg
      rw [hPu.2.2, hR0] at e; exact e.symm

  have hWhadd : ∀ x ∈ CB.reg, ∀ y ∈ CB.reg, Wh (x + y) = Wh x + Wh y :=
    fun x hx y hy => CB.W_add (CB.continuous_of_mem_reg hx) (CB.continuous_of_mem_reg hy)
  have hWhsmul : ∀ (a : ℂ), ∀ x ∈ CB.reg, Wh (a • x) = a • Wh x := fun a x _ => CB.W_smul a x
  have hWhcomm : ∀ y ∈ CB.reg,
      Wh (WhittakerBlock.casimir1 y) = WhittakerBlock.casimir1 (Wh y) ∧
      Wh (WhittakerBlock.casimir2 y) = WhittakerBlock.casimir2 (Wh y) ∧
      Wh (WhittakerBlock.casimir3 y) = WhittakerBlock.casimir3 (Wh y) := fun y hy => CB.W_casimir_comm hy
  have hWP : ∀ x ∈ CB.reg,
      (CC.P WhittakerBlock.casimir1 a₁ x = 0 → CC.P WhittakerBlock.casimir1 a₁ (Wh x) = 0) ∧
      (CC.P WhittakerBlock.casimir2 a₂ x = 0 → CC.P WhittakerBlock.casimir2 a₂ (Wh x) = 0) ∧
      (CC.P WhittakerBlock.casimir3 a₃ x = 0 → CC.P WhittakerBlock.casimir3 a₃ (Wh x) = 0) := by
    intro x hx
    refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩
    · have e := CC.P_comm _ hT1 a₁ (Wh) hWhadd hWhsmul (fun y hy => (hWhcomm y hy).1) hx
      rw [h0, CB.W_zero] at e; exact e.symm
    · have e := CC.P_comm _ hT2 a₂ (Wh) hWhadd hWhsmul (fun y hy => (hWhcomm y hy).2.1) hx
      rw [h0, CB.W_zero] at e; exact e.symm
    · have e := CC.P_comm _ hT3 a₃ (Wh) hWhadd hWhsmul (fun y hy => (hWhcomm y hy).2.2) hx
      rw [h0, CB.W_zero] at e; exact e.symm

  have hallM : ∀ w ∈ M, CC.P WhittakerBlock.casimir1 a₁ w = 0 ∧ CC.P WhittakerBlock.casimir2 a₂ w = 0 ∧
      CC.P WhittakerBlock.casimir3 a₃ w = 0 := by
    intro w hw
    have hw' := hw
    rw [hM] at hw'
    have key : ∀ x ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : GA → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (GA → ℂ), ∀ k : GA,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (GA → ℂ))}),
        x ∈ CB.reg → (CC.P WhittakerBlock.casimir1 a₁ x = 0 ∧ CC.P WhittakerBlock.casimir2 a₂ x = 0 ∧
          CC.P WhittakerBlock.casimir3 a₃ x = 0) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        intro _
        obtain ⟨φ, ⟨hφ, -⟩, rfl⟩ := hx
        exact hgenM φ hφ
      | zero => intro _; exact ⟨CC.P_zero CA.good_casimir1 a₁, CC.P_zero CA.good_casimir2 a₂, CC.P_zero CA.good_casimir3 a₃⟩
      | add x y hx' hy' hx hy =>
        intro _
        have hxr : x ∈ CB.reg := hMreg (by rw [hM]; exact hx')
        have hyr : y ∈ CB.reg := hMreg (by rw [hM]; exact hy')
        obtain ⟨h1, h2, h3⟩ := hx hxr
        obtain ⟨k1, k2, k3⟩ := hy hyr
        exact ⟨by rw [CC.P_add CA.good_casimir1 a₁ hxr.1 hyr.1, h1, k1, add_zero],
          by rw [CC.P_add CA.good_casimir2 a₂ hxr.1 hyr.1, h2, k2, add_zero],
          by rw [CC.P_add CA.good_casimir3 a₃ hxr.1 hyr.1, h3, k3, add_zero]⟩
      | smul a x hx' hx =>
        intro _
        have hxr : x ∈ CB.reg := hMreg (by rw [hM]; exact hx')
        obtain ⟨h1, h2, h3⟩ := hx hxr
        exact ⟨by rw [CC.P_smul CA.good_casimir1 a₁ a hxr.1, h1, smul_zero],
          by rw [CC.P_smul CA.good_casimir2 a₂ a hxr.1, h2, smul_zero],
          by rw [CC.P_smul CA.good_casimir3 a₃ a hxr.1, h3, smul_zero]⟩
    exact key w hw' (hMreg hw)
  refine ⟨⟨N₁, N₂, N₃, a₁, a₂, a₃, ha₁, ha₂, ha₃, fun w hw => ?_⟩, ⟨N₁, N₂, N₃, a₁, a₂, a₃, ha₁, ha₂, ha₃, fun w hw => ?_⟩⟩
  · obtain ⟨h1, h2, h3⟩ := hallM w hw
    obtain ⟨k1, k2, k3⟩ := hWP w (hMreg hw)
    exact ⟨k1 h1, k2 h2, k3 h3⟩
  · exact hallM w hw

end CasC
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_smoothingModule_casimir_relations.R1CuspDeriv"

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped Classical in
theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (hmg : IsModerateGrowth3 ℚ f)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (hsa : WhittakerBlock.IsArchSmooth3 f)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite fun x => ∑ i, c i * f (x * t i))
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hu : u ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
          φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
            (fun g => ∑ i, c i * f (g * h * t i)) w})
    (m J : ℕ) (e : Fin m → ℂ) (he : Function.Injective e)
    (a : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => a i j p.1 p.2) {p | 0 < p.1})
    (τ : ℝ) (hτ : 1 / 2 < τ)
    (hexp : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, a i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ)
    (i₀ : Fin m) (hD : (e i₀).re = 1 / 2) :
    (∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}),
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l]
            (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w))) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l]
            (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w))) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l]
            (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w))) = 0) ∧
    (∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}),
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l] w)) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0) :=
  CC.main ω f hc hmg hsa hKf n c t ht hz u hu _ rfl

end S_LanglandsTunnell_CubicInduction_smoothingModule_casimir_relations
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_smoothingModule_casimir_relations (solution)
