-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.integral_archDeriv_smoothingOperator_mul_conj_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a5b8dac3-80b6-56ff-a263-820e541ba242

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_integral_smoothingOperator_comp_archRealLift3_mul_conj_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_hasDerivAt_integral_smoothingOperator_comp_archRealLift3_mul_conj
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_integral_archDeriv_smoothingOperator_mul_conj_eq_neg
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.CubicInduction.fnTwist3_apply"

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

private theorem _root_.R1CuspDeriv.det_cfun_ne (i j : Fin 3) {s : ℝ} (hs : |s| < 1) : (Matrix.of (cfun i j s)).det ≠ 0 := by
  rw [det_cfun]; exact (kap_pos i j hs).ne'

p2m_export "R1CuspDeriv" "det_cfun_ne"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_integral_archDeriv_smoothingOperator_mul_conj_eq_neg.R1CuspDeriv"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_integral_archDeriv_smoothingOperator_mul_conj_eq_neg.R1CuspDeriv"

section GantiGlue

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory Filter Topology
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace GANTI
private theorem _root_.GANTI.det_cfun_ne (i j : Fin 3) {s : ℝ} (hs : |s| < 1) :
    (Matrix.of (fun a c : Fin 3 => (if a = c then (1 : ℝ) else 0) + if a = i ∧ c = j then s else 0)).det ≠ 0 :=
  R1CuspDeriv.det_cfun_ne i j hs

end GANTI
p2m_export "" "GANTI.det_cfun_ne"
end GantiGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_integral_archDeriv_smoothingOperator_mul_conj_eq_neg.R1CuspDeriv"

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (hW0a :
      ∃ c C : ℝ, 0 < c ∧ ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ∃ (γ : GL (Fin 3) ℚ) (n t k : AdelicGL 3 (𝓞 ℚ) ℚ),
          globalPointsGL 3 (𝓞 ℚ) ℚ γ * g = n * t * k ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
          ∀ w : InfinitePlace ℚ,
            (∀ i j : Fin 3,
              (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
              (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
              ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
            (∀ i j : Fin 3, i ≠ j →
              (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
            (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
                (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1)
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous u)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (hmg : IsModerateGrowth3 ℚ u)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) u)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) u)
    (φ φ' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ) (hφ' : IsSmoothingKernel φ') (i j : Fin 3) :
    ∫ g, WhittakerBlock.archDeriv i j (smoothingOperator φ u) g * (starRingEnd ℂ) (smoothingOperator φ' u g)
        ∂(domainMeasure a b Φ₀) =
      - ∫ g, smoothingOperator φ u g * (starRingEnd ℂ) (WhittakerBlock.archDeriv i j (smoothingOperator φ' u) g)
        ∂(domainMeasure a b Φ₀) := by
  have hD := LanglandsTunnell.CubicInduction.SlabL2.hasDerivAt_integral_smoothingOperator_comp_archRealLift3_mul_conj
    ω hω a b Φ₀ hΦ₀ hW0a u hc haut hcen hmg hP21 hP12 φ φ' hφ hφ' i j
  have hconst : HasDerivAt
      (fun s : ℝ => ∫ g, smoothingOperator φ u
          (g * WhittakerBlock.archRealLift3 (fun a c => (if a = c then (1 : ℝ) else 0) + if a = i ∧ c = j then s else 0)) *
        (starRingEnd ℂ) (smoothingOperator φ' u
          (g * WhittakerBlock.archRealLift3 (fun a c => (if a = c then (1 : ℝ) else 0) + if a = i ∧ c = j then s else 0)))
        ∂(domainMeasure a b Φ₀)) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) (∫ g, smoothingOperator φ u g * (starRingEnd ℂ) (smoothingOperator φ' u g)
      ∂(domainMeasure a b Φ₀))).congr_of_eventuallyEq ?_
    have hnb : Metric.ball (0 : ℝ) 1 ∈ nhds (0 : ℝ) := Metric.isOpen_ball.mem_nhds (by simp)
    filter_upwards [hnb] with s hs
    have hs' : |s| < 1 := by simpa [Real.dist_eq] using hs
    exact LanglandsTunnell.CubicInduction.SlabL2.integral_smoothingOperator_comp_archRealLift3_mul_conj_eq
      ω hω a b Φ₀ hΦ₀ hW0a u hc haut hcen hmg hP21 hP12 φ φ' hφ hφ' _ (GANTI.det_cfun_ne i j hs')
  have h0 := hD.unique hconst
  exact eq_neg_of_add_eq_zero_left h0

end S_LanglandsTunnell_CubicInduction_SlabL2_integral_archDeriv_smoothingOperator_mul_conj_eq_neg
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_integral_archDeriv_smoothingOperator_mul_conj_eq_neg (solution)
