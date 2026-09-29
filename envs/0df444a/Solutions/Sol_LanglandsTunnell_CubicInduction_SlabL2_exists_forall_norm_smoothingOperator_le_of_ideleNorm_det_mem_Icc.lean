-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.exists_forall_norm_smoothingOperator_le_of_ideleNorm_det_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/870baf64-28af-516d-ac79-ef9d31d1bb82

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Theorems.Thm_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth
import Theorems.Thm_LanglandsTunnell_CubicInduction_smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong
import Theorems.Thm_LanglandsTunnell_CubicInduction_gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_isSlabDomain
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_archDeriv_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_ideleNorm_det_globalPointsGL_eq_one_and_measurableSet_ideleNormDetSlab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_forall_norm_smoothingOperator_le_of_ideleNorm_det_mem_Icc
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.CubicInduction.fnTwist3_apply LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace SmoothBdd

scoped instance : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
scoped instance : T2Space (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (T2Space (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
scoped instance : LocallyCompactSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := inferInstance

section Local

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem fin_localToAdelic3 (x : LocalGL3 p) :
    (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (localToAdelic3 p x : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      localMatN (Fin 3) (𝓞 ℚ) ℚ p (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) := by
  change (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ
    (localMatN (Fin 3) (𝓞 ℚ) ℚ p (x : Matrix (Fin 3) (Fin 3) _))) = _
  rw [mapMatrix_fin_finMatN]

theorem arch_localToAdelic3 (x : LocalGL3 p) :
    (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (localToAdelic3 p x : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      1 := by
  change (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ
    (localMatN (Fin 3) (𝓞 ℚ) ℚ p (x : Matrix (Fin 3) (Fin 3) _))) = _
  rw [mapMatrix_arch_finMatN]

theorem componentAt3_coe {q : HeightOneSpectrum (𝓞 ℚ)} (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (componentAt3 (𝓞 ℚ) ℚ q g : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) =
      (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ q).mapMatrix
        ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) :=
  rfl

theorem componentAt3_localToAdelic3_self (x : LocalGL3 p) :
    componentAt3 (𝓞 ℚ) ℚ p (localToAdelic3 p x) = x := by
  apply Units.ext
  rw [componentAt3_coe, fin_localToAdelic3, mapMatrix_localMatN_self]

theorem componentAt3_localToAdelic3_of_ne {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (x : LocalGL3 p) :
    componentAt3 (𝓞 ℚ) ℚ q (localToAdelic3 p x) = 1 := by
  apply Units.ext
  rw [componentAt3_coe, fin_localToAdelic3, mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ p _ hq, Units.val_one]

theorem archEntries_localToAdelic3 (x : LocalGL3 p) :
    Matrix.of (archEntries (localToAdelic3 p x)) = 1 := by
  ext a b
  have h := congrFun (congrFun (arch_localToAdelic3 p x) a) b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h
  show realCoordinate ((localToAdelic3 p x : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) a b).1 = (1 : Matrix (Fin 3) (Fin 3) ℝ) a b
  have h' : ((localToAdelic3 p x : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) a b).1 = (1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b := h
  rw [h', Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Local

def archHom : AdeleRing (𝓞 ℚ) ℚ →+* ℝ :=
  realCoordinate.comp (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ →+* InfiniteAdeleRing ℚ)

theorem archEntries_eq (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    archEntries g i j = archHom ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) := rfl

theorem archEntries_mul (x y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Matrix.of (archEntries (x * y)) = Matrix.of (archEntries x) * Matrix.of (archEntries y) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, archEntries_eq, Units.val_mul, map_sum, map_mul]

theorem smoothingOperator_mul_right (φ u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (k x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    smoothingOperator φ u (x * k) = smoothingOperator (fun g => φ (k⁻¹ * g)) u x := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  rw [smoothingOperator_apply, smoothingOperator_apply]
  rw [← integral_mul_left_eq_self (fun g => φ (k⁻¹ * g) * u (x * g)) k]
  simp only [inv_mul_cancel_left, mul_assoc]

theorem kernel_level {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    {α : (Fin 3 → Fin 3 → ℝ) → ℂ} {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hφ : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      φ g = α (archEntries g) *
        Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g)
    (p : HeightOneSpectrum (𝓞 ℚ)) (k : LocalGL3 p) (hk : k ∈ K' p) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    φ ((localToAdelic3 p k)⁻¹ * g) = φ g := by
  classical
  rw [hφ, hφ g]
  have h1 : archEntries ((localToAdelic3 p k)⁻¹ * g) = archEntries g := by
    have := archEntries_mul (localToAdelic3 p k)⁻¹ g
    rw [← map_inv, archEntries_localToAdelic3, Matrix.one_mul] at this
    exact Matrix.of.injective this
  have h2 : ((localToAdelic3 p k)⁻¹ * g ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ q, componentAt3 (𝓞 ℚ) ℚ q x ∈ K' q}) ↔
      (g ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ q, componentAt3 (𝓞 ℚ) ℚ q x ∈ K' q}) := by
    simp only [Set.mem_setOf_eq, map_mul, map_inv]
    refine forall_congr' fun q => ?_
    by_cases hq : q = p
    · subst hq
      rw [componentAt3_localToAdelic3_self]
      constructor
      · intro h
        have := (K' q).mul_mem hk h
        rwa [mul_inv_cancel_left] at this
      · intro h
        exact (K' q).mul_mem ((K' q).inv_mem hk) h
    · rw [componentAt3_localToAdelic3_of_ne p hq, inv_one, one_mul]
  rw [h1]
  congr 1
  by_cases hg : g ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ q, componentAt3 (𝓞 ℚ) ℚ q x ∈ K' q}
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (h2.mpr hg)]
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt h2.mp hg)]

theorem smoothingOperator_level {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    {α : (Fin 3 → Fin 3 → ℝ) → ℂ} {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hφ : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      φ g = α (archEntries g) *
        Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g)
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (p : HeightOneSpectrum (𝓞 ℚ)) (k : LocalGL3 p) (hk : k ∈ K' p)
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    smoothingOperator φ u (x * localToAdelic3 p k) = smoothingOperator φ u x := by
  rw [smoothingOperator_mul_right]
  congr 1
  funext g
  exact kernel_level hφ p k hk g

theorem foldr_archDeriv_smoothingOperator (φ u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ)
    (hu : LocallyIntegrable u (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (w : List (Fin 3 × Fin 3)) :
    ∃ ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel ψ ∧
      List.foldr (fun ij f => WhittakerBlock.archDeriv ij.1 ij.2 f) (smoothingOperator φ u) w =
        smoothingOperator ψ u := by
  induction w with
  | nil => exact ⟨φ, hφ, rfl⟩
  | cons ij w ih =>
    obtain ⟨ψ, hψ, hw⟩ := ih
    obtain ⟨hψ', hD⟩ := archDeriv_smoothingOperator ψ u hψ hu ij.1 ij.2
    refine ⟨_, hψ', ?_⟩
    rw [List.foldr_cons, hw, hD]

end SmoothBdd
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_forall_norm_smoothingOperator_le_of_ideleNorm_det_mem_Icc.SmoothBdd"

open SmoothBdd in
theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
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
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ)
    (a' b' : ℝ) (ha' : 0 < a') (hab' : a' < b') :
    ∃ B : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a' b' →
        ‖smoothingOperator φ u g‖ ≤ B := by
  classical
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  set F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := smoothingOperator φ u with hF
  have hu : LocallyIntegrable u (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := hc.locallyIntegrable
  obtain ⟨hcF, hsaF⟩ := continuous_and_isArchSmooth3_smoothingOperator φ u hφ hu

  obtain ⟨Φ₁, hΦ₁⟩ := exists_isSlabDomain 1 2 one_pos one_lt_two
  have hmem := smoothingOperator_mem_cuspFunctions_of_isCuspidalAlong ω 1 2 Φ₁ hΦ₁ hW0a u hc haut hcen hmg hP21 hP12 φ hφ
  obtain ⟨hautm, _, hP21F, hP12F⟩ := (mem_cuspFunctions_iff ω 1 2 Φ₁ _).1 hmem
  obtain ⟨hautF, hcenF, _⟩ := (mem_automorphicSubmodule_iff ω 1 2 Φ₁ _).1 hautm

  obtain ⟨α, K', hα, hK'oc, hcof, hφeq⟩ := hφ
  have hfin : Set.Finite {p : HeightOneSpectrum (𝓞 ℚ) | ¬ (K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p)} :=
    Filter.eventually_cofinite.1 hcof
  set S : Finset (HeightOneSpectrum (𝓞 ℚ)) := hfin.toFinset with hS
  have hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F := by
    intro p hp g k hk
    have hp' : K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p := by
      by_contra h
      exact hp (hfin.mem_toFinset.2 h)
    obtain ⟨k0, hk0, rfl⟩ := Subgroup.mem_map.1 hk
    exact smoothingOperator_level hφeq u p k0 (hp' ▸ hk0) g
  have hsm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, F (g * localToAdelic3 v k) = F g :=
    fun v => ⟨K' v, (hK'oc v).1, fun k hk g => smoothingOperator_level hφeq u v k hk g⟩

  have hφ0 : IsSmoothingKernel φ := ⟨α, K', hα, hK'oc, hcof, hφeq⟩
  have hcw : ∀ w : List (Fin 3 × Fin 3),
      Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) F w) := by
    intro w
    obtain ⟨ψ, hψ, hw⟩ := foldr_archDeriv_smoothingOperator φ u hφ0 hu w
    rw [hw]
    exact (continuous_and_isArchSmooth3_smoothingOperator ψ u hψ hu).1
  obtain ⟨C₀, N, hN⟩ := hmg
  have hgr : ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) F w g‖ ≤ C * gauge3 ℚ g ^ N := by
    intro w
    obtain ⟨ψ, hψ, hw⟩ := foldr_archDeriv_smoothingOperator φ u hφ0 hu w
    rw [hw]
    exact gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow.2 N u ψ
      ⟨C₀, fun g => hN g (Set.mem_univ g)⟩ hψ

  obtain ⟨c, C, hc0, hcov⟩ := hW0a
  obtain ⟨C', hC'⟩ := norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth F hcF hautF hP21F hP12F
    S hK hsm hsaF hcw N hgr c C a' b' hc0 ha' hab' 0
  obtain ⟨hdet1, _⟩ := ideleNorm_det_globalPointsGL_eq_one_and_measurableSet_ideleNormDetSlab
  refine ⟨C', fun g hg => ?_⟩
  obtain ⟨γ, n, t, k, hγ, hn, ht, hk, harch⟩ := hcov g
  have hslab : NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (n * t * k)) ∈ Set.Icc a' b' := by
    rw [← hγ, map_mul, NumberField.TateGlobal.ideleNorm_mul, hdet1, one_mul]
    exact hg
  have h := hC' n t k hn ht hk harch hslab
  rw [pow_zero, mul_one, ← hγ] at h
  have h' : ‖smoothingOperator φ u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g)‖ ≤ C' := h
  rw [hautF] at h'
  exact h'

end
end S_LanglandsTunnell_CubicInduction_SlabL2_exists_forall_norm_smoothingOperator_le_of_ideleNorm_det_mem_Icc
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_forall_norm_smoothingOperator_le_of_ideleNorm_det_mem_Icc (solution)
