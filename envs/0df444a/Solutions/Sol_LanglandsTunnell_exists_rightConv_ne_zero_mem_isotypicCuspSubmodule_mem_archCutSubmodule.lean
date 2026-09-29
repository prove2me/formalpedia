-- Prove2me | solution 1 for LanglandsTunnell.exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/aaf14fad-b03b-5079-a70d-c1621959f560

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant
import Theorems.Thm_AutomorphicForm_isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume

noncomputable section

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

private theorem lintegral_enorm_sq_lt_top_of_memLp (D : Set (AdelicGL2 (𝓞 F) F)) (ψ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
      MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D)) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    ∫⁻ g in D, ‖ψ g‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  have h2 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (f := ψ)
    (μ := (adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) two_ne_zero ENNReal.ofNat_ne_top).mp h.2
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using h2

private theorem memLp_of_lintegral_enorm_sq_lt_top (D : Set (AdelicGL2 (𝓞 F) F)) (ψ : AdelicGL2 (𝓞 F) F → ℂ)
    (hψ : Continuous ψ)
    (h : letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
      ∫⁻ g in D, ‖ψ g‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  refine ⟨hψ.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using h

private theorem measure_window_inter_support_pos [Countable F] (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ) (hZ : ∀ z, z ∈ Z)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ) (hcont : Continuous φ)
    (hne : ∃ g, φ g ≠ 0) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    0 < adelicGLHaar (Fin 2) (𝓞 F) F
      ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∩ {g | φ g ≠ 0}) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  have hUopen : IsOpen {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} := isOpen_ne_fun hcont continuous_const
  have hUne : ({g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} : Set (AdelicGL2 (𝓞 F) F)).Nonempty := by
    obtain ⟨g, hg⟩ := hne
    exact ⟨g, hg⟩
  have hUγ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      globalPoints (𝓞 F) F γ * g ∈ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} ↔ g ∈ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} := by
    intro γ g
    simp only [Set.mem_setOf_eq, hφ.left_invariant γ g]
  have hUz : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      centralScalar (𝓞 F) F z * g ∈ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} ↔
        g ∈ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} := by
    intro z g
    have hz : φ (centralScalar (𝓞 F) F z * g) = ((ξ ⟨z, hZ z⟩ : ℂˣ) : ℂ) * φ g :=
      hφ.central_transform ⟨z, hZ z⟩ g
    simp only [Set.mem_setOf_eq, hz, mul_ne_zero_iff]
    exact and_iff_right (Units.ne_zero _)
  rw [pos_iff_ne_zero]
  intro hWU
  have hpiece : ∀ k : ℕ, adelicGLHaar (Fin 2) (𝓞 F) F ({g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} ∩
      {g : AdelicGL2 (𝓞 F) F | TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc (((k : ℝ) + 1)⁻¹) ((k : ℝ) + 1)}) = 0 := by
    intro k
    obtain ⟨N, hN⟩ := AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre F c u d₁ d₂ T
      hd hcov (((k : ℝ) + 1)⁻¹) ((k : ℝ) + 1) (by positivity)
    refine measure_mono_null (t := ⋃ γ : Matrix.GeneralLinearGroup (Fin 2) F, ⋃ n ∈ N,
      (fun h => globalPoints (𝓞 F) F γ * h) ⁻¹' ((fun h => centralScalar (𝓞 F) F n * h) ''
        ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∩ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0}))) ?_ ?_
    · rintro g ⟨hgU, hgslab⟩
      obtain ⟨γ, n, hn, x, hx, s, hs, hsx⟩ := hN g hgslab
      have hsx' : s * (centralScalar (𝓞 F) F n * x) = globalPoints (𝓞 F) F γ * g := hsx
      have hkey : globalPoints (𝓞 F) F γ * g = centralScalar (𝓞 F) F n * (s * x) := by
        rw [← hsx', ← mul_assoc, mul_centralScalar_comm, mul_assoc]
      refine Set.mem_iUnion.mpr ⟨γ, Set.mem_iUnion₂.mpr ⟨n, hn, ?_⟩⟩
      show globalPoints (𝓞 F) F γ * g ∈ (fun h => centralScalar (𝓞 F) F n * h) ''
        ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∩ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0})
      refine ⟨s * x, ⟨Set.mem_iUnion₂.mpr ⟨x, hx, ⟨s, hs, rfl⟩⟩, ?_⟩, hkey.symm⟩
      have h1 : globalPoints (𝓞 F) F γ * g ∈ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} := (hUγ γ g).mpr hgU
      rw [hkey] at h1
      exact (hUz n (s * x)).mp h1
    · refine measure_iUnion_null_iff.mpr fun γ => (measure_biUnion_null_iff N.countable_toSet).mpr fun n _ => ?_
      rw [measure_preimage_mul, Set.image_mul_left, measure_preimage_mul]
      exact hWU
  have hcover : {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} ⊆ ⋃ k : ℕ, ({g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} ∩
      {g : AdelicGL2 (𝓞 F) F | TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc (((k : ℝ) + 1)⁻¹) ((k : ℝ) + 1)}) := by
    intro g hg
    have hpos : 0 < TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) := TateGlobal.ideleNorm_pos _
    obtain ⟨k, hk⟩ := exists_nat_ge (max (TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹
      (TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g)))
    have hk1 : (TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ≤ (k : ℝ) + 1 :=
      (le_max_left _ _).trans (hk.trans (by linarith))
    have hk2 : TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ≤ (k : ℝ) + 1 :=
      (le_max_right _ _).trans (hk.trans (by linarith))
    exact Set.mem_iUnion.mpr ⟨k, hg, ⟨inv_le_of_inv_le₀ hpos hk1, hk2⟩⟩
  have hU0 : adelicGLHaar (Fin 2) (𝓞 F) F {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} = 0 := by
    refine le_antisymm ((measure_mono hcover).trans ((measure_iUnion_le _).trans ?_)) zero_le
    simp only [hpiece, tsum_zero, le_refl]
  exact (hUopen.measure_pos (adelicGLHaar (Fin 2) (𝓞 F) F) hUne).ne' hU0

omit [NumberField F] in
private theorem two_ne_zero_completion (w₀ : InfinitePlace F) : (2 : w₀.Completion) ≠ 0 := by
  intro h
  have h2 := norm_two_completion w₀
  rw [h, norm_zero] at h2
  norm_num at h2

private def smwScaleUnit (w₀ : InfinitePlace F) : (w₀.Completion)ˣ :=
  Units.mk0 (2 : w₀.Completion) (two_ne_zero_completion F w₀)

private def smwZ (w₀ : InfinitePlace F) (n : ℕ) : AdelicGL2 (𝓞 F) F :=
  centralScalar (𝓞 F) F (archCentralUnit F w₀ (smwScaleUnit F w₀ ^ n))

omit [NumberField F] in
private theorem norm_smwScaleUnit_pow (w₀ : InfinitePlace F) (n : ℕ) :
    ‖((smwScaleUnit F w₀ ^ n : (w₀.Completion)ˣ) : w₀.Completion)‖ = 2 ^ n := by
  rw [Units.val_pow_eq_pow_val, norm_pow]
  simp only [smwScaleUnit, Units.val_mk0, norm_two_completion]

private theorem archDetNorm_smwZ_mul (w₀ : InfinitePlace F) (n : ℕ) (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm w₀ (smwZ F w₀ n * g) = 4 ^ n * archDetNorm w₀ g := by
  unfold smwZ
  rw [archDetNorm_centralScalar_mul, norm_smwScaleUnit_pow, ← mul_pow]
  norm_num

private theorem glFin_smwZ_mul (w₀ : InfinitePlace F) (n : ℕ) (g : AdelicGL2 (𝓞 F) F) :
    glFin (𝓞 F) F (smwZ F w₀ n * g) = glFin (𝓞 F) F g := by
  unfold smwZ
  rw [map_mul, glFin_centralScalar_archCentralUnit, one_mul]

private theorem coords_smwZ_mul (w₀ : InfinitePlace F) (n : ℕ) (g : AdelicGL2 (𝓞 F) F) :
    localHeight (archComponent F w₀ (glArch (𝓞 F) F (smwZ F w₀ n * g)))
        = localHeight (archComponent F w₀ (glArch (𝓞 F) F g)) ∧
      xWindowSq (archComponent F w₀ (glArch (𝓞 F) F (smwZ F w₀ n * g)))
        = xWindowSq (archComponent F w₀ (glArch (𝓞 F) F g)) := by
  unfold smwZ
  rw [map_mul, map_mul]
  have e := archComponent_centralScalar_archCentralUnit_apply (F := F) w₀ (smwScaleUnit F w₀ ^ n)
  have hne : ((smwScaleUnit F w₀ ^ n : (w₀.Completion)ˣ) : w₀.Completion) ≠ 0 := Units.ne_zero _
  exact ⟨localHeight_scalar_entries_mul hne (by rw [e]; rfl) (by rw [e]; rfl) (by rw [e]; rfl) (by rw [e]; rfl) _,
    xWindowSq_scalar_entries_mul hne (by rw [e]; rfl) (by rw [e]; rfl) (by rw [e]; rfl) (by rw [e]; rfl) _⟩

private theorem smwZ_mul_mem_iff (w₀ : InfinitePlace F) (hw₀ : ∀ w : InfinitePlace F, w = w₀) (n : ℕ)
    (c u a b : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    smwZ F w₀ n * g ∈ centreCutSiegelSet F c u a b ↔ g ∈ centreCutSiegelSet F c u (a / 4 ^ n) (b / 4 ^ n) := by
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  rw [mem_centreCutSiegelSet_iff, mem_centreCutSiegelSet_iff, glFin_smwZ_mul]
  constructor
  · rintro ⟨h1, h2, h3, h5⟩
    refine ⟨h1, fun w => ?_, fun w => ?_, fun w => ?_⟩
    · rw [hw₀ w]
      have := h2 w₀
      rwa [(coords_smwZ_mul F w₀ n g).1] at this
    · rw [hw₀ w]
      have := h3 w₀
      rwa [(coords_smwZ_mul F w₀ n g).2] at this
    · rw [hw₀ w]
      have := h5 w₀
      rw [archDetNorm_smwZ_mul] at this
      exact ⟨(div_le_iff₀ h4).mpr (by linarith [this.1]), (le_div_iff₀ h4).mpr (by linarith [this.2])⟩
  · rintro ⟨h1, h2, h3, h5⟩
    refine ⟨h1, fun w => ?_, fun w => ?_, fun w => ?_⟩
    · rw [hw₀ w, (coords_smwZ_mul F w₀ n g).1]
      exact h2 w₀
    · rw [hw₀ w, (coords_smwZ_mul F w₀ n g).2]
      exact h3 w₀
    · rw [hw₀ w, archDetNorm_smwZ_mul]
      have := h5 w₀
      have ha := (div_le_iff₀ h4).mp this.1
      have hb := (le_div_iff₀ h4).mp this.2
      exact ⟨by linarith, by linarith⟩

private theorem mem_centreCutSiegelSet_of_det_window_le {c u a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ centreCutSiegelSet F c u a' b') : g ∈ centreCutSiegelSet F c u a b := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_centreCutSiegelSet_iff.mp hg
  exact mem_centreCutSiegelSet_iff.mpr ⟨h1, h2, h3, fun w => ⟨ha.trans (h4 w).1, (h4 w).2.trans hb⟩⟩

private theorem archDetNorm_mul_right (w₀ : InfinitePlace F) (s x : AdelicGL2 (𝓞 F) F) :
    archDetNorm w₀ (s * x) = archDetNorm w₀ s * archDetNorm w₀ x := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]

private def smwBase (w₀ : InfinitePlace F) (c u d₁ d₂ : ℝ) (x : AdelicGL2 (𝓞 F) F) : Set (AdelicGL2 (𝓞 F) F) :=
  (· * x) '' (centreCutSiegelSet F c u d₁ d₂ ∩ archDetNorm w₀ ⁻¹' Set.Ioi (d₂ / 4))

private def smwShell (w₀ : InfinitePlace F) (c u d₁ d₂ : ℝ) (x : AdelicGL2 (𝓞 F) F) (n : ℕ) :
    Set (AdelicGL2 (𝓞 F) F) :=
  (fun h => smwZ F w₀ n * h) ⁻¹' smwBase F w₀ c u d₁ d₂ x

private theorem measurableSet_smwBase (w₀ : InfinitePlace F) (c u d₁ d₂ : ℝ) (x : AdelicGL2 (𝓞 F) F) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MeasurableSet (smwBase F w₀ c u d₁ d₂ x) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  unfold smwBase
  rw [Set.image_mul_right]
  refine MeasurableSet.preimage ?_ (measurable_mul_const _)
  exact (measurableSet_centreCutSiegelSet c u d₁ d₂).inter
    (measurableSet_Ioi.preimage (continuous_archDetNorm (F := F) w₀).measurable)

private theorem measurableSet_smwShell (w₀ : InfinitePlace F) (c u d₁ d₂ : ℝ) (x : AdelicGL2 (𝓞 F) F) (n : ℕ) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MeasurableSet (smwShell F w₀ c u d₁ d₂ x n) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  have hb : MeasurableSet (smwBase F w₀ c u d₁ d₂ x) := measurableSet_smwBase F w₀ c u d₁ d₂ x
  exact hb.preimage (measurable_const_mul _)

private theorem det_bounds_of_mem_smwBase (w₀ : InfinitePlace F) {c u d₁ d₂ : ℝ} {x h : AdelicGL2 (𝓞 F) F}
    (hh : h ∈ smwBase F w₀ c u d₁ d₂ x) :
    d₂ / 4 * archDetNorm w₀ x < archDetNorm w₀ h ∧ archDetNorm w₀ h ≤ d₂ * archDetNorm w₀ x := by
  obtain ⟨s, ⟨hs, hlt⟩, rfl⟩ := hh
  have hlt' : d₂ / 4 < archDetNorm w₀ s := hlt
  have hx := archDetNorm_pos w₀ x
  have hsd := (mem_centreCutSiegelSet_iff.mp hs).2.2.2 w₀
  show d₂ / 4 * archDetNorm w₀ x < archDetNorm w₀ (s * x) ∧ archDetNorm w₀ (s * x) ≤ d₂ * archDetNorm w₀ x
  rw [archDetNorm_mul_right]
  exact ⟨mul_lt_mul_of_pos_right hlt' hx, mul_le_mul_of_nonneg_right hsd.2 hx.le⟩

private theorem smwShell_subset (w₀ : InfinitePlace F) (hw₀ : ∀ w : InfinitePlace F, w = w₀) (n : ℕ)
    {c u d₁ d₂ : ℝ} (hd₁ : d₁ ≤ 0) (hd₂ : 0 ≤ d₂) (x : AdelicGL2 (𝓞 F) F) :
    smwShell F w₀ c u d₁ d₂ x n ⊆ (· * x) '' centreCutSiegelSet F c u d₁ d₂ := by
  rintro h ⟨s, ⟨hs, -⟩, hsx⟩
  have hsx' : s * x = smwZ F w₀ n * h := hsx
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have h41 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  refine ⟨(smwZ F w₀ n)⁻¹ * s, ?_, ?_⟩
  · have h1 : smwZ F w₀ n * ((smwZ F w₀ n)⁻¹ * s) ∈ centreCutSiegelSet F c u d₁ d₂ := by
      rwa [mul_inv_cancel_left]
    have h2 := (smwZ_mul_mem_iff F w₀ hw₀ n c u d₁ d₂ _).mp h1
    refine mem_centreCutSiegelSet_of_det_window_le F ?_ (div_le_self hd₂ h41) h2
    rw [le_div_iff₀ h4]
    nlinarith
  · show (smwZ F w₀ n)⁻¹ * s * x = h
    rw [mul_assoc, hsx', inv_mul_cancel_left]

private theorem smwShell_pairwise_disjoint (w₀ : InfinitePlace F) (c u d₁ d₂ : ℝ) (x : AdelicGL2 (𝓞 F) F) :
    Pairwise (Function.onFun Disjoint (smwShell F w₀ c u d₁ d₂ x)) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  intro h hm hn
  have hD := archDetNorm_pos w₀ h
  obtain ⟨hm1, hm2⟩ := det_bounds_of_mem_smwBase F w₀ hm
  obtain ⟨hn1, hn2⟩ := det_bounds_of_mem_smwBase F w₀ hn
  rw [archDetNorm_smwZ_mul] at hm1 hm2 hn1 hn2
  have hE : d₂ * archDetNorm w₀ x = 4 * (d₂ / 4 * archDetNorm w₀ x) := by ring
  have key : ∀ a b : ℕ, (4 : ℝ) ^ a * archDetNorm w₀ h ≤ d₂ * archDetNorm w₀ x →
      d₂ / 4 * archDetNorm w₀ x < (4 : ℝ) ^ b * archDetNorm w₀ h → a ≤ b := by
    intro a b ha hb
    have h1 : (4 : ℝ) ^ a * archDetNorm w₀ h < 4 ^ (b + 1) * archDetNorm w₀ h := by
      rw [pow_succ]
      nlinarith
    have h2 : (4 : ℝ) ^ a < 4 ^ (b + 1) := lt_of_mul_lt_mul_right h1 hD.le
    have h3 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).mp h2
    omega
  exact hmn (le_antisymm (key m n hm2 hn1) (key n m hn2 hm1))

private theorem exists_shell_index {d₂ t : ℝ} (ht : 0 < t) (htd : t ≤ d₂) :
    ∃ n : ℕ, d₂ / 4 < 4 ^ n * t ∧ 4 ^ n * t ≤ d₂ := by
  have hex : ∃ m : ℕ, d₂ < 4 ^ (m + 1) * t := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (d₂ / t) (by norm_num : (1 : ℝ) < 4)
    refine ⟨m, ?_⟩
    have h1 : d₂ < 4 ^ m * t := (div_lt_iff₀ ht).mp hm
    have h2 : (4 : ℝ) ^ m * t ≤ 4 ^ (m + 1) * t :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ m)) ht.le
    exact h1.trans_le h2
  classical
  refine ⟨Nat.find hex, ?_, ?_⟩
  · have h := Nat.find_spec hex
    rw [pow_succ] at h
    linarith
  · rcases hn : Nat.find hex with _ | k
    · simpa using htd
    · have hk : k < Nat.find hex := by omega
      exact not_lt.mp (Nat.find_min hex hk)

private theorem subset_iUnion_smwShell (w₀ : InfinitePlace F) (hw₀ : ∀ w : InfinitePlace F, w = w₀)
    (c u d₁ d₂ : ℝ) (hd₁ : d₁ ≤ 0) (hd₂ : 0 < d₂) (x : AdelicGL2 (𝓞 F) F) :
    (· * x) '' centreCutSiegelSet F c u d₁ d₂ ⊆ ⋃ n : ℕ, smwShell F w₀ c u d₁ d₂ x n := by
  rintro _ ⟨s, hs, rfl⟩
  have hsd := (mem_centreCutSiegelSet_iff.mp hs).2.2.2 w₀
  obtain ⟨n, hn1, hn2⟩ := exists_shell_index (archDetNorm_pos w₀ s) hsd.2
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  show smwZ F w₀ n * (s * x) ∈ smwBase F w₀ c u d₁ d₂ x
  refine ⟨smwZ F w₀ n * s, ⟨?_, ?_⟩, ?_⟩
  · rw [smwZ_mul_mem_iff F w₀ hw₀]
    obtain ⟨h1, h2, h3, -⟩ := mem_centreCutSiegelSet_iff.mp hs
    refine mem_centreCutSiegelSet_iff.mpr ⟨h1, h2, h3, fun w => ?_⟩
    rw [hw₀ w]
    have hpos := archDetNorm_pos w₀ s
    constructor
    · rw [div_le_iff₀ h4]
      nlinarith
    · rw [le_div_iff₀ h4]
      linarith
  · show d₂ / 4 < archDetNorm w₀ (smwZ F w₀ n * s)
    rw [archDetNorm_smwZ_mul]
    exact hn1
  · show smwZ F w₀ n * s * x = smwZ F w₀ n * (s * x)
    exact mul_assoc _ _ _

private def smwFactor (w₀ : InfinitePlace F) (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (hZ : ∀ z, z ∈ Z) (n : ℕ) : ℝ≥0∞ :=
  ‖((ξ ⟨archCentralUnit F w₀ (smwScaleUnit F w₀ ^ n), hZ _⟩ : ℂˣ) : ℂ)‖ₑ ^ 2

private theorem smwFactor_ne_zero (w₀ : InfinitePlace F) (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (hZ : ∀ z, z ∈ Z) (n : ℕ) : smwFactor F w₀ Z ξ hZ n ≠ 0 := by
  unfold smwFactor
  intro h0
  exact (ξ ⟨archCentralUnit F w₀ (smwScaleUnit F w₀ ^ n), hZ _⟩).ne_zero
    (enorm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0))

private theorem smwFactor_ne_top (w₀ : InfinitePlace F) (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (hZ : ∀ z, z ∈ Z) (n : ℕ) : smwFactor F w₀ Z ξ hZ n ≠ ⊤ := by
  unfold smwFactor
  exact ENNReal.pow_ne_top enorm_ne_top

private theorem lintegral_smwShell_eq (w₀ : InfinitePlace F) (c u d₁ d₂ : ℝ) (x : AdelicGL2 (𝓞 F) F) (n : ℕ)
    (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ) (hZ : ∀ z, z ∈ Z)
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : IsLsXiFunction (𝓞 F) F Z ξ ψ) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    ∫⁻ h in smwShell F w₀ c u d₁ d₂ x n, ‖ψ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = (smwFactor F w₀ Z ξ hZ n)⁻¹ *
          ∫⁻ h in smwBase F w₀ c u d₁ d₂ x, ‖ψ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hκ0 := smwFactor_ne_zero F w₀ Z ξ hZ n
  have hκtop := smwFactor_ne_top F w₀ Z ξ hZ n
  have hlaw : ∀ h : AdelicGL2 (𝓞 F) F, ψ (smwZ F w₀ n * h)
      = ((ξ ⟨archCentralUnit F w₀ (smwScaleUnit F w₀ ^ n), hZ _⟩ : ℂˣ) : ℂ) * ψ h :=
    fun h => hψ.central_transform ⟨archCentralUnit F w₀ (smwScaleUnit F w₀ ^ n), hZ _⟩ h
  have hG : ∀ h : AdelicGL2 (𝓞 F) F, ‖ψ (smwZ F w₀ n * h)‖ₑ ^ 2 = smwFactor F w₀ Z ξ hZ n * ‖ψ h‖ₑ ^ 2 := by
    intro h
    unfold smwFactor
    rw [hlaw h, enorm_mul, mul_pow]
  have hbase : MeasurableSet (smwBase F w₀ c u d₁ d₂ x) := measurableSet_smwBase F w₀ c u d₁ d₂ x
  have hshell : MeasurableSet (smwShell F w₀ c u d₁ d₂ x n) := measurableSet_smwShell F w₀ c u d₁ d₂ x n
  have hind : ∀ h : AdelicGL2 (𝓞 F) F,
      (smwShell F w₀ c u d₁ d₂ x n).indicator (fun h => ‖ψ h‖ₑ ^ 2) h
        = (smwFactor F w₀ Z ξ hZ n)⁻¹ *
            (smwBase F w₀ c u d₁ d₂ x).indicator (fun h => ‖ψ h‖ₑ ^ 2) (smwZ F w₀ n * h) := by
    intro h
    by_cases hmem : h ∈ smwShell F w₀ c u d₁ d₂ x n
    · have hmem' : smwZ F w₀ n * h ∈ smwBase F w₀ c u d₁ d₂ x := hmem
      simp only [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem']
      rw [hG h, ← mul_assoc, ENNReal.inv_mul_cancel hκ0 hκtop, one_mul]
    · have hmem' : smwZ F w₀ n * h ∉ smwBase F w₀ c u d₁ d₂ x := hmem
      simp only [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem', mul_zero]
  calc ∫⁻ h in smwShell F w₀ c u d₁ d₂ x n, ‖ψ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ∫⁻ h, (smwShell F w₀ c u d₁ d₂ x n).indicator (fun h => ‖ψ h‖ₑ ^ 2) h
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := (lintegral_indicator hshell _).symm
    _ = ∫⁻ h, (smwFactor F w₀ Z ξ hZ n)⁻¹ *
          (smwBase F w₀ c u d₁ d₂ x).indicator (fun h => ‖ψ h‖ₑ ^ 2) (smwZ F w₀ n * h)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := lintegral_congr hind
    _ = (smwFactor F w₀ Z ξ hZ n)⁻¹ * ∫⁻ h,
          (smwBase F w₀ c u d₁ d₂ x).indicator (fun h => ‖ψ h‖ₑ ^ 2) (smwZ F w₀ n * h)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hκ0)
    _ = (smwFactor F w₀ Z ξ hZ n)⁻¹ * ∫⁻ h, (smwBase F w₀ c u d₁ d₂ x).indicator (fun h => ‖ψ h‖ₑ ^ 2) h
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        rw [lintegral_mul_left_eq_self ((smwBase F w₀ c u d₁ d₂ x).indicator (fun h => ‖ψ h‖ₑ ^ 2)) (smwZ F w₀ n)]
    _ = (smwFactor F w₀ Z ξ hZ n)⁻¹ *
          ∫⁻ h in smwBase F w₀ c u d₁ d₂ x, ‖ψ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        rw [lintegral_indicator hbase]

private theorem smwBase_subset (w₀ : InfinitePlace F) (hw₀ : ∀ w : InfinitePlace F, w = w₀) (c u d₁ d₂ : ℝ)
    (x : AdelicGL2 (𝓞 F) F) :
    smwBase F w₀ c u d₁ d₂ x ⊆ (· * x) '' centreCutSiegelSet F c u (d₂ / 4) d₂ := by
  rintro _ ⟨s, ⟨hs, hlt⟩, rfl⟩
  refine ⟨s, ?_, rfl⟩
  have hlt' : d₂ / 4 < archDetNorm w₀ s := hlt
  obtain ⟨h1, h2, h3, h4⟩ := mem_centreCutSiegelSet_iff.mp hs
  refine mem_centreCutSiegelSet_iff.mpr ⟨h1, h2, h3, fun w => ?_⟩
  rw [hw₀ w]
  exact ⟨hlt'.le, (h4 w₀).2⟩

private theorem lintegral_smwBase_lt_top (w₀ : InfinitePlace F) (hw₀ : ∀ w : InfinitePlace F, w = w₀)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (hd₂ : 0 < d₂) (x : AdelicGL2 (𝓞 F) F)
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψc : Continuous ψ) (hψb : IsBoundedOnSiegelWindows F ψ) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    ∫⁻ h in smwBase F w₀ c u d₁ d₂ x, ‖ψ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  obtain ⟨C, hC⟩ := hψb c u (d₂ / 4) d₂ {x} hc (by positivity)
  simp only [Finset.set_biUnion_singleton] at hC
  have hfin : adelicGLHaar (Fin 2) (𝓞 F) F ((· * x) '' centreCutSiegelSet F c u (d₂ / 4) d₂) < ⊤ :=
    adelicGLHaar_mul_right_centreCutSiegelSet_lt_top F hc u (by positivity) d₂ x
  have hmem : MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict ((· * x) '' centreCutSiegelSet F c u (d₂ / 4) d₂)) :=
    memLp_two_restrict_of_bound F _ hfin ψ hψc C hC
  have hint : ∫⁻ h in (· * x) '' centreCutSiegelSet F c u (d₂ / 4) d₂, ‖ψ h‖ₑ ^ 2
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := lintegral_enorm_sq_lt_top_of_memLp F _ ψ hmem
  exact lt_of_le_of_lt (lintegral_mono_set (smwBase_subset F w₀ hw₀ c u d₁ d₂ x)) hint

private theorem memLp_rightConv_of_nonpos [Countable F] (w₀ : InfinitePlace F)
    (hw₀ : ∀ w : InfinitePlace F, w = w₀) (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hc : 0 < c) (hd₁ : d₁ ≤ 0)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsSmoothCuspAutomorphicFnAt F
      ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))) ξ φ)
    (hφc : Continuous φ) (hne : ∃ g, φ g ≠ 0) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MemLp (rightConv F φ f) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hd₂ : 0 < d₂ := by
    by_contra hd₂'
    have hempty : centreCutSiegelSet F c u d₁ d₂ = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun g hg => ?_
      have h4 := (mem_centreCutSiegelSet_iff.mp hg).2.2.2 w₀
      exact not_le.mpr (archDetNorm_pos w₀ g) (h4.2.trans (not_lt.mp hd₂'))
    rw [hempty] at hcov
    simp only [Set.image_empty, Set.iUnion_empty] at hcov
    exact not_coversModCentre_empty hcov
  have hZ : ∀ z : (AdeleRing (𝓞 F) F)ˣ, z ∈ (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) := fun z => Subgroup.mem_top z
  have hauto : IsAutomorphicFnAt F
      ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))) ξ φ := hφ.1.1
  have hls := (@lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _ (glBorel (Fin 2) (𝓞 F) F) (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) φ).mp hauto
  have hlsxi : IsLsXiFunction (𝓞 F) F ⊤ ξ φ := hls.1
  have hφint : ∫⁻ h in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖φ h‖ₑ ^ 2
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := lintegral_enorm_sq_lt_top_of_memLp F _ φ hls.2
  have hψc : Continuous (rightConv F φ f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hφc f hf).1
  have hψls : IsLsXiFunction (𝓞 F) F ⊤ ξ (rightConv F φ f) :=
    isLsXiFunction_rightConv_of_isLsXiFunction F ⊤ ξ hlsxi f
  have hψb : IsBoundedOnSiegelWindows F (rightConv F φ f) :=
    AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre F c u d₁ d₂ T
      hd hcov ξ φ hφ.1 hφc f hf
  have hWU := measure_window_inter_support_pos F c u d₁ d₂ T hd hcov ⊤ ξ hZ φ hlsxi hφc hne

  have hx : ∃ x ∈ T, 0 < adelicGLHaar (Fin 2) (𝓞 F) F
      ((· * x) '' centreCutSiegelSet F c u d₁ d₂ ∩ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0}) := by
    by_contra hcon
    have hall : ∀ x ∈ T, adelicGLHaar (Fin 2) (𝓞 F) F
        ((· * x) '' centreCutSiegelSet F c u d₁ d₂ ∩ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0}) = 0 := fun x hxT =>
      le_antisymm (not_lt.mp fun hlt => hcon ⟨x, hxT, hlt⟩) zero_le
    refine hWU.ne' (measure_mono_null ?_ ((measure_biUnion_null_iff T.countable_toSet).mpr hall))
    rintro g ⟨hgW, hgU⟩
    obtain ⟨x, hxT, hgx⟩ := Set.mem_iUnion₂.mp hgW
    exact Set.mem_iUnion₂.mpr ⟨x, hxT, hgx, hgU⟩
  obtain ⟨x₀, hx₀T, hx₀⟩ := hx

  have hn : ∃ n : ℕ, 0 < adelicGLHaar (Fin 2) (𝓞 F) F
      (smwShell F w₀ c u d₁ d₂ x₀ n ∩ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0}) := by
    by_contra hcon
    have hall : ∀ n : ℕ, adelicGLHaar (Fin 2) (𝓞 F) F
        (smwShell F w₀ c u d₁ d₂ x₀ n ∩ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0}) = 0 := fun n =>
      le_antisymm (not_lt.mp fun hlt => hcon ⟨n, hlt⟩) zero_le
    refine hx₀.ne' (measure_mono_null ?_ (measure_iUnion_null_iff.mpr hall))
    rintro g ⟨hgS, hgU⟩
    obtain ⟨n, hgn⟩ := Set.mem_iUnion.mp (subset_iUnion_smwShell F w₀ hw₀ c u d₁ d₂ hd₁ hd₂ x₀ hgS)
    exact Set.mem_iUnion.mpr ⟨n, hgn, hgU⟩
  obtain ⟨n₀, hn₀⟩ := hn
  have hmeasφ : Measurable fun h : AdelicGL2 (𝓞 F) F => ‖φ h‖ₑ ^ 2 := hφc.measurable.enorm.pow_const 2
  have hIn : 0 < ∫⁻ h in smwShell F w₀ c u d₁ d₂ x₀ n₀, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [setLIntegral_pos_iff hmeasφ]
    refine hn₀.trans_le (measure_mono ?_)
    rintro g ⟨hgn, hgU⟩
    have hgU' : φ g ≠ 0 := hgU
    refine ⟨?_, hgn⟩
    show ‖φ g‖ₑ ^ 2 ≠ 0
    exact fun h0 => hgU' (enorm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0))
  have hI0 : 0 < ∫⁻ h in smwBase F w₀ c u d₁ d₂ x₀, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [lintegral_smwShell_eq F w₀ c u d₁ d₂ x₀ n₀ ⊤ ξ hZ φ hlsxi] at hIn
    exact (ENNReal.mul_pos_iff.mp hIn).2

  have hsum : (∑' n : ℕ, (smwFactor F w₀ ⊤ ξ hZ n)⁻¹) *
        ∫⁻ h in smwBase F w₀ c u d₁ d₂ x₀, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      ≤ ∫⁻ h in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖φ h‖ₑ ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [← ENNReal.tsum_mul_right]
    calc ∑' n : ℕ, (smwFactor F w₀ ⊤ ξ hZ n)⁻¹ *
            ∫⁻ h in smwBase F w₀ c u d₁ d₂ x₀, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        = ∑' n : ℕ, ∫⁻ h in smwShell F w₀ c u d₁ d₂ x₀ n, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          tsum_congr fun n => (lintegral_smwShell_eq F w₀ c u d₁ d₂ x₀ n ⊤ ξ hZ φ hlsxi).symm
      _ = ∫⁻ h in ⋃ n : ℕ, smwShell F w₀ c u d₁ d₂ x₀ n, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          (lintegral_iUnion (fun n => measurableSet_smwShell F w₀ c u d₁ d₂ x₀ n)
            (smwShell_pairwise_disjoint F w₀ c u d₁ d₂ x₀) _).symm
      _ ≤ ∫⁻ h in (· * x₀) '' centreCutSiegelSet F c u d₁ d₂, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          lintegral_mono_set (Set.iUnion_subset fun n => smwShell_subset F w₀ hw₀ n hd₁ hd₂.le x₀)
      _ ≤ ∫⁻ h in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖φ h‖ₑ ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          lintegral_mono_set (Set.subset_iUnion₂ (s := fun x (_ : x ∈ T) => (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            x₀ hx₀T)
  have hM : (∑' n : ℕ, (smwFactor F w₀ ⊤ ξ hZ n)⁻¹) < ⊤ := by
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop, ENNReal.top_mul hI0.ne'] at hsum
    exact hφint.ne (top_le_iff.mp hsum)

  have hψx : ∀ y ∈ T, ∫⁻ h in (· * y) '' centreCutSiegelSet F c u d₁ d₂, ‖rightConv F φ f h‖ₑ ^ 2
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
    intro y _
    have hJ : ∫⁻ h in smwBase F w₀ c u d₁ d₂ y, ‖rightConv F φ f h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ :=
      lintegral_smwBase_lt_top F w₀ hw₀ c u d₁ d₂ hc hd₂ y (rightConv F φ f) hψc hψb
    calc ∫⁻ h in (· * y) '' centreCutSiegelSet F c u d₁ d₂, ‖rightConv F φ f h‖ₑ ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        ≤ ∫⁻ h in ⋃ n : ℕ, smwShell F w₀ c u d₁ d₂ y n, ‖rightConv F φ f h‖ₑ ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          lintegral_mono_set (subset_iUnion_smwShell F w₀ hw₀ c u d₁ d₂ hd₁ hd₂ y)
      _ ≤ ∑' n : ℕ, ∫⁻ h in smwShell F w₀ c u d₁ d₂ y n, ‖rightConv F φ f h‖ₑ ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := lintegral_iUnion_le _ _
      _ = ∑' n : ℕ, (smwFactor F w₀ ⊤ ξ hZ n)⁻¹ *
            ∫⁻ h in smwBase F w₀ c u d₁ d₂ y, ‖rightConv F φ f h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          tsum_congr fun n => lintegral_smwShell_eq F w₀ c u d₁ d₂ y n ⊤ ξ hZ (rightConv F φ f) hψls
      _ = (∑' n : ℕ, (smwFactor F w₀ ⊤ ξ hZ n)⁻¹) *
            ∫⁻ h in smwBase F w₀ c u d₁ d₂ y, ‖rightConv F φ f h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          ENNReal.tsum_mul_right
      _ < ⊤ := ENNReal.mul_lt_top hM hJ
  have hsub : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
      ⊆ ⋃ x : T, (· * (x : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSet F c u d₁ d₂ := by
    intro g hg
    obtain ⟨x, hxT, hgx⟩ := Set.mem_iUnion₂.mp hg
    exact Set.mem_iUnion.mpr ⟨⟨x, hxT⟩, hgx⟩
  have hWint : ∫⁻ h in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖rightConv F φ f h‖ₑ ^ 2
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
    calc ∫⁻ h in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖rightConv F φ f h‖ₑ ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        ≤ ∫⁻ h in ⋃ x : T, (· * (x : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSet F c u d₁ d₂,
            ‖rightConv F φ f h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := lintegral_mono_set hsub
      _ ≤ ∑' x : T, ∫⁻ h in (· * (x : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSet F c u d₁ d₂,
            ‖rightConv F φ f h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := lintegral_iUnion_le _ _
      _ = ∑ x : T, ∫⁻ h in (· * (x : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSet F c u d₁ d₂,
            ‖rightConv F φ f h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := tsum_fintype _
      _ < ⊤ := ENNReal.sum_lt_top.mpr fun x _ => hψx x x.2
  exact memLp_of_lintegral_enorm_sq_lt_top F _ _ hψc hWint

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

private theorem memLp_rightConv_window [Countable F] (w₀ : InfinitePlace F) (hw₀ : ∀ w : InfinitePlace F, w = w₀)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MemLp (rightConv F R.toFun f) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
  by_cases hc : c ≤ 0
  · exact ((AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre F c u d₁ d₂ T
      hc hd hcov Φ) ⟨R, hR⟩).elim
  · have hc' : 0 < c := not_le.mp hc
    by_cases hd₁ : 0 < d₁
    · exact memLp_rightConv_of_lt F c u d₁ d₂ T hd hc' hd₁ hcov R.centralChar R.toFun R.smoothCusp hR f hf
    · exact memLp_rightConv_of_nonpos F w₀ hw₀ c u d₁ d₂ T hd hc' (not_lt.mp hd₁) hcov R.centralChar R.toFun
        R.smoothCusp hR R.exists_ne_zero f hf

private theorem memLp_rightConv_window_rat (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : IsFactorizableTestFn ℚ f) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 ℚ) ℚ) := glBorel (Fin 2) (𝓞 ℚ) ℚ
    MemLp (rightConv ℚ R.toFun f) 2
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) :=
  memLp_rightConv_window ℚ default (fun w => Subsingleton.elim w default) c u d₁ d₂ T hd hcov Φ R hR f hf

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

section ModKFinite

set_option autoImplicit false

open NumberField NumberField.AdelicHaar MeasureTheory
open AutomorphicForm

namespace ArchFiniteVector
namespace KFinite

variable (F : Type) [Field F] [NumberField F]

private theorem rightConv_mul_right (φ f : AdelicGL2 (𝓞 F) F → ℂ) (k g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (g * k) = rightConv F φ (fun y => f (k⁻¹ * y)) g := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  rw [rightConv_apply, rightConv_apply]
  have key : (fun x => φ (g * k * x) * f x) =
      fun x => (fun y => φ (g * y) * f (k⁻¹ * y)) (k * x) := by
    funext x
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [key]
  exact MeasureTheory.integral_mul_left_eq_self (fun y => φ (g * y) * f (k⁻¹ * y)) k

private theorem integrable_rightConv_integrand (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (g : AdelicGL2 (𝓞 F) F) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    Integrable (fun x => φ (g * x) * f x) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hcont : Continuous fun x => φ (g * x) * f x := (hφ.comp (continuous_const_mul g)).mul hf
  have hsupp : HasCompactSupport fun x => φ (g * x) * f x := hfc.mul_left
  exact hcont.integrable_of_hasCompactSupport hsupp

private theorem rightConv_mem_span {n : ℕ} (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fs : Fin n → AdelicGL2 (𝓞 F) F → ℂ) (hfs : ∀ i, Continuous (fs i)) (hfsc : ∀ i, HasCompactSupport (fs i))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range fs)) :
    rightConv F φ f ∈ Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i)) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  refine (Submodule.span_induction
    (p := fun f _ => (∀ g, Integrable (fun x => φ (g * x) * f x) (adelicGLHaar (Fin 2) (𝓞 F) F)) ∧
      rightConv F φ f ∈ Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i)))
    ?_ ?_ ?_ ?_ hf).2
  · rintro _ ⟨i, rfl⟩
    exact ⟨fun g => integrable_rightConv_integrand F φ hφ (fs i) (hfs i) (hfsc i) g,
      Submodule.subset_span ⟨i, rfl⟩⟩
  · refine ⟨fun g => ?_, ?_⟩
    · have e : (fun x => φ (g * x) * (0 : AdelicGL2 (𝓞 F) F → ℂ) x) = fun _ => (0 : ℂ) := by
        funext x
        simp
      rw [e]
      exact integrable_zero _ _ _
    · have e : rightConv F φ (0 : AdelicGL2 (𝓞 F) F → ℂ) = 0 := by
        funext g
        simp [rightConv]
      rw [e]
      exact Submodule.zero_mem _
  · rintro f₁ f₂ - - ⟨h₁, m₁⟩ ⟨h₂, m₂⟩
    refine ⟨fun g => ?_, ?_⟩
    · have e : (fun x => φ (g * x) * (f₁ + f₂) x) = fun x => φ (g * x) * f₁ x + φ (g * x) * f₂ x := by
        funext x
        simp only [Pi.add_apply, mul_add]
      rw [e]
      exact (h₁ g).add (h₂ g)
    · have e : rightConv F φ (f₁ + f₂) = rightConv F φ f₁ + rightConv F φ f₂ := by
        funext g
        rw [Pi.add_apply, rightConv_apply, rightConv_apply, rightConv_apply]
        simp only [Pi.add_apply, mul_add]
        exact MeasureTheory.integral_add (h₁ g) (h₂ g)
      rw [e]
      exact Submodule.add_mem _ m₁ m₂
  · rintro a f₁ - ⟨h₁, m₁⟩
    refine ⟨fun g => ?_, ?_⟩
    · have e : (fun x => φ (g * x) * (a • f₁) x) = fun x => a * (φ (g * x) * f₁ x) := by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact (h₁ g).const_mul a
    · have e : rightConv F φ (a • f₁) = a • rightConv F φ f₁ := by
        funext g
        rw [Pi.smul_apply, smul_eq_mul, rightConv_apply, rightConv_apply, ← MeasureTheory.integral_const_mul]
        congr 1
        funext x
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact Submodule.smul_mem _ a m₁

private theorem exists_finiteDimensional_mem_of_forall_mem_span {n : ℕ} {H : Type} [Monoid H]
    (ι : H →* AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fs : Fin n → AdelicGL2 (𝓞 F) F → ℂ) (hfs : ∀ i, Continuous (fs i)) (hfsc : ∀ i, HasCompactSupport (fs i))
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hW : ∀ k : H, (fun y => f ((ι k)⁻¹ * y)) ∈ Submodule.span ℂ (Set.range fs)) :
    ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ V ∧ rightConv F φ f ∈ V ∧
      ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V := by
  refine ⟨Submodule.span ℂ (Set.range fun k : H => fun x => rightConv F φ f (x * ι k)), ?_, ?_, ?_⟩
  · have hle : Submodule.span ℂ (Set.range fun k : H => fun x => rightConv F φ f (x * ι k)) ≤
        Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i)) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      show (fun x => rightConv F φ f (x * ι k)) ∈ Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i))
      have e : (fun x => rightConv F φ f (x * ι k)) = rightConv F φ (fun y => f ((ι k)⁻¹ * y)) := by
        funext x
        exact rightConv_mul_right F φ f (ι k) x
      rw [e]
      exact rightConv_mem_span F φ hφ fs hfs hfsc _ (hW k)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i => rightConv F φ (fs i))) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    exact Submodule.finiteDimensional_of_le hle
  · have e : (fun x => rightConv F φ f (x * ι 1)) = rightConv F φ f := by
      funext x
      rw [map_one, mul_one]
    have h1 : (fun x => rightConv F φ f (x * ι 1)) ∈
        Submodule.span ℂ (Set.range fun k : H => fun x => rightConv F φ f (x * ι k)) :=
      Submodule.subset_span ⟨1, rfl⟩
    rwa [e] at h1
  · intro k v hv
    refine Submodule.span_induction
      (p := fun v _ => (fun x => v (x * ι k)) ∈
        Submodule.span ℂ (Set.range fun k : H => fun x => rightConv F φ f (x * ι k)))
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      funext x
      simp only [map_mul, mul_assoc]
    · exact Submodule.zero_mem _
    · exact fun _ _ _ _ hu hw => Submodule.add_mem _ hu hw
    · exact fun c _ _ hu => Submodule.smul_mem _ c hu

end ArchFiniteVector.KFinite

end ModKFinite

section ModArchCut

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume

namespace ArchFiniteVector
namespace ArchCut

section Generic

variable {H G : Type*} [Group H] [Group G]

private def translateOn (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) (k : H) : V →ₗ[ℂ] V where
  toFun v := ⟨fun x => (v : G → ℂ) (x * ι k), hV k v v.2⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => rfl)

private theorem translateOn_apply_coe (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) (k : H) (v : V) (x : G) :
    (translateOn ι V hV k v : G → ℂ) x = (v : G → ℂ) (x * ι k) :=
  rfl

private theorem translateOn_one (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) :
    translateOn ι V hV 1 = LinearMap.id :=
  LinearMap.ext fun v => Subtype.ext (funext fun x => by simp [translateOn_apply_coe])

private theorem translateOn_mul (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) (k₁ k₂ : H) :
    translateOn ι V hV (k₁ * k₂) = translateOn ι V hV k₁ ∘ₗ translateOn ι V hV k₂ :=
  LinearMap.ext fun v => Subtype.ext (funext fun x => by simp [translateOn_apply_coe, mul_assoc])

private def transportRep (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) {n : ℕ} (e : V ≃ₗ[ℂ] (Fin n → ℂ)) :
    Representation ℂ H (Fin n → ℂ) where
  toFun k := (e : V →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ translateOn ι V hV k ∘ₗ (e.symm : (Fin n → ℂ) →ₗ[ℂ] V)
  map_one' := LinearMap.ext fun a => by simp [translateOn_one]
  map_mul' k₁ k₂ := LinearMap.ext fun a => by simp [translateOn_mul, Module.End.mul_apply]

private theorem transportRep_apply (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) {n : ℕ} (e : V ≃ₗ[ℂ] (Fin n → ℂ)) (k : H)
    (a : Fin n → ℂ) : transportRep ι V hV e k a = e (translateOn ι V hV k (e.symm a)) :=
  rfl

private theorem isRightEquivariant_subtype_comp_symm (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) {n : ℕ} (e : V ≃ₗ[ℂ] (Fin n → ℂ)) :
    IsRightEquivariant ι (transportRep ι V hV e)
      (V.subtype ∘ₗ (e.symm : (Fin n → ℂ) →ₗ[ℂ] V)) := by
  intro k a x
  simp [transportRep_apply, translateOn_apply_coe]

private theorem exists_rep_mem_typeSubmodule (ι : H →* G) {u : G → ℂ} (V : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ V] (hu : u ∈ V) (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) :
    ∃ (n : ℕ) (ρ : Representation ℂ H (Fin n → ℂ)), u ∈ typeSubmodule ι ρ := by
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
  refine ⟨Module.finrank ℂ V, transportRep ι V hV e, ?_⟩
  have hmem := mem_typeSubmodule_of_isRightEquivariant (isRightEquivariant_subtype_comp_symm ι V hV e)
    (e ⟨u, hu⟩)
  simpa using hmem

private theorem comp_inv_mem_span {N : ℕ} (b : Fin N → G → ℂ) {h : G → ℂ}
    (hh : h ∈ Submodule.span ℂ (Set.range b)) :
    (fun x => h x⁻¹) ∈ Submodule.span ℂ (Set.range fun i => fun x => b i x⁻¹) := by
  refine Submodule.span_induction
    (p := fun h _ => (fun x => h x⁻¹) ∈ Submodule.span ℂ (Set.range fun i => fun x => b i x⁻¹))
    ?_ ?_ ?_ ?_ hh
  · rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · exact Submodule.zero_mem _
  · exact fun _ _ _ _ hu hw => Submodule.add_mem _ hu hw
  · exact fun c _ _ hu => Submodule.smul_mem _ c hu

private theorem exists_stable_of_translates_mem (ι : H →* G) (u : G → ℂ) (W : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ W] (hW : ∀ k : H, (fun x => u (x * ι k)) ∈ W) :
    ∃ V : Submodule ℂ (G → ℂ), FiniteDimensional ℂ V ∧ u ∈ V ∧
      ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V := by
  refine ⟨Submodule.span ℂ (Set.range fun k : H => fun x => u (x * ι k)), ?_, ?_, ?_⟩
  · have hle : Submodule.span ℂ (Set.range fun k : H => fun x => u (x * ι k)) ≤ W := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      exact hW k
    exact Submodule.finiteDimensional_of_le hle
  · have e : (fun x => u (x * ι 1)) = u := by
      funext x
      rw [map_one, mul_one]
    have h1 : (fun x => u (x * ι 1)) ∈ Submodule.span ℂ (Set.range fun k : H => fun x => u (x * ι k)) :=
      Submodule.subset_span ⟨1, rfl⟩
    rwa [e] at h1
  · intro k v hv
    refine Submodule.span_induction
      (p := fun v _ => (fun x => v (x * ι k)) ∈ Submodule.span ℂ (Set.range fun k : H => fun x => u (x * ι k)))
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      funext x
      simp only [map_mul, mul_assoc]
    · exact Submodule.zero_mem _
    · exact fun _ _ _ _ hu hw => Submodule.add_mem _ hu hw
    · exact fun c _ _ hu => Submodule.smul_mem _ c hu

private def dualCarrierEquiv (n : ℕ) : (Fin n → ℂ) ≃ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ) :=
  (Pi.basisFun ℂ (Fin n)).dualBasis.equivFun.symm

private def dualTransport {n : ℕ} (σ : Representation ℂ H (Fin n → ℂ)) : Representation ℂ H (Fin n → ℂ) where
  toFun k := ((dualCarrierEquiv n).symm : Module.Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ σ.dual k ∘ₗ
    (dualCarrierEquiv n : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ))
  map_one' := LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_one, Module.End.one_apply,
      LinearEquiv.symm_apply_apply]
  map_mul' k₁ k₂ := LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_mul, Module.End.mul_apply,
      LinearEquiv.apply_symm_apply]

private theorem dualTransport_apply {n : ℕ} (σ : Representation ℂ H (Fin n → ℂ)) (k : H) (a : Fin n → ℂ) :
    dualTransport σ k a = (dualCarrierEquiv n).symm (σ.dual k (dualCarrierEquiv n a)) :=
  rfl

private def dualEquiv (n : ℕ) : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  ((dualCarrierEquiv n).symm.dualMap).trans (Module.evalEquiv ℂ (Fin n → ℂ)).symm

private theorem apply_dualEquiv (n : ℕ) (φ ψ : Module.Dual ℂ (Fin n → ℂ)) :
    ψ (dualEquiv n φ) = φ ((dualCarrierEquiv n).symm ψ) := by
  simp only [dualEquiv, LinearEquiv.trans_apply, Module.apply_evalEquiv_symm_apply, LinearEquiv.dualMap_apply]

private theorem dualEquiv_dual_apply {n : ℕ} (σ : Representation ℂ H (Fin n → ℂ)) (k : H)
    (φ : Module.Dual ℂ (Fin n → ℂ)) :
    dualEquiv n ((dualTransport σ).dual k φ) = σ k (dualEquiv n φ) := by
  have key : ∀ ψ : Module.Dual ℂ (Fin n → ℂ),
      ψ (dualEquiv n ((dualTransport σ).dual k φ)) = ψ (σ k (dualEquiv n φ)) := by
    intro ψ
    rw [apply_dualEquiv]
    change φ (dualTransport σ k⁻¹ ((dualCarrierEquiv n).symm ψ)) = _
    rw [dualTransport_apply, LinearEquiv.apply_symm_apply]
    change φ ((dualCarrierEquiv n).symm (ψ ∘ₗ σ k⁻¹⁻¹)) = _
    rw [inv_inv, ← apply_dualEquiv n φ (ψ ∘ₗ σ k)]
    rfl
  exact (Module.evalEquiv ℂ (Fin n → ℂ)).injective (LinearMap.ext fun ψ => by
    simpa only [Module.evalEquiv_apply, Module.Dual.eval_apply] using key ψ)

private theorem exists_rep_mem_typeSubmodule_dual (ι : H →* G) {u : G → ℂ} (V : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ V] (hu : u ∈ V) (hV : ∀ k : H, ∀ v ∈ V, (fun x => v (x * ι k)) ∈ V) :
    ∃ (n : ℕ) (ρ : Representation ℂ H (Fin n → ℂ)), u ∈ typeSubmodule ι ρ.dual := by
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
  refine ⟨Module.finrank ℂ V, dualTransport (transportRep ι V hV e), ?_⟩
  have hT : IsRightEquivariant ι (dualTransport (transportRep ι V hV e)).dual
      ((V.subtype ∘ₗ (e.symm : (Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] V)) ∘ₗ
        (dualEquiv (Module.finrank ℂ V) :
          Module.Dual ℂ (Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ))) := by
    intro k φ x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, dualEquiv_dual_apply]
    exact isRightEquivariant_subtype_comp_symm ι V hV e k (dualEquiv _ φ) x
  have hmem := mem_typeSubmodule_of_isRightEquivariant hT ((dualEquiv (Module.finrank ℂ V)).symm (e ⟨u, hu⟩))
  simpa using hmem

end Generic

private theorem exists_archTypeFamily_mem_archCutSubmodule (F : Type) [Field F] [NumberField F]
    (u : AdelicGL2 (𝓞 F) F → ℂ)
    (hV : ∀ w : InfinitePlace F, ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ V ∧ u ∈ V ∧
        ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ v ∈ V, (fun x => v (x * rowIsometryInclAt₀ F w k)) ∈ V) :
    ∃ tys : ArchTypeFamily F, u ∈ archCutSubmodule F tys := by
  have h : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w, u ∈ archTypeSubmoduleAt F w τ := by
    intro w
    obtain ⟨V, hfin, hu, hstab⟩ := hV w
    haveI := hfin
    obtain ⟨n, ρ, hmem⟩ := exists_rep_mem_typeSubmodule (rowIsometryInclAt₀ F w) V hu hstab
    exact ⟨⟨n, ρ⟩, hmem⟩
  choose τ hτ using h
  refine ⟨⟨fun _ => 1, fun w _ => τ w⟩, ?_⟩
  rw [mem_archCutSubmodule_iff]
  intro w
  exact Submodule.mem_iSup_of_mem (0 : Fin 1) (hτ w)

end ArchFiniteVector.ArchCut

end ModArchCut

section ModPoly

set_option autoImplicit false

open scoped Classical
open MeasureTheory

namespace ArchFiniteVector
namespace Poly

section Checks
end Checks

section SubstFinite

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private def precomp (L : E →ₗ[ℝ] E) : (E → ℝ) →ₐ[ℝ] (E → ℝ) where
  toFun v := v ∘ L
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[scoped simp] private theorem precomp_apply (L : E →ₗ[ℝ] E) (v : E → ℝ) (x : E) :
    precomp L v x = v (L x) := rfl

private def IsSubstFinite (h : E → ℝ) : Prop :=
  ∃ V : Submodule ℝ (E → ℝ), FiniteDimensional ℝ V ∧ h ∈ V ∧
    ∀ L : E →ₗ[ℝ] E, ∀ v ∈ V, precomp L v ∈ V

private theorem IsSubstFinite.mul {h₁ h₂ : E → ℝ} (H₁ : IsSubstFinite h₁) (H₂ : IsSubstFinite h₂) :
    IsSubstFinite (h₁ * h₂) := by
  obtain ⟨V₁, hfd₁, hm₁, hs₁⟩ := H₁
  obtain ⟨V₂, hfd₂, hm₂, hs₂⟩ := H₂
  haveI := hfd₁
  haveI := hfd₂
  refine ⟨V₁ * V₂, ?_, Submodule.mul_mem_mul hm₁ hm₂, ?_⟩
  · exact Module.Finite.iff_fg.mpr
      ((Module.Finite.iff_fg.mp hfd₁).mul (Module.Finite.iff_fg.mp hfd₂))
  · intro L v hv
    refine Submodule.mul_induction_on hv ?_ ?_
    · intro m hm n hn
      rw [map_mul]
      exact Submodule.mul_mem_mul (hs₁ L m hm) (hs₂ L n hn)
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy

private theorem IsSubstFinite.add {h₁ h₂ : E → ℝ} (H₁ : IsSubstFinite h₁) (H₂ : IsSubstFinite h₂) :
    IsSubstFinite (h₁ + h₂) := by
  obtain ⟨V₁, hfd₁, hm₁, hs₁⟩ := H₁
  obtain ⟨V₂, hfd₂, hm₂, hs₂⟩ := H₂
  haveI := hfd₁
  haveI := hfd₂
  refine ⟨V₁ ⊔ V₂, inferInstance, Submodule.add_mem_sup hm₁ hm₂, ?_⟩
  intro L v hv
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add]
  exact Submodule.add_mem_sup (hs₁ L y hy) (hs₂ L z hz)

private theorem IsSubstFinite.const (c : ℝ) : IsSubstFinite (fun _ : E => c) := by
  refine ⟨Submodule.span ℝ {fun _ : E => (1 : ℝ)}, ?_, ?_, ?_⟩
  · exact FiniteDimensional.span_of_finite ℝ (Set.finite_singleton _)
  · have h1 : (fun _ : E => c) = c • (fun _ : E => (1 : ℝ)) := by
      funext x
      simp
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · intro L v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have h2 : precomp L (a • fun _ : E => (1 : ℝ)) = a • fun _ : E => (1 : ℝ) := by
      funext x
      simp
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

variable (E) in
private def substFinite : Subalgebra ℝ (E → ℝ) where
  carrier := {h | IsSubstFinite h}
  mul_mem' := IsSubstFinite.mul
  add_mem' := IsSubstFinite.add
  algebraMap_mem' c := by
    have h : (algebraMap ℝ (E → ℝ) c) = fun _ => c := by
      funext x
      simp
    show IsSubstFinite (algebraMap ℝ (E → ℝ) c)
    rw [h]
    exact IsSubstFinite.const c

private theorem IsSubstFinite.linear [FiniteDimensional ℝ E] (ℓ : E →ₗ[ℝ] ℝ) :
    IsSubstFinite (ℓ : E → ℝ) := by
  let b := Module.finBasis ℝ E
  let V : Submodule ℝ (E → ℝ) :=
    Submodule.span ℝ (Set.range fun i => (b.coord i : E → ℝ))
  have key : ∀ f : E →ₗ[ℝ] ℝ, (f : E → ℝ) ∈ V := by
    intro f
    have hf : (f : E → ℝ) = ∑ i, f (b i) • (b.coord i : E → ℝ) := by
      funext m
      rw [Finset.sum_apply]
      conv_lhs => rw [← b.sum_repr m]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_smul, Pi.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
      ring
    rw [hf]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨V, FiniteDimensional.span_of_finite ℝ (Set.finite_range _), key ℓ, ?_⟩
  intro L v hv
  have hle : V.map (precomp L).toLinearMap ≤ V := by
    refine (Submodule.map_span_le _ _ _).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact key ((b.coord i).comp L)
  exact hle (Submodule.mem_map_of_mem hv)

end SubstFinite

section Poly

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private def smoothSubmodule : Submodule ℝ (E → ℝ) where
  carrier := {w | ContDiff ℝ (⊤ : ℕ∞) w}
  add_mem' {v w} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hw : ContDiff ℝ (⊤ : ℕ∞) w) := by
    show ContDiff ℝ (⊤ : ℕ∞) (v + w)
    exact hv.add hw
  zero_mem' := by
    show ContDiff ℝ (⊤ : ℕ∞) (0 : E → ℝ)
    exact contDiff_const
  smul_mem' c w (hw : ContDiff ℝ (⊤ : ℕ∞) w) := by
    show ContDiff ℝ (⊤ : ℕ∞) (c • w)
    exact contDiff_const.smul hw

variable {E} in
private theorem IsSubstFinite.exists_smooth_span {p : E → ℝ} (hs : IsSubstFinite p) (hp : ContDiff ℝ (⊤ : ℕ∞) p) :
    ∃ (n : ℕ) (b : Fin n → E → ℝ), (∀ i, ContDiff ℝ (⊤ : ℕ∞) (b i)) ∧
      ∀ L : E →ₗ[ℝ] E, (p ∘ L) ∈ Submodule.span ℝ (Set.range b) := by
  obtain ⟨V, hfd, hpV, hst⟩ := hs
  haveI := hfd
  let W : Submodule ℝ (E → ℝ) := Submodule.span ℝ (Set.range fun L : E →ₗ[ℝ] E => precomp L p)
  have hWV : W ≤ V := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨L, rfl⟩
    exact hst L p hpV
  haveI : FiniteDimensional ℝ W := Submodule.finiteDimensional_of_le hWV
  have hWsmooth : W ≤ smoothSubmodule E := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨L, rfl⟩
    show ContDiff ℝ (⊤ : ℕ∞) (p ∘ L)
    exact hp.comp (LinearMap.toContinuousLinearMap L).contDiff
  let bW := Module.finBasis ℝ W
  refine ⟨Module.finrank ℝ W, fun i => (bW i : E → ℝ), fun i => hWsmooth (bW i).2, fun L => ?_⟩
  have hmem : precomp L p ∈ W := Submodule.subset_span ⟨L, rfl⟩
  have hrepr := bW.sum_repr ⟨precomp L p, hmem⟩
  have hsum : (p ∘ L : E → ℝ) = ∑ i, bW.repr ⟨precomp L p, hmem⟩ i • (bW i : E → ℝ) := by
    have h := congrArg (W.subtype) hrepr
    rw [map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    exact h.symm
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private def coordC (ℓ : E →ₗ[ℝ] ℝ) : C(E, ℝ) := ⟨ℓ, ℓ.continuous_of_finiteDimensional⟩

@[scoped simp] private theorem coordC_apply (ℓ : E →ₗ[ℝ] ℝ) (x : E) : coordC E ℓ x = ℓ x := rfl

private def polyAlg : Subalgebra ℝ C(E, ℝ) :=
  Algebra.adjoin ℝ (Set.range fun ℓ : E →ₗ[ℝ] ℝ => coordC E ℓ)

private def goodAlg : Subalgebra ℝ C(E, ℝ) where
  carrier := {p | ContDiff ℝ (⊤ : ℕ∞) (p : E → ℝ) ∧ IsSubstFinite (p : E → ℝ)}
  mul_mem' := fun {p q} hp hq => ⟨hp.1.mul hq.1, hp.2.mul hq.2⟩
  add_mem' := fun {p q} hp hq => ⟨hp.1.add hq.1, hp.2.add hq.2⟩
  algebraMap_mem' c := by
    have h : ((algebraMap ℝ C(E, ℝ) c : C(E, ℝ)) : E → ℝ) = fun _ => c := by
      funext x
      simp [Algebra.algebraMap_eq_smul_one]
    refine ⟨?_, ?_⟩
    · rw [h]
      exact contDiff_const
    · rw [h]
      exact IsSubstFinite.const c

private theorem polyAlg_le_goodAlg : polyAlg E ≤ goodAlg E := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨ℓ, rfl⟩
  refine ⟨?_, ?_⟩
  · have h : ((coordC E ℓ : C(E, ℝ)) : E → ℝ) = (LinearMap.toContinuousLinearMap ℓ : E → ℝ) := by
      funext x
      simp
    rw [h]
    exact (LinearMap.toContinuousLinearMap ℓ).contDiff
  · exact IsSubstFinite.linear ℓ

private theorem polyAlg_separatesPoints : (polyAlg E).SeparatesPoints := by
  intro x y hxy
  let b := Module.finBasis ℝ E
  have hex : ∃ i, b.repr x i ≠ b.repr y i :=
    not_forall.mp fun h => hxy (b.ext_elem_iff.mpr h)
  obtain ⟨i, hi⟩ := hex
  refine ⟨coordC E (b.coord i), ⟨coordC E (b.coord i), Algebra.subset_adjoin ⟨b.coord i, rfl⟩, rfl⟩,
    ?_⟩
  show b.coord i x ≠ b.coord i y
  simpa [Module.Basis.coord_apply] using hi

private theorem exists_poly_near (K : Set E) (hK : IsCompact K) (Φ : E → ℝ) (hΦ : Continuous Φ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧ IsSubstFinite p ∧ ∀ x ∈ K, ‖p x - Φ x‖ < ε := by
  obtain ⟨g, hg, happrox⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (polyAlg_separatesPoints E) (⟨Φ, hΦ⟩ : C(E, ℝ)) hK hε
  exact ⟨g, (polyAlg_le_goodAlg E hg).1, (polyAlg_le_goodAlg E hg).2, fun x hx => happrox x hx⟩

private theorem exists_poly_pair_near (K : Set E) (hK : IsCompact K) (Φ : E → ℂ) (hΦ : Continuous Φ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧ IsSubstFinite p ∧ ContDiff ℝ (⊤ : ℕ∞) q ∧
      IsSubstFinite q ∧ ∀ x ∈ K, ‖((p x : ℂ) + (q x : ℂ) * Complex.I) - Φ x‖ < ε := by
  obtain ⟨p, hp1, hp2, hp3⟩ := exists_poly_near E K hK (fun x => (Φ x).re)
    (Complex.continuous_re.comp hΦ) (ε / 2) (half_pos hε)
  obtain ⟨q, hq1, hq2, hq3⟩ := exists_poly_near E K hK (fun x => (Φ x).im)
    (Complex.continuous_im.comp hΦ) (ε / 2) (half_pos hε)
  refine ⟨p, q, hp1, hp2, hq1, hq2, fun x hx => ?_⟩
  have hre : |p x - (Φ x).re| < ε / 2 := by simpa [Real.norm_eq_abs] using hp3 x hx
  have him : |q x - (Φ x).im| < ε / 2 := by simpa [Real.norm_eq_abs] using hq3 x hx
  set z : ℂ := ((p x : ℂ) + (q x : ℂ) * Complex.I) - Φ x with hz
  have hzre : z.re = p x - (Φ x).re := by simp [hz]
  have hzim : z.im = q x - (Φ x).im := by simp [hz]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ < ε / 2 + ε / 2 := by rw [hzre, hzim]; exact add_lt_add hre him
    _ = ε := by ring

end Poly

section Estimate

variable {G : Type*} [MeasurableSpace G] {μ : Measure G}

private theorem norm_integral_sub_integral_le {w a a' r : G → ℂ} {δ : ℝ}
    (hi : Integrable (fun y => w y * (a y * r y)) μ)
    (hi' : Integrable (fun y => w y * (a' y * r y)) μ)
    (hwr : Integrable (fun y => ‖w y‖ * ‖r y‖) μ)
    (hb : ∀ y, r y ≠ 0 → ‖a y - a' y‖ ≤ δ) :
    ‖(∫ y, w y * (a y * r y) ∂μ) - ∫ y, w y * (a' y * r y) ∂μ‖
      ≤ δ * ∫ y, ‖w y‖ * ‖r y‖ ∂μ := by
  rw [← integral_sub hi hi', ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hwr.const_mul δ) (Filter.Eventually.of_forall fun y => ?_)
  have h1 : w y * (a y * r y) - w y * (a' y * r y) = w y * ((a y - a' y) * r y) := by ring
  rw [h1, norm_mul, norm_mul]
  by_cases hr : r y = 0
  · simp [hr]
  · calc ‖w y‖ * (‖a y - a' y‖ * ‖r y‖) ≤ ‖w y‖ * (δ * ‖r y‖) := by
          gcongr
          exact hb y hr
      _ = δ * (‖w y‖ * ‖r y‖) := by ring

private theorem integral_ne_zero_of_close {w a a' r : G → ℂ} {δ : ℝ}
    (hi : Integrable (fun y => w y * (a y * r y)) μ)
    (hi' : Integrable (fun y => w y * (a' y * r y)) μ)
    (hwr : Integrable (fun y => ‖w y‖ * ‖r y‖) μ)
    (hb : ∀ y, r y ≠ 0 → ‖a y - a' y‖ ≤ δ)
    (hsmall : δ * ∫ y, ‖w y‖ * ‖r y‖ ∂μ < ‖∫ y, w y * (a' y * r y) ∂μ‖) :
    (∫ y, w y * (a y * r y) ∂μ) ≠ 0 := by
  intro h0
  have hle := norm_integral_sub_integral_le (μ := μ) hi hi' hwr hb
  rw [h0, zero_sub, norm_neg] at hle
  exact absurd (lt_of_le_of_lt hle hsmall) (lt_irrefl _)

end Estimate

end ArchFiniteVector.Poly
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector"

end ModPoly
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

section ModPlateau

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.InfinitePlace
p2m_open "NumberField.InfinitePlace.Completion IsDedekindDomain NumberField.InfiniteAdeleRing AutomorphicForm"
open AutomorphicForm.WindowedSiegel Metric Topology

open scoped Classical

namespace ArchFiniteVector
namespace Plateau

section PinChecks
end PinChecks
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

section PerField

variable {K : Type*} [NormedField K]

private def HS (A : Matrix (Fin 2) (Fin 2) K) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

private theorem HS_eq_four (A : Matrix (Fin 2) (Fin 2) K) :
    HS A = ‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + (‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) := by
  simp [HS, Fin.sum_univ_two]

private theorem HS_eq (g : GL (Fin 2) K) :
    HS (g : Matrix (Fin 2) (Fin 2) K) =
      ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ^ 2 *
        (topNormSq ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) +
          rowNormSq ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  have hinv : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (g : Matrix (Fin 2) (Fin 2) K).det⁻¹ • (g : Matrix (Fin 2) (Fin 2) K).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv]
  have hn : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ≠ 0 := norm_ne_zero_iff.mpr hdet
  rw [hinv, Matrix.adjugate_fin_two, HS_eq_four]
  simp [topNormSq, rowNormSq, Matrix.smul_apply, norm_mul, norm_inv, norm_neg]
  field_simp
  ring

private theorem HS_rowIsometry_mul (k g : GL (Fin 2) K) (hk : IsRowIsometry k) :
    HS ((k * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = HS (g : Matrix (Fin 2) (Fin 2) K) := by
  rw [HS_eq, HS_eq, _root_.mul_inv_rev, topNormSq_mul_rowIsometry _ hk.inv,
    rowNormSq_mul_rowIsometry _ hk.inv, Units.val_mul, Matrix.det_mul, norm_mul, hk.1, one_mul]

private theorem HS_mul_rowIsometry (g k : GL (Fin 2) K) (hk : IsRowIsometry k) :
    HS ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = HS (g : Matrix (Fin 2) (Fin 2) K) := by
  rw [HS_eq_four, HS_eq_four, Units.val_mul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hk.2, hk.2]

end PerField
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

section EntrySpace

variable (F : Type) [Field F] [NumberField F]

private abbrev E : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F

private def q (m : mixedEmbedding.mixedSpace F) : ℝ := (∑ v, ‖m.1 v‖ ^ 2) + ∑ v, ‖m.2 v‖ ^ 2

private theorem q_nonneg (m : mixedEmbedding.mixedSpace F) : 0 ≤ q F m :=
  add_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (Finset.sum_nonneg fun _ _ => by positivity)

private theorem sq_fst_le_q (m : mixedEmbedding.mixedSpace F) (v : {w : InfinitePlace F // IsReal w}) :
    ‖m.1 v‖ ^ 2 ≤ q F m :=
  le_add_of_le_of_nonneg
    (Finset.single_le_sum (f := fun v => ‖m.1 v‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ v))
    (Finset.sum_nonneg fun _ _ => by positivity)

private theorem sq_snd_le_q (m : mixedEmbedding.mixedSpace F) (v : {w : InfinitePlace F // IsComplex w}) :
    ‖m.2 v‖ ^ 2 ≤ q F m :=
  le_add_of_nonneg_of_le (Finset.sum_nonneg fun _ _ => by positivity)
    (Finset.single_le_sum (f := fun v => ‖m.2 v‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ v))

private theorem contDiff_q : ContDiff ℝ (⊤ : ℕ∞) (q F) := by
  unfold q
  refine ContDiff.add ?_ ?_
  · exact ContDiff.sum fun v _ => ((contDiff_apply ℝ ℝ v).comp contDiff_fst).norm_sq (𝕜 := ℝ)
  · exact ContDiff.sum fun v _ => ((contDiff_apply ℝ ℂ v).comp contDiff_snd).norm_sq (𝕜 := ℂ)

private theorem q_ringEquiv (x : InfiniteAdeleRing F) :
    q F (InfiniteAdeleRing.ringEquiv_mixedSpace F x) = ∑ w, ‖x w‖ ^ 2 := by
  have h1 : ∀ v : {w : InfinitePlace F // IsReal w},
      ‖extensionEmbeddingOfIsReal v.2 (x v.1)‖ = ‖x v.1‖ := fun v =>
    (isometry_extensionEmbeddingOfIsReal v.2).norm_map_of_map_zero (map_zero _) _
  have h2 : ∀ v : {w : InfinitePlace F // IsComplex w},
      ‖extensionEmbedding v.1 (x v.1)‖ = ‖x v.1‖ := fun v =>
    (isometry_extensionEmbedding v.1).norm_map_of_map_zero (map_zero _) _
  simp only [q, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, h1, h2]
  rw [← Fintype.sum_subtype_add_sum_subtype IsReal (fun w => ‖x w‖ ^ 2)]
  congr 1
  exact (Fintype.sum_equiv (Equiv.subtypeEquivRight fun _ => not_isReal_iff_isComplex)
    (fun v => ‖x v.1‖ ^ 2) (fun v => ‖x v.1‖ ^ 2) fun _ => rfl).symm

private def N (M : E F) : ℝ := ∑ i, ∑ j, q F (M i j)

private theorem q_le_N (M : E F) (i j : Fin 2) : q F (M i j) ≤ N F M := by
  unfold N
  calc q F (M i j) ≤ ∑ j', q F (M i j') :=
        Finset.single_le_sum (f := fun j' => q F (M i j')) (fun _ _ => q_nonneg F _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', q F (M i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', q F (M i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => q_nonneg F _) (Finset.mem_univ i)

private theorem contDiff_N : ContDiff ℝ (⊤ : ℕ∞) (N F) := by
  unfold N
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (contDiff_q F).comp ((contDiff_apply ℝ (mixedEmbedding.mixedSpace F) j).comp
      (contDiff_apply ℝ (Fin 2 → mixedEmbedding.mixedSpace F) i))

private theorem norm_le_sqrt_N (M : E F) : ‖M‖ ≤ Real.sqrt (N F M) := by
  have key : ∀ (a : ℝ), 0 ≤ a → a ^ 2 ≤ N F M → a ≤ Real.sqrt (N F M) := fun a ha h =>
    calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
      _ ≤ Real.sqrt (N F M) := Real.sqrt_le_sqrt h
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun v => ?_
    exact key _ (norm_nonneg _) ((sq_fst_le_q F _ v).trans (q_le_N F M i j))
  · refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun v => ?_
    exact key _ (norm_nonneg _) ((sq_snd_le_q F _ v).trans (q_le_N F M i j))

private def detE (M : E F) : mixedEmbedding.mixedSpace F := M 0 0 * M 1 1 - M 0 1 * M 1 0

omit [NumberField F] in
private theorem detE_eq_det (M : E F) :
    detE F M = Matrix.det (M : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) := by
  rw [Matrix.det_fin_two]
  rfl

private theorem contDiff_detE : ContDiff ℝ (⊤ : ℕ∞) (detE F) := by
  have hc : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) fun M : E F => M i j := fun i j =>
    (contDiff_apply ℝ (mixedEmbedding.mixedSpace F) j).comp
      (contDiff_apply ℝ (Fin 2 → mixedEmbedding.mixedSpace F) i)
  unfold detE
  exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))

private def PD (M : E F) : ℝ := (∏ v, ‖(detE F M).1 v‖ ^ 2) * ∏ v, ‖(detE F M).2 v‖ ^ 2

private theorem PD_nonneg (M : E F) : 0 ≤ PD F M :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) (Finset.prod_nonneg fun _ _ => by positivity)

private theorem contDiff_PD : ContDiff ℝ (⊤ : ℕ∞) (PD F) := by
  unfold PD
  refine ContDiff.mul ?_ ?_
  · exact contDiff_prod fun v _ =>
      ((contDiff_apply ℝ ℝ v).comp (contDiff_fst.comp (contDiff_detE F))).norm_sq (𝕜 := ℝ)
  · exact contDiff_prod fun v _ =>
      ((contDiff_apply ℝ ℂ v).comp (contDiff_snd.comp (contDiff_detE F))).norm_sq (𝕜 := ℂ)

private theorem isUnit_detE_of_PD_ne_zero {M : E F} (h : PD F M ≠ 0) : IsUnit (detE F M) := by
  have h1 : ∀ v, (detE F M).1 v ≠ 0 := fun v hv => by
    apply h
    unfold PD
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hv, norm_zero, zero_pow two_ne_zero]), zero_mul]
  have h2 : ∀ v, (detE F M).2 v ≠ 0 := fun v hv => by
    apply h
    unfold PD
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hv, norm_zero, zero_pow two_ne_zero]), mul_zero]
  refine IsUnit.of_mul_eq_one ⟨fun v => ((detE F M).1 v)⁻¹, fun v => ((detE F M).2 v)⁻¹⟩ ?_
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · show (detE F M).1 v * ((detE F M).1 v)⁻¹ = 1
    exact mul_inv_cancel₀ (h1 v)
  · show (detE F M).2 v * ((detE F M).2 v)⁻¹ = 1
    exact mul_inv_cancel₀ (h2 v)

end EntrySpace
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

section Bridges

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
private theorem archEntries_eq_mapMatrix (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    (archEntries F y : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.mapMatrix
        (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  funext i j
  rfl

omit [NumberField F] in
private theorem archComponent_coe (w : InfinitePlace F) (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    ((archComponent F w y : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) =
      (archEval F w).mapMatrix (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  ext i j
  rfl

private theorem N_archEntries (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    N F (archEntries F y) =
      ∑ w : InfinitePlace F, HS ((archComponent F w y : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) := by
  unfold N HS
  simp only [archEntries_apply, q_ringEquiv]
  calc (∑ i, ∑ j, ∑ w, ‖(y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w‖ ^ 2)
        = ∑ i, ∑ w, ∑ j, ‖(y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w‖ ^ 2 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ w, ∑ i, ∑ j, ‖(y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w‖ ^ 2 := Finset.sum_comm
    _ = _ := by rfl

omit [NumberField F] in
private theorem detE_archEntries (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    detE F (archEntries F y) =
      InfiniteAdeleRing.ringEquiv_mixedSpace F (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det := by
  rw [detE_eq_det, archEntries_eq_mapMatrix]
  exact (RingHom.map_det _ _).symm

omit [NumberField F] in
private theorem norm_detE_fst (y : GL (Fin 2) (InfiniteAdeleRing F)) (v : {w : InfinitePlace F // IsReal w}) :
    ‖(detE F (archEntries F y)).1 v‖ =
      ‖((archComponent F v.1 y : GL (Fin 2) v.1.Completion) : Matrix (Fin 2) (Fin 2) v.1.Completion).det‖ := by
  rw [detE_archEntries, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  show ‖extensionEmbeddingOfIsReal v.2 ((y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det v.1)‖ = _
  rw [(isometry_extensionEmbeddingOfIsReal v.2).norm_map_of_map_zero (map_zero _), archComponent_coe,
    ← RingHom.map_det]
  rfl

omit [NumberField F] in
private theorem norm_detE_snd (y : GL (Fin 2) (InfiniteAdeleRing F)) (v : {w : InfinitePlace F // IsComplex w}) :
    ‖(detE F (archEntries F y)).2 v‖ =
      ‖((archComponent F v.1 y : GL (Fin 2) v.1.Completion) : Matrix (Fin 2) (Fin 2) v.1.Completion).det‖ := by
  rw [detE_archEntries, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  show ‖extensionEmbedding v.1 ((y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det v.1)‖ = _
  rw [(isometry_extensionEmbedding v.1).norm_map_of_map_zero (map_zero _), archComponent_coe,
    ← RingHom.map_det]
  rfl

private theorem PD_archEntries_pos (y : GL (Fin 2) (InfiniteAdeleRing F)) : 0 < PD F (archEntries F y) := by
  unfold PD
  refine mul_pos (Finset.prod_pos fun v _ => ?_) (Finset.prod_pos fun v _ => ?_)
  · rw [norm_detE_fst]
    exact pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)) 2
  · rw [norm_detE_snd]
    exact pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)) 2

variable {F}

omit [NumberField F] in
private theorem norm_det_archComponent_mul (w : InfinitePlace F) (k : GL (Fin 2) w.Completion)
    (hk : IsRowIsometry k) (y : GL (Fin 2) (InfiniteAdeleRing F)) (v : InfinitePlace F) :
    ‖((archComponent F v (archGLIncl F w k * y) : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion).det‖ =
      ‖((archComponent F v y : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion).det‖ := by
  rw [map_mul]
  by_cases h : v = w
  · subst h
    rw [archComponent_archGLIncl_self, Units.val_mul, Matrix.det_mul, norm_mul, hk.1, one_mul]
  · rw [archComponent_archGLIncl_of_ne F h, one_mul]

private theorem N_archEntries_mul (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    N F (archEntries F (archGLIncl F w k * y)) = N F (archEntries F y) := by
  rw [N_archEntries, N_archEntries]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul]
  by_cases h : v = w
  · subst h
    rw [archComponent_archGLIncl_self]
    exact HS_rowIsometry_mul k _ hk
  · rw [archComponent_archGLIncl_of_ne F h, one_mul]

private theorem PD_archEntries_mul (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    PD F (archEntries F (archGLIncl F w k * y)) = PD F (archEntries F y) := by
  unfold PD
  simp only [norm_detE_fst, norm_detE_snd, norm_det_archComponent_mul w k hk y]

omit [NumberField F] in
private theorem norm_det_archComponent_mul_right (w : InfinitePlace F) (k : GL (Fin 2) w.Completion)
    (hk : IsRowIsometry k) (y : GL (Fin 2) (InfiniteAdeleRing F)) (v : InfinitePlace F) :
    ‖((archComponent F v (y * archGLIncl F w k) : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion).det‖ =
      ‖((archComponent F v y : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion).det‖ := by
  rw [map_mul]
  by_cases h : v = w
  · subst h
    rw [archComponent_archGLIncl_self, Units.val_mul, Matrix.det_mul, norm_mul, hk.1, mul_one]
  · rw [archComponent_archGLIncl_of_ne F h, mul_one]

private theorem N_archEntries_mul_right (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    N F (archEntries F (y * archGLIncl F w k)) = N F (archEntries F y) := by
  rw [N_archEntries, N_archEntries]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul]
  by_cases h : v = w
  · subst h
    rw [archComponent_archGLIncl_self]
    exact HS_mul_rowIsometry _ k hk
  · rw [archComponent_archGLIncl_of_ne F h, mul_one]

private theorem PD_archEntries_mul_right (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    PD F (archEntries F (y * archGLIncl F w k)) = PD F (archEntries F y) := by
  unfold PD
  simp only [norm_detE_fst, norm_detE_snd, norm_det_archComponent_mul_right w k hk y]

end Bridges
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

section Plateau

private def θup (R t : ℝ) : ℝ := Real.smoothTransition (R + 1 - t)

private def θlow (ε t : ℝ) : ℝ := Real.smoothTransition (2 / ε * t - 1)

private theorem contDiff_θup (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (θup R) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

private theorem contDiff_θlow (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (θlow ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

private theorem θup_eq_one {R t : ℝ} (h : t ≤ R) : θup R t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem θup_eq_zero {R t : ℝ} (h : R + 1 ≤ t) : θup R t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem θlow_eq_one {ε t : ℝ} (hε : 0 < ε) (h : ε ≤ t) : θlow ε t = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have : 2 / ε * t ≥ 2 / ε * ε := mul_le_mul_of_nonneg_left h (by positivity)
  have h2 : 2 / ε * ε = 2 := by field_simp
  linarith

private theorem θlow_eq_zero {ε t : ℝ} (hε : 0 < ε) (h : t ≤ ε / 2) : θlow ε t = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have : 2 / ε * t ≤ 2 / ε * (ε / 2) := mul_le_mul_of_nonneg_left h (by positivity)
  have h2 : 2 / ε * (ε / 2) = 1 := by field_simp
  linarith

variable (F : Type) [Field F] [NumberField F]

private def plateau (R ε : ℝ) (M : E F) : ℝ := θup R (N F M) * θlow ε (PD F M)

private theorem contDiff_plateau (R ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (plateau F R ε) :=
  ((contDiff_θup R).comp (contDiff_N F)).mul ((contDiff_θlow ε).comp (contDiff_PD F))

private theorem plateau_eq_one {R ε : ℝ} (hε : 0 < ε) {M : E F} (hN : N F M ≤ R) (hP : ε ≤ PD F M) :
    plateau F R ε M = 1 := by
  rw [plateau, θup_eq_one hN, θlow_eq_one hε hP, one_mul]

private theorem N_lt_of_plateau_ne_zero {R ε : ℝ} {M : E F} (h : plateau F R ε M ≠ 0) : N F M < R + 1 := by
  by_contra hc
  exact h (by rw [plateau, θup_eq_zero (not_lt.mp hc), zero_mul])

private theorem PD_gt_of_plateau_ne_zero {R ε : ℝ} (hε : 0 < ε) {M : E F} (h : plateau F R ε M ≠ 0) :
    ε / 2 < PD F M := by
  by_contra hc
  exact h (by rw [plateau, θlow_eq_zero hε (not_lt.mp hc), mul_zero])

private def ZE (R ε : ℝ) : Set (E F) := {M | N F M ≤ R + 1 ∧ ε / 2 ≤ PD F M}

private theorem plateau_ne_zero_subset_ZE (R ε : ℝ) (hε : 0 < ε) :
    {M : E F | plateau F R ε M ≠ 0} ⊆ ZE F R ε := fun _ h =>
  ⟨(N_lt_of_plateau_ne_zero F h).le, (PD_gt_of_plateau_ne_zero F hε h).le⟩

private theorem isClosed_ZE (R ε : ℝ) : IsClosed (ZE F R ε) :=
  (isClosed_le (contDiff_N F).continuous continuous_const).inter
    (isClosed_le continuous_const (contDiff_PD F).continuous)

private theorem isCompact_ZE (R ε : ℝ) : IsCompact (ZE F R ε) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_ZE F R ε)
    ((Metric.isBounded_closedBall (x := (0 : E F)) (r := Real.sqrt (R + 1))).subset fun M hM => ?_)
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_sqrt_N F M).trans (Real.sqrt_le_sqrt hM.1)

private theorem isUnit_detE_of_mem_ZE {R ε : ℝ} (hε : 0 < ε) {M : E F} (hM : M ∈ ZE F R ε) :
    IsUnit (detE F M) :=
  isUnit_detE_of_PD_ne_zero F (lt_of_lt_of_le (half_pos hε) hM.2).ne'

private theorem plateau_archEntries_mul (R ε : ℝ) (w : InfinitePlace F) (k : GL (Fin 2) w.Completion)
    (hk : IsRowIsometry k) (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    plateau F R ε (archEntries F (archGLIncl F w k * y)) = plateau F R ε (archEntries F y) := by
  rw [plateau, plateau, N_archEntries_mul w k hk, PD_archEntries_mul w k hk]

private theorem plateau_archEntries_mul_right (R ε : ℝ) (w : InfinitePlace F) (k : GL (Fin 2) w.Completion)
    (hk : IsRowIsometry k) (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    plateau F R ε (archEntries F (y * archGLIncl F w k)) = plateau F R ε (archEntries F y) := by
  rw [plateau, plateau, N_archEntries_mul_right w k hk, PD_archEntries_mul_right w k hk]

end Plateau
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

section Topology

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
private theorem continuous_ringEquiv_mixedSpace : Continuous (ringEquiv_mixedSpace F) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

omit [NumberField F] in
private theorem continuous_ringEquiv_mixedSpace_symm : Continuous (ringEquiv_mixedSpace F).symm := by
  apply continuous_pi
  intro v
  by_cases hv : IsReal v
  · have key : (fun y : mixedEmbedding.mixedSpace F => (ringEquiv_mixedSpace F).symm y v)
        = fun y => (isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace F => z.1 ⟨v, hv⟩)
        ((ringEquiv_mixedSpace F).apply_symm_apply y)
    rw [key]
    exact (isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : IsComplex v := not_isReal_iff_isComplex.1 hv
    have key : (fun y : mixedEmbedding.mixedSpace F => (ringEquiv_mixedSpace F).symm y v)
        = fun y => (isometryEquivComplexOfIsComplex hc).symm (y.2 ⟨v, hc⟩) := by
      funext y
      apply (isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace F => z.2 ⟨v, hc⟩)
        ((ringEquiv_mixedSpace F).apply_symm_apply y)
    rw [key]
    exact (isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

omit [NumberField F] in
private def mixedHomeo : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F where
  toEquiv := (ringEquiv_mixedSpace F).toEquiv
  continuous_toFun := continuous_ringEquiv_mixedSpace F
  continuous_invFun := continuous_ringEquiv_mixedSpace_symm F

omit [NumberField F] in
private def matHomeo : (Fin 2 → Fin 2 → InfiniteAdeleRing F) ≃ₜ E F :=
  Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => mixedHomeo F

omit [NumberField F] in
private def pairHomeo :
    (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) × (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))ᵐᵒᵖ)
      ≃ₜ (E F × E F) :=
  Homeomorph.prodCongr (matHomeo F) (MulOpposite.opHomeomorph.symm.trans (matHomeo F))

omit [NumberField F] in
private def J (g : GL (Fin 2) (InfiniteAdeleRing F)) : E F × E F :=
  pairHomeo F (Units.embedProduct _ g)

omit [NumberField F] in
private theorem J_apply (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    J F g = (archEntries F g, archEntries F g⁻¹) := rfl

omit [NumberField F] in
private theorem isClosedEmbedding_J : IsClosedEmbedding (J F) :=
  (pairHomeo F).isClosedEmbedding.comp Units.isClosedEmbedding_embedProduct

omit [NumberField F] in
private theorem continuous_archEntries : Continuous (archEntries F) := by
  have : archEntries F = fun g => (J F g).1 := funext fun g => rfl
  rw [this]
  exact continuous_fst.comp (isClosedEmbedding_J F).continuous

private def Ψinv (m : E F) : E F :=
  fun i j => (Ring.inverse (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) •
    Matrix.adjugate (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) i j

omit [NumberField F] in
private theorem Ψinv_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    Ψinv F (archEntries F g) = archEntries F g⁻¹ := by
  set A := (ringEquiv_mixedSpace F).toRingHom.mapMatrix
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) with hA
  have hAinv : (ringEquiv_mixedSpace F).toRingHom.mapMatrix
      ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = A⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [hA, ← map_mul, Units.inv_mul, map_one]
  have h1 : (archEntries F g⁻¹ : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) = A⁻¹ := by
    rw [archEntries_eq_mapMatrix, hAinv]
  funext i j
  show (Ring.inverse (Matrix.det (archEntries F g : Matrix (Fin 2) (Fin 2) _)) •
      Matrix.adjugate (archEntries F g : Matrix (Fin 2) (Fin 2) _)) i j = archEntries F g⁻¹ i j
  have h2 : archEntries F g⁻¹ i j = (archEntries F g⁻¹ : Matrix (Fin 2) (Fin 2) _) i j := rfl
  rw [h2, h1, archEntries_eq_mapMatrix, ← hA, Matrix.inv_def]

private theorem continuousOn_Ψinv {R ε : ℝ} (hε : 0 < ε) : ContinuousOn (Ψinv F) (ZE F R ε) := by
  intro m hm
  have hunit : IsUnit (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) := by
    rw [← detE_eq_det]
    exact isUnit_detE_of_mem_ZE F hε hm
  obtain ⟨u, hu⟩ := hunit
  apply ContinuousAt.continuousWithinAt
  have hdet : Continuous fun m : E F =>
      Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) :=
    Continuous.matrix_det continuous_id
  have h1 : ContinuousAt (fun m : E F =>
      Ring.inverse (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)))) m := by
    have hi : ContinuousAt Ring.inverse
        (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) :=
      hu ▸ NormedRing.inverse_continuousAt u
    exact hi.comp hdet.continuousAt
  have h2 : Continuous fun m : E F =>
      Matrix.adjugate (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) :=
    Continuous.matrix_adjugate continuous_id
  rw [continuousAt_pi]
  intro i
  rw [continuousAt_pi]
  intro j
  have h3 : ContinuousAt (fun m : E F =>
      Ring.inverse (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) *
        Matrix.adjugate (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) i j) m :=
    h1.mul (h2.matrix_elem i j).continuousAt
  have e : (fun y : E F => Ψinv F y i j) = fun m : E F =>
      Ring.inverse (Matrix.det (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) *
        Matrix.adjugate (m : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) i j := by
    funext y
    simp only [Ψinv, Matrix.smul_apply, smul_eq_mul]
  rw [e]
  exact h3

private theorem hasCompactSupport_of_plateau {R ε : ℝ} (hε : 0 < ε)
    (f : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hf : ∀ y, plateau F R ε (archEntries F y) = 0 → f y = 0) : HasCompactSupport f := by
  set T : Set (E F × E F) := ZE F R ε ×ˢ (Ψinv F '' ZE F R ε) with hT
  have hTc : IsCompact T :=
    (isCompact_ZE F R ε).prod ((isCompact_ZE F R ε).image_of_continuousOn (continuousOn_Ψinv F hε))
  have hpre : IsCompact (J F ⁻¹' T) := (isClosedEmbedding_J F).isCompact_preimage hTc
  refine HasCompactSupport.intro' hpre (hTc.isClosed.preimage (isClosedEmbedding_J F).continuous) ?_
  intro y hy
  apply hf
  by_contra hne
  apply hy
  have hZ : archEntries F y ∈ ZE F R ε := plateau_ne_zero_subset_ZE F R ε hε hne
  show J F y ∈ T
  rw [J_apply, hT, Set.mem_prod]
  exact ⟨hZ, ⟨archEntries F y, hZ, Ψinv_archEntries F y⟩⟩

end Topology
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

section Parameters

variable (F : Type) [Field F] [NumberField F]

private theorem exists_R (C : Set (GL (Fin 2) (InfiniteAdeleRing F))) (hC : IsCompact C) :
    ∃ R : ℝ, ∀ y ∈ C, N F (archEntries F y) ≤ R := by
  obtain ⟨R, hR⟩ := hC.bddAbove_image
    (f := fun y => N F (archEntries F y)) ((contDiff_N F).continuous.comp (continuous_archEntries F)).continuousOn
  exact ⟨R, fun y hy => hR ⟨y, hy, rfl⟩⟩

private theorem exists_eps (C : Set (GL (Fin 2) (InfiniteAdeleRing F))) (hC : IsCompact C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ C, ε ≤ PD F (archEntries F y) := by
  by_cases hne : C.Nonempty
  · obtain ⟨y₀, hy₀, hmin⟩ := hC.exists_isMinOn hne
      ((contDiff_PD F).continuous.comp (continuous_archEntries F)).continuousOn
    exact ⟨PD F (archEntries F y₀), PD_archEntries_pos F y₀, fun y hy => hmin hy⟩
  · exact ⟨1, one_pos, fun y hy => (hne ⟨y, hy⟩).elim⟩

private theorem exists_plateau (C : Set (GL (Fin 2) (InfiniteAdeleRing F))) (hC : IsCompact C) :
    ∃ Ψ₀ : E F → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ₀ ∧ (∀ y ∈ C, Ψ₀ (archEntries F y) = 1) ∧
      (∀ (w : InfinitePlace F) (k : GL (Fin 2) w.Completion), IsRowIsometry k →
        ∀ y, Ψ₀ (archEntries F (archGLIncl F w k * y)) = Ψ₀ (archEntries F y)) ∧
      (∀ (w : InfinitePlace F) (k : GL (Fin 2) w.Completion), IsRowIsometry k →
        ∀ y, Ψ₀ (archEntries F (y * archGLIncl F w k)) = Ψ₀ (archEntries F y)) ∧
      (∀ f : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
        (∀ y, Ψ₀ (archEntries F y) = 0 → f y = 0) → HasCompactSupport f) ∧
      (∃ Kc : Set (E F), IsCompact Kc ∧ ∀ M, Ψ₀ M ≠ 0 → M ∈ Kc) := by
  obtain ⟨R, hR⟩ := exists_R F C hC
  obtain ⟨ε, hε, hP⟩ := exists_eps F C hC
  exact ⟨plateau F R ε, contDiff_plateau F R ε, fun y hy => plateau_eq_one F hε (hR y hy) (hP y hy),
    fun w k hk y => plateau_archEntries_mul F R ε w k hk y,
    fun w k hk y => plateau_archEntries_mul_right F R ε w k hk y,
    fun f hf => hasCompactSupport_of_plateau F hε f hf,
    ⟨ZE F R ε, isCompact_ZE F R ε, fun M hM => plateau_ne_zero_subset_ZE F R ε hε hM⟩⟩

end Parameters
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

end ArchFiniteVector.Plateau
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

end ModPlateau
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

section ModAssembly

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume

open scoped Classical

namespace ArchFiniteVector
namespace Assembly

section PinChecks
end PinChecks
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

variable (F : Type) [Field F] [NumberField F]

private abbrev E : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F

private def Lsub (A : E F) : E F →ₗ[ℝ] E F where
  toFun M := fun i j => ∑ l, A i l * M l j
  map_add' M M' := by
    funext i j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c M := by
    funext i j
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, mul_smul_comm]

omit [NumberField F] in
private theorem Lsub_apply (A M : E F) (i j : Fin 2) : Lsub F A M i j = ∑ l, A i l * M l j := rfl

omit [NumberField F] in
private theorem archEntries_mul (a z : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F (a * z) = Lsub F (archEntries F a) (archEntries F z) := by
  funext i j
  rw [Lsub_apply]
  simp only [archEntries_apply, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]

omit [NumberField F] in
private theorem isRowIsometry_coe_inv {w : InfinitePlace F} (k : rowIsometrySubgroup₀ w.Completion) :
    IsRowIsometry ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :=
  ((mem_rowIsometrySubgroup₀_iff w.Completion).mp (k⁻¹).2).2

private theorem glFin_inv_mul (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (y : AdelicGL2 (𝓞 F) F) :
    glFin (𝓞 F) F ((rowIsometryInclAt₀ F w k)⁻¹ * y) = glFin (𝓞 F) F y := by
  rw [map_mul, map_inv, glFin_rowIsometryInclAt₀, inv_one, one_mul]

private theorem glArch_inv_mul (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (y : AdelicGL2 (𝓞 F) F) :
    glArch (𝓞 F) F ((rowIsometryInclAt₀ F w k)⁻¹ * y) =
      archGLIncl F w ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) *
        glArch (𝓞 F) F y := by
  rw [map_mul, ← map_inv, glArch_rowIsometryInclAt₀]
  rfl

private def Tfix (r : AdelicGL2 (𝓞 F) F → ℂ) : (E F → ℝ) →ₗ[ℝ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun v := fun y => (v (archEntries F (glArch (𝓞 F) F y)) : ℂ) * r y
  map_add' v v' := by
    funext y
    simp only [Pi.add_apply, Complex.ofReal_add, add_mul]
  map_smul' c v := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Complex.real_smul,
      mul_assoc]

private theorem Tfix_apply (r : AdelicGL2 (𝓞 F) F → ℂ) (v : E F → ℝ) (y : AdelicGL2 (𝓞 F) F) :
    Tfix F r v y = (v (archEntries F (glArch (𝓞 F) F y)) : ℂ) * r y := rfl

private theorem Tfix_mem_span (r : AdelicGL2 (𝓞 F) F → ℂ) {n : ℕ} (b : Fin n → E F → ℝ) {v : E F → ℝ}
    (hv : v ∈ Submodule.span ℝ (Set.range b)) :
    Tfix F r v ∈ Submodule.span ℂ (Set.range fun i => Tfix F r (b i)) := by
  have h1 : Tfix F r v ∈ (Submodule.span ℝ (Set.range b)).map (Tfix F r) := Submodule.mem_map_of_mem hv
  rw [Submodule.map_span, ← Set.range_comp] at h1
  exact Submodule.span_le_restrictScalars ℝ ℂ _ h1

private theorem isArchTestFactor_mul_plateau (Ψ₀ : E F → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ₀)
    (hkill : ∀ f : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
      (∀ y, Ψ₀ (archEntries F y) = 0 → f y = 0) → HasCompactSupport f)
    (h : E F → ℂ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    IsArchTestFactor F (fun z => h (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ)) := by
  refine ⟨⟨fun M => h M * (Ψ₀ M : ℂ), hh.mul (Complex.ofRealCLM.contDiff.comp hΨ), fun _ => rfl⟩, ?_⟩
  exact hkill _ fun y hy => by simp only [hy, Complex.ofReal_zero, mul_zero]

private theorem contDiff_ofReal_comp {p : E F → ℝ} (hp : ContDiff ℝ (⊤ : ℕ∞) p) :
    ContDiff ℝ (⊤ : ℕ∞) fun M => (p M : ℂ) :=
  Complex.ofRealCLM.contDiff.comp hp

private theorem contDiff_pair {p q : E F → ℝ} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ContDiff ℝ (⊤ : ℕ∞) fun M => (p M : ℂ) + (q M : ℂ) * Complex.I :=
  (contDiff_ofReal_comp F hp).add ((contDiff_ofReal_comp F hq).mul contDiff_const)

private theorem continuous_and_hasCompactSupport_tensor (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : IsArchTestFactor F fa) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) :
    Continuous (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∧
      HasCompactSupport (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) :=
  continuous_and_hasCompactSupport_of_isFactorizableTestFn F _
    (ArchFiniteVector.ConvHalf.isFactorizableTestFn_mk F fa hfa ff hff)

section Translate

variable {F}
variable (Ψ₀ p q : E F → ℝ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)

private def rfun : AdelicGL2 (𝓞 F) F → ℂ :=
  fun y => (Ψ₀ (archEntries F (glArch (𝓞 F) F y)) : ℂ) * ff (glFin (𝓞 F) F y)

private def ffun : AdelicGL2 (𝓞 F) F → ℂ :=
  fun y => ((p (archEntries F (glArch (𝓞 F) F y)) : ℂ) +
      (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) * Complex.I) *
    (Ψ₀ (archEntries F (glArch (𝓞 F) F y)) : ℂ) * ff (glFin (𝓞 F) F y)

private theorem ffun_eq_tensor : ffun Ψ₀ p q ff = fun g =>
    (fun z => ((p (archEntries F z) : ℂ) + (q (archEntries F z) : ℂ) * Complex.I) *
      (Ψ₀ (archEntries F z) : ℂ)) (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g) := rfl

variable (hΨinv : ∀ (w : InfinitePlace F) (k : GL (Fin 2) w.Completion), IsRowIsometry k →
  ∀ y, Ψ₀ (archEntries F (archGLIncl F w k * y)) = Ψ₀ (archEntries F y))

include hΨinv in
private theorem ffun_translate (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 F) F) :
    ffun Ψ₀ p q ff ((rowIsometryInclAt₀ F w k)⁻¹ * y) =
      Tfix F (rfun Ψ₀ ff) (p ∘ Lsub F (archEntries F (archGLIncl F w
          ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)))) y +
        Complex.I * Tfix F (rfun Ψ₀ ff) (q ∘ Lsub F (archEntries F (archGLIncl F w
          ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)))) y := by
  rw [Tfix_apply, Tfix_apply]
  unfold ffun rfun
  rw [glFin_inv_mul, glArch_inv_mul, hΨinv w _ (isRowIsometry_coe_inv F k), archEntries_mul]
  simp only [Function.comp_apply]
  ring

include hΨinv in
private theorem ffun_translate_mem_span {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ)
    (hp : ∀ L : E F →ₗ[ℝ] E F, (p ∘ L) ∈ Submodule.span ℝ (Set.range bp))
    (hq : ∀ L : E F →ₗ[ℝ] E F, (q ∘ L) ∈ Submodule.span ℝ (Set.range bq))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    (fun y => ffun Ψ₀ p q ff ((rowIsometryInclAt₀ F w k)⁻¹ * y)) ∈
      Submodule.span ℂ (Set.range (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i))
        (fun j => Tfix F (rfun Ψ₀ ff) (bq j)))) := by
  have key : (fun y => ffun Ψ₀ p q ff ((rowIsometryInclAt₀ F w k)⁻¹ * y)) =
      Tfix F (rfun Ψ₀ ff) (p ∘ Lsub F (archEntries F (archGLIncl F w
          ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)))) +
        Complex.I • Tfix F (rfun Ψ₀ ff) (q ∘ Lsub F (archEntries F (archGLIncl F w
          ((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)))) := by
    funext y
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact ffun_translate Ψ₀ p q ff hΨinv w k y
  rw [key]
  have hl : Set.range (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) ⊆
      Set.range (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) (fun j => Tfix F (rfun Ψ₀ ff) (bq j))) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.castAdd m i, by rw [Fin.append_left]⟩
  have hr : Set.range (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) ⊆
      Set.range (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) (fun j => Tfix F (rfun Ψ₀ ff) (bq j))) := by
    rintro _ ⟨j, rfl⟩
    exact ⟨Fin.natAdd n j, by rw [Fin.append_right]⟩
  refine add_mem ?_ (Submodule.smul_mem _ _ ?_)
  · exact Submodule.span_mono hl (Tfix_mem_span F (rfun Ψ₀ ff) bp (hp _))
  · exact Submodule.span_mono hr (Tfix_mem_span F (rfun Ψ₀ ff) bq (hq _))

end Translate
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

private theorem rightConv_ffun_ne_zero (u₀ : AdelicGL2 (𝓞 F) F → ℂ) (hu₀ : Continuous u₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (Φ₀ : E F → ℂ) (hΦ₀ : ∀ z, fa₀ z = Φ₀ (archEntries F z))
    (hfa₀ : IsArchTestFactor F fa₀)
    (Ψ₀ : E F → ℝ) (hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ₀) (hΨ1 : ∀ z ∈ tsupport fa₀, Ψ₀ (archEntries F z) = 1)
    (hkill : ∀ f : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
      (∀ y, Ψ₀ (archEntries F y) = 0 → f y = 0) → HasCompactSupport f)
    (Kc : Set (E F)) (hKc : ∀ M, Ψ₀ M ≠ 0 → M ∈ Kc)
    (p q : E F → ℝ) (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (δ : ℝ)
    (hclose : ∀ M ∈ Kc, ‖((p M : ℂ) + (q M : ℂ) * Complex.I) - Φ₀ M‖ < δ)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hsmall : letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
      δ * ∫ y, ‖u₀ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) <
        ‖rightConv F u₀ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖) :
    rightConv F u₀ (ffun Ψ₀ p q ff) g₀ ≠ 0 := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  have hΨarch : IsArchTestFactor F
      (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ)) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill (fun _ => (1 : ℂ)) contDiff_const
  have hr := continuous_and_hasCompactSupport_tensor F _ hΨarch ff hff
  have hr_eq : (fun g => (fun z => (fun _ : E F => (1 : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ))
      (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) = rfun Ψ₀ ff := by
    funext g
    simp only [rfun, one_mul]
  rw [hr_eq] at hr
  have hfarch : IsArchTestFactor F (fun z => ((p (archEntries F z) : ℂ) + (q (archEntries F z) : ℂ) *
      Complex.I) * (Ψ₀ (archEntries F z) : ℂ)) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_pair F hp hq)
  have hf := continuous_and_hasCompactSupport_tensor F _ hfarch ff hff
  rw [← ffun_eq_tensor] at hf
  have hf₀ := continuous_and_hasCompactSupport_tensor F fa₀ hfa₀ ff hff
  have hint := ArchFiniteVector.KFinite.integrable_rightConv_integrand F u₀ hu₀ _ hf.1 hf.2 g₀
  have hint₀ := ArchFiniteVector.KFinite.integrable_rightConv_integrand F u₀ hu₀ _ hf₀.1 hf₀.2 g₀
  have hintr := ArchFiniteVector.KFinite.integrable_rightConv_integrand F u₀ hu₀ _ hr.1 hr.2 g₀
  have e1 : (fun y => u₀ (g₀ * y) * ffun Ψ₀ p q ff y) = fun y => u₀ (g₀ * y) *
      ((fun y => (p (archEntries F (glArch (𝓞 F) F y)) : ℂ) +
        (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) * Complex.I) y * rfun Ψ₀ ff y) := by
    funext y
    simp only [ffun, rfun]
    ring
  have e0 : (fun y => u₀ (g₀ * y) * (fa₀ (glArch (𝓞 F) F y) * ff (glFin (𝓞 F) F y))) = fun y => u₀ (g₀ * y) *
      (Φ₀ (archEntries F (glArch (𝓞 F) F y)) * rfun Ψ₀ ff y) := by
    funext y
    simp only [rfun]
    by_cases h0 : fa₀ (glArch (𝓞 F) F y) = 0
    · rw [h0, ← hΦ₀, h0]
      ring
    · rw [hΨ1 _ (subset_tsupport _ h0), ← hΦ₀]
      push_cast
      ring
  have hne : rightConv F u₀ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ =
      ∫ y, u₀ (g₀ * y) * (Φ₀ (archEntries F (glArch (𝓞 F) F y)) * rfun Ψ₀ ff y)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [rightConv_apply, ← e0]
  have hgoal : rightConv F u₀ (ffun Ψ₀ p q ff) g₀ =
      ∫ y, u₀ (g₀ * y) * ((fun y => (p (archEntries F (glArch (𝓞 F) F y)) : ℂ) +
        (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) * Complex.I) y * rfun Ψ₀ ff y)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [rightConv_apply, ← e1]
  rw [hgoal]
  refine ArchFiniteVector.Poly.integral_ne_zero_of_close (μ := adelicGLHaar (Fin 2) (𝓞 F) F)
    (w := fun y => u₀ (g₀ * y))
    (a := fun y => (p (archEntries F (glArch (𝓞 F) F y)) : ℂ) + (q (archEntries F (glArch (𝓞 F) F y)) : ℂ) *
      Complex.I) (a' := fun y => Φ₀ (archEntries F (glArch (𝓞 F) F y))) (r := rfun Ψ₀ ff) (δ := δ)
    (e1 ▸ hint) (e0 ▸ hint₀) ?_ ?_ ?_
  · simpa only [norm_mul] using hintr.norm
  · intro y hy
    have hΨne : Ψ₀ (archEntries F (glArch (𝓞 F) F y)) ≠ 0 := fun h0 => hy (by simp only [rfun, h0,
      Complex.ofReal_zero, zero_mul])
    exact (hclose _ (hKc _ hΨne)).le
  · have h := hsmall
    rw [hne] at h
    exact h

section BiFinite

private def Rsub (A : E F) : E F →ₗ[ℝ] E F where
  toFun M := fun i j => ∑ l, M i l * A l j
  map_add' M M' := by
    funext i j
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    funext i j
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_mul_assoc]

omit [NumberField F] in
private theorem Rsub_apply (A M : E F) (i j : Fin 2) : Rsub F A M i j = ∑ l, M i l * A l j := rfl

omit [NumberField F] in
private theorem archEntries_mul_right (z a : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F (z * a) = Rsub F (archEntries F a) (archEntries F z) := by
  funext i j
  rw [Rsub_apply]
  simp only [archEntries_apply, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]

section FactorTranslate

variable {F}

omit [NumberField F] in
private theorem isRowIsometry_coe {w : InfinitePlace F} (k : rowIsometrySubgroup₀ w.Completion) :
    IsRowIsometry (k : GL (Fin 2) w.Completion) :=
  ((mem_rowIsometrySubgroup₀_iff w.Completion).mp k.2).2

omit [NumberField F] in
private theorem archRowIsometryInclAt₀_eq (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    archRowIsometryInclAt₀ F w k = archGLIncl F w (k : GL (Fin 2) w.Completion) :=
  rfl

private def TfixA (r : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :
    (E F → ℝ) →ₗ[ℝ] (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) where
  toFun v := fun z => (v (archEntries F z) : ℂ) * r z
  map_add' v v' := by
    funext z
    simp only [Pi.add_apply, Complex.ofReal_add, add_mul]
  map_smul' c v := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Complex.real_smul,
      mul_assoc]

omit [NumberField F] in
private theorem TfixA_apply (r : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (v : E F → ℝ)
    (z : GL (Fin 2) (InfiniteAdeleRing F)) : TfixA r v z = (v (archEntries F z) : ℂ) * r z :=
  rfl

omit [NumberField F] in
private theorem TfixA_mem_span (r : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) {n : ℕ} (b : Fin n → E F → ℝ)
    {v : E F → ℝ} (hv : v ∈ Submodule.span ℝ (Set.range b)) :
    TfixA r v ∈ Submodule.span ℂ (Set.range fun i => TfixA r (b i)) := by
  have h1 : TfixA r v ∈ (Submodule.span ℝ (Set.range b)).map (TfixA r) := Submodule.mem_map_of_mem hv
  rw [Submodule.map_span, ← Set.range_comp] at h1
  exact Submodule.span_le_restrictScalars ℝ ℂ _ h1

variable (Ψ₀ p q : E F → ℝ)

private def rA : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun z => (Ψ₀ (archEntries F z) : ℂ)

private def afun : GL (Fin 2) (InfiniteAdeleRing F) → ℂ :=
  fun z => ((p (archEntries F z) : ℂ) + (q (archEntries F z) : ℂ) * Complex.I) * (Ψ₀ (archEntries F z) : ℂ)

private theorem ffun_eq_afun (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) :
    ffun Ψ₀ p q ff = fun g => afun Ψ₀ p q (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g) :=
  rfl

private def BA {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ) :
    Fin (n + m) → GL (Fin 2) (InfiniteAdeleRing F) → ℂ :=
  Fin.append (fun i => TfixA (rA Ψ₀) (bp i)) (fun j => TfixA (rA Ψ₀) (bq j))

private def BAinv {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ) :
    Fin (n + m) → GL (Fin 2) (InfiniteAdeleRing F) → ℂ :=
  fun i => fun x => BA Ψ₀ bp bq i x⁻¹

omit [NumberField F] in
private theorem mem_span_BA_of_eq {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ) {vp vq : E F → ℝ}
    (hvp : vp ∈ Submodule.span ℝ (Set.range bp)) (hvq : vq ∈ Submodule.span ℝ (Set.range bq))
    {g : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hg : ∀ z, g z = TfixA (rA Ψ₀) vp z + Complex.I * TfixA (rA Ψ₀) vq z) :
    g ∈ Submodule.span ℂ (Set.range (BA Ψ₀ bp bq)) := by
  have key : g = TfixA (rA Ψ₀) vp + Complex.I • TfixA (rA Ψ₀) vq := by
    funext z
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact hg z
  rw [key]
  have hl : Set.range (fun i => TfixA (rA Ψ₀) (bp i)) ⊆ Set.range (BA Ψ₀ bp bq) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨Fin.castAdd m i, ?_⟩
    unfold BA
    rw [Fin.append_left]
  have hr : Set.range (fun j => TfixA (rA Ψ₀) (bq j)) ⊆ Set.range (BA Ψ₀ bp bq) := by
    rintro _ ⟨j, rfl⟩
    refine ⟨Fin.natAdd n j, ?_⟩
    unfold BA
    rw [Fin.append_right]
  refine add_mem ?_ (Submodule.smul_mem _ _ ?_)
  · exact Submodule.span_mono hl (TfixA_mem_span (rA Ψ₀) bp hvp)
  · exact Submodule.span_mono hr (TfixA_mem_span (rA Ψ₀) bq hvq)

variable (hΨinv : ∀ (w : InfinitePlace F) (k : GL (Fin 2) w.Completion), IsRowIsometry k →
  ∀ y, Ψ₀ (archEntries F (archGLIncl F w k * y)) = Ψ₀ (archEntries F y))
variable (hΨinvR : ∀ (w : InfinitePlace F) (k : GL (Fin 2) w.Completion), IsRowIsometry k →
  ∀ y, Ψ₀ (archEntries F (y * archGLIncl F w k)) = Ψ₀ (archEntries F y))

omit [NumberField F] in
include hΨinv in
private theorem afun_mul_left (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (z : GL (Fin 2) (InfiniteAdeleRing F)) :
    afun Ψ₀ p q (archGLIncl F w k * z) =
      TfixA (rA Ψ₀) (p ∘ Lsub F (archEntries F (archGLIncl F w k))) z +
        Complex.I * TfixA (rA Ψ₀) (q ∘ Lsub F (archEntries F (archGLIncl F w k))) z := by
  rw [TfixA_apply, TfixA_apply]
  unfold afun rA
  rw [hΨinv w k hk z, archEntries_mul]
  simp only [Function.comp_apply]
  ring

omit [NumberField F] in
include hΨinvR in
private theorem afun_mul_right (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k)
    (z : GL (Fin 2) (InfiniteAdeleRing F)) :
    afun Ψ₀ p q (z * archGLIncl F w k) =
      TfixA (rA Ψ₀) (p ∘ Rsub F (archEntries F (archGLIncl F w k))) z +
        Complex.I * TfixA (rA Ψ₀) (q ∘ Rsub F (archEntries F (archGLIncl F w k))) z := by
  rw [TfixA_apply, TfixA_apply]
  unfold afun rA
  rw [hΨinvR w k hk z, archEntries_mul_right]
  simp only [Function.comp_apply]
  ring

omit [NumberField F] in
include hΨinv in
private theorem afun_mul_left_mem_span {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ)
    (hp : ∀ L : E F →ₗ[ℝ] E F, (p ∘ L) ∈ Submodule.span ℝ (Set.range bp))
    (hq : ∀ L : E F →ₗ[ℝ] E F, (q ∘ L) ∈ Submodule.span ℝ (Set.range bq))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    (fun z => afun Ψ₀ p q (archRowIsometryInclAt₀ F w k * z)) ∈ Submodule.span ℂ (Set.range (BA Ψ₀ bp bq)) :=
  mem_span_BA_of_eq Ψ₀ bp bq (hp _) (hq _) fun z => by
    rw [archRowIsometryInclAt₀_eq]
    exact afun_mul_left Ψ₀ p q hΨinv w _ (isRowIsometry_coe k) z

omit [NumberField F] in
include hΨinvR in
private theorem afun_mul_right_mem_span {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ)
    (hp : ∀ L : E F →ₗ[ℝ] E F, (p ∘ L) ∈ Submodule.span ℝ (Set.range bp))
    (hq : ∀ L : E F →ₗ[ℝ] E F, (q ∘ L) ∈ Submodule.span ℝ (Set.range bq))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    (fun z => afun Ψ₀ p q (z * archRowIsometryInclAt₀ F w k)) ∈ Submodule.span ℂ (Set.range (BA Ψ₀ bp bq)) :=
  mem_span_BA_of_eq Ψ₀ bp bq (hp _) (hq _) fun z => by
    rw [archRowIsometryInclAt₀_eq]
    exact afun_mul_right Ψ₀ p q hΨinvR w _ (isRowIsometry_coe k) z

omit [NumberField F] in
include hΨinv in
private theorem afun_inv_mul_mem_span {n m : ℕ} (bp : Fin n → E F → ℝ) (bq : Fin m → E F → ℝ)
    (hp : ∀ L : E F →ₗ[ℝ] E F, (p ∘ L) ∈ Submodule.span ℝ (Set.range bp))
    (hq : ∀ L : E F →ₗ[ℝ] E F, (q ∘ L) ∈ Submodule.span ℝ (Set.range bq))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    (fun x => afun Ψ₀ p q (x * archRowIsometryInclAt₀ F w k)⁻¹) ∈
      Submodule.span ℂ (Set.range (BAinv Ψ₀ bp bq)) := by
  have h := afun_mul_left_mem_span Ψ₀ p q hΨinv bp bq hp hq w k⁻¹
  have e : (fun x => afun Ψ₀ p q (x * archRowIsometryInclAt₀ F w k)⁻¹) =
      fun x => (fun z => afun Ψ₀ p q (archRowIsometryInclAt₀ F w k⁻¹ * z)) x⁻¹ := by
    funext x
    simp only [_root_.mul_inv_rev, map_inv]
  rw [e]
  exact ArchFiniteVector.ArchCut.comp_inv_mem_span (BA Ψ₀ bp bq) h

end FactorTranslate
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

omit [NumberField F] in
private theorem exists_archRepAt_of_translates (w : InfinitePlace F) (u : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (W : Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ k : rowIsometrySubgroup₀ w.Completion, (fun x => u (x * archRowIsometryInclAt₀ F w k)) ∈ W) :
    ∃ τ : ArchRepAt F w, u ∈ archFactorTypeSubmoduleAt F w τ := by
  obtain ⟨V, hfin, hu, hV⟩ :=
    ArchFiniteVector.ArchCut.exists_stable_of_translates_mem (archRowIsometryInclAt₀ F w) u W hW
  haveI := hfin
  obtain ⟨n, ρ, hmem⟩ := ArchFiniteVector.ArchCut.exists_rep_mem_typeSubmodule (archRowIsometryInclAt₀ F w) V hu hV
  exact ⟨⟨n, ρ⟩, hmem⟩

omit [NumberField F] in
private theorem exists_archRepAt_dual_of_translates (w : InfinitePlace F) (u : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (W : Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ k : rowIsometrySubgroup₀ w.Completion, (fun x => u (x * archRowIsometryInclAt₀ F w k)) ∈ W) :
    ∃ τ : ArchRepAt F w, u ∈ archFactorDualTypeSubmoduleAt F w τ := by
  obtain ⟨V, hfin, hu, hV⟩ :=
    ArchFiniteVector.ArchCut.exists_stable_of_translates_mem (archRowIsometryInclAt₀ F w) u W hW
  haveI := hfin
  obtain ⟨n, ρ, hmem⟩ :=
    ArchFiniteVector.ArchCut.exists_rep_mem_typeSubmodule_dual (archRowIsometryInclAt₀ F w) V hu hV
  exact ⟨⟨n, ρ⟩, hmem⟩

private def tripleFamily (τ₁ τ₂ τ₃ : ∀ w : InfinitePlace F, ArchRepAt F w) : ArchTypeFamily F where
  card := fun _ => 3
  rep := fun w => ![τ₁ w, τ₂ w, τ₃ w]

omit [NumberField F] in
private theorem mem_archFactorCut_tripleFamily (τ₁ τ₂ τ₃ : ∀ w : InfinitePlace F, ArchRepAt F w)
    {u : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : ∀ w, u ∈ archFactorTypeSubmoduleAt F w (τ₁ w)) :
    u ∈ archFactorCutSubmodule F (tripleFamily F τ₁ τ₂ τ₃) :=
  (Submodule.mem_iInf _).mpr fun w => Submodule.mem_iSup_of_mem (0 : Fin 3) (h w)

omit [NumberField F] in
private theorem mem_archFactorDualCut_tripleFamily (τ₁ τ₂ τ₃ : ∀ w : InfinitePlace F, ArchRepAt F w)
    {u : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : ∀ w, u ∈ archFactorDualTypeSubmoduleAt F w (τ₂ w)) :
    u ∈ archFactorDualCutSubmodule F (tripleFamily F τ₁ τ₂ τ₃) :=
  (Submodule.mem_iInf _).mpr fun w => Submodule.mem_iSup_of_mem (1 : Fin 3) (h w)

private theorem mem_archCut_tripleFamily (τ₁ τ₂ τ₃ : ∀ w : InfinitePlace F, ArchRepAt F w)
    {v : AdelicGL2 (𝓞 F) F → ℂ} (h : ∀ w, v ∈ archTypeSubmoduleAt F w (τ₃ w)) :
    v ∈ archCutSubmodule F (tripleFamily F τ₁ τ₂ τ₃) :=
  (Submodule.mem_iInf _).mpr fun w => Submodule.mem_iSup_of_mem (2 : Fin 3) (h w)

private theorem exists_archFiniteVector (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa₀ : IsArchTestFactor F fa₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ ≠ 0) :
    ∃ (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∈ archCutSubmodule F tys := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  obtain ⟨⟨Φ₀, hΦ₀, hfaΦ⟩, hfa₀c⟩ := id hfa₀
  obtain ⟨Ψ₀, hΨs, hΨ1, hΨinv, hΨinvR, hkill, Kc, hKc, hKcΨ⟩ :=
    ArchFiniteVector.Plateau.exists_plateau F (tsupport fa₀) hfa₀c
  obtain ⟨δ, hδpos, hsmall⟩ : ∃ δ : ℝ, 0 < δ ∧
      δ * (∫ y, ‖φ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) <
        ‖rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖ := by
    set M : ℝ := ∫ y, ‖φ (g₀ * y)‖ * ‖rfun Ψ₀ ff y‖ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
    set cc : ℝ := ‖rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀‖
    have hMnn : 0 ≤ M := integral_nonneg fun y => by positivity
    have hccpos : 0 < cc := norm_pos_iff.mpr hg₀
    have h2 : 0 < 2 * (M + 1) := by linarith
    refine ⟨cc / (2 * (M + 1)), div_pos hccpos h2, ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ h2]
    nlinarith
  obtain ⟨p, q, hp, hps, hq, hqs, hclose⟩ :=
    ArchFiniteVector.Poly.exists_poly_pair_near (E F) Kc hKc Φ₀ hΦ₀.continuous δ hδpos
  obtain ⟨n, bp, hbp, hpspan⟩ := hps.exists_smooth_span hp
  obtain ⟨m, bq, hbq, hqspan⟩ := hqs.exists_smooth_span hq
  have hfarch : IsArchTestFactor F (afun Ψ₀ p q) :=
    isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_pair F hp hq)
  have hune : rightConv F φ (fun g => afun Ψ₀ p q (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 := fun h0 =>
    rightConv_ffun_ne_zero F φ hφ ff hff fa₀ Φ₀ hfaΦ hfa₀ Ψ₀ hΨs hΨ1 hkill Kc hKcΨ p q hp hq δ hclose g₀ hsmall
      (by rw [ffun_eq_afun Ψ₀ p q ff, h0]; rfl)
  have hfs : ∀ i, Continuous (Fin.append (fun i => Tfix F (rfun Ψ₀ ff) (bp i))
      (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) i) ∧ HasCompactSupport (Fin.append
        (fun i => Tfix F (rfun Ψ₀ ff) (bp i)) (fun j => Tfix F (rfun Ψ₀ ff) (bq j)) i) := by
    have key : ∀ (b : E F → ℝ), ContDiff ℝ (⊤ : ℕ∞) b →
        Continuous (Tfix F (rfun Ψ₀ ff) b) ∧ HasCompactSupport (Tfix F (rfun Ψ₀ ff) b) := by
      intro b hb
      have harch : IsArchTestFactor F (fun z => (fun M => (b M : ℂ)) (archEntries F z) *
          (Ψ₀ (archEntries F z) : ℂ)) :=
        isArchTestFactor_mul_plateau F Ψ₀ hΨs hkill _ (contDiff_ofReal_comp F hb)
      have h := continuous_and_hasCompactSupport_tensor F _ harch ff hff
      have e : (fun g => (fun z => (fun M => (b M : ℂ)) (archEntries F z) * (Ψ₀ (archEntries F z) : ℂ))
          (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) = Tfix F (rfun Ψ₀ ff) b := by
        funext g
        rw [Tfix_apply]
        simp only [rfun]
        ring
      rw [e] at h
      exact h
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact key _ (hbp i)
    · rw [Fin.append_right]
      exact key _ (hbq j)
  have hV : ∀ w : InfinitePlace F, ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ V ∧ rightConv F φ (ffun Ψ₀ p q ff) ∈ V ∧
        ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ v ∈ V, (fun x => v (x * rowIsometryInclAt₀ F w k)) ∈ V :=
    fun w => ArchFiniteVector.KFinite.exists_finiteDimensional_mem_of_forall_mem_span F (rowIsometryInclAt₀ F w) φ
      hφ _ (fun i => (hfs i).1) (fun i => (hfs i).2) (ffun Ψ₀ p q ff)
      (ffun_translate_mem_span Ψ₀ p q ff hΨinv bp bq hpspan hqspan w)
  have hτ₃ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w,
      rightConv F φ (ffun Ψ₀ p q ff) ∈ archTypeSubmoduleAt F w τ := by
    intro w
    obtain ⟨V, hfin, hu, hstab⟩ := hV w
    haveI := hfin
    obtain ⟨n', ρ, hmem⟩ :=
      ArchFiniteVector.ArchCut.exists_rep_mem_typeSubmodule (rowIsometryInclAt₀ F w) V hu hstab
    exact ⟨⟨n', ρ⟩, hmem⟩
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (BA Ψ₀ bp bq))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (BAinv Ψ₀ bp bq))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hτ₂ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w, afun Ψ₀ p q ∈ archFactorDualTypeSubmoduleAt F w τ :=
    fun w => exists_archRepAt_dual_of_translates F w (afun Ψ₀ p q) _
      (fun k => afun_mul_right_mem_span Ψ₀ p q hΨinvR bp bq hpspan hqspan w k)
  have hτ₁ : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w,
      (fun x => afun Ψ₀ p q x⁻¹) ∈ archFactorTypeSubmoduleAt F w τ :=
    fun w => exists_archRepAt_of_translates F w (fun x => afun Ψ₀ p q x⁻¹) _
      (fun k => afun_inv_mul_mem_span Ψ₀ p q hΨinv bp bq hpspan hqspan w k)
  choose τ₁ hτ₁ using hτ₁
  choose τ₂ hτ₂ using hτ₂
  choose τ₃ hτ₃ using hτ₃
  refine ⟨tripleFamily F τ₁ τ₂ τ₃, afun Ψ₀ p q, hfarch,
    ⟨mem_archFactorCut_tripleFamily F τ₁ τ₂ τ₃ hτ₁, mem_archFactorDualCut_tripleFamily F τ₁ τ₂ τ₃ hτ₂⟩, hune, ?_⟩
  have h3 := mem_archCut_tripleFamily F τ₁ τ₂ τ₃ hτ₃
  rwa [ffun_eq_afun] at h3

end BiFinite
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

end ArchFiniteVector.Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

end ModAssembly
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

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

private theorem isIsotypicCuspFormAt_rightConv_of_memLp (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : IsFactorizableTestFn ℚ f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
      glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k)
    (hmem : letI : MeasurableSpace (AdelicGL2 (𝓞 ℚ) ℚ) := glBorel (Fin 2) (𝓞 ℚ) ℚ
      MemLp (rightConv ℚ R.toFun f) 2
        ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))) :
    IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      R.centralChar Φ.level R.exceptionalSet Φ (rightConv ℚ R.toFun f) := by
  obtain ⟨hcusp, hkf, hlev, hhecke⟩ :=
    AutomorphicForm.isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
      ℚ c u d₁ d₂ T Φ.toRawCentral R hR f hf hfs
  have hcont : Continuous (rightConv ℚ R.toFun f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn ℚ R.toFun hR f hf).1
  have hauto : IsAutomorphicFnAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      R.centralChar R.toFun := R.smoothCusp.1.1
  have hlsxi : IsLsXiFunction (𝓞 ℚ) ℚ ⊤ R.centralChar R.toFun :=
    ((@lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ _ _ _ (glBorel (Fin 2) (𝓞 ℚ) ℚ) (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) ⊤ R.centralChar
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) R.toFun).mp hauto).1
  have hauto' : IsAutomorphicFnAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      R.centralChar (rightConv ℚ R.toFun f) :=
    (@lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ _ _ _ (glBorel (Fin 2) (𝓞 ℚ) ℚ) (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) ⊤ R.centralChar
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) (rightConv ℚ R.toFun f)).mpr
      ⟨SmwShell.isLsXiFunction_rightConv_of_isLsXiFunction ℚ ⊤ R.centralChar hlsxi f, hmem⟩
  exact ⟨⟨⟨hauto', hcusp⟩, hkf⟩, hcont, hlev, hhecke,
    fun v hv g => SmwShell.rightConv_mul_left_of_forall_mul ℚ (fun x => R.central_eigen v hv x) g⟩

private theorem exists_finFactor_forall_isIsotypicCuspFormAt_rightConv (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (hR : Continuous R.toFun)
    (f₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf₀ : IsFactorizableTestFn ℚ f₀) (hne : ∃ y₀, f₀ y₀ ≠ 0)
    (hsupp : ∀ x, f₀ x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
      glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) :
    ∃ (fa₀ : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ),
      IsArchTestFactor ℚ fa₀ ∧ IsFinTestFactor ℚ ff ∧
        (∀ g, f₀ g = fa₀ (glArch (𝓞 ℚ) ℚ g) * ff (glFin (𝓞 ℚ) ℚ g)) ∧
        ∀ fa : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ, IsArchTestFactor ℚ fa →
          IsIsotypicCuspFormAt ℚ
            (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
            R.centralChar Φ.level R.exceptionalSet Φ
            (rightConv ℚ R.toFun (fun g => fa (glArch (𝓞 ℚ) ℚ g) * ff (glFin (𝓞 ℚ) ℚ g))) := by
  obtain ⟨fa₀, ff, hfa₀, hff, hf₀eq⟩ := hf₀
  refine ⟨fa₀, ff, hfa₀, hff, hf₀eq, fun fa hfa => ?_⟩
  have hf : IsFactorizableTestFn ℚ (fun g => fa (glArch (𝓞 ℚ) ℚ g) * ff (glFin (𝓞 ℚ) ℚ g)) :=
    ArchFiniteVector.ConvHalf.isFactorizableTestFn_mk ℚ fa hfa ff hff
  have hfs := support_shape_of_finFactor ℚ Φ.level f₀ fa₀ ff hf₀eq hne hsupp _ fa (fun _ => rfl)
  exact isIsotypicCuspFormAt_rightConv_of_memLp c u d₁ d₂ T Φ R hR _ hf hfs
    (SmwShell.memLp_rightConv_window_rat c u d₁ d₂ T hd hcov Φ R hR _ hf)

end G1PrimeRat.ConvHalf
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

end ModConvHalfR
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

section ModMain

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

namespace G1PrimeRat
namespace Main

private theorem main (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (tys : ArchTypeFamily ℚ) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      R.exceptionalSet ⊆ S ∧ IsFactorizableTestFn ℚ f ∧ IsArchBiFinite ℚ tys f ∧
        rightConv ℚ R.toFun f ≠ 0 ∧
        rightConv ℚ R.toFun f ∈ isotypicCuspSubmodule ℚ
          (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
          R.centralChar Φ.level S Φ ∧
        rightConv ℚ R.toFun f ∈ archCutSubmodule ℚ tys := by
  obtain ⟨f₀, hf₀, -, hsupp, g₀, hg₀⟩ :=
    AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant ℚ Φ.level Φ.level_ne_bot
      R.toFun hR R.exists_ne_zero R.level_invariant
  have hne : ∃ y₀, f₀ y₀ ≠ 0 := G1PrimeRat.ConvHalf.exists_ne_zero_of_rightConv_ne_zero ℚ R.toFun f₀ ⟨g₀, hg₀⟩
  obtain ⟨fa₀, ff, hfa₀, hff, hf₀eq, hiso⟩ :=
    G1PrimeRat.ConvHalf.exists_finFactor_forall_isIsotypicCuspFormAt_rightConv c u d₁ d₂ T hd hcov Φ R hR f₀ hf₀
      hne hsupp
  have hg₀' : rightConv ℚ R.toFun (fun g => fa₀ (glArch (𝓞 ℚ) ℚ g) * ff (glFin (𝓞 ℚ) ℚ g)) g₀ ≠ 0 := by
    have e : (fun g => fa₀ (glArch (𝓞 ℚ) ℚ g) * ff (glFin (𝓞 ℚ) ℚ g)) = f₀ := funext fun g => (hf₀eq g).symm
    rw [e]
    exact hg₀
  obtain ⟨tys, fa, hfa, hbi, hne', hcut⟩ :=
    ArchFiniteVector.Assembly.exists_archFiniteVector ℚ R.toFun hR fa₀ hfa₀ ff hff g₀ hg₀'
  exact ⟨R.exceptionalSet, tys, fun g => fa (glArch (𝓞 ℚ) ℚ g) * ff (glFin (𝓞 ℚ) ℚ g), Finset.Subset.refl _,
    ArchFiniteVector.ConvHalf.isFactorizableTestFn_mk ℚ fa hfa ff hff,
    IsArchBiFinite.of_factorization ℚ (fun _ => rfl) hbi, hne', (hiso fa hfa).mem_isotypicCuspSubmodule, hcut⟩

end G1PrimeRat.Main
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

end ModMain
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (_hd : d₁ < d₂) (_hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (tys : ArchTypeFamily ℚ) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      R.exceptionalSet ⊆ S ∧ IsFactorizableTestFn ℚ f ∧ IsArchBiFinite ℚ tys f ∧
        rightConv ℚ R.toFun f ≠ 0 ∧
        rightConv ℚ R.toFun f ∈ isotypicCuspSubmodule ℚ
          (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
            (adelicBox ℚ))
          R.centralChar Φ.level S Φ ∧
        rightConv ℚ R.toFun f ∈ archCutSubmodule ℚ tys :=
  G1PrimeRat.Main.main c u d₁ d₂ T _hd _hcov Φ R hR

end
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.ArchFiniteVector.Poly"

end S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule
end P2MW
export P2MW.S_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule (solution)
