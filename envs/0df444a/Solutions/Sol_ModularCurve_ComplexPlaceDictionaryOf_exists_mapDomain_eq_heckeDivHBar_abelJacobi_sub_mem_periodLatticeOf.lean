-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionaryOf.exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4a9931a2-378c-5597-ba0a-4685a6e04f1e

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_PeriodOf
import Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_GammaH
import Theorems.Thm_ModularForm_heckeU_add_slash_slash_eq_self_of_mem_GammaH
import Theorems.Thm_CuspForm_stableT
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_heckeDivHBar_single_pt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Manifold Topology
open UpperHalfPlane

namespace ModularCurve
p2m_export "ModularCurve" "ComplexPlaceDictionaryOf laurentBaseChange HeckeBetaHDefined HeckeAlphaHBarIntegral HeckeBetaHBarIntegral heckeDivHBar translation_mem_GammaH xHFunctionField xHTopFunctionFieldC periodAlongOf periodAlongOf_apply periodOf periodLatticeOf periodOf_mem_periodLatticeOf clamp01 clamp01_of_mem segmentPoint continuous_segmentPoint segmentPath continuous_segmentPath periodAlong period JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ComplexPlaceDictionaryOf.heckeDivHBar_single_pt"
p2m_open "ModularCurve"

namespace PeriodLatticeHStableProof

def IsPrimitive (h : ℍ → ℂ) (G : ℂ → ℂ) : Prop :=
  ∀ τ : ℍ, HasDerivAt G (h τ) (τ : ℂ)

theorem IsPrimitive.add {h₁ h₂ : ℍ → ℂ} {G₁ G₂ : ℂ → ℂ} (h1 : IsPrimitive h₁ G₁)
    (h2 : IsPrimitive h₂ G₂) : IsPrimitive (h₁ + h₂) (G₁ + G₂) :=
  fun τ => (h1 τ).add (h2 τ)

theorem IsPrimitive.sum {ι : Type*} (s : Finset ι) {h : ι → ℍ → ℂ} {G : ι → ℂ → ℂ}
    (hG : ∀ i ∈ s, IsPrimitive (h i) (G i)) :
    IsPrimitive (∑ i ∈ s, h i) (fun z => ∑ i ∈ s, G i z) := by
  intro τ
  have h' : (fun z => ∑ i ∈ s, G i z) = ∑ i ∈ s, G i := by
    ext z; simp [Finset.sum_apply]
  have := HasDerivAt.sum (u := s) (A := G) (A' := fun i => h i τ) (x := (τ : ℂ))
    (fun i hi => hG i hi τ)
  rw [h']
  simpa [Finset.sum_apply] using this

theorem IsPrimitive.exists_const {h : ℍ → ℂ} {G G' : ℂ → ℂ} (hG : IsPrimitive h G)
    (hG' : IsPrimitive h G') : ∃ a : ℂ, ∀ τ : ℍ, G τ = G' τ + a := by
  obtain ⟨a, ha⟩ := isOpen_upperHalfPlaneSet.exists_eq_add_of_deriv_eq
    (convex_halfSpace_im_gt 0).isPreconnected
    (fun z hz => (hG ⟨z, hz⟩).differentiableAt.differentiableWithinAt)
    (fun z hz => (hG' ⟨z, hz⟩).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hG ⟨z, hz⟩).deriv, (hG' ⟨z, hz⟩).deriv])
  exact ⟨a, fun τ => ha τ.im_pos⟩

theorem exists_isPrimitive {h : ℍ → ℂ} (hh : MDiff h) : ∃ G : ℂ → ℂ, IsPrimitive h G := by
  have hF : DifferentiableOn ℂ (h ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hh

  let r : ℕ → ℝ := fun n => (n : ℝ) + 1
  let c : ℕ → ℂ := fun n => (r n : ℂ) * Complex.I
  have hr : ∀ n, 0 < r n := fun n => by positivity
  have hc_im : ∀ n, (c n).im = r n := fun n => by simp [c]
  have hc_re : ∀ n, (c n).re = 0 := fun n => by simp [c]
  have hsub : ∀ n, Metric.ball (c n) (r n) ⊆ {z : ℂ | 0 < z.im} := by
    intro n z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have h1 : |(z - c n).im| ≤ ‖z - c n‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hc_im] at h1
    have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hz)).1
    show 0 < z.im
    linarith
  have hI : ∀ n, Complex.I ∈ Metric.ball (c n) (r n) := by
    intro n
    rw [Metric.mem_ball, Complex.dist_eq]
    have : Complex.I - c n = ((1 - r n : ℝ) : ℂ) * Complex.I := by
      simp only [c]; push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    simp only [r]
    rw [abs_lt]; constructor <;> linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hcover : ∀ z : ℂ, 0 < z.im → ∃ n : ℕ, z ∈ Metric.ball (c n) (r n) := by
    intro z hz
    obtain ⟨n, hn⟩ := exists_nat_gt (‖z‖ ^ 2 / (2 * z.im))
    refine ⟨n, ?_⟩
    rw [Metric.mem_ball, Complex.dist_eq]
    have hn' : ‖z‖ ^ 2 / (2 * z.im) < r n := lt_of_lt_of_le hn (by simp [r])
    have h2 : ‖z‖ ^ 2 < 2 * z.im * r n := by
      rwa [div_lt_iff₀ (by positivity), mul_comm] at hn'
    have hsq : ‖z - c n‖ ^ 2 = ‖z‖ ^ 2 - 2 * z.im * r n + r n ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
        Complex.sub_re, Complex.sub_im, hc_re, hc_im]
      ring
    have h3 : ‖z - c n‖ ^ 2 < r n ^ 2 := by rw [hsq]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (hr n).le h3
  have hmono : ∀ {n m : ℕ}, n ≤ m → Metric.ball (c n) (r n) ⊆ Metric.ball (c m) (r m) := by
    intro n m hnm z hz
    rw [Metric.mem_ball] at hz ⊢
    have hd : dist (c n) (c m) = r m - r n := by
      rw [Complex.dist_eq]
      have : c n - c m = ((r n - r m : ℝ) : ℂ) * Complex.I := by
        simp only [c]; push_cast; ring
      rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
        abs_sub_comm, abs_of_nonneg]
      simp only [r]; linarith [(Nat.cast_le.mpr hnm : (n : ℝ) ≤ m)]
    calc dist z (c m) ≤ dist z (c n) + dist (c n) (c m) := dist_triangle _ _ _
      _ < r n + (r m - r n) := by rw [hd]; linarith
      _ = r m := by ring

  have hex : ∀ n, ∃ g : ℂ → ℂ, g Complex.I = 0 ∧
      ∀ z ∈ Metric.ball (c n) (r n), HasDerivAt g ((h ∘ ofComplex) z) z :=
    fun n => ((hF.mono (hsub n)).isExactOn_ball).with_val_at Complex.I 0
  choose g hg0 hg using hex
  have hagree : ∀ {n m : ℕ}, n ≤ m → Set.EqOn (g n) (g m) (Metric.ball (c n) (r n)) := by
    intro n m hnm
    refine Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected ?_ ?_ ?_ (hI n) ?_
    · exact fun z hz => (hg n z hz).differentiableAt.differentiableWithinAt
    · exact fun z hz => (hg m z (hmono hnm hz)).differentiableAt.differentiableWithinAt
    · exact fun z hz => by rw [(hg n z hz).deriv, (hg m z (hmono hnm hz)).deriv]
    · rw [hg0, hg0]
  classical
  let idx : ℂ → ℕ := fun z => if hz : 0 < z.im then Nat.find (hcover z hz) else 0
  have hidx : ∀ z : ℂ, (hz : 0 < z.im) → z ∈ Metric.ball (c (idx z)) (r (idx z)) := by
    intro z hz
    simp only [idx, dif_pos hz]
    exact Nat.find_spec (hcover z hz)
  refine ⟨fun z => g (idx z) z, fun τ => ?_⟩
  have hτ := hidx τ τ.im_pos
  have key : (fun z => g (idx z) z) =ᶠ[𝓝 (τ : ℂ)] g (idx τ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hτ] with w hw
    have hw' : 0 < w.im := hsub _ hw
    rcases le_total (idx w) (idx (τ : ℂ)) with hle | hle
    · exact hagree hle (hidx w hw')
    · exact (hagree hle hw).symm
  have := (hg (idx (τ : ℂ)) τ hτ).congr_of_eventuallyEq key
  simpa [Function.comp, ofComplex_apply] using this

theorem IsPrimitive.integral_segment_eq {h : ℍ → ℂ} {G : ℂ → ℂ} (hG : IsPrimitive h G)
    (hc : Continuous h) (τ₀ τ₁ : ℍ) :
    ∫ t in (0 : ℝ)..1, h (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀) = G τ₁ - G τ₀ := by
  have h0 : segmentPoint τ₀ τ₁ 0 = τ₀ := by simp [segmentPoint, clamp01]
  have h1 : segmentPoint τ₀ τ₁ 1 = τ₁ := by simp [segmentPoint, clamp01]
  have hcontG : Continuous fun t => G (segmentPoint τ₀ τ₁ t) :=
    continuous_iff_continuousAt.mpr fun t =>
      ContinuousAt.comp (g := G) (f := segmentPoint τ₀ τ₁) (x := t)
        (hG (segmentPath τ₀ τ₁ t)).continuousAt (continuous_segmentPoint τ₀ τ₁).continuousAt
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun t => G (segmentPoint τ₀ τ₁ t)) (h (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) t := by
    intro t ht
    have hs : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have hlin : HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * (τ₀ : ℂ) + (s : ℂ) * τ₁)
        ((τ₁ : ℂ) - τ₀) t := by
      have := ((hs.const_sub 1).mul_const (τ₀ : ℂ)).add (hs.mul_const (τ₁ : ℂ))
      convert this using 1 <;> first | rfl | ring
    have heq : segmentPoint τ₀ τ₁ =ᶠ[𝓝 t] fun s : ℝ => (1 - (s : ℂ)) * (τ₀ : ℂ) + (s : ℂ) * τ₁ := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [segmentPoint, clamp01_of_mem (Set.Ioo_subset_Icc_self hs), Complex.real_smul,
        Complex.real_smul]
      push_cast
      ring
    have hseg : HasDerivAt (segmentPoint τ₀ τ₁) ((τ₁ : ℂ) - τ₀) t :=
      hlin.congr_of_eventuallyEq heq
    exact (hG (segmentPath τ₀ τ₁ t)).comp t hseg
  have hint : IntervalIntegrable (fun t => h (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀))
      MeasureTheory.volume 0 1 :=
    ((hc.comp (continuous_segmentPath τ₀ τ₁)).mul continuous_const).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcontG.continuousOn hderiv
    hint, h0, h1]

theorem IsPrimitive.slash_two {f : ℍ → ℂ} {G : ℂ → ℂ} (hG : IsPrimitive f G)
    {α : GL (Fin 2) ℝ} (hα : 0 < (α.det : ℝ)) :
    IsPrimitive (f ∣[(2 : ℤ)] α) (fun z => G (↑(α • ofComplex z))) := by
  have hα' : 0 < α.val.det := by rwa [Matrix.GeneralLinearGroup.val_det_apply] at hα
  intro τ
  have h1 : HasDerivAt (fun z : ℂ => ((α • ofComplex z : ℍ) : ℂ)) (↑(α.val.det) / denom α τ ^ 2) τ :=
    (hasStrictDerivAt_smul hα' τ).hasDerivAt
  have h2 : HasDerivAt G (f (α • τ)) ((fun z : ℂ => ((α • ofComplex z : ℍ) : ℂ)) τ) := by
    simp only [ofComplex_apply]
    exact hG (α • τ)
  have h3 := h2.comp (τ : ℂ) h1
  convert h3 using 1 <;> try rfl
  have hσ : σ α = ContinuousAlgEquiv.refl ℝ ℂ := by simp [σ, hα']
  rw [ModularForm.slash_apply, hσ, abs_of_pos hα, ← Matrix.GeneralLinearGroup.val_det_apply]
  simp only [ContinuousAlgEquiv.refl_apply]
  rw [show (2 : ℤ) - 1 = 1 by norm_num, zpow_one, zpow_neg, zpow_ofNat]
  have hd : denom α τ ≠ 0 := denom_ne_zero α τ
  field_simp

theorem slash_zero_apply_of_det_eq_one (g : ℍ → ℂ) {γ : GL (Fin 2) ℝ} (hγ : γ.det = 1) (τ : ℍ) :
    (g ∣[(0 : ℤ)] γ) τ = g (γ • τ) := by
  have hσ : σ γ = ContinuousAlgEquiv.refl ℝ ℂ := by simp [σ, hγ]
  rw [ModularForm.slash_apply, hσ, hγ]
  simp

theorem slash_zero_apply_of_det_pos (g : ℍ → ℂ) {α : GL (Fin 2) ℝ} (hα : 0 < (α.det : ℝ))
    (τ : ℍ) : (g ∣[(0 : ℤ)] α) τ = ((α.det : ℝ) : ℂ)⁻¹ * g (α • τ) := by
  have hα' : 0 < α.val.det := by rwa [Matrix.GeneralLinearGroup.val_det_apply] at hα
  have hσ : σ α = ContinuousAlgEquiv.refl ℝ ℂ := by simp [σ, hα']
  rw [ModularForm.slash_apply, hσ, abs_of_pos hα]
  simp [mul_comm]

abbrev GammaHGL (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

def Φ (τ : ℍ) : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) :=
  periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ

variable {M H}

theorem Φ_apply_of_isPrimitive (τ : ℍ) (f : CuspForm (CohCarrier.GammaH M H) 2)
    {G : ℂ → ℂ} (hG : IsPrimitive ⇑f G) : Φ M H τ f = G τ - G UpperHalfPlane.I := by
  show periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ f = _
  rw [periodAlongOf_apply]
  exact hG.integral_segment_eq (CuspFormClass.holo f).continuous _ _

theorem period_eq_Φ (g : CohCarrier.GammaH M H) :
    periodOf (CohCarrier.GammaH M H) g = Φ M H ((g : SL(2, ℤ)) • UpperHalfPlane.I) := rfl

theorem Φ_smul_sub_Φ (g : CohCarrier.GammaH M H) (τ : ℍ) :
    Φ M H ((g : SL(2, ℤ)) • τ) - Φ M H τ = periodOf (CohCarrier.GammaH M H) g := by
  apply LinearMap.ext
  intro f
  obtain ⟨G, hG⟩ := exists_isPrimitive (CuspFormClass.holo f)
  have hmem : ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ GammaHGL M H :=
    Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) g.2
  have hinv : (⇑f) ∣[(2 : ℤ)] ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) = ⇑f :=
    SlashInvariantForm.slash_action_eqn f _ hmem
  have hdet : 0 < ((Matrix.GeneralLinearGroup.det ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) : ℝ)) := by
    simp
  have hG' : IsPrimitive ⇑f (fun z => G ↑(((g : SL(2, ℤ)) : GL (Fin 2) ℝ) • ofComplex z)) := by
    have := hG.slash_two hdet
    rwa [hinv] at this
  obtain ⟨a, ha⟩ := hG'.exists_const hG
  have ha' : ∀ τ : ℍ, G ↑((g : SL(2, ℤ)) • τ) = G τ + a := fun τ => by
    simpa [ofComplex_apply] using ha τ
  rw [LinearMap.sub_apply, period_eq_Φ, Φ_apply_of_isPrimitive _ f hG,
    Φ_apply_of_isPrimitive _ f hG, Φ_apply_of_isPrimitive _ f hG, ha', ha']
  ring

theorem Φ_smul_sub_Φ_mem {γ : GL (Fin 2) ℝ} (hγ : γ ∈ GammaHGL M H) (τ : ℍ) :
    Φ M H (γ • τ) - Φ M H τ ∈ periodLatticeOf (CohCarrier.GammaH M H) := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  have := Φ_smul_sub_Φ (M := M) (H := H) ⟨g, hg⟩ τ
  rw [ModularGroup.sl_moeb] at this
  rw [show Matrix.SpecialLinearGroup.mapGL ℝ g • τ = ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) • τ from rfl,
    this]
  exact periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) _

theorem mkQ_Φ_smul {γ : GL (Fin 2) ℝ} (hγ : γ ∈ GammaHGL M H) (τ : ℍ) :
    (periodLatticeOf (CohCarrier.GammaH M H)).mkQ (Φ M H (γ • τ)) = (periodLatticeOf (CohCarrier.GammaH M H)).mkQ (Φ M H τ) := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact Φ_smul_sub_Φ_mem hγ τ

section Engine

variable {ι : Type*} [Fintype ι] (A : ι → GL (Fin 2) ℝ)

theorem dualMap_period_eq (hA : ∀ i, 0 < ((A i).det : ℝ))
    (T : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2)
    (hT : ∀ f : CuspForm (CohCarrier.GammaH M H) 2, ⇑(T f) = ∑ i, (⇑f) ∣[(2 : ℤ)] A i)
    (g : CohCarrier.GammaH M H) :
    T.dualMap (periodOf (CohCarrier.GammaH M H) g) =
      ∑ i, (Φ M H (A i • (g : SL(2, ℤ)) • UpperHalfPlane.I) - Φ M H (A i • UpperHalfPlane.I)) := by
  apply LinearMap.ext
  intro f
  obtain ⟨G, hG⟩ := exists_isPrimitive (CuspFormClass.holo f)

  have hprim : IsPrimitive ⇑(T f) (fun z => ∑ i, G ↑(A i • ofComplex z)) := by
    rw [hT]
    exact IsPrimitive.sum Finset.univ (fun i _ => hG.slash_two (hA i))
  rw [LinearMap.dualMap_apply, period_eq_Φ, Φ_apply_of_isPrimitive _ _ hprim,
    LinearMap.sum_apply]
  simp only [LinearMap.sub_apply, Φ_apply_of_isPrimitive _ f hG, ofComplex_apply,
    Finset.sum_sub_distrib]
  ring

theorem sum_mkQ_Φ_smul_eq {d : ℝ} (hd : 0 < d) (hA : ∀ i, ((A i).det : ℝ) = d)
    (hstab : ∀ g : ℍ → ℂ, (∀ γ ∈ GammaHGL M H, g ∣[(0 : ℤ)] γ = g) →
      ∀ γ ∈ GammaHGL M H, (∑ i, g ∣[(0 : ℤ)] A i) ∣[(0 : ℤ)] γ = ∑ i, g ∣[(0 : ℤ)] A i)
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ GammaHGL M H) (τ : ℍ) :
    ∑ i, (periodLatticeOf (CohCarrier.GammaH M H)).mkQ (Φ M H (A i • γ • τ)) = ∑ i, (periodLatticeOf (CohCarrier.GammaH M H)).mkQ (Φ M H (A i • τ)) := by
  classical
  set Φb : ℍ → (Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)) ⧸ periodLatticeOf (CohCarrier.GammaH M H) :=
    fun τ => (periodLatticeOf (CohCarrier.GammaH M H)).mkQ (Φ M H τ) with hΦb
  have hΦb_inv : ∀ γ ∈ GammaHGL M H, ∀ τ : ℍ, Φb (γ • τ) = Φb τ := fun γ hγ τ => mkQ_Φ_smul hγ τ
  have hAdet : ∀ i, 0 < ((A i).det : ℝ) := fun i => (hA i).symm ▸ hd

  have hcount : ∀ v, (Finset.univ.filter fun i => v = Φb (A i • γ • τ)).card =
      (Finset.univ.filter fun i => v = Φb (A i • τ)).card := by
    intro v
    let g : ℍ → ℂ := fun τ => if v = Φb τ then 1 else 0
    have hg : ∀ γ ∈ GammaHGL M H, g ∣[(0 : ℤ)] γ = g := by
      intro γ hγ
      funext τ
      rw [slash_zero_apply_of_det_eq_one g (Subgroup.HasDetOne.det_eq hγ)]
      simp only [g, hΦb_inv γ hγ]
    have key := congr_fun (hstab g hg γ hγ) τ
    rw [slash_zero_apply_of_det_eq_one _ (Subgroup.HasDetOne.det_eq hγ)] at key
    simp only [Finset.sum_apply, slash_zero_apply_of_det_pos _ (hAdet _), hA,
      ← Finset.mul_sum] at key
    have hd' : ((d : ℝ) : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hd.ne')
    have key' := mul_left_cancel₀ hd' key
    simp only [g, Finset.sum_boole] at key'
    exact_mod_cast key'
  have hms : (Finset.univ.val.map fun i => Φb (A i • γ • τ)) =
      Finset.univ.val.map fun i => Φb (A i • τ) := by
    refine Multiset.ext.mpr fun v => ?_
    rw [Multiset.count_map, Multiset.count_map]
    have := hcount v
    simpa [Finset.card_def, Finset.filter_val] using this
  show ∑ i, Φb (A i • γ • τ) = ∑ i, Φb (A i • τ)
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum, hms]

theorem dualMap_period_mem {d : ℝ} (hd : 0 < d) (hA : ∀ i, ((A i).det : ℝ) = d)
    (T : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2)
    (hT : ∀ f : CuspForm (CohCarrier.GammaH M H) 2, ⇑(T f) = ∑ i, (⇑f) ∣[(2 : ℤ)] A i)
    (hstab : ∀ g : ℍ → ℂ, (∀ γ ∈ GammaHGL M H, g ∣[(0 : ℤ)] γ = g) →
      ∀ γ ∈ GammaHGL M H, (∑ i, g ∣[(0 : ℤ)] A i) ∣[(0 : ℤ)] γ = ∑ i, g ∣[(0 : ℤ)] A i)
    (g : CohCarrier.GammaH M H) :
    T.dualMap (periodOf (CohCarrier.GammaH M H) g) ∈ periodLatticeOf (CohCarrier.GammaH M H) := by
  have hAdet : ∀ i, 0 < ((A i).det : ℝ) := fun i => (hA i).symm ▸ hd
  rw [dualMap_period_eq A hAdet T hT g, ← Submodule.ker_mkQ (periodLatticeOf (CohCarrier.GammaH M H)), LinearMap.mem_ker,
    map_sum]
  simp only [map_sub, Finset.sum_sub_distrib]
  have hmem : ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ GammaHGL M H :=
    Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) g.2
  have := sum_mkQ_Φ_smul_eq A hd hA hstab hmem UpperHalfPlane.I
  simp only [ModularGroup.sl_moeb]
  rw [this, sub_self]

end Engine

section Instances

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem heckeU_eq_sum (k : ℤ) (p : ℕ) (f : ℍ → ℂ) :
    ModularForm.heckeU k p f = ∑ j : Fin p, f ∣[k] ModularForm.heckeMatrix p j := by
  rw [ModularForm.heckeU_def, Finset.sum_range]

def heckeTFamilyH (M : ℕ) [NeZero M] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    Option (Fin ℓ) → GL (Fin 2) ℝ :=
  fun o => o.elim
    ((Matrix.SpecialLinearGroup.mapGL ℝ
        ((CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM) : CongruenceSubgroup.Gamma0 M) :
          SL(2, ℤ)) : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ)
    fun j => ModularForm.heckeMatrix ℓ j

theorem sum_slash_heckeTFamilyH (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : ℍ → ℂ) :
    ∑ o, f ∣[k] heckeTFamilyH M hℓ hℓM o =
      ModularForm.heckeU k ℓ f +
        f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
          ((CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM) : CongruenceSubgroup.Gamma0 M) :
            SL(2, ℤ)) : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ) := by
  rw [Fintype.sum_option, heckeU_eq_sum, add_comm]
  rfl

theorem det_heckeTFamilyH {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (o : Option (Fin ℓ)) :
    ((heckeTFamilyH M hℓ hℓM o).det : ℝ) = ℓ := by
  cases o with
  | none =>
    show (((Matrix.SpecialLinearGroup.mapGL ℝ _ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ).det : ℝ) = ℓ
    rw [map_mul, Units.val_mul, ModularForm.det_heckeDiagMatrix hℓ.ne_zero]
    simp
  | some j => exact ModularForm.det_heckeMatrix hℓ.ne_zero j

theorem heckeTLinH_dualMap_period_mem {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (g : CohCarrier.GammaH M H) :
    (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap (periodOf (CohCarrier.GammaH M H) g) ∈
      periodLatticeOf (CohCarrier.GammaH M H) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine dualMap_period_mem (heckeTFamilyH M hℓ hℓM) (d := (ℓ : ℝ)) (by exact_mod_cast hℓ.pos)
    (det_heckeTFamilyH hℓ hℓM) _ (fun f => ?_) (fun g hg γ hγ => ?_) g
  · rw [CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM), sum_slash_heckeTFamilyH]
  · rw [sum_slash_heckeTFamilyH]
    exact ModularForm.heckeU_add_slash_slash_eq_self_of_mem_GammaH M H 0 hℓ hℓM _
      (CuspForm.gammaLift_apply_11 hℓ hℓM) hg γ hγ

theorem heckeULinH_dualMap_period_mem {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (g : CohCarrier.GammaH M H) :
    (CuspForm.heckeULinH 2 q).dualMap (periodOf (CohCarrier.GammaH M H) g) ∈
      periodLatticeOf (CohCarrier.GammaH M H) := by
  refine dualMap_period_mem (fun j : Fin q => ModularForm.heckeMatrix q j) (d := (q : ℝ))
    (by exact_mod_cast hq.pos) (fun j => ModularForm.det_heckeMatrix hq.ne_zero j) _
    (fun f => ?_) (fun g hg γ hγ => ?_) g
  · rw [CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU M H 2 hq hqM), heckeU_eq_sum]
  · rw [← heckeU_eq_sum]
    exact ModularForm.heckeU_slash_eq_self_of_mem_GammaH M H 0 hq hqM hg γ hγ

theorem diamondLinH_dualMap_period_mem (d : (ZMod M)ˣ) (g : CohCarrier.GammaH M H) :
    (CuspForm.diamondLinH 2 d).dualMap (periodOf (CohCarrier.GammaH M H) g) ∈
      periodLatticeOf (CohCarrier.GammaH M H) := by
  set σ : CongruenceSubgroup.Gamma0 M := CuspForm.gammaLift M d with hσ
  refine dualMap_period_mem (fun _ : Unit => (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))
    (d := (1 : ℝ)) one_pos (fun _ => by simp) _ (fun f => ?_) (fun g hg γ hγ => ?_) g
  · rw [Fintype.sum_unique, CuspForm.coe_diamondLinH_apply 2 (CuspForm.stableD M H 2)]
  · rw [Fintype.sum_unique]
    obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.mp hγ
    have hconj : (σ : SL(2, ℤ)) * γ₀ * (σ : SL(2, ℤ))⁻¹ ∈ CohCarrier.GammaH M H :=
      CohCarrier.conj_mem_GammaH M H σ ⟨γ₀, hγ₀⟩
    have e : (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ γ₀ : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((σ : SL(2, ℤ)) * γ₀ * (σ : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
      rw [← map_mul, ← map_mul, inv_mul_cancel_right]
    show (g ∣[(0 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∣[(0 : ℤ)]
        (Matrix.SpecialLinearGroup.mapGL ℝ γ₀ : GL (Fin 2) ℝ) =
      g ∣[(0 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)
    rw [← SlashAction.slash_mul, e, SlashAction.slash_mul, hg _ (Subgroup.mem_map_of_mem _ hconj)]

end Instances

end PeriodLatticeHStableProof

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "ComplexPlaceDictionaryOf laurentBaseChange HeckeBetaHDefined HeckeAlphaHBarIntegral HeckeBetaHBarIntegral heckeDivHBar translation_mem_GammaH xHFunctionField xHTopFunctionFieldC periodAlongOf periodAlongOf_apply periodOf periodLatticeOf periodOf_mem_periodLatticeOf clamp01 clamp01_of_mem segmentPoint continuous_segmentPoint segmentPath continuous_segmentPath periodAlong period JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ComplexPlaceDictionaryOf.heckeDivHBar_single_pt"
p2m_open "ModularCurve"
namespace HeckeAbelJacobiH

open UpperHalfPlane PeriodLatticeHStableProof
open scoped MatrixGroups ModularForm

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

set_option linter.unusedSectionVars false

def aj : (ℍ →₀ ℤ) →+ Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) :=
  Finsupp.liftAddHom fun τ => zmultiplesHom _ (Φ M H τ)

theorem aj_apply (c : ℍ →₀ ℤ) :
    aj M H c = c.sum fun τ n => n • periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ := by
  simp only [aj, Finsupp.liftAddHom_apply]
  rfl

@[scoped simp] theorem aj_single (τ : ℍ) (n : ℤ) : aj M H (Finsupp.single τ n) = n • Φ M H τ := by
  simp [aj]

variable {M H}
variable {ι : Type*} [Fintype ι] (A : ι → GL (Fin 2) ℝ)

def liftA (τ : ℍ) : ℍ →₀ ℤ := ∑ i, Finsupp.single (A i • τ) 1

def liftAHom : (ℍ →₀ ℤ) →+ (ℍ →₀ ℤ) :=
  Finsupp.liftAddHom fun τ => zmultiplesHom _ (liftA A τ)

@[scoped simp] theorem liftAHom_single (τ : ℍ) (n : ℤ) : liftAHom A (Finsupp.single τ n) = n • liftA A τ := by
  simp [liftAHom]

theorem aj_liftA (τ : ℍ) : aj M H (liftA A τ) = ∑ i, Φ M H (A i • τ) := by
  simp only [liftA, map_sum, aj_single, one_smul]

theorem dualMap_Φ_eq (hA : ∀ i, 0 < ((A i).det : ℝ))
    (T : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2)
    (hT : ∀ f : CuspForm (CohCarrier.GammaH M H) 2, ⇑(T f) = ∑ i, (⇑f) ∣[(2 : ℤ)] A i) (τ : ℍ) :
    T.dualMap (Φ M H τ) = ∑ i, (Φ M H (A i • τ) - Φ M H (A i • UpperHalfPlane.I)) := by
  apply LinearMap.ext
  intro f
  obtain ⟨G, hG⟩ := exists_isPrimitive (CuspFormClass.holo f)
  have hprim : IsPrimitive ⇑(T f) (fun z => ∑ i, G ↑(A i • ofComplex z)) := by
    rw [hT]
    exact IsPrimitive.sum Finset.univ (fun i _ => hG.slash_two (hA i))
  rw [LinearMap.dualMap_apply, Φ_apply_of_isPrimitive _ _ hprim, LinearMap.sum_apply]
  simp only [LinearMap.sub_apply, Φ_apply_of_isPrimitive _ f hG, ofComplex_apply, Finset.sum_sub_distrib]
  ring

theorem aj_liftA_sub_dualMap (hA : ∀ i, 0 < ((A i).det : ℝ))
    (T : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2)
    (hT : ∀ f : CuspForm (CohCarrier.GammaH M H) 2, ⇑(T f) = ∑ i, (⇑f) ∣[(2 : ℤ)] A i) (τ : ℍ) :
    aj M H (liftA A τ) - T.dualMap (Φ M H τ) = aj M H (liftA A UpperHalfPlane.I) := by
  rw [aj_liftA, aj_liftA, dualMap_Φ_eq A hA T hT, Finset.sum_sub_distrib, sub_sub_cancel]

theorem aj_liftAHom_sub_dualMap (hA : ∀ i, 0 < ((A i).det : ℝ))
    (T : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2)
    (hT : ∀ f : CuspForm (CohCarrier.GammaH M H) 2, ⇑(T f) = ∑ i, (⇑f) ∣[(2 : ℤ)] A i) (c : ℍ →₀ ℤ) :
    aj M H (liftAHom A c) - T.dualMap (aj M H c) = (c.sum fun _ n => n) • aj M H (liftA A UpperHalfPlane.I) := by
  let Φ₁ : (ℍ →₀ ℤ) →+ Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) :=
    (aj M H).comp (liftAHom A) - T.dualMap.toAddMonoidHom.comp (aj M H)
  let Ψ : (ℍ →₀ ℤ) →+ Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) :=
    (zmultiplesHom _ (aj M H (liftA A UpperHalfPlane.I))).comp (Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ)
  have hΦΨ : Φ₁ = Ψ := by
    refine Finsupp.addHom_ext fun τ n => ?_
    simp only [Φ₁, Ψ, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, liftAHom_single, map_zsmul,
      aj_single, LinearMap.toAddMonoidHom_coe, Finsupp.liftAddHom_apply_single,
      AddMonoidHom.id_apply, zmultiplesHom_apply, ← smul_sub]
    rw [aj_liftA_sub_dualMap A hA T hT τ]
  have h := DFunLike.congr_fun hΦΨ c
  simp only [Φ₁, Ψ, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    zmultiplesHom_apply, Finsupp.liftAddHom_apply] at h
  rw [h]
  rfl

theorem aj_liftAHom_sub_dualMap_mem (hA : ∀ i, 0 < ((A i).det : ℝ))
    (T : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2)
    (hT : ∀ f : CuspForm (CohCarrier.GammaH M H) 2, ⇑(T f) = ∑ i, (⇑f) ∣[(2 : ℤ)] A i) (c : ℍ →₀ ℤ)
    (hsum : (c.sum fun _ n => n) = 0) :
    (((liftAHom A c).sum fun τ n => n • periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) -
        T.dualMap (c.sum fun τ n => n • periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ)) ∈
      periodLatticeOf (CohCarrier.GammaH M H) := by
  rw [← aj_apply, ← aj_apply, aj_liftAHom_sub_dualMap A hA T hT c, hsum, zero_smul]
  exact Submodule.zero_mem _

def heckeUFamily (ℓ : ℕ) : Fin ℓ → GL (Fin 2) ℝ := fun j => ModularForm.heckeMatrix ℓ j

theorem aj_liftAHom_heckeT_sub_mem {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (c : ℍ →₀ ℤ)
    (hsum : (c.sum fun _ n => n) = 0) :
    (((liftAHom (heckeTFamilyH M hℓ hℓM) c).sum fun τ n => n • periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) -
        (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap
          (c.sum fun τ n => n • periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ)) ∈
      periodLatticeOf (CohCarrier.GammaH M H) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine aj_liftAHom_sub_dualMap_mem (heckeTFamilyH M hℓ hℓM) (fun o => ?_) _ (fun f => ?_) c hsum
  · rw [det_heckeTFamilyH hℓ hℓM]; exact_mod_cast hℓ.pos
  · rw [CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM), sum_slash_heckeTFamilyH]

theorem aj_liftAHom_heckeU_sub_mem {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) (c : ℍ →₀ ℤ)
    (hsum : (c.sum fun _ n => n) = 0) :
    (((liftAHom (heckeUFamily ℓ) c).sum fun τ n => n • periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) -
        (CuspForm.heckeULinH 2 ℓ).dualMap
          (c.sum fun τ n => n • periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ)) ∈
      periodLatticeOf (CohCarrier.GammaH M H) := by
  refine aj_liftAHom_sub_dualMap_mem (heckeUFamily ℓ) (fun j => ?_) _ (fun f => ?_) c hsum
  · show 0 < ((ModularForm.heckeMatrix ℓ j).det : ℝ)
    rw [ModularForm.det_heckeMatrix hℓ.ne_zero j]; exact_mod_cast hℓ.pos
  · rw [CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU M H 2 hℓ hℓM), heckeU_eq_sum]
    rfl

end HeckeAbelJacobiH
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.ModularCurve.HeckeAbelJacobiH"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.ModularCurve.HeckeAbelJacobiH P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "ComplexPlaceDictionaryOf laurentBaseChange HeckeBetaHDefined HeckeAlphaHBarIntegral HeckeBetaHBarIntegral heckeDivHBar translation_mem_GammaH xHFunctionField xHTopFunctionFieldC periodAlongOf periodAlongOf_apply periodOf periodLatticeOf periodOf_mem_periodLatticeOf clamp01 clamp01_of_mem segmentPoint continuous_segmentPoint segmentPath continuous_segmentPath periodAlong period JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ComplexPlaceDictionaryOf.heckeDivHBar_single_pt"
p2m_open "ModularCurve"
namespace HeckeAbelJacobiH

open UpperHalfPlane AlgebraicCurve PeriodLatticeHStableProof
open scoped MatrixGroups ModularForm

set_option linter.unusedSectionVars false

section DivisorClause

variable {ι : Type*} [Fintype ι] (A : ι → GL (Fin 2) ℝ) {X : Type*} (pt : ℍ → X) (T : (X →₀ ℤ) →+ (X →₀ ℤ))

theorem mapDomain_liftAHom (hpt : ∀ τ : ℍ, T (Finsupp.single (pt τ) 1) = ∑ i, Finsupp.single (pt (A i • τ)) 1)
    (c : ℍ →₀ ℤ) : Finsupp.mapDomain pt (liftAHom A c) = T (Finsupp.mapDomain pt c) := by
  classical
  have key : (Finsupp.mapDomain.addMonoidHom pt).comp (liftAHom A) =
      T.comp (Finsupp.mapDomain.addMonoidHom pt) := by
    refine Finsupp.addHom_ext fun τ n => ?_
    simp only [AddMonoidHom.comp_apply, Finsupp.mapDomain.addMonoidHom_apply, liftAHom_single,
      Finsupp.mapDomain_single]
    rw [Finsupp.mapDomain_smul, ← Finsupp.smul_single_one (pt τ) n, map_zsmul, hpt τ, liftA,
      Finsupp.mapDomain_finsetSum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_single
  simpa using DFunLike.congr_fun key c

end DivisorClause
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.ModularCurve.HeckeAbelJacobiH P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.ModularCurve"

section Degree

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem exists_transcendental_xH :
    ∃ x : laurentBaseChange ℂ (xHFunctionField M H), Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set (laurentBaseChange ℂ (xHFunctionField M H))))
        (laurentBaseChange ℂ (xHFunctionField M H)) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ℂ (CohCarrier.GammaH M H)
    (translation_mem_GammaH M H)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem isCurveOver_xH : IsCurveOver ℂ (laurentBaseChange ℂ (xHFunctionField M H)) := by
  obtain ⟨x, hx, hfin⟩ := exists_transcendental_xH M H
  haveI := hfin
  have hsep : Algebra.IsSeparable (IntermediateField.adjoin ℂ ({x} : Set (laurentBaseChange ℂ (xHFunctionField M H))))
      (laurentBaseChange ℂ (xHFunctionField M H)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact AlgebraicCurve.isCurveOver_of_transcendental hx hfin hsep

theorem deg_pt_eq_one (v : Place ℂ (laurentBaseChange ℂ (xHFunctionField M H))) : v.deg = 1 :=
  haveI := isCurveOver_xH M H
  IsCurveOver.deg_eq_one_of_isAlgClosed v

variable {M H}

theorem degree_mapDomain_pt (D : ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (xHFunctionField M H))
    (c : ℍ →₀ ℤ) : Divisor.degree (Finsupp.mapDomain D.pt c) = c.sum fun _ n => n := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, Finsupp.mapDomain_single, ih,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
      Divisor.degree_single, deg_pt_eq_one]
    simp

end Degree
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.ModularCurve.HeckeAbelJacobiH P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.ModularCurve"

section Main

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem main (D : ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (xHFunctionField M H))
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (h0 : HeckeBetaHDefined M H ℓ)
    (hα : HeckeAlphaHBarIntegral ℂ M H ℓ) (hβ : HeckeBetaHBarIntegral ℂ M H ℓ)
    [HasPrincipalDivisors ℂ (laurentBaseChange ℂ (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (c : ℍ →₀ ℤ) (hdeg : Divisor.degree (Finsupp.mapDomain D.pt c) = 0) :
    ∃ c' : ℍ →₀ ℤ,
      Finsupp.mapDomain D.pt c' = heckeDivHBar hα hβ (Finsupp.mapDomain D.pt c) ∧
      (∀ hℓM : ¬ ℓ ∣ M,
        (c'.sum fun τ n => n • periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) -
            (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap
              (c.sum fun τ n => n • periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
          periodLatticeOf (CohCarrier.GammaH M H)) ∧
      (ℓ ∣ M →
        (c'.sum fun τ n => n • periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) -
            (CuspForm.heckeULinH 2 ℓ).dualMap
              (c.sum fun τ n => n • periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
          periodLatticeOf (CohCarrier.GammaH M H)) := by
  have hsum : (c.sum fun _ n => n) = 0 := by rw [← degree_mapDomain_pt D c]; exact hdeg
  have hpt := ModularCurve.ComplexPlaceDictionaryOf.heckeDivHBar_single_pt M H D ℓ hℓ h0 hα hβ
  by_cases hdvd : ℓ ∣ M
  · refine ⟨liftAHom (heckeUFamily ℓ) c, ?_, fun hℓM => absurd hdvd hℓM,
      fun _ => aj_liftAHom_heckeU_sub_mem hℓ hdvd c hsum⟩
    refine mapDomain_liftAHom (heckeUFamily ℓ) D.pt (heckeDivHBar hα hβ) (fun τ => ?_) c
    rw [(hpt τ).2 hdvd, Finset.sum_range]
    rfl
  · refine ⟨liftAHom (heckeTFamilyH M hℓ hdvd) c, ?_, fun hℓM => aj_liftAHom_heckeT_sub_mem hℓ hℓM c hsum,
      fun h => absurd h hdvd⟩
    refine mapDomain_liftAHom (heckeTFamilyH M hℓ hdvd) D.pt (heckeDivHBar hα hβ) (fun τ => ?_) c
    rw [(hpt τ).1 hdvd _ (CuspForm.gammaLift_apply_11 hℓ hdvd), Finset.sum_range, Fintype.sum_option,
      add_comm]
    rfl

end Main
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.ModularCurve.HeckeAbelJacobiH P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.ModularCurve"

end HeckeAbelJacobiH
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.ModularCurve.HeckeAbelJacobiH P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.ModularCurve.HeckeAbelJacobiH P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.ModularCurve.HeckeAbelJacobiH P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf.ModularCurve"

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (h0 : ModularCurve.HeckeBetaHDefined M H ℓ)
    (hα : ModularCurve.HeckeAlphaHBarIntegral ℂ M H ℓ) (hβ : ModularCurve.HeckeBetaHBarIntegral ℂ M H ℓ)
    [AlgebraicCurve.HasPrincipalDivisors ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0) :
    ∃ c' : UpperHalfPlane →₀ ℤ,
      Finsupp.mapDomain D.pt c' = ModularCurve.heckeDivHBar hα hβ (Finsupp.mapDomain D.pt c) ∧
      (∀ hℓM : ¬ ℓ ∣ M,
        (c'.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) -
            (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap
              (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) ∧
      (ℓ ∣ M →
        (c'.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) -
            (CuspForm.heckeULinH 2 ℓ).dualMap
              (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :=
  ModularCurve.HeckeAbelJacobiH.main M H D ℓ hℓ h0 hα hβ c hdeg

end
end S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_mapDomain_eq_heckeDivHBar_abelJacobi_sub_mem_periodLatticeOf (solution)
