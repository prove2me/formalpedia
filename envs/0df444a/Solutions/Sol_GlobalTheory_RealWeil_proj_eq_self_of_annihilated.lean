-- Prove2me | solution 1 for GlobalTheory.RealWeil.proj_eq_self_of_annihilated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:50:11.287299+00:00
-- url     : https://prove2.me/submissions/f2bfd6db-52b7-4b5f-aff6-54212306a841

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_continuous
import Theorems.Thm_GlobalTheory_RealWeil_proj_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
namespace GlobalTheory.RealWeil.Vacuum
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}
end GlobalTheory.RealWeil.Vacuum
namespace GlobalTheory.RealWeil
open Vacuum
open MeasureTheory Complex in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] in
private theorem gaussian_exponent_add_eq (a s : ℝ) (ζ η : ℂ)
    (hs : s = a * (ζ.im * η.re - ζ.re * η.im)) :
    ((Real.pi / 2 * a * ‖ζ + η‖ ^ 2 : ℝ) : ℂ) + -(Real.pi * I * s) =
      ((Real.pi / 2 * a * ‖ζ‖ ^ 2 : ℝ) : ℂ) + Real.pi * a * ((starRingEnd ℂ) ζ * η) +
        ((Real.pi / 2 * a * ‖η‖ ^ 2 : ℝ) : ℂ) := by
  subst hs
  apply Complex.ext <;>
    simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring
open MeasureTheory Complex in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] in
private theorem omJ_line_line_eq {J : V ≃ₗᵢ[ℝ] V} (hJ : ∀ x, J (J x) = -x)
    (u : V) (ζ η : ℂ) :
    _root_.GlobalTheory.RealWeil.omJ J (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ)
      (_root_.GlobalTheory.RealWeil.Vacuum.line J u η) = ‖u‖ ^ 2 * (ζ.im * η.re - ζ.re * η.im) := by
  have h0 := inner_self_complexStructure_eq_zero hJ u
  unfold _root_.GlobalTheory.RealWeil.omJ
  simp only [_root_.GlobalTheory.RealWeil.Vacuum.line_apply, map_add, map_smul, hJ, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, inner_neg_right,
    real_inner_comm u (J u), h0, LinearIsometryEquiv.inner_map_map, real_inner_self_eq_norm_sq]
  ring
open MeasureTheory Complex in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] in
private theorem differentiable_gaussian_mul_orbit_line {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}
    (hJ : ∀ x, J (J x) = -x)
    (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ)
    (f : B) (hf : _root_.GlobalTheory.RealWeil.Sm ρ f)
    (ha : ∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (J z) = 0)
    (u : V) :
    Differentiable ℂ fun ζ : ℂ =>
      cexp ((Real.pi / 2 * ‖u‖ ^ 2 * ‖ζ‖ ^ 2 : ℝ) : ℂ) • ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f := by
  obtain ⟨-, hmul, -, -⟩ := h
  set ψ : ℂ → B := fun ζ =>
    cexp ((Real.pi / 2 * ‖u‖ ^ 2 * ‖ζ‖ ^ 2 : ℝ) : ℂ) • ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f
    with hψ
  set D := fderiv ℝ (fun v => ρ v f) 0
  have hD : HasFDerivAt (fun v => ρ v f) D 0 :=
    ((hf.differentiable (by simp)) 0).hasFDerivAt
  have hDJ : ∀ z, D (J z) = I • D z := by
    intro z
    have e : I • D (J z) = -D z := eq_neg_of_add_eq_zero_right (ha z)
    calc D (J z) = (-I * I) • D (J z) := by simp [I_mul_I]
      _ = -I • (I • D (J z)) := by rw [smul_smul]
      _ = I • D z := by rw [e, smul_neg, neg_smul, neg_neg]
  have key : ∀ η : ℂ, D (_root_.GlobalTheory.RealWeil.Vacuum.line J u η) = η • D u := by
    intro η
    rw [_root_.GlobalTheory.RealWeil.Vacuum.line_apply, map_add, map_smul, map_smul, hDJ,
      ← Complex.coe_smul η.re, ← Complex.coe_smul η.im, smul_smul (η.im : ℂ) I, ← add_smul,
      Complex.re_add_im]
  have hψ0 : HasDerivAt ψ (D u) 0 := by
    have hn : HasFDerivAt (fun ζ : ℂ => ((Real.pi / 2 * ‖u‖ ^ 2 * ‖ζ‖ ^ 2 : ℝ) : ℂ))
        (0 : ℂ →L[ℝ] ℂ) 0 := by
      have h1 := ((hasStrictFDerivAt_norm_sq (0 : ℂ)).hasFDerivAt.const_mul
        (Real.pi / 2 * ‖u‖ ^ 2))
      have h2 := ofRealCLM.hasFDerivAt.comp (0 : ℂ) h1
      simpa [Function.comp_def] using h2
    have hg : HasFDerivAt (fun ζ => ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f)
        (D.comp (_root_.GlobalTheory.RealWeil.Vacuum.line J u)) 0 := by
      have hD0 : HasFDerivAt (fun v => ρ v f) D (_root_.GlobalTheory.RealWeil.Vacuum.line J u 0) := by
        simpa using hD
      have h3 := hD0.comp (0 : ℂ) (_root_.GlobalTheory.RealWeil.Vacuum.line J u).hasFDerivAt
      simpa [Function.comp_def] using h3
    have hP := hn.cexp.smul hg
    refine (hasFDerivAt_of_restrictScalars ℝ hP
      (f' := (1 : ℂ →L[ℂ] ℂ).smulRight (D u)) ?_).hasDerivAt.congr_deriv (by simp)
    ext η
    simp [key]
  have hshift : ∀ ζ η : ℂ, ψ (ζ + η) =
      cexp ((Real.pi / 2 * ‖u‖ ^ 2 * ‖ζ‖ ^ 2 : ℝ) : ℂ) •
        (cexp (Real.pi * ‖u‖ ^ 2 * ((starRingEnd ℂ) ζ * η)) •
          ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) (ψ η)) := by
    intro ζ η
    simp only [hψ, map_add, map_smul]
    rw [hmul, smul_smul, smul_smul, smul_smul, ← exp_add, ← exp_add, ← exp_add]
    congr 2
    have e := gaussian_exponent_add_eq (‖u‖ ^ 2) _ ζ η (omJ_line_line_eq hJ u ζ η)
    push_cast at e ⊢
    linear_combination e
  intro ζ
  have hd : DifferentiableAt ℂ (fun η => ψ (ζ + η)) (ζ - ζ) := by
    rw [sub_self]
    simp_rw [hshift ζ]
    have hψd : DifferentiableAt ℂ ψ 0 := hψ0.differentiableAt
    fun_prop
  have h4 := hd.comp (f := fun y => y - ζ) ζ (differentiableAt_id.sub_const ζ)
  simpa [Function.comp_def] using h4
open MeasureTheory Complex in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] in
private theorem circleAverage_orbit_line_eq_gaussian_smul {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}
    [CompleteSpace B] (hJ : ∀ x, J (J x) = -x)
    (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ)
    (f : B) (hf : _root_.GlobalTheory.RealWeil.Sm ρ f)
    (ha : ∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (J z) = 0)
    (u : V) :
    Real.circleAverage (fun ζ => ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f) 0 1 =
      cexp (-(Real.pi / 2) * ‖u‖ ^ 2) • f := by
  have hψ := differentiable_gaussian_mul_orbit_line hJ h f hf ha u
  have hmean := (hψ.diffContOnCl (s := Metric.ball (0 : ℂ) |1|)).circleAverage
  have hρ0 : ρ 0 f = f := h.1 f
  have hs : Set.EqOn
      (fun ζ : ℂ => cexp ((Real.pi / 2 * ‖u‖ ^ 2 * ‖ζ‖ ^ 2 : ℝ) : ℂ) •
        ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f)
      (fun ζ : ℂ => cexp ((Real.pi / 2 * ‖u‖ ^ 2 : ℝ) : ℂ) • ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f)
      (Metric.sphere 0 |1|) := by
    intro ζ hζ
    simp only [abs_one, mem_sphere_zero_iff_norm] at hζ
    simp [hζ]
  rw [Real.circleAverage_congr_sphere hs, Real.circleAverage_fun_smul] at hmean
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    ofReal_zero, exp_zero, map_zero, hρ0, one_smul] at hmean
  calc Real.circleAverage (fun ζ => ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f) 0 1
      = (cexp (-(Real.pi / 2) * ‖u‖ ^ 2) * cexp ((Real.pi / 2 * ‖u‖ ^ 2 : ℝ) : ℂ)) •
          Real.circleAverage (fun ζ => ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f) 0 1 := by
        rw [← exp_add]; push_cast; ring_nf; simp
    _ = cexp (-(Real.pi / 2) * ‖u‖ ^ 2) • f := by rw [mul_smul, hmean]
end GlobalTheory.RealWeil
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil
open Vacuum
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
namespace GlobalTheory.RealWeil
namespace _root_.GlobalTheory.RealWeil
theorem _root_.solution (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B]
    [CompleteSpace B]
    (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B) (hJ : ∀ x, J (J x) = -x)
    (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ) (f : B)
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f)
    (ha : ∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (J z) = 0) :
    _root_.GlobalTheory.RealWeil.proj h f = f := by
  have hg : ∀ u : V, _root_.GlobalTheory.RealWeil.gau u = cexp (-(Real.pi / 2) * ‖u‖ ^ 2) := fun u => rfl
  have hiso : ∀ (x : V) (y : B), ‖ρ x y‖ = ‖y‖ := h.2.2.1
  rw [_root_.GlobalTheory.RealWeil.proj_apply]
  set G : ℝ → V → B := fun θ u =>
    _root_.GlobalTheory.RealWeil.gau u • ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u (circleMap 0 1 θ)) f with hG
  have hrot : ∀ θ, ∫ u, _root_.GlobalTheory.RealWeil.gau u • ρ u f = ∫ u, G θ u := by
    intro θ
    set R := _root_.GlobalTheory.RealWeil.Vacuum.rot hJ θ
    have e := (LinearIsometryEquiv.measurePreserving R).integral_comp
      R.toHomeomorph.measurableEmbedding (fun u => _root_.GlobalTheory.RealWeil.gau u • ρ u f)
    rw [← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hG, hg, LinearIsometryEquiv.norm_map]
    rfl
  have hcont : Continuous (Function.uncurry G) := by
    have ha' : Continuous fun p : ℝ × V => _root_.GlobalTheory.RealWeil.Vacuum.line J p.2 (circleMap 0 1 p.1) := by
      simp only [_root_.GlobalTheory.RealWeil.Vacuum.line_apply]
      have := continuous_circleMap (0 : ℂ) 1
      fun_prop
    exact (_root_.GlobalTheory.RealWeil.continuous_gau.comp continuous_snd).smul
      (h.continuous ha' continuous_const)
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) := by
    rw [isFiniteMeasure_restrict]
    exact ((measure_mono Set.uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top).ne
  have hint : Integrable (Function.uncurry G)
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod volume) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod
      (_root_.GlobalTheory.RealWeil.integrable_gau.norm.mul_const ‖f‖)) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    simp [Function.uncurry, hG, norm_smul, hiso]
  have hpos : (2 * Real.pi) ≠ 0 := by positivity
  calc ∫ u, _root_.GlobalTheory.RealWeil.gau u • ρ u f
      = (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, ∫ u, G θ u := by
        rw [intervalIntegral.integral_congr (g := fun _ => ∫ u, _root_.GlobalTheory.RealWeil.gau u • ρ u f)
          (fun θ _ => (hrot θ).symm), intervalIntegral.integral_const, smul_smul, sub_zero,
          inv_mul_cancel₀ hpos, one_smul]
    _ = ∫ u, _root_.GlobalTheory.RealWeil.gau u •
          Real.circleAverage (fun ζ => ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f) 0 1 := by
        rw [intervalIntegral_integral_swap hint, ← integral_smul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only [hG, Real.circleAverage_def, intervalIntegral.integral_smul]
        rw [smul_comm]
    _ = ∫ u, cexp (-(Real.pi : ℂ) * ‖u‖ ^ 2) • f := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only
        rw [circleAverage_orbit_line_eq_gaussian_smul hJ h f hf ha u, smul_smul, hg, ← exp_add]
        ring_nf
    _ = f := by
        rw [integral_smul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm (by simp [Real.pi_pos])]
        simp [div_self (ofReal_ne_zero.2 Real.pi_ne_zero)]
end _root_.GlobalTheory.RealWeil
end GlobalTheory.RealWeil
