-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OneParamFourier.integral_mul_char_eq_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:13:14.615978+00:00
-- url     : https://prove2.me/submissions/d538f2bd-e634-46a4-ab97-39c10b387d93

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierOneParameterIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_OneParamFourier_integral_translate_mul_char
import Theorems.Thm_GlobalTheory_CompanionTheory_OneParamFourier_integrable_mul_char
import Theorems.Thm_GlobalTheory_CompanionTheory_OneParamFourier_integrable_uncurry_translate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OneParamFourier
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [MeasurableSpace A] [BorelSpace A]
namespace GlobalTheory.CompanionTheory.OneParamFourier
theorem _root_.solution (A : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] (lam : Measure A)
    [lam.IsAddHaarMeasure] [SFinite lam] (c : ℝ →+ A) (hc : Continuous c) (F G : A → ℂ)
    (hF : Continuous F) (hG : Continuous G) (hFi : Integrable F lam) (hGi : Integrable G lam)
    (χ : AddChar A ℂ) (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) (f : ℝ)
    (hf : ∀ s : ℝ, χ (c s) = Complex.exp (-(2 * Real.pi * Complex.I * ((s * f : ℝ) : ℂ))))
    (hd : ∀ (b : A) (s : ℝ),
      HasDerivAt (fun t : ℝ => F (b + c t)) (2 * Real.pi * Complex.I * G (b + c s)) s) :
    ∫ b, G b * χ b ∂lam = (f : ℂ) * ∫ b, F b * χ b ∂lam := by
  set K : ℂ := 2 * Real.pi * Complex.I with hK
  have hK0 : K ≠ 0 := by
    simp [hK, Real.pi_ne_zero, Complex.I_ne_zero]
  set e : ℝ → ℂ := fun u => Complex.exp (K * ((u * f : ℝ) : ℂ)) with he
  have hχe : ∀ s : ℝ, χ (-(c s)) = e s := by
    intro s
    rw [← map_neg, hf, he]
    simp only
    congr 1
    push_cast
    ring
  set Fh : ℂ := ∫ b, F b * χ b ∂lam with hFh
  set Gh : ℂ := ∫ b, G b * χ b ∂lam with hGh
  have hec : Continuous e := by
    rw [he]
    fun_prop
  have key : ∀ s : ℝ, (e s - 1) * Fh = K * Gh * ∫ u in (0 : ℝ)..s, e u := by
    intro s
    have hftc : ∀ b : A, F (b + c s) - F b = ∫ u in (0 : ℝ)..s, K * G (b + c u) := by
      intro b
      have hcu : Continuous fun u : ℝ => K * G (b + c u) := by fun_prop
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s)
        (f := fun t : ℝ => F (b + c t)) (f' := fun u => K * G (b + c u))
        (fun x _ => hd b x) (hcu.intervalIntegrable _ _)
      simpa using this.symm
    have hswap := intervalIntegral_integral_swap
      (integrable_uncurry_translate lam c hc hG hGi hχ hn K s)
    have h1 : ∫ b, F (b + c s) * χ b ∂lam = e s * Fh := by
      rw [integral_translate_mul_char, hχe]
    have hi1 : Integrable (fun b => F (b + c s) * χ b) lam :=
      integrable_mul_char (hFi.comp_add_right (c s)) hχ hn
    have hi2 : Integrable (fun b => F b * χ b) lam := integrable_mul_char hFi hχ hn
    have h2 : (e s - 1) * Fh = ∫ b, (∫ u in (0 : ℝ)..s, K * G (b + c u) * χ b) ∂lam := by
      have : (e s - 1) * Fh = ∫ b, (F (b + c s) * χ b - F b * χ b) ∂lam := by
        rw [integral_sub hi1 hi2, h1]
        ring
      rw [this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      rw [intervalIntegral.integral_mul_const, ← hftc b]
      ring
    rw [h2, ← hswap, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    beta_reduce
    have h3 : ∫ b, K * G (b + c u) * χ b ∂lam = K * ∫ b, G (b + c u) * χ b ∂lam := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      ring
    rw [h3, integral_translate_mul_char, hχe]
    ring
  have hL : HasDerivAt (fun s : ℝ => (e s - 1) * Fh) (K * f * Fh) 0 := by
    have h0 : HasDerivAt (fun u : ℝ => K * ((u * f : ℝ) : ℂ)) (K * f) 0 := by
      have : HasDerivAt (fun u : ℝ => ((u : ℂ))) 1 0 := Complex.ofRealCLM.hasDerivAt
      simpa [mul_assoc] using (this.mul_const (f : ℂ)).const_mul K
    have := ((h0.cexp).sub_const 1).mul_const Fh
    simpa [he] using this
  have hR : HasDerivAt (fun s : ℝ => K * Gh * ∫ u in (0 : ℝ)..s, e u) (K * Gh) 0 := by
    have := (hec.integral_hasStrictDerivAt 0 0).hasDerivAt.const_mul (K * Gh)
    simpa [he] using this
  have hEq : (fun s : ℝ => (e s - 1) * Fh) = fun s : ℝ => K * Gh * ∫ u in (0 : ℝ)..s, e u :=
    funext key
  rw [hEq] at hL
  have := hL.unique hR
  have h4 : K * (f * Fh) = K * Gh := by
    rw [← mul_assoc]
    exact this
  exact (mul_left_cancel₀ hK0 h4).symm
end GlobalTheory.CompanionTheory.OneParamFourier
