-- Prove2me | solution 1 for GlobalTheory.torus_elliptic_system_solvable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:04:18.616055+00:00
-- url     : https://prove2.me/submissions/d2324492-dd9e-4911-af87-d86562ae23cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRapidFourierSeriesOfIntPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FourierCoeffEqZeroOfTsumEqZeroFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorusEllipticSystemSolvable
import Theorems.Thm_GlobalTheory_TorusElliptic_ch_periodic
import Theorems.Thm_GlobalTheory_TorusElliptic_Rapid_summable
import Theorems.Thm_GlobalTheory_TorusElliptic_summable_ch
import Theorems.Thm_GlobalTheory_TorusElliptic_summable_symb
import Theorems.Thm_GlobalTheory_TorusElliptic_sum_fderiv
import Theorems.Thm_GlobalTheory_TorusElliptic_symbol_lower
import Theorems.Thm_GlobalTheory_contDiff_and_fderiv_tsum_fourier_of_rapid
import Theorems.Thm_GlobalTheory_exists_rapid_fourierSeries_of_int_periodic
import Theorems.Thm_GlobalTheory_fourier_coeff_eq_zero_of_tsum_eq_zero_fin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open TorusElliptic
namespace GlobalTheory
theorem _root_.solution : ∀ (n m : ℕ) (p : Fin m → Fin n → ℂ), (∀ ξ : Fin n → ℝ, (∀ a, ∑ k, p a k * (ξ k : ℂ) = 0) → ξ = 0) → ∀ w : Fin m → (Fin n → ℝ) → ℂ, (∀ a, ContDiff ℝ ∞ (w a) ∧ (∀ (ν : Fin n → ℤ) x, w a (x + fun k => (ν k : ℝ)) = w a x)) → (∀ a b x, ∑ k, p a k * fderiv ℝ (w b) x (Pi.single k 1) = ∑ k, p b k * fderiv ℝ (w a) x (Pi.single k 1)) → ∃ (t : Fin m → ℂ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ f ∧ (∀ (ν : Fin n → ℤ) x, f (x + fun k => (ν k : ℝ)) = f x) ∧ ∀ a x, ∑ k, p a k * fderiv ℝ f x (Pi.single k 1) = w a x - t a := by
  classical
  intro n m p hp w hw hcomp
  choose c hc hwc using fun a => GlobalTheory.exists_rapid_fourierSeries_of_int_periodic n (w a) (hw a).1 (hw a).2
  have hc' : ∀ a, Rapid (c a) := hc
  have hwf : ∀ a, w a = fun x => ∑' ν, c a ν * ch ν x := fun a => funext (hwc a)
  have h2pi : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hsym : ∀ a b ν, (∑ k, p a k * (ν k : ℂ)) * c b ν = (∑ k, p b k * (ν k : ℂ)) * c a ν := by
    intro a b ν
    have hs1 := summable_symb (hc' b) (p a)
    have hs2 := summable_symb (hc' a) (p b)
    have := GlobalTheory.fourier_coeff_eq_zero_of_tsum_eq_zero_fin n (fun ν => 2 * π * I * (∑ k, p a k * (ν k : ℂ)) * c b ν
      - 2 * π * I * (∑ k, p b k * (ν k : ℂ)) * c a ν)
      (summable_norm_iff.2 (hs1.of_norm.sub hs2.of_norm)) (fun x => by
        have h := hcomp a b x
        rw [hwf a, hwf b, sum_fderiv (hc' b), sum_fderiv (hc' a)] at h
        have h' := (summable_ch hs1 x).tsum_sub (summable_ch hs2 x)
        rw [h, sub_self] at h'
        rw [← h']
        exact tsum_congr fun ν => by unfold ch; ring) ν
    apply mul_left_cancel₀ h2pi
    linear_combination this
  obtain ⟨ε, hε, hlow⟩ := symbol_lower p hp
  choose α hα using hlow
  let d : (Fin n → ℤ) → ℂ := fun ν =>
    if h : ν = 0 then 0 else c (α ν h) ν / (2 * π * I * ∑ k, p (α ν h) k * (ν k : ℂ))
  have hd : Rapid d := by
    intro N
    choose C hC using fun a => hc' a N
    have hC0 : ∀ a, 0 ≤ C a := fun a => le_trans (by positivity) (hC a 0)
    refine ⟨(∑ a, C a) / (‖(2 * π * I : ℂ)‖ * ε), fun ν => ?_⟩
    have hn : 0 < ‖(2 * π * I : ℂ)‖ := norm_pos_iff.2 h2pi
    have hS : 0 ≤ ∑ a, C a := Finset.sum_nonneg fun a _ => hC0 a
    by_cases h : ν = 0
    · simp only [d, dif_pos h, norm_zero, zero_mul]
      positivity
    · simp only [d, dif_neg h]
      rw [norm_div, norm_mul (2 * π * I : ℂ), div_mul_eq_mul_div]
      have h1 := Finset.single_le_sum (f := C) (fun a _ => hC0 a) (Finset.mem_univ (α ν h))
      have h2 := hα ν h
      have h3 := hC (α ν h) ν
      gcongr
      linarith
  refine ⟨fun a => c a 0, fun x => ∑' ν, d ν * ch ν x, (GlobalTheory.contDiff_and_fderiv_tsum_fourier_of_rapid n d hd).1, ?_, ?_⟩
  · intro μ x
    simp only [ch_periodic]
  · intro a x
    rw [sum_fderiv hd, hwf a]
    have hs := summable_ch (hc' a).summable x
    have h0 := hs.tsum_eq_add_tsum_ite 0
    have hch : ch (0 : Fin n → ℤ) x = 1 := by simp [ch]
    rw [hch, mul_one] at h0
    simp only []
    rw [h0, add_sub_cancel_left]
    refine tsum_congr fun ν => ?_
    by_cases h : ν = 0
    · simp only [d, dif_pos h, if_pos h, mul_zero, zero_mul]
    · simp only [d, dif_neg h, if_neg h]
      have h2 : (∑ k, p (α ν h) k * (ν k : ℂ)) ≠ 0 := by
        intro h0
        have := hα ν h
        rw [h0, norm_zero] at this
        linarith
      have h3 := hsym a (α ν h) ν
      congr 1
      rw [mul_div_assoc', div_eq_iff (mul_ne_zero h2pi h2)]
      linear_combination (2 * π * I) * h3
end GlobalTheory
