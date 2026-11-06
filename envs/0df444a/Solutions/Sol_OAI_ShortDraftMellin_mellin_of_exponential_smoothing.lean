-- Prove2me | solution 1 for OAI.ShortDraftMellin.mellin_of_exponential_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:29:35.01877+00:00
-- url     : https://prove2.me/submissions/d618ceaa-1506-4b06-917d-1ae050e003fe

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftMellin
namespace OAI.ShortDraftMellin
theorem _root_.solution
    (a : ℕ → ℂ) (F : ℝ → ℂ) (s : ℂ)
    (hs : 1 < s.re) (ha0 : a 0 = 0)
    (hF : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasSum (fun n : ℕ => a n * Real.exp (-(n : ℝ) * t)) (F t))
    (hlsum : LSeriesSummable a s) :
    mellin (fun D : ℝ => F D⁻¹) (-s) = Complex.Gamma s * LSeries a s := by
  have hp (n : ℕ) : a n = 0 ∨ 0 < (n : ℝ) := by
    rcases n with _ | n
    · exact Or.inl ha0
    · exact Or.inr (by exact_mod_cast Nat.succ_pos n)
  have hnorm : (fun n : ℕ => ‖a n‖ / (n : ℝ) ^ s.re) =
      fun n : ℕ => ‖LSeries.term a s n‖ := by
    funext n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst n
      simp [ha0]
    · simp [hn]
  have hsum : Summable (fun n : ℕ => ‖a n‖ / (n : ℝ) ^ s.re) := by
    rw [hnorm]
    exact hlsum.norm
  have hM := hasSum_mellin hp (by linarith) hF hsum
  have hterm (n : ℕ) : Complex.Gamma s * a n / (n : ℝ) ^ s =
      Complex.Gamma s * LSeries.term a s n := by
    by_cases hn : n = 0
    · subst n
      simp [ha0, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn]
      simp only [Complex.ofReal_natCast]
      ring
  have hM' : HasSum (fun n : ℕ => Complex.Gamma s * LSeries.term a s n) (mellin F s) := by
    simpa only [hterm] using hM
  have hseries : HasSum (fun n : ℕ => Complex.Gamma s * LSeries.term a s n)
      (Complex.Gamma s * LSeries a s) := by
    simpa only [LSeries] using hlsum.hasSum.mul_left (Complex.Gamma s)
  have heq : mellin F s = Complex.Gamma s * LSeries a s := hM'.unique hseries
  simpa only [mellin_comp_inv, neg_neg] using heq
end OAI.ShortDraftMellin
