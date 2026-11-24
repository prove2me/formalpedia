-- Prove2me | solution 1 for GlobalTheory.PolyOfDeriv.taylor_of_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:27:15.636727+00:00
-- url     : https://prove2.me/submissions/edbd4e2f-1b9b-47ea-b3c7-c3496b51748e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_EqEvalOfDirDerivVanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.PolyOfDeriv
namespace GlobalTheory.PolyOfDeriv
theorem _root_.solution (N : ℕ) : ∀ (G : ℕ → ℝ → ℂ) (_ : ∀ k t, HasDerivAt (G k) (G (k+1) t) t)
    (_ : G N = 0) (t : ℝ),
    G 0 t = ∑ k ∈ Finset.range N, G k 0 * ((t ^ k / k.factorial : ℝ) : ℂ) := by
  induction N with
  | zero => intro G _ hN t; simp [hN]
  | succ N ih =>
    intro G hG hN t
    have h1 : ∀ s, G 1 s = ∑ k ∈ Finset.range N, G (k+1) 0 * ((s ^ k / k.factorial : ℝ) : ℂ) :=
      fun s => ih (fun k => G (k+1)) (fun k t => hG (k+1) t) hN s
    have hm : ∀ (k : ℕ) (s : ℝ), HasDerivAt
        (fun s : ℝ => ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ))
        ((s ^ k / k.factorial : ℝ) : ℂ) s := by
      intro k s
      have h := (hasDerivAt_pow (k+1) s).div_const ((k+1).factorial : ℝ)
      have e : ((k+1 : ℕ) : ℝ) * s ^ (k + 1 - 1) / ((k+1).factorial : ℝ) = s ^ k / k.factorial := by
        rw [Nat.factorial_succ, Nat.add_sub_cancel, Nat.cast_mul]
        have : ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
        have : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
      rw [e] at h
      exact h.ofReal_comp
    have hH : ∀ s, HasDerivAt (fun s => G 0 s - ∑ k ∈ Finset.range N,
        G (k+1) 0 * ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ)) 0 s := by
      intro s
      have h2 : HasDerivAt (fun s : ℝ => ∑ k ∈ Finset.range N,
          G (k+1) 0 * ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ)) (G 1 s) s := by
        rw [h1 s]
        exact HasDerivAt.fun_sum fun k _ => (hm k s).const_mul _
      have h3 := (hG 0 s).fun_sub h2
      rwa [zero_add, sub_self] at h3
    have hc := is_const_of_deriv_eq_zero (fun s => (hH s).differentiableAt)
      (fun s => (hH s).deriv) t 0
    rw [Finset.sum_range_succ']
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
      zero_div, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero, sub_zero] at hc
    rw [← hc]
    simp
end GlobalTheory.PolyOfDeriv
