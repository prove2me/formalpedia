-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.VectorTaylor.iter_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:53:23.487812+00:00
-- url     : https://prove2.me/submissions/06a840d2-1447-49ba-8433-8fddb9d6d056

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnalyticOrthogonalVanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.CompanionTheory.VectorTaylor
open Filter Topology
private theorem norm_le_pow_succ_div_factorial_of_deriv_bound (g g' : ℝ → ℂ) (a : ℝ) (n : ℕ)
    (hg : ∀ σ, HasDerivAt g (g' σ) σ) (hg0 : g 0 = 0)
    (hb : ∀ σ, 0 ≤ σ → ‖g' σ‖ ≤ a * σ ^ n / n.factorial) (x : ℝ) (hx : 0 ≤ x) :
    ‖g x‖ ≤ a * x ^ (n + 1) / (n + 1).factorial := by
  have hB : ∀ σ, HasDerivAt (fun σ : ℝ => a * σ ^ (n + 1) / (n + 1).factorial)
      (a * σ ^ n / n.factorial) σ := by
    intro σ
    have h := ((hasDerivAt_pow (n + 1) σ).const_mul a).div_const ((n + 1).factorial : ℝ)
    refine h.congr_deriv ?_
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := g) (f' := g') (a := 0) (b := x)
    (fun σ _ => (hg σ).continuousAt.continuousWithinAt)
    (fun σ _ => (hg σ).hasDerivWithinAt) (by simp [hg0]) hB
    (fun σ hσ => hb σ hσ.1) ⟨hx, le_rfl⟩
end GlobalTheory.CompanionTheory.VectorTaylor
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VectorTaylor
open Filter Topology
namespace GlobalTheory.CompanionTheory.VectorTaylor
theorem _root_.solution (f : ℕ → ℝ → ℂ) (A : ℕ → ℝ)
    (hd : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t)
    (hb : ∀ k t, ‖f k t‖ ≤ A k) (t₀ : ℝ) (h0 : ∀ k, f k t₀ = 0) (n : ℕ) :
    ∀ k s, ‖f k (t₀ + s)‖ ≤ A (k + n) * |s| ^ n / n.factorial := by
  induction n with
  | zero =>
    intro k s
    simpa using hb k (t₀ + s)
  | succ n ih =>
    intro k s
    have hA : A (k + 1 + n) = A (k + (n + 1)) := by congr 1; omega
    rcases le_total 0 s with hs | hs
    · have h := norm_le_pow_succ_div_factorial_of_deriv_bound (fun σ => f k (t₀ + σ)) (fun σ => f (k + 1) (t₀ + σ))
        (A (k + (n + 1))) n (fun σ => (hd k (t₀ + σ)).comp_const_add t₀ σ) (by simpa using h0 k)
        (fun σ hσ => by
          have := ih (k + 1) σ
          rwa [hA, abs_of_nonneg hσ] at this) s hs
      rwa [abs_of_nonneg hs]
    · have h := norm_le_pow_succ_div_factorial_of_deriv_bound (fun σ => f k (t₀ - σ)) (fun σ => -f (k + 1) (t₀ - σ))
        (A (k + (n + 1))) n (fun σ => (hd k (t₀ - σ)).comp_const_sub t₀ σ) (by simpa using h0 k)
        (fun σ hσ => by
          have := ih (k + 1) (-σ)
          rw [hA, abs_neg, abs_of_nonneg hσ, ← sub_eq_add_neg] at this
          rwa [norm_neg]) (-s) (by linarith)
      rw [abs_of_nonpos hs]
      simpa [sub_neg_eq_add] using h
end GlobalTheory.CompanionTheory.VectorTaylor
