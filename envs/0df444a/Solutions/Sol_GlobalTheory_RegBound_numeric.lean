-- Prove2me | solution 1 for GlobalTheory.RegBound.numeric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:55:20.786252+00:00
-- url     : https://prove2.me/submissions/8b0a7081-c325-4a4d-b87c-a678f38b8fd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
namespace GlobalTheory.RegBound
theorem _root_.solution {g : ℕ → ℚ} {δ : ℕ → ℕ} {d B : ℕ} (h1 : ∀ e ≥ d, g (e + 1) = g e - δ (e + 1))
    (h2 : ∀ᶠ e in atTop, g e = 0) (h3 : g d ≤ B) (h4 : ∀ e ≥ d, δ e = 0 → δ (e + 1) = 0) :
    ∀ e ≥ d + B + 1, δ e = 0 ∧ g e = 0 := by
  have mono : ∀ e ≥ d, ∀ e' ≥ e, g e' ≤ g e := by
    intro e he e' he'
    induction e', he' using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
      rw [h1 n (he.trans hn)]
      have : (0 : ℚ) ≤ δ (n + 1) := Nat.cast_nonneg _
      linarith
  have nonneg : ∀ e ≥ d, 0 ≤ g e := by
    intro e he
    obtain ⟨e', h, h'⟩ := (h2.and (eventually_ge_atTop e)).exists
    exact h ▸ mono e he e' h'
  have prop : ∀ e ≥ d, δ e = 0 → ∀ e' ≥ e, δ e' = 0 := by
    intro e he h e' he'
    induction e', he' using Nat.le_induction with
    | base => exact h
    | succ n hn ih => exact h4 n (he.trans hn) ih
  have dec : ∀ k : ℕ, δ (d + k) ≠ 0 → g (d + k) ≤ g d - k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have h5 := ih fun h => hk (h4 (d + k) (Nat.le_add_right _ _) h)
      have h6 : (1 : ℚ) ≤ δ (d + k + 1) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
      rw [← add_assoc, h1 _ (by omega)]
      push_cast
      linarith
  have z : δ (d + (B + 1)) = 0 := by
    by_contra h
    have := dec _ h
    have := nonneg (d + (B + 1)) (by omega)
    push_cast at *
    linarith
  intro e he
  refine ⟨prop _ (by omega) z e (by omega), ?_⟩
  have const : ∀ e' ≥ e, g e' = g e := by
    intro e' he'
    induction e', he' using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [h1 n (by omega), prop _ (by omega) z (n + 1) (by omega), ih]; simp
  obtain ⟨e', h, h'⟩ := (h2.and (eventually_ge_atTop e)).exists
  rw [← const e' h', h]
end GlobalTheory.RegBound
