-- Prove2me | solution 1 for MultimodularDocks.marginal_bike
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:56:24.317769+00:00
-- url     : https://prove2.me/submissions/5c0dbba2-d34a-4810-a038-69d4d041f3f1

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular

set_option autoImplicit false

open MultimodularDocks

namespace MultimodularDocks.BikeProof

theorem iter_mono (φ : ℤ → ℝ) (a : ℤ) (h : ∀ n, a ≤ n → φ n ≤ φ (n + 1)) (n : ℤ) (hn : a ≤ n) :
    φ a ≤ φ n := by
  induction n, hn using Int.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact ih.trans (h k hk)

theorem monoC (g : ℤ → ℤ → ℝ) (h1 : ∀ p q, 1 ≤ p → 0 ≤ q → g p q ≤ g (p + 1) q)
    (h2 : ∀ p q, 1 ≤ p → 0 ≤ q → g p (q + 1) ≤ g p q) (p q P Q : ℤ) (hp : 1 ≤ p) (hpP : p ≤ P)
    (hQ : 0 ≤ Q) (hQq : Q ≤ q) : g p q ≤ g P Q := by
  have e1 : g p q ≤ g P q :=
    iter_mono (fun t => g t q) p (fun n hn => h1 n q (by linarith) (by linarith)) P hpP
  have e2 : -g P Q ≤ -g P q :=
    iter_mono (fun t => -g P t) Q (fun n hn => by
      have := h2 P n (by linarith) (by linarith)
      show -g P n ≤ -g P (n + 1)
      linarith) q hQq
  linarith

end MultimodularDocks.BikeProof

open MultimodularDocks.BikeProof in
theorem solution (f : ℤ → ℤ → ℝ) (hf : IsMultimodular f) (d b d' b' : ℤ)
    (hd : 0 ≤ d) (hb : 0 ≤ b) (hd' : 0 ≤ d') (hb' : 0 ≤ b') :
    (d' + b' ≤ d + b → b < b' → f (d' + 1) (b' - 1) - f d' b' ≤ f d b - f (d - 1) (b + 1)) ∧
      (d + b ≤ d' + b' → b' < b →
        f (d' - 1) (b' + 1) - f d' b' ≤ f d b - f (d + 1) (b - 1)) := by
  let C : ℤ → ℤ → ℝ := fun p q => f p q - f (p - 1) (q + 1)
  have stepP : ∀ p q, 1 ≤ p → 0 ≤ q → C p q ≤ C (p + 1) q := by
    intro p q hp hq
    have h := hf.2.2 p (q + 1) hp (by linarith)
    simp only [add_sub_cancel_right] at h
    show f p q - f (p - 1) (q + 1) ≤ f (p + 1) q - f (p + 1 - 1) (q + 1)
    rw [add_sub_cancel_right]
    linarith
  have stepQ : ∀ p q, 1 ≤ p → 0 ≤ q → C p (q + 1) ≤ C p q := by
    intro p q hp hq
    have h := hf.2.1 p (q + 1) hp (by linarith)
    simp only [add_sub_cancel_right] at h
    show f p (q + 1) - f (p - 1) (q + 1 + 1) ≤ f p q - f (p - 1) (q + 1)
    linarith
  constructor
  · intro hsum hbb
    have := monoC C stepP stepQ (d' + 1) (b' - 1) d b (by linarith) (by linarith) hb (by linarith)
    simp only [C, add_sub_cancel_right, sub_add_cancel] at this
    exact this
  · intro hsum hbb
    have := monoC C stepP stepQ (d + 1) (b - 1) d' b' (by linarith) (by linarith) hb' (by linarith)
    simp only [C, add_sub_cancel_right, sub_add_cancel] at this
    linarith
