-- Prove2me | solution 1 for MultimodularDocks.marginal_dock
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:58:32.00216+00:00
-- url     : https://prove2.me/submissions/400ef634-af31-4c41-83b7-f117b8d6e0d7

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular

set_option autoImplicit false

open MultimodularDocks

namespace MultimodularDocks.DockProof

theorem iter_mono (φ : ℤ → ℝ) (a : ℤ) (h : ∀ n, a ≤ n → φ n ≤ φ (n + 1)) (n : ℤ) (hn : a ≤ n) :
    φ a ≤ φ n := by
  induction n, hn using Int.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact ih.trans (h k hk)

theorem mono2 (g : ℤ → ℤ → ℝ) (h1 : ∀ p q, 0 ≤ p → 0 ≤ q → g p q ≤ g (p + 1) q)
    (h2 : ∀ p q, 0 ≤ p → 0 ≤ q → g p q ≤ g p (q + 1))
    (h3 : ∀ p q, 0 ≤ p → 0 ≤ q → g p (q + 1) ≤ g (p + 1) q)
    (p q P Q : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hQ : 0 ≤ Q) (hpP : p ≤ P) (hsum : p + q ≤ P + Q) :
    g p q ≤ g P Q := by
  by_cases hqQ : q ≤ Q
  · calc g p q ≤ g P q :=
          iter_mono (fun t => g t q) p (fun n hn => h1 n q (by linarith) hq) P hpP
      _ ≤ g P Q :=
          iter_mono (fun t => g P t) q (fun n hn => h2 P n (by linarith) (by linarith)) Q hqQ
  · push Not at hqQ
    have hanti : ∀ k : ℤ, 0 ≤ k → ∀ p, 0 ≤ p → g p (Q + k) ≤ g (p + k) Q := by
      intro k hk
      induction k, hk using Int.le_induction with
      | base =>
        intro p _
        simp
      | succ k hk ih =>
        intro p hp
        calc g p (Q + (k + 1)) = g p (Q + k + 1) := by rw [add_assoc]
          _ ≤ g (p + 1) (Q + k) := h3 p (Q + k) hp (by linarith)
          _ ≤ g (p + 1 + k) Q := ih (p + 1) (by linarith)
          _ = g (p + (k + 1)) Q := by congr 1; ring
    have e1 := hanti (q - Q) (by linarith) p hp
    rw [show Q + (q - Q) = q by ring] at e1
    calc g p q ≤ g (p + (q - Q)) Q := e1
      _ ≤ g P Q := iter_mono (fun t => g t Q) (p + (q - Q))
          (fun n hn => h1 n Q (by linarith) hQ) P (by linarith)

end MultimodularDocks.DockProof

open MultimodularDocks.DockProof in
theorem solution (f : ℤ → ℤ → ℝ) (hf : IsMultimodular f) (d b d' b' : ℤ)
    (hd : 0 ≤ d) (hb : 0 ≤ b) (hd' : 0 ≤ d') (hb' : 0 ≤ b') :
    (d < d' → d + b < d' + b' → f (d' - 1) b' - f d' b' ≤ f d b - f (d + 1) b) ∧
      (d' < d → d' + b' < d + b → f (d - 1) b - f d b ≤ f d' b' - f (d' + 1) b') ∧
      (b < b' → d + b < d' + b' → f d' (b' - 1) - f d' b' ≤ f d b - f d (b + 1)) ∧
      (b' < b → d' + b' < d + b → f d (b - 1) - f d b ≤ f d' b' - f d' (b' + 1)) := by
  let B : ℤ → ℤ → ℝ := fun p q => f (p + 1) q - f p q
  let A : ℤ → ℤ → ℝ := fun p q => f p (q + 1) - f p q
  have Bb : ∀ p q, 0 ≤ p → 0 ≤ q → B p q ≤ B p (q + 1) := by
    intro p q hp hq
    have h := hf.1 p q hp hq
    show f (p + 1) q - f p q ≤ f (p + 1) (q + 1) - f p (q + 1)
    linarith
  have Banti : ∀ p q, 0 ≤ p → 0 ≤ q → B p (q + 1) ≤ B (p + 1) q := by
    intro p q hp hq
    have h := hf.2.2 (p + 1) (q + 1) (by linarith) (by linarith)
    simp only [add_sub_cancel_right] at h
    show f (p + 1) (q + 1) - f p (q + 1) ≤ f (p + 1 + 1) q - f (p + 1) q
    linarith
  have Bd : ∀ p q, 0 ≤ p → 0 ≤ q → B p q ≤ B (p + 1) q := fun p q hp hq =>
    (Bb p q hp hq).trans (Banti p q hp hq)
  have Ad : ∀ p q, 0 ≤ p → 0 ≤ q → A p q ≤ A (p + 1) q := by
    intro p q hp hq
    have h := hf.1 p q hp hq
    show f p (q + 1) - f p q ≤ f (p + 1) (q + 1) - f (p + 1) q
    linarith
  have Aanti : ∀ p q, 0 ≤ p → 0 ≤ q → A (p + 1) q ≤ A p (q + 1) := by
    intro p q hp hq
    have h := hf.2.1 (p + 1) (q + 1) (by linarith) (by linarith)
    simp only [add_sub_cancel_right] at h
    show f (p + 1) (q + 1) - f (p + 1) q ≤ f p (q + 1 + 1) - f p (q + 1)
    linarith
  have Ab : ∀ p q, 0 ≤ p → 0 ≤ q → A p q ≤ A p (q + 1) := fun p q hp hq =>
    (Ad p q hp hq).trans (Aanti p q hp hq)
  have Bmono := mono2 B Bd Bb Banti
  have Amono := mono2 (fun q p => A p q) (fun q p hq hp => Ab p q hp hq)
    (fun q p hq hp => Ad p q hp hq) (fun q p hq hp => Aanti p q hp hq)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2
    have := Bmono d b (d' - 1) b' hd hb hb' (by linarith) (by linarith)
    simp only [B, sub_add_cancel] at this
    linarith
  · intro h1 h2
    have := Bmono d' b' (d - 1) b hd' hb' hb (by linarith) (by linarith)
    simp only [B, sub_add_cancel] at this
    linarith
  · intro h1 h2
    have := Amono b d (b' - 1) d' hb hd hd' (by linarith) (by linarith)
    simp only [A, sub_add_cancel] at this
    linarith
  · intro h1 h2
    have := Amono b' d' (b - 1) d hb' hd' hd (by linarith) (by linarith)
    simp only [A, sub_add_cancel] at this
    linarith
