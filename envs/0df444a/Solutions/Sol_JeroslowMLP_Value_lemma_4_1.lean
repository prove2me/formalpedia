-- Prove2me | solution 1 for JeroslowMLP.Value.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:19:50.534182+00:00
-- url     : https://prove2.me/submissions/3f3dcb13-4bfe-4b1e-b46e-54a2cd417ea4

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Formula

set_option autoImplicit false
open JeroslowMLP.Value

lemma JML41_neg (δ lG v vG : ℝ) (b : Bool) (hδ : 0 < δ) (hl : 0 ≤ lG) (hx : v = 1 - vG)
    (h : |vG - (if b = true then 1 else 0)| < δ * lG) :
    |v - (if (!b) = true then (1:ℝ) else 0)| < δ * (lG + 1) := by
  cases b <;> simp at h ⊢ <;> rw [abs_lt] at h ⊢ <;> constructor <;> nlinarith [h.1, h.2]

lemma JML41_and (δ lG lH v vG vH : ℝ) (b c : Bool) (hδ : 0 < δ) (hl : 0 ≤ lG) (hl' : 0 ≤ lH)
    (hvG : v ≤ vG) (hvH : v ≤ vH) (hs : vG + vH - 1 ≤ v) (h0 : 0 ≤ v) (h1 : v ≤ 1)
    (g1 : vG ≤ 1) (k1 : vH ≤ 1)
    (g2 : |vG - (if b = true then 1 else 0)| < δ * lG)
    (k2 : |vH - (if c = true then 1 else 0)| < δ * lH) :
    |v - (if (b && c) = true then (1:ℝ) else 0)| < δ * (lG + lH + 1) := by
  have m1 := mul_nonneg hδ.le hl
  have m2 := mul_nonneg hδ.le hl'
  cases b <;> cases c <;> simp at g2 k2 ⊢ <;> rw [abs_lt] at g2 k2 ⊢ <;>
    constructor <;> nlinarith [g2.1, g2.2, k2.1, k2.2]

lemma JML41_or (δ lG lH v vG vH : ℝ) (b c : Bool) (hδ : 0 < δ) (hl : 0 ≤ lG) (hl' : 0 ≤ lH)
    (hvG : vG ≤ v) (hvH : vH ≤ v) (hs : v ≤ vG + vH) (h0 : 0 ≤ v) (h1 : v ≤ 1)
    (g1 : vG ≤ 1) (k1 : vH ≤ 1)
    (g2 : |vG - (if b = true then 1 else 0)| < δ * lG)
    (k2 : |vH - (if c = true then 1 else 0)| < δ * lH) :
    |v - (if (b || c) = true then (1:ℝ) else 0)| < δ * (lG + lH + 1) := by
  have m1 := mul_nonneg hδ.le hl
  have m2 := mul_nonneg hδ.le hl'
  cases b <;> cases c <;> simp at g2 k2 ⊢ <;> rw [abs_lt] at g2 k2 ⊢ <;>
    constructor <;> nlinarith [g2.1, g2.2, k2.1, k2.2]

lemma JML41_aux {α : Type} (δ : ℝ) (hδ : 0 < δ) (x₀ : α → Bool) (xa : α → ℝ) :
    ∀ (G : Formula α) (xn : G.Node → ℝ),
      (∀ a ∈ G.atoms, |xa a - (if x₀ a then 1 else 0)| < δ) → G.LSys xa xn →
      0 ≤ G.nodeVal xa xn ∧ G.nodeVal xa xn ≤ 1 ∧
      |G.nodeVal xa xn - (if G.eval x₀ then 1 else 0)| < δ * (G.length : ℝ) := by
  intro G
  induction G with
  | var a =>
    intro xn h49 hsys
    have h := h49 a (by simp [Formula.atoms])
    refine ⟨hsys.1, hsys.2, ?_⟩
    show |xa a - (if x₀ a = true then 1 else 0)| < δ * ((1 : ℕ) : ℝ)
    rw [Nat.cast_one, mul_one]
    exact h
  | neg G ih =>
    intro xn h49 hsys
    obtain ⟨hG, hx, h0, h1⟩ := hsys
    obtain ⟨i0, i1, i2⟩ := ih (fun g => xn (some g)) (by
      intro a ha; exact h49 a (by simpa [Formula.atoms] using ha)) hG
    refine ⟨h0, h1, ?_⟩
    have := JML41_neg δ (G.length : ℝ) (xn none) (G.nodeVal xa fun g => xn (some g))
      (G.eval x₀) hδ (Nat.cast_nonneg _) hx i2
    show |xn none - (if (!G.eval x₀) = true then 1 else 0)| < δ * ((G.length + 1 : ℕ) : ℝ)
    rw [Nat.cast_add, Nat.cast_one]
    exact this
  | and G H ihG ihH =>
    intro xn h49 hsys
    obtain ⟨hG, hH, hxG, hxH, hxs, h0, h1⟩ := hsys
    obtain ⟨g0, g1, g2⟩ := ihG (fun g => xn (some (Sum.inl g))) (by
      intro a ha; exact h49 a (by simp [Formula.atoms, ha])) hG
    obtain ⟨k0, k1, k2⟩ := ihH (fun g => xn (some (Sum.inr g))) (by
      intro a ha; exact h49 a (by simp [Formula.atoms, ha])) hH
    refine ⟨h0, h1, ?_⟩
    have := JML41_and δ (G.length : ℝ) (H.length : ℝ) (xn none)
      (G.nodeVal xa fun g => xn (some (Sum.inl g))) (H.nodeVal xa fun g => xn (some (Sum.inr g)))
      (G.eval x₀) (H.eval x₀) hδ (Nat.cast_nonneg _) (Nat.cast_nonneg _) hxG hxH hxs h0 h1 g1 k1 g2 k2
    show |xn none - (if (G.eval x₀ && H.eval x₀) = true then 1 else 0)| <
      δ * ((G.length + H.length + 1 : ℕ) : ℝ)
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
    exact this
  | or G H ihG ihH =>
    intro xn h49 hsys
    obtain ⟨hG, hH, hxs, hxG, hxH, h0, h1⟩ := hsys
    obtain ⟨g0, g1, g2⟩ := ihG (fun g => xn (some (Sum.inl g))) (by
      intro a ha; exact h49 a (by simp [Formula.atoms, ha])) hG
    obtain ⟨k0, k1, k2⟩ := ihH (fun g => xn (some (Sum.inr g))) (by
      intro a ha; exact h49 a (by simp [Formula.atoms, ha])) hH
    refine ⟨h0, h1, ?_⟩
    have := JML41_or δ (G.length : ℝ) (H.length : ℝ) (xn none)
      (G.nodeVal xa fun g => xn (some (Sum.inl g))) (H.nodeVal xa fun g => xn (some (Sum.inr g)))
      (G.eval x₀) (H.eval x₀) hδ (Nat.cast_nonneg _) (Nat.cast_nonneg _) hxG hxH hxs h0 h1 g1 k1 g2 k2
    show |xn none - (if (G.eval x₀ || H.eval x₀) = true then 1 else 0)| <
      δ * ((G.length + H.length + 1 : ℕ) : ℝ)
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
    exact this

theorem solution {α : Type} (G : Formula α) (δ γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hδγ : δ * (G.length : ℝ) ≤ γ) (x₀ : α → Bool) (xa : α → ℝ) (xn : G.Node → ℝ)
    (h49 : ∀ a ∈ G.atoms, |xa a - (if x₀ a then 1 else 0)| < δ)
    (hsys : G.LSys xa xn) :
    |G.nodeVal xa xn - (if G.eval x₀ then 1 else 0)| < γ := by
  obtain ⟨-, -, h⟩ := JML41_aux δ hδ x₀ xa G xn h49 hsys
  linarith
