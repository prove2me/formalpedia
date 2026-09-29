-- Prove2me | solution 1 for MegiddoLP.FixedDim.optimal_set_one_side
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:59:06.631055+00:00
-- url     : https://prove2.me/submissions/6690f803-1c5c-49ca-983f-fe76fcfb99ce

import Mathlib
import Definitions.Def_Polyhedron

open Matrix LinearOptimization

namespace MegiddoLP.FixedDim

theorem aux_osos_convex {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ)
    (c : Fin d → ℝ) (x y : Fin d → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : IsLpOptimal c (polyhedron A b) x) (hy : IsLpOptimal c (polyhedron A b) y) :
    IsLpOptimal c (polyhedron A b) (t • x + (1 - t) • y) := by
  obtain ⟨hxS, hxo⟩ := hx
  obtain ⟨hyS, hyo⟩ := hy
  have hxy : c ⬝ᵥ x = c ⬝ᵥ y := le_antisymm (hxo y hyS) (hyo x hxS)
  refine ⟨?_, ?_⟩
  · simp only [polyhedron, Set.mem_ofPred_eq] at hxS hyS ⊢
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    intro i
    have h1 := hxS i
    have h2 := hyS i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 ht0,
      mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr ht1)]
  · intro w hw
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hxy]
    have := hxo w hw
    nlinarith

end MegiddoLP.FixedDim

open Matrix LinearOptimization
open MegiddoLP.FixedDim

theorem solution {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ)
    (c a : Fin d → ℝ) (β : ℝ)
    (hmiss : ∀ x, IsLpOptimal c (polyhedron A b) x → a ⬝ᵥ x ≠ β) :
    (∀ x, IsLpOptimal c (polyhedron A b) x → a ⬝ᵥ x < β) ∨
    (∀ x, IsLpOptimal c (polyhedron A b) x → β < a ⬝ᵥ x) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x, hx, hxβ⟩, ⟨y, hy, hyβ⟩⟩ := hcon
  have hx' : β < a ⬝ᵥ x := lt_of_le_of_ne hxβ (Ne.symm (hmiss x hx))
  have hy' : a ⬝ᵥ y < β := lt_of_le_of_ne hyβ (hmiss y hy)
  set t : ℝ := (β - a ⬝ᵥ y) / (a ⬝ᵥ x - a ⬝ᵥ y) with ht
  have hpos : 0 < a ⬝ᵥ x - a ⬝ᵥ y := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hpos.le
  have ht1 : t ≤ 1 := (div_le_one hpos).mpr (by linarith)
  have hz := aux_osos_convex A b c x y t ht0 ht1 hx hy
  apply hmiss _ hz
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have : t * (a ⬝ᵥ x - a ⬝ᵥ y) = β - a ⬝ᵥ y := by
    rw [ht]; field_simp
  nlinarith
