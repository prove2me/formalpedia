-- Prove2me | solution 1 for GlobalTheory.schur_block_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:51.038673+00:00
-- url     : https://prove2.me/submissions/8eaac13b-a2a1-4642-95b2-7b23cf25e9ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SchurComplementBlockQuadraticLowerBound
import Theorems.Thm_GlobalTheory_schur_scalar_bound
import Theorems.Thm_GlobalTheory_dot_sq_le
import Theorems.Thm_P2M_GlobalTheory_dot_self_nonneg__607dd4203c70

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k l : ℕ) (a bt : Matrix (Fin k) (Fin k) ℝ) (b : Matrix (Fin k) (Fin l) ℝ) (d : Matrix (Fin l) (Fin l) ℝ) (C₀ c₀ b₀ : ℝ), 0 ≤ C₀ → 0 < c₀ → 0 < b₀ → a.IsSymm → d.IsSymm → bt.IsSymm → (∀ x, |x ⬝ᵥ a.mulVec x| ≤ C₀ * (x ⬝ᵥ x)) → (∀ y, (b.mulVec y) ⬝ᵥ (b.mulVec y) ≤ C₀ ^ 2 * (y ⬝ᵥ y)) → (∀ y, c₀ * (y ⬝ᵥ y) ≤ y ⬝ᵥ d.mulVec y) → (∀ x, b₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ bt.mulVec x) → ∀ z : Fin k ⊕ Fin l → ℝ, ((1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀))⁻¹ * (z ⬝ᵥ z) ≤ z ⬝ᵥ (Matrix.fromBlocks (a + ((1 + C₀ + C₀ ^ 2 / c₀) / b₀) • bt) b b.transpose d).mulVec z := by
  intro k l a bt b d C₀ c₀ b₀ hC hc hb _ _ _ ha hbb hd hbt z
  set x : Fin k → ℝ := z ∘ Sum.inl with hx
  set y : Fin l → ℝ := z ∘ Sum.inr with hy
  set L := (1 + C₀ + C₀ ^ 2 / c₀) / b₀ with hL
  have hsum : ∀ (f g : Fin k ⊕ Fin l → ℝ), f ⬝ᵥ g = (f ∘ Sum.inl) ⬝ᵥ (g ∘ Sum.inl) + (f ∘ Sum.inr) ⬝ᵥ (g ∘ Sum.inr) := by
    intro f g; simp [dotProduct, Fintype.sum_sum_type]
  have htr : y ⬝ᵥ b.transpose.mulVec x = x ⬝ᵥ b.mulVec y := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have hexp : z ⬝ᵥ (Matrix.fromBlocks (a + L • bt) b b.transpose d).mulVec z
      = x ⬝ᵥ a.mulVec x + L * (x ⬝ᵥ bt.mulVec x) + 2 * (x ⬝ᵥ b.mulVec y) + y ⬝ᵥ d.mulVec y := by
    rw [hsum, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [← hx, ← hy, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_add, dotProduct_add,
      dotProduct_smul, htr, smul_eq_mul]
    ring
  have hzz : z ⬝ᵥ z = x ⬝ᵥ x + y ⬝ᵥ y := hsum z z
  rw [hexp, hzz]
  set U := x ⬝ᵥ x
  set W := y ⬝ᵥ y
  have hU : 0 ≤ U := dot_self_nonneg' k x
  have hW : 0 ≤ W := dot_self_nonneg' l y
  set u := Real.sqrt U
  set w := Real.sqrt W
  have hu : u ^ 2 = U := Real.sq_sqrt hU
  have hw : w ^ 2 = W := Real.sq_sqrt hW
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _

  have hQ : |x ⬝ᵥ b.mulVec y| ≤ C₀ * u * w := by
    have h1 := dot_sq_le k x (b.mulVec y)
    have h2 := hbb y
    have h3 : (x ⬝ᵥ b.mulVec y) ^ 2 ≤ (C₀ * u * w) ^ 2 := by
      calc (x ⬝ᵥ b.mulVec y) ^ 2 ≤ U * (b.mulVec y ⬝ᵥ b.mulVec y) := h1
        _ ≤ U * (C₀ ^ 2 * W) := mul_le_mul_of_nonneg_left h2 hU
        _ = (C₀ * u * w) ^ 2 := by rw [← hu, ← hw]; ring
    exact abs_le_of_sq_le_sq' h3 (by positivity) |>.2 |> fun h => abs_le.mpr ⟨(abs_le_of_sq_le_sq' h3 (by positivity)).1, h⟩
  have hT : -(C₀ * U) ≤ x ⬝ᵥ a.mulVec x := by
    have := ha x; exact (abs_le.mp this).1
  have hB : (1 + C₀ + C₀ ^ 2 / c₀) * U ≤ L * (x ⬝ᵥ bt.mulVec x) := by
    have h := hbt x
    have hL0 : 0 ≤ L := by rw [hL]; positivity
    calc (1 + C₀ + C₀ ^ 2 / c₀) * U = L * (b₀ * U) := by rw [hL]; field_simp
      _ ≤ L * (x ⬝ᵥ bt.mulVec x) := mul_le_mul_of_nonneg_left h hL0
  have hD := hd y
  have hQ' := (abs_le.mp hQ).1
  have key := schur_scalar_bound u w C₀ c₀ hC hc
  have hK : 0 < (1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀) := by
    have : 0 < 1 + C₀ / c₀ := by have := div_nonneg hC hc.le; linarith
    exact mul_pos (pow_pos this 2) (lt_of_lt_of_le one_pos (le_max_left _ _))
  rw [inv_mul_le_iff₀ hK]
  have hS : (1 + C₀ ^ 2 / c₀) * u ^ 2 - 2 * C₀ * u * w + c₀ * w ^ 2 ≤
      x ⬝ᵥ a.mulVec x + L * (x ⬝ᵥ bt.mulVec x) + 2 * (x ⬝ᵥ b.mulVec y) + y ⬝ᵥ d.mulVec y := by
    rw [hu, hw]; nlinarith
  calc U + W = u ^ 2 + w ^ 2 := by rw [hu, hw]
    _ ≤ _ := key
    _ ≤ _ := mul_le_mul_of_nonneg_left hS hK.le
end GlobalTheory
