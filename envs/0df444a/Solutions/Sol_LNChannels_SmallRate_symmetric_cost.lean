-- Prove2me | solution 1 for LNChannels.SmallRate.symmetric_cost
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:07:34.869431+00:00
-- url     : https://prove2.me/submissions/db80ec7b-952d-4020-8a8e-ffcda94f6f2d

import Mathlib
import Definitions.Def_LNChannels_RateBounds_ClosedForms

set_option autoImplicit false

namespace LNSHelp2

lemma alg (B u v : ℝ) (hu : 1 < u) (hv : 1 < v) :
    B * (u⁻¹ * (1 - u * v) - u * (1 - (u * v)⁻¹)) /
      (u⁻¹ * (1 - u * v) - u * (1 - (u * v)⁻¹) + u * v - (u * v)⁻¹)
      = -(B * (u + v) / ((u - 1) * (v - 1))) := by
  have hu0 : u ≠ 0 := by linarith
  have hv0 : v ≠ 0 := by linarith
  have huv : 1 - u * v ≠ 0 := by nlinarith
  have hu1 : u - 1 ≠ 0 := by linarith
  have hv1 : v - 1 ≠ 0 := by linarith
  have hN : u⁻¹ * (1 - u * v) - u * (1 - (u * v)⁻¹) = (u + v) * (1 - u * v) / (u * v) := by
    field_simp; ring
  have hD : u⁻¹ * (1 - u * v) - u * (1 - (u * v)⁻¹) + u * v - (u * v)⁻¹
      = -((1 - u * v) * (u - 1) * (v - 1)) / (u * v) := by
    field_simp; ring
  rw [hD, hN]
  field_simp

end LNSHelp2

theorem solution (lam r B l₁ l₂ : ℝ) (hlam : 0 < lam) (hr : 0 < r)
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) :
    let a := LNChannels.Exact.alphaPlus lam lam r
    1 < a ∧ LNChannels.RateBounds.biCost lam lam r B l₁ l₂ =
      l₁ + l₂ + B * (a ^ l₁ + a ^ l₂) / ((a ^ l₁ - 1) * (a ^ l₂ - 1)) := by
  show 1 < LNChannels.Exact.alphaPlus lam lam r ∧ LNChannels.RateBounds.biCost lam lam r B l₁ l₂ =
      l₁ + l₂ + B * (LNChannels.Exact.alphaPlus lam lam r ^ l₁ + LNChannels.Exact.alphaPlus lam lam r ^ l₂) /
        ((LNChannels.Exact.alphaPlus lam lam r ^ l₁ - 1) * (LNChannels.Exact.alphaPlus lam lam r ^ l₂ - 1))
  have hD : 0 < r ^ 2 + 4 * r * lam := by positivity
  have hd2 : Real.sqrt (r ^ 2 + 4 * r * lam) ^ 2 = r ^ 2 + 4 * r * lam := Real.sq_sqrt hD.le
  have hdpos : 0 < Real.sqrt (r ^ 2 + 4 * r * lam) := Real.sqrt_pos.2 hD
  have hform : (lam - lam) ^ 2 + r ^ 2 + 2 * r * (lam + lam) = r ^ 2 + 4 * r * lam := by ring
  have hl : lam ≠ 0 := hlam.ne'
  have hap : LNChannels.Exact.alphaPlus lam lam r
      = (2 * lam + r + Real.sqrt (r ^ 2 + 4 * r * lam)) / (2 * lam) := by
    unfold LNChannels.Exact.alphaPlus
    rw [hform]; ring_nf
  have ham : LNChannels.Exact.alphaMinus lam lam r
      = (2 * lam + r - Real.sqrt (r ^ 2 + 4 * r * lam)) / (2 * lam) := by
    unfold LNChannels.Exact.alphaMinus
    rw [hform]; ring_nf
  have hgt : 1 < LNChannels.Exact.alphaPlus lam lam r := by
    rw [hap, lt_div_iff₀ (by positivity)]
    linarith
  have hinv : LNChannels.Exact.alphaMinus lam lam r = (LNChannels.Exact.alphaPlus lam lam r)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [hap, ham, div_mul_div_comm, div_eq_one_iff_eq (by positivity)]
    linear_combination (-1 : ℝ) * hd2
  refine ⟨hgt, ?_⟩
  simp only [LNChannels.RateBounds.biCost]
  generalize LNChannels.Exact.alphaPlus lam lam r = β at hgt hinv ⊢
  rw [hinv]
  have hβ : 0 < β := by linarith
  have hu : 1 < β ^ l₁ := Real.one_lt_rpow hgt hl₁
  have hv : 1 < β ^ l₂ := Real.one_lt_rpow hgt hl₂
  have hadd : β ^ (l₁ + l₂) = β ^ l₁ * β ^ l₂ := Real.rpow_add hβ _ _
  simp only [Real.inv_rpow hβ.le, hadd]
  generalize β ^ l₁ = u at hu ⊢
  generalize β ^ l₂ = v at hv ⊢
  rw [LNSHelp2.alg B u v hu hv]
  ring
