-- Prove2me | solution 1 for LocalLemma.exp_mul_pow_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:28.830857+00:00
-- url     : https://prove2.me/submissions/d7316fa1-6d11-44b3-92c9-d0bc7ae5c71d

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution (d : ℕ) : 1 ≤ Real.exp 1 * (((d:ℝ) + 1) / ((d:ℝ) + 2)) ^ (d + 1) := by
  set t : ℝ := 1 / ((d:ℝ) + 1) with ht
  have hd : (0:ℝ) < (d:ℝ) + 1 := by positivity
  have h1 : (1 + t) ^ (d + 1) ≤ Real.exp 1 := by
    calc (1 + t) ^ (d + 1) ≤ Real.exp t ^ (d + 1) := by
          gcongr; linarith [Real.add_one_le_exp t]
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; congr 1; rw [ht]; push_cast; field_simp
  have h2 : ((d:ℝ) + 1) / ((d:ℝ) + 2) = (1 + t)⁻¹ := by
    rw [ht]; field_simp; ring
  rw [h2, inv_pow]
  have h3 : 0 < (1 + t) ^ (d + 1) := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ h3]; linarith
end LocalLemma
