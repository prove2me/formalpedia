-- Prove2me | solution 1 for GlobalTheory.JacobiTriple.finTriple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:47:48.274277+00:00
-- url     : https://prove2.me/submissions/3e957a01-9a35-43d0-b90f-a675c37b81bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QBinomialFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleFiniteProduct
import Theorems.Thm_GlobalTheory_JacobiTriple_finTriple_sum_odd
import Theorems.Thm_GlobalTheory_JacobiTriple_finTriple_term
import Theorems.Thm_GlobalTheory_T_prod_range_one_add_mul_pow_two_mul_eq_sum_qBinom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real
open GlobalTheory GlobalTheory.JacobiTriple
namespace GlobalTheory.JacobiTriple
theorem _root_.solution (s x : ℂ) (hs : s ≠ 0) (hs1 : ‖s‖ < 1) (hx : x ≠ 0) (n : ℕ) :
    ∏ k ∈ Finset.range n, ((1 + x * s ^ (2 * k + 1)) * (1 + x⁻¹ * s ^ (2 * k + 1))) =
      ∑ j ∈ Finset.Icc (-(n : ℤ)) n, finCoeff (s ^ 2) n j * (x ^ j * s ^ (j ^ 2)) := by
  set X := x * s ^ ((1 : ℤ) - 2 * n) with hX
  have ha : ∀ k ∈ Finset.range n, 1 + x * s ^ (2 * k + 1) = 1 + X * s ^ (2 * (n + k)) := by
    intro k _
    rw [hX, mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hs]
    congr 3
    push_cast; ring
  have hb : ∀ k ∈ Finset.range n, 1 + x⁻¹ * s ^ (2 * k + 1) =
      (x⁻¹ * s ^ (2 * k + 1)) * (1 + X * s ^ (2 * (n - 1 - k))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have e : ((2 * k + 1 : ℕ) : ℤ) + (1 - 2 * n) + ((2 * (n - 1 - k) : ℕ) : ℤ) = 0 := by omega
    have hab : x⁻¹ * s ^ (2 * k + 1) * (X * s ^ (2 * (n - 1 - k))) = 1 := by
      calc x⁻¹ * s ^ (2 * k + 1) * (X * s ^ (2 * (n - 1 - k)))
          = (x⁻¹ * x) * (s ^ ((2 * k + 1 : ℕ) : ℤ) * s ^ ((1 : ℤ) - 2 * n) *
              s ^ ((2 * (n - 1 - k) : ℕ) : ℤ)) := by
            rw [hX, zpow_natCast, zpow_natCast]; ring
        _ = 1 := by
            rw [inv_mul_cancel₀ hx, ← zpow_add₀ hs, ← zpow_add₀ hs, e, zpow_zero, one_mul]
    linear_combination -hab
  have hr : ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * (n - 1 - k))) =
      ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * k)) :=
    Finset.prod_range_reflect (fun k => 1 + X * s ^ (2 * k)) n
  have hC : ∏ k ∈ Finset.range n, (x⁻¹ * s ^ (2 * k + 1)) = x⁻¹ ^ n * s ^ (n ^ 2) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_pow_eq_pow_sum, finTriple_sum_odd]
  have hsplit : ∏ k ∈ Finset.range (2 * n), (1 + X * s ^ (2 * k)) =
      (∏ k ∈ Finset.range n, (1 + X * s ^ (2 * k))) *
        ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * (n + k))) := by
    rw [two_mul, Finset.prod_range_add]
  rw [Finset.prod_mul_distrib, Finset.prod_congr rfl ha, Finset.prod_congr rfl hb,
    Finset.prod_mul_distrib, hr, hC]
  calc _ = x⁻¹ ^ n * s ^ (n ^ 2) * ∏ k ∈ Finset.range (2 * n), (1 + X * s ^ (2 * k)) := by
        rw [hsplit]; ring
    _ = x⁻¹ ^ n * s ^ (n ^ 2) * ∑ k ∈ Finset.range (2 * n + 1),
          qBinom (s ^ 2) (2 * n) k * s ^ (k * (k - 1)) * X ^ k := by
        rw [GlobalTheory.T.prod_range_one_add_mul_pow_two_mul_eq_sum_qBinom s X hs1 (2 * n)]
    _ = ∑ k ∈ Finset.range (2 * n + 1),
          finCoeff (s ^ 2) n ((k : ℤ) - n) * (x ^ ((k : ℤ) - n) * s ^ (((k : ℤ) - n) ^ 2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        exact finTriple_term s x hs hx n k (by omega)
    _ = _ := by
        refine Finset.sum_nbij' (fun k : ℕ => (k : ℤ) - n) (fun j : ℤ => (j + n).toNat)
          ?_ ?_ ?_ ?_ ?_
        · intro a ha; simp only [Finset.mem_coe, Finset.mem_range] at ha
          simp only [Finset.mem_coe, Finset.mem_Icc]; omega
        · intro a ha; simp only [Finset.mem_coe, Finset.mem_Icc] at ha
          simp only [Finset.mem_coe, Finset.mem_range]; omega
        · intro a _; omega
        · intro a ha; simp only [Finset.mem_coe, Finset.mem_Icc] at ha
          omega
        · intro a _; rfl
end GlobalTheory.JacobiTriple
