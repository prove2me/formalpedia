-- Prove2me | solution 1 for GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:42:50.497951+00:00
-- url     : https://prove2.me/submissions/74208e23-e233-4d08-b3fd-72a31c394d75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QBinomialFinite
import Theorems.Thm_GlobalTheory_JacobiTriple_QBinomial_qBinom_zero_right
import Theorems.Thm_GlobalTheory_JacobiTriple_QBinomial_qBinom_self
import Theorems.Thm_GlobalTheory_JacobiTriple_QBinomial_qBinom_pascal
import Theorems.Thm_GlobalTheory_JacobiTriple_QBinomial_exp_eq

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
open GlobalTheory GlobalTheory.JacobiTriple GlobalTheory.JacobiTriple.QBinomial
open GlobalTheory.JacobiTriple
namespace GlobalTheory.JacobiTriple.QBinomial
theorem _root_.solution : ∀ (s X : ℂ), ‖s‖ < 1 → ∀ m : ℕ, ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), GlobalTheory.JacobiTriple.qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k := by
  intro s X hs m
  have ht : ‖s ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg s]
  induction m with
  | zero => simp [qBinom_zero_right _ ht]
  | succ m ih =>
    set f : ℕ → ℕ → ℂ := fun m k => qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k with hf
    change ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), f m k at ih
    change _ = ∑ k ∈ Finset.range (m + 1 + 1), f (m + 1) k
    rw [Finset.prod_range_succ, ih, mul_add, mul_one]
    have A : ∑ k ∈ Finset.range (m + 1), f m k = f m 0 + ∑ k ∈ Finset.range m, f m (k + 1) := by
      rw [Finset.sum_range_succ', add_comm]
    have B : (∑ k ∈ Finset.range (m + 1), f m k) * (X * s ^ (2 * m)) =
        ∑ k ∈ Finset.range m, f m k * (X * s ^ (2 * m)) + f m m * (X * s ^ (2 * m)) := by
      rw [Finset.sum_mul, Finset.sum_range_succ]
    have C : ∑ k ∈ Finset.range (m + 1 + 1), f (m + 1) k =
        f (m + 1) 0 + ∑ k ∈ Finset.range m, f (m + 1) (k + 1) + f (m + 1) (m + 1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ', add_comm (f (m + 1) 0)]
    have hsum : ∑ k ∈ Finset.range m, f (m + 1) (k + 1)
        = ∑ k ∈ Finset.range m, f m (k + 1) + ∑ k ∈ Finset.range m, f m k * (X * s ^ (2 * m)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' := Finset.mem_range.mp hk
      simp only [hf]
      rw [qBinom_pascal _ ht m k hk']
      have : s ^ (k * (k - 1)) * s ^ (2 * m) = s ^ ((k + 1) * k) * (s ^ 2) ^ (m - k) := by
        rw [← pow_add, ← pow_mul, ← pow_add, exp_eq m k hk']
      simp only [Nat.add_sub_cancel]
      linear_combination (-(qBinom (s ^ 2) m k * X ^ (k + 1))) * this
    have hlast : s ^ ((m + 1) * (m + 1 - 1)) = s ^ (m * (m - 1)) * s ^ (2 * m) := by
      rw [← pow_add]; congr 1; rcases m with _ | m
      · simp
      · simp only [Nat.add_sub_cancel]; ring
    have e0 : f (m + 1) 0 = f m 0 := by
      simp only [hf, qBinom_zero_right _ ht]
    have em : f (m + 1) (m + 1) = f m m * (X * s ^ (2 * m)) := by
      simp only [hf, qBinom_self _ ht, hlast]; ring
    rw [B, A, C, hsum, e0, em]
    ring
end GlobalTheory.JacobiTriple.QBinomial
