-- Prove2me | solution 1 for GlobalTheory.DirichletTail.norm_LFunction_sub_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:07:14.122947+00:00
-- url     : https://prove2.me/submissions/6e891d2a-9d3b-43bd-81ed-b1b4918c90d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt
import Theorems.Thm_GlobalTheory_DirichletTail_hasSum_telescope
import Theorems.Thm_GlobalTheory_DirichletTail_abel
import Theorems.Thm_GlobalTheory_DirichletTail_norm_term_le
import Theorems.Thm_GlobalTheory_DirichletTail_summable_term
import Theorems.Thm_GlobalTheory_DirichletTail_norm_boundary_le
import Theorems.Thm_GlobalTheory_DirichletTail_LFunction_eq_tsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.DirichletTail
open Filter Topology
namespace GlobalTheory.DirichletTail
theorem _root_.solution :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 0 < s.re → ∀ N : ℕ, 1 ≤ N →
      ‖LFunction χ s - ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖
        ≤ 2 * q * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
  intro q _ χ hχ s hs N hN
  have hsum : ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s) =
      ∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q) * ((n + 1 : ℕ) : ℂ) ^ (-s) := by
    clear hN
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
  have hsm := summable_term χ hχ hs
  have hsplit := hsm.sum_add_tsum_nat_add N
  rw [hsum, abel χ s N, LFunction_eq_tsum χ hχ hs, ← hsplit]
  set c : ℝ := (q : ℝ) * (‖s‖ / s.re)
  have htail : ‖∑' n, term χ (n + N) s‖ ≤ c * ((N + 1 : ℕ) : ℝ) ^ (-s.re) :=
    tsum_of_norm_bounded ((hasSum_telescope hs N).mul_left c) fun n ↦
      norm_term_le χ hχ (n + N) hs le_rfl le_rfl
  have hbd := norm_boundary_le χ hχ s N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmono : ((N + 1 : ℕ) : ℝ) ^ (-s.re) ≤ (N : ℝ) ^ (-s.re) :=
    Real.rpow_le_rpow_of_nonpos hNpos (by push_cast; linarith) (by linarith)
  have hpow : 0 ≤ ((N + 1 : ℕ) : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hc0 : 0 ≤ c := by positivity
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hr : 0 ≤ ‖s‖ / s.re := by positivity
  calc ‖∑ i ∈ Finset.range N, term χ i s + ∑' n, term χ (n + N) s -
        (∑ i ∈ Finset.range N, term χ i s +
          (∑ k ∈ Finset.range N, χ ((k + 1 : ℕ) : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s))‖
      = ‖∑' n, term χ (n + N) s -
          (∑ k ∈ Finset.range N, χ ((k + 1 : ℕ) : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s)‖ := by
        congr 1
        ring
    _ ≤ ‖∑' n, term χ (n + N) s‖ +
          ‖(∑ k ∈ Finset.range N, χ ((k + 1 : ℕ) : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s)‖ :=
        norm_sub_le _ _
    _ ≤ c * ((N + 1 : ℕ) : ℝ) ^ (-s.re) + q * ((N + 1 : ℕ) : ℝ) ^ (-s.re) := add_le_add htail hbd
    _ = q * (1 + ‖s‖ / s.re) * ((N + 1 : ℕ) : ℝ) ^ (-s.re) := by ring
    _ ≤ q * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by gcongr
    _ ≤ 2 * q * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
        have : 0 ≤ (q : ℝ) * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by positivity
        nlinarith
end GlobalTheory.DirichletTail
