-- Prove2me | solution 1 for Lean4LPD.partFactor_mul_tail_rungs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:41.177505+00:00
-- url     : https://prove2.me/submissions/482d412f-836c-46f8-9c6b-7d772eae23c2

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Theorems.Thm_Lean4LPD_chainWeight_tail_rungs
public import Theorems.Thm_Lean4LPD_partFactor_denom_pos


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {c : ℝ} (hc : 0 ≤ c) (kh1 : ℝ)
    {j m : ℕ} (hjm : j ≤ m) :
    partFactor j ((m : ℝ) + c) * (∏ i ∈ range j, rungW kh1 c (m - j + i + 2))
      = rungW kh1 c (m + j) ^ j / (Nat.factorial j : ℝ) := by
  have hmc : (j : ℝ) ≤ (m : ℝ) + c := by
    exact (by exact_mod_cast hjm : (j : ℝ) ≤ m).trans (le_add_of_nonneg_right hc)
  have hQ : (∏ i ∈ range j, ((m : ℝ) + c - j + 1 + i)) ≠ 0 :=
    ne_of_gt (partFactor_denom_pos hmc)
  have hfac : (Nat.factorial j : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hnum : rungW kh1 c (m + j) = kh1 * ((m : ℝ) + c + j - 1) := by
    unfold rungW
    push_cast
    ring
  rw [partFactor, chainWeight_tail_rungs kh1 c hjm, hnum, mul_pow]
  field_simp [hQ, hfac]
end Lean4LPD
