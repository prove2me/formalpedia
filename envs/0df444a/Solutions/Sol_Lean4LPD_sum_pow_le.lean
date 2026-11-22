-- Prove2me | solution 1 for Lean4LPD.sum_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:10.999123+00:00
-- url     : https://prove2.me/submissions/556d0184-1be9-46a4-a881-54b3d468fb91

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Theorems.Thm_Lean4LPD_pow_le_sub_pow

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution (m r : ℕ) :
    ∑ i ∈ range r, ((i : ℝ) + 1) ^ m ≤ ((r : ℝ) + 1) ^ (m + 1) / ((m : ℝ) + 1) := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hterm : ∀ i ∈ range r, ((m : ℝ) + 1) * (((i : ℝ) + 1) ^ m)
      ≤ (((i : ℝ) + 1) + 1) ^ (m + 1) - ((i : ℝ) + 1) ^ (m + 1) := by
    intro i _
    have hi : (1 : ℝ) ≤ (i : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    exact pow_le_sub_pow hi m
  have hsum : ((m : ℝ) + 1) * ∑ i ∈ range r, ((i : ℝ) + 1) ^ m
      ≤ ∑ i ∈ range r, ((((i : ℝ) + 1) + 1) ^ (m + 1) - ((i : ℝ) + 1) ^ (m + 1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have htel : ∑ i ∈ range r, ((((i : ℝ) + 1) + 1) ^ (m + 1) - ((i : ℝ) + 1) ^ (m + 1))
      = ((r : ℝ) + 1) ^ (m + 1) - 1 := by
    have := Finset.sum_range_sub (f := fun i : ℕ => ((i : ℝ) + 1) ^ (m + 1)) r
    simpa using this
  rw [le_div_iff₀ hm1, mul_comm]
  rw [htel] at hsum
  linarith [hsum]
end Lean4LPD
