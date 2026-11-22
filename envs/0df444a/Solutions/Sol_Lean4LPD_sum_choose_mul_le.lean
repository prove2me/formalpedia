-- Prove2me | solution 1 for Lean4LPD.sum_choose_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:51.458802+00:00
-- url     : https://prove2.me/submissions/bdf5633e-fa5c-4d4e-b76a-b8eb3ac15b3d

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Theorems.Thm_Lean4LPD_sum_pow_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution (K r G : ℕ) (hG : 1 ≤ G) :
    ∑ i ∈ range r, (((i + 1) * G).choose K : ℝ)
      ≤ (((r : ℝ) + 1) * G) ^ (K + 1) / ((G : ℝ) * (Nat.factorial (K + 1) : ℝ)) := by
  have hGpos : (0 : ℝ) < (G : ℝ) := by exact_mod_cast hG
  have hKfac : (0 : ℝ) < (Nat.factorial K : ℝ) := by exact_mod_cast Nat.factorial_pos K
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  -- bound each binomial
  have hbin : ∀ i ∈ range r, (((i + 1) * G).choose K : ℝ)
      ≤ (G : ℝ) ^ K / (Nat.factorial K : ℝ) * (((i : ℝ) + 1) ^ K) := by
    intro i _
    have h := Nat.choose_le_pow_div (α := ℝ) K ((i + 1) * G)
    have hcast : (((i + 1) * G : ℕ) : ℝ) = ((i : ℝ) + 1) * (G : ℝ) := by push_cast; ring
    rw [hcast] at h
    calc (((i + 1) * G).choose K : ℝ)
        ≤ (((i : ℝ) + 1) * (G : ℝ)) ^ K / (Nat.factorial K : ℝ) := h
      _ = (G : ℝ) ^ K / (Nat.factorial K : ℝ) * (((i : ℝ) + 1) ^ K) := by
          rw [mul_pow]; ring
  have hstep : ∑ i ∈ range r, (((i + 1) * G).choose K : ℝ)
      ≤ (G : ℝ) ^ K / (Nat.factorial K : ℝ) * ∑ i ∈ range r, ((i : ℝ) + 1) ^ K := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hbin
  have hpow := sum_pow_le K r
  have hcoef : (0 : ℝ) ≤ (G : ℝ) ^ K / (Nat.factorial K : ℝ) := by positivity
  have hfac1 : (Nat.factorial (K + 1) : ℝ) = ((K : ℝ) + 1) * (Nat.factorial K : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hfinal : (G : ℝ) ^ K / (Nat.factorial K : ℝ) * (((r : ℝ) + 1) ^ (K + 1) / ((K : ℝ) + 1))
      = (((r : ℝ) + 1) * G) ^ (K + 1) / ((G : ℝ) * (Nat.factorial (K + 1) : ℝ)) := by
    rw [hfac1, mul_pow]
    field_simp
    ring
  calc ∑ i ∈ range r, (((i + 1) * G).choose K : ℝ)
      ≤ (G : ℝ) ^ K / (Nat.factorial K : ℝ) * ∑ i ∈ range r, ((i : ℝ) + 1) ^ K := hstep
    _ ≤ (G : ℝ) ^ K / (Nat.factorial K : ℝ) * (((r : ℝ) + 1) ^ (K + 1) / ((K : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hpow hcoef
    _ = (((r : ℝ) + 1) * G) ^ (K + 1) / ((G : ℝ) * (Nat.factorial (K + 1) : ℝ)) := hfinal
end Lean4LPD
