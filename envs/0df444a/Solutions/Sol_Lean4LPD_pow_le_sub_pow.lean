-- Prove2me | solution 1 for Lean4LPD.pow_le_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:30.883603+00:00
-- url     : https://prove2.me/submissions/ba3d0d32-204c-4daa-90ec-b54b2e7504d0

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {d : ℝ} (hd : 1 ≤ d) (m : ℕ) :
    ((m : ℝ) + 1) * d ^ m ≤ (d + 1) ^ (m + 1) - d ^ (m + 1) := by
  have hdpos : (0 : ℝ) < d := by linarith
  have hinv : (-2 : ℝ) ≤ 1 / d := by
    have : (0 : ℝ) ≤ 1 / d := by positivity
    linarith
  have hb : (1 : ℝ) + ((m : ℝ) + 1) * (1 / d) ≤ (1 + 1 / d) ^ (m + 1) := by
    have h := one_add_mul_le_pow hinv (m + 1)
    push_cast at h
    linarith [h]
  have hsplit : (d + 1) ^ (m + 1) = d ^ (m + 1) * (1 + 1 / d) ^ (m + 1) := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hdm : (0 : ℝ) < d ^ (m + 1) := pow_pos hdpos _
  rw [hsplit]
  have hmul := mul_le_mul_of_nonneg_left hb (le_of_lt hdm)
  have hcancel : d ^ (m + 1) * (1 + ((m : ℝ) + 1) * (1 / d))
      = d ^ (m + 1) + ((m : ℝ) + 1) * d ^ m := by
    rw [pow_succ]
    field_simp
  rw [hcancel] at hmul
  linarith [hmul]
end Lean4LPD
