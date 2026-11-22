-- Prove2me | solution 1 for Lean4LPD.cZero_pow_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:30.324941+00:00
-- url     : https://prove2.me/submissions/4d664150-f7c6-4987-af12-aeca03d58661

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Theorems.Thm_Lean4LPD_chainWeight_zero
attribute [local simp] Lean4LPD.chainWeight_zero



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {r G B : ℝ} (hB : 0 ≤ B) (m : ℕ) :
    cZero r (m : ℝ) G B ^ (m + 1) =
      ((r + 1) / r) ^ (m + 1) *
        Real.exp (9 / 4 * ((m : ℝ) + 1) ^ 2 / (r * G)) * (1 + B) := by
  have hroot : ((1 + B) ^ ((1 : ℝ) / ((m : ℝ) + 1))) ^ (m + 1) = 1 + B := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      Real.rpow_inv_natCast_pow (x := 1 + B) (n := m + 1) (by positivity) (by omega)
  have he : (Real.exp (9 / 4 * ((m : ℝ) + 1) / (r * G))) ^ (m + 1) =
      Real.exp (9 / 4 * ((m : ℝ) + 1) ^ 2 / (r * G)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [cZero, mul_pow, mul_pow, hroot, he]
end Lean4LPD
