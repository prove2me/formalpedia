-- Prove2me | solution 1 for Lean4LPD.factorial_ratio_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:20.814394+00:00
-- url     : https://prove2.me/submissions/2c9bebfd-91a0-4d17-a35b-f271a46d3dc8

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {m D : ℕ} (hD : D ≤ m) :
    (Nat.factorial m : ℝ) / (Nat.factorial (m - D) : ℝ) ≤ (m : ℝ) ^ D := by
  have h : Nat.factorial m ≤ m ^ D * Nat.factorial (m - D) := by
    calc
      Nat.factorial m = Nat.factorial (m - D) * m.descFactorial D :=
        (Nat.factorial_mul_descFactorial hD).symm
      _ ≤ Nat.factorial (m - D) * m ^ D :=
        Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow m D)
      _ = m ^ D * Nat.factorial (m - D) := Nat.mul_comm _ _
  apply (div_le_iff₀ (by positivity)).mpr
  exact_mod_cast h
end Lean4LPD
