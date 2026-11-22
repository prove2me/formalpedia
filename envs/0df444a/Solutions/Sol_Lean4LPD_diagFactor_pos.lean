-- Prove2me | solution 1 for Lean4LPD.diagFactor_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:17.514014+00:00
-- url     : https://prove2.me/submissions/ef3fbc11-b27d-4652-a254-e1a22c3cd045

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {j : ℕ} (hj : 1 ≤ j) : 0 < diagFactor j := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hfac : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  unfold diagFactor
  apply div_pos (pow_pos (by linarith) j) (by positivity)
end Lean4LPD
