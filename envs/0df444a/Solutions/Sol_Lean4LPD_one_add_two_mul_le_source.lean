-- Prove2me | solution 1 for Lean4LPD.one_add_two_mul_le_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:18.534998+00:00
-- url     : https://prove2.me/submissions/786c0e56-0669-4336-8ec3-5f8f7c774985

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {b : ℝ} (hb : 0 ≤ b) :
    1 + 2 * b ≤ 1 + 4 * Real.exp 1 * b := by
  have h : (2 : ℝ) ≤ 4 * Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  nlinarith [hb, h]
end Lean4LPD
