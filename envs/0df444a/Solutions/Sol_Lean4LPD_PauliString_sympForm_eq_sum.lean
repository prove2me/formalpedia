-- Prove2me | solution 1 for Lean4LPD.PauliString.sympForm_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:06:28.255151+00:00
-- url     : https://prove2.me/submissions/096aaeab-d80f-42c5-aa08-5ad3db8c9a9e

module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}
namespace Lean4LPD.PauliString
theorem _root_.solution (s t : PauliString n) :
    sympForm s t = ∑ i, (s.x i * t.z i + s.z i * t.x i) := by
  simp [sympForm, dotProduct, Finset.sum_add_distrib]
end Lean4LPD.PauliString
