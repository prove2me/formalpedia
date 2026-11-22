-- Prove2me | solution 1 for Lean4LPD.bits_add_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:59:56.854934+00:00
-- url     : https://prove2.me/submissions/70a9bae0-bdf1-45fc-8eac-13d726e70ae4

module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
section
@[expose] public section
namespace Lean4LPD
private lemma bit_add_eq_zero_iff {a b : ZMod 2} : a + b = 0 ↔ a = b := by
  revert a b; decide
namespace PauliString
variable {n : ℕ} {s t u : PauliString n}
end PauliString
end Lean4LPD
end
end

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
namespace Lean4LPD
theorem _root_.solution {n : ℕ} {u v : Fin n → ZMod 2} : u + v = 0 ↔ u = v := by
  constructor
  · intro h
    funext i
    exact bit_add_eq_zero_iff.1 (congrFun h i)
  · rintro rfl; exact bits_add_self _
end Lean4LPD
