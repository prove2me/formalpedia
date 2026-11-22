-- Prove2me | solution 1 for Lean4LPD.signPhase_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:56.138079+00:00
-- url     : https://prove2.me/submissions/7df639ac-6263-4952-b10a-365769e759ba

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
namespace Lean4LPD
theorem _root_.solution : Function.Injective signPhase := by decide
end Lean4LPD
