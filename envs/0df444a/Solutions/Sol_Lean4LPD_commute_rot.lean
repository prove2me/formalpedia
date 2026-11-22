-- Prove2me | solution 1 for Lean4LPD.commute_rot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:26.496361+00:00
-- url     : https://prove2.me/submissions/c8cc7b15-46d4-404b-ab5a-a03063054d1d

module
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
variable {A : Type*} [Ring A] [Algebra ℂ A] {G P : A} {θ θ₁ θ₂ : ℝ}
namespace Lean4LPD
theorem _root_.solution (h : Commute G P) : Commute (rot G θ) P :=
  ((Commute.one_left P).smul_left _).add_left (h.smul_left _)
end Lean4LPD
