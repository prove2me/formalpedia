-- Prove2me | solution 2 for Monodromy.NestedContinuation.nested_curve_unique
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:58:35.116727+00:00
-- url     : https://prove2.me/submissions/bdb39a9a-e04b-46ee-ab9e-fbb04747a3bb

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Logarithm
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.NestedContinuation
open unitInterval
theorem solution (first second : C(I, ℂ))
    (projects : ∀ t, expCover (Complex.exp (first t)) = expCover (Complex.exp (second t)))
    (starts : first 0 = second 0) : first = second := by
  have middle : (fun t => Complex.exp (first t)) = (fun t => Complex.exp (second t)) :=
    covering.eq_of_comp_eq
      (Complex.continuous_exp.comp first.continuous)
      (Complex.continuous_exp.comp second.continuous)
      (funext projects) 0 (congrArg Complex.exp starts)
  have upper : expCover ∘ first = expCover ∘ second := by
    funext t
    apply Subtype.ext
    exact congrFun middle t
  ext t
  exact congrFun (covering.eq_of_comp_eq first.continuous second.continuous upper 0 starts) t
