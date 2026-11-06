-- Prove2me | solution 1 for Monodromy.NestedContinuation.nested_curve_unique
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:32:57.604851+00:00
-- url     : https://prove2.me/submissions/e968b582-ca4a-4b33-81e8-695c3ae6258d

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

open Monodromy
open Monodromy.NestedContinuation
open unitInterval


theorem solution (first second : C(I, ℂ))
    (projects : ∀ t, expCover (Complex.exp (first t)) = expCover (Complex.exp (second t)))
    (starts : first 0 = second 0) : first = second := by
  have outer : Complex.exp ∘ first = Complex.exp ∘ second := by
    apply covering.isSeparatedMap.eq_of_comp_eq
      covering.isLocalHomeomorph.isLocallyInjective
    · fun_prop
    · fun_prop
    · funext t
      exact projects t
    · exact congrArg Complex.exp starts
  apply ContinuousMap.ext
  have inner : (first : I → ℂ) = second := by
    apply covering.isSeparatedMap.eq_of_comp_eq
      covering.isLocalHomeomorph.isLocallyInjective
    · exact first.continuous
    · exact second.continuous
    · funext t
      change expCover (first t) = expCover (second t)
      apply Subtype.ext
      change Complex.exp (first t) = Complex.exp (second t)
      simpa only [Function.comp_apply] using congrFun outer t
    · exact starts
  exact congrFun inner
