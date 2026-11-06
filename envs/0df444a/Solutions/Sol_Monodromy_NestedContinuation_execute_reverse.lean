-- Prove2me | solution 1 for Monodromy.NestedContinuation.execute_reverse
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:34:42.452892+00:00
-- url     : https://prove2.me/submissions/f2fb280e-c919-4548-b6d3-1a4338551bc0

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

private theorem nested_curve_unique_for_reverse (first second : C(I, ℂ))
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

private theorem executionPath_projects_for_reverse (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) (t : I) :
    expCover (Complex.exp (executionPath path avoids state t)) = path t :=
  secondRaw_projects path avoids state t

theorem solution (path : Path base base)
    (avoids : ∀ t, path t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    execute path.symm (avoids_symm path avoids) (execute path avoids state) = state := by
  apply Subtype.ext
  let backwards := (executionPath path avoids state).symm
  have projects : ∀ t, expCover (Complex.exp (backwards t)) = path.symm t := by
    intro t
    exact executionPath_projects_for_reverse path avoids state (σ t)
  have same : secondRaw path.symm (avoids_symm path avoids) (execute path avoids state) =
      backwards.toContinuousMap :=
    nested_curve_unique_for_reverse _ _
      (fun t => (secondRaw_projects path.symm (avoids_symm path avoids)
        (execute path avoids state) t).trans (projects t).symm)
      ((secondRaw_start path.symm (avoids_symm path avoids)
        (execute path avoids state)).trans backwards.source.symm)
  exact (congrArg (fun curve : C(I, ℂ) => curve 1) same).trans backwards.target
