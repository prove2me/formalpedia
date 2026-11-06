-- Prove2me | solution 1 for Monodromy.NestedContinuation.execute_trans
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:14:00.133808+00:00
-- url     : https://prove2.me/submissions/af7ef9e3-e850-412e-bce9-82b27e8952ce

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

private theorem nested_curve_unique_for_trans (first second : C(I, ℂ))
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

theorem solution (first second : Path base base)
    (first_avoids : ∀ t, first t ≠ (⟨1, one_ne_zero⟩ : Punctured))
    (second_avoids : ∀ t, second t ≠ (⟨1, one_ne_zero⟩ : Punctured)) (state : Memory) :
    execute (first.trans second) (avoids_trans first second first_avoids second_avoids) state =
      execute second second_avoids (execute first first_avoids state) := by
  apply Subtype.ext
  let combined := sequentialPath first second first_avoids second_avoids state
  have projects : ∀ t, expCover (Complex.exp (combined t)) = (first.trans second) t := by
    intro t
    unfold combined sequentialPath
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact secondRaw_projects first first_avoids state _
    · exact secondRaw_projects second second_avoids (execute first first_avoids state) _
  have same : secondRaw (first.trans second)
      (avoids_trans first second first_avoids second_avoids) state = combined.toContinuousMap :=
    nested_curve_unique_for_trans _ _
      (fun t => (secondRaw_projects (first.trans second)
        (avoids_trans first second first_avoids second_avoids) state t).trans (projects t).symm)
      ((secondRaw_start (first.trans second)
        (avoids_trans first second first_avoids second_avoids) state).trans combined.source.symm)
  exact (congrArg (fun curve : C(I, ℂ) => curve 1) same).trans combined.target
