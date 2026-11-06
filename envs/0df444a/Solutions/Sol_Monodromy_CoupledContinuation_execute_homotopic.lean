-- Prove2me | solution 1 for Monodromy.CoupledContinuation.execute_homotopic
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:32:07.672221+00:00
-- url     : https://prove2.me/submissions/e5fa143d-58d9-45b5-8558-7ad5ddf68e1e

module
public import Definitions.Def_Monodromy_Continuation
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Computability.StateTransition
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.CoupledContinuation

theorem solution (first second : Driver)
    (deformation : first.restrictedPath.Homotopic second.restrictedPath) (state : Memory) :
    execute first state = execute second state := by
  have lower_lift (driver : Driver) (state : Memory) :
      intermediateCurve driver state =
        CoupledPullback.lowerCovering.liftPath driver.restrictedPath
          (CoupledPullback.upperProjection (restrictedState state))
          (driver.restrictedPath.source.trans (restrictedState_over_base state).symm) := by
    apply (CoupledPullback.lowerCovering.eq_liftPath_iff' _).mpr
    exact ⟨funext (restricted_lower_projection driver state),
      (intermediatePath driver state).source⟩
  have upper_lift (driver : Driver) (state : Memory) :
      restrictedTrajectory driver state =
        CoupledPullback.upperCovering.liftPath (intermediatePath driver state)
          (restrictedState state) (intermediatePath driver state).source := by
    apply (CoupledPullback.upperCovering.eq_liftPath_iff' _).mpr
    exact ⟨funext (restricted_upper_projection driver state),
      restrictedTrajectory_start driver state⟩
  have lower_deformation :
      (intermediateCurve first state).HomotopicRel
        (intermediateCurve second state) {0, 1} := by
    rw [lower_lift first state, lower_lift second state]
    exact CoupledPullback.lowerCovering.homotopicRel_liftPath deformation
      (CoupledPullback.upperProjection (restrictedState state))
      (first.restrictedPath.source.trans (restrictedState_over_base state).symm)
      (second.restrictedPath.source.trans (restrictedState_over_base state).symm)
  have endpoints : restrictedTrajectory first state 1 = restrictedTrajectory second state 1 := by
    rw [upper_lift first state, upper_lift second state]
    exact CoupledPullback.upperCovering.liftPath_apply_one_eq_of_homotopicRel
      lower_deformation (restrictedState state)
      (intermediatePath first state).source (intermediatePath second state).source
  apply Subtype.ext
  exact congrArg forgetPoint endpoints
