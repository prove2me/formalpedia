-- Prove2me | solution 2 for Monodromy.CoupledContinuation.execute_homotopic
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:58:09.811946+00:00
-- url     : https://prove2.me/submissions/8662eb3e-76b3-458f-a26f-4243686ba8fd

-- Generated mechanically from the frozen source; no own-target import.
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


-- Inline helper skeleton from Monodromy.Continuation.


@[expose] public section

/-!
# Coupled analytic continuation

Two retained logarithmic memory roots share one upper control root through
`F(w₁,w₂,z) = (exp w₁, exp w₂, exp z / (w₁*w₂))`. The two actual lower
lifts generate the upper input path. The returned root is the actual upper
lift endpoint; integer labels occur only in preparation and proofs.

The matching lower product covering and upper pullback covering are explicit.
Their actual lifts agree with the complete runtime curves. Five fixed loops
provide memory shifts, zero-conditional control writes and a control shift.
Concatenation and reversal follow from lift uniqueness. A finite power-root
observation routes whole base paths by normalized analytic kernels at returns.

Five oriented loops give a finite word language and finite root-controlled
program tables with internal stopping. Effective semantics and machine
simulation are proved in the subsequent research layers.
-/

noncomputable section

namespace Monodromy.CoupledContinuation

open unitInterval












attribute [local fun_prop] analyticAt_fst analyticAt_snd





















































































































end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval























end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation









end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation





end Monodromy.CoupledContinuation


namespace Monodromy.CoupledPullback
























end Monodromy.CoupledPullback


namespace Monodromy.CoupledPullback











end Monodromy.CoupledPullback

namespace Monodromy.CoupledContinuation



















end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



attribute [local fun_prop] analyticAt_fst analyticAt_snd



end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval

variable (degree : ℕ) [NeZero degree]



























end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval










































/-- The runtime intermediate curve is the unique actual lift for the matching lower cover. -/
theorem intermediateCurve_actual_lift (driver : Driver) (state : Memory) :
    intermediateCurve driver state =
      CoupledPullback.lowerCovering.liftPath driver.restrictedPath
        (CoupledPullback.upperProjection (restrictedState state))
        (driver.restrictedPath.source.trans (restrictedState_over_base state).symm) := by
  apply (CoupledPullback.lowerCovering.eq_liftPath_iff'
    (driver.restrictedPath.source.trans (restrictedState_over_base state).symm)).mpr
  constructor
  · funext t
    exact restricted_lower_projection driver state t
  · have first := restricted_upper_projection driver state 0
    rw [restrictedTrajectory_start] at first
    exact first.symm

/-- The runtime upper trajectory is the unique actual lift for the matching upper cover. -/
theorem restrictedTrajectory_actual_lift (driver : Driver) (state : Memory) :
    restrictedTrajectory driver state =
      CoupledPullback.upperCovering.liftPath (intermediatePath driver state) (restrictedState state)
        (intermediatePath driver state).source := by
  apply (CoupledPullback.upperCovering.eq_liftPath_iff'
    (intermediatePath driver state).source).mpr
  constructor
  · funext t
    exact restricted_upper_projection driver state t
  · exact restrictedTrajectory_start driver state

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval













section FiniteRouting

variable (degree : ℕ) [NeZero degree]



























end FiniteRouting











































end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval



































end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



namespace Program

variable {degree : ℕ} [NeZero degree]















end Program

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation











end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation





end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]

















end Monodromy.CoupledContinuation.Program

/-!
## Reversible conditional control

A finite permutation of control cells is compiled into signed words of the
existing conditional loop. Its inverse is selected from the returned roots.
-/

namespace Monodromy.ReversibleControl

open CoupledContinuation



























variable {degree : ℕ} [NeZero degree]



























end Monodromy.ReversibleControl

/-! Finite root-controlled memory translations use the same signed native A paths. -/

namespace Monodromy.ReversibleMemory

open CoupledContinuation



























variable {degree : ℕ} [NeZero degree]

















end Monodromy.ReversibleMemory


/-!
## Integer coordinates of actual returned roots

These coordinates state and prove the action of the existing geometric execution.
They do not participate in path generation or add an execution rule.
-/

namespace Monodromy.CoupledContinuation













namespace Program

variable {degree : ℕ} [NeZero degree]

























end Program

end Monodromy.CoupledContinuation


/-!
## Finite cyclic staging in the existing upper branch

The compiler emits only the existing signed geometric words. A finite stage is
packed into the upper branch, and every generated word is executed by the
unchanged native lifting kernel.
-/

namespace Monodromy.StagedProgram

open CoupledContinuation
open Fin.NatCast



















variable (count degree : ℕ) [NeZero count] [NeZero degree]

























































end Monodromy.StagedProgram

/-! Static phase-zero stopping for the existing finite-stage compiler. -/

namespace Monodromy.StagedProgram

open CoupledContinuation
open Fin.NatCast

variable (count degree : ℕ) [NeZero count] [NeZero degree]































end Monodromy.StagedProgram

/-! First-return predecessor uniqueness for reversible advances. -/

namespace Monodromy.ReversibleReturn

variable {State Source : Type*}









end Monodromy.ReversibleReturn


/-! Marked inverse execution and first-return transport. -/

namespace Monodromy.CoupledContinuation.Program

noncomputable section

variable {degree : ℕ} [NeZero degree]







end

end Monodromy.CoupledContinuation.Program

namespace Monodromy.ReversibleReturn

variable {State : Type*}





end Monodromy.ReversibleReturn

end

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.CoupledContinuation
theorem solution (first second : Driver)
    (deformation : first.restrictedPath.Homotopic second.restrictedPath) (state : Memory) :
    execute first state = execute second state := by
  have lower_deformation : (intermediateCurve first state).HomotopicRel
      (intermediateCurve second state) {0, 1} := by
    rw [intermediateCurve_actual_lift first state, intermediateCurve_actual_lift second state]
    exact CoupledPullback.lowerCovering.homotopicRel_liftPath deformation
      (CoupledPullback.upperProjection (restrictedState state))
      (first.restrictedPath.source.trans (restrictedState_over_base state).symm)
      (second.restrictedPath.source.trans (restrictedState_over_base state).symm)
  have upper_end := CoupledPullback.upperCovering.liftPath_apply_one_eq_of_homotopicRel
    lower_deformation (restrictedState state)
      (intermediatePath first state).source (intermediatePath second state).source
  have endpoints : restrictedTrajectory first state 1 = restrictedTrajectory second state 1 := by
    rw [restrictedTrajectory_actual_lift first state, restrictedTrajectory_actual_lift second state]
    exact upper_end
  apply Subtype.ext
  exact congrArg forgetPoint endpoints
