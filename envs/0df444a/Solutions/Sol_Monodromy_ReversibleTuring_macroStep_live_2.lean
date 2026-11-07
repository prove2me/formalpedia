-- Prove2me | solution 2 for Monodromy.ReversibleTuring.macroStep_live
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:06:14.48118+00:00
-- url     : https://prove2.me/submissions/17009316-3350-4a0d-957f-cdd24c8307f7

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_FormalCompilation
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
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting
public import Theorems.Thm_Monodromy_ReversibleTuring_step_firstReturn

@[expose] public section


-- Inline helper skeleton from Monodromy.FormalCompilation.


/-!
# Finite Turing tables and native continuation

Mathlib's stack evaluator is translated to a Post–Turing table and restricted
to its finite support. The source code fixes the table; its numeric arguments
are supplied through an explicit finite input word.

The native simulation composes the actual finite counter compilers with
fixed geometric Word execution. It preserves full configurations, complete
partial results, halting and divergence. Source steps are causal first returns
marked by finite analytic root observations. Finite executions are realized
by the two matching covering-space lifts.
-/

@[expose] public section

namespace Monodromy.FormalCompilation

open Turing











variable (source : ToPartrec.Code)















































end Monodromy.FormalCompilation

noncomputable section

namespace Monodromy.NativeTuring

open Turing CoupledContinuation

variable (a q : ℕ) [NeZero a] [NeZero q]





































section FiniteTypes

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Fintype Q] [Inhabited Q]















end FiniteTypes

end Monodromy.NativeTuring

namespace Monodromy.NativeTuring

open Turing CoupledContinuation

section Marking

variable {m : ℕ} [NeZero m]



















end Marking

variable (a q : ℕ) [NeZero a] [NeZero q]




















































section FiniteTypes

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Fintype Q] [Inhabited Q]





end FiniteTypes



end Monodromy.NativeTuring

/-!
## Universal simulation with recoverable history

The ordinary two-counter compilation supplies only the source to be made
reversible. A fixed finite recording graph executes it, retaining the complete
configuration and history. Its four source registers are a proof intermediate;
reversibility-preserving compression to two native memory roots is separate.
-/

namespace Monodromy.RecordedTuring

open Turing

noncomputable section

variable (a q : ℕ) [NeZero a] [NeZero q]









end

end Monodromy.RecordedTuring

namespace Monodromy.ReversibleTuring

open Turing

noncomputable section

variable (a q : ℕ) [NeZero a] [NeZero q]



























private theorem boundaryTransition_stops (machine : TM0.Machine (Fin a) (Fin q))
    {state : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))}
    (marked : Boundary a q machine state) : boundaryTransition a q machine state = none := by
  simp only [boundaryTransition, ite_eq_left marked]

private theorem internal_marked_reaches (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))}
    (run : Counter.Reversible.Recording.InternalMarkedReaches
      (NativeTuring.source2 a q machine) (NativeTuring.counterMark a q machine) first last) :
    StateTransition.Reaches (boundaryTransition a q machine) first last := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | @tail first last _ edge previous =>
      apply previous.tail
      change (if Boundary a q machine first then none
        else Counter.Reversible.step (table a q machine) first) = some last
      have unmarked : ¬ Boundary a q machine first := edge.2
      rw [ite_eq_right unmarked]
      exact edge.1





















end

end Monodromy.ReversibleTuring

/-!
## Recoverable-history simulation on two counters
-/

noncomputable section

namespace Monodromy.ReversibleTuring.Compression

open Turing Counter.Reversible



variable (a q : ℕ) [NeZero a] [NeZero q]

































































end Monodromy.ReversibleTuring.Compression

end

/-!
## Reversible universality by actual path lifting
-/

noncomputable section

namespace Monodromy.ReversibleNativeTuring

open Turing CoupledContinuation ReversibleTuring

variable (a q : ℕ) [NeZero a] [NeZero q]




































































end Monodromy.ReversibleNativeTuring

end

end

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.ReversibleTuring
open Turing
variable (a q : ℕ) [NeZero a] [NeZero q]
theorem solution (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      macroStep a q machine (encode a q machine first history) =
        Part.some (some (encode a q machine last finalHistory)) := by
  obtain ⟨finalHistory, grew, _, marked, next, initial, rest⟩ :=
    step_firstReturn a q machine transition history
  have completed : StateTransition.eval (boundaryTransition a q machine) next =
      Part.some (encode a q machine last finalHistory) := by
    apply Part.eq_some_iff.mpr
    exact StateTransition.mem_eval.mpr
      ⟨internal_marked_reaches a q machine rest, boundaryTransition_stops a q machine marked⟩
  refine ⟨finalHistory, grew, ?_⟩
  change Counter.Reversible.step (table a q machine) (encode a q machine first history) =
    some next at initial
  simp only [macroStep, initial, completed, Part.map_some]
