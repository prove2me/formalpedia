-- Prove2me | solution 2 for Monodromy.FormalCompilation.eval1
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:01:15.252832+00:00
-- url     : https://prove2.me/submissions/15f17b59-ebf9-44ed-b16d-772ba5c986c7

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
public import Theorems.Thm_Monodromy_FormalCompilation_relation_unique

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























theorem initial_relation (values : List ℕ) :
    TM2to1.TrCfg (PartrecToTM2.init source values)
      (TM1.init (tapeData values) : TM1.Cfg Alphabet (Control1 source) Store) := by
  let _ : Inhabited Label2 := ⟨PartrecToTM2.trNormal source PartrecToTM2.Cont'.halt⟩
  have initial := TM2to1.trCfg_init (Γ := fun _ : Stack => Symbol) (Λ := Label2) (σ := Store)
    PartrecToTM2.K'.main (PartrecToTM2.trList values)
  have same : (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList values) :
      TM2.Cfg (fun _ : Stack => Symbol) Label2 Store) = PartrecToTM2.init source values := by
    apply congrArg (fun storage => TM2.Cfg.mk
      (some (PartrecToTM2.trNormal source PartrecToTM2.Cont'.halt)) none storage)
    funext index
    cases index <;> rfl
  rw [same] at initial
  exact initial



theorem relation_stop
    {configuration : TM2.Cfg (fun _ : Stack => Symbol) Label2 Store}
    {target : TM1.Cfg Alphabet (Control1 source) Store}
    (related : TM2to1.TrCfg configuration target) :
    TM2to1.TrCfg (Λ := Label2) { configuration with l := none } { target with l := none } := by
  cases related with
  | mk contents projection => exact TM2to1.TrCfg.mk contents projection



theorem halt_relation (values : List ℕ) :
    TM2to1.TrCfg (PartrecToTM2.halt values) (halt1 source values) :=
  relation_stop source (initial_relation source values)















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
open Monodromy.FormalCompilation
open Turing
variable (source : ToPartrec.Code)
theorem solution (values : List ℕ) :
    StateTransition.eval (TM1.step (machine1 source))
      (TM1.init (tapeData values) : TM1.Cfg Alphabet (Control1 source) Store) =
      halt1 source <$> source.eval values := by
  have source_evaluation := PartrecToTM2.tr_eval source values
  apply Part.ext
  intro target
  constructor
  · intro completed
    obtain ⟨source_result, related, finished⟩ := StateTransition.tr_eval_rev
      (TM2to1.tr_respects PartrecToTM2.tr) (initial_relation source values) completed
    rw [source_evaluation] at finished
    obtain ⟨value, value_finished, rfl⟩ := (Part.mem_map_iff _).mp finished
    exact (Part.mem_map_iff _).mpr
      ⟨value, value_finished, (relation_unique source related (halt_relation source value)).symm⟩
  · intro completed
    obtain ⟨result, result_finished, rfl⟩ := (Part.mem_map_iff _).mp completed
    have source_finished : PartrecToTM2.halt result ∈
        StateTransition.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init source values) := by
      rw [source_evaluation]
      exact (Part.mem_map_iff _).mpr ⟨result, result_finished, rfl⟩
    obtain ⟨target, related, finished⟩ := StateTransition.tr_eval
      (TM2to1.tr_respects PartrecToTM2.tr) (initial_relation source values) source_finished
    have same := relation_unique source related (halt_relation source result)
    rw [same] at finished
    exact finished
