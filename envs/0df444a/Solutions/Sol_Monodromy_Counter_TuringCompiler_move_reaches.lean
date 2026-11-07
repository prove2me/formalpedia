-- Prove2me | solution 1 for Monodromy.Counter.TuringCompiler.move_reaches
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:02:10.562194+00:00
-- url     : https://prove2.me/submissions/349e7103-bdcc-445f-b72d-8a2e77a49e5c

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Counter
public import Definitions.Def_Monodromy_Tape
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
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
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
public import Theorems.Thm_Monodromy_Counter_TuringCompiler_add_reaches
public import Theorems.Thm_Monodromy_Counter_TuringCompiler_divide_reaches
public import Theorems.Thm_Monodromy_Counter_TuringCompiler_multiply_reaches

@[expose] public section


-- Inline helper skeleton from Monodromy.Tape.


/-!
# Canonical half-tape codes

Positional encoding descends to blank-padded tapes and preserves every cell.
-/

@[expose] public section

namespace Monodromy.TapeCode

open Turing

variable {a : ℕ} [NeZero a]



@[simp] theorem encode_mk (word : List (Fin a)) :
    encode (ListBlank.mk word) = Nat.ofDigits (a + 1) (word.map Fin.val) := rfl



/-- Push, pop and head observation are arithmetic identities on the blank quotient itself. -/
theorem encode_cons (symbol : Fin a) (tape : ListBlank (Fin a)) :
    encode (tape.cons symbol) = symbol.val + (a + 1) * encode tape := by
  refine ListBlank.induction_on tape (fun word => ?_)
  simp only [ListBlank.cons_mk, encode_mk, List.map_cons, Nat.ofDigits_cons]

theorem decomposition (tape : ListBlank (Fin a)) :
    encode tape = tape.head.val + (a + 1) * encode tape.tail := by
  simpa only [ListBlank.cons_head_tail] using encode_cons tape.head tape.tail

theorem head_code (tape : ListBlank (Fin a)) :
    encode tape % (a + 1) = tape.head.val := by
  rw [decomposition, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (Nat.lt_succ_of_lt tape.head.isLt)]

theorem tail_code (tape : ListBlank (Fin a)) :
    encode tape / (a + 1) = encode tape.tail := by
  rw [decomposition, Nat.add_mul_div_left _ _ (Nat.succ_pos a),
    Nat.div_eq_of_lt (Nat.lt_succ_of_lt tape.head.isLt), zero_add]







end Monodromy.TapeCode

end


-- Inline helper skeleton from Monodromy.Counter.


/-!
# Counter machines and native continuation

The standard finite counter semantics is retained. A three-phase finite
compiler realizes each two-counter step by two actual geometric returns;
the faithful configuration encoding preserves complete partial execution.

Classical finite counter macros and prime coding compile an entire finite
Turing table through three source registers to the same two-counter target.
Every arithmetic loop has a separate finite control region, with marked
source entries and no intermediate return boundary.
-/

@[expose] public section

namespace Monodromy.Counter









variable {n m : ℕ} (program : Program n m) (state : Configuration n m)















variable {k : ℕ}











end Monodromy.Counter

noncomputable section

namespace Monodromy.CounterContinuation

open CoupledContinuation



























variable {m : ℕ} [NeZero m]





end Monodromy.CounterContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation

variable {m : ℕ} [NeZero m]

















end Monodromy.CounterContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation

variable {m : ℕ}



variable [NeZero m]













end Monodromy.CounterContinuation


namespace Monodromy.CounterContinuation

variable {m : ℕ} [NeZero m]



end Monodromy.CounterContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation









variable {m : ℕ} [NeZero m]







end Monodromy.CounterContinuation

namespace Monodromy.PrimeCode



namespace Basis

variable {n : ℕ} (basis : Basis n)

























end Basis





































end Monodromy.PrimeCode

namespace Monodromy.Counter.RegisterRelocation

variable {n k m : ℕ}





















end Monodromy.Counter.RegisterRelocation

namespace Monodromy.Counter

variable {n m k : ℕ}





end Monodromy.Counter

namespace Monodromy.CounterMultiplication

















































end Monodromy.CounterMultiplication

namespace Monodromy.Counter.DivMod

variable (p : ℕ) [NeZero p]
































































end Monodromy.Counter.DivMod

namespace Monodromy.CounterPrimeProbe

variable (p : ℕ) [NeZero p]





























































end Monodromy.CounterPrimeProbe

namespace Monodromy.Counter.TuringCompiler

open Turing

variable (a q : ℕ) [NeZero a] [NeZero q]

























































































theorem symbol_tape (tape : ListBlank (Fin a)) :
    symbol a (DivMod.residue (base a) (TapeCode.encode tape)) = tape.head := by
  have remainder : (DivMod.residue (base a) (TapeCode.encode tape)).val = tape.head.val :=
    TapeCode.head_code tape
  have small : (DivMod.residue (base a) (TapeCode.encode tape)).val < a := by
    rw [remainder]
    exact tape.head.isLt
  apply Fin.ext
  simp only [symbol, dite_eq_left small]
  exact remainder

















end Monodromy.Counter.TuringCompiler

namespace Monodromy.Counter.Compression

variable {m : ℕ}








































































































end Monodromy.Counter.Compression

namespace Monodromy.Counter.EntryDispatch

variable {a m : ℕ}























end Monodromy.Counter.EntryDispatch

/-!
## Locally reversible counter tables
-/

namespace Monodromy.Counter.Reversible









namespace Action

variable {n : ℕ}



















end Action

variable {n q e : ℕ}

namespace Edge







end Edge

























namespace Action











end Action



































namespace Action



end Action





















end Monodromy.Counter.Reversible

/-!
## Static finite port matchings
-/

namespace Monodromy.ReversiblePorts

variable {q e : ℕ}

























open Counter.Reversible





















end Monodromy.ReversiblePorts

/-!
## Native guarded routing
-/

namespace Monodromy.ReversibleRouting

open CoupledContinuation Counter.Reversible ReversiblePorts

variable {q e : ℕ} [NeZero (q + e)]



variable (table : Table 2 q e) (owner : Fin e → Fin q)
  (matching : ∀ guard, Matching owner (selected table guard))





























end Monodromy.ReversibleRouting

/-!
## The fixed reversible native compiler
-/

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation ReversiblePorts

variable {q e : ℕ} [NeZero q]











































































end Monodromy.ReversibleCompilation

/-!
## Complete execution and actual lifted results
-/

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation

variable {q e : ℕ} [NeZero q]



















































end Monodromy.ReversibleCompilation

/-!
## Protected source register relocation
-/

namespace Monodromy.Counter.Reversible.RegisterRelocation

variable {n m q e : ℕ}







































end Monodromy.Counter.Reversible.RegisterRelocation

/-!
## Composition by gluing control interfaces
-/

namespace Monodromy.Counter.Reversible.Glue

variable {n q₁ q₂ e₁ e₂ : ℕ}









































/-! Finite traces inside larger control graphs. -/

section FiniteTrace

variable {n m q k e f : ℕ}







end FiniteTrace

end Monodromy.Counter.Reversible.Glue

/-!
## Finite port identification

A partial matching identifies existing output and input positions. Original
edges and actions are retained, including in cyclic networks.
-/

noncomputable section

namespace Monodromy.Counter.Reversible.PortNetwork

variable {n q e : ℕ}



variable {original : Table n q e} (wiring : Wiring original)



















































end Monodromy.Counter.Reversible.PortNetwork

end


/-!
## One reversible radix graph: unpacking and packing
-/

namespace Monodromy.Counter.Reversible.Radix

variable (p : ℕ) [NeZero p]




































































































end Monodromy.Counter.Reversible.Radix

/-!
## Read-only remainder observation by identified radix ports
-/

noncomputable section

namespace Monodromy.Counter.Reversible.RadixObservation

variable (p m : ℕ) [NeZero p]



















































































end Monodromy.Counter.Reversible.RadixObservation

end


/-!
## A source specification for reversible transition recording
-/

namespace Monodromy.Counter.Recorded

variable {n m : ℕ}





























end Monodromy.Counter.Recorded


/-!
## Recoverable execution histories

Finite copies of the reversed radix graph record each instruction branch.
The source registers are protected while the history is packed; the workspace
returns to zero at every dispatch. This is an intermediate reversible source
graph, prior to compression into the two native memory coordinates.
-/

noncomputable section

namespace Monodromy.Counter.Reversible.Recording

variable {n m : ℕ}


















































































































































/-! The natural domain is preserved at every intermediate port. -/













































































































end Monodromy.Counter.Reversible.Recording

end

/-!
## Reversible prime compression

A finite virtual register vector is encoded in prime exponents. All arithmetic
uses the same two-counter radix graph; shared ports select and restore tests.
Exact first returns preserve the entire source configuration. Ordinary traces
are derived from that stronger execution statement.
-/

noncomputable section

namespace Monodromy.Counter.Reversible.PrimeCompression

variable {n q e : ℕ}























































































































































































































































































































































end Monodromy.Counter.Reversible.PrimeCompression

end


/-! Finite source marks on the same native geometric word table. -/

noncomputable section

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation

variable {q e : ℕ} [NeZero q]









































end Monodromy.ReversibleCompilation

end

end

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.Counter
open Monodromy.Counter.TuringCompiler
open Turing
variable (a q : ℕ) [NeZero a] [NeZero q]
theorem solution (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (target : Fin q) (direction : Dir)
    (selected : machine state.q state.Tape.head = some (target, .move direction)) :
    InternalReaches a q machine
      ⟨mulTarget a q (state.q, state.Tape.head) 0, (encode a q state).counters⟩
      (encode a q ⟨target, state.Tape.move direction⟩) := by
  cases direction with
  | left =>
      have multiplied := multiply_reaches a q machine (state.q, state.Tape.head) target .left
        selected (TapeCode.encode state.Tape.right) (TapeCode.encode state.Tape.left)
      have written := add_reaches a q machine (state.q, state.Tape.head) target .left
        selected state.Tape.head (base a * TapeCode.encode state.Tape.right)
        (TapeCode.encode state.Tape.left)
      have divided := divide_reaches a q machine (state.q, state.Tape.head) target .left
        selected (TapeCode.encode state.Tape.left)
        (base a * TapeCode.encode state.Tape.right + state.Tape.head.val)
      have combined := multiplied.trans (written.trans divided)
      rw [symbol_tape a state.Tape.left] at combined
      simpa [encode, Tape.move, TapeCode.encode_cons, ← TapeCode.tail_code,
        pushRegister, popRegister, frame, counters, Nat.add_comm, base] using combined
  | right =>
      have multiplied := multiply_reaches a q machine (state.q, state.Tape.head) target .right
        selected (TapeCode.encode state.Tape.left) (TapeCode.encode state.Tape.right)
      have written := add_reaches a q machine (state.q, state.Tape.head) target .right
        selected state.Tape.head (base a * TapeCode.encode state.Tape.left)
        (TapeCode.encode state.Tape.right)
      have divided := divide_reaches a q machine (state.q, state.Tape.head) target .right
        selected (TapeCode.encode state.Tape.right)
        (base a * TapeCode.encode state.Tape.left + state.Tape.head.val)
      have combined := multiplied.trans (written.trans divided)
      rw [symbol_tape a state.Tape.right] at combined
      simpa [encode, Tape.move, TapeCode.encode_cons, ← TapeCode.tail_code,
        pushRegister, popRegister, frame, counters, Nat.add_comm, base] using combined
