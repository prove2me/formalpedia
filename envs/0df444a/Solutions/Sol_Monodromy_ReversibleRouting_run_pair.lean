-- Prove2me | solution 1 for Monodromy.ReversibleRouting.run_pair
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:59:03.873225+00:00
-- url     : https://prove2.me/submissions/b1dfe44c-8147-4060-85e2-237058fe463d

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Counter
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

@[expose] public section


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













theorem Compatible.not_both {first second : Action n} (compatible : Compatible first second)
    (values : Fin n → ℤ) : ¬ (enabled first values ∧ enabled second values) := by
  cases first <;> cases second <;> simp only [Compatible] at compatible
  rcases compatible with ⟨rfl, different⟩
  rename_i firstZero secondZero
  cases firstZero <;> cases secondZero <;> simp_all [enabled]





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



















theorem permutation_owner (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) (edge : Fin e) (selected : active edge = true) :
    permutation owner active matching (Fin.castAdd e (owner edge)) = Fin.natAdd q edge := by
  have chosen := (mate_some owner active matching (owner edge) edge).mpr ⟨selected, rfl⟩
  simp [permutation_apply, exchange, chosen]

theorem permutation_port (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) (edge : Fin e) :
    permutation owner active matching (Fin.natAdd q edge) =
      if active edge then Fin.castAdd e (owner edge) else Fin.natAdd q edge := by
  cases selected : active edge <;> simp [permutation_apply, exchange, selected]

theorem permutation_fixed_owner (owner : Fin e → Fin q) (active : Fin e → Bool)
    (matching : Matching owner active) (vertex : Fin q)
    (missing : ∀ edge, active edge = true → owner edge ≠ vertex) :
    permutation owner active matching (Fin.castAdd e vertex) = Fin.castAdd e vertex := by
  have absent : ¬ ∃ edge, active edge = true ∧ owner edge = vertex := by
    rintro ⟨edge, selected, endpoint⟩
    exact missing edge selected endpoint
  simp [permutation_apply, exchange, mate, absent]

open Counter.Reversible





/-- Numerical guard evaluation is used only in the proof interpretation. -/
theorem guard_enabled_iff (action : Action 2) (values : Fin 2 → ℤ) :
    ReversibleControl.enabled (actionGuard action) (values 0) (values 1) = true ↔
      action.enabled values := by
  cases action with
  | shift => simp [actionGuard, ReversibleControl.enabled, Action.enabled]
  | test register atZero =>
      fin_cases register <;> cases atZero <;>
        simp [actionGuard, ReversibleControl.enabled, Action.enabled] <;>
          exact decide_eq_true_iff















end Monodromy.ReversiblePorts

/-!
## Native guarded routing
-/

namespace Monodromy.ReversibleRouting

open CoupledContinuation Counter.Reversible ReversiblePorts

variable {q e : ℕ} [NeZero (q + e)]



variable (table : Table 2 q e) (owner : Fin e → Fin q)
  (matching : ∀ guard, Matching owner (selected table guard))







@[simp] theorem run_cons (guard : ReversibleControl.Guard)
    (stages : List ReversibleControl.Guard) (state : Memory) :
    run table owner matching (guard :: stages) state =
      run table owner matching stages ((route table owner matching guard).advance state) := rfl



theorem route_prepare (guard : ReversibleControl.Guard) (values : Fin 2 → ℤ)
    (index : Fin (q + e)) :
    (route table owner matching guard).advance (point values index) =
      if ReversibleControl.enabled guard (values 0) (values 1) then
        point values (permutation owner (selected table guard) (matching guard) index)
      else point values index := by
  simpa only [route, point, mul_zero, zero_add] using
    ReversibleControl.advance_prepare guard
      (permutation owner (selected table guard) (matching guard)) (values 0) (values 1) 0 index





omit [NeZero (q + e)] in
/-- A different guard cannot activate any alternative at the enabled edge's owner. -/
theorem off_guard_owner (compatible : CompatibleOwner table owner)
    (values : Fin 2 → ℤ) (edge : Fin e) (enabled : (table edge).action.enabled values)
    (guard : ReversibleControl.Guard) (different : actionGuard (table edge).action ≠ guard)
    (active : ReversibleControl.enabled guard (values 0) (values 1) = true) :
    ∀ other, selected table guard other = true → owner other ≠ owner edge := by
  intro other chosen same_owner
  have other_guard := (selected_iff table guard other).mp chosen
  have other_enabled : (table other).action.enabled values :=
    (guard_enabled_iff (table other).action values).mp (other_guard ▸ active)
  have distinct : other ≠ edge := by
    intro same
    subst other
    exact different other_guard
  exact (compatible other edge distinct same_owner).not_both values ⟨other_enabled, enabled⟩

theorem route_owner (compatible : CompatibleOwner table owner) (values : Fin 2 → ℤ)
    (edge : Fin e) (enabled : (table edge).action.enabled values)
    (guard : ReversibleControl.Guard) :
    (route table owner matching guard).advance (point values (Fin.castAdd e (owner edge))) =
      if actionGuard (table edge).action = guard then point values (Fin.natAdd q edge)
      else point values (Fin.castAdd e (owner edge)) := by
  rw [route_prepare]
  by_cases chosen : actionGuard (table edge).action = guard
  · have active : ReversibleControl.enabled guard (values 0) (values 1) = true :=
      chosen ▸ (guard_enabled_iff (table edge).action values).mpr enabled
    rw [ite_eq_left active, ite_eq_left chosen,
      permutation_owner owner (selected table guard) (matching guard) edge
        ((selected_iff table guard edge).mpr chosen)]
  · rw [ite_eq_right chosen]
    by_cases active : ReversibleControl.enabled guard (values 0) (values 1) = true
    · rw [ite_eq_left active,
        permutation_fixed_owner owner (selected table guard) (matching guard) (owner edge)
          (off_guard_owner table owner compatible values edge enabled guard chosen active)]
    · rw [ite_eq_right active]

theorem route_port (values : Fin 2 → ℤ) (edge : Fin e)
    (enabled : (table edge).action.enabled values) (guard : ReversibleControl.Guard) :
    (route table owner matching guard).advance (point values (Fin.natAdd q edge)) =
      if actionGuard (table edge).action = guard then point values (Fin.castAdd e (owner edge))
      else point values (Fin.natAdd q edge) := by
  rw [route_prepare]
  by_cases chosen : actionGuard (table edge).action = guard
  · have active : ReversibleControl.enabled guard (values 0) (values 1) = true :=
      chosen ▸ (guard_enabled_iff (table edge).action values).mpr enabled
    rw [ite_eq_left active, permutation_port, ite_eq_left ((selected_iff table guard edge).mpr chosen),
      ite_eq_left chosen]
  · rw [ite_eq_right chosen]
    by_cases active : ReversibleControl.enabled guard (values 0) (values 1) = true
    · rw [ite_eq_left active, permutation_port]
      have unselected : selected table guard edge = false := by simpa [selected] using chosen
      rw [unselected]
      rfl
    · rw [ite_eq_right active]







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
open Monodromy.ReversibleRouting
open CoupledContinuation Counter.Reversible ReversiblePorts
variable {q e : ℕ} [NeZero (q + e)]
variable (table : Table 2 q e) (owner : Fin e → Fin q)
  (matching : ∀ guard, Matching owner (selected table guard))
theorem solution (compatible : CompatibleOwner table owner) (values : Fin 2 → ℤ)
    (edge : Fin e) (enabled : (table edge).action.enabled values)
    (stages : List ReversibleControl.Guard) (distinct : stages.Nodup) :
    (run table owner matching stages (point values (Fin.castAdd e (owner edge))) =
      if actionGuard (table edge).action ∈ stages then point values (Fin.natAdd q edge)
      else point values (Fin.castAdd e (owner edge))) ∧
    (run table owner matching stages (point values (Fin.natAdd q edge)) =
      if actionGuard (table edge).action ∈ stages then point values (Fin.castAdd e (owner edge))
      else point values (Fin.natAdd q edge)) := by
  induction stages with
  | nil => simp
  | cons guard stages induction_hypothesis =>
      obtain ⟨not_member, rest_distinct⟩ := List.nodup_cons.mp distinct
      obtain ⟨owner_run, port_run⟩ := induction_hypothesis rest_distinct
      by_cases chosen : actionGuard (table edge).action = guard
      · constructor
        · rw [run_cons, route_owner table owner matching compatible values edge enabled,
            ite_eq_left chosen, port_run]
          simp [chosen, not_member]
        · rw [run_cons, route_port table owner matching values edge enabled,
            ite_eq_left chosen, owner_run]
          simp [chosen, not_member]
      · constructor
        · rw [run_cons, route_owner table owner matching compatible values edge enabled,
            ite_eq_right chosen, owner_run]
          simp [chosen]
        · rw [run_cons, route_port table owner matching values edge enabled,
            ite_eq_right chosen, port_run]
          simp [chosen]
