-- Prove2me | solution 1 for Monodromy.Counter.Reversible.PrimeCompression.decrement_firstReturn
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:03:16.589216+00:00
-- url     : https://prove2.me/submissions/cbe5b0f9-d85f-4f92-a1e7-c406cf5e289d

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
public import Theorems.Thm_Monodromy_Counter_Reversible_Radix_reaches_result
public import Theorems.Thm_Monodromy_Counter_Reversible_step_iff

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





theorem encode_positive (registers : Fin n → ℕ) : 0 < basis.encode registers := by
  apply Finset.prod_pos
  intro index _
  exact pow_pos (basis.isPrime index).pos _

/-- Prime valuations recover every register, uniformly in the finite dimension. -/
theorem factorization_encode (registers : Fin n → ℕ) (index : Fin n) :
    (basis.encode registers).factorization (basis.prime index) = registers index := by
  unfold encode
  rw [Nat.factorization_prod_apply (fun other _ => pow_ne_zero _ (basis.isPrime other).ne_zero)]
  rw [Finset.sum_eq_single index]
  · exact Nat.factorization_pow_self (basis.isPrime index)
  · intro other _ different
    rw [(basis.isPrime other).factorization_pow]
    exact Finsupp.single_eq_of_ne' (basis.distinct.ne different)
  · simp







theorem encode_increment (registers : Fin n → ℕ) (index : Fin n) :
    basis.encode (Function.update registers index (registers index + 1)) =
      basis.prime index * basis.encode registers := by
  unfold encode
  rw [Fintype.prod_eq_mul_prod_compl index, Fintype.prod_eq_mul_prod_compl index]
  rw [Function.update_self, pow_succ]
  have unchanged :
      (∏ other ∈ ({index}ᶜ : Finset (Fin n)), basis.prime other ^
        Function.update registers index (registers index + 1) other) =
      ∏ other ∈ ({index}ᶜ : Finset (Fin n)), basis.prime other ^ registers other := by
    apply Finset.prod_congr rfl
    intro other present
    have different : other ≠ index := by simpa using present
    rw [Function.update_of_ne different]
  rw [unchanged]
  ac_rfl

theorem prime_dvd_encode_iff (registers : Fin n → ℕ) (index : Fin n) :
    basis.prime index ∣ basis.encode registers ↔ registers index ≠ 0 := by
  rw [(basis.isPrime index).dvd_iff_one_le_factorization (basis.encode_positive registers).ne',
    basis.factorization_encode]
  omega





theorem encode_decrement (registers : Fin n → ℕ) (index : Fin n)
    (nonzero : registers index ≠ 0) :
    basis.encode (Function.update registers index (registers index - 1)) =
      basis.encode registers / basis.prime index := by
  let previous := Function.update registers index (registers index - 1)
  have restores : Function.update previous index (previous index + 1) = registers := by
    funext other
    by_cases same : other = index
    · subst other
      simp only [previous, Function.update_self]
      omega
    · simp [previous, same]
  have restores_code := basis.encode_increment previous index
  rw [restores] at restores_code
  change basis.encode previous = basis.encode registers / basis.prime index
  rw [restores_code, Nat.mul_div_cancel_left _ (basis.isPrime index).pos]

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

/-- Inclusion of the chosen edges preserves live steps; exit edges may be added. -/
theorem step_map_live (source : Table n q e) (target : Table n k f)
    (control : Fin q → Fin k) (edge : Fin e → Fin f)
    (agrees : ∀ index, target (edge index) = mapEdge control (source index))
    (source_valid : Deterministic source) (target_valid : Deterministic target)
    {first last : State n q} (transition : step source first = some last) :
    step target (mapState control first) = some (mapState control last) := by
  obtain ⟨index, enabled, result⟩ := (step_iff source source_valid).mp transition
  apply (step_iff target target_valid).mpr
  refine ⟨edge index, ?_, ?_⟩
  · rw [agrees]
    exact ⟨congrArg control enabled.1, enabled.2⟩
  · rw [agrees]
    exact congrArg (mapState control) result





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

























/-- A wire is a literal equality of control positions, not a new transition. -/
theorem interface {exit entry : Fin q} (linked : wiring.link exit = some entry) :
    control wiring exit = control wiring entry := by
  apply congrArg (nodeEquiv wiring)
  apply Subtype.ext
  rw [representative_linked wiring exit entry linked,
    representative_unlinked wiring entry (wiring.terminal linked)]











/-- Every original live step remains an actual step of the graph with identified ports. -/
theorem step_map_live (valid : Deterministic original) {first last : State n q}
    (transition : step original first = some last) :
    step (table wiring) (Glue.mapState (control wiring) first) =
      some (Glue.mapState (control wiring) last) := by
  exact Glue.step_map_live original (table wiring) (control wiring) id
    (fun _ => rfl) valid (deterministic wiring valid) transition













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





















































































@[simp] theorem boundary_source (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) : boundary basis source site.val = sourceInput basis source site := by
  simp only [boundary, dite_eq_left site.property]





























































































































/-- A retained source boundary is never removed by the static port matching. -/
theorem boundary_link_none (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (position : Fin q) :
    (wiring basis source deterministic compatible).link (boundary basis source position) = none := by
  change PortNetwork.relationLink (Connection basis source) (boundary basis source position) = none
  exact (PortNetwork.relationLink_none_iff (Connection basis source) _).mpr
    (boundary_unconnected basis source deterministic position)





/-- A connection is a control-position equality, with no intermediate transition. -/
theorem connection_controls (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    {exit entry : Fin (rawSize basis source)} (connected : Connection basis source exit entry) :
    PortNetwork.control (wiring basis source deterministic compatible) exit =
      PortNetwork.control (wiring basis source deterministic compatible) entry := by
  apply PortNetwork.interface
  change PortNetwork.relationLink (Connection basis source) exit = some entry
  exact (PortNetwork.relationLink_some_iff (Connection basis source)
    (connection_functional basis source deterministic) exit entry).mpr connected











theorem sourceEdge_of_shift (source : Table n q e) (deterministic : Deterministic source)
    (edge : Fin e) (register : Fin n) (amount : ℤ)
    (shift : (source edge).action = .shift register amount) :
    sourceEdge source (siteOfEdge source edge) = edge := by
  apply Eq.symm
  exact shift_owner_unique source (fun index => (source index).source) deterministic shift
    (sourceEdge_spec source (siteOfEdge source edge)).symm

theorem sourceRegister_of_shift (source : Table n q e) (deterministic : Deterministic source)
    (edge : Fin e) (register : Fin n) (amount : ℤ)
    (shift : (source edge).action = .shift register amount) :
    moduleRegister source (.inl (siteOfEdge source edge)) = register := by
  simp only [moduleRegister, sourceEdge_of_shift source deterministic edge register amount shift,
    shift, actionRegister]







/-- The end of a shift is joined directly to its statically specified target. -/
theorem shift_connected (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (edge : Fin e) (register : Fin n) (amount : ℤ)
    (shift : (source edge).action = .shift register amount) :
    Connection basis source (sourceShiftOutput basis source (siteOfEdge source edge))
      (boundary basis source (source edge).target) := by
  refine Or.inl ⟨siteOfEdge source edge, ?_, rfl, ?_⟩
  · simp only [sourceEdge_of_shift source deterministic edge register amount shift, shift, Action.IsShift]
  · rw [sourceEdge_of_shift source deterministic edge register amount shift]





theorem component_step_map (basis : PrimeCode.Basis n) (source : Table n q e)
    (block : Module source)
    {first last : State 2 (Radix.size (modulus basis source block))}
    (transition : step (componentTable basis source block) first = some last) :
    step (rawTable basis source) (Glue.mapState (moduleNode basis source block) first) =
      some (Glue.mapState (moduleNode basis source block) last) := by
  exact Glue.step_map_live (componentTable basis source block) (rawTable basis source)
    (moduleNode basis source block) (fun index => rawArcEquiv basis source ⟨block, index⟩)
    (fun index => by rw [rawTable_arc]; rfl)
    (component_deterministic basis source block) (raw_deterministic basis source) transition





private theorem positive_of_control_ne {d f : ℕ} (table : Table 2 d f)
    {first last : State 2 d} (run : StateTransition.Reaches (step table) first last)
    (different : first.1 ≠ last.1) : StateTransition.Reaches₁ (step table) first last := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp run with same | positive
  · exact False.elim (different (congrArg Prod.fst same.symm))
  · exact positive

/-- The forward radix module has a positive execution to its actual quotient and remainder. -/
theorem forward_query_local_positive (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source) (forward : reversed source (.inl site) = false) (value : ℕ) :
    let p := modulus basis source (.inl site)
    StateTransition.Reaches₁ (step (componentTable basis source (.inl site)))
      (Radix.point p (Radix.entry p) value 0)
      (Radix.point p (Radix.finish p (Counter.DivMod.residue p value)) (value / p : ℕ) 0) := by
  dsimp only
  apply positive_of_control_ne
  · simpa only [componentTable, forward, Bool.false_eq_true, reduceIte] using
      Radix.reaches_result (modulus basis source (.inl site)) value
  · exact radix_entry_ne_finish _ _





















theorem boundary_encode (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (state : Counter.Configuration n q) :
    Boundary basis source deterministic compatible (encode basis source deterministic compatible state) :=
  ⟨state.pc, rfl⟩

/-- A local step is executed by precisely the retained compressed table. -/
theorem mapped_step (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (block : Module source)
    {first last : State 2 (Radix.size (modulus basis source block))}
    (transition : step (componentTable basis source block) first = some last) :
    step (table basis source deterministic compatible)
      (MappedState basis source deterministic compatible block first) =
      some (MappedState basis source deterministic compatible block last) :=
  PortNetwork.step_map_live (wiring basis source deterministic compatible)
    (raw_deterministic basis source) (component_step_map basis source block transition)

/-- A local state's control is retained whenever it is the source of an actual edge. -/
theorem module_source_unlinked (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (block : Module source)
    {first last : State 2 (Radix.size (modulus basis source block))}
    (transition : step (componentTable basis source block) first = some last) :
    (wiring basis source deterministic compatible).link (moduleNode basis source block first.1) = none := by
  obtain ⟨index, enabled, _⟩ := (step_iff (rawTable basis source) (raw_deterministic basis source)).mp
    (component_step_map basis source block transition)
  have source_eq : (rawTable basis source index).source = moduleNode basis source block first.1 := enabled.1
  rw [← source_eq]
  exact (wiring basis source deterministic compatible).source_free index

/-- No step of a source module targets its own input port. -/
theorem source_target_ne_input (basis : PrimeCode.Basis n) (source : Table n q e)
    (site : SourceSite source)
    {first last : State 2 (Radix.size (modulus basis source (.inl site)))}
    (transition : step (componentTable basis source (.inl site)) first = some last) :
    last.1 ≠ sourceInputPosition basis source site := by
  obtain ⟨index, _, result⟩ := (step_iff _ (component_deterministic basis source (.inl site))).mp transition
  intro equal
  exact component_no_incoming_sourceInput basis source site index
    ((congrArg Prod.fst result).trans equal)

private theorem source_internal_step (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (site : SourceSite source)
    {first last : State 2 (Radix.size (modulus basis source (.inl site)))}
    (interior : first.1 ≠ sourceInputPosition basis source site)
    (transition : step (componentTable basis source (.inl site)) first = some last) :
    InternalStep basis source deterministic compatible
      (MappedState basis source deterministic compatible (.inl site) first)
      (MappedState basis source deterministic compatible (.inl site) last) := by
  refine ⟨mapped_step basis source deterministic compatible (.inl site) transition, ?_⟩
  rintro ⟨position, equal⟩
  have raw_equal := PortNetwork.control_unlinked_injective (wiring basis source deterministic compatible)
    (module_source_unlinked basis source deterministic compatible (.inl site) transition)
    (boundary_link_none basis source deterministic compatible position) equal
  exact sourceNode_ne_boundary basis source site first.1 interior position raw_equal

/-- A source-module run beginning past its input has only interior compiled sources. -/
theorem source_internal_reaches (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (site : SourceSite source)
    {first last : State 2 (Radix.size (modulus basis source (.inl site)))}
    (run : StateTransition.Reaches (step (componentTable basis source (.inl site))) first last)
    (interior : first.1 ≠ sourceInputPosition basis source site) :
    InternalReaches basis source deterministic compatible
      (MappedState basis source deterministic compatible (.inl site) first)
      (MappedState basis source deterministic compatible (.inl site) last) := by
  have lifted : InternalReaches basis source deterministic compatible
      (MappedState basis source deterministic compatible (.inl site) first)
      (MappedState basis source deterministic compatible (.inl site) last) ∧
      last.1 ≠ sourceInputPosition basis source site := by
    induction run with
    | refl => exact ⟨Relation.ReflTransGen.refl, interior⟩
    | tail _ transition previous =>
        exact ⟨previous.1.tail (source_internal_step basis source deterministic compatible site previous.2 transition),
          source_target_ne_input basis source site transition⟩
  exact lifted.1

/-- After its first actual step, every positive source-module run is interior
until its terminal port. No extra transition is inserted at departure. -/
theorem source_departure (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (site : SourceSite source)
    {first last : State 2 (Radix.size (modulus basis source (.inl site)))}
    (run : StateTransition.Reaches₁ (step (componentTable basis source (.inl site))) first last) :
    ∃ next, step (table basis source deterministic compatible)
      (MappedState basis source deterministic compatible (.inl site) first) = some next ∧
      InternalReaches basis source deterministic compatible next
        (MappedState basis source deterministic compatible (.inl site) last) := by
  obtain ⟨middle, initial, rest⟩ := Relation.TransGen.head'_iff.mp run
  exact ⟨MappedState basis source deterministic compatible (.inl site) middle,
    mapped_step basis source deterministic compatible (.inl site) initial,
    source_internal_reaches basis source deterministic compatible site rest
      (source_target_ne_input basis source site initial)⟩























































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
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.PrimeCompression
variable {n q e : ℕ}
theorem solution (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (before : Counter.Configuration n q) (edge : Fin e) (register : Fin n)
    (at_source : (source edge).source = before.pc)
    (instruction : (source edge).action = .shift register (-1))
    (positive : before.counters register ≠ 0) :
    FirstReturn basis source deterministic compatible
      (encode basis source deterministic compatible before)
      (encode basis source deterministic compatible
        ⟨(source edge).target, Function.update before.counters register (before.counters register - 1)⟩) := by
  let site := siteOfEdge source edge
  let p := modulus basis source (.inl site)
  let value := basis.encode before.counters
  have forward : reversed source (.inl site) = false := by
    dsimp only [site, reversed]
    rw [sourceEdge_of_shift source deterministic edge register (-1) instruction, instruction]
    change decide ((-1 : ℤ) = 1) = false
    decide
  have prime : p = basis.prime register := by
    dsimp only [p, modulus, site]
    rw [sourceRegister_of_shift source deterministic edge register (-1) instruction]
  have divisible : p ∣ value := by
    rw [prime]
    exact (basis.prime_dvd_encode_iff before.counters register).mpr positive
  have remainder_zero : Counter.DivMod.residue p value = 0 := by
    apply Fin.ext
    change value % p = 0
    exact Nat.mod_eq_zero_of_dvd divisible
  have initial : sourceInput basis source site = boundary basis source before.pc := by
    rw [← boundary_source basis source site]
    exact congrArg (boundary basis source) at_source
  have input : moduleNode basis source (.inl site) (Radix.entry p) =
      sourceInput basis source site := by
    simp [sourceInput, sourceInputPosition, forward, p]
  have output : moduleNode basis source (.inl site) (Radix.finish p 0) =
      sourceShiftOutput basis source site := by
    simp [sourceShiftOutput, forward, p]
  have final := connection_controls basis source deterministic compatible
    (shift_connected basis source deterministic edge register (-1) instruction)
  have code : basis.encode (Function.update before.counters register (before.counters register - 1)) =
      value / p := by
    rw [prime]
    exact basis.encode_decrement before.counters register positive
  have local_run := forward_query_local_positive basis source site forward value
  change StateTransition.Reaches₁ (step (componentTable basis source (.inl site)))
    (Radix.point p (Radix.entry p) value 0)
    (Radix.point p (Radix.finish p (Counter.DivMod.residue p value)) (value / p : ℕ) 0) at local_run
  rw [remainder_zero] at local_run
  have departure := source_departure basis source deterministic compatible site local_run
  simp only [MappedState, Glue.mapState, Radix.point] at departure
  rw [input, initial, output, final, ← code] at departure
  exact ⟨boundary_encode basis source deterministic compatible before,
    boundary_encode basis source deterministic compatible _, departure⟩
