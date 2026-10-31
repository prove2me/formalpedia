-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.prepare_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:33:41.451852+00:00
-- url     : https://prove2.me/submissions/75395eef-a778-45b7-8f82-bb7aab759732

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSelectionSpace_prepare_trace_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureKeyNative_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

theorem clearStacks_frame {S : Type u} [DecidableEq S] (src j : S) (stk : Stacks S)
    (hj : j ≠ src) : clearStacks src stk j = stk j := by
  simp [clearStacks, hj]

open BitProgram

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BankRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite banks of stack-copy and stack-clear routines

The port lists below are part of the finite program syntax.  Word contents and
word lengths remain runtime inputs.  Each call is justified by an actual trace
of the existing stack routine, including its return instruction.  A final clear
of an already empty temporary gives a uniform reset of the two read registers,
including when the port list is empty.
-/

namespace SubexponentialSAT.BankRoutines

open BitProgram StackRoutines StructuredCalls

universe u

theorem clearBankStacks_frame {S : Type u} [DecidableEq S]
    (j : S) (ports : List S) (stk : Stacks S) (hj : j ∉ ports) :
    clearBankStacks ports stk j = stk j := by
  simp [clearBankStacks, hj]

theorem clearStacks_eq_self_of_empty {S : Type u} [DecidableEq S]
    (tmp : S) (stk : Stacks S) (htmp : stk tmp = []) :
    clearStacks tmp stk = stk := by
  funext j
  by_cases hj : j = tmp
  · subst j
    simp [htmp]
  · exact clearStacks_frame _ _ _ hj

theorem clearBankStacks_cons {S : Type u} [DecidableEq S]
    (dst : S) (ports : List S) (stk : Stacks S) :
    clearBankStacks ports (clearStacks dst stk) =
      clearBankStacks (dst :: ports) stk := by
  funext j
  by_cases hj : j = dst
  · subst j
    simp [clearBankStacks]
  · simp [clearBankStacks, clearStacks, hj]

theorem clear_call_eval {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Eval (.call (clearProgram src value present)) (2 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearStacks src stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src value present regs stk

/-- Exact clearing cost in terms of the original word lengths.  The temporary
may also occur in the bank: its initial emptiness makes the final clear cost
exactly three instructions in either case. -/
theorem clear_eval {r s : ℕ} (tmp : Fin s) (value present : Fin r)
    (ports : List (Fin s)) (hports : ports.Nodup)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmpEmpty : stk tmp = []) :
    Eval (clearCmd tmp value present ports)
      (2 * (ports.map (fun j => (stk j).length)).sum + 3 * ports.length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearBankStacks ports stk⟩ := by
  induction ports generalizing regs stk with
  | nil =>
      have run := clear_call_eval tmp value present regs stk
      simpa [clearCmd, htmpEmpty, clearStacks_eq_self_of_empty tmp stk htmpEmpty] using run
  | cons dst ports ih =>
      have hn := List.nodup_cons.mp hports
      have htemp : clearStacks dst stk tmp = [] := by
        by_cases h : tmp = dst
        · subst tmp
          simp
        · rw [clearStacks_frame dst tmp stk h, htmpEmpty]
      have hmap : ports.map (fun j => (clearStacks dst stk j).length) =
          ports.map (fun j => (stk j).length) := by
        apply List.map_congr_left
        intro j hj
        have hjd : j ≠ dst := by
          intro h
          subst j
          exact hn.1 hj
        rw [clearStacks_frame dst j stk hjd]
      have first := clear_call_eval dst value present regs stk
      have rest := ih hn.2 (readRegs regs value present none)
        (clearStacks dst stk) htemp
      have run := Eval.seq first rest
      simpa only [clearCmd, List.map_cons, List.sum_cons, List.length_cons,
        hmap, readRegs_reset, clearBankStacks_cons, Nat.mul_add,
        Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

open BitProgram

/-- Summing the port bounds counts every simultaneously live buffer. -/
theorem dataBits_le_mul {r s l bound : ℕ} (c : Cfg r s l)
    (h : ∀ i, (c.stacks i).length ≤ bound) : dataBits c ≤ s * bound := by
  simpa [dataBits, stackBits] using Finset.sum_le_card_nsmul Finset.univ
    (fun i => (c.stacks i).length) bound (fun i _ => h i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

namespace NativeHeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

theorem result_frame (a : Data) (rf : Fin 4 → Bool) (i : Fin 896)
    (hi : i ∉ changed) : (result a rf).stacks i = a.stacks i := by
  have hn : ¬ ∃ j, stackMap j=i := by
    rintro ⟨j,rfl⟩
    fin_cases j <;> simp [stackMap,changed] at hi
  rw [show (result a rf).stacks i = (copied a).stacks i from
    embedState_stack_frame regs stackMap (copied a) _ i hn]
  have h1 : i ≠ 879 := by intro he; subst i; simp [changed] at hi
  have h2 : i ≠ 878 := by intro he; subst i; simp [changed] at hi
  simp [copied,copyStacks,h1,h2]

theorem reset_frame (a : Data) (i : Fin 896) (hi : i ∉ changed) :
    (resetState a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame i changed a.stacks hi


@[simp] theorem prepared_E (a : Data) (rf : Fin 4 → Bool) :
    (result (resetState a) rf).stacks 867=Restriction.selected true (a.stacks 670) (a.stacks 858) := by
  rw [result_E,reset_frame a 670 (by decide),reset_frame a 858 (by decide)]

@[simp] theorem prepared_H (a : Data) (rf : Fin 4 → Bool) :
    (result (resetState a) rf).stacks 868=List.replicate (Restriction.highCount (a.stacks 670)) true := by
  rw [result_H,reset_frame a 670 (by decide)]

theorem prepared_frame (a : Data) (rf : Fin 4 → Bool) (i : Fin 896) (hi : i∉changed) :
    (result (resetState a) rf).stacks i=a.stacks i :=
  (result_frame (resetState a) rf i hi).trans (reset_frame a i hi)

end NativeHeadSelect

open OAI.Algorithms.SubexponentialSAT.StackRoutines


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

open BitProgram StructuredCalls

theorem copyWord_eval (src dst tmp : Fin 896)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (a : State 40 896) (he : a.stacks tmp = []) :
    Eval (copyWord src dst tmp) (7 * (a.stacks src).length + 5) a
      (copyState src dst a) := by
  have ht := StackRoutines.copyProgram_trace src dst (tmp) (0 : Fin 40) 1
    hsd hst htd (by decide) a.regs a.stacks he
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  exact .call _ (by simpa [copyState, StackRoutines.copyResult,
    StructuredProgram.State.withPC, StackRoutines.copyProgram, Nat.add_assoc] using hh)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleVisitor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The representative tuple is already a polynomial-length stack of escaped
frames, deepest head first. These fixed commands copy that stack, extract one
actual representative, and decrement its unary physical head address. They do
not enumerate assignments or construct a Cartesian product. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

open OAI BitProgram StructuredCalls
open SignatureTupleProgram

private theorem clear_eval (dst : Fin 896) (a : Data) :
    Eval (.call (StackRoutines.clearProgram dst 0 1)) (2 * (a.stacks dst).length + 3)
      a ⟨readRegs a.regs 0 1 none,StackRoutines.clearStacks dst a.stacks⟩ :=
  Eval.call _ (ListRegisterProgram.clear_run dst (0 : Fin 40) 1 a.regs a.stacks)

theorem overwrite_eval (src dst : Fin 896) (hsd : src ≠ dst)
    (hst : src ≠ 841) (htd : (841 : Fin 896) ≠ dst)
    (a : Data) (htmp : a.stacks 841 = []) :
    Eval (overwrite src dst) (2 * (a.stacks dst).length + 7 * (a.stacks src).length + 8)
      a (overwriteState src dst a) := by
  have hc := clear_eval dst a
  have ht : (StackRoutines.clearStacks dst a.stacks) 841 = [] := by
    simp [StackRoutines.clearStacks, htd, htmp]
  have hp := copyWord_eval src dst 841 hsd hst htd
    ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks dst a.stacks⟩ ht
  have hs : (StackRoutines.clearStacks dst a.stacks) src = a.stacks src := by
    simp [StackRoutines.clearStacks,hsd]
  simpa only [overwrite, overwriteState, hs, show 2 * (a.stacks dst).length + 3 +
    (7 * (a.stacks src).length + 5) =
    2 * (a.stacks dst).length + 7 * (a.stacks src).length + 8 by omega] using hc.seq hp

theorem overwriteState_stacks (src dst : Fin 896) (hsd : src ≠ dst) (a : Data) :
    (overwriteState src dst a).stacks = Function.update a.stacks dst (a.stacks src) := by
  funext i
  by_cases hi : i = dst
  · subst i
    simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hsd]
  · simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hi]

/-- Repeated passes retain the same word bound: overwrite replaces one word,
rather than appending to a growing visit history. -/
theorem overwriteState_bound (src dst : Fin 896) (hsd : src ≠ dst)
    (a : Data) (B : ℕ) (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((overwriteState src dst a).stacks i).length ≤ B := by
  intro i
  rw [overwriteState_stacks src dst hsd]
  by_cases hi : i = dst
  · subst i
    rw [Function.update_self]
    exact hb src
  · rw [Function.update_of_ne hi]
    exact hb i

theorem overwriteState_frame (src dst : Fin 896) (hsd : src ≠ dst)
    (a : Data) (i : Fin 896) (hi : i ≠ dst) :
    (overwriteState src dst a).stacks i = a.stacks i := by
  rw [overwriteState_stacks src dst hsd,Function.update_of_ne hi]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Composition of the concrete streamed query. The traversal resource lemma
keeps the per-head execution time separate from its prefix storage bound;
neither the number of assignments nor their running time is used as space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution

open OAI BitProgram StructuredCalls
open QueryTupleVisitor SignatureTupleProgram

theorem PrefixBound.mono {command : Code} {steps B D : ℕ} {a : Data}
    (h : PrefixBound command steps a B) (hBD : B ≤ D) :
    PrefixBound command steps a D :=
  ⟨fun q z hq hz i => (h.bound q z hq hz i).trans hBD⟩

theorem prefix_local (command : Code) (steps B : ℕ) (a : Data)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    PrefixBound command steps a (896*B+steps) := by
  constructor
  exact StructuredSpace.local_stack_bound (compiled command 838 838)
    (StreamResources.dataBits_le_mul _ ha)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The attained-tuple traversal retains the actual query inputs and the
meaning of its current pair accumulator. These predicates contain word
identities and algebraic facts, with no execution or algorithm-service fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram Subexp.ConstructivePacking MulticolorTypes
open TruncatedRingProgram SubexpSetupStorage

namespace QueryReady

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ} {a b : Data}
    (h : QueryReady q node H high E U P a) (hf : QueryMasterFrame a b) :
    QueryReady q node H high E U P b := by
  refine {
    lifting := h.lifting
    generatedTheta := h.generatedTheta
    sourceMinus := h.sourceMinus
    ambient := (hf.word 128 (by decide)).trans h.ambient
    theta := (hf.word 78 (by decide)).trans h.theta
    modulus := (hf.word 194 (by decide)).trans h.modulus
    table := (hf.word 201 (by decide)).trans h.table
    width := (hf.word 202 (by decide)).trans h.width
    scalarZero := (hf.word 203 (by decide)).trans h.scalarZero
    degree := (hf.word 204 (by decide)).trans h.degree
    one := (hf.word 207 (by decide)).trans h.one
    minus := (hf.word 211 (by decide)).trans h.minus
    precision := (hf.word 212 (by decide)).trans h.precision
    order := (hf.word 243 (by decide)).trans h.order
    zero := (hf.word 280 (by decide)).trans h.zero
    code := (hf.word 281 (by decide)).trans h.code
    clauses := (hf.word 700 (by decide)).trans h.clauses
    rows := (hf.word 701 (by decide)).trans h.rows
    rowCount := (hf.word 704 (by decide)).trans h.rowCount
    markedIndex := (hf.word 705 (by decide)).trans h.markedIndex
    markedFlag := (hf.word 706 (by decide)).trans h.markedFlag
    indexModulus := (congrArg BinaryArithmetic.toNat (hf.word 707 (by decide))).trans h.indexModulus
    indexWidth := (congrArg List.length (hf.word 708 (by decide))).trans h.indexWidth
    highMask := (hf.word 702 (by decide)).trans h.highMask
    highBits := (hf.word 703 (by decide)).trans h.highBits
    outer := (hf.word 858 (by decide)).trans h.outer
    inner := (hf.word 857 (by decide)).trans h.inner
    outerFree := h.outerFree
    innerSubset := h.innerSubset
    colors := (hf.word 130 (by decide)).trans h.colors
    nodes := (hf.word 131 (by decide)).trans h.nodes
    typeWidth := (hf.word 132 (by decide)).trans h.typeWidth
    positive := (hf.word 710 (by decide)).trans h.positive
    negative := (hf.word 711 (by decide)).trans h.negative
    sourceWidth := (hf.word 140 (by decide)).trans h.sourceWidth
    power := (hf.word 712 (by decide)).trans h.power
    powerNegative := h.powerNegative
    radius := (hf.word 138 (by decide)).trans h.radius
    offset := (hf.word 139 (by decide)).trans h.offset
    metadata := (hf.word 135 (by decide)).trans h.metadata
    plans := (hf.word 136 (by decide)).trans h.plans
    inverses := (hf.word 713 (by decide)).trans h.inverses
    negatives := (hf.word 714 (by decide)).trans h.negatives
    differences := (hf.word 715 (by decide)).trans h.differences
    ringWidth := (hf.word 717 (by decide)).trans h.ringWidth
    rowWidth := (hf.word 716 (by decide)).trans h.rowWidth
    inverseDenominator := (hf.word 728 (by decide)).trans h.inverseDenominator
    cacheCaps := ?_
    ambientCap := ?_
    oneCap := ?_ }
  · intro p hp
    have hm : p.1.castAdd 128∈masterPorts := by
      simp only [LeafNodeCacheProgram.directCopies,List.mem_cons,
        List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [hf.word _ hm]
    exact h.cacheCaps p hp
  · rw [hf.word 128 (by decide)]
    exact h.ambientCap
  · rw [hf.word 207 (by decide)]
    exact h.oneCap

end QueryReady

namespace DenseWord

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {port : Fin 896}
    {value : Dense (q.p.model.O q.p.t) q.p.t q.J} {a b : Data}
    (h : DenseWord q port value a) (hf : b.stacks port=a.stacks port) :
    DenseWord q port value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end DenseWord

namespace PairAccumulatorMeaning

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {value : Truncated (q.p.model.O q.p.t) q.J} {a b : Data}
    (h : PairAccumulatorMeaning q value a) (hf : b.stacks 851=a.stacks 851) :
    PairAccumulatorMeaning q value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end PairAccumulatorMeaning

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureKeyNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# One full integer signature on the leaf ABI

All port numbers here are leaf-local. The actual key-only machine preserves
the assignment, shifted matrix and every unrelated caller word; it has no
predecessor, countdown, or signature-table input.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative

open BitProgram StructuredCalls AttainedSignatureProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

theorem Ready.projection {a : State 40 896} {W bits : List Bool}
    {rows : List (List (List Bool))} (ready : Ready a W bits rows) :
    projectState registers stackPorts a = state (a.regs ∘ registers) W bits rows [] := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i
  change a.stacks (stackPorts i) = _
  by_cases h0 : i = 0
  · subst i; exact ready.offset
  by_cases h12 : i = 12
  · subst i; exact ready.assignment
  by_cases h14 : i = 14
  · subst i; exact ready.output
  by_cases h15 : i = 15
  · subst i; exact ready.matrix
  rw [ready.scratch i h0 h12 h14 h15]
  fin_cases i <;> simp_all

theorem output_stacks (a : State 40 896) (out : Fin 8 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool))) (ready : Ready a W bits rows) :
    (outputState a out W bits rows).stacks =
      Function.update a.stacks (stackPorts 14) (signatureValue W bits rows) := by
  have hlocal : (state out W bits rows (signatureValue W bits rows)).stacks =
      Function.update (state (a.regs ∘ registers) W bits rows []).stacks 14
        (signatureValue W bits rows) := by
    funext i
    fin_cases i <;> simp [state]
  have hemb : Function.extend stackPorts
      (state (a.regs ∘ registers) W bits rows []).stacks a.stacks = a.stacks := by
    change (embedState registers stackPorts a (state (a.regs ∘ registers) W bits rows [])).stacks = _
    rw [← ready.projection, embedState_project _ _ _ registers.injective stackPorts.injective]
  change Function.extend stackPorts _ a.stacks = _
  rw [hlocal, ProgramLinking.extend_update stackPorts.injective, hemb]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid setup for one visited signature head. The physical key workspace,
old master words and selector outputs are cleared by the command itself. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare

open BitProgram StructuredCalls StackRoutines
open HighQueryAdapter QueryTupleVisitor
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

theorem reset_eval (a : State 40 896) : Eval reset (resetCost a) a (resetState a) := by
  have first := BankRoutines.clear_call_eval (841 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have rest := BankRoutines.clear_eval (841 : Fin 896) (0 : Fin 40) 1 cleared (by decide)
    (readRegs a.regs 0 1 none) (clearStacks 841 a.stacks) (by simp)
  have he : BankRoutines.clearBankStacks cleared (clearStacks 841 a.stacks) =
      BankRoutines.clearBankStacks cleared a.stacks := by
    funext i
    by_cases hi : i ∈ cleared
    · simp [BankRoutines.clearBankStacks, hi]
    · have h841 : i ≠ 841 := by intro h; subst i; exact hi (by decide)
      simp [BankRoutines.clearBankStacks, clearStacks, hi, h841]
  simpa only [reset, resetCost, resetState, show cleared.length = 14 from rfl,
    show 3 * 14 + 3 = 45 by omega, he, readRegs_reset] using first.seq rest

theorem reset_frame (a : State 40 896) (i : Fin 896) (hi : i ∉ cleared) :
    (resetState a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame i cleared a.stacks hi

theorem reset_bound (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((resetState a).stacks i).length ≤ B := by
  intro i
  by_cases hi : i ∈ cleared
  · simp [resetState, BankRoutines.clearBankStacks, hi]
  · simpa only [reset_frame a i hi] using ha i

theorem reset_cost_le (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) : resetCost a ≤ 30 * B + 48 := by
  have hs : (cleared.map (fun i => ((clearStacks 841 a.stacks) i).length)).sum ≤ 14 * B := by
    apply (List.sum_le_card_nsmul _ B (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      by_cases he : i = 841
      · subst i; simp
      · simpa [clearStacks, he] using ha i)).trans_eq
    simp [cleared]
  have h841 := ha 841
  unfold resetCost
  omega

/-- Only the concrete immutable input words are premises; scratch and output
readiness are established by the paid reset. -/
theorem reset_ready (a : State 40 896) (W bits : List Bool)
    (rows : List (List (List Bool)))
    (hW : a.stacks 141 = W) (hbits : a.stacks 838 = bits)
    (hrows : a.stacks 847 = words (rows.map words)) :
    SignatureKeyNative.Ready (resetState a) W bits rows := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (reset_frame a 141 (by decide)).trans hW
  · exact (reset_frame a 838 (by decide)).trans hbits
  · exact BankRoutines.clearBankStacks_mem 866 cleared a.stacks (by decide)
  · exact (reset_frame a 847 (by decide)).trans hrows
  · intro i h0 h12 h14 h15
    apply BankRoutines.clearBankStacks_mem
    fin_cases i <;> first | contradiction | decide

theorem masters_eval (a : State 40 896) (htmp : a.stacks 841 = []) :
    Eval masters (2 * (a.stacks 864).length + 7 * (a.stacks 141).length +
      2 * (a.stacks 865).length + 7 * (a.stacks 847).length +
      2 * (a.stacks 175).length + 7 * (a.stacks 671).length + 24) a (mastersState a) := by
  have first := overwrite_eval 141 864 (by decide) (by decide) (by decide) a htmp
  have second := overwrite_eval 847 865 (by decide) (by decide) (by decide)
    (overwriteState 141 864 a)
    (by simpa only [overwriteState_frame 141 864 (by decide) a 841 (by decide)] using htmp)
  have third := overwrite_eval 671 175 (by decide) (by decide) (by decide)
    (overwriteState 847 865 (overwriteState 141 864 a))
    (by simpa only [overwriteState_frame 847 865 (by decide) _ 841 (by decide),
      overwriteState_frame 141 864 (by decide) a 841 (by decide)] using htmp)
  have all := first.seq (second.seq third)
  simp only [overwriteState_frame 141 864 (by decide) a 865 (by decide),
    overwriteState_frame 141 864 (by decide) a 847 (by decide),
    overwriteState_frame 847 865 (by decide) _ 175 (by decide),
    overwriteState_frame 847 865 (by decide) _ 671 (by decide),
    overwriteState_frame 141 864 (by decide) a 175 (by decide),
    overwriteState_frame 141 864 (by decide) a 671 (by decide)] at all
  convert all using 1
  · rfl
  · omega
  · rfl

theorem masters_stacks (a : State 40 896) :
    (mastersState a).stacks = Function.update
      (Function.update (Function.update a.stacks 864 (a.stacks 141)) 865 (a.stacks 847))
      175 (a.stacks 671) := by
  rw [mastersState, overwriteState_stacks 671 175 (by decide),
    overwriteState_stacks 847 865 (by decide),
    overwriteState_stacks 141 864 (by decide)]
  simp

theorem masters_bound (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((mastersState a).stacks i).length ≤ B :=
  overwriteState_bound 671 175 (by decide) _ B
    (overwriteState_bound 847 865 (by decide) _ B
      (overwriteState_bound 141 864 (by decide) a B ha))

/-- The complete paid preparation keeps the same boundary envelope for the
next head. Its transient bound includes all896 caller stacks and the actual
compiled halt; no successful key/scratch layout is an input premise. -/
theorem run (a : State 40 896) (W bits : List Bool)
    (rows : List (List (List Bool))) (B : ℕ)
    (hW : a.stacks 141 = W) (hbits : a.stacks 838 = bits)
    (hrows : a.stacks 847 = words (rows.map words))
    (hrowlen : ∀ row ∈ rows, row.length = bits.length)
    (hlen : (a.stacks 670).length = (a.stacks 858).length)
    (hkey : 16 * (W.length + bits.length + (words (rows.map words)).length) +
      AttainedSignatureProgram.cost W bits rows + 1 ≤ B)
    (hselect : 11 * (a.stacks 670).length + 6 ≤ B)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ n, n + 1 ≤ 100 * B + 200 ∧ ∃ keyRegs selectRegs,
      Eval command n a (result a keyRegs selectRegs W bits rows) ∧
      Trace program (n + 1) (a.withPC (some program.entry))
        ((result a keyRegs selectRegs W bits rows).withPC none) ∧
      (∀ i, ((result a keyRegs selectRegs W bits rows).stacks i).length ≤ B) ∧
      ∀ q z, q ≤ n + 1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤ 996 * B + 200 := by
  have ready := reset_ready a W bits rows hW hbits hrows
  obtain ⟨nk, hnk, kr, hk, hkt, hkb⟩ :=
    SignatureKeyNative.run (resetState a) W bits rows ready hrowlen B (reset_bound a B ha)
  let keyed := SignatureKeyNative.outputState (resetState a) kr W bits rows
  have hkbound : ∀ i, (keyed.stacks i).length ≤ B := by
    intro i
    exact (hkb nk (keyed.withPC none) le_rfl hkt i).trans (max_le hkey le_rfl)
  have hks : keyed.stacks = Function.update (resetState a).stacks 866
      (signatureValue W bits rows) :=
    SignatureKeyNative.output_stacks (resetState a) kr W bits rows ready
  have hktmp : keyed.stacks 841 = [] := by
    rw [hks, Function.update_of_ne (by decide : (841 : Fin 896) ≠ 866)]
    exact BankRoutines.clearBankStacks_mem 841 cleared a.stacks (by decide)
  have hm := masters_eval keyed hktmp
  have hmbound := masters_bound keyed B hkbound
  have hframe (i : Fin 896) (hi : i ∉ cleared) (h864 : i ≠ 864) (h865 : i ≠ 865) (h175 : i ≠ 175) :
      (mastersState keyed).stacks i = a.stacks i := by
    have h866 : i ≠ 866 := by intro h; subst i; exact hi (by decide)
    rw [masters_stacks, Function.update_of_ne h175, Function.update_of_ne h865, Function.update_of_ne h864,
      hks, Function.update_of_ne h866, reset_frame a i hi]
  have hm670 := hframe 670 (by decide) (by decide) (by decide) (by decide)
  have hm858 := hframe 858 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨ns, sr, hs, hns, hsb⟩ := HeadSelectionSpace.prepare_trace_space
    (mastersState keyed) (a.stacks 670).length B
    (by simpa only [hm670, hm858] using hlen) (by simp only [hm670, le_refl])
    hselect hmbound
  have hse : Eval (.call NativeHeadSelect.prepareProgram) ns (mastersState keyed)
      (NativeHeadSelect.result (NativeHeadSelect.resetState (mastersState keyed)) sr) :=
    Eval.call _ hs
  have whole := (reset_eval a).seq (hk.seq (hm.seq hse))
  have htime : resetCost a + (nk +
      (2 * (keyed.stacks 864).length + 7 * (keyed.stacks 141).length +
        2 * (keyed.stacks 865).length + 7 * (keyed.stacks 847).length +
        2 * (keyed.stacks 175).length + 7 * (keyed.stacks 671).length + 24 + ns)) + 1 ≤
      100 * B + 200 := by
    have hr := reset_cost_le a B ha
    have hk864 := hkbound 864
    have hk141 := hkbound 141
    have hk865 := hkbound 865
    have hk847 := hkbound 847
    have hk175 := hkbound 175
    have hk671 := hkbound 671
    omega
  refine ⟨_, htime, kr, sr, whole, compiled_halt_trace whole 838 866, ?_, ?_⟩
  · exact hsb ns _ (Nat.le_refl ns) hs
  · intro q z hq hz i
    have hi : dataBits (a.withPC (some program.entry)) ≤ 896 * B :=
      StreamResources.dataBits_le_mul _ ha
    have hb := StructuredSpace.local_stack_bound program (steps := 100 * B + 200) hi
      q z (hq.trans htime) hz i
    omega

theorem result_frame (a : State 40 896) (kr : Fin 8 → Bool) (sr : Fin 4 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool)))
    (hW : a.stacks 141 = W) (hbits : a.stacks 838 = bits)
    (hrows : a.stacks 847 = words (rows.map words))
    (i : Fin 896) (hi : i ∉ cleared) (h864 : i ≠ 864) (h865 : i ≠ 865) (h175 : i ≠ 175)
    (hselect : i ∉ NativeHeadSelect.changed) :
    (result a kr sr W bits rows).stacks i = a.stacks i := by
  have h866 : i ≠ 866 := by intro h; subst i; exact hi (by decide)
  rw [result, NativeHeadSelect.prepared_frame _ sr i hselect, masters_stacks,
    Function.update_of_ne h175, Function.update_of_ne h865, Function.update_of_ne h864,
    SignatureKeyNative.output_stacks _ kr W bits rows (reset_ready a W bits rows hW hbits hrows),
    show SignatureKeyNative.stackPorts 14 = 866 from rfl,
    Function.update_of_ne h866, reset_frame a i hi]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Correctness of the fixed concrete two-pass visitor. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
open OAI BitProgram StructuredCalls

open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SubexpSetupStorage

theorem prepared_masterFrame (a : Data) (kr : Fin 8 → Bool) (sr : Fin 4 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool)))
    (hW : a.stacks 141=W) (hbits : a.stacks 838=bits)
    (hrows : a.stacks 847=Subexp.MatrixProgramSupport.words
      (rows.map Subexp.MatrixProgramSupport.words)) :
    QueryMasterFrame a (SignatureHeadPrepare.result a kr sr W bits rows) := by
  constructor
  intro i hi
  have hs : i∉SignatureHeadPrepare.cleared ∧ i≠864 ∧ i≠865 ∧ i≠175 ∧
      i∉HighQueryAdapter.NativeHeadSelect.changed := by
    simp only [masterPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact SignatureHeadPrepare.result_frame a kr sr W bits rows hW hbits hrows i
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2

/-- The actual full-key and correction-gate setup preserves the three
semantic invariants needed by the subsequent head sum and multiplication. -/
theorem prepare_run_oai {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
    {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
    (hv : DenseWord q 852 tupleValue a) (ha : WordBound B a)
    (W bits : List Bool) (rows : List (List (List Bool)))
    (hW : a.stacks 141=W) (hbits : a.stacks 838=bits)
    (hrows : a.stacks 847=Subexp.MatrixProgramSupport.words
      (rows.map Subexp.MatrixProgramSupport.words))
    (hrowlen : ∀ row∈rows,row.length=bits.length)
    (hlen : (a.stacks 670).length=(a.stacks 858).length)
    (hkey : 16*(W.length+bits.length+
      (Subexp.MatrixProgramSupport.words (rows.map Subexp.MatrixProgramSupport.words)).length)+
      AttainedSignatureProgram.cost W bits rows+1≤B)
    (hselect : 11*(a.stacks 670).length+6≤B) :
    ∃ steps kr sr, Eval SignatureHeadPrepare.command steps a
        (SignatureHeadPrepare.result a kr sr W bits rows) ∧
      QueryReady q node H high E U P (SignatureHeadPrepare.result a kr sr W bits rows) ∧
      PairAccumulatorMeaning q pairValue (SignatureHeadPrepare.result a kr sr W bits rows) ∧
      DenseWord q 852 tupleValue (SignatureHeadPrepare.result a kr sr W bits rows) ∧
      QueryMasterFrame a (SignatureHeadPrepare.result a kr sr W bits rows) ∧
      WordBound B (SignatureHeadPrepare.result a kr sr W bits rows) ∧
      steps+1≤100*B+200 ∧
      QueryExecution.PrefixBound SignatureHeadPrepare.command (steps+1) a (996*B+200) := by
  obtain ⟨steps,ht,kr,sr,he,_,hb,_⟩ :=
    SignatureHeadPrepare.run a W bits rows B hW hbits hrows hrowlen hlen hkey hselect ha
  have hf:=prepared_masterFrame a kr sr W bits rows hW hbits hrows
  refine ⟨steps,kr,sr,he,hr.frame hf,?_,?_,hf,hb,ht,?_⟩
  · exact hm.frame (SignatureHeadPrepare.result_frame a kr sr W bits rows hW hbits hrows
      851 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hv.frame (SignatureHeadPrepare.result_frame a kr sr W bits rows hW hbits hrows
      852 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact (QueryExecution.prefix_local SignatureHeadPrepare.command (steps+1) B a ha).mono (by omega)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.prepare_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.prepare_run_oai
