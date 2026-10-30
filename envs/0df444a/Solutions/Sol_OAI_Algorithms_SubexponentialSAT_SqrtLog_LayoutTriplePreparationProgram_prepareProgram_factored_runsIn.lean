-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram_factored_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:32:32.41222+00:00
-- url     : https://prove2.me/submissions/2d383eb0-e283-42f7-a425-c4defbc13547

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S043
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S091
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram_factoredEncodes_sum
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram_factoredTotalEncodes_sum
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram_loop_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutScalarEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving signed-pair emission into a reverse buffer. The existing exact
pair serializer is called on paid copies, and its output is transferred once.
All source words survive; the four work stacks are restored to empty. -/
namespace SubexponentialSAT.SqrtLog.LayoutScalarEmitter
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport

theorem finishList_eval (d : Data) (h6 : d.stacks 6 = []) :
    ∃ e, Eval finishList (3*(d.stacks 2).length+8) d e ∧
      e.stacks = Function.update (Function.update d.stacks 2 []) 6
        ((d.stacks 2).reverse ++ [false]) := by
  let a := (StructuredProgram.Atom.set (0 : Fin 8) false).eval d
  let b := (StructuredProgram.Atom.push (2 : Fin 7) (0 : Fin 8)).eval a
  have ha : Eval (.base (.atom (.set 0 false))) 1 d a := .base (.atom _ _)
  have hb : Eval (.base (.atom (.push 2 0))) 1 a b := .base (.atom _ _)
  obtain ⟨e,he,hse⟩ := transfer_eval (2 : Fin 7) 6 (by decide) b
  have hbs : b.stacks = Function.update d.stacks 2 (false :: d.stacks 2) := by
    simp [b,a,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr]
  have hall := ha.seq (hb.seq he)
  have hb2 : (b.stacks 2).length = (d.stacks 2).length+1 := by simp [hbs]
  rw [hb2] at hall
  have ht : 1+(1+(3*((d.stacks 2).length+1)+3)) = 3*(d.stacks 2).length+8 := by omega
  rw [ht] at hall
  refine ⟨e,hall,?_⟩
  rw [hse,hbs]
  funext i; fin_cases i <;> simp [StackRoutines.transferStacks,h6,List.reverse_cons]

end SubexponentialSAT.SqrtLog.LayoutScalarEmitter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixParityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A four-label program computes the sign parity of a unary index. The
bits of the counter are irrelevant; only its length is used. -/

namespace SubexponentialSAT.Subexp.MatrixParityProgram

open BitProgram

theorem nil_trace (regs : Fin 3 → Bool) :
    Trace program 3 (start regs []) (finish (regs 2)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, start, finish, execInstr, readRegs]
  funext j
  fin_cases j <;> simp

theorem cons_trace (regs : Fin 3 → Bool) (bit : Bool) (bits : List Bool) :
    Trace program 3 (start regs (bit :: bits))
      (start ![bit, true, !(regs 2)] bits) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, start, execInstr, readRegs]
  all_goals first
    | (constructor
       · funext j
         fin_cases j <;> simp
       · funext j
         fin_cases j
         rfl)
    | (funext j
       fin_cases j <;> simp)

theorem program_trace (regs : Fin 3 → Bool) (bits : List Bool) :
    Trace program (3 * bits.length + 3) (start regs bits)
      (finish (toggle bits.length (regs 2))) := by
  induction bits generalizing regs with
  | nil => exact nil_trace regs
  | cons bit bits ih =>
      have ht := (cons_trace regs bit bits).trans (ih ![bit, true, !(regs 2)])
      convert ht using 1
      · simp only [List.length_cons]
        omega
      · simp [toggle]

theorem sign_toggle {K : Type*} [Ring K] (n : ℕ) (b : Bool) :
    sign (K := K) (toggle n b) = (-1 : K)^n * sign b := by
  induction n generalizing b with
  | zero => simp [toggle]
  | succ n ih =>
      rw [toggle, ih, pow_succ]
      cases b <;> simp [sign ]

theorem false_sign_toggle {K : Type*} [Ring K] (n : ℕ) :
    sign (K := K) (toggle n false) = (-1 : K)^n := by
  simpa [sign] using sign_toggle (K := K) n false

end SubexponentialSAT.Subexp.MatrixParityProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed port assignments for cache access and triple serialization. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem workRegisters_injective : Function.Injective workRegisters := Fin.castAdd_injective _ _

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


-- LayoutTriplePreparationProgramLookup.lean

/-! List-level cache representation for the preserving physical array scan. -/

/-! One real triple-production iteration: two scans, three serializers and
paid cleanup. Only a parity bit is kept outside the subroutine registers. -/

/-! A fixed, paid iteration producing the three real scalar operands. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

theorem Cache.Hword_length (c : Cache) (hu : c.Uniform) (i : ℕ)
    (hp : i < c.Hpositive.length) (hn : i < c.Hnegative.length) :
    pairLength (c.Hword i) = 2*c.width.length := by
  have h1 := hu.1 (c.Hpositive[i]) (List.getElem_mem hp)
  have h2 := hu.2.1 (c.Hnegative[i]) (List.getElem_mem hn)
  simp only [Cache.Hword,pairLength,List.getD_eq_getElem _ _ hp,List.getD_eq_getElem _ _ hn]
  omega

theorem Cache.Bword_length (c : Cache) (hu : c.Uniform) (i : ℕ)
    (hp : i < c.Bpositive.length) (hn : i < c.Bnegative.length) :
    pairLength (c.Bword i) = 2*c.width.length := by
  have h1 := hu.2.2.1 (c.Bpositive[i]) (List.getElem_mem hp)
  have h2 := hu.2.2.2 (c.Bnegative[i]) (List.getElem_mem hn)
  simp only [Cache.Bword,pairLength,List.getD_eq_getElem _ _ hp,List.getD_eq_getElem _ _ hn]
  omega

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramLoop.lean

/-! The native unary loop produces all triples in increasing binomial index. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open SubexponentialSAT.Subexp.MatrixParityProgram (toggle)

theorem loopCost_le (n k W P : ℕ) :
    loopCost n k W P ≤ n*((n+k)*(28*W+34)+140*W+18*P+222)+2 := by
  induction n generalizing k with
  | zero => simp [loopCost]
  | succ n ih =>
    have ht := ih (k+1)
    simp only [loopCost,bodyCost]
    nlinarith

theorem preparedRecords_encoding (c : Cache) (sign : Bool) (n k : ℕ) :
    pairEncoding (tripleWords (preparedTriples c sign n k)) =
      preparedRecords c sign n k ++ [false] := by
  have h : ∀ xs : List Triple,
      pairEncoding (tripleWords xs) = xs.flatMap tripleRecord ++ [false] := by
    intro xs
    induction xs with
    | nil => rfl
    | cons t xs ih =>
      change pairEncoding (t.1::t.2.1::t.2.2::tripleWords xs) =
        (tripleRecord t ++ xs.flatMap tripleRecord) ++ [false]
      simp only [pairEncoding]
      rw [ih]
      simp [tripleRecord,wordRecord,LayoutScalarEmitter.record,
        RowSelectionProgram.Entries.pairPrefix,List.append_assoc]
  exact h _

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramFinish.lean

/-! Initial unary copy/parity and final stream reversal are native paid calls. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open SubexponentialSAT.Subexp.MatrixParityProgram (toggle)

theorem parityRegisters_injective : Function.Injective parityRegisters := by decide
theorem parityPorts_injective : Function.Injective parityPorts := by decide

theorem parityCall_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool) :
    ∃ r, r 8 = toggle parity.length (regs 8) ∧
      Eval parityCall (3*parity.length+3)
        (cacheState c regs counter hindex kindex buffer queue parity)
        (cacheState c r counter hindex kindex buffer queue []) := by
  let d := cacheState c regs counter hindex kindex buffer queue parity
  let a := projectState parityRegisters parityPorts d
  let b : State 3 1 := ⟨![false,false,toggle parity.length (regs 8)],fun _ => []⟩
  have ht : Trace SubexponentialSAT.Subexp.MatrixParityProgram.program (3*parity.length+3)
      (a.withPC (some SubexponentialSAT.Subexp.MatrixParityProgram.program.entry)) (b.withPC none) := by
    have hstart : a.withPC (some SubexponentialSAT.Subexp.MatrixParityProgram.program.entry) =
        SubexponentialSAT.Subexp.MatrixParityProgram.start a.regs parity := by
      congr 1
    have ha2 : a.regs 2 = regs 8 := rfl
    rw [hstart]
    simpa [b, SubexponentialSAT.Subexp.MatrixParityProgram.finish,
      StructuredProgram.State.withPC, ha2] using
      SubexponentialSAT.Subexp.MatrixParityProgram.program_trace a.regs parity
  let e := embedState parityRegisters parityPorts d b
  have he := eval_call_from_state SubexponentialSAT.Subexp.MatrixParityProgram.program
    parityRegisters parityPorts d parityRegisters_injective parityPorts_injective ht
  have hr : e.regs 8 = toggle parity.length (regs 8) := by
    have h := embedState_register parityRegisters parityPorts d b parityRegisters_injective 2
    simpa [e,parityRegisters,b] using h
  have hbs : b.stacks = Function.update a.stacks 0 [] := by funext j; fin_cases j; rfl
  have hst : e.stacks = Function.update d.stacks 19 [] := by
    change Function.extend parityPorts b.stacks d.stacks = _
    rw [hbs,ProgramLinking.extend_update parityPorts_injective]
    have hf := congrArg StructuredProgram.State.stacks
      (embedState_project parityRegisters parityPorts d parityRegisters_injective parityPorts_injective)
    change Function.extend parityPorts a.stacks d.stacks = d.stacks at hf
    rw [hf]
    rfl
  have heq : e = cacheState c e.regs counter hindex kindex buffer queue [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    change e.stacks = _
    rw [hst]
    funext j
    fin_cases j <;> simp [d,cacheState]
  exact ⟨e.regs,hr,by simpa only [parityCall,← heq] using he⟩

theorem initializeTriples_eval (c : Cache) (regs : Fin 9 → Bool) (counter parity : List Bool) :
    ∃ r, r 8 = toggle parity.length false ∧
      Eval initializeTriples (7*counter.length+3*parity.length+9)
        (cacheState c regs counter [] [] [] [] parity)
        (cacheState c r counter counter [] [] [] []) := by
  let d := cacheState c regs counter [] [] [] [] parity
  have hc := StackRoutines.halt_after_trace _
    (StackRoutines.copyProgram_trace (7 : Fin 20) 8 10 (0 : Fin 9) 1
      (by decide) (by decide) (by decide) (by decide) d.regs d.stacks rfl) 7 rfl rfl
  let r0 := readRegs regs 0 1 none
  have hcopy : Eval (.call (StackRoutines.copyProgram 7 8 10 0 1)) (7*counter.length+5)
      d (cacheState c r0 counter counter [] [] [] parity) := by
    apply Eval.call
    convert hc using 1 <;>
      simp [d,r0,cacheState,StackRoutines.copyResult,
        StructuredProgram.State.withPC,StackRoutines.copyStacks,Nat.add_assoc]
    funext j
    fin_cases j <;> simp
  let r1 := Function.update r0 8 false
  have hset : Eval (.base (.atom (.set 8 false))) 1
      (cacheState c r0 counter counter [] [] [] parity)
      (cacheState c r1 counter counter [] [] [] parity) := by
    exact .base (.atom _ _)
  obtain ⟨r,hr,hp⟩ := parityCall_eval c r1 counter counter [] [] [] parity
  refine ⟨r,by simpa [r1] using hr,?_⟩
  convert hcopy.seq (hset.seq hp) using 1
  · rfl
  · ring

theorem finishPorts_injective : Function.Injective finishPorts := by decide

theorem finish_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer parity : List Bool) :
    ∃ r, Eval finish (3*buffer.length+9)
      (cacheState c regs counter hindex kindex buffer [] parity)
      (cacheState c r counter hindex kindex [] (buffer.reverse++[false]) parity) := by
  let d := cacheState c regs counter hindex kindex buffer [] parity
  let a := projectState workRegisters finishPorts d
  obtain ⟨b,hb,hbs⟩ := LayoutScalarEmitter.finishList_eval a rfl
  let e := embedState workRegisters finishPorts d b
  have he := eval_liftCommand_from_state LayoutScalarEmitter.finishList 2 6
    workRegisters finishPorts d workRegisters_injective finishPorts_injective hb
  have hst : e.stacks = Function.update (Function.update d.stacks 17 []) 18
      (buffer.reverse++[false]) := by
    change Function.extend finishPorts b.stacks d.stacks = _
    rw [hbs,ProgramLinking.extend_update finishPorts_injective,
      ProgramLinking.extend_update finishPorts_injective]
    have hf := congrArg StructuredProgram.State.stacks
      (embedState_project workRegisters finishPorts d workRegisters_injective finishPorts_injective)
    change Function.extend finishPorts a.stacks d.stacks = d.stacks at hf
    rw [hf]
    rfl
  have heq : e = cacheState c e.regs counter hindex kindex [] (buffer.reverse++[false]) parity := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    change e.stacks = _
    rw [hst]
    funext j
    fin_cases j <;> simp [d,cacheState]
  change Eval _ _ d e at he
  rw [heq] at he
  refine ⟨e.regs,?_⟩
  simpa [finish,a,d,projectState,finishPorts,cacheState,Nat.add_assoc] using he

theorem clearIndex_eval (c : Cache) (regs : Fin 9 → Bool) (kindex queue : List Bool) :
    Eval clearIndex (2*kindex.length+3)
      (cacheState c regs [] [] kindex [] queue [])
      (cacheState c (readRegs regs 0 1 none) [] [] [] [] queue []) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.clear_eval (9 : Fin 20) (0 : Fin 9) 1
    (cacheState c regs [] [] kindex [] queue [])
  have hs : StackRoutines.clearStacks 9 (cacheState c regs [] [] kindex [] queue []).stacks =
      (cacheState c regs [] [] [] [] queue []).stacks := by
    funext j
    fin_cases j <;> simp [StackRoutines.clearStacks,cacheState]
  rw [hs] at h
  simpa [clearIndex,cacheState] using h

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgram.lean

/-! Complete cache-to-triple primitive program with all scans and copies paid. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open SubexponentialSAT.Subexp.MatrixParityProgram (toggle)

theorem signedPair_length (s : Bool) (p n : List Bool) :
    pairLength (signedPair s p n) = p.length+n.length := by
  cases s <;> simp [signedPair,pairLength,Nat.add_comm]

theorem tripleRecord_length (c : Cache) (s : Bool) (n k : ℕ)
    (hu : c.Uniform) (hhp : n < c.Hpositive.length) (hhn : n < c.Hnegative.length)
    (hbp : k < c.Bpositive.length) (hbn : k < c.Bnegative.length) :
    (tripleRecord (triple c s n k)).length = 8*c.width.length+2*pairLength c.power+9 := by
  have hh := c.Hword_length hu n hhp hhn
  have hb := c.Bword_length hu k hbp hbn
  simp only [tripleRecord,triple,List.length_append,wordRecord,LayoutScalarEmitter.record_length]
  change ((2*pairLength (signedPair s (c.Hword n).1 (c.Hword n).2)+3)+
    (2*pairLength c.power+3))+(2*pairLength (c.Bword k)+3) = _
  rw [signedPair_length]
  change ((2*pairLength (c.Hword n)+3)+(2*pairLength c.power+3))+(2*pairLength (c.Bword k)+3) = _
  rw [hh,hb]
  ring

theorem preparedRecords_length (c : Cache) (s : Bool) (n k : ℕ)
    (hu : c.Uniform) (hf : c.Fits (n+k)) :
    (preparedRecords c s n k).length = n*(8*c.width.length+2*pairLength c.power+9) := by
  induction n generalizing s k with
  | zero => simp [preparedRecords,preparedTriples]
  | succ n ih =>
    have ht := tripleRecord_length c s n k hu (by have := hf.1; omega)
      (by have := hf.2.1; omega) (by have := hf.2.2.1; omega) (by have := hf.2.2.2; omega)
    have hf' : c.Fits (n+(k+1)) := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hf
    have hi := ih (!s) (k+1) hf'
    simp only [preparedRecords,preparedTriples,List.flatMap_cons,List.length_append] at ht hi ⊢
    rw [ht,hi]
    ring

/-- The only nonempty input stacks are the retained caches, width, power,
the unary number of terms, and the unary parity exponent. -/
theorem prepare_eval (c : Cache) (regs : Fin 9 → Bool) (counter parity : List Bool)
    (hu : c.Uniform) (hf : c.Fits counter.length) :
    ∃ r, Eval prepare (prepareCost counter.length parity.length c.width.length (pairLength c.power))
      (cacheState c regs counter [] [] [] [] parity)
      (cacheState c r [] [] [] []
        (pairEncoding (tripleWords
          (preparedTriples c (toggle parity.length false) counter.length 0))) []) := by
  obtain ⟨r0,hr0,hi⟩ := initializeTriples_eval c regs counter parity
  obtain ⟨r1,hr1,hl⟩ := loop_eval c r0 counter counter [] [] [] [] hu
    (by simpa using hf) rfl
  rw [hr0] at hl
  simp only [List.length_nil,List.append_nil] at hl
  let records := preparedRecords c (toggle parity.length false) counter.length 0
  obtain ⟨r2,hf2⟩ := finish_eval c r1 [] [] (List.replicate counter.length true) records.reverse []
  have hc := clearIndex_eval c r2 (List.replicate counter.length true)
    (records.reverse.reverse++[false])
  have hlen : records.length = counter.length*(8*c.width.length+2*pairLength c.power+9) :=
    preparedRecords_length c _ _ _ hu (by simpa using hf)
  have hencoding : records++[false] =
      pairEncoding (tripleWords
        (preparedTriples c (toggle parity.length false) counter.length 0)) :=
    (preparedRecords_encoding c _ _ _).symm
  have hfinish := hf2.seq hc
  have hloop := hl.seq hfinish
  have hall := hi.seq hloop
  simp only [List.length_reverse,List.length_replicate,hlen,List.reverse_reverse,hencoding] at hall
  have ht : (7*counter.length+3*parity.length+9) +
      (loopCost counter.length 0 c.width.length (pairLength c.power) +
        ((3*(counter.length*(8*c.width.length+2*pairLength c.power+9))+9) +
          (2*counter.length+3))) =
      prepareCost counter.length parity.length c.width.length (pairLength c.power) := by
    unfold prepareCost
    ring
  rw [ht] at hall
  refine ⟨readRegs r2 0 1 none,?_⟩
  simpa only [prepare] using hall

theorem prepareCost_le (N A W P : ℕ) :
    prepareCost N A W P ≤
      9*N+3*A+N*(N*(28*W+34)+140*W+18*P+222)+3*(N*(8*W+2*P+9))+23 := by
  have h := loopCost_le N 0 W P
  simp only [Nat.add_zero] at h
  unfold prepareCost
  omega

/-- A concrete finite program, including its final halt, with no arithmetic
oracle in the transition relation. All original cache words are retained. -/
theorem prepareProgram_runsIn (c : Cache) (regs : Fin 9 → Bool) (counter parity : List Bool)
    (hu : c.Uniform) (hf : c.Fits counter.length) :
    ∃ r, RunsIn prepareProgram
      (9*counter.length+3*parity.length+
        counter.length*(counter.length*(28*c.width.length+34)+140*c.width.length+
          18*pairLength c.power+222)+
        3*(counter.length*(8*c.width.length+2*pairLength c.power+9))+24)
      ((cacheState c regs counter [] [] [] [] parity).withPC (some prepareProgram.entry))
      ((cacheState c r [] [] [] []
        (pairEncoding (tripleWords
          (preparedTriples c (toggle parity.length false) counter.length 0))) []).withPC none) := by
  obtain ⟨r,he⟩ := prepare_eval c regs counter parity hu hf
  refine ⟨r,⟨_,?_,compiled_halt_trace he 7 18⟩⟩
  have h := prepareCost_le counter.length parity.length c.width.length (pairLength c.power)
  omega

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramInterface
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

-- LayoutTriplePreparationProgramAlgebra.lean

/-! The factored triple stream uses the positive H cache directly. The outer
parity and both powers in a scalar summand are combined before serialization. -/

/-! The actual generated stream has the exact coefficient sum and nonnegative
mass required by the scalar machine, despite the factored cache representation. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open scoped BigOperators
open RowSelectionProgram LayoutProgramScalar LayoutCoefficientRecurrence
open SubexponentialSAT.Subexp.MatrixParityProgram (toggle sign)

theorem signedPair_value (s : Bool) (p n : List Bool) :
    pairValue (signedPair s p n) = sign s * pairValue (p,n) := by
  cases s <;> simp [signedPair,pairValue,sign,RowSelectionProgram.signedValue]

theorem signedPair_total (s : Bool) (p n : List Bool) :
    wordTotal (signedPair s p n) = wordTotal (p,n) := by
  cases s <;> simp [signedPair,wordTotal,pairTotal,Nat.add_comm]

theorem preparedTriples_eq_ofFn (c : Cache) (s : Bool) (n k : ℕ) :
    preparedTriples c s n k = List.ofFn (fun i : Fin n =>
      triple c (toggle i.val s) (n-1-i.val) (k+i.val)) := by
  induction n generalizing s k with
  | zero => rfl
  | succ n ih =>
    rw [preparedTriples,List.ofFn_succ]
    congr 1
    rw [ih]
    apply congrArg List.ofFn
    funext i
    simp only [Fin.val_succ,toggle]
    congr 1 <;> omega

theorem preparedTriples_get (c : Cache) (s : Bool) (n k i : ℕ) (hi : i < n) :
    (preparedTriples c s n k)[i]'(by simpa using hi) =
      triple c (toggle i s) (n-1-i) (k+i) := by
  simp [preparedTriples_eq_ofFn]

theorem prepared_factoredEncodes (c : Cache) (A R d h : ℕ)
    (hv : c.Values A R h) :
    FactoredEncodes A R d h (preparedTriples c (toggle A false) (R-d) 0) := by
  refine ⟨preparedTriples_length c _ _ _,?_⟩
  intro k
  have hk : k.val < R-d := by simpa using k.isLt
  have hi : R-d-1-k.val < R := by omega
  have hkR : k.val < R := by omega
  have hget := preparedTriples_get c (toggle A false) (R-d) 0 k.val hk
  simp only [List.get_eq_getElem] at ⊢
  rw [hget]
  have hsign : sign (K := ℤ) (toggle k.val (toggle A false)) = (-1 : ℤ)^(A+k.val) := by
    rw [SubexponentialSAT.Subexp.MatrixParityProgram.sign_toggle,
      SubexponentialSAT.Subexp.MatrixParityProgram.false_sign_toggle,pow_add,mul_comm]
  have hindex : R-d-1-k.val = R-1-d-k.val := by omega
  change pairValue (signedPair (toggle k.val (toggle A false))
      (c.Hword (R-d-1-k.val)).1 (c.Hword (R-d-1-k.val)).2) = _ ∧
    pairValue c.power = _ ∧ pairValue (c.Bword (0+k.val)) = _
  rw [signedPair_value,hsign,hv.1 _ hi,hindex]
  exact ⟨rfl,hv.2.1,by simpa using hv.2.2 _ hkR⟩

theorem prepared_bounded (c : Cache) (s : Bool) (n k B : ℕ)
    (hu : c.Uniform) (hf : c.Fits (n+k))
    (hW : 2*c.width.length ≤ B) (hP : pairLength c.power ≤ B) :
    Bounded B (preparedTriples c s n k) := by
  induction n generalizing s k with
  | zero => simp [Bounded,preparedTriples]
  | succ n ih =>
    have hh := c.Hword_length hu n (by have := hf.1; omega) (by have := hf.2.1; omega)
    have hb := c.Bword_length hu k (by have := hf.2.2.1; omega) (by have := hf.2.2.2; omega)
    have hf' : c.Fits (n+(k+1)) := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hf
    intro t ht
    simp only [preparedTriples,List.mem_cons] at ht
    rcases ht with rfl | ht
    · change pairLength (signedPair s (c.Hword n).1 (c.Hword n).2) ≤ B ∧
        pairLength c.power ≤ B ∧ pairLength (c.Bword k) ≤ B
      rw [signedPair_length]
      exact ⟨by change pairLength (c.Hword n) ≤ B; omega,hP,by omega⟩
    · exact ih (!s) (k+1) hf' t ht

theorem prepared_totalEncodes (c : Cache) (A R d h : ℕ)
    (hv : c.Totals A R h) (s : Bool) :
    FactoredTotalEncodes A R d h (preparedTriples c s (R-d) 0) := by
  refine ⟨preparedTriples_length c _ _ _,?_⟩
  intro k
  have hk : k.val < R-d := by simpa using k.isLt
  have hi : R-d-1-k.val < R := by omega
  have hkR : k.val < R := by omega
  have hget := preparedTriples_get c s (R-d) 0 k.val hk
  simp only [List.get_eq_getElem] at ⊢
  rw [hget]
  simp only [termTotal,triple,signedPair_total,Nat.zero_add]
  rw [hv.1 _ hi,hv.2.1,hv.2.2 _ hkR]
  have hindex : R-d-1-k.val = R-1-d-k.val := by omega
  rw [hindex]

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramInterface.lean

/-! One consumer-facing contract for native triple preparation. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

/-- The produced stream is already in the scalar machine's exact triple order.
Its signed sum is the numerator and its total is the no-cancellation budget. -/
theorem prepareProgram_factored_runsIn_oai (c : Cache) (regs : Fin 9 → Bool)
    (counter parity : List Bool) (A R d h : ℕ)
    (hc : counter.length = R-d) (ha : parity.length = A)
    (hu : c.Uniform) (hf : c.Fits (R-d))
    (hv : c.Values A R h) (hm : c.Totals A R h) :
    ∃ r xs,
      RunsIn prepareProgram
        (9*(R-d)+3*A+(R-d)*((R-d)*(28*c.width.length+34)+140*c.width.length+
          18*pairLength c.power+222)+3*((R-d)*(8*c.width.length+2*pairLength c.power+9))+24)
        ((cacheState c regs counter [] [] [] [] parity).withPC (some prepareProgram.entry))
        ((cacheState c r [] [] [] []
          (pairEncoding (LayoutProgramScalar.tripleWords xs)) []).withPC none) ∧
      FactoredEncodes A R d h xs ∧ FactoredTotalEncodes A R d h xs ∧
      LayoutProgramScalar.Bounded (2*c.width.length+pairLength c.power) xs ∧
      (xs.map LayoutProgramScalar.termValue).sum = LayoutCoefficientAlgorithm.scalarSum A R d h ∧
      (xs.map LayoutProgramScalar.termTotal).sum = LayoutProgram.scalarMass R d h
        (fun j => (LayoutCoefficientAlgorithm.coefficientAt A R j).natAbs) := by
  let xs := preparedTriples c (SubexponentialSAT.Subexp.MatrixParityProgram.toggle A false) (R-d) 0
  obtain ⟨r,he⟩ := prepareProgram_runsIn c regs counter parity hu (by simpa [hc] using hf)
  have hx : FactoredEncodes A R d h xs := prepared_factoredEncodes c A R d h hv
  have ht : FactoredTotalEncodes A R d h xs := prepared_totalEncodes c A R d h hm _
  refine ⟨r,xs,by simpa [hc,ha,xs,tripleWords,LayoutProgramScalar.tripleWords] using he,hx,ht,?_,
    factoredEncodes_sum A R d h xs hx,factoredTotalEncodes_sum A R d h xs ht⟩
  exact prepared_bounded c _ (R-d) 0 _ hu (by simpa using hf) (by omega) (by omega)

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram_factored_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram_factored_runsIn_oai
