-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.local_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:55:54.296934+00:00
-- url     : https://prove2.me/submissions/2e073e39-f862-4698-a7ed-4112ffed33aa

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S098
import Definitions.Def_OAIQ081S108

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed frame emitter. The source is a reversed payload. It is consumed
and the forward framed payload is prepended to the destination. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

theorem frameBody_eval (regs : Fin 3 → Bool) (b : Bool)
    (source output : List Bool) (htrue : regs 2 = true) :
    Eval frameBody 3 (frameReady regs (b :: source) output)
      (frameReady (readRegs regs 0 1 (some b)) source (true :: b :: output)) := by
  let d := frameReady regs (b :: source) output
  let d1 := (Atom.push (1 : Fin 2) (0 : Fin 3)).eval d
  let d2 := (Atom.push (1 : Fin 2) (2 : Fin 3)).eval d1
  have hh := Eval.seq (Eval.atom (Atom.push (1 : Fin 2) (0 : Fin 3)) d)
    (Eval.seq (Eval.atom (Atom.push (1 : Fin 2) (2 : Fin 3)) d1)
      (Eval.atom (Atom.pop (0 : Fin 2) (0 : Fin 3) 1) d2))
  convert hh using 1 ;
    simp [ frameReady, frameData, d, d1, d2, Atom.eval, Atom.instr,
      State.ofCfg, execInstr, readRegs, htrue] ;
    try (first | done | (funext i; fin_cases i <;> rfl))

theorem frameLoop_eval (source output : List Bool) (regs : Fin 3 → Bool)
    (htrue : regs 2 = true) :
    ∃ final, final 2 = true ∧ Eval frameLoop (4 * source.length + 1)
      (frameReady regs source output) (frameData final [] (emitPairs source output)) := by
  induction source generalizing regs output with
  | nil =>
    refine ⟨readRegs regs 0 1 none, by simpa [readRegs] using htrue, ?_⟩
    apply Eval.while_false
    simp [frameReady, frameData, readRegs]
  | cons b bs ih =>
    have hr : (readRegs regs 0 1 (some b)) 2 = true := by simpa [readRegs] using htrue
    obtain ⟨final, hf, he⟩ := ih (true :: b :: output) (readRegs regs 0 1 (some b)) hr
    refine ⟨final, hf, ?_⟩
    have hh := Eval.while_true
      (by simp [frameReady, frameData, readRegs] : (frameReady regs (b :: bs) output).regs 1 = true)
      (frameBody_eval regs b bs output htrue) he
    have hc : 3 + (4 * bs.length + 1) + 1 = 4 * (b :: bs).length + 1 := by simp; omega
    rw [hc] at hh
    exact hh

theorem emitPairs_append (a b out : List Bool) :
    emitPairs (a ++ b) out = emitPairs b (emitPairs a out) := by
  induction a generalizing out with
  | nil => rfl
  | cons x xs ih => simpa [emitPairs] using ih (true :: x :: out)

theorem emitPairs_frame (source out : List Bool) :
    emitPairs source.reverse (false :: out) = Encoding.frame source ++ out := by
  induction source with
  | nil => rfl
  | cons b bs ih =>
    simp [List.reverse_cons, emitPairs_append, emitPairs, ih, Encoding.frame ]

theorem frameEmit_eval (source output : List Bool) (regs : Fin 3 → Bool) :
    ∃ final, Eval frameEmit (4 * source.length + 5)
      (frameData regs source.reverse output)
      (frameData final [] (Encoding.frame source ++ output)) := by
  let r0 := Function.update regs (2 : Fin 3) false
  let r1 := Function.update r0 (2 : Fin 3) true
  have h0 : Eval (.atom (.set 2 false)) 1 (frameData regs source.reverse output)
      (frameData r0 source.reverse output) := Eval.atom _ _
  have h1 : Eval (.atom (.push 1 2)) 1 (frameData r0 source.reverse output)
      (frameData r0 source.reverse (false :: output)) := by
    convert Eval.atom (Atom.push (1 : Fin 2) (2 : Fin 3)) (frameData r0 source.reverse output) using 1
    all_goals try with_reducible_and_instances rfl
    simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, frameData, r0]
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have h2 : Eval (.atom (.set 2 true)) 1 (frameData r0 source.reverse (false :: output))
      (frameData r1 source.reverse (false :: output)) := Eval.atom _ _
  have h3 : Eval (.atom (.pop 0 0 1)) 1 (frameData r1 source.reverse (false :: output))
      (frameReady r1 source.reverse (false :: output)) := by
    convert Eval.atom (Atom.pop (0 : Fin 2) (0 : Fin 3) 1) (frameData r1 source.reverse (false :: output)) using 1
    all_goals try with_reducible_and_instances rfl
    cases source.reverse <;>
      simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, frameData, frameReady] ;
      (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨final, _, hf⟩ := frameLoop_eval source.reverse (false :: output) r1 (by simp [r1])
  rw [emitPairs_frame] at hf
  refine ⟨final, ?_⟩
  have hh := h0.seq (h1.seq (h2.seq (h3.seq hf)))
  convert hh using 1 ; simp [] ; omega

theorem frameEmit_trace (source output : List Bool) (regs : Fin 3 → Bool) :
    ∃ final, Trace frameEmitProgram (4 * source.length + 6)
      ((frameData regs source.reverse output).withPC (some frameEmitProgram.entry))
      ((frameData final [] (Encoding.frame source ++ output)).withPC none) := by
  obtain ⟨final,hf⟩ := frameEmit_eval source output regs
  refine ⟨final, ?_⟩
  simpa [frameEmitProgram, Nat.add_assoc] using compiled_halt_trace hf 0 1
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramPrepend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed primitive emission of a key/coefficient record. Both source words
are reversed; all bits, framing tags and source cleanup are executed. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem payloadPorts_injective : Function.Injective payloadPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [payloadPorts]
theorem keyPorts_injective : Function.Injective keyPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [keyPorts]

theorem embedPayload (regs rr : Fin 3 → Bool) (key coeff output coeff' output' : List Bool) :
    embedState id payloadPorts (prependData regs key coeff output) (frameData rr coeff' output') =
      prependData rr key coeff' output' := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id payloadPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [payloadPorts,prependData,Fin.exists_fin_succ]

theorem embedKey (regs rr : Fin 3 → Bool) (key coeff output key' output' : List Bool) :
    embedState id keyPorts (prependData regs key coeff output) (frameData rr key' output') =
      prependData rr key' coeff output' := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id keyPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [keyPorts,prependData,Fin.exists_fin_succ]

theorem prependRecord_eval (regs : Fin 3 → Bool) (key coeff output : List Bool) :
    ∃ final, Eval prependRecord (4 * key.length + 4 * coeff.length + 12)
      (prependData regs key.reverse coeff.reverse output)
      (prependData final [] [] (Encoding.frame key ++ Encoding.frame coeff ++ output)) := by
  obtain ⟨r1,hp⟩ := frameEmit_trace coeff output regs
  have hp' := eval_call_lifted frameEmitProgram id payloadPorts
    (prependData regs key.reverse coeff.reverse output)
    Function.injective_id payloadPorts_injective hp
  simp only [embedPayload] at hp'
  obtain ⟨r2,hk⟩ := frameEmit_trace key (Encoding.frame coeff ++ output) r1
  have hk' := eval_call_lifted frameEmitProgram id keyPorts
    (prependData r1 key.reverse [] (Encoding.frame coeff ++ output))
    Function.injective_id keyPorts_injective hk
  simp only [embedKey] at hk'
  refine ⟨r2,?_⟩
  convert hp'.seq hk' using 1 <;> try omega
  simp [List.append_assoc]

theorem prependRecord_trace (regs : Fin 3 → Bool) (key coeff output : List Bool) :
    ∃ final, Trace prependRecordProgram (4 * key.length + 4 * coeff.length + 13)
      ((prependData regs key.reverse coeff.reverse output).withPC (some prependRecordProgram.entry))
      ((prependData final [] [] (Encoding.frame key ++ Encoding.frame coeff ++ output)).withPC none) := by
  obtain ⟨final,he⟩ := prependRecord_eval regs key coeff output
  exact ⟨final,by simpa [prependRecordProgram,Nat.add_assoc] using compiled_halt_trace he 0 2⟩
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseLiteralPadding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Padding arbitrary literal payloads for the dense interpreter

The existing five-label padding table already truncates long inputs. This
module proves that behavior without a length precondition, then connects the
table to the actual framed operand stack. The cached dense zero array supplies
the requested bit width; no dimension is baked into the program control.
-/

namespace SubexponentialSAT.SubexpDenseLiteralPadding

open BitProgram StructuredCalls ModularArithmetic ModularPrograms
open SubexpConvolutionControl (Store Code ExecutesIn)

theorem padding_exit_any (regs : Fin 8 → Bool) (input output : List Bool) :
    Trace paddingProgram 3 (paddingCfg (some 0) regs [] input output)
      (paddingCfg none (readRegs regs 1 3 none) [] input output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, paddingProgram, execInstr,
    paddingCfg, readRegs, operandStacks, Function.update_apply]

theorem padding_trace_any (regs : Fin 8 → Bool) (shape input output : List Bool) :
    ∃ rf : Fin 8 → Bool,
      Trace paddingProgram (4 * shape.length + 3)
        (paddingCfg (some 0) regs shape input output)
        (paddingCfg none rf [] (input.drop shape.length) ((padTo shape input).reverse ++ output)) := by
  induction shape generalizing regs input output with
  | nil =>
      refine ⟨readRegs regs 1 3 none, ?_⟩
      simpa [padTo] using padding_exit_any regs input output
  | cons bit shape ih =>
      obtain ⟨rf, ht⟩ := ih (paddingRegs regs bit input) input.tail
        (input.head?.getD false :: output)
      refine ⟨rf, ?_⟩
      have h := (padding_round regs bit shape input output).trans ht
      cases input <;> convert h using 1 <;>
        simp [padTo, List.reverse_cons, List.append_assoc] <;> omega

end SubexponentialSAT.SubexpDenseLiteralPadding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramConstant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Construct a cached sparse constant from a shape word and a forward flat
coefficient. Zero support bits, key delimiters, reversal, record framing and
cleanup all execute on the native bit machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem padStacks_injective : Function.Injective padStacks := Fin.castAdd_injective _ _

private theorem embedPad (regs rr : Fin 8 → Bool)
    (shape input before coeff rev out shape' input' after : List Bool) :
    embedState id padStacks (data regs shape input before coeff rev out)
      (⟨rr,ModularPrograms.operandStacks shape' input' after⟩ : State 8 3) =
        data rr shape' input' after coeff rev out := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id padStacks_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [padStacks,data,Fin.exists_fin_succ]

theorem pad_eval (regs : Fin 8 → Bool) (shape coeff : List Bool) :
    ∃ rr, Eval pad (4*shape.length+3) (data regs shape [] [] coeff [] [])
      (data rr [] [] (List.replicate shape.length false) coeff [] []) := by
  obtain ⟨rr,h⟩ := SubexponentialSAT.SubexpDenseLiteralPadding.padding_trace_any regs shape [] []
  have ht : Trace ModularPrograms.paddingProgram (4*shape.length+3)
      ((⟨regs,ModularPrograms.operandStacks shape [] []⟩ : State 8 3).withPC
        (some ModularPrograms.paddingProgram.entry))
      ((⟨rr,ModularPrograms.operandStacks [] (([] : List Bool).drop shape.length)
        ((ModularArithmetic.padTo shape []).reverse ++ [])⟩ : State 8 3).withPC none) := by
    simpa [ModularPrograms.paddingCfg,ModularPrograms.paddingProgram,StructuredProgram.State.withPC] using h
  have he := eval_call_lifted ModularPrograms.paddingProgram id padStacks
    (data regs shape [] [] coeff [] []) Function.injective_id padStacks_injective ht
  simp only [embedPad] at he
  have hp : ModularArithmetic.padTo shape [] = List.replicate shape.length false := by
    clear h ht he
    induction shape with
    | nil => rfl
    | cons b shape ih => simpa [ModularArithmetic.padTo,List.replicate_succ] using congrArg (false :: ·) ih
  refine ⟨rr,?_⟩
  simpa [hp] using he

theorem tag_eval (regs : Fin 8 → Bool) (n : ℕ) (coeff : List Bool) :
    Eval tag 3 (data regs [] [] (List.replicate n false) coeff [] [])
      (data (Function.update regs 0 false) [] [] (key n) coeff [] []) := by
  let d := data regs [] [] (List.replicate n false) coeff [] []
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 8) false) d)).seq
    ((Eval.base (StructuredProgram.Eval.atom (.push (2 : Fin 6) (0 : Fin 8)) _)).seq
      (Eval.base (StructuredProgram.Eval.atom (.push (2 : Fin 6) (0 : Fin 8)) _)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;>
      simp [d,data,key,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr,List.replicate_succ]

theorem reverseCoefficient_eval (regs : Fin 8 → Bool) (k coeff : List Bool) :
    Eval reverseCoefficient (3*coeff.length+3) (data regs [] [] k coeff [] [])
      (data (readRegs regs 0 1 none) [] [] k [] coeff.reverse []) := by
  let d := data regs [] [] k coeff [] []
  have h := StackRoutines.transferProgram_trace (3 : Fin 6) 4 (0 : Fin 8) 1
    (by decide) (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  have hs : StackRoutines.transferStacks (3 : Fin 6) 4 d.stacks =
      (data (readRegs regs 0 1 none) [] [] k [] coeff.reverse []).stacks := by
    funext i; fin_cases i <;> simp [d,data,StackRoutines.transferStacks]
  apply Eval.call
  simp only [StackRoutines.transferResult] at hh
  rw [hs] at hh
  simpa [d,data,StructuredProgram.State.withPC,StackRoutines.transferProgram,Nat.add_assoc] using hh

theorem emitRegisters_injective : Function.Injective emitRegisters := Fin.castAdd_injective _ _
theorem emitStacks_injective : Function.Injective emitStacks := by decide

private theorem embedEmit (regs : Fin 8 → Bool) (rr : Fin 3 → Bool)
    (beforeKey beforeCoeff beforeOut k c o : List Bool) :
    embedState emitRegisters emitStacks (data regs [] [] beforeKey [] beforeCoeff beforeOut)
      (Squarefree.Program.prependData rr k c o) =
        data (Function.extend emitRegisters rr regs) [] [] k [] c o := by
  apply embedState_eq_of_ports _ _ _ _ _ emitRegisters_injective emitStacks_injective
  · intro i
    exact emitRegisters_injective.extend_apply rr regs i
  · intro i hi
    exact Function.extend_apply' rr regs i hi
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [emitStacks,data,Fin.exists_fin_succ]

theorem emit_eval (regs : Fin 8 → Bool) (n : ℕ) (coeff : List Bool) :
    ∃ rr, Eval emit (4*(n+2)+4*coeff.length+13)
      (data regs [] [] (key n) [] coeff.reverse [])
      (data rr [] [] [] [] [] (Encoding.frame (key n) ++ Encoding.frame coeff)) := by
  obtain ⟨rr,h⟩ := Squarefree.Program.prependRecord_trace (regs ∘ emitRegisters) (key n) coeff []
  have he := eval_call_lifted Squarefree.Program.prependRecordProgram emitRegisters emitStacks
    (data regs [] [] (key n) [] coeff.reverse []) emitRegisters_injective emitStacks_injective h
  have hr : Function.extend emitRegisters (regs ∘ emitRegisters) regs = regs := by
    funext i
    by_cases hi : ∃ j, emitRegisters j = i
    · obtain ⟨j,rfl⟩ := hi
      exact emitRegisters_injective.extend_apply _ _ _
    · exact Function.extend_apply' _ _ _ hi
  simp only [embedEmit,hr] at he
  refine ⟨Function.extend emitRegisters rr regs,?_⟩
  simpa [key] using he

theorem command_eval (regs : Fin 8 → Bool) (shape coeff : List Bool) :
    ∃ rr, Eval command (8*shape.length+7*coeff.length+30)
      (data regs shape [] [] coeff [] [])
      (data rr [] [] [] [] [] (Encoding.frame (key shape.length) ++ Encoding.frame coeff)) := by
  obtain ⟨r1,h1⟩ := pad_eval regs shape coeff
  have h2 := tag_eval r1 shape.length coeff
  have h3 := reverseCoefficient_eval (Function.update r1 0 false) (key shape.length) coeff
  obtain ⟨r4,h4⟩ := emit_eval (readRegs (Function.update r1 0 false) 0 1 none) shape.length coeff
  refine ⟨r4,?_⟩
  convert h1.seq (h2.seq (h3.seq h4)) using 1 ; omega

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafNodeCacheProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical staging of node-local cached ring words. The ambient source tapes
and ring masters are copied, never consumed. The two raw-one caches are built
by the checked sparse-constant program, rather than supplied semantically. -/
namespace SubexponentialSAT.SqrtLog.LeafNodeCacheProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem constantStacks_injective : Function.Injective constantStacks := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [constantStacks] at this
  omega

private theorem prepared_word (a : LocalData) (h : Ready a.stacks) :
    (prepared a).stacks 340 = a.stacks 128 ∧
    (prepared a).stacks 343 = a.stacks 207 ∧
    (∀ i ∈ ([341,342,344,345,346,69,167] : List (Fin 768)), (prepared a).stacks i=[]) := by
  have h340 := h 340 (by decide)
  have h343 := h 343 (by decide)
  constructor
  · simp [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks,h340]
  constructor
  · simp [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks,h343]
  · intro i hi
    have hi' : i=341 ∨ i=342 ∨ i=344 ∨ i=345 ∨ i=346 ∨ i=69 ∨ i=167 := by simpa using hi
    rcases hi' with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks] using h 341 (by decide)
    · simpa [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks] using h 342 (by decide)
    · simpa [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks] using h 344 (by decide)
    · simpa [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks] using h 345 (by decide)
    · simpa [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks] using h 346 (by decide)
    · simpa [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks] using h 69 (by decide)
    · simpa [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks] using h 167 (by decide)

private theorem constant_embed (a : LocalData) (rr : Fin 8 → Bool) (word : List Bool) :
    embedState constantRegisters constantStacks a
      (HashCircuitProgram.Constant.data rr [] [] [] [] [] word) = constantResult a rr word := by
  apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective _ _) constantStacks_injective
  · intro i
    exact (Fin.castAdd_injective _ _).extend_apply _ _ i
  · intro i hi
    exact Function.extend_apply' _ _ _ hi
  · intro i; fin_cases i  <;> simp [constantStacks,constantResult,constantTapes,HashCircuitProgram.Constant.data]
  · intro i hi
    have hn (j : Fin 6) : i ≠ constantStacks j := fun h => hi ⟨j,h.symm⟩
    have h345 : i ≠ 345 := hn 5
    have hr : ¬(340 ≤ i.val ∧ i.val < 345) := by
      rintro ⟨hl,hu⟩
      have he : i = constantStacks ⟨i.val-340,by omega⟩ := by apply Fin.ext; simp [constantStacks]; omega
      exact hn _ he
    simp [constantResult,constantTapes,h345,hr]

private theorem constant_eval (a : LocalData) (h : Ready a.stacks) :
    ∃ rr, Eval constant (8*(a.stacks 128).length+7*(a.stacks 207).length+31)
      (prepared a) (constantResult (prepared a) rr (rawOne a.stacks)) := by
  obtain ⟨h340,h343,hrest⟩ := prepared_word a h
  obtain ⟨rr,he⟩ := HashCircuitProgram.Constant.command_eval
    ((prepared a).regs ∘ constantRegisters) (a.stacks 128) (a.stacks 207)
  have hp : project constantRegisters constantStacks (prepared a) =
      HashCircuitProgram.Constant.data ((prepared a).regs ∘ constantRegisters)
        (a.stacks 128) [] [] (a.stacks 207) [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i  <;>
        simpa [project,constantStacks,HashCircuitProgram.Constant.data] using
          (show (prepared a).stacks _ = _ from by first | exact h340 | exact h343 | exact hrest _ (by decide))
  have ht := compiled_halt_trace he 0 5
  rw [← hp] at ht
  have hc := invoke_eval HashCircuitProgram.Constant.program constantRegisters constantStacks
    (Fin.castAdd_injective _ _) constantStacks_injective (prepared a) _ ht
  refine ⟨rr,?_⟩
  simpa [constant,invoke,constant_embed,rawOne,Nat.add_assoc] using hc

/-- Every copy, sparse-constant construction and private-pocket clear is paid.
The theorem applies to arbitrary external frames and arbitrary registers. -/
theorem local_eval_oai (a : LocalData) (h : Ready a.stacks) :
    ∃ rr, Eval localCommand (localBudget a) a
      (finalState (prepared a) rr (rawOne a.stacks)) := by
  have htmp := h 346 (by decide)
  have hp := copyMany_eval (346:Fin 768) copies a (by simp [copies,directCopies]) htmp
  obtain ⟨rr,hc⟩ := constant_eval a h
  have hrest := (prepared_word a h).2.2
  let b := constantResult (prepared a) rr (rawOne a.stacks)
  have hbtemp : b.stacks 346=[] := by simp [b,constantResult,constantTapes,hrest 346 (by decide)]
  have hd := copyMany_eval (346:Fin 768) [(345,69),(345,167)] b (by simp) hbtemp
  have hf := clear_eval (345:Fin 768) (copyManyState [(345,69),(345,167)] b)
  have hdCost : copyManyCost [(345,69),(345,167)] b = 14*(rawOne a.stacks).length+10 := by
    simp [copyManyCost,copyState,StackRoutines.copyStacks,b,constantResult,constantTapes]
    omega
  have hfCost : 2*((copyManyState [(345,69),(345,167)] b).stacks 345).length+3 =
      2*(rawOne a.stacks).length+3 := by
    simp [copyManyState,copyState,StackRoutines.copyStacks,b,constantResult,constantTapes]
  have ht : copyManyCost copies a +
      ((8*(a.stacks 128).length+7*(a.stacks 207).length+31) +
        (copyManyCost [(345,69),(345,167)] b +
          (2*((copyManyState [(345,69),(345,167)] b).stacks 345).length+3))) = localBudget a := by
    rw [hdCost,hfCost]
    unfold localBudget
    omega
  have he := hp.seq (hc.seq (hd.seq hf))
  rw [ht] at he
  exact ⟨rr,he⟩


end SubexponentialSAT.SqrtLog.LeafNodeCacheProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.local_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.local_eval_oai
