-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.loop_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:44:03.322995+00:00
-- url     : https://prove2.me/submissions/2a873cf1-0b20-45b1-b55c-9c1ec0f57f2c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S119
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashInputProgram_Loop_frameRecord_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashInputProgram_Loop_frameWeight_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashInputProgram_Loop_lookup_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterConversions
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual binary-to-unary conversion

The finite controller consumes a little-endian binary counter on stack 0.
Each positive iteration pushes one true bit onto stack 1. Stack 2 is counter
scratch. The cleanup empties the counter and resets every Boolean register.
The numeric value controls execution through stack instructions only.
-/

namespace SubexponentialSAT.CounterConversions

open BitProgram StructuredProgram StructuredCalls CounterPrograms CounterForPrograms

theorem encodeNat_eval (regs : Fin 3 → Bool) (bits : List Bool) :
    ∃ n, StructuredCalls.Eval encodeNatCmd n (state regs bits [])
      (state zeroRegs [] (Encoding.encodeNat (value bits))) ∧ n ≤ coreBound bits + 2 := by
  let d := state regs bits []
  obtain ⟨n, he, hn⟩ := unary_correct (pushed false d) (by simp [pushed, d, state])
  refine ⟨2 + n, ?_, ?_⟩
  · have h := (push_eval false d).seq he
    simpa [encodeNatCmd, pushed, d, state, Encoding.encodeNat] using h
  · have hn' : n ≤ coreBound bits := by simpa [pushed, d, state] using hn
    omega

theorem encodeNat_runs (regs : Fin 3 → Bool) (bits : List Bool) :
    BitProgram.RunsIn encodeNatProgram (runtimeBound bits)
      ((state regs bits []).withPC (some encodeNatProgram.entry))
      ((state zeroRegs [] (Encoding.encodeNat (value bits))).withPC none) := by
  obtain ⟨n, he, hn⟩ := encodeNat_eval regs bits
  exact ⟨n + 1, by have := coreBound_le bits; omega,
    StructuredCalls.compiled_halt_trace he 0 1⟩

end SubexponentialSAT.CounterConversions

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native integer-representative coefficient lifting. The only arithmetic
performed by the machine is the audited dynamic padding/clearing routine. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularRingPrograms

theorem flat_constantVector (t d : ℕ) (c : ZMod 3) :
    RingProgram.flat (constantVector t d c) =
      (RingProgram.liftCoefficientRun t c).1.val ++
        List.replicate (d*baseWidth 3 t) false := by
  simp [RingProgram.flat,constantVector,List.ofFn_succ,
    SubexponentialSAT.SubexpPreparedQuartic.zeroWord,List.flatten_replicate_replicate]

theorem zeros_value (n : ℕ) : BinaryArithmetic.toNat (List.replicate n false)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,bitVal,ih]

theorem constantVector_value (t d : ℕ) (ht : 0 < t) (c : ZMod 3) :
    BinaryArithmetic.toNat (RingProgram.flat (constantVector t d c)) = c.val := by
  rw [flat_constantVector,SubexponentialSAT.SubexpFactorProgram.toNat_append,zeros_value]
  simpa using RingProgram.liftCoefficientRun_value t ht c

theorem padTo_constantVector (t d : ℕ) (ht : 0 < t) (c : ZMod 3)
    (shape input : List Bool) (hshape : shape.length=(d+1)*baseWidth 3 t)
    (hinput : BinaryArithmetic.toNat input=c.val) :
    padTo shape input = RingProgram.flat (constantVector t d c) := by
  apply SubexponentialSAT.SubexpModulusConstruction.bits_eq_of_length_of_value
  · simpa [hshape] using (padTo_length shape input)
  · rw [padTo_value_of_lt,constantVector_value t d ht c,hinput]
    rw [hinput,hshape]
    have hw : 2 ≤ baseWidth 3 t := by
      rw [RingProgram.ternary_baseWidth]
      omega
    have hW : 2 ≤ (d+1)*baseWidth 3 t := by nlinarith
    have hp := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) hW
    have hc := c.val_lt
    norm_num at hp
    omega

/-- A single fixed program produces the whole flat extension-ring constant.
The runtime shape contains one bit per output bit, and is consumed. Long padded
input representations are cleared with their actual lengths charged. -/
theorem lift_runs (t d : ℕ) (ht : 0 < t) (c : ZMod 3)
    (shape input modulus : List Bool) (hshape : shape.length=(d+1)*baseWidth 3 t)
    (hinput : BinaryArithmetic.toNat input=c.val) (regs : Fin 8 → Bool) :
    ∃ finalRegs, RunsIn normalizeProgram (7*shape.length+2*input.length+9)
      ⟨some 0,regs,normalizationState input shape [] modulus⟩
      ⟨none,finalRegs,normalizationState
        (RingProgram.flat (constantVector t d c)) [] [] modulus⟩ := by
  obtain ⟨rf,hr⟩ := normalize_correct regs input shape modulus
  rw [padTo_constantVector t d ht c shape input hshape hinput] at hr
  exact ⟨rf,hr⟩

end SubexponentialSAT.SqrtLog.HashInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoopDecode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native decoding of one raw hash digit.  The width and modulus are
runtime data.  A digit is split into its coefficient quotient and original
clause-index remainder; the latter is emitted in the source list's canonical
natural-field syntax.  No expanded clause payload is an input. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.LoopDecode
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

theorem take_eval (regs : Fin 8 → Bool) (word rest width modulus : List Bool)
    (hw : width.length = word.length) :
    Eval take (14*word.length+11)
      (data regs (word++rest) width modulus [] [] [] [])
      (data (readRegs regs 0 1 none) rest width modulus word [] [] []) := by
  have h := takeWord_eval (data regs (word++rest) width modulus [] [] [] [])
    1 2 3 0 4 0 1 (by decide) (by decide) word rest rfl rfl rfl hw
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [tapes]

theorem divide_eval (regs : Fin 8 → Bool) (rest width modulus word : List Bool) :
    ∃ n ≤ 100*(modulus.length+word.length+1)^2, ∃ rf,
      Eval divide n (data regs rest width modulus word [] [] [])
        (data rf rest width modulus []
          (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).2
          (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1 []) := by
  obtain ⟨n,hn,rf,h⟩ := SubexponentialSAT.ModularQuotientLift.programAt_eval divisionPorts modulus word regs
    (tapes rest width modulus word [] [] []) rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨n,hn,rf,?_⟩
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [tapes,
      SubexponentialSAT.ModularQuotientLift.quotientStacksAt,divisionPorts]

theorem conversionRegisters_injective : Function.Injective conversionRegisters :=
  Fin.castAdd_injective _ _
theorem conversionStacks_injective : Function.Injective conversionStacks := by decide

theorem encode_eval (regs : Fin 8 → Bool) (rest width modulus remainder quotient : List Bool) :
    ∃ n ≤ SubexponentialSAT.CounterConversions.runtimeBound remainder, ∃ rf,
      Eval encode n (data regs rest width modulus [] remainder quotient [])
        (data rf rest width modulus [] [] quotient
          (Encoding.encodeNat (SubexponentialSAT.BinaryArithmetic.toNat remainder))) := by
  let d := data regs rest width modulus [] remainder quotient []
  let a := SubexponentialSAT.CounterConversions.state (regs ∘ conversionRegisters) remainder []
  let b := SubexponentialSAT.CounterConversions.state SubexponentialSAT.CounterConversions.zeroRegs []
    (Encoding.encodeNat (SubexponentialSAT.CounterPrograms.value remainder))
  have ha : projectState conversionRegisters conversionStacks d = a := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨n,hn,ht⟩ := SubexponentialSAT.CounterConversions.encodeNat_runs
    (regs ∘ conversionRegisters) remainder
  change Trace SubexponentialSAT.CounterConversions.encodeNatProgram n
    (a.withPC (some SubexponentialSAT.CounterConversions.encodeNatProgram.entry)) (b.withPC none) at ht
  rw [← ha] at ht
  have h := eval_call_from_state SubexponentialSAT.CounterConversions.encodeNatProgram
    conversionRegisters conversionStacks d conversionRegisters_injective
    conversionStacks_injective ht
  let rf := (embedState conversionRegisters conversionStacks d b).regs
  have hb : embedState conversionRegisters conversionStacks d b =
      data rf rest width modulus [] [] quotient
        (Encoding.encodeNat (SubexponentialSAT.CounterPrograms.value remainder)) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : ∃ j, conversionStacks j = i
      · obtain ⟨j,rfl⟩ := hi
        exact (embedState_stack conversionRegisters conversionStacks d b
          conversionStacks_injective j).trans (by fin_cases j <;> rfl)
      · apply (embedState_stack_frame conversionRegisters conversionStacks d b i hi).trans
        have h5 : i ≠ 5 := fun h => hi ⟨0,h.symm⟩
        have h12 : i ≠ 12 := fun h => hi ⟨1,h.symm⟩
        fin_cases i <;> simp_all [d,data,tapes]
  rw [hb,SubexponentialSAT.CounterPrograms.value_eq_toNat] at h
  exact ⟨n,hn,rf,h⟩

end SubexponentialSAT.SqrtLog.HashInputProgram.LoopDecode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoopReverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The raw selector parser exposes a reversed payload. Decode its last
fixed-width digit first, reversing only that digit, so prepending emitted
records later restores the original tuple order. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.LoopDecode
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

theorem reverseChunk_eval (regs : Fin 8 → Bool) (word rest width modulus : List Bool) :
    Eval reverseChunk (9*word.length+7)
      (data regs rest width modulus word.reverse [] [] [])
      (data (readRegs regs 0 1 none) rest width modulus word [] [] []) := by
  have h := reverse_eval (data regs rest width modulus word.reverse [] [] [])
    4 2 3 0 1 (by decide) (by decide) (by decide) (by decide) rfl rfl
  convert h using 1
  · simp [tapes]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [tapes,StackRoutines.reverseStacks]

theorem reversedCommand_eval (regs : Fin 8 → Bool) (word rest width modulus : List Bool)
    (hw : width.length = word.length) (hm : 0 < SubexponentialSAT.BinaryArithmetic.toNat modulus) :
    ∃ n ≤ budget word.length modulus.length (SubexponentialSAT.BinaryArithmetic.toNat modulus)+
        9*word.length+7, ∃ rf,
      Eval reversedCommand n (data regs (word.reverse++rest) width modulus [] [] [] [])
        (data rf rest width modulus [] []
          (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
          (Encoding.encodeNat (SubexponentialSAT.BinaryArithmetic.toNat word %
            SubexponentialSAT.BinaryArithmetic.toNat modulus))) := by
  have ht := take_eval regs word.reverse rest width modulus (by simpa using hw)
  have hv := reverseChunk_eval (readRegs regs 0 1 none) word rest width modulus
  obtain ⟨nd,hnd,rd,hd⟩ := divide_eval
    (readRegs (readRegs regs 0 1 none) 0 1 none) rest width modulus word
  obtain ⟨ne,hne,re,he⟩ := encode_eval rd rest width modulus
    (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).2
    (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
  have hr := SubexponentialSAT.ModularQuotientArithmetic.divide_remainder_correct modulus word hm
  rw [hr] at he
  have hb : ne ≤ 32*(SubexponentialSAT.BinaryArithmetic.toNat modulus+1)*(modulus.length+word.length+1) := by
    unfold SubexponentialSAT.CounterConversions.runtimeBound at hne
    rw [SubexponentialSAT.CounterPrograms.value_eq_toNat,hr,
      SubexponentialSAT.ModularQuotientArithmetic.divide_remainder_length] at hne
    exact hne.trans (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mod_lt _ hm).le 1)))
  refine ⟨_,?_,re,ht.seq (hv.seq (hd.seq he))⟩
  simp only [List.length_reverse]
  unfold budget
  omega

theorem reversedProgram_runs (regs : Fin 8 → Bool) (word rest width modulus : List Bool)
    (hw : width.length = word.length) (hm : 0 < SubexponentialSAT.BinaryArithmetic.toNat modulus) :
    ∃ rf, RunsIn reversedProgram
      (budget word.length modulus.length (SubexponentialSAT.BinaryArithmetic.toNat modulus)+
        9*word.length+8)
      ((data regs (word.reverse++rest) width modulus [] [] [] []).withPC
        (some reversedProgram.entry))
      ((data rf rest width modulus [] []
        (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
        (Encoding.encodeNat (SubexponentialSAT.BinaryArithmetic.toNat word %
          SubexponentialSAT.BinaryArithmetic.toNat modulus))).withPC none) := by
  obtain ⟨n,hn,rf,he⟩ := reversedCommand_eval regs word rest width modulus hw hm
  exact ⟨rf,n+1,by omega,compiled_halt_trace he 0 12⟩

end SubexponentialSAT.SqrtLog.HashInputProgram.LoopDecode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoopTerm
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Assembly of one raw tuple term. All source lookup, coefficient lifting,
and record framing are executed by fixed native programs. The only persistent
data are the unexpanded original source, word width, modulus, ring shape,
unread raw bytes, and the already emitted output. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

theorem embed_tapes {r s : ℕ} (register : Fin r → Fin 8) (stack : Fin s → Fin 24)
    (hs : Function.Injective stack) (frame : Data) (source : State r s)
    (target : Fin 24 → List Bool)
    (hp : ∀ i, target (stack i) = source.stacks i)
    (hf : ∀ i, (¬ ∃ j, stack j = i) → target i = frame.stacks i) :
    embedState register stack frame source =
      (⟨(embedState register stack frame source).regs,target⟩ : Data) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases hi : ∃ j, stack j = i
    · obtain ⟨j,rfl⟩ := hi
      exact (embedState_stack register stack frame source hs j).trans (hp j).symm
    · exact (embedState_stack_frame register stack frame source i hi).trans (hf i hi).symm

theorem decoderStacks_injective : Function.Injective decoderStacks := Fin.castAdd_injective _ _

theorem decode_eval (regs : Fin 8 → Bool)
    (word rest width modulus master shape acc : List Bool)
    (hw : width.length=word.length) (hm : 0 < SubexponentialSAT.BinaryArithmetic.toNat modulus) :
    ∃ n ≤ LoopDecode.budget word.length modulus.length (SubexponentialSAT.BinaryArithmetic.toNat modulus)+
        9*word.length+8, ∃ rf,
      Eval decode n (data regs (word.reverse++rest) width modulus master shape acc [] [] [] [])
        (data rf rest width modulus master shape acc
          (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
          (Encoding.encodeNat (SubexponentialSAT.BinaryArithmetic.toNat word %
            SubexponentialSAT.BinaryArithmetic.toNat modulus)) [] []) := by
  let d := data regs (word.reverse++rest) width modulus master shape acc [] [] [] []
  obtain ⟨rf,n,hn,ht⟩ := LoopDecode.reversedProgram_runs regs word rest width modulus hw hm
  have hi : projectState id decoderStacks d =
      LoopDecode.data regs (word.reverse++rest) width modulus [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [← hi] at ht
  have he := eval_call_from_state LoopDecode.reversedProgram id decoderStacks d
    Function.injective_id decoderStacks_injective ht
  have ho := embed_tapes id decoderStacks decoderStacks_injective d
    (LoopDecode.data rf rest width modulus [] []
      (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
      (Encoding.encodeNat (SubexponentialSAT.BinaryArithmetic.toNat word % SubexponentialSAT.BinaryArithmetic.toNat modulus)))
    (tapes rest width modulus master shape acc
      (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
      (Encoding.encodeNat (SubexponentialSAT.BinaryArithmetic.toNat word % SubexponentialSAT.BinaryArithmetic.toNat modulus)) [] [])
    (by intro i; fin_cases i <;> rfl)
    (by
      intro i h
      have h0 : i ≠ 0 := fun hh => h ⟨0,hh.symm⟩
      have h6 : i ≠ 6 := fun hh => h ⟨6,hh.symm⟩
      have h12 : i ≠ 12 := fun hh => h ⟨12,hh.symm⟩
      fin_cases i <;> simp_all [d,data,tapes])
  rw [ho] at he
  exact ⟨n,hn,_,he⟩

theorem copyShape_eval (regs : Fin 8 → Bool)
    (rest width modulus master shape acc quotient payload : List Bool) :
    Eval copyShape (7*shape.length+5)
      (data regs rest width modulus master shape acc quotient [] payload [])
      (data (readRegs regs 0 1 none) rest width modulus master shape acc quotient [] payload shape) := by
  have h := copy_eval (data regs rest width modulus master shape acc quotient [] payload [])
    15 19 20 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  convert h using 1
  · simp [data, tapes]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [data,tapes,StackRoutines.copyStacks]

theorem normalizationStacks_injective : Function.Injective normalizationStacks := by decide

theorem normalize_eval (t d : ℕ) (ht : 0 < t) (c : ZMod 3) (regs : Fin 8 → Bool)
    (rest width modulus master shape acc quotient payload : List Bool)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t)
    (hq : SubexponentialSAT.BinaryArithmetic.toNat quotient=c.val) :
    ∃ n ≤ 7*shape.length+2*quotient.length+9, ∃ rf,
      Eval normalize n
        (data regs rest width modulus master shape acc quotient [] payload shape)
        (data rf rest width modulus master shape acc
          (RingProgram.flat (constantVector t d c)) [] payload []) := by
  let a := data regs rest width modulus master shape acc quotient [] payload shape
  obtain ⟨rf,n,hn,hr⟩ := lift_runs t d ht c shape quotient [] hshape hq regs
  have hi : projectState id normalizationStacks a =
      (⟨regs,SubexponentialSAT.ModularRingPrograms.normalizationState quotient shape [] []⟩ : State 8 8) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  change Trace SubexponentialSAT.ModularRingPrograms.normalizeProgram n
    ((⟨regs,SubexponentialSAT.ModularRingPrograms.normalizationState quotient shape [] []⟩ : State 8 8).withPC
      (some SubexponentialSAT.ModularRingPrograms.normalizeProgram.entry))
    ((⟨rf,SubexponentialSAT.ModularRingPrograms.normalizationState
      (RingProgram.flat (constantVector t d c)) [] [] []⟩ : State 8 8).withPC none) at hr
  rw [← hi] at hr
  have he := eval_call_from_state SubexponentialSAT.ModularRingPrograms.normalizeProgram id normalizationStacks a
    Function.injective_id normalizationStacks_injective hr
  have ho := embed_tapes id normalizationStacks normalizationStacks_injective a
    (⟨rf,SubexponentialSAT.ModularRingPrograms.normalizationState
      (RingProgram.flat (constantVector t d c)) [] [] []⟩ : State 8 8)
    (tapes rest width modulus master shape acc (RingProgram.flat (constantVector t d c)) [] payload [])
    (by intro i; fin_cases i <;> rfl)
    (by
      intro i h
      have h6 : i ≠ 6 := fun hh => h ⟨0,hh.symm⟩
      have h19 : i ≠ 19 := fun hh => h ⟨7,hh.symm⟩
      fin_cases i <;> simp_all [a,data,tapes])
  rw [ho] at he
  exact ⟨n,hn,_,he⟩

theorem tagRecord_eval (regs : Fin 8 → Bool)
    (rest width modulus master shape acc : List Bool) :
    Eval tagRecord 2 (data regs rest width modulus master shape acc [] [] [] [])
      (data (Function.update regs 0 true) rest width modulus master shape (true::acc) [] [] [] []) := by
  let a := data regs rest width modulus master shape acc [] [] [] []
  let b := (StructuredProgram.Atom.set (0 : Fin 8) true).eval a
  have h1 : Eval (.base (.atom (.set 0 true))) 1 a b := .base (.atom _ _)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (16 : Fin 24) 0) b)
  have he := h1.seq h2
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [a,b,data,tapes,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed raw-tuple assembler. The machine traverses raw digit bytes, not a
pre-expanded clause table. Each step looks up one ORIGINAL source clause and
emits its lifted coefficient plus unchanged canonical literal bytes. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem flat_length (t d : ℕ) (c : ZMod 3) :
    (RingProgram.flat (constantVector t d c)).length =
      (d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t := by
  exact RingProgram.flat_length (constantVector t d c)

theorem term_eval (t d : ℕ) (ht : 0 < t) (clauses : List (List Bool))
    (a : Fin clauses.length × ZMod 3) (regs : Fin 8 → Bool)
    (word rest width modulus shape acc : List Bool)
    (hw : width.length=word.length)
    (hm : SubexponentialSAT.BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t)
    (hword : SubexponentialSAT.BinaryArithmetic.toNat word=a.1.val+clauses.length*a.2.val) :
    ∃ n ≤ termBudget word.length modulus.length clauses.length
        (Encoding.encodeList id clauses).length shape.length clauses[a.1.val].length,
      ∃ rf, Eval term n
        (data regs (word.reverse++rest) width modulus (Encoding.encodeList id clauses) shape acc [] [] [] [])
        (data rf rest width modulus (Encoding.encodeList id clauses) shape
          (true::(Encoding.frame (payload t d clauses a)++acc)) [] [] [] []) := by
  have hmpos : 0 < clauses.length := lt_of_le_of_lt (Nat.zero_le _) a.1.isLt
  have hrem : SubexponentialSAT.BinaryArithmetic.toNat word % SubexponentialSAT.BinaryArithmetic.toNat modulus=a.1.val := by
    rw [hm,hword,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt a.1.isLt]
  have hquot : SubexponentialSAT.BinaryArithmetic.toNat
      (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1=a.2.val := by
    rw [SubexponentialSAT.ModularQuotientArithmetic.divide_quotient_correct modulus word (by omega),hm,hword,
      Nat.add_mul_div_left _ _ hmpos,Nat.div_eq_of_lt a.1.isLt,Nat.zero_add]
  obtain ⟨n0,hn0,r0,h0⟩ := decode_eval regs word rest width modulus
    (Encoding.encodeList id clauses) shape acc hw (by omega)
  rw [hrem] at h0
  rw [hm] at hn0
  obtain ⟨n1,hn1,r1,h1⟩ := lookup_eval r0 clauses a.1 rest width modulus shape acc
    (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
  have h2 := copyShape_eval r1 rest width modulus (Encoding.encodeList id clauses) shape acc
    (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1 clauses[a.1.val]
  obtain ⟨n3,hn3,r3,h3⟩ := normalize_eval t d ht a.2 (readRegs r1 0 1 none)
    rest width modulus (Encoding.encodeList id clauses) shape acc
    (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1 clauses[a.1.val] hshape hquot
  obtain ⟨n4,hn4,r4,h4⟩ := frameWeight_eval r3 rest width modulus
    (Encoding.encodeList id clauses) shape acc (RingProgram.flat (constantVector t d a.2)) clauses[a.1.val]
  obtain ⟨n5,hn5,r5,h5⟩ := frameRecord_eval r4 rest width modulus
    (Encoding.encodeList id clauses) shape acc (payload t d clauses a)
  have h6 := tagRecord_eval r5 rest width modulus (Encoding.encodeList id clauses) shape
    (Encoding.frame (payload t d clauses a)++acc)
  have he := h0.seq (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6)))))
  refine ⟨_,?_,_,he⟩
  have hlen := flat_length t d a.2
  rw [← hshape] at hlen
  rw [hlen] at hn4
  have hp : (payload t d clauses a).length=2*shape.length+1+clauses[a.1.val].length := by
    simp only [payload,List.length_append,Encoding.length_frame,hlen]
  rw [hp] at hn5
  rw [SubexponentialSAT.ModularQuotientArithmetic.divide_quotient_length] at hn3
  unfold termBudget
  omega

theorem peek_nil (regs : Fin 8 → Bool) (width modulus master shape acc : List Bool) :
    Eval peek 2 (data regs [] width modulus master shape acc [] [] [] [])
      (data (peekRegs regs []) [] width modulus master shape acc [] [] [] []) := by
  let a := data regs [] width modulus master shape acc [] [] [] []
  have hp := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (0 : Fin 24) 0 1) a)
  have he : (StructuredProgram.Atom.pop (0 : Fin 24) (0 : Fin 8) 1).eval a =
      data (peekRegs regs []) [] width modulus master shape acc [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [a,data,tapes,
        StructuredProgram.Atom.instr,execInstr]
  rw [he] at hp
  exact hp.seq (Eval.ite_false rfl (.base (.skip _)))

theorem peek_cons (regs : Fin 8 → Bool) (bit : Bool)
    (raw width modulus master shape acc : List Bool) :
    Eval peek 3 (data regs (bit::raw) width modulus master shape acc [] [] [] [])
      (data (peekRegs regs (bit::raw)) (bit::raw) width modulus master shape acc [] [] [] []) := by
  let a := data regs (bit::raw) width modulus master shape acc [] [] [] []
  let b := (StructuredProgram.Atom.pop (0 : Fin 24) (0 : Fin 8) 1).eval a
  have hp : Eval (.base (.atom (.pop 0 0 1))) 1 a b := .base (.atom _ _)
  have hpush := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (0 : Fin 24) 0) b)
  have he : (StructuredProgram.Atom.push (0 : Fin 24) (0 : Fin 8)).eval b =
      data (peekRegs regs (bit::raw)) (bit::raw) width modulus master shape acc [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [a,b,data,tapes,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr,readRegs]
  rw [he] at hpush
  exact hp.seq (Eval.ite_true rfl hpush)

theorem loop_eval_oai (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (regs : Fin 8 → Bool)
    (width modulus shape acc : List Bool)
    (hw : width.length=b) (hm : SubexponentialSAT.BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ loopBudget t d b modulus.length clauses terms, ∃ rf,
      Eval loop n
        (data regs (scanInput b terms) width modulus (Encoding.encodeList id clauses) shape acc [] [] [] [])
        (data rf [] width modulus (Encoding.encodeList id clauses) shape
          (records (terms.reverse.map (payload t d clauses)) acc) [] [] [] []) := by
  induction terms generalizing regs acc with
  | nil =>
      refine ⟨3,by simp [loopBudget],peekRegs regs [],?_⟩
      exact (peek_nil regs width modulus (Encoding.encodeList id clauses) shape acc).seq
        (Eval.while_false rfl)
  | cons a terms ih =>
      have hwlen : (word b clauses.length a).length=b := by simp [word]
      have hv : SubexponentialSAT.BinaryArithmetic.toNat (word b clauses.length a)=
          a.1.val+clauses.length*a.2.val := by
        apply SubexponentialSAT.SubexpLiftRing.toNat_fixedBits_of_lt
        have hc := a.2.val_lt
        have hi := a.1.isLt
        have : a.1.val+clauses.length*a.2.val < 3*clauses.length := by nlinarith
        exact this.trans_le hbound
      have hnonnil : (word b clauses.length a).reverse++scanInput b terms ≠ [] := by
        intro he
        have he' := congrArg List.length he
        simp [hwlen] at he'
        omega
      obtain ⟨bit,raw,hraw⟩ := List.exists_cons_of_ne_nil hnonnil
      have hp := peek_cons regs bit raw width modulus (Encoding.encodeList id clauses) shape acc
      rw [← hraw] at hp
      obtain ⟨nu,hnu,ru,hu⟩ := term_eval t d ht clauses a
        (peekRegs regs ((word b clauses.length a).reverse++scanInput b terms))
        (word b clauses.length a) (scanInput b terms) width modulus shape acc
        (hw.trans hwlen.symm) hm hshape hv
      obtain ⟨nv,hnv,rv,hv⟩ := ih ru (true::(Encoding.frame (payload t d clauses a)++acc))
      cases hv with
      | @seq first second nx ny aa bb cc hpeek hwhile =>
          have hg : (data (peekRegs regs ((word b clauses.length a).reverse++scanInput b terms))
              ((word b clauses.length a).reverse++scanInput b terms) width modulus
              (Encoding.encodeList id clauses) shape acc [] [] [] []).regs 1=true := by
            rw [hraw]
            rfl
          have he := hp.seq (Eval.while_true hg (hu.seq hpeek) hwhile)
          refine ⟨3+(nu+nx+ny+1),?_,rv,?_⟩
          · rw [hwlen,hshape] at hnu
            simp only [loopBudget,List.map_cons,List.sum_cons] at *
            omega
          · simpa [scanInput,List.reverse_cons,List.map_append,records_append,records] using he

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.loop_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.loop_eval_oai
