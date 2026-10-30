-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.lookup_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:24:12.80069+00:00
-- url     : https://prove2.me/submissions/f0a9e67f-94c6-4acb-b29f-07b387f2de6b

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S084

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFRecords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control skipping of framed CNF records

The program below has three Boolean registers, one Boolean stack, and eleven
fixed labels. It consumes an escaped frame or one tagged list item without
materializing the payload. The payload may itself encode a list of literals,
a clause, or a more deeply nested record. Every bound is proved for actual
`BitProgram.step` traces, rather than assigned to a semantic list operation.
-/

namespace SubexponentialSAT.ExecCNFRecords

open SubexponentialSAT.BitProgram

theorem start_pop (b v p f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 0) v p f (b :: input)) =
      some (cfg (some 1) b true f input) := by
  simp [step, cfg, execInstr, readRegs]

theorem start_present (v f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 1) v true f input) =
      some (cfg (some 2) v true f input) := by
  simp [step, cfg, execInstr]

theorem start_true (f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 2) true true f input) =
      some (cfg (some 3) true true f input) := by
  simp [step, cfg, execInstr]

theorem mark_found (f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 3) true true f input) =
      some (cfg (some 4) true true true input) := by
  simp [step, cfg, execInstr]

theorem record_prefix (v p f : Bool) (input : List Bool) :
    Trace skipProgram 4 (cfg (some 0) v p f (true :: input))
      (cfg (some 4) true true true input) :=
  .cons (start_pop true v p f input)
    (.cons (start_present true f input)
      (.cons (start_true f input) (.cons (mark_found f input) (.refl _))))

/-- Public entry skips one tagged record, reporting that an item was present. -/
theorem record_trace (bits rest : List Bool) (v p f : Bool) :
    Trace skipProgram (5 * bits.length + 8)
      (cfg (some 0) v p f (true :: (Encoding.frame bits ++ rest)))
      (cfg none false true true rest) := by
  have h := (record_prefix v p f (Encoding.frame bits ++ rest)).trans
    (frame_trace bits rest true true true)
  have ht : 4 + (5 * bits.length + 4) = 5 * bits.length + 8 := by omega
  simpa only [ht] using h

end SubexponentialSAT.ExecCNFRecords

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical positional lookup in the ORIGINAL encoded clause list. The index
is a canonical natural field; all preceding records are scanned and discarded.
The master source is copied, preserved, and charged. No pre-expanded hash input
table is assumed. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Source
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

theorem skip_eval (v p f : Bool) (master bits rest index payload tmp out : List Bool) :
    Eval skip (5*bits.length+8)
      (data v p f master (true :: (Encoding.frame bits ++ rest)) index payload tmp out)
      (data false true true master rest index payload tmp out) := by
  have hs : Function.Injective (fun _ : Fin 1 => (1 : Fin 6)) := by
    intro i j _; exact Subsingleton.elim i j
  let d := data v p f master (true :: (Encoding.frame bits ++ rest)) index payload tmp out
  let a : State 3 1 := ⟨ExecCNFRecords.regs v p f,
    fun _ => true :: (Encoding.frame bits ++ rest)⟩
  let b : State 3 1 := ⟨ExecCNFRecords.regs false true true, fun _ => rest⟩
  have hi : embedState id (fun _ : Fin 1 => (1 : Fin 6)) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id hs
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i; rfl
    · intros; rfl
  have ho : embedState id (fun _ : Fin 1 => (1 : Fin 6)) d b =
      data false true true master rest index payload tmp out := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id hs
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i; rfl
    · intro i hi
      have hn : i ≠ 1 := fun h => hi ⟨0,h.symm⟩
      fin_cases i <;> simp_all [d,data]
  have h := eval_call_lifted ExecCNFRecords.skipProgram id (fun _ => (1 : Fin 6))
    d Function.injective_id hs (a := a) (b := b)
    (ExecCNFRecords.record_trace bits rest v p f)
  rw [hi,ho] at h
  exact h

theorem popIndex_eval (v p f b : Bool) (master scan index payload tmp out : List Bool) :
    Eval popIndex 1 (data v p f master scan (b::index) payload tmp out)
      (data b true f master scan index payload tmp out) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 6) (0 : Fin 3) 1)
    (data v p f master scan (b::index) payload tmp out))) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [data,ExecCNFRecords.regs,
      StructuredProgram.Atom.instr,
      execInstr,readRegs]
  · funext i; fin_cases i <;> simp [data,
      StructuredProgram.Atom.instr,
      execInstr]

theorem skipLoop_eval (xs : List (List Bool)) (master rest payload tmp out : List Bool)
    (f : Bool) :
    Eval skipLoop (skipCost xs+1)
      (data (!xs.isEmpty) true f master (recordPrefix xs ++ rest)
        ((Encoding.encodeNat xs.length).tail) payload tmp out)
      (data false true (if xs=[] then f else true) master rest [] payload tmp out) := by
  induction xs generalizing f with
  | nil => simpa [skipLoop,skipCost,recordPrefix,Encoding.encodeNat,data] using
      (Eval.while_false (test := (0 : Fin 3))
        (body := .seq skip popIndex) (a := data false true f master rest [] payload tmp out) rfl)
  | cons x xs ih =>
      have hskip := skip_eval true true f master x (recordPrefix xs ++ rest)
        (Encoding.encodeNat xs.length) payload tmp out
      have hp := popIndex_eval false true true (!xs.isEmpty) master (recordPrefix xs ++ rest)
        ((Encoding.encodeNat xs.length).tail) payload tmp out
      have hc : Encoding.encodeNat xs.length =
          (!xs.isEmpty) :: (Encoding.encodeNat xs.length).tail := by
        cases xs <;> simp [Encoding.encodeNat,List.replicate_succ]
      rw [← hc] at hp
      have hi := ih true
      have hh := Eval.while_true (test := (0 : Fin 3)) rfl (hskip.seq hp) hi
      convert hh using 1 <;>
        simp [skipCost,recordPrefix,Encoding.encodeNat,List.replicate_succ,
          List.append_assoc] ; omega

theorem skipPrefix_eval (xs : List (List Bool)) (v p f : Bool)
    (master rest payload tmp out : List Bool) :
    Eval skipPrefix (skipCost xs+2)
      (data v p f master (recordPrefix xs ++ rest) (Encoding.encodeNat xs.length) payload tmp out)
      (data false true (if xs=[] then f else true) master rest [] payload tmp out) := by
  have hp := popIndex_eval v p f (!xs.isEmpty) master (recordPrefix xs ++ rest)
    ((Encoding.encodeNat xs.length).tail) payload tmp out
  have hc : Encoding.encodeNat xs.length =
      (!xs.isEmpty) :: (Encoding.encodeNat xs.length).tail := by
    cases xs <;> simp [Encoding.encodeNat,List.replicate_succ]
  rw [← hc] at hp
  have hh := hp.seq (skipLoop_eval xs master rest payload tmp out f)
  simpa only [skipPrefix,show 1+(skipCost xs+1)=skipCost xs+2 by omega] using hh

theorem parser_state (v p f v' p' f' : Bool)
    (master scan index payload tmp out scan' payload' : List Bool) :
    RecordPrograms.state ports (data v p f master scan index payload tmp out)
      v' p' f' scan' payload' = data v' p' f' master scan' index payload' tmp out := by
  apply congrArg₂ StructuredProgram.State.mk
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))

theorem popTag_eval (v p f b : Bool) (master scan index payload tmp out : List Bool) :
    Eval popTag 1 (data v p f master (b::scan) index payload tmp out)
      (data b true f master scan index payload tmp out) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (1 : Fin 6) (0 : Fin 3) 1)
    (data v p f master (b::scan) index payload tmp out))) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [data,ExecCNFRecords.regs,
      StructuredProgram.Atom.instr,
      execInstr,readRegs]
  · funext i; fin_cases i <;> simp [data,
      StructuredProgram.Atom.instr,
      execInstr]

theorem readSelected_eval (v p f : Bool) (master bits rest out : List Bool) :
    Eval readSelected (6*bits.length+5)
      (data v p f master (true :: (Encoding.frame bits ++ rest)) [] [] [] out)
      (data false true f master rest [] bits.reverse [] out) := by
  have hp := popTag_eval v p f true master (Encoding.frame bits ++ rest) [] [] [] out
  have hr := RecordPrograms.reader_eval ports
    (data true true f master (Encoding.frame bits ++ rest) [] [] [] out)
    bits rest [] true true f
  simp only [parser_state,List.append_nil] at hr
  simpa only [readSelected,show 1+(6*bits.length+4)=6*bits.length+5 by omega] using hp.seq hr

end SubexponentialSAT.SqrtLog.HashInputProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete preserving, paid lookup of a source clause by its list position. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Source
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

theorem copySource_eval (v p f : Bool) (master index : List Bool) :
    Eval copySource (7*master.length+5)
      (data v p f master [] index [] [] [])
      (data false false f master master index [] [] []) := by
  have h := copy_eval (data v p f master [] index [] [] []) 0 1 4 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  convert h using 1
  · simp [data]
  · apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [data, ExecCNFRecords.regs, readRegs]
    · funext i; fin_cases i <;> simp [data, StackRoutines.copyStacks]

theorem clearScan_eval (v p f : Bool) (master rest payload : List Bool) :
    Eval clearScan (2*rest.length+3)
      (data v p f master rest [] payload [] [])
      (data false false f master [] [] payload [] []) := by
  have h := StackRoutines.clearProgram_trace (1 : Fin 6) (0 : Fin 3) 1
    (data v p f master rest [] payload [] []).regs
    (data v p f master rest [] payload [] []).stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  apply Eval.call
  convert hh using 1 <;>
    simp [StackRoutines.clearResult,
      StructuredProgram.State.withPC,data,
      StackRoutines.clearStacks,readRegs,Nat.add_assoc]
  all_goals first | done | (first | done | (funext i; fin_cases i <;> rfl))

theorem forward_eval (v p f : Bool) (master bits : List Bool) :
    Eval forward (3*bits.length+3)
      (data v p f master [] [] bits.reverse [] [])
      (data false false f master [] [] [] [] bits) := by
  have h := transfer_eval (data v p f master [] [] bits.reverse [] []) 3 5 0 1
    (by decide) (by decide)
  convert h using 1
  · simp [data]
  · apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [data,ExecCNFRecords.regs,readRegs]
    · funext i; fin_cases i <;> simp [data,StackRoutines.transferStacks]

theorem fetch_eval (before : List (List Bool)) (bits rest : List Bool) (v p f : Bool) :
    let master := recordPrefix before ++ true :: (Encoding.frame bits ++ rest)
    Eval fetch (7*master.length+skipCost before+9*bits.length+2*rest.length+18)
      (data v p f master [] (Encoding.encodeNat before.length) [] [] [])
      (data false false (if before=[] then f else true) master [] [] [] [] bits) := by
  dsimp only
  let master := recordPrefix before ++ true :: (Encoding.frame bits ++ rest)
  have hc := copySource_eval v p f master (Encoding.encodeNat before.length)
  have hs := skipPrefix_eval before false false f master
    (true :: (Encoding.frame bits ++ rest)) [] [] []
  have hr := readSelected_eval false true (if before=[] then f else true) master bits rest []
  have hz := clearScan_eval false true (if before=[] then f else true) master rest bits.reverse
  have ht := forward_eval false false (if before=[] then f else true) master bits
  have h := hc.seq (hs.seq (hr.seq (hz.seq ht)))
  convert h using 1 ; simp only [master] ; omega

theorem recordPrefix_append (before after : List (List Bool)) :
    Encoding.encodeList id (before ++ after) = recordPrefix before ++ Encoding.encodeList id after := by
  induction before with
  | nil => rfl
  | cons b bs ih => simp [Encoding.encodeList,recordPrefix,ih,List.append_assoc]

theorem skipCost_le (before : List (List Bool)) : skipCost before ≤ 5*(recordPrefix before).length := by
  induction before with
  | nil => simp [skipCost,recordPrefix]
  | cons b bs ih =>
      simp only [skipCost,List.map_cons,List.sum_cons,recordPrefix,List.foldr_cons,
        List.length_cons,List.length_append] at *
      have hl : (Encoding.frame b).length=2*b.length+1 := Encoding.length_frame b
      omega

theorem fetch_cost_le (before : List (List Bool)) (bits rest : List Bool) :
    let master := recordPrefix before ++ true :: (Encoding.frame bits ++ rest)
    7*master.length+skipCost before+9*bits.length+2*rest.length+18 ≤
      23*master.length+18 := by
  have hs := skipCost_le before
  have hl : (Encoding.frame bits).length=2*bits.length+1 := Encoding.length_frame bits
  simp only [List.length_append,List.length_cons]
  omega

/-- The source bytes are the original encoded list. The result is exactly the
indexed original payload, including order and repeated literals. -/
theorem fetch_original_runs (clauses : List (List Bool)) (i : Fin clauses.length)
    (v p f : Bool) :
    ∃ flag, RunsIn fetchProgram (23*(Encoding.encodeList id clauses).length+19)
      ((data v p f (Encoding.encodeList id clauses) []
        (Encoding.encodeNat i.val) [] [] []).withPC (some fetchProgram.entry))
      ((data false false flag (Encoding.encodeList id clauses) [] [] [] []
        clauses[i.val]).withPC none) := by
  let before := clauses.take i.val
  let rest := Encoding.encodeList id (clauses.drop (i.val+1))
  have hlen : before.length=i.val := by simp [before]
  have hsplit : Encoding.encodeList id clauses =
      recordPrefix before ++ true :: (Encoding.frame clauses[i.val] ++ rest) := by
    have h := List.take_append_drop i.val clauses
    rw [List.drop_eq_getElem_cons i.isLt] at h
    calc
      Encoding.encodeList id clauses = Encoding.encodeList id
          (clauses.take i.val ++ clauses[i.val] :: clauses.drop (i.val+1)) :=
        congrArg (Encoding.encodeList id) h.symm
      _ = _ := by rw [recordPrefix_append]; rfl
  have he := fetch_eval before clauses[i.val] rest v p f
  have hb := fetch_cost_le before clauses[i.val] rest
  dsimp only at he hb
  rw [← hsplit,hlen] at he
  rw [← hsplit] at hb
  refine ⟨if before=[] then f else true,?_,?_,?_⟩
  · exact 7*(Encoding.encodeList id clauses).length+skipCost before+
      9*clauses[i.val].length+2*rest.length+18+1
  · omega
  · exact compiled_halt_trace he 2 5

end SubexponentialSAT.SqrtLog.HashInputProgram.Source

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

theorem lowRegisters_injective : Function.Injective lowRegisters := Fin.castAdd_injective _ _
theorem lookupStacks_injective : Function.Injective lookupStacks := by decide

theorem lookup_eval_oai (regs : Fin 8 → Bool) (clauses : List (List Bool))
    (i : Fin clauses.length) (rest width modulus shape acc quotient : List Bool) :
    ∃ n ≤ 23*(Encoding.encodeList id clauses).length+19, ∃ rf,
      Eval lookup n
        (data regs rest width modulus (Encoding.encodeList id clauses) shape acc quotient
          (Encoding.encodeNat i.val) [] [])
        (data rf rest width modulus (Encoding.encodeList id clauses) shape acc quotient
          [] clauses[i.val] []) := by
  let d := data regs rest width modulus (Encoding.encodeList id clauses) shape acc quotient
    (Encoding.encodeNat i.val) [] []
  obtain ⟨flag,n,hn,ht⟩ := Source.fetch_original_runs clauses i (regs 0) (regs 1) (regs 2)
  have hi : projectState lowRegisters lookupStacks d =
      Source.data (regs 0) (regs 1) (regs 2) (Encoding.encodeList id clauses) []
        (Encoding.encodeNat i.val) [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
  rw [← hi] at ht
  have he := eval_call_from_state Source.fetchProgram lowRegisters lookupStacks d
    lowRegisters_injective lookupStacks_injective ht
  have ho := embed_tapes lowRegisters lookupStacks lookupStacks_injective d
    (Source.data false false flag (Encoding.encodeList id clauses) [] [] [] [] clauses[i.val])
    (tapes rest width modulus (Encoding.encodeList id clauses) shape acc quotient [] clauses[i.val] [])
    (by intro j; fin_cases j <;> rfl)
    (by
      intro j h
      have h12 : j ≠ 12 := fun hh => h ⟨2,hh.symm⟩
      have h18 : j ≠ 18 := fun hh => h ⟨5,hh.symm⟩
      fin_cases j <;> simp_all [d,data,tapes])
  rw [ho] at he
  exact ⟨n,hn,_,he⟩

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.lookup_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.lookup_eval_oai
