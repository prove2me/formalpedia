-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.program_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:47:38.59073+00:00
-- url     : https://prove2.me/submissions/bbad1c81-fc57-4fc6-ae83-efb060339b01

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099
import Definitions.Def_OAIQ081S102
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpScopeProducer_command_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramBytes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram

theorem encodeRecords_eq (xs : List (List Bool)) :
    Encoding.encodeList id xs = recordPrefix xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList, recordPrefix, ih, List.append_assoc]

theorem recordPrefix_append (xs ys : List (List Bool)) :
    recordPrefix (xs ++ ys) = recordPrefix xs ++ recordPrefix ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [recordPrefix, ih, List.append_assoc]

theorem prefix_encodeRecords (xs ys : List (List Bool)) :
    recordPrefix xs ++ Encoding.encodeList id ys = Encoding.encodeList id (xs ++ ys) := by
  simp [encodeRecords_eq, recordPrefix_append, List.append_assoc]

@[simp] theorem accumulate_payload (weight : List Bool) (records : List (List Bool)) (out : List Bool) :
    accumulate (Encoding.frame weight ++ Encoding.encodeList id records) out =
      recordPrefix records ++ out := by
  unfold accumulate
  rw [clauseBytes_payload, encodeRecords_eq]
  simp

end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramExtract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical extraction of the literal-record bytes from one weighted raw
clause. Coefficient bytes are discarded even when the coefficient is zero. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Extract
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem move12_eval (v p f : Bool) (s x w o t : List Bool) :
    Eval move12 (3*x.length+3) (data v p f s x [] w o t)
      (data false false f s [] x.reverse w o t) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.transfer_eval (1 : Fin 6) 2 (0 : Fin 3) 1
    (by decide) (by decide) (data v p f s x [] w o t)
  convert h using 1
  · simp [data]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> simp [data, ExecCNFRecords.regs, readRegs]
    · funext i; fin_cases i <;> simp [data, StackRoutines.transferStacks]

theorem move25_eval (v p f : Bool) (s x w o : List Bool) :
    Eval move25 (3*x.length+3) (data v p f s [] x w o [])
      (data false false f s [] [] w o x.reverse) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.transfer_eval (2 : Fin 6) 5 (0 : Fin 3) 1
    (by decide) (by decide) (data v p f s [] x w o [])
  convert h using 1
  · simp [data]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> simp [data, ExecCNFRecords.regs, readRegs]
    · funext i; fin_cases i <;> simp [data, StackRoutines.transferStacks]

theorem move54_eval (v p f : Bool) (s o t : List Bool) :
    Eval move54 (3*t.length+3) (data v p f s [] [] [] o t)
      (data false false f s [] [] [] (t.reverse++o) []) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.transfer_eval (5 : Fin 6) 4 (0 : Fin 3) 1
    (by decide) (by decide) (data v p f s [] [] [] o t)
  convert h using 1
  · simp [data]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> simp [data, ExecCNFRecords.regs, readRegs]
    · funext i; fin_cases i <;> simp [data, StackRoutines.transferStacks]

theorem clear3_eval (v p f : Bool) (s x w o t : List Bool) :
    Eval clear3 (2*w.length+3) (data v p f s [] x w o t)
      (data false false f s [] x [] o t) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.clear_eval (3 : Fin 6) (0 : Fin 3) 1
    (data v p f s [] x w o t)
  convert h using 1
  · simp [data]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> simp [data, ExecCNFRecords.regs, readRegs]
    · funext i; fin_cases i <;> simp [data, StackRoutines.clearStacks]

theorem pop5_eval (v p f : Bool) (s o t : List Bool) :
    Eval pop5 1 (data v p f s [] [] [] o (false::t))
      (data false true f s [] [] [] o t) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (5 : Fin 6) (0 : Fin 3) 1)
    (data v p f s [] [] [] o (false::t)))) using 1
  all_goals try with_reducible_and_instances rfl
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [data,ExecCNFRecords.regs,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
      execInstr,readRegs]
  · funext i; fin_cases i <;> simp [data,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
      execInstr]

theorem finish_eval (s o : List Bool) :
    Eval finish 1 (data false false false s [] [] [] o [])
      (data false true false s [] [] [] o []) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.set (s := 6) (1 : Fin 3) true)
    (data false false false s [] [] [] o []))) using 1
  all_goals try with_reducible_and_instances rfl
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [data,ExecCNFRecords.regs,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
      execInstr]
  · rfl

theorem reader_eval (s w clause out : List Bool) :
    Eval (RecordPrograms.reader weightPorts) (6*w.length+4)
      (data false false false s [] (Encoding.frame w ++ clause) [] out [])
      (data false true false s [] clause w.reverse out []) := by
  have h := RecordPrograms.reader_eval weightPorts
    (data false false false s [] [] [] out []) w clause [] false false false
  convert h using 1 <;>
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext <;>
    (funext i; fin_cases i <;> simp [RecordPrograms.state,weightPorts,data,ExecCNFRecords.regs])

theorem command_eval (w s out : List Bool) (records : List (List Bool)) :
    ∃ t ≤ 30*((Encoding.frame w ++ Encoding.encodeList id records).length+1),
      Eval command t
        (data false true false s (Encoding.frame w ++ Encoding.encodeList id records).reverse [] [] out [])
        (data false true false s [] [] [] (recordPrefix records ++ out) []) := by
  let clause := Encoding.encodeList id records
  let bits := Encoding.frame w ++ clause
  have h1 := move12_eval false true false s bits.reverse [] out []
  simp only [List.length_reverse,List.reverse_reverse] at h1
  have h2 := reader_eval s w clause out
  have h3 := clear3_eval false true false s clause w.reverse out []
  simp only [List.length_reverse] at h3
  have h4 := move25_eval false false false s clause [] out
  have hr : clause.reverse = false :: (recordPrefix records).reverse := by
    simp [clause,encodeRecords_eq]
  rw [hr] at h4
  have h5 := pop5_eval false false false s out (recordPrefix records).reverse
  have h6 := move54_eval false true false s out (recordPrefix records).reverse
  simp only [List.length_reverse,List.reverse_reverse] at h6
  have h7 := finish_eval s (recordPrefix records ++ out)
  refine ⟨_, ?_, h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))⟩
  have hc : (Encoding.encodeList id records).length = (recordPrefix records).length+1 := by
    simp [encodeRecords_eq]
  dsimp [bits,clause]
  simp only [List.length_append,Encoding.length_frame]
  omega

end SubexponentialSAT.SqrtLog.HashScopeProgram.Extract

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramRecords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured physical folds over sparse-hash records

This module specializes the audited framed-record iterator to an accumulator
fold which visits every record. The callback is an actual finite `Cmd`; its
local execution contract remains explicit. `foldProgram_run` concerns primitive
Boolean-register/stack transitions, not an operation counter or semantic oracle.
The same program shape handles clause-literal products, sparse weighted sums,
coefficient-array maps, and support-key dictionary scans.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

variable {r s : ℕ} {A : Type*}

theorem visits_fold (read : State r s → A) (step : List Bool → A → A)
    {records : List (List Bool)} {before after : State r s}
    (h : Visits (fun _ => false) (foldEffect read step) records before after) :
    read after = records.foldl (fun a bits => step bits a) (read before) := by
  induction h with
  | nil base => rfl
  | hit ht _ => cases ht
  | miss _ he _ ih =>
      simpa only [List.foldl_cons, foldEffect] using ih.trans (congrArg
        (fun a => List.foldl (fun a bits => step bits a) a _) he)

theorem foldCommand_run (ports : Ports r s) (callback : Cmd r s)
    (read : State r s → A) (step : List Bool → A → A)
    (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (validPayload : List Bool → Prop)
    (contract : FoldContract ports callback read step cost invariant validPayload)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (hrecords : ∀ bits ∈ records, validPayload bits) (hbase : invariant base)
    (v pr f : Bool) :
    ∃ n next, n ≤ 3 + budget cost records ∧ invariant next ∧
      read next = records.foldl (fun a bits => step bits a) (read base) ∧
      Eval (foldCommand ports callback) n
        (state ports base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state ports next false true false suffix []) := by
  obtain ⟨n, next, hn, hnext, hhistory, hrun⟩ :=
    iterate_run_with_on ports callback (fun _ => false) cost invariant
      (foldEffect read step) validPayload contract records suffix base hrecords hbase v pr f
  refine ⟨n, next, hn, hnext, visits_fold read step hhistory, ?_⟩
  simpa [foldCommand] using hrun

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramFlatten
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed framed-record fold physically concatenates original literal-code
records after removing each term's coefficient frame. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Flatten
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open Extract (Data data)

theorem parser_state (base : Data) (v p f : Bool) (source payload : List Bool) :
    RecordPrograms.state ports base v p f source payload =
      data v p f source payload (base.stacks 2) (base.stacks 3) (base.stacks 4) (base.stacks 5) := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [RecordPrograms.state,ports,data,ExecCNFRecords.regs]
  · funext i; fin_cases i <;> simp [RecordPrograms.state,ports,data]

theorem contract :
    LeafProgram.FoldContract ports Extract.command (fun a => a.stacks 4) accumulate
      (fun bits => 30*(bits.length+1)) Ready Valid := by
  intro bits tail base hvalid hb
  obtain ⟨w,records,rfl⟩ := hvalid
  obtain ⟨t,ht,he⟩ := Extract.command_eval w tail (base.stacks 4) records
  let b := data false true false tail [] [] [] (recordPrefix records ++ base.stacks 4) []
  refine ⟨t,b,ht,?_,?_,?_⟩
  · simp [Ready,b,data]
  · simp [LeafProgram.foldEffect,b,data]
  · simpa [parser_state,b,data,hb.1,hb.2.1,hb.2.2] using he

theorem command_eval (records : List (List Bool)) (out : List Bool)
    (hv : ∀ bits ∈ records, Valid bits) :
    ∃ t ≤ cost records - 1,
      Eval command t (data false false false (Encoding.encodeList id records) [] [] [] out [])
        (data false true false [] [] [] [] (records.foldl (fun o b => accumulate b o) out) []) := by
  let base := data false false false [] [] [] [] out []
  obtain ⟨t,b,ht,hb,hout,he⟩ := LeafProgram.foldCommand_run ports Extract.command
    (fun a => a.stacks 4) accumulate (fun bits => 30*(bits.length+1)) Ready Valid contract
    records [] base hv (by simp [Ready,base,data]) false false false
  refine ⟨t,by unfold cost; omega,?_⟩
  simpa [command,parser_state,base,data,hb.1,hb.2.1,hb.2.2,hout] using he

theorem program_runsIn (records : List (List Bool)) (out : List Bool)
    (hv : ∀ bits ∈ records, Valid bits) :
    RunsIn program (cost records)
      ((data false false false (Encoding.encodeList id records) [] [] [] out []).withPC (some program.entry))
      ((data false true false [] [] [] [] (records.foldl (fun o b => accumulate b o) out) []).withPC none) := by
  obtain ⟨t,ht,he⟩ := command_eval records out hv
  refine ⟨t+1,?_,compiled_halt_trace he 0 4⟩
  have hpos : 1 ≤ cost records := by unfold cost; omega
  omega

theorem fold_accumulate (terms : List (List Bool × List (List Bool))) (acc : List (List Bool)) :
    (terms.map termPayload).foldl (fun o b => accumulate b o) (Encoding.encodeList id acc) =
      Encoding.encodeList id (terms.reverse.flatMap Prod.snd ++ acc) := by
  induction terms generalizing acc with
  | nil => simp
  | cons term terms ih =>
      rcases term with ⟨w,records⟩
      simp only [List.map_cons,List.foldl_cons,termPayload,accumulate_payload,prefix_encodeRecords]
      rw [ih]
      simp [List.flatMap_append,List.append_assoc]

theorem term_runsIn (terms : List (List Bool × List (List Bool))) :
    RunsIn program (cost (terms.map termPayload))
      ((data false false false (Encoding.encodeList termPayload terms) [] [] [] [false] []).withPC (some program.entry))
      ((data false true false [] [] [] []
        (Encoding.encodeList id (terms.reverse.flatMap Prod.snd)) []).withPC none) := by
  have hm : Encoding.encodeList id (terms.map termPayload) = Encoding.encodeList termPayload terms := by
    induction terms with
    | nil => rfl
    | cons term terms ih => simp [Encoding.encodeList,ih]
  have hv : ∀ bits ∈ terms.map termPayload, Valid bits := by
    intro bits hb
    obtain ⟨term,ht,rfl⟩ := List.mem_map.mp hb
    exact ⟨term.1,term.2,rfl⟩
  have h := program_runsIn (terms.map termPayload) (Encoding.encodeList id ([] : List (List Bool))) hv
  rw [fold_accumulate] at h
  simpa [hm, Encoding.encodeList] using h

end SubexponentialSAT.SqrtLog.HashScopeProgram.Flatten

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramSingle
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed program turns a physically materialized weighted raw row into
its deduplicated original-variable scope. All constant initialization is paid. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Single
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpChunkRecordMap (Data data tapes regs)
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

theorem registers_injective : Function.Injective registers := by decide
theorem stackPorts_injective : Function.Injective stackPorts := by decide

private theorem embed_flatten (v p f v' p' f' : Bool) (ell src oldSrc out oldOut : List Bool) :
    embedState registers stackPorts (data v' p' f' ell oldSrc oldOut [])
      (Extract.data v p f src [] [] [] out []) = data v p f ell src out [] := by
  apply embedState_eq_of_ports _ _ _ _ _ registers_injective stackPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h8 : i ≠ 8 := fun h => hi ⟨0,h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨1,h.symm⟩
    have h10 : i ≠ 10 := fun h => hi ⟨2,h.symm⟩
    simp [data,regs,h8,h9,h10]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h19 : i ≠ 19 := fun h => hi ⟨0,h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨1,h.symm⟩
    have h20 : i ≠ 20 := fun h => hi ⟨4,h.symm⟩
    simp [data,tapes,h19,h9,h20]

theorem wordTerms_payload (terms : List Term) :
    (wordTerms terms).map Flatten.termPayload = terms.map payload := by
  simp only [wordTerms,List.map_map]
  apply List.map_congr_left
  intro term _
  dsimp [Flatten.termPayload,payload]
  congr 1
  induction term.2 with
  | nil => rfl
  | cons c cs ih => simp [Encoding.encodeList,ih]

theorem wordTerms_merged (terms : List Term) :
    (wordTerms terms).reverse.flatMap Prod.snd = (mergedCodes terms).map Encoding.encodeNat := by
  simp [wordTerms,mergedCodes,← List.map_reverse,List.flatMap_map,List.map_flatMap]

private theorem encode_map {α β : Type*} (enc : β → List Bool) (f : α → β) (xs : List α) :
    Encoding.encodeList enc (xs.map f) = Encoding.encodeList (fun a => enc (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [Encoding.encodeList,ih]

theorem flatten_eval (terms : List Term) (ell : List Bool) :
    ∃ t ≤ Flatten.cost (terms.map payload),
      Eval flatten t
        (data false false false ell (Encoding.encodeList payload terms) [false] [])
        (data false true false ell [] (Encoding.encodeList Encoding.encodeNat (mergedCodes terms)) []) := by
  have ht := Flatten.term_runsIn (wordTerms terms)
  have hp : Encoding.encodeList Flatten.termPayload (wordTerms terms) =
      Encoding.encodeList payload terms := by
    have h := congrArg (Encoding.encodeList id) (wordTerms_payload terms)
    simpa only [encode_map,id_eq] using h
  rw [wordTerms_payload,wordTerms_merged,hp] at ht
  simp only [encode_map] at ht
  let a := data false false false ell (Encoding.encodeList payload terms) [false] []
  let b := Extract.data false true false [] [] [] []
    (Encoding.encodeList Encoding.encodeNat (mergedCodes terms)) []
  have ha : restrictState registers stackPorts a =
      Extract.data false false false (Encoding.encodeList payload terms) [] [] [] [false] [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨t,hn,he⟩ := lifted_call Flatten.program registers stackPorts registers_injective stackPorts_injective
    a b (Flatten.cost (terms.map payload)) (by simpa [ha,b] using ht)
  exact ⟨t,hn,by simpa [a,b,embed_flatten] using he⟩

theorem restore_eval (ell out : List Bool) :
    Eval restore (6*out.length+6) (data false true false ell [] out [])
      (data false false false ell out [] []) := by
  let a := data false true false ell [] out []
  let b := SubexponentialSAT.SubexpScanPrimitives.afterTransfer a 20 21 8 9
  have h1 := SubexponentialSAT.SubexpScanPrimitives.transfer_eval a 20 21 8 9 (by decide) (by decide)
  have h2 := SubexponentialSAT.SubexpScanPrimitives.transfer_eval b 21 19 8 9 (by decide) (by decide)
  have hl : (b.stacks 21).length = out.length := by
    simp [b,a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,StackRoutines.transferStacks,data,tapes]
  have he : SubexponentialSAT.SubexpScanPrimitives.afterTransfer b 21 19 8 9 = data false false false ell out [] [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> simp [b,a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,data,regs,readRegs]
    · funext i; fin_cases i <;> simp [b,a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,StackRoutines.transferStacks,data,tapes]
  have hh := h1.seq h2
  rw [hl,he] at hh
  simpa [restore,a,data,tapes,show 3*out.length+3+(3*out.length+3)=6*out.length+6 by omega] using hh

theorem initialize_eval (source : List Bool) :
    Eval initializeCmd 4 (data false false false [] source [] [])
      (data false false false [true] source [false] []) := by
  have h := (SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (18 : Fin 22) (8 : Fin 11) true
    (data false false false [] source [] [])).seq
    (SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (20 : Fin 22) (8 : Fin 11) false
      (SubexponentialSAT.Subexp.TupleProgram.pushedState 18 8 true (data false false false [] source [] [])))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [data,regs]
  · funext i; fin_cases i <;> simp [data,tapes]

theorem program_runsIn_oai (terms : List Term) :
    ∃ rf, RunsIn program (cost terms)
      ((data false false false [] (Encoding.encodeList payload terms) [] []).withPC (some program.entry))
      ((⟨rf,tapes [true] (Encoding.encodeList Encoding.encodeNat (scope terms)) [] []⟩ : Data).withPC none) := by
  have hi := initialize_eval (Encoding.encodeList payload terms)
  obtain ⟨nf,hf,hef⟩ := flatten_eval terms [true]
  have hr := restore_eval [true] (Encoding.encodeList Encoding.encodeNat (mergedCodes terms))
  obtain ⟨ns,hs,rf,hes⟩ := SubexpScopeProducer.command_eval [true] (mergedCodes terms) (by decide)
  refine ⟨rf,4+(nf+(6*(Encoding.encodeList Encoding.encodeNat (mergedCodes terms)).length+6+ns))+1,?_,?_⟩
  · unfold cost; omega
  · exact compiled_halt_trace (hi.seq (hef.seq (hr.seq hes))) 19 19

end SubexponentialSAT.SqrtLog.HashScopeProgram.Single

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.program_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.program_runsIn_oai
