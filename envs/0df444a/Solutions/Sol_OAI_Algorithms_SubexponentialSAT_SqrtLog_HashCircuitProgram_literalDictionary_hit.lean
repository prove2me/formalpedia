-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalDictionary_hit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:21:45.085415+00:00
-- url     : https://prove2.me/submissions/8a4a656b-f7bf-4c8d-b040-1c1c519d783d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S063
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S089

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramLookupBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The lookup suffix is bounded by the original table. This explicit bound
pays for reclaiming the unused suffix in dictionary updates. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan
open SubexponentialSAT.Subexp.SelectorProgram

private theorem lookup_cons_eq (query value : List Bool) (rest : List (List Bool × List Bool)) :
    ((query, value) :: rest).lookup query = some value := by simp

private theorem lookup_cons_ne (query key value : List Bool)
    (rest : List (List Bool × List Bool)) (h : key ≠ query) :
    ((key, value) :: rest).lookup query = rest.lookup query := by
  simp [List.lookup_cons, beq_false_of_ne (Ne.symm h)]

private theorem ready_nil_guard (regs : Fin 5 → Bool) (query : List Bool) :
    (ready regs [] query).regs 1 = false := by simp [ready, rawRecords, recordState, readRegs]

private theorem ready_cons_guard (regs : Fin 5 → Bool) (key value query : List Bool)
    (records : List (List Bool × List Bool)) :
    (ready regs ((key, value) :: records) query).regs 1 = true := by
  cases key <;> simp [ready, rawRecords, Encoding.frame, recordState, readRegs]

/-- An actual first-match scan of the encoded table. All scratch strings are
cleared by the existing record routine before the next iteration. -/
theorem scan_eval_tail (query : List Bool) (records : List (List Bool × List Bool))
    (regs : Fin 5 → Bool) (hflag : regs 4 = false) :
    ∃ n ≤ scanBudget query records, ∃ regs' tail,
      Eval scan n (ready regs records query)
        (recordState regs' tail [] query.reverse [] [] (framedResult (records.lookup query))) ∧
      regs' 4 = (records.lookup query).isSome ∧
      tail.length ≤ (rawRecords records).length := by
  induction records generalizing regs with
  | nil =>
      refine ⟨1, le_rfl, readRegs regs 0 1 none, [], ?_, ?_, by simp [rawRecords]⟩
      · simpa [scan, ready, rawRecords, framedResult] using
          (Eval.while_false (test := (1 : Fin 5)) (body := body)
            (a := ready regs [] query) (ready_nil_guard regs query))
      · first | (simpa [readRegs, -OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.status_read] using hflag) | (simpa [readRegs] using hflag)
  | cons p records ih =>
      rcases p with ⟨key, value⟩
      let rr := readRegs regs 0 1 (rawRecords ((key, value) :: records)).head?
      obtain ⟨n, hn, middle, hrecord, hanswer⟩ :=
        oneRecord_eval rr key query value (rawRecords records) []
      have hstart : recordState rr
          (Encoding.frame key ++ (Encoding.frame value ++ rawRecords records))
          [] query.reverse [] [] [] = ready regs ((key, value) :: records) query := by
        simp [ready, rr, rawRecords, List.append_assoc]
      rw [hstart] at hrecord
      by_cases hkey : key = query
      · subst key
        have hm : middle 4 = true := by simpa using hanswer
        have hrec : Eval oneRecord n (ready regs ((query, value) :: records) query)
            (recordState middle (rawRecords records) [] query.reverse [] [] (Encoding.frame value)) := by
          simpa using hrecord
        have hcontrol : Eval continueOrStop 2
            (recordState middle (rawRecords records) [] query.reverse [] [] (Encoding.frame value))
            (recordState (Function.update middle 1 false) (rawRecords records)
              [] query.reverse [] [] (Encoding.frame value)) := by
          exact Eval.ite_true hm (stop_eval middle _ _ _)
        have hend : Eval scan 1
            (recordState (Function.update middle 1 false) (rawRecords records)
              [] query.reverse [] [] (Encoding.frame value))
            (recordState (Function.update middle 1 false) (rawRecords records)
              [] query.reverse [] [] (Encoding.frame value)) := by
          apply Eval.while_false
          simp []
        have hrun := Eval.while_true (ready_cons_guard regs query value query records)
          (Eval.seq hrec hcontrol) hend
        refine ⟨(n + 2) + 1 + 1, ?_, Function.update middle 1 false, rawRecords records, ?_, ?_, ?_⟩
        · simp only [scanBudget]
          omega
        · simpa only [scan, body, lookup_cons_eq, framedResult, Option.map_some, Option.getD_some]
            using hrun
        · simpa [lookup_cons_eq] using hm
        · simp [rawRecords, List.length_flatMap]
          omega
      · have hm : middle 4 = false := by simpa [hkey] using hanswer
        have hrec : Eval oneRecord n (ready regs ((key, value) :: records) query)
            (recordState middle (rawRecords records) [] query.reverse [] [] []) := by
          simpa [hkey] using hrecord
        have hcontrol : Eval continueOrStop 2
            (recordState middle (rawRecords records) [] query.reverse [] [] [])
            (ready middle records query) := by
          exact Eval.ite_false hm (peek_eval middle _ _ _)
        obtain ⟨m, hmBound, final, tail, hrest, hfinal, htail⟩ := ih middle hm
        have hrun := Eval.while_true (ready_cons_guard regs key value query records)
          (Eval.seq hrec hcontrol) hrest
        refine ⟨(n + 2) + m + 1, ?_, final, tail, ?_, ?_, ?_⟩
        · simp only [scanBudget]
          omega
        · simpa only [scan, body, lookup_cons_ne query key value records hkey] using hrun
        · simpa only [lookup_cons_ne query key value records hkey] using hfinal
        · have hle : (rawRecords records).length ≤ (rawRecords ((key, value) :: records)).length := by
            simp only [rawRecords,List.flatMap_cons,List.length_append]
            omega
          exact htail.trans hle


theorem dictionaryLookup_eval_tail (query : List Bool)
    (entries : List (List Bool × List Bool)) (regs : Fin 5 → Bool) :
    ∃ n ≤ lookupBudget query entries + 2, ∃ regs' tail,
      Eval dictionaryLookup n
        (recordState regs (lookupRecords entries) [] query.reverse [] [] [])
        (recordState regs' tail [] query.reverse [] [] (lookupResult (entries.lookup query))) ∧
      regs' 4 = (entries.lookup query).isSome ∧
      tail.length ≤ (lookupRecords entries).length := by
  let initRegs := Function.update regs (4 : Fin 5) false
  have hs : Eval (.base (.atom (.set 4 false))) 1
      (recordState regs (lookupRecords entries) [] query.reverse [] [] [])
      (recordState initRegs (lookupRecords entries) [] query.reverse [] [] []) :=
    .base (.atom _ _)
  have hp := peek_eval initRegs (lookupRecords entries) query.reverse []
  obtain ⟨n, hn, final, tail, he, hf, ht⟩ :=
    scan_eval_tail query entries initRegs (by simp [initRegs])
  exact ⟨1 + (1 + n), by dsimp [lookupBudget] at *; omega,
    final, tail, hs.seq (hp.seq he), hf, ht⟩

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Native literal parsing and hash-specific incidence lookup

A literal payload is `key ++ [positive]`; the existing record parser supplies
its reversal. The key selects a variable in a physically selected hash slice.
The fixed command pops the polarity, copies and scans the saved incidence
slice, returns its framed dictionary payload, and reclaims both scan and query.
There is no circuit-evaluation instruction and no scope truth table.
-/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

theorem embed_extend (a b : State 5 6) (positive : Bool) (table : List Bool) :
    embedState Fin.castSucc Fin.castSucc (extend a positive table) b =
      extend b positive table := by
  apply embedState_eq_of_ports _ _ _ _ _ (Fin.castSucc_injective 5) (Fin.castSucc_injective 6)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> simp_all [ Fin.exists_fin_succ]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> simp_all [ Fin.exists_fin_succ]

theorem lookupCall_eval (query : List Bool)
    (entries : List (List Bool × List Bool)) (regs : Fin 5 → Bool)
    (positive : Bool) (table : List Bool) :
    ∃ n ≤ Squarefree.Program.lookupBudget query entries + 3, ∃ regs' tail,
      Eval lookupCall n
        (data regs positive (Squarefree.Program.lookupRecords entries) query.reverse [] table)
        (data regs' positive tail query.reverse
          (Squarefree.Program.lookupResult (entries.lookup query)) table) ∧
      regs' 4 = (entries.lookup query).isSome ∧
      tail.length ≤ (Squarefree.Program.lookupRecords entries).length := by
  obtain ⟨n,hn,rr,tail,he,hflag,htail⟩ :=
    Squarefree.Program.dictionaryLookup_eval_tail query entries regs
  have hh := eval_liftCommand he 0 5 Fin.castSucc Fin.castSucc
    (data regs positive (Squarefree.Program.lookupRecords entries) query.reverse [] table)
    (Fin.castSucc_injective 5) (Fin.castSucc_injective 6)
  simp only [data, embed_extend] at hh
  exact ⟨n+1,by omega,rr,tail,hh,hflag,htail⟩

theorem copy_eval (d : Data) (src dst tmp : Fin 7)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (htmp : d.stacks tmp = []) :
    Eval (copy src dst tmp) (7 * (d.stacks src).length + 5) d (copied d src dst) := by
  apply Eval.call
  have h := StackRoutines.copyProgram_trace src dst tmp (0 : Fin 6) 1
    hsd hst htd (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  simpa [copied,StackRoutines.copyResult,StructuredProgram.State.withPC,
    StackRoutines.copyProgram,Nat.add_assoc] using hh

theorem clear_eval (d : Data) (src : Fin 7) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared d src) := by
  apply Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 6) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [cleared,StackRoutines.clearResult,StructuredProgram.State.withPC,
    StackRoutines.clearProgram,Nat.add_assoc] using hh

theorem popLiteral_eval (regs : Fin 5 → Bool) (old positive : Bool)
    (key table : List Bool) :
    Eval popLiteral 1 (data regs old [] (positive :: key.reverse) [] table)
      (data (Function.update regs 1 true) positive [] key.reverse [] table) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 7) (5 : Fin 6) 1)
    (data regs old [] (positive :: key.reverse) [] table))) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;>
      simp [StructuredProgram.Atom.instr,execInstr,readRegs]
  · funext i; fin_cases i <;>
      simp [StructuredProgram.Atom.instr,execInstr]

private theorem copied_data (regs : Fin 5 → Bool) (positive : Bool)
    (query output table : List Bool) :
    copied (data regs positive [] query output table) 6 0 =
      data (readRegs regs 0 1 none) positive table query output table := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [readRegs]
  · funext i; fin_cases i <;> simp [StackRoutines.copyStacks]

private theorem cleared_scan (regs : Fin 5 → Bool) (positive : Bool)
    (scan query output table : List Bool) :
    cleared (data regs positive scan query output table) 0 =
      data (readRegs regs 0 1 none) positive [] query output table := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [readRegs]
  · funext i; fin_cases i <;> simp [StackRoutines.clearStacks]

private theorem cleared_query (regs : Fin 5 → Bool) (positive : Bool)
    (query output table : List Bool) :
    cleared (data regs positive [] query output table) 2 =
      data (readRegs regs 0 1 none) positive [] [] output table := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [readRegs]
  · funext i; fin_cases i <;> simp [StackRoutines.clearStacks]

theorem literalFetch_eval (regs : Fin 5 → Bool) (old positive : Bool)
    (key : List Bool) (entries : List (List Bool × List Bool)) :
    ∃ n ≤ literalFetchBudget key entries, ∃ regs',
      Eval literalFetch n
        (data regs old [] (key ++ [positive]).reverse []
          (Squarefree.Program.lookupRecords entries))
        (data regs' positive [] [] (Squarefree.Program.lookupResult (entries.lookup key))
          (Squarefree.Program.lookupRecords entries)) ∧
      regs' 4 = (entries.lookup key).isSome := by
  let table := Squarefree.Program.lookupRecords entries
  let r1 := Function.update regs (1 : Fin 5) true
  let r2 := readRegs r1 0 1 none
  have hp := popLiteral_eval regs old positive key table
  have hc := copy_eval (data r1 positive [] key.reverse [] table) 6 0 1
    (by decide) (by decide) (by decide) rfl
  simp only [copied_data] at hc
  obtain ⟨n,hn,rr,tail,hl,hflag,htail⟩ := lookupCall_eval key entries r2 positive table
  have hcs := clear_eval (data rr positive tail key.reverse
    (Squarefree.Program.lookupResult (entries.lookup key)) table) 0
  simp only [cleared_scan] at hcs
  have hcq := clear_eval (data (readRegs rr 0 1 none) positive [] key.reverse
    (Squarefree.Program.lookupResult (entries.lookup key)) table) 2
  simp only [cleared_query] at hcq
  refine ⟨1 + ((7*table.length+5) + (n + ((2*tail.length+3) + (2*key.reverse.length+3)))),
    ?_,readRegs (readRegs rr 0 1 none) 0 1 none,?_,?_⟩
  · dsimp [literalFetchBudget,table] at *
    simp only [List.length_reverse] at *
    omega
  · have hrun := hp.seq (hc.seq (hl.seq (hcs.seq hcq)))
    first | (simp [data, extend, storage, -OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.status_read] at hrun) | (simp [data, extend, storage] at hrun)
    first | (simpa [literalFetch, table, data, extend, recordState, storage, readRegs, -OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.status_read] using hrun) | (simpa [literalFetch, table, data, extend, recordState, storage, readRegs] using hrun)
  · first | (simpa [readRegs, -OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.status_read] using hflag) | (simpa [readRegs] using hflag)

end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramPayload
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native unframing of the selected incidence dictionary. A successful literal
lookup returns the actual forward dictionary bits on stack5. The success guard
handles a missing key without invoking a parser on an absent frame. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

theorem transfer_eval (d : Data) (src dst : Fin 7) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3*(d.stacks src).length+3) d (transferred d src dst) := by
  apply Eval.call
  have h := StackRoutines.transferProgram_trace src dst (0 : Fin 6) 1 hsd (by decide)
    d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  simpa [transferred,StackRoutines.transferResult,StructuredProgram.State.withPC,
    StackRoutines.transferProgram,Nat.add_assoc] using hh

private theorem parse_after (regs : Fin 5 → Bool) (payload : List Bool) :
    afterFrame (recordState regs [] [] [] [] [] (Encoding.frame payload)) 5 0 payload [] =
      recordState (readRegs regs 0 1 (some false)) payload.reverse [] [] [] [] [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp []

private theorem transferred_payload (regs : Fin 5 → Bool) (positive : Bool)
    (payload table : List Bool) :
    transferred (extend (recordState regs payload.reverse [] [] [] [] []) positive table) 0 5 =
      data (readRegs regs 0 1 none) positive [] [] payload table := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [readRegs]
  · funext i; fin_cases i <;>
      simp [StackRoutines.transferStacks]

theorem unframeResult_hit (regs : Fin 5 → Bool) (positive : Bool)
    (payload table : List Bool) (hflag : regs 4 = true) :
    ∃ regs', Eval unframeResult (9*payload.length+9)
      (data regs positive [] [] (Encoding.frame payload) table)
      (data regs' positive [] [] payload table) ∧ regs' 4 = true := by
  have hparse := parseFrame_eval (recordState regs [] [] [] [] [] (Encoding.frame payload))
    5 0 (by decide) payload [] (by simp [])
  rw [parse_after] at hparse
  have hp := eval_liftCommand hparse 5 0 Fin.castSucc Fin.castSucc
    (data regs positive [] [] (Encoding.frame payload) table)
    (Fin.castSucc_injective 5) (Fin.castSucc_injective 6)
  simp only [data,embed_extend] at hp
  let rr := readRegs regs 0 1 (some false)
  have ht := transfer_eval
    (extend (recordState rr payload.reverse [] [] [] [] []) positive table) 0 5 (by decide)
  rw [transferred_payload] at ht
  refine ⟨readRegs rr 0 1 none,?_,?_⟩
  · have he := Eval.ite_true (yes := .seq parsePayload (transfer 0 5))
      (no := (.base .skip : Cmd 6 7)) (show (data regs positive [] [] (Encoding.frame payload) table).regs 4 = true by
        simpa [data,extend,recordState] using hflag) (hp.seq ht)
    convert he using 1 ; simp [] ; omega
  · simpa [rr,readRegs] using hflag

theorem literalDictionary_hit_oai (regs : Fin 5 → Bool) (old positive : Bool)
    (key payload : List Bool) (entries : List (List Bool × List Bool))
    (hlookup : entries.lookup key = some payload) :
    ∃ n ≤ literalFetchBudget key entries + 9*payload.length+9, ∃ regs',
      Eval literalDictionary n
        (data regs old [] (key ++ [positive]).reverse []
          (Squarefree.Program.lookupRecords entries))
        (data regs' positive [] [] payload (Squarefree.Program.lookupRecords entries)) ∧
      regs' 4 = true := by
  obtain ⟨n,hn,rr,he,hf⟩ := literalFetch_eval regs old positive key entries
  rw [hlookup] at he hf
  have he' : Eval literalFetch n
      (data regs old [] (key ++ [positive]).reverse [] (Squarefree.Program.lookupRecords entries))
      (data rr positive [] [] (Encoding.frame payload) (Squarefree.Program.lookupRecords entries)) := by
    simpa [Squarefree.Program.lookupResult,SubexponentialSAT.Subexp.SelectorProgram.framedResult] using he
  have hf' : rr 4 = true := by simpa using hf
  obtain ⟨r2,hp,hf2⟩ := unframeResult_hit rr positive payload
    (Squarefree.Program.lookupRecords entries) hf'
  exact ⟨n+(9*payload.length+9),by omega,r2,he'.seq hp,hf2⟩

end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalDictionary_hit_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalDictionary_hit_oai
