-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_hit_eval
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:58:20.345889+00:00
-- url     : https://prove2.me/submissions/90cf9a35-831a-49b8-8d9f-4b09ecad7a09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S063
import Definitions.Def_OAIQ081S110
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Dictionary_finish_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Dictionary_onHit_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical dictionary-insertion program. All dictionary/key/vector
lengths are input data. The complete semantic composition is proved separately;
this file defines the finite table and its paid stack primitives. -/
namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem copy_eval (d : Data) (src dst tmp : Fin 27)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (htmp : d.stacks tmp = []) :
    Eval (copy src dst tmp) (7 * (d.stacks src).length + 5) d (copied d src dst) := by
  apply Eval.call
  have h := copyProgram_trace src dst tmp (0 : Fin 8) 1 hsd hst htd (by decide)
    d.regs d.stacks htmp
  have hh := halt_after_trace _ h 7 rfl rfl
  simpa [copy, copied, copyResult, StructuredProgram.State.withPC, copyProgram,
    Nat.add_assoc] using hh

theorem smallRegs_injective : Function.Injective smallRegs := Fin.castAdd_injective _ _
theorem lookupStacks_injective : Function.Injective lookupStacks := by decide

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem overlay_same (regs : Fin 8 → Bool) : overlay regs (regs ∘ smallRegs) = regs := by
  funext i
  by_cases h : ∃ j, smallRegs j = i
  · obtain ⟨j,rfl⟩ := h
    exact smallRegs_injective.extend_apply _ _ _
  · exact Function.extend_apply' _ _ _ h

theorem embed_lookup (regs : Fin 8 → Bool) (a : Tape)
    (rr : Fin 5 → Bool) (remain found : List Bool) :
    embedState smallRegs lookupStacks (machine regs a)
      (SubexponentialSAT.SubexpRecordScan.recordState rr remain [] a.query [] [] found) =
    machine (overlay regs rr) { a with remain := remain, found := found } := by
  apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective lookupStacks_injective
  · intro i; exact smallRegs_injective.extend_apply _ _ _
  · intro i hi; exact Function.extend_apply' _ _ _ hi
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> simp_all [machine,tapes,lookupStacks,Fin.exists_fin_succ]

theorem lookup_eval (regs : Fin 8 → Bool) (a : Tape)
    (query : List Bool) (entries : List (List Bool × List Bool))
    (hq : a.query = query.reverse) (hr : a.remain = Squarefree.Program.lookupRecords entries)
    (hf : a.found = []) :
    ∃ n ≤ Squarefree.Program.lookupBudget query entries + 3, ∃ rr remain,
      Eval lookup n (machine regs a)
        (machine (overlay regs rr) { a with remain := remain, found := Squarefree.Program.lookupResult (entries.lookup query) }) ∧
      rr 4 = (entries.lookup query).isSome ∧
      remain.length ≤ (Squarefree.Program.lookupRecords entries).length := by
  obtain ⟨n,hn,rr,remain,he,hflag,hrest⟩ :=
    Squarefree.Program.dictionaryLookup_eval_tail query entries (regs ∘ smallRegs)
  have ht := compiled_halt_trace he 0 5
  have hh := eval_call_lifted Squarefree.Program.dictionaryLookupProgram smallRegs lookupStacks
    (machine regs a) smallRegs_injective lookupStacks_injective ht
  have ha : embedState smallRegs lookupStacks (machine regs a)
      (SubexponentialSAT.SubexpRecordScan.recordState (regs ∘ smallRegs)
        (Squarefree.Program.lookupRecords entries) [] query.reverse [] [] []) = machine regs a := by
    rw [←hq,embed_lookup,overlay_same]
    congr 1
    cases a
    simp_all
  rw [ha,←hq,embed_lookup] at hh
  exact ⟨n+1,by omega,rr,remain,hh,hflag,hrest⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryMoves
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem copy_machine (regs : Fin 8 → Bool) (a b : Tape) (src dst tmp : Fin 27)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (htmp : tapes a tmp = []) (hs : copyStacks src dst (tapes a) = tapes b) :
    Eval (copy src dst tmp) (7 * (tapes a src).length + 5) (machine regs a)
      (machine (readRegs regs 0 1 none) b) := by
  simpa only [copied,machine,hs] using copy_eval (machine regs a) src dst tmp hsd hst htd htmp

theorem copyDict_eval (regs : Fin 8 → Bool) (a : Tape) (he : a.remain = []) :
    Eval (copy 15 18 23) (7 * a.dict.length + 5) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with remain := a.dict }) := by
  apply copy_machine regs a _ 15 18 23 (by decide) (by decide) (by decide) rfl
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryReplace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem rawEntries_eq_lookupRecords (entries : List (List Bool × List Bool)) :
    Squarefree.Program.rawEntries entries = Squarefree.Program.lookupRecords entries := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    simp only [Squarefree.Program.rawEntries,List.flatMap_cons,Squarefree.Program.lookupRecords,
      SubexponentialSAT.Subexp.SelectorProgram.rawRecords] at *
    simpa only [List.append_assoc] using congrArg (fun t => Encoding.frame a.1 ++ Encoding.frame a.2 ++ t) ih

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryInsert
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem insert_hit_eval_oai (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (width count : List Bool)
    (entries : List (List Bool × List Bool)) (query : List Bool)
    (hhit : entries.lookup query = some (RingScan.rightBits pairs))
    (hc : count.length = pairs.length) (hw : width.length = baseWidth p t) :
    ∃ n ≤ insertBudget entries query (RingScan.sumBits p t M pairs) (hitBudget p t pairs), ∃ rr,
      Eval insert n (machine regs (inputTape M.bits width count entries query (RingScan.leftBits pairs)))
        (machine rr (outputTape M.bits width count
          (updatedBytes entries query (RingScan.sumBits p t M pairs)) (RingScan.leftBits pairs))) := by
  let a := inputTape M.bits width count entries query (RingScan.leftBits pairs)
  let a1 : Tape := { a with remain := a.dict }
  let r1 := readRegs regs 0 1 none
  have hp := copyDict_eval regs a rfl
  obtain ⟨n,hn,r2,tail,hl,hflag,htail⟩ := lookup_eval r1 a1 query entries rfl
    (rawEntries_eq_lookupRecords entries) rfl
  let r3 := overlay r1 r2
  let a2 : Tape := { a1 with remain := tail, found := Squarefree.Program.lookupResult (entries.lookup query) }
  obtain ⟨k,hk,r4,hh⟩ := onHit_eval p t M pairs r3 a2 rfl rfl
    (by simp [a2,hhit,Squarefree.Program.lookupResult,SubexponentialSAT.Subexp.SelectorProgram.framedResult])
    rfl rfl rfl rfl hc hw
  have hb : (machine r3 a2).regs 4 = true := by
    change overlay r1 r2 (smallRegs 4) = true
    rw [show overlay r1 r2 (smallRegs 4) = r2 4 from smallRegs_injective.extend_apply _ _ _]
    simpa only [hhit,Option.isSome_some] using hflag
  have hbranch := Eval.ite_true (no := onMiss) hb hh
  let a3 : Tape := { a2 with found := [], left := [], right := [], steps := [], out := RingScan.sumBits p t M pairs }
  obtain ⟨m,hmBound,rr,hf⟩ := finish_eval r4 a3 entries query (RingScan.sumBits p t M pairs) rfl rfl rfl rfl rfl
  have run := hp.seq (hl.seq (hbranch.seq hf))
  refine ⟨_, ?_, rr, (by simpa [insert,finish,a,a1,a2,a3,r1,r3,inputTape,outputTape] using run)⟩
  have htail' : tail.length ≤ (Squarefree.Program.rawEntries entries).length := by
    simpa only [rawEntries_eq_lookupRecords] using htail
  dsimp [a,a1,a2,a3,inputTape,insertBudget,finishBudget] at hn hmBound ⊢
  omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_hit_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_hit_eval_oai
