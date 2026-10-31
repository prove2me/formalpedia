-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_code_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:01:20.179258+00:00
-- url     : https://prove2.me/submissions/85df08fa-9016-4636-bece-50c1a1e75778

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S130
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Dictionary_finish_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Dictionary_insert_hit_eval

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

theorem copyMiss_eval (regs : Fin 8 → Bool) (a : Tape) (he : a.out = []) :
    Eval (copy 17 0 23) (7 * a.coeff.length + 5) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with out := a.coeff }) := by
  apply copy_machine regs a _ 17 0 23 (by decide) (by decide) (by decide) rfl
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

theorem insert_miss_eval (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (entries : List (List Bool × List Bool)) (query coeff : List Bool)
    (hmiss : entries.lookup query = none) :
    ∃ n ≤ insertBudget entries query coeff (7 * coeff.length + 5), ∃ rr,
      Eval insert n (machine regs (inputTape modulus width count entries query coeff))
        (machine rr (outputTape modulus width count (updatedBytes entries query coeff) coeff)) := by
  let a := inputTape modulus width count entries query coeff
  let a1 : Tape := { a with remain := a.dict }
  let r1 := readRegs regs 0 1 none
  have hp := copyDict_eval regs a rfl
  obtain ⟨n,hn,r2,tail,hl,hflag,htail⟩ := lookup_eval r1 a1 query entries rfl
    (rawEntries_eq_lookupRecords entries) rfl
  let r3 := overlay r1 r2
  let a2 : Tape := { a1 with remain := tail, found := Squarefree.Program.lookupResult (entries.lookup query) }
  have hm := copyMiss_eval r3 a2 rfl
  have hb : (machine r3 a2).regs 4 = false := by
    change overlay r1 r2 (smallRegs 4) = false
    rw [show overlay r1 r2 (smallRegs 4) = r2 4 from smallRegs_injective.extend_apply _ _ _]
    simpa only [hmiss,Option.isSome_none] using hflag
  have hbranch := Eval.ite_false (yes := onHit) hb hm
  let a3 : Tape := { a2 with out := a2.coeff }
  obtain ⟨m,hmBound,rr,hf⟩ := finish_eval (readRegs r3 0 1 none) a3 entries query coeff rfl rfl rfl rfl rfl
  have run := hp.seq (hl.seq (hbranch.seq hf))
  refine ⟨_, ?_, rr, (by simpa [insert,onMiss,finish,a,a1,a2,a3,r1,r3,inputTape,outputTape,hmiss,
    Squarefree.Program.lookupResult,SubexponentialSAT.Subexp.SelectorProgram.framedResult] using run)⟩
  have htail' : tail.length ≤ (Squarefree.Program.rawEntries entries).length := by
    simpa only [rawEntries_eq_lookupRecords] using htail
  dsimp [a,a1,a2,a3,inputTape,insertBudget,finishBudget] at hn hmBound ⊢
  omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

theorem leftBits_codePairs {B d : ℕ} (x y : RingProgram.Code (Word B) d) :
    RingScan.leftBits (codePairs x y) = RingProgram.flat x := by
  have h (l : List (Word B × Word B)) : RingScan.leftBits l = (l.map fun z => z.1.val).flatten := by
    induction l with
    | nil => rfl
    | cons z l ih => simp only [RingScan.leftBits,List.map_cons,List.flatten_cons,ih]
  simp only [h,codePairs,List.map_ofFn,RingProgram.flat,Function.comp_def]

theorem rightBits_codePairs {B d : ℕ} (x y : RingProgram.Code (Word B) d) :
    RingScan.rightBits (codePairs x y) = RingProgram.flat y := by
  have h (l : List (Word B × Word B)) : RingScan.rightBits l = (l.map fun z => z.2.val).flatten := by
    induction l with
    | nil => rfl
    | cons z l ih => simp only [RingScan.rightBits,List.map_cons,List.flatten_cons,ih]
  simp only [h,codePairs,List.map_ofFn,RingProgram.flat,Function.comp_def]

theorem sumBits_codePairs (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (x y : RingProgram.Code (Word (baseWidth p t)) d) :
    RingScan.sumBits p t M (codePairs x y) =
      RingProgram.flat (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1 := by
  have h (l : List (Word (baseWidth p t) × Word (baseWidth p t))) :
      RingScan.sumBits p t M l = (l.map fun z => (SubexpPreparedQuartic.wordAdd p t M z.1 z.2).1.val).flatten := by
    induction l with
    | nil => rfl
    | cons z l ih => simp only [RingScan.sumBits,List.map_cons,List.flatten_cons,ih]
  simp only [h,codePairs,List.map_ofFn,RingProgram.flat,RingProgram.addRun,
    RingProgram.tabulateRun_eq,RingProgram.scalarProgram,Function.comp_def]

theorem lookup_encode (key : K → List Bool) {C : Type*} (coeff : C → List Bool)
    (hk : Function.Injective key) (entries : List (K × C)) (k : K) :
    (Squarefree.Program.encodeDictionary key coeff entries).lookup (key k) =
      (entries.lookup k).map coeff := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    rcases a with ⟨j,c⟩
    by_cases h : j=k
    · subst j; simp [Squarefree.Program.encodeDictionary]
    · have he : key j ≠ key k := fun hh => h (hk hh)
      simp only [Squarefree.Program.encodeDictionary,List.map_cons,List.lookup_cons] at ih ⊢
      simp [beq_false_of_ne (Ne.symm h),beq_false_of_ne (Ne.symm he),ih]

theorem hitBudget_codePairs (p t : ℕ) {d : ℕ}
    (x y : RingProgram.Code (Word (baseWidth p t)) d) :
    hitBudget p t (codePairs x y) = codeBranchBudget (baseWidth p t) d := by
  rw [hitBudget,leftBits_codePairs,rightBits_codePairs]
  simp only [RingProgram.flat_length,codePairs,List.length_ofFn,codeBranchBudget]
  ring


theorem encoded_update {C : Type*} (key : K → List Bool) (coeff : C → List Bool)
    (hk : Function.Injective key) (entries : List (K × C)) (k : K) (c : C) :
    Squarefree.Program.rawEntries (Squarefree.Program.encodeDictionary key coeff
      ((k,c)::(Squarefree.Sparse.erase k entries).reverse)) =
    updatedBytes (Squarefree.Program.encodeDictionary key coeff entries) (key k) (coeff c) := by
  simp only [Squarefree.Program.encodeDictionary,List.map_cons,List.map_reverse,updatedBytes]
  have he : List.map (fun a : K × C => (key a.1,coeff a.2)) (Squarefree.Sparse.erase k entries) =
      Squarefree.Program.erasedEntries (key k) (List.map (fun a : K × C => (key a.1,coeff a.2)) entries) := by
    induction entries with
    | nil => rfl
    | cons a entries ih =>
      by_cases h : a.1 = k
      · simp [Squarefree.Sparse.erase,Squarefree.Program.erasedEntries,h] at ih ⊢
        exact ih
      · have h' : key a.1 ≠ key k := fun e => h (hk e)
        simp [Squarefree.Sparse.erase,Squarefree.Program.erasedEntries,h,h'] at ih ⊢
        exact ih
  rw [he]

/-- The real insertion machine refines normalized additive insertion on concrete
coefficient vectors. It executes the same fixed table for every dimension. -/
theorem insert_code_eval_oai (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (key : K → List Bool) (hk : Function.Injective key)
    (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (regs : Fin 8 → Bool) (width count : List Bool)
    (hc : count.length = d) (hw : width.length = baseWidth p t) :
    let encoded := Squarefree.Program.encodeDictionary key RingProgram.flat entries
    let value := match entries.lookup k with
      | none => x
      | some y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1
    ∃ n ≤ insertBudget encoded (key k) (RingProgram.flat value) (codeBranchBudget (baseWidth p t) d),
    ∃ rr, Eval insert n (machine regs (inputTape M.bits width count encoded (key k) (RingProgram.flat x)))
      (machine rr (outputTape M.bits width count
        (Squarefree.Program.rawEntries (Squarefree.Program.encodeDictionary key RingProgram.flat
          (insertCode p t M cache k x entries))) (RingProgram.flat x))) := by
  dsimp only
  cases he : entries.lookup k with
  | none =>
    have hl : (Squarefree.Program.encodeDictionary key RingProgram.flat entries).lookup (key k) = none := by
      rw [lookup_encode key RingProgram.flat hk,he]; rfl
    obtain ⟨n,hn,rr,hr⟩ := insert_miss_eval regs M.bits width count
      (Squarefree.Program.encodeDictionary key RingProgram.flat entries) (key k) (RingProgram.flat x) hl
    refine ⟨n,?_,rr,?_⟩
    · have hb : 7 * (RingProgram.flat x).length + 5 ≤ codeBranchBudget (baseWidth p t) d := by
        rw [RingProgram.flat_length]
        dsimp [codeBranchBudget]
        nlinarith [Nat.zero_le (d*(6000*(baseWidth p t+1)^2))]
      simp only [] at ⊢
      dsimp [insertBudget] at hn ⊢
      omega
    · simpa only [insertCode,he,encoded_update key RingProgram.flat hk] using hr
  | some y =>
    have hl : (Squarefree.Program.encodeDictionary key RingProgram.flat entries).lookup (key k) =
        some (RingScan.rightBits (codePairs x y)) := by
      rw [lookup_encode key RingProgram.flat hk,he,rightBits_codePairs]; rfl
    obtain ⟨n,hn,rr,hr⟩ := insert_hit_eval p t M (codePairs x y) regs width count
      (Squarefree.Program.encodeDictionary key RingProgram.flat entries) (key k) hl
      (by simpa only [codePairs,List.length_ofFn] using hc) hw
    refine ⟨n,?_,rr,?_⟩
    · simpa only [he,hitBudget_codePairs,sumBits_codePairs p t M cache] using hn
    · simpa only [insertCode,he,encoded_update key RingProgram.flat hk,
        leftBits_codePairs,sumBits_codePairs p t M cache] using hr

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_code_eval_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_code_eval_oai.{u_1}
