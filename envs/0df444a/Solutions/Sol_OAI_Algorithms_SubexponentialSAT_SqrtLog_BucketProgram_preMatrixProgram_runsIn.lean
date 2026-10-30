-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixProgram_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:16:18.437241+00:00
-- url     : https://prove2.me/submissions/af44ec29-c3c2-42d6-8fa6-7f8063379e8b

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S106
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_BucketProgram_preScan_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and frame-reading routines used by the encoded matrix checker. -/

namespace SubexponentialSAT.Subexp.MatrixProgramSupport

open BitProgram StructuredCalls

variable {s : ℕ}

theorem words_append (xs ys : List (List Bool)) : words (xs ++ ys) = words xs ++ words ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [words, ih, List.append_assoc]

end SubexponentialSAT.Subexp.MatrixProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessReverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed EOF-controlled reversal of a raw list of framed words. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem preReverseStep_eval (regs : Fin 8 → Bool) (x : List Bool)
    (xs : List (List Bool)) (out : List Bool) :
    ∃ rf, Eval preReverseStep (17*x.length+15)
      (preReverseState regs (x::xs) out)
      (preReverseState rf xs (Encoding.frame x++out)) := by
  let d := preReverseState regs (x::xs) out
  obtain ⟨a,ha,hsa⟩ := readWord_eval (0 : Fin 4) 1 2
    (by decide) (by decide) (by decide) d x (words xs) rfl rfl rfl
  obtain ⟨b,hb,hsb⟩ := emitFrame_eval (1 : Fin 4) 3 2
    (by decide) (by decide) (by decide) a (by rw [hsa]; rfl)
  have ha1 : a.stacks 1=x := by rw [hsa]; rfl
  have hend : b=preReverseState b.regs xs (Encoding.frame x++out) := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    rw [hsb,hsa]
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have he := ha.seq hb
  rw [hend,ha1] at he
  exact ⟨b.regs, by convert he using 1 ; omega⟩

theorem preReversePeek_eval (regs : Fin 8 → Bool) (xs : List (List Bool))
    (out : List Bool) : Eval preReversePeek 1 (preReverseState regs xs out)
      (preReverseReady regs xs out) := Eval.base (StructuredProgram.Eval.atom _ _)

theorem preReverseLoop_eval (regs : Fin 8 → Bool) (xs : List (List Bool))
    (out : List Bool) : ∃ rf,
    Eval preReverseLoop (preReverseCost xs) (preReverseReady regs xs out)
      (preReverseState rf [] (words xs.reverse++out)) := by
  induction xs generalizing regs out with
  | nil =>
      refine ⟨(preReverseReady regs [] out).regs, ?_⟩
      change Eval preReverseLoop 1 (preReverseReady regs [] out) (preReverseReady regs [] out)
      exact Eval.while_false (show (preReverseReady regs [] out).regs 1 = false by
        simp [words, readRegs])
  | cons x xs ih =>
      obtain ⟨rm,hm⟩ := preReverseStep_eval (preReverseReady regs (x::xs) out).regs x xs out
      obtain ⟨rf,hf⟩ := ih rm (Encoding.frame x++out)
      have hg : (preReverseReady regs (x::xs) out).regs 1=true := by
        cases x <;> simp [words,Encoding.frame,readRegs]
      have he := Eval.while_true hg (hm.seq (preReversePeek_eval rm xs _)) hf
      refine ⟨rf, ?_⟩
      convert he using 1 <;>
        simp [preReverseCost,List.reverse_cons,words_append,words,List.append_assoc] ; omega

theorem preReverseCommand_eval (regs : Fin 8 → Bool) (xs : List (List Bool))
    (out : List Bool) : ∃ rf,
    Eval preReverseCommand (preReverseCost xs+1) (preReverseState regs xs out)
      (preReverseState rf [] (words xs.reverse++out)) := by
  obtain ⟨rf,hf⟩ := preReverseLoop_eval regs xs out
  exact ⟨rf, by simpa [Nat.add_comm] using (preReversePeek_eval regs xs out).seq hf⟩

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A measured signed row scan, followed by a physical frame-order repair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem shiftedWords_length {W : List Bool} {xs : List SignedWord} {ys : List (List Bool)}
    (h : List.Forall₂ (shiftedWord W) xs ys) : xs.length=ys.length := by
  induction h with
  | nil => rfl
  | cons h hs ih => simpa using ih

theorem shiftedWords_totalLength {W : List Bool} {xs : List SignedWord} {ys : List (List Bool)}
    (h : List.Forall₂ (shiftedWord W) xs ys) :
    (ys.map List.length).sum ≤ preOutputLength W xs := by
  induction h with
  | nil => simp [preOutputLength]
  | cons h hs ih =>
      simp only [List.map_cons,List.sum_cons,preOutputLength] at *
      exact Nat.add_le_add h.2 ih

theorem preWords_length (ys : List (List Bool)) :
    (words ys).length=2*(ys.map List.length).sum+ys.length := by
  induction ys with
  | nil => simp [words]
  | cons y ys ih => simp [words,Encoding.length_frame,ih]; omega

theorem preReverseCost_eq (ys : List (List Bool)) :
    preReverseCost ys=17*(ys.map List.length).sum+17*ys.length+1 := by
  induction ys with
  | nil => simp [preReverseCost]
  | cons y ys ih => simp only [preReverseCost,List.map_cons,List.sum_cons,List.length_cons] at *; omega

theorem preReversePorts_injective : Function.Injective preReversePorts := by decide

theorem preRepair_eval (regs : Fin 8 → Bool) (W : List Bool) (ys : List (List Bool)) :
    ∃ rf, Eval preRepair (preReverseCost ys.reverse+2+6*(words ys).length+6)
      (preState regs W [] (words ys.reverse)) (preState rf W [] (words ys)) := by
  let d := preState regs W [] (words ys.reverse)
  have hp : projectState id preReversePorts d=preReverseState regs ys.reverse [] := by
    apply congrArg (StructuredProgram.State.mk regs)
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨rr,hr⟩ := preReverseCommand_eval regs ys.reverse []
  rw [←hp] at hr
  have hc := eval_call_from_state preReverseProgram id preReversePorts d
    Function.injective_id preReversePorts_injective (compiled_halt_trace hr 0 3)
  let e : PreData := ⟨rr,Function.update (Function.update d.stacks 11 []) 13 (words ys)⟩
  have he : embedState id preReversePorts d
      (preReverseState rr [] (words ys.reverse.reverse++[]))=e := by
    apply embedState_eq_of_ports id preReversePorts d _ _ Function.injective_id preReversePorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [preReversePorts,e,d,preState,signedWords,words]
    · intro i hi
      have h11 : i≠11 := fun h => hi ⟨0,h.symm⟩
      have h13 : i≠13 := fun h => hi ⟨3,h.symm⟩
      simp [e,h11,h13]
  rw [he] at hc
  obtain ⟨f,hf,hsf⟩ := move_eval (13 : Fin 14) 11 12
    (by decide) (by decide) (by decide) e (by simp [e]) (by simp [e,d,preState])
  have he13 : e.stacks 13=words ys := by simp [e]
  have hend : f=preState f.regs W [] (words ys) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    rw [hsf]
    funext i; fin_cases i <;> simp [e,d,preState,signedWords]
  have hh := hc.seq hf
  rw [hend,he13] at hh
  exact ⟨f.regs, by simpa [preRepair, d, Nat.add_assoc] using hh⟩

theorem preRowCommand_eval (regs : Fin 8 → Bool) (W : List Bool) (xs : List SignedWord) :
    ∃ t ≤ preRowCost W xs, ∃ rf ys,
      Eval preRowCommand t (preState regs W xs []) (preState rf W [] (words ys)) ∧
      List.Forall₂ (shiftedWord W) xs ys := by
  obtain ⟨t,ht,rm,ys,he,hy⟩ := preScan_eval regs W xs
  obtain ⟨rf,hf⟩ := preRepair_eval rm W ys
  have hl := shiftedWords_totalLength hy
  have hn := shiftedWords_length hy
  refine ⟨_,?_,rf,ys,he.seq hf,hy⟩
  rw [preReverseCost_eq,preWords_length]
  simp only [List.length_reverse,List.map_reverse,List.sum_reverse]
  dsimp [preRowCost]
  omega

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete row-major signed matrix preprocessor. All input and output
frames are scanned by fixed instructions; the original bound word is retained. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem preMatrixStep_eval (regs : Fin 8 → Bool) (W : List Bool)
    (row : List SignedWord) (rows : List (List SignedWord)) (acc : List Bool) :
    ∃ t ≤ preMatrixStepCost W row, ∃ rf ys,
      Eval preMatrixStep t (preMatrixState regs W (row::rows) acc)
        (preMatrixState rf W rows (Encoding.frame (words ys)++acc)) ∧
      List.Forall₂ (shiftedWord W) row ys := by
  let d := preMatrixState regs W (row::rows) acc
  obtain ⟨a,ha,hsa⟩ := readWord_eval (14 : Fin 17) 10 12
    (by decide) (by decide) (by decide) d (signedWords row)
    (words (rows.map signedWords)) rfl rfl rfl
  have hp : projectState id preRowPorts a=preState a.regs W row [] := by
    apply congrArg (StructuredProgram.State.mk a.regs)
    funext i; fin_cases i <;> simp [preRowPorts,hsa,d,preMatrixState]
  obtain ⟨tr,htr,rr,ys,hr,hy⟩ := preRowCommand_eval a.regs W row
  rw [←hp] at hr
  have hc := eval_call_from_state preRowProgram id preRowPorts a
    Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace hr 10 11)
  let e : PreMatrixData := ⟨rr,Function.update (Function.update a.stacks 10 []) 11 (words ys)⟩
  have he : embedState id preRowPorts a (preState rr W [] (words ys))=e := by
    apply embedState_eq_of_ports id preRowPorts a _ _ Function.injective_id
      (Fin.castAdd_injective _ _)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [preRowPorts,preState,e,hsa,d,preMatrixState,signedWords]
    · intro i hi
      have h10 : i≠10 := fun h => hi ⟨10,h.symm⟩
      have h11 : i≠11 := fun h => hi ⟨11,h.symm⟩
      simp [e,h10,h11]
  rw [he] at hc
  obtain ⟨f,hf,hsf⟩ := emitFrame_eval (11 : Fin 17) 15 12
    (by decide) (by decide) (by decide) e (by simp [e,hsa,d,preMatrixState])
  have he11 : e.stacks 11=words ys := by simp [e]
  have hend : f=preMatrixState f.regs W rows (Encoding.frame (words ys)++acc) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    rw [hsf]
    funext i; fin_cases i <;> simp [e,hsa,d,preMatrixState]
  have hall := ha.seq (hc.seq hf)
  rw [hend] at hall
  have hl := shiftedWords_totalLength hy
  have hn := shiftedWords_length hy
  refine ⟨_,?_,f.regs,ys,hall,hy⟩
  rw [he11,preWords_length]
  dsimp [preMatrixStepCost]
  omega

theorem preMatrixPeek_eval (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) (acc : List Bool) :
    Eval preMatrixPeek 1 (preMatrixState regs W rows acc) (preMatrixReady regs W rows acc) :=
  Eval.base (StructuredProgram.Eval.atom _ _)

theorem preMatrixLoop_eval (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) (acc : List Bool) :
    ∃ t ≤ preMatrixScanCost W rows, ∃ rf ys,
      Eval preMatrixLoop t (preMatrixReady regs W rows acc)
        (preMatrixState rf W [] (words (ys.map words).reverse++acc)) ∧
      List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys := by
  induction rows generalizing regs acc with
  | nil =>
      refine ⟨1,by simp [preMatrixScanCost],readRegs regs 0 1 none,[],?_,.nil⟩
      simpa [preMatrixLoop, preMatrixReady, words] using (Eval.while_false
        (show (preMatrixReady regs W [] acc).regs 1=false by
          simp [preMatrixReady,preMatrixState,words,readRegs]) :
        Eval preMatrixLoop 1 (preMatrixReady regs W [] acc) (preMatrixReady regs W [] acc))
  | cons row rows ih =>
      obtain ⟨ts,hts,rs,y,hes,hy⟩ := preMatrixStep_eval
        (preMatrixReady regs W (row::rows) acc).regs W row rows acc
      obtain ⟨tt,htt,rf,ys,het,hys⟩ := ih rs (Encoding.frame (words y)++acc)
      have hg : (preMatrixReady regs W (row::rows) acc).regs 1=true := by
        cases hr : signedWords row <;> simp [preMatrixReady,preMatrixState,words,Encoding.frame,readRegs,hr]
      have he := Eval.while_true hg (hes.seq (preMatrixPeek_eval rs W rows _)) het
      refine ⟨(ts+1)+tt+1,?_,rf,y::ys,?_,.cons hy hys⟩
      · simp only [preMatrixScanCost,List.map_cons,List.sum_cons] at *; omega
      · simpa [preMatrixLoop,preMatrixBody,List.reverse_cons,words_append,words,
          List.append_assoc] using he

theorem shiftedMatrix_lengths {W : List Bool} {rows : List (List SignedWord)}
    {ys : List (List (List Bool))} (h : List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys) :
    rows.length=ys.length ∧ ((ys.map words).map List.length).sum ≤ preMatrixPayload W rows := by
  induction h with
  | nil => simp [preMatrixPayload]
  | cons h hs ih =>
      have hl := shiftedWords_totalLength h
      have hn := shiftedWords_length h
      simp only [List.length_cons,List.map_cons,List.sum_cons,preWords_length,preMatrixPayload] at *
      constructor <;> omega

theorem preMatrixReversePorts_injective : Function.Injective preMatrixReversePorts := by decide

theorem preMatrixRepair_eval (regs : Fin 8 → Bool) (W : List Bool) (ys : List (List Bool)) :
    ∃ rf, Eval preMatrixRepair (preReverseCost ys.reverse+2+6*(words ys).length+6)
      (preMatrixState regs W [] (words ys.reverse)) (preMatrixState rf W [] (words ys)) := by
  let d := preMatrixState regs W [] (words ys.reverse)
  have hp : projectState id preMatrixReversePorts d=preReverseState regs ys.reverse [] := by
    apply congrArg (StructuredProgram.State.mk regs)
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨rr,hr⟩ := preReverseCommand_eval regs ys.reverse []
  rw [←hp] at hr
  have hc := eval_call_from_state preReverseProgram id preMatrixReversePorts d
    Function.injective_id preMatrixReversePorts_injective (compiled_halt_trace hr 0 3)
  let e : PreMatrixData := ⟨rr,Function.update (Function.update d.stacks 15 []) 16 (words ys)⟩
  have he : embedState id preMatrixReversePorts d
      (preReverseState rr [] (words ys.reverse.reverse++[]))=e := by
    apply embedState_eq_of_ports id preMatrixReversePorts d _ _ Function.injective_id preMatrixReversePorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [preMatrixReversePorts,e,d,preMatrixState,words]
    · intro i hi
      have h15 : i≠15 := fun h => hi ⟨0,h.symm⟩
      have h16 : i≠16 := fun h => hi ⟨3,h.symm⟩
      simp [e,h15,h16]
  rw [he] at hc
  obtain ⟨f,hf,hsf⟩ := move_eval (16 : Fin 17) 15 12
    (by decide) (by decide) (by decide) e (by simp [e]) (by simp [e,d,preMatrixState])
  have he16 : e.stacks 16=words ys := by simp [e]
  have hend : f=preMatrixState f.regs W [] (words ys) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    rw [hsf]
    funext i; fin_cases i <;> simp [e,d,preMatrixState,words]
  have hall := hc.seq hf
  rw [hend,he16] at hall
  refine ⟨f.regs, ?_⟩
  convert hall using 1 <;> first | rfl | omega

theorem preMatrixCommand_eval (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) :
    ∃ t ≤ preMatrixCost W rows, ∃ rf ys,
      Eval preMatrixCommand t (preMatrixState regs W rows [])
        (preMatrixState rf W [] (words (ys.map words))) ∧
      List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys := by
  obtain ⟨ts,hts,rs,ys,hs,hys⟩ := preMatrixLoop_eval regs W rows []
  have hscan := (preMatrixPeek_eval regs W rows []).seq hs
  obtain ⟨rf,hr⟩ := preMatrixRepair_eval rs W (ys.map words)
  simp only [List.append_nil] at hscan
  have hl := shiftedMatrix_lengths hys
  refine ⟨_,?_,rf,ys,hscan.seq hr,hys⟩
  rw [preReverseCost_eq,preWords_length]
  simp only [List.length_reverse,List.length_map,List.map_reverse,List.sum_reverse]
  dsimp [preMatrixCost]
  omega

theorem preMatrixProgram_runsIn_oai (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) :
    ∃ rf ys, RunsIn preMatrixProgram (preMatrixCost W rows+1)
      ((preMatrixState regs W rows []).withPC (some preMatrixProgram.entry))
      ((preMatrixState rf W [] (words (ys.map words))).withPC none) ∧
      List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys := by
  obtain ⟨t,ht,rf,ys,he,hy⟩ := preMatrixCommand_eval regs W rows
  exact ⟨rf,ys,⟨t+1,by omega,compiled_halt_trace he 14 15⟩,hy⟩

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixProgram_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixProgram_runsIn_oai
