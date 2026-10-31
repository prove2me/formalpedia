-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.finish_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:00:52.326104+00:00
-- url     : https://prove2.me/submissions/148f6373-39b3-43ca-9909-69179c53eae9

import Mathlib
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Squarefree_Program_dictionaryReplace_trace

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

theorem transfer_eval (d : Data) (src dst : Fin 27) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (transferred d src dst) := by
  apply Eval.call
  have h := transferProgram_trace src dst (0 : Fin 8) 1 hsd (by decide) d.regs d.stacks
  have hh := halt_after_trace _ h 3 rfl rfl
  simpa [transfer, transferred, transferResult, StructuredProgram.State.withPC,
    transferProgram, Nat.add_assoc] using hh

theorem clear_eval (d : Data) (src : Fin 27) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared d src) := by
  apply Eval.call
  have h := clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have hh := halt_after_trace _ h 2 rfl rfl
  simpa [clear, cleared, clearResult, StructuredProgram.State.withPC,
    clearProgram, Nat.add_assoc] using hh

theorem smallRegs_injective : Function.Injective smallRegs := Fin.castAdd_injective _ _
theorem replaceStacks_injective : Function.Injective replaceStacks := by decide

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

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

theorem transfer_machine (regs : Fin 8 → Bool) (a b : Tape) (src dst : Fin 27)
    (hsd : src ≠ dst) (hs : transferStacks src dst (tapes a) = tapes b) :
    Eval (transfer src dst) (3 * (tapes a src).length + 3) (machine regs a)
      (machine (readRegs regs 0 1 none) b) := by
  simpa only [transferred,machine,hs] using transfer_eval (machine regs a) src dst hsd

theorem clear_machine (regs : Fin 8 → Bool) (a b : Tape) (src : Fin 27)
    (hs : clearStacks src (tapes a) = tapes b) :
    Eval (clear src) (2 * (tapes a src).length + 3) (machine regs a)
      (machine (readRegs regs 0 1 none) b) := by
  simpa only [cleared,machine,hs] using clear_eval (machine regs a) src

theorem copyResult_eval (regs : Fin 8 → Bool) (a : Tape) (he : a.dict = []) :
    Eval (copy 25 15 23) (7 * a.result.length + 5) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with dict := a.result }) := by
  apply copy_machine regs a _ 25 15 23 (by decide) (by decide) (by decide) rfl
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem transferSum_eval (regs : Fin 8 → Bool) (a : Tape) (he : a.combined = []) :
    Eval (transfer 0 26) (3 * a.out.length + 3) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with out := [], combined := a.out.reverse }) := by
  apply transfer_machine regs a _ 0 26 (by decide)
  funext i; fin_cases i <;> simp [transferStacks,tapes,he]

theorem clearRemain_eval (regs : Fin 8 → Bool) (a : Tape) :
    Eval (clear 18) (2 * a.remain.length + 3) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with remain := [] }) := by
  apply clear_machine regs a _ 18
  funext i; fin_cases i <;> simp [clearStacks,tapes]

theorem clearResult_eval (regs : Fin 8 → Bool) (a : Tape) :
    Eval (clear 25) (2 * a.result.length + 3) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with result := [] }) := by
  apply clear_machine regs a _ 25
  funext i; fin_cases i <;> simp [clearStacks,tapes]

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

private theorem embed_replacement (regs : Fin 8 → Bool) (rr : Fin 5 → Bool)
    (a : Tape) (dict query result combined : List Bool) (hr : a.remain = []) :
    embedState smallRegs replaceStacks (machine regs a)
      (Squarefree.Program.keepCoefficient
        (Squarefree.Program.eraseData rr dict query result []) combined) =
    machine (overlay regs rr) { a with dict := dict, query := query.reverse, result := result, combined := combined } := by
  apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective replaceStacks_injective
  · intro i; exact smallRegs_injective.extend_apply _ _ _
  · intro i hi; exact Function.extend_apply' _ _ _ hi
  · intro i; fin_cases i <;> simp [machine,tapes,replaceStacks,
      Squarefree.Program.keepCoefficient,Squarefree.Program.eraseData,Squarefree.Program.extendStorage,SubexponentialSAT.SubexpRecordScan.storage,hr]
  · intro i hi
    fin_cases i <;> simp_all [machine,tapes,replaceStacks,Fin.exists_fin_succ]

theorem replace_eval (regs : Fin 8 → Bool) (a : Tape)
    (entries : List (List Bool × List Bool)) (query coeff : List Bool)
    (hd : a.dict = Squarefree.Program.rawEntries entries)
    (hq : a.query = query.reverse) (hc : a.combined = coeff.reverse)
    (hr : a.remain = []) (hout : a.result = []) :
    ∃ n ≤ Squarefree.Program.eraseBudget query entries + 4 * query.length + 4 * coeff.length + 17,
    ∃ rr, Eval replace n (machine regs a)
      (machine (overlay regs rr) { a with dict := [], query := [], result := Squarefree.Program.rawEntries ((query,coeff)::(Squarefree.Program.erasedEntries query entries).reverse), combined := [] }) := by
  obtain ⟨n,hn,rr,ht⟩ := Squarefree.Program.dictionaryReplace_trace entries query coeff (regs ∘ smallRegs)
  have hh := eval_call_lifted Squarefree.Program.dictionaryReplaceProgram smallRegs replaceStacks
    (machine regs a) smallRegs_injective replaceStacks_injective ht
  simp only [Squarefree.Program.replaceData,Squarefree.Program.replaceDone] at hh
  rw [embed_replacement _ _ _ _ _ _ _ hr,embed_replacement _ _ _ _ _ _ _ hr,overlay_same] at hh
  have ha : { a with dict := Squarefree.Program.rawEntries entries, query := query.reverse, result := [], combined := coeff.reverse } = a := by cases a; simp_all
  rw [ha] at hh
  exact ⟨n,hn,rr,hh⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem finish_eval_oai (regs : Fin 8 → Bool) (a : Tape)
    (entries : List (List Bool × List Bool)) (query coeff : List Bool)
    (hd : a.dict = Squarefree.Program.rawEntries entries) (hq : a.query = query.reverse)
    (ho : a.out = coeff) (hc : a.combined = []) (hr : a.result = []) :
    ∃ n ≤ finishBudget entries query coeff a.remain, ∃ rr,
      Eval finish n (machine regs a)
        (machine rr { a with dict := updatedBytes entries query coeff, query := [], remain := [], out := [], combined := [], result := [] }) := by
  let a1 : Tape := { a with remain := [] }
  let a2 : Tape := { a1 with out := [], combined := a1.out.reverse }
  let output := updatedBytes entries query coeff
  let a3 : Tape := { a2 with dict := [], query := [], result := output, combined := [] }
  let a4 : Tape := { a3 with dict := a3.result }
  let a5 : Tape := { a4 with result := [] }
  have hclear := clearRemain_eval regs a
  have htransfer := transferSum_eval (readRegs regs 0 1 none) a1 hc
  obtain ⟨n,hn,rr,hreplace⟩ := replace_eval
    (readRegs (readRegs regs 0 1 none) 0 1 none) a2 entries query coeff hd hq
    (by simp [a2,a1,ho]) rfl hr
  let r3 := overlay (readRegs (readRegs regs 0 1 none) 0 1 none) rr
  have hcopy := copyResult_eval r3 a3 rfl
  have hclean := clearResult_eval (readRegs r3 0 1 none) a4
  have run := hclear.seq (htransfer.seq (hreplace.seq (hcopy.seq hclean)))
  refine ⟨_, ?_, readRegs (readRegs r3 0 1 none) 0 1 none, (by simpa only [finish,a1,a2,a3,a4,a5,output,r3,updatedBytes] using run)⟩
  simp only [ho] at hn ⊢
  dsimp [finishBudget,updatedBytes]
  omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.finish_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.finish_eval_oai
