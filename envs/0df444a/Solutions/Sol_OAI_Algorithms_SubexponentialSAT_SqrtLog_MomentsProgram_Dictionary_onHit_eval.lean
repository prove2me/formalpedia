-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.onHit_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:58:49.268531+00:00
-- url     : https://prove2.me/submissions/4e699131-8536-4b04-a076-035600c4f4f4

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S110

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

theorem smallRegs_injective : Function.Injective smallRegs := Fin.castAdd_injective _ _
theorem nativeStacks_injective : Function.Injective nativeStacks := Fin.castAdd_injective _ _

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

theorem copyNew_eval (regs : Fin 8 → Bool) (a : Tape) (he : a.left = []) :
    Eval (copy 17 8 23) (7 * a.coeff.length + 5) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with left := a.coeff }) := by
  apply copy_machine regs a _ 17 8 23 (by decide) (by decide) (by decide) rfl
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem copyCount_eval (regs : Fin 8 → Bool) (a : Tape) (he : a.steps = []) :
    Eval (copy 24 11 23) (7 * a.count.length + 5) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with steps := a.count }) := by
  apply copy_machine regs a _ 24 11 23 (by decide) (by decide) (by decide) rfl
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem transferOld_eval (regs : Fin 8 → Bool) (a : Tape) (he : a.right = []) :
    Eval (transfer 8 9) (3 * a.left.length + 3) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with left := [], right := a.left.reverse }) := by
  apply transfer_machine regs a _ 8 9 (by decide)
  funext i; fin_cases i <;> simp [transferStacks,tapes,he]

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

private theorem embed_native (regs rr : Fin 8 → Bool) (a : Tape)
    (out left right steps : List Bool) :
    embedState id nativeStacks (machine regs a)
      (RingScan.addState rr a.modulus out [] left right [] steps a.width) =
    machine rr { a with out := out, left := left, right := right, steps := steps } := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id nativeStacks_injective
  · intros; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> simp_all [machine,tapes,nativeStacks,Fin.exists_fin_succ]

theorem add_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (a : Tape)
    (hm : a.modulus = M.bits) (hl : a.left = RingScan.leftBits pairs)
    (hr : a.right = RingScan.rightBits pairs) (ho : a.out = [])
    (hc : a.steps.length = pairs.length) (hw : a.width.length = baseWidth p t) :
    ∃ n ≤ pairs.length * (6000 * (baseWidth p t + 1)^2 + 34 * baseWidth p t + 29) + 6,
    ∃ rr, Eval add n (machine regs a)
      (machine rr { a with out := RingScan.sumBits p t M pairs, left := [], right := [], steps := [] }) := by
  obtain ⟨rr,n,hn,ht⟩ := RingScan.addVectorProgram_run p t M pairs regs a.steps a.width hc hw
  have hh := eval_call_lifted RingScan.addVectorProgram id nativeStacks
    (machine regs a) Function.injective_id nativeStacks_injective ht
  rw [←hm,←hl,←hr] at hh
  rw [embed_native,embed_native] at hh
  have ha : { a with out := [], left := a.left, right := a.right, steps := a.steps } = a := by
    cases a; simp_all
  rw [ha] at hh
  exact ⟨n,hn,rr,hh⟩

theorem parseStacks_injective : Function.Injective parseStacks := by decide

private theorem embed_parser (regs : Fin 8 → Bool) (rr : Fin 5 → Bool)
    (a : Tape) (found left : List Bool) :
    embedState parseRegisters parseStacks (machine regs a)
      (SubexponentialSAT.SubexpRecordScan.recordState rr found left [] [] [] []) =
    machine (overlay regs rr) { a with found := found, left := left } := by
  apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective parseStacks_injective
  · intro i; exact smallRegs_injective.extend_apply _ _ _
  · intro i hi; exact Function.extend_apply' _ _ _ hi
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> simp_all [machine,tapes,parseStacks,Fin.exists_fin_succ]

theorem parseOld_eval (regs : Fin 8 → Bool) (a : Tape) (bits : List Bool)
    (hf : a.found = Encoding.frame bits) (hl : a.left = []) :
    ∃ rr, Eval parseOld (6 * bits.length + 4) (machine regs a)
      (machine rr { a with found := [], left := bits.reverse }) := by
  let d := SubexponentialSAT.SubexpRecordScan.recordState (regs ∘ smallRegs) a.found a.left [] [] [] []
  have he := SubexponentialSAT.SubexpRecordScan.parseFrame_eval d 0 1 (by decide) bits []
    (by simpa [d,SubexponentialSAT.SubexpRecordScan.recordState,SubexponentialSAT.SubexpRecordScan.storage] using hf)
  cases he with
  | call _ ht =>
    have hh := eval_call_lifted (SubexponentialSAT.SubexpRecordScan.parseFrame 0 1)
      parseRegisters parseStacks (machine regs a) smallRegs_injective parseStacks_injective ht
    have hb : SubexponentialSAT.SubexpRecordScan.afterFrame d 0 1 bits [] =
      SubexponentialSAT.SubexpRecordScan.recordState (readRegs (regs ∘ smallRegs) 0 1 (some false))
        [] bits.reverse [] [] [] [] := by
      apply congrArg (fun st => (⟨readRegs (regs ∘ smallRegs) 0 1 (some false), st⟩ : State 5 6))
      funext i; fin_cases i <;>
          simp [d,
            SubexponentialSAT.SubexpRecordScan.storage,hl]
    rw [hb] at hh
    change Eval parseOld _
      (embedState parseRegisters parseStacks (machine regs a)
        (SubexponentialSAT.SubexpRecordScan.recordState (regs ∘ smallRegs) a.found a.left [] [] [] [])) _ at hh
    rw [embed_parser,embed_parser,overlay_same] at hh
    have ha : { a with found := a.found, left := a.left } = a := by cases a; rfl
    rw [ha] at hh
    exact ⟨_,hh⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryHit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem onHit_eval_oai (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (a : Tape)
    (hm : a.modulus = M.bits) (hnew : a.coeff = RingScan.leftBits pairs)
    (hf : a.found = Encoding.frame (RingScan.rightBits pairs))
    (hl : a.left = []) (hr : a.right = []) (ho : a.out = []) (hs : a.steps = [])
    (hc : a.count.length = pairs.length) (hw : a.width.length = baseWidth p t) :
    ∃ n ≤ hitBudget p t pairs, ∃ rr,
      Eval onHit n (machine regs a)
        (machine rr { a with found := [], left := [], right := [], steps := [], out := RingScan.sumBits p t M pairs }) := by
  obtain ⟨r1,hp⟩ := parseOld_eval regs a (RingScan.rightBits pairs) hf hl
  let a1 : Tape := { a with found := [], left := (RingScan.rightBits pairs).reverse }
  let a2 : Tape := { a1 with left := [], right := a1.left.reverse }
  let a3 : Tape := { a2 with left := a2.coeff }
  let a4 : Tape := { a3 with steps := a3.count }
  have ht := transferOld_eval r1 a1 hr
  have hn := copyNew_eval (readRegs r1 0 1 none) a2 rfl
  have hk := copyCount_eval (readRegs (readRegs r1 0 1 none) 0 1 none) a3 hs
  obtain ⟨n,nb,r5,ha⟩ := add_eval p t M pairs
    (readRegs (readRegs (readRegs r1 0 1 none) 0 1 none) 0 1 none) a4
    hm hnew (by simp [a4,a3,a2,a1]) ho hc hw
  have run := hp.seq (ht.seq (hn.seq (hk.seq ha)))
  refine ⟨_, ?_, r5, (by simpa only [onHit,a1,a2,a3,a4] using run)⟩
  dsimp [hitBudget]
  simp only [List.length_reverse,hnew,hc] at nb ⊢
  omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.onHit_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.onHit_eval_oai
