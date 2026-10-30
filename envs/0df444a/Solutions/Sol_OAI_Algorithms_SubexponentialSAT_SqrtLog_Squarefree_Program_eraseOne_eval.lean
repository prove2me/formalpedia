-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.eraseOne_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:01:13.931874+00:00
-- url     : https://prove2.me/submissions/2383b591-1008-4056-9514-a5db445a82f8

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S114

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Destructive key comparison with query preservation and complete scratch
cleanup, as a fixed primitive subroutine for dictionary replacement. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

theorem compareDictionaryKey_eval (regs : Fin 5 → Bool)
    (source key query output : List Bool) :
    ∃ n ≤ 11 * key.length + 9 * query.length + 20, ∃ final,
      Eval compareDictionaryKey n
        (recordState regs source key.reverse query.reverse [] [] output)
        (recordState final source [] query.reverse [] [] output) ∧
      final 4 = decide (key = query) := by
  let r0 := readRegs regs 0 1 none
  have hcopy : Eval (.call (StackRoutines.copyProgram 2 3 4 (0 : Fin 5) 1))
      (7 * query.length + 5)
      (recordState regs source key.reverse query.reverse [] [] output)
      (recordState r0 source key.reverse query.reverse query.reverse [] output) := by
    simpa [afterCopy, StackRoutines.copyStacks, recordState, r0] using
      copy_eval (recordState regs source key.reverse query.reverse [] [] output)
        2 3 4 (by decide) (by decide) (by decide) rfl
  obtain ⟨nc, hnc, rr, left, right, hcompare, hanswer, hleft, hright⟩ :=
    compareKeys_eval r0 source key.reverse query.reverse query.reverse [] output
  simp only [List.length_reverse] at hnc hleft hright
  have hans : rr 4 = decide (key = query) := by simpa only [List.reverse_inj] using hanswer
  let r1 := readRegs rr 0 1 none
  let r2 := readRegs r1 0 1 none
  have hclear1 : Eval (.call (StackRoutines.clearProgram 1 (0 : Fin 5) 1))
      (2 * left.length + 3)
      (recordState rr source left query.reverse right [] output)
      (recordState r1 source [] query.reverse right [] output) := by
    simpa [afterClear, StackRoutines.clearStacks, recordState, r1] using
      clear_eval (recordState rr source left query.reverse right [] output) 1
  have hclear3 : Eval (.call (StackRoutines.clearProgram 3 (0 : Fin 5) 1))
      (2 * right.length + 3)
      (recordState r1 source [] query.reverse right [] output)
      (recordState r2 source [] query.reverse [] [] output) := by
    simpa [afterClear, StackRoutines.clearStacks, recordState, r2] using
      clear_eval (recordState r1 source [] query.reverse right [] output) 3
  refine ⟨(7 * query.length + 5) + (nc + ((2 * left.length + 3) + (2 * right.length + 3))),
    by omega, r2, hcopy.seq (hcompare.seq (hclear1.seq hclear3)), ?_⟩
  first | (simpa [r2, r1, readRegs, -OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.status_read] using hans) | (simpa [r2, r1, readRegs] using hans)
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Port relocation and paid bit-copy primitives for the dictionary builder. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpRecordScan

theorem embedStorage (a b : State 5 6) (saved : List Bool) :
    embedState id Fin.castSucc (extendStorage a saved) b = extendStorage b saved := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (Fin.castSucc_injective 6)
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have hi' : ¬ i.val < 6 := by
      intro hil
      apply hi
      exact ⟨⟨i.val, hil⟩, Fin.ext rfl⟩
    have hv : i.val = 6 := by have := i.isLt; omega
    have he : i = (6 : Fin 7) := Fin.ext hv
    subst i
    rfl

theorem storageCall_eval {c : Cmd 5 6} {n : ℕ} {a b : State 5 6}
    (h : Eval c n a b) (saved : List Bool) :
    Eval (storageCall c) (n + 1) (extendStorage a saved) (extendStorage b saved) := by
  have hh := eval_liftCommand h 0 5 id Fin.castSucc (extendStorage a saved)
    Function.injective_id (Fin.castSucc_injective 6)
  simpa only [storageCall, embedStorage] using hh

theorem storageCopy_eval (d : StorageData) (src dst tmp : Fin 7)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (htmp : d.stacks tmp = []) :
    Eval (storageCopy src dst tmp) (7 * (d.stacks src).length + 5)
      d (storageCopied d src dst) := by
  apply Eval.call
  have h := StackRoutines.copyProgram_trace src dst tmp (0 : Fin 5) 1
    hsd hst htd (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  simpa [storageCopied, StackRoutines.copyResult, StructuredProgram.State.withPC,
    StackRoutines.copyProgram, Nat.add_assoc] using hh

theorem storageClear_eval (d : StorageData) (src : Fin 7) :
    Eval (storageClear src) (2 * (d.stacks src).length + 3)
      d (storageCleared d src) := by
  apply Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 5) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [storageCleared, StackRoutines.clearResult, StructuredProgram.State.withPC,
    StackRoutines.clearProgram, Nat.add_assoc] using hh
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramErase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete one-record deletion for sparse coefficient dictionaries. The
selected key is saved before comparison; retained records are emitted intact. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

theorem frameRegPorts_injective : Function.Injective frameRegPorts := Fin.castAdd_injective _ _
theorem frameStackPorts_injective : Function.Injective frameStackPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [frameStackPorts]

theorem emitSaved_eval (regs : Fin 5 → Bool) (source query output key : List Bool) :
    ∃ final, Eval emitSaved (4 * key.length + 6)
      (eraseData regs source query output key.reverse)
      (eraseData final source query (Encoding.frame key ++ output) []) := by
  let d := eraseData regs source query output key.reverse
  obtain ⟨rr, ht⟩ := frameEmit_trace key output (regs ∘ frameRegPorts)
  let b := frameData rr [] (Encoding.frame key ++ output)
  let final := (embedState frameRegPorts frameStackPorts d b).regs
  have ha : embedState frameRegPorts frameStackPorts d
      (frameData (regs ∘ frameRegPorts) key.reverse output) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ frameRegPorts_injective frameStackPorts_injective
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [d, frameData, frameStackPorts, extendStorage, storage]
    · intros; rfl
  have hb : embedState frameRegPorts frameStackPorts d b =
      eraseData final source query (Encoding.frame key ++ output) [] := by
    apply embedState_eq_of_ports _ _ _ _ _ frameRegPorts_injective frameStackPorts_injective
    · intro i
      exact embedState_register frameRegPorts frameStackPorts d b frameRegPorts_injective i
    · intro i hi
      exact embedState_register_frame frameRegPorts frameStackPorts d b i hi
    · intro i; fin_cases i <;> simp [b, eraseData, frameData, frameStackPorts, extendStorage, storage]
    · intro i hi
      fin_cases i <;> simp_all [d, eraseData, frameStackPorts, extendStorage, storage,
        Fin.exists_fin_succ]
  refine ⟨final, ?_⟩
  have he := eval_call_lifted frameEmitProgram frameRegPorts frameStackPorts d
    frameRegPorts_injective frameStackPorts_injective ht
  change Eval emitSaved (4 * key.length + 6)
    (embedState frameRegPorts frameStackPorts d (frameData (regs ∘ frameRegPorts) key.reverse output))
    (embedState frameRegPorts frameStackPorts d b) at he
  rw [ha,hb] at he
  exact he

theorem eraseBranch_eval (regs : Fin 5 → Bool) (key query payload tail output : List Bool)
    (hflag : regs 4 = decide (key = query)) :
    ∃ n ≤ 4 * key.length + 13 * payload.length + 19, ∃ final,
      Eval eraseBranch n
        (eraseData regs (Encoding.frame payload ++ tail) query output key.reverse)
        (eraseData final tail query
          (if key = query then output else Encoding.frame key ++ Encoding.frame payload ++ output) []) := by
  by_cases hk : key = query
  · have hf : regs 4 = true := by simpa [hk] using hflag
    have hs := storageCall_eval
      (skipPayload_eval (recordState regs (Encoding.frame payload ++ tail) [] query.reverse [] [] output)
        payload tail rfl) key.reverse
    let rr := readRegs regs 0 1 (some false)
    have hs' : Eval (storageCall (.call skipPayload)) (5 * payload.length + 5)
        (eraseData regs (Encoding.frame payload ++ tail) query output key.reverse)
        (eraseData rr tail query output key.reverse) := by
      simpa [eraseData, afterSkip, recordState, rr, Nat.add_assoc] using hs
    have hc := storageClear_eval (eraseData rr tail query output key.reverse) 6
    let rr' := readRegs rr 0 1 none
    have hc' : Eval (storageClear 6) (2 * key.length + 3)
        (eraseData rr tail query output key.reverse) (eraseData rr' tail query output []) := by
      convert hc using 1
      · simp [eraseData, extendStorage]
      · apply congrArg₂ StructuredProgram.State.mk
        · rfl
        · funext i; fin_cases i <;>
            simp [eraseData, extendStorage, StackRoutines.clearStacks, storage]
    refine ⟨(5 * payload.length + 5) + (2 * key.length + 3) + 1, by omega, rr', ?_⟩
    simpa [eraseBranch, eraseDrop, hk] using (Eval.ite_true hf (hs'.seq hc') : Eval (.ite 4 eraseDrop eraseKeep) _ _ _)
  · have hf : regs 4 = false := by simpa [hk] using hflag
    have hs := storageCall_eval
      (copyPayload_eval (recordState regs (Encoding.frame payload ++ tail) [] query.reverse [] [] output)
        payload tail rfl rfl) key.reverse
    let rr := readRegs regs 0 1 none
    have hs' : Eval (storageCall (.call copyPayload)) (13 * payload.length + 12)
        (eraseData regs (Encoding.frame payload ++ tail) query output key.reverse)
        (eraseData rr tail query (Encoding.frame payload ++ output) key.reverse) := by
      simpa [eraseData, afterPayload, recordState, rr, Nat.add_assoc] using hs
    obtain ⟨final,he⟩ := emitSaved_eval rr tail query (Encoding.frame payload ++ output) key
    refine ⟨(13 * payload.length + 12) + (4 * key.length + 6) + 1, by omega, final, ?_⟩
    simpa [eraseBranch, eraseKeep, hk, List.append_assoc] using
      (Eval.ite_false hf (hs'.seq he) : Eval (.ite 4 eraseDrop eraseKeep) _ _ _)

theorem eraseOne_eval_oai (regs : Fin 5 → Bool) (key query payload tail output : List Bool) :
    ∃ n ≤ 28 * key.length + 9 * query.length + 13 * payload.length + 50, ∃ final,
      Eval eraseOne n
        (eraseData regs (Encoding.frame key ++ Encoding.frame payload ++ tail) query output [])
        (eraseData final tail query
          (if key = query then output else Encoding.frame key ++ Encoding.frame payload ++ output) []) := by
  let source := Encoding.frame payload ++ tail
  let r0 := readRegs regs 0 1 (some false)
  have hp := storageCall_eval
    (parseFrame_eval (recordState regs (Encoding.frame key ++ source) [] query.reverse [] [] output)
      0 1 (by decide) key source rfl) []
  have hp' : Eval (storageCall (.call (parseFrame 0 1))) (6 * key.length + 5)
      (eraseData regs (Encoding.frame key ++ source) query output [])
      (extendStorage (recordState r0 source key.reverse query.reverse [] [] output) []) := by
    simpa [eraseData, afterFrame, recordState, r0, Nat.add_assoc] using hp
  let d := extendStorage (recordState r0 source key.reverse query.reverse [] [] output) []
  have hs := storageCopy_eval d 1 6 4 (by decide) (by decide) (by decide) (by simp [d,extendStorage,storage])
  let r1 := readRegs r0 0 1 none
  have hs' : Eval (storageCopy 1 6 4) (7 * key.length + 5) d
      (extendStorage (recordState r1 source key.reverse query.reverse [] [] output) key.reverse) := by
    convert hs using 1
    · simp [d,extendStorage,storage]
    · apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; fin_cases i <;>
          simp [d,extendStorage,storage,StackRoutines.copyStacks]
  obtain ⟨nc, hnc, r2, hc, hf⟩ := compareDictionaryKey_eval r1 source key query output
  have hc' := storageCall_eval hc key.reverse
  obtain ⟨nb, hnb, final,hb⟩ := eraseBranch_eval r2 key query payload tail output hf
  refine ⟨(6 * key.length + 5) + ((7 * key.length + 5) + ((nc + 1) + nb)), by omega, final, ?_⟩
  simpa only [eraseOne, source, List.append_assoc] using hp'.seq (hs'.seq (hc'.seq hb))
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.eraseOne_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.eraseOne_eval_oai
