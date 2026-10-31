-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult_nonoutput_length
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:39:37.628667+00:00
-- url     : https://prove2.me/submissions/ab93c04f-4dc5-4551-a62b-b873b8b4ab2d

import Mathlib
import Definitions.Def_OAIQ081S165

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical storage operations for the closed parameter setup

All copies, clears, and register resets are fixed instruction sequences or
calls to proved bit programs. Their state transformations below are assertion
notation only. The setup program uses them to isolate dirty arithmetic
subroutines from the persistent parameter words.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem finish_empty {S : ℕ} (ports : List (Fin S)) (outputs : List (Fin S × Fin S))
    (a : Data S) (i : Fin S) (hi : i ∈ ports) :
    (finishState ports outputs a).stacks i = [] := by
  rw [finishState, resetMany_stacks, clearMany_stacks, ite_eq_left hi]

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame and value rules for the actual setup copy/cleanup routines. -/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem finish_frame {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (hp : i ∉ ports) (ho : ∀ p ∈ outputs, i ≠ p.2) :
    (finishState ports outputs a).stacks i = a.stacks i := by
  have hmem : i ∉ outputs.map Prod.snd := by
    intro hi
    obtain ⟨p, hm, he⟩ := List.mem_map.mp hi
    exact ho p hm he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hp,
    copyMany_frame _ _ _ ho, clearMany_stacks, ite_eq_right hmem]

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, isolated service calls in the leaf head-builder's reserved bank.
The entire local service bank is moved to340..627. In particular a matrix
entry bank cannot overwrite the persistent ring tables below340. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem work_mem_workPorts {s : ℕ} (hs : s ≤ 288) (j : Fin s) :
    workPort hs j ∈ workPorts hs := by
  simp only [workPorts,List.mem_ofFn]
  exact ⟨j,rfl⟩

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The isolated bank never enlarges a non-output stack. This includes work
ports and the copy temporary, not only protected source masters. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem returned_nonoutput_eq {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (i : Fin 768) (hn : ∀ p∈outs,i≠p.2) :
    (returned reg hs ins outs a b).stacks i=
      if i∈workPorts hs ∨ i=temporary then [] else a.stacks i := by
  by_cases hw : i∈workPorts hs
  · rw [returned,finish_empty _ _ _ _ hw]
    simp [hw]
  have hno : ¬∃j,workPort hs j=i := by
    rintro ⟨j,rfl⟩
    exact hw (work_mem_workPorts hs j)
  have hin : ∀ p∈inputCopies hs ins,i≠p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    intro he
    exact hno ⟨q.2,he.symm⟩
  have hout : ∀ p∈outputCopies hs outs,i≠p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hn q hq
  calc
    (returned reg hs ins outs a b).stacks i=(prepared hs ins a).stacks i :=
      (finish_frame _ _ _ i hw hout).trans
        (embedState_stack_frame reg (workPort hs) _ b i hno)
    _ = (beforeCopies temporary (workPorts hs) a).stacks i := copyMany_frame _ _ i hin
    _ = _ := by simp [beforeCopies,resetMany_stacks,clearMany_stacks,hw]

theorem returned_nonoutput_length_le {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (i : Fin 768) (hn : ∀ p∈outs,i≠p.2) :
    ((returned reg hs ins outs a b).stacks i).length ≤ (a.stacks i).length := by
  rw [returned_nonoutput_eq reg hs ins outs a b i hn]
  split_ifs <;> simp

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage



theorem prepare_nonoutput_length (a : Data) (rp : Fin 8 → Bool)
    (n N : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) (i : Fin 768)
    (h650 : i≠650) (h651 : i≠651) (h652 : i≠652) (h670 : i≠670) (h671 : i≠671) :
    ((preparedHead a rp n N rows low W z).stacks i).length ≤ (a.stacks i).length := by
  let b := headResult a n rows low W z
  let c := countResult b
  let d := scatterResult c rp n (selectedHeads n rows low z)
  have hb : (b.stacks i).length ≤ (a.stacks i).length :=
    returned_nonoutput_length_le id (by decide) headInputs headOutputs a _ i
      (by simp [headOutputs,h650,h651])
  have hc : (c.stacks i).length ≤ (b.stacks i).length :=
    returned_nonoutput_length_le countRegs (by decide) countInputs countOutputs b _ i
      (by simp [countOutputs,h652])
  have hd : (d.stacks i).length ≤ (c.stacks i).length :=
    returned_nonoutput_length_le scatterRegs (by decide) scatterInputs scatterOutputs c _ i
      (by simp [scatterOutputs,h670])
  have he : ((factorResult d n N rows W z).stacks i).length ≤ (d.stacks i).length :=
    returned_nonoutput_length_le id (by decide) factorInputs factorOutputs d _ i
      (by simp [factorOutputs,h671])
  exact he.trans (hd.trans (hc.trans hb))

/-- Non-output stacks never grow across reloads, including dirty arithmetic
scratch. This endpoint fact prevents retained storage from compounding across
an exponential number of generator calls. -/
theorem localResult_nonoutput_length_oai (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 768) (h650 : i≠650) (h651 : i≠651) (h652 : i≠652)
    (h668 : i≠668) (h670 : i≠670) (h671 : i≠671) :
    ((localResult a rp rm rs n N W z rows low raw shifted).stacks i).length ≤
      (a.stacks i).length := by
  by_cases h669 : i=669
  · subst i
    simp [localResult,clearState]
  let p := preparedHead a rp n N rows low W z
  let m := returned id (by decide) matrixInputs rawOutputs p
    (LayoutMatrixProgram.finalState (matrixBase p) rm raw)
  have hp := prepare_nonoutput_length a rp n N rows low W z i
    h650 h651 h652 h670 h671
  have hm := returned_nonoutput_length_le id (by decide) matrixInputs rawOutputs
    p (LayoutMatrixProgram.finalState (matrixBase p) rm raw) i
    (by simpa [rawOutputs] using h669)
  have hs := returned_nonoutput_length_le shiftRegs (by decide) shiftInputs shiftOutputs m
    (BucketProgram.preMatrixState rs (m.stacks 141) []
      (Subexp.MatrixProgramSupport.words (shifted.map Subexp.MatrixProgramSupport.words))) i
    (by simpa [shiftOutputs] using h668)
  simpa only [localResult,clearState,Function.update_of_ne h669,p,m] using hs.trans (hm.trans hp)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult_nonoutput_length_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.localResult_nonoutput_length_oai
