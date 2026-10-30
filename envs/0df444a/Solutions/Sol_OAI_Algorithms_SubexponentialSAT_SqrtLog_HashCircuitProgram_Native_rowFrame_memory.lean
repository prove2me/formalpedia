-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.rowFrame_memory
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:21:15.344573+00:00
-- url     : https://prove2.me/submissions/710f120e-e666-4e74-94b7-97e7ddab993c

import Mathlib
import Definitions.Def_OAIQ081S036
import Definitions.Def_OAIQ081S084

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed caller framing for the native sparse-hash interpreter. Low ports
0--55 are reserved for arithmetic. Literal lookup uses 56--62, leaving the
clause, row and constant accumulators physically untouched. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem rowStacks_injective : Function.Injective rowStacks := by decide

/-- All clause/row accumulator stacks are outside the opener's scratch set. -/
theorem rowFrame_stack (base : Machine) (regs : Fin 5 → Bool) (payload clause weight : List Bool)
    (i : Fin 96) (hi : i.val < 56 ∨ 67 ≤ i.val) :
    (rowFrame base regs payload clause weight).stacks i = base.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  fin_cases j <;> simp [rowStacks] at hj <;> subst i <;> omega

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramRowMemory
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact frame for unpacking an inline weighted clause into the two physical
operands used by the clause loop and weighted accumulator. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem rowFrame_memory_oai (regs : Fin 8 → Bool) (low : Fin 56 → List Bool)
    (high : Fin 40 → List Bool) (rr : Fin 5 → Bool) (clause weight : List Bool) :
    let out := rowFrame (Memory.state regs low high) rr [] clause weight
    out = Memory.state out.regs low (openedHigh high clause weight) := by
  dsimp only
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    induction i using (Fin.addCases (m := 56) (n := 40)) with
    | left i =>
      have h := rowFrame_stack (Memory.state regs low high) rr [] clause weight
        (Fin.castAdd 40 i) (Or.inl i.isLt)
      simpa [rowFrame, embedState, Memory.state,Memory.tapes] using h
    | right i =>
      rw [Memory.tapes, Fin.addCases_right]
      have hp (j : Fin 6) := embedState_stack rowRegisters rowStacks (Memory.state regs low high)
        (SubexponentialSAT.SubexpRecordScan.recordState rr [] [] clause [] [] weight) rowStacks_injective j
      have hf (j : Fin 96) (hj : ¬ ∃ k, rowStacks k = j) :=
        embedState_stack_frame rowRegisters rowStacks (Memory.state regs low high)
          (SubexponentialSAT.SubexpRecordScan.recordState rr [] [] clause [] [] weight) j hj
      have hf_high (j : Fin 40) (hj : ¬ ∃ k, rowStacks k = Fin.natAdd 56 j) :
          Function.extend rowStacks
              (SubexponentialSAT.SubexpRecordScan.recordState rr [] [] clause [] [] weight).stacks
              (Memory.state regs low high).stacks (Fin.natAdd 56 j) = high j := by
        calc
          _ = (Memory.state regs low high).stacks (Fin.natAdd 56 j) :=
            hf (Fin.natAdd 56 j) hj
          _ = high j := by simp [Memory.state, Memory.tapes]
      fin_cases i
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (0 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh,rowStacks,
          SubexponentialSAT.SubexpRecordScan.recordState,SubexponentialSAT.SubexpRecordScan.storage]
          using hp 1
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (2 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh,rowStacks,
          SubexponentialSAT.SubexpRecordScan.recordState,SubexponentialSAT.SubexpRecordScan.storage]
          using hp 3
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh,rowStacks,
          SubexponentialSAT.SubexpRecordScan.recordState,SubexponentialSAT.SubexpRecordScan.storage]
          using hp 4
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (5 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (6 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh,rowStacks,
          SubexponentialSAT.SubexpRecordScan.recordState,SubexponentialSAT.SubexpRecordScan.storage]
          using hp 2
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (8 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh,rowStacks,
          SubexponentialSAT.SubexpRecordScan.recordState,SubexponentialSAT.SubexpRecordScan.storage]
          using hp 5
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh,rowStacks,
          SubexponentialSAT.SubexpRecordScan.recordState,SubexponentialSAT.SubexpRecordScan.storage]
          using hp 0
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (11 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (12 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (13 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (14 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (15 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (16 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (17 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (18 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (19 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (20 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (21 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (22 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (23 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (24 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (25 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (26 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (27 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (28 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (29 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (30 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (31 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (32 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (33 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (34 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (35 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (36 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (37 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (38 : Fin 40) (by decide)
      · simpa [rowFrame,embedState,Memory.state,Memory.tapes,Fin.addCases_left,Fin.addCases_right,openedHigh]
          using hf_high (39 : Fin 40) (by decide)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.rowFrame_memory_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.rowFrame_memory_oai
