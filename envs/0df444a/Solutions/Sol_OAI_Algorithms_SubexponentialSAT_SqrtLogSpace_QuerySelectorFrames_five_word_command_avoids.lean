-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames.five_word_command_avoids
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:52:47.461309+00:00
-- url     : https://prove2.me/submissions/a802da12-cc7a-44d3-9cee-d8d441fd3c97

import Mathlib
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryReconstructionReplay_prepare_avoids
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QuerySelectorFrames_pairs_avoids
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryStreamFrames_nodes_avoids

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node-array readout after all finite-difference pairs. The fixed
cleanup pays for transient lower words and clears the old output. Preserved
masters supply the coefficient zero vector and both truncation bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem mem_scratchIndices (i : Fin 40) : i ∈ scratchIndices ↔
    i ≠ 0 ∧ i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 15 ∧ i ≠ 24 ∧ i ≠ 27 ∧
      i ≠ 28 ∧ i ≠ 29 ∧ i ≠ 36 := by
  simp only [scratchIndices, List.mem_filter, List.mem_ofFn, exists_eq,
    decide_eq_true_eq, true_and]

theorem scratchPorts_low {i : Fin 896} (hi : i ∈ scratchPorts) :
    88 ≤ i.val ∧ i.val < 128 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  obtain ⟨h0,h5,h12,h15,h24,h27,h28,h29,h36⟩ := (mem_scratchIndices j).mp hj
  simp only [ports, h0, h5, h12, h15, h24, h27, h28, h29, h36, ite_false]
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplayFootprint
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Compositional certificates for the tape footprint of compiled finite programs. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s l R S L : ℕ}

theorem avoids_transferProgram (H : Fin s → Prop) (src dst : Fin s) (value present : Fin r)
    (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsProgram H (StackRoutines.transferProgram src dst value present) := by
  intro q
  fin_cases q <;> simp [AvoidsInstr,hs,hd]

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeFinishReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete no-read/no-write certificates for the emitted-node tail.
These check the actual finite port maps and calls, including every peek;
the pending caller and accumulated count on320/322 are never inspected. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeFinishReplay

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay

theorem clearMany_avoids (H : Fin 896 → Prop) (ports : List (Fin 896))
    (hp : ∀ i ∈ ports, ¬ H i) : AvoidsCmd H (NodeReadoutSpace.clearMany ports) := by
  induction ports with
  | nil => exact True.intro
  | cons i ports ih =>
      exact ⟨avoids_clearProgram H i 0 1 (hp i (by simp)),
        ih (fun j hj => hp j (by simp [hj]))⟩

/-- The full streamed jet handoff used by recovery avoids the same caller words. -/
theorem handoff_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322) NodeAppendSpace.handoff :=
  ⟨avoids_clearProgram _ 265 0 1 (by decide),
    avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 265 0 1 (by decide) (by decide)⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeFinishReplay
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplayMacros
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Footprints of the fixed storage and scan controllers used by the leaf. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s : ℕ}

theorem avoids_resetMany (H : Fin s → Prop) (ps : List (Fin 16)) :
    AvoidsCmd H (SubexpSetupStorage.resetMany ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨trivial,ih⟩

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryElementaryReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual elementary query commands never inspect the two retained marked
polynomial tapes. These certificates exclude peeks as well as writes. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryElementaryReplay

open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog
open ProgramTapeReplay

private theorem bankClear_avoids {r s : ℕ} (H : Fin s → Prop)
    (tmp : Fin s) (value present : Fin r) (ports : List (Fin s))
    (ht : ¬ H tmp) (hp : ∀ i ∈ ports, ¬ H i) :
    AvoidsCmd H (BankRoutines.clearCmd tmp value present ports) := by
  induction ports with
  | nil => exact avoids_clearProgram H tmp value present ht
  | cons i ports ih =>
    exact ⟨avoids_clearProgram H i value present (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

theorem prepareHigh_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      HighQueryAdapter.prepareHigh := by
  refine ⟨⟨avoids_clearProgram _ _ _ _ (by decide),
    bankClear_avoids _ _ _ _ _ (by decide) (by norm_num [HighQueryAdapter.highChanged, Fin.coe_ofNat_eq_mod])⟩, ?_⟩
  apply avoids_liftProgram_of_range
  intro i
  fin_cases i <;> decide

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryElementaryReplay
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ReconstructionReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual CRT, canonical whole-word reader and paid cleanup never inspect
or modify the marked-record cursor320 or accumulated mass322. This syntactic
certificate supports exact-time replay while the caller still charges their
retained words in every prefix-space bound. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionReplay

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog ProgramTapeReplay

/-- Only the explicit eight scalar-reader ports can be touched. -/
theorem reader_avoids :
    AvoidsCmd (fun i : Fin 330 => i.val = 320 ∨ i.val = 322)
      ReconstructionSpace.canonicalQueryReadCommand := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

/-- Both physical transfers avoid the two persistent collector words. -/
theorem move_avoids :
    AvoidsCmd (fun i : Fin 330 => i.val = 320 ∨ i.val = 322)
      LeafProgram.QueryReadback.moveCommand := by
  exact ⟨avoids_transferProgram _ 261 324 0 1 (by decide) (by decide),
    avoids_transferProgram _ 324 323 0 1 (by decide) (by decide)⟩

theorem query_program_avoids :
    AvoidsProgram (fun i : Fin 330 => i.val = 320 ∨ i.val = 322)
      ReconstructionSpace.canonicalQueryProgram :=
  avoids_compiled _ ReconstructionSpace.canonicalQueryCommand
    ⟨reader_avoids, move_avoids⟩ 261 323

theorem wide_read_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322)
      ReconstructionNative.canonicalWideRead := by
  apply avoids_liftProgram
  exact query_program_avoids

/-- The CRT's entire320-stack bank lies below the collector frame. -/
theorem crt_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322)
      LeafProgram.Count.reconstruct := by
  apply avoids_call_lift_of_range
  intro i
  change ¬(i.val = 320 ∨ i.val = 322)
  omega

theorem cleanup_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322)
      LeafProgram.Count.clearCaches := by
  exact ⟨avoids_clearProgram _ 5 0 1 (by decide),
    avoids_clearProgram _ 10 0 1 (by decide)⟩

theorem command_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322)
      ReconstructionNative.command :=
  ⟨crt_avoids, wide_read_avoids, cleanup_avoids⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionReplay
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReconstructionReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The complete streamed recovery command does not inspect or modify the
marked-record cursor320 or accumulated mass322. This includes the paid jet
handoff, actual scratch preparation, the CRT, canonical reader and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstructionReplay

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay

theorem core_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322)
      QueryReconstruction.coreCommand :=
  ⟨prepare_avoids, ReconstructionReplay.command_avoids⟩

theorem core_lift_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      (liftCommand QueryReconstruction.coreCommand 256 323 id (Fin.castAdd 128)) := by
  apply avoids_liftProgram
  exact avoids_compiled _ _ core_avoids 256 323

theorem command_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      QueryReconstruction.command :=
  ⟨NodeFinishReplay.handoff_avoids, core_lift_avoids⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstructionReplay
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QuerySelectorControlFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual query control commands exclude every read, peek and write in the
retained selector bank768..831. Calls into the original768-stack bank are
covered by their genuine port ranges, independently of their internal code. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorControlFrames

open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog
open ProgramTapeReplay

/-- Every actual instruction of a lifted lower-bank program is disjoint from
the persistent selector interval. -/
theorem lowProgram_avoids {r l : ℕ} (p : Program r 768 l)
    (register : Fin r → Fin 40) :
    AvoidsProgram (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (ProgramLinking.liftProgram p register (Fin.castAdd 128)) := by
  apply avoids_liftProgram_of_range
  intro i hi
  change 768 ≤ i.val ∧ i.val < 832 at hi
  omega

theorem lowCommand_avoids {r : ℕ} (c : Cmd r 768) (input output : Fin 768)
    (register : Fin r → Fin 40) :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (liftCommand c input output register (Fin.castAdd 128)) :=
  lowProgram_avoids (compiled c input output) register

private theorem isolated_avoids {r s l : ℕ}
    (p : Program r s l) (register : Fin r → Fin 16) (stack : Fin s → Fin 896)
    (tmp : Fin 896) (ports : List (Fin 896)) (inputs outputs : List (Fin 896 × Fin 896))
    (ht : ¬ (768 ≤ tmp.val ∧ tmp.val < 832))
    (hp : ∀ i ∈ ports, ¬ (768 ≤ i.val ∧ i.val < 832))
    (hi : ∀ q ∈ inputs, ¬ (768 ≤ q.1.val ∧ q.1.val < 832) ∧
      ¬ (768 ≤ q.2.val ∧ q.2.val < 832))
    (ho : ∀ q ∈ outputs, ¬ (768 ≤ q.1.val ∧ q.1.val < 832) ∧
      ¬ (768 ≤ q.2.val ∧ q.2.val < 832))
    (hs : ∀ i, ¬ (768 ≤ (stack i).val ∧ (stack i).val < 832)) :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (isolated p register stack tmp ports inputs outputs) := by
  refine ⟨?_, avoids_liftProgram_of_range _ p register stack hs, ?_⟩
  · exact ⟨avoids_clearMany _ [tmp] (by simpa using ht),
      avoids_clearMany _ ports hp, avoids_resetMany _ workRegisters,
      avoids_copyMany _ tmp inputs ht hi⟩
  · refine ⟨avoids_clearMany _ (outputs.map Prod.snd) ?_,
      avoids_copyMany _ tmp outputs ht ho, avoids_clearMany _ ports hp,
      avoids_resetMany _ workRegisters⟩
    intro i h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    exact (ho q hq).2

private theorem bankClear_avoids {r : ℕ} (tmp : Fin 896)
    (value present : Fin r) (ports : List (Fin 896))
    (ht : ¬ (768 ≤ tmp.val ∧ tmp.val < 832))
    (hp : ∀ i ∈ ports, ¬ (768 ≤ i.val ∧ i.val < 832)) :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (BankRoutines.clearCmd tmp value present ports) := by
  induction ports with
  | nil => exact avoids_clearProgram _ tmp value present ht
  | cons i ports ih =>
    exact ⟨avoids_clearProgram _ i value present (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

theorem countCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      PairNativeSetup.countCommand := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · intro i
    fin_cases i <;> decide

theorem setupCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      PairNativeSetup.setupCommand :=
  ⟨countCommand_avoids, avoids_clearMany _ _ (by norm_num [Fin.coe_ofNat_eq_mod]),
    avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide)⟩

theorem setupCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      PairNativeSetup.setupCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ setupCommand_avoids _ _)

theorem prepareHigh_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      HighQueryAdapter.prepareHigh := by
  refine ⟨⟨avoids_clearProgram _ _ _ _ (by decide),
    bankClear_avoids _ _ _ _ (by decide)
      (by norm_num [HighQueryAdapter.highChanged, Fin.coe_ofNat_eq_mod])⟩, ?_⟩
  apply avoids_liftProgram_of_range
  intro i
  fin_cases i <;> decide

theorem nativeLayoutLoad_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NativeLayoutLoad.command := by
  constructor
  · apply avoids_liftProgram
    apply avoids_compiled
    apply avoids_clearMany
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
      change ¬ (768 ≤ j.val ∧ j.val < 832)
      omega
  · exact lowCommand_avoids _ _ _ _

theorem initializeNodes_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryAssembler.Nodes.initializeNodes := by
  refine ⟨lowCommand_avoids _ _ _ _, NodeFinishReplay.clearMany_avoids _ _ ?_⟩
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> decide

theorem beginNode_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryAssembler.Nodes.beginNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, lowCommand_avoids _ _ _ _⟩
  intro i hi
  simp only [QueryAssembler.Nodes.nodeResetPorts, List.mem_cons, List.mem_nil_iff,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem readout_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeReadoutSpace.command := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    rcases List.mem_cons.mp hi with hi | hi
    · subst i
      decide
    · have hs := NodeReadoutSpace.scratchPorts_low hi
      omega
  · apply avoids_call_lift_of_range
    intro i
    fin_cases i <;> decide

/-- The exact paid scalar-cache copies are also used by the tuple-sum visitor. -/
theorem nodeAppendPrepare_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.prepare := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  · exact ⟨avoids_copyProgram _ 194 5 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 202 12 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 204 39 89 0 1 (by decide) (by decide) (by decide)⟩

theorem append_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.append :=
  ⟨avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 862 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 863 0 1 (by decide) (by decide)⟩

theorem nodeAppend_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.command :=
  ⟨nodeAppendPrepare_avoids, readout_avoids, append_avoids⟩

theorem finishNode_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryNodeFinish.finishNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ⟨⟨True.intro, ?_⟩, ?_⟩⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl <;> decide
  · change ¬ (768 ≤ (307 : Fin 896).val ∧ (307 : Fin 896).val < 832)
    decide
  · change ¬ (768 ≤ (301 : Fin 896).val ∧ (301 : Fin 896).val < 832)
    decide

theorem nodeFinish_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryNodeFinish.command := ⟨nodeAppend_avoids, finishNode_avoids⟩

theorem handoff_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.handoff :=
  ⟨avoids_clearProgram _ 265 0 1 (by decide),
    avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 265 0 1 (by decide) (by decide)⟩

theorem reconstruction_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryReconstruction.command := ⟨handoff_avoids, lowCommand_avoids _ _ _ _⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorControlFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Syntactic read and write exclusion for the actual streaming query.
The collector's remaining records and accumulated count stay opaque to the
conditioned query, so replay after changing those words uses the same steps. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

local notation "H" => (fun i : Fin 896 => Fin.val i = 320 ∨ Fin.val i = 322)

/-- Every instruction of the one fixed conditioned query excludes both
outer collector tapes, including all peeks and called instruction tables. -/
theorem command_avoids : AvoidsCmd H QueryStreamProgram.command :=
  ⟨QueryElementaryReplay.prepareHigh_avoids, nodes_avoids,
    QueryReconstructionReplay.command_avoids⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QuerySelectorFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The conditioned query also excludes the entire retained selector bank.
This accounts for arbitrary incumbent and remaining-round words in the
actual greedy callback's time quantifiers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

local notation "H" => (fun i : Fin 896 => 768 ≤ Fin.val i ∧ Fin.val i ≤ 831)


private theorem instr_five {r s l : ℕ} (c : Instr r s l)
    (hc : AvoidsInstr (fun i : Fin s => i.val=320 ∨ i.val=322) c)
    (hs : AvoidsInstr (fun i : Fin s => 768 ≤ i.val ∧ i.val ≤ 831) c) :
    AvoidsInstr (fun i : Fin s => i.val=320 ∨ i.val=322 ∨ i.val=770 ∨ i.val=771 ∨ i.val=781) c := by
  cases c <;> simp only [AvoidsInstr] at * <;>
    first | exact True.intro | omega

private theorem base_five {r s : ℕ} (c : StructuredProgram.Cmd r s)
    (hc : AvoidsBase (fun i : Fin s => i.val=320 ∨ i.val=322) c)
    (hs : AvoidsBase (fun i : Fin s => 768 ≤ i.val ∧ i.val ≤ 831) c) :
    AvoidsBase (fun i : Fin s => i.val=320 ∨ i.val=322 ∨ i.val=770 ∨ i.val=771 ∨ i.val=781) c := by
  induction c with
  | skip => exact True.intro
  | atom a =>
    cases a <;> simp only [AvoidsBase, AvoidsAtom] at * <;>
      first | exact True.intro | omega
  | seq a b ha hb => exact ⟨ha hc.1 hs.1, hb hc.2 hs.2⟩
  | ite i a b ha hb => exact ⟨ha hc.1 hs.1, hb hc.2 hs.2⟩
  | «while» i a ha => exact ha hc hs

private theorem command_five {r s : ℕ} (c : Cmd r s)
    (hc : AvoidsCmd (fun i : Fin s => i.val=320 ∨ i.val=322) c)
    (hs : AvoidsCmd (fun i : Fin s => 768 ≤ i.val ∧ i.val ≤ 831) c) :
    AvoidsCmd (fun i : Fin s => i.val=320 ∨ i.val=322 ∨ i.val=770 ∨ i.val=771 ∨ i.val=781) c := by
  induction c with
  | base a => exact base_five a hc hs
  | call p => exact fun q => instr_five (p.code q) (hc q) (hs q)
  | seq a b ha hb => exact ⟨ha hc.1 hs.1, hb hc.2 hs.2⟩
  | ite i a b ha hb => exact ⟨ha hc.1 hs.1, hb hc.2 hs.2⟩
  | «while» i a ha => exact ha hc hs

open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem lower_avoids {r l : ℕ} (p : Program r 768 l) (reg : Fin r → Fin 40) :
    AvoidsProgram (fun i : Fin 896 => 768 ≤ i.val ∧ i.val ≤ 831)
      (ProgramLinking.liftProgram p reg SignatureHeadLoader.lowStacks) := by
  apply avoids_liftProgram_of_range
  intro i hi
  have hv := i.isLt
  change 768 ≤ i.val ∧ i.val ≤ 831 at hi
  omega


private theorem interval_convert {c : Cmd 40 896}
    (h : AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832) c) :
    AvoidsCmd H c := by simpa only [Nat.lt_succ_iff] using h


theorem bootstrap_avoids : AvoidsCmd H QueryStreamProgram.bootstrapNode :=
  lower_avoids SignatureHeadLoader.bootstrapProgram SignatureHeadLoader.leafRegs

theorem node_body_avoids : AvoidsCmd H QueryStreamProgram.nodeBody :=
  ⟨interval_convert QuerySelectorControlFrames.beginNode_avoids,
    interval_convert QuerySelectorControlFrames.nativeLayoutLoad_avoids, bootstrap_avoids,
    interval_convert QuerySelectorControlFrames.setupCaller_avoids, pairs_avoids,
    interval_convert QuerySelectorControlFrames.nodeFinish_avoids⟩

theorem nodes_avoids : AvoidsCmd H QueryStreamProgram.nodes := by
  refine ⟨interval_convert QuerySelectorControlFrames.initializeNodes_avoids, ?_, node_body_avoids⟩
  change ¬ H 301
  decide

/-- The actual fixed conditioned query excludes the whole retained selector
bank, including every invoked table and every peek. -/
theorem command_avoids : AvoidsCmd H QueryStreamProgram.command :=
  ⟨interval_convert QuerySelectorControlFrames.prepareHigh_avoids, nodes_avoids,
    interval_convert QuerySelectorControlFrames.reconstruction_avoids⟩

local notation "K" => (fun i : Fin 896 => Fin.val i=320 ∨ Fin.val i=322 ∨
  Fin.val i=770 ∨ Fin.val i=771 ∨ Fin.val i=781)

/-- All five unconstrained words in the concrete greedy query-time binder
are excluded from the fixed conditioned query's actual instruction stream. -/
theorem five_word_command_avoids_oai : AvoidsCmd K QueryStreamProgram.command :=
  command_five _ QueryStreamFrames.command_avoids command_avoids

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames.five_word_command_avoids_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames.five_word_command_avoids_oai
