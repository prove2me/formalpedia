-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.nodes_avoids
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:44:46.293328+00:00
-- url     : https://prove2.me/submissions/a44aa547-f956-4d08-8475-7c33fbef9993

import Mathlib
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryStreamFrames_pairs_avoids

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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

theorem readout_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322) NodeReadoutSpace.command := by
  refine ⟨clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    rcases List.mem_cons.mp hi with hi | hi
    · subst i
      decide
    · have hs := NodeReadoutSpace.scratchPorts_low hi
      omega
  · apply avoids_call_lift_of_range
    intro i
    fin_cases i <;> decide

theorem prepare_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322) NodeAppendSpace.prepare := by
  refine ⟨clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  ·
    exact ⟨avoids_copyProgram _ 194 5 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 202 12 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 204 39 89 0 1 (by decide) (by decide) (by decide)⟩

theorem append_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322) NodeAppendSpace.append :=
  ⟨avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 862 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 863 0 1 (by decide) (by decide)⟩

theorem nodeAppend_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322) NodeAppendSpace.command :=
  ⟨prepare_avoids, readout_avoids, append_avoids⟩

theorem finishNode_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322) QueryNodeFinish.finishNode := by
  refine ⟨clearMany_avoids _ _ ?_, ⟨⟨True.intro, ?_⟩, ?_⟩⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl <;> decide
  · change ¬ ((307 : Fin 896).val = 320 ∨ (307 : Fin 896).val = 322)
    decide
  · change ¬ ((301 : Fin 896).val = 320 ∨ (301 : Fin 896).val = 322)
    decide

theorem command_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322) QueryNodeFinish.command :=
  ⟨nodeAppend_avoids, finishNode_avoids⟩

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

theorem avoids_record_reader (H : Fin s → Prop) (p : RecordPrograms.Ports r s)
    (hs : ¬ H p.source) (hp : ¬ H p.payload) : AvoidsCmd H (RecordPrograms.reader p) := by
  apply avoids_call_lift_of_range
  intro i
  unfold RecordPrograms.stackMap
  split <;> assumption

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeCursorReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node-cursor initialization and frame parsing never read or write
the external marked-record cursor320 or accumulated mass322. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeCursorReplay

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay

theorem native_init_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322) RingNodeSetup.initNodes :=
  ⟨avoids_clearProgram _ 301 0 1 (by decide),
    avoids_clearProgram _ 302 0 1 (by decide),
    avoids_clearProgram _ 305 0 1 (by decide),
    avoids_clearProgram _ 307 0 1 (by decide),
    avoids_clearProgram _ 78 0 1 (by decide),
    avoids_copyProgram _ 300 301 305 0 1 (by decide) (by decide) (by decide)⟩

theorem native_read_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322) RingNodeSetup.readNode := by
  refine ⟨?_, avoids_record_reader _ SqrtLog.LeafNodeSamplesProgram.ports
    (by decide) (by decide), avoids_transferProgram _ 302 78 0 1 (by decide) (by decide)⟩
  change ¬ ((301 : Fin 768).val = 320 ∨ (301 : Fin 768).val = 322)
  decide

theorem call_avoids (command : Cmd 40 768)
    (hc : AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322) command) :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      (QueryAssembler.Nodes.call command) := by
  apply avoids_liftProgram
  exact avoids_compiled _ command hc 301 78

theorem initializeNodes_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      QueryAssembler.Nodes.initializeNodes := by
  refine ⟨call_avoids _ native_init_avoids, NodeFinishReplay.clearMany_avoids _ _ ?_⟩
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> decide

theorem beginNode_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      QueryAssembler.Nodes.beginNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, call_avoids _ native_read_avoids⟩
  intro i hi
  simp only [QueryAssembler.Nodes.nodeResetPorts, List.mem_cons, List.mem_nil_iff,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeCursorReplay
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

private theorem isolated_avoids {r s l S : ℕ} (H : Fin S → Prop)
    (p : Program r s l) (register : Fin r → Fin 16) (stack : Fin s → Fin S)
    (tmp : Fin S) (ports : List (Fin S)) (inputs outputs : List (Fin S × Fin S))
    (ht : ¬ H tmp) (hp : ∀ i ∈ ports, ¬ H i)
    (hi : ∀ q ∈ inputs, ¬ H q.1 ∧ ¬ H q.2)
    (ho : ∀ q ∈ outputs, ¬ H q.1 ∧ ¬ H q.2)
    (hs : ∀ i, ¬ H (stack i)) :
    AvoidsCmd H (isolated p register stack tmp ports inputs outputs) := by
  refine ⟨?_, avoids_liftProgram_of_range H p register stack hs, ?_⟩
  · exact ⟨avoids_clearMany H [tmp] (by simpa using ht),
      avoids_clearMany H ports hp, avoids_resetMany H workRegisters,
      avoids_copyMany H tmp inputs ht hi⟩
  · refine ⟨avoids_clearMany H (outputs.map Prod.snd) ?_,
      avoids_copyMany H tmp outputs ht ho, avoids_clearMany H ports hp,
      avoids_resetMany H workRegisters⟩
    intro i h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    exact (ho q hq).2

/-- The paid unary false-count setup reads only its real local bank and
explicit copies; the marked polynomial tapes are absent from all accesses. -/
theorem countCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      PairNativeSetup.countCommand := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · intro i
    fin_cases i <;> decide

theorem setupCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      PairNativeSetup.setupCommand :=
  ⟨countCommand_avoids, avoids_clearMany _ _ (by norm_num [Fin.coe_ofNat_eq_mod]),
    avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide)⟩

theorem setupCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      PairNativeSetup.setupCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ setupCommand_avoids _ _)

/-- The original fourteen-copy loader uses only its real parked sources,
low destinations, and temporary684. -/
theorem layoutMasters_load_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val=320 ∨ i.val=322)
      LeafProgram.LayoutMasters.load := by
  apply avoids_liftProgram
  apply avoids_compiled
  apply avoids_copyMany
  · decide
  · intro q hq
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hq
    change ¬ (730+i.val=320 ∨ 730+i.val=322) ∧
      ¬ (128+i.val=320 ∨ 128+i.val=322)
    constructor <;> omega

/-- The literal paid loader command uses only its cleared workspace and the
original fourteen source/destination copies. -/
theorem layout_command_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      (.seq
        (liftCommand
          (clearMany (([684,660,665] : List (Fin 896)) ++
            LeafProgram.LayoutMasters.lowPorts.map (Fin.castAdd 128)))
          730 128 (Fin.castAdd 24) id)
        (liftCommand LeafProgram.LayoutMasters.load 730 128 id (Fin.castAdd 128))) := by
  constructor
  · apply avoids_liftProgram
    apply avoids_compiled
    apply avoids_clearMany
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl <;> decide
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
      obtain ⟨k,_,rfl⟩ := List.mem_map.mp hj
      change ¬ (128+k.val=320 ∨ 128+k.val=322)
      omega
  · exact avoids_liftProgram _ _ _ _
      (avoids_compiled _ _ layoutMasters_load_avoids _ _)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryElementaryReplay
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureLoaderReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual bootstrap and head loader never inspect the two retained
collector tapes. This syntactic certificate includes peeks and all calls. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureLoaderReplay
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay

private theorem copyMany_avoids {s : ℕ} (H : Fin s → Prop) (tmp : Fin s)
    (ps : List (Fin s × Fin s)) (ht : ¬ H tmp)
    (hp : ∀ p∈ps,¬ H p.1 ∧ ¬ H p.2) : AvoidsCmd H (copyMany tmp ps) := by
  induction ps with
  | nil => exact True.intro
  | cons p ps ih =>
    exact ⟨avoids_copyProgram H p.1 p.2 tmp 0 1 (hp p (by simp)).1
      (hp p (by simp)).2 ht,ih (fun q hq=>hp q (by simp [hq]))⟩

private theorem clearMany_avoids {s : ℕ} (H : Fin s → Prop) (ps : List (Fin s))
    (hp : ∀ p∈ps,¬ H p) : AvoidsCmd H (clearMany ps) := by
  induction ps with
  | nil => exact True.intro
  | cons p ps ih =>
    exact ⟨avoids_clearProgram H p 0 1 (hp p (by simp)),ih (fun q hq=>hp q (by simp [hq]))⟩

private theorem resetMany_avoids {s : ℕ} (H : Fin s → Prop) (rs : List (Fin 16)) :
    AvoidsCmd H (resetMany (S:=s) rs) := by
  induction rs with
  | nil => exact True.intro
  | cons r rs ih => exact ⟨True.intro,ih⟩

private theorem prepare_avoids {s : ℕ} (H : Fin s → Prop) (tmp : Fin s)
    (ps : List (Fin s)) (ins : List (Fin s × Fin s))
    (ht : ¬ H tmp) (hp : ∀ p∈ps,¬ H p) (hi : ∀ p∈ins,¬ H p.1 ∧ ¬ H p.2) :
    AvoidsCmd H (prepare tmp ps ins) :=
  ⟨clearMany_avoids H [tmp] (by simpa using ht),clearMany_avoids H ps hp,
    resetMany_avoids H workRegisters,copyMany_avoids H tmp ins ht hi⟩

private theorem finish_avoids {s : ℕ} (H : Fin s → Prop) (tmp : Fin s)
    (ps : List (Fin s)) (outs : List (Fin s × Fin s))
    (ht : ¬ H tmp) (hp : ∀ p∈ps,¬ H p) (ho : ∀ p∈outs,¬ H p.1 ∧ ¬ H p.2) :
    AvoidsCmd H (finish tmp ps outs) := by
  refine ⟨clearMany_avoids H (outs.map Prod.snd) ?_,copyMany_avoids H tmp outs ht ho,
    clearMany_avoids H ps hp,resetMany_avoids H workRegisters⟩
  intro q hq
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
  exact (ho p hp).2

private theorem work_avoids {s : ℕ} (hs : s≤288) (i : Fin s) :
    ¬ (workPort hs i=320 ∨ workPort hs i=322) := by
  intro h
  rcases h with h|h <;> have hv := congrArg Fin.val h <;>
    simp only [workPort,Fin.coe_ofNat_eq_mod,Nat.reduceMod] at hv <;> omega

private theorem stage_avoids {r s l : ℕ} (p : Program r s l) (reg : Fin r → Fin 16)
    (hs : s≤288) (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (hi : ∀ q∈ins,¬ (q.1=320 ∨ q.1=322))
    (ho : ∀ q∈outs,¬ (q.2=320 ∨ q.2=322)) :
    AvoidsCmd (fun i : Fin 768=>i=320 ∨ i=322) (stage p reg hs ins outs) := by
  let H := fun i : Fin 768=>i=320 ∨ i=322
  have ht : ¬ H temporary := by decide
  have hw : ∀ i∈workPorts hs,¬ H i := by
    intro i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    exact work_avoids hs j
  have hin : ∀ q∈inputCopies hs ins,¬ H q.1 ∧ ¬ H q.2 := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    exact ⟨hi z hz,work_avoids hs z.2⟩
  have hout : ∀ q∈outputCopies hs outs,¬ H q.1 ∧ ¬ H q.2 := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    exact ⟨work_avoids hs z.1,ho z hz⟩
  exact ⟨prepare_avoids H temporary (workPorts hs) (inputCopies hs ins) ht hw hin,
    avoids_liftProgram_of_range H p reg (workPort hs) (work_avoids hs),
    finish_avoids H temporary (workPorts hs) (outputCopies hs outs) ht hw hout⟩

theorem bootstrap_avoids :
    AvoidsProgram (fun i : Fin 768=>i=320 ∨ i=322) SignatureHeadLoader.bootstrapProgram := by
  apply avoids_compiled
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · exact stage_avoids _ _ _ _ _ (by simp [addressInputs]) (by simp [addressOutputs])
  · exact stage_avoids _ _ _ _ _ (by simp [rowCountInputs]) (by simp [rowCountOutputs])
  · exact stage_avoids _ _ _ _ _ (by simp [cacheInputs]) (by simp [cacheOutputs])
  · exact clearMany_avoids _ retainedPorts (by simp [retainedPorts])
  · exact copyMany_avoids _ temporary retainedCopies (by decide) (by simp [retainedCopies])

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureLoaderReplay
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

theorem layout_load_avoids : AvoidsCmd H NativeLayoutLoad.command :=
  QueryElementaryReplay.layout_command_avoids

theorem bootstrap_avoids : AvoidsCmd H QueryStreamProgram.bootstrapNode := by
  apply avoids_liftProgram
  simpa only [Function.comp_def, QueryAssembler.Nodes.lowPort, Fin.val_castAdd,
    Fin.ext_iff, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using
    SignatureLoaderReplay.bootstrap_avoids

theorem node_body_avoids : AvoidsCmd H QueryStreamProgram.nodeBody :=
  ⟨NodeCursorReplay.beginNode_avoids, layout_load_avoids, bootstrap_avoids,
    QueryElementaryReplay.setupCaller_avoids, pairs_avoids, NodeFinishReplay.command_avoids⟩

theorem nodes_avoids_oai : AvoidsCmd H QueryStreamProgram.nodes := by
  refine ⟨NodeCursorReplay.initializeNodes_avoids, ?_, node_body_avoids⟩
  change ¬ H 301
  decide

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.nodes_avoids_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.nodes_avoids_oai
