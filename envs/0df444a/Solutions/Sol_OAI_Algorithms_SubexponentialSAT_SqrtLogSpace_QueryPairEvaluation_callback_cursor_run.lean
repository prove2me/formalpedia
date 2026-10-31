-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_cursor_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:48:23.078191+00:00
-- url     : https://prove2.me/submissions/ce76d65b-f131-49b7-8c62-03344c614207

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation_callback_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem basePort_high (i : Fin 768) :
    (basePort i).val < 768 ∨ (885 ≤ (basePort i).val ∧ (basePort i).val ≤ 892) := by
  simp only [basePort]
  split_ifs <;> simp_all only [Fin.val_castAdd, Fin.coe_ofNat_eq_mod] <;> omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head-sum assembly. The first head gate receives a physically
cleared arithmetic bank; persistent source parameters remain outside that bank.
Accepted assignments continue through dense addition and workspace reclamation,
including empty factor products and zero-valued products. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly

open OAI BitProgram StructuredCalls StackRoutines
open HeadEvaluationProgram.StagedGate

private theorem workPorts_eq :
    workPorts = List.ofFn (fun i : Fin 56 => i.castAdd 840) ++ controllerPorts :=
  workPortsData.2

theorem mem_workPorts (i : Fin 896) :
    i ∈ workPorts ↔ i.val < 56 ∨ i ∈ controllerPorts := by
  rw [workPorts_eq]
  simp only [List.mem_append]
  apply or_congr_left
  constructor
  · intro hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    exact j.isLt
  · intro hi
    exact List.mem_ofFn.mpr ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeFinishReplay
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryAssembler
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical assembly of the streamed query. Arithmetic caches are installed
from retained produced words by paid finite commands. These local theorems do
not assert completion of the node, pair, or tuple evaluator. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem low_mem (i : Fin 896) :
    i∈(List.finRange 56).map (Fin.castAdd 840) ↔ i.val<56 := by
  constructor
  · intro h
    obtain ⟨j,_,hj⟩ := List.mem_map.mp h
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    omega
  · intro h
    exact List.mem_map.mpr ⟨⟨i.val,h⟩,List.mem_finRange _,Fin.ext rfl⟩

private theorem normalize_mem (i : Fin 896) :
    i∈(List.finRange 28).map (fun j => (⟨100+j.val,by omega⟩ : Fin 896)) ↔
      100 ≤ i.val ∧ i.val<128 := by
  constructor
  · intro h
    obtain ⟨j,_,hj⟩ := List.mem_map.mp h
    have hv := congrArg Fin.val hj
    change 100+j.val=i.val at hv
    omega
  · intro h
    refine List.mem_map.mpr ⟨⟨i.val-100,by omega⟩,List.mem_finRange _,?_⟩
    apply Fin.ext
    dsimp
    omega

theorem pairScratch_mem (i : Fin 896) : i∈pairScratch ↔
    i.val<56 ∨ (100 ≤ i.val ∧ i.val<128) ∨ i=159 ∨ i=841 ∨ i=848 ∨ i=849 := by
  simp [pairScratch,low_mem,normalize_mem]

open SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram
open TruncatedRingProgram


/-! The interpolation-node cursor is the actual framed table emitted by the
ring producer. Its low-bank loader is embedded into the common leaf bank;
all high pair/tuple state is preserved by the injective port map. -/


/-! Native multiplication of one completed head sum into the tuple product.
The original accumulator is relocated only at its two persistent operands. -/

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of one attained-signature tuple product. The
multiplicative identity is built by the native cache routine, and every stale
output and borrowed word is cleared by an actual command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram

theorem mem_lowPorts (i : Fin 896) : i ∈ lowPorts ↔ i.val < 56 := by
  constructor
  · intro hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    exact j.isLt
  · intro hi
    exact List.mem_ofFn.mpr ⟨⟨i.val, hi⟩, Fin.ext rfl⟩


open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleSum
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete unsigned tuple accumulation. The complete head product on852
is normalized into the pair accumulator851. Physical caches are copied from
retained masters and every native peripheral scratch word is paid for. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem mem_scratchIndices (i : Fin 28) : i ∈ scratchIndices ↔
    i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 24 ∧ i ≠ 15 ∧ i ≠ 27 := by
  simp only [scratchIndices,List.mem_filter,List.mem_ofFn,exists_eq,
    decide_eq_true_eq,true_and]

theorem scratchPorts_low {i : Fin 896} (hi : i ∈ scratchPorts) :
    100 ≤ i.val ∧ i.val < 128 := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  obtain ⟨h5,h12,h24,h15,h27⟩ := (mem_scratchIndices j).mp hj
  simp only [ports,h5,h12,h24,h15,h27,ite_false]
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairCommit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The signed finite-difference term is committed to the actual node word.
The pair product and the node sum use the same stored dictionaries as their
validity and readout witnesses. Marker readout remains additive. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram
open TruncatedRingProgram QueryProgram QueryTupleState

namespace NodeAccumulatorMeaning

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {value : Truncated (q.p.model.O q.p.t) q.J} {a b : Data}
    (h : NodeAccumulatorMeaning q value a) (hf : b.stacks 850=a.stacks 850) :
    NodeAccumulatorMeaning q value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end NodeAccumulatorMeaning

open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit
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

theorem avoids_liftCommand_of_range {R S : ℕ} (H : Fin S → Prop)
    (c : Cmd r s) (input output : Fin s) (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (h : ∀ i, ¬ H (stack i)) :
    AvoidsCmd H (liftCommand c input output register stack) :=
  avoids_call_lift_of_range H _ register stack h

theorem avoids_resetMany (H : Fin s → Prop) (ps : List (Fin 16)) :
    AvoidsCmd H (SubexpSetupStorage.resetMany ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨trivial,ih⟩

theorem avoids_forCmd (H : Fin s → Prop) (p : UnaryForPrograms.Ports r s)
    (body : Cmd r s) (hp : ¬ H p.counter) (hb : AvoidsCmd H body) :
    AvoidsCmd H (UnaryForPrograms.forCmd p body) := ⟨hp,hb,hp⟩

theorem avoids_record_reader (H : Fin s → Prop) (p : RecordPrograms.Ports r s)
    (hs : ¬ H p.source) (hp : ¬ H p.payload) : AvoidsCmd H (RecordPrograms.reader p) := by
  apply avoids_call_lift_of_range
  intro i
  unfold RecordPrograms.stackMap
  split <;> assumption

theorem avoids_record_iterate (H : Fin s → Prop) (p : RecordPrograms.Ports r s)
    (body : Cmd r s) (hs : ¬ H p.source) (hp : ¬ H p.payload)
    (hb : AvoidsCmd H body) : AvoidsCmd H (RecordPrograms.iterate p body) :=
  ⟨trivial,hs,avoids_record_reader H p hs hp,hb,trivial,hs⟩

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadPrepareFootprint
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual key and paid head preparation never inspect or modify the
pending caller word320 or accumulated count322, including through peeks. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepareFootprint

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open HighQueryAdapter

theorem bank_clear_avoids {r s : ℕ} (H : Fin s → Prop) (tmp : Fin s)
    (value present : Fin r) (ports : List (Fin s)) (ht : ¬ H tmp)
    (hp : ∀ i ∈ ports, ¬ H i) :
    AvoidsCmd H (BankRoutines.clearCmd tmp value present ports) := by
  induction ports with
  | nil => exact avoids_clearProgram H tmp value present ht
  | cons i ports ih =>
      exact ⟨avoids_clearProgram H i value present (hp i (by simp)),
        ih (fun j hj => hp j (by simp [hj]))⟩

theorem overwrite_avoids (H : Fin 896 → Prop) (src dst : Fin 896)
    (hs : ¬ H src) (hd : ¬ H dst) (ht : ¬ H 841) :
    AvoidsCmd H (QueryTupleVisitor.overwrite src dst) :=
  ⟨avoids_clearProgram H dst 0 1 hd, avoids_copyProgram H src dst 841 0 1 hs hd ht⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepareFootprint
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairControlFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual emitted-pair callback excludes reads, peeks and writes on832/833.
The mask words834/835 remain real callback inputs. This certificate does not
cover the enclosing pair controller, which operates on its own traversal words. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame.Factor
open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SqrtLog SqrtLog.LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

local notation "H" => (fun i : Fin 896 => (Fin.val i = 832 ∨ Fin.val i = 833))

theorem low_port (i : Fin 768) : ¬ H (FactorAssignmentProgram.lowStack i) := by
  change ¬ ((i.val = 832 ∨ i.val = 833))
  omega

theorem setup_avoids : AvoidsCmd H FactorAssignmentProgram.setup :=
  avoids_liftCommand_of_range H _ _ _ _ _ low_port

private theorem lift_low_avoids (c : Cmd 40 768) (input output : Fin 768) :
    AvoidsCmd H (FactorAssignmentProgram.liftLow c input output) :=
  avoids_liftCommand_of_range H _ _ _ _ _ low_port

namespace Table
open FactorTableProgram

theorem base_port (i : Fin 768) : ¬ H (basePort i) := by
  have hi := basePort_high i
  omega

theorem lift_base_avoids (c : Cmd 16 768) : AvoidsCmd H (liftBase c) :=
  avoids_liftCommand_of_range H _ _ _ _ _ base_port

theorem inner_avoids (c : Cmd 16 256) : AvoidsCmd H (liftInner c) := by
  apply avoids_liftCommand_of_range
  intro i
  change ¬ ((340+i.val = 832 ∨ 340+i.val = 833))
  omega

theorem specialize_avoids : AvoidsCmd H specializeCall := by
  refine ⟨avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide), ?_⟩
  apply avoids_liftCommand_of_range
  intro i
  change ¬ ((340+i.val = 832 ∨ 340+i.val = 833))
  omega

theorem low_payload_avoids : AvoidsCmd H lowPayload :=
  ⟨lift_base_avoids _, specialize_avoids⟩

theorem literal_payload_avoids : AvoidsCmd H literalPayload :=
  ⟨inner_avoids _, inner_avoids _, low_payload_avoids⟩

theorem literal_iteration_avoids : AvoidsCmd H literalIteration :=
  ⟨inner_avoids _, literal_payload_avoids, inner_avoids _⟩

theorem prepare_factor_avoids : AvoidsCmd H prepareFactor :=
  ⟨inner_avoids _, avoids_forCmd _ _ _ (by decide) literal_iteration_avoids,
    inner_avoids _⟩

theorem entry_ports_avoid : ∀ i ∈ entryPorts, ¬ H i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact base_port j
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem entry_avoids : AvoidsCmd H initializeWorker :=
  avoids_clearMany H _ entry_ports_avoid

theorem command_avoids : AvoidsCmd H command :=
  ⟨entry_avoids, lift_base_avoids _, prepare_factor_avoids, lift_base_avoids _⟩

theorem program_avoids : AvoidsProgram H program :=
  avoids_compiled H _ command_avoids _ _

theorem caller_avoids : AvoidsCmd H caller :=
  avoids_liftProgram H _ _ _ program_avoids
end Table

private theorem prepare_incidence_avoids :
    AvoidsCmd H FactorAssignmentProgram.prepareIncidence :=
  ⟨lift_low_avoids _ _ _, Table.caller_avoids⟩

private theorem choose_avoids : AvoidsCmd H FactorAssignmentProgram.choose :=
  ⟨⟨prepare_incidence_avoids, lift_low_avoids _ _ _⟩,
    ⟨prepare_incidence_avoids, lift_low_avoids _ _ _⟩, True.intro⟩

private theorem copy_avoids (src dst : Fin 896) (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (FactorAssignmentProgram.copy src dst) :=
  avoids_copyProgram H src dst 159 0 1 hs hd (by decide)

private theorem clear_avoids (src : Fin 896) (hs : ¬ H src) :
    AvoidsCmd H (FactorAssignmentProgram.clear src) :=
  avoids_clearProgram H src 0 1 hs

private theorem move_avoids (src dst : Fin 896) (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (FactorAssignmentProgram.move src dst) :=
  ⟨copy_avoids src dst hs hd, clear_avoids src hs⟩

theorem callback_avoids : AvoidsCmd H FactorAssignmentProgram.callback :=
  ⟨avoids_liftCommand_of_range H _ _ _ _ _ low_port,
    lift_low_avoids _ _ _, choose_avoids, clear_avoids _ (by decide),
    True.intro, True.intro, True.intro⟩

private theorem loop_avoids : AvoidsCmd H FactorAssignmentProgram.loop :=
  avoids_record_iterate H FactorAssignmentProgram.ports FactorAssignmentProgram.callback
    (by decide) (by decide) callback_avoids

private theorem product_avoids : AvoidsCmd H FactorAssignmentProgram.product :=
  ⟨copy_avoids _ _ (by decide) (by decide), copy_avoids _ _ (by decide) (by decide),
    loop_avoids, move_avoids _ _ (by decide) (by decide)⟩

private theorem entry_scratch_avoids :
    ∀ i ∈ FactorAssignmentProgram.entryScratch, ¬ H i := by
  intro i hi
  simp only [FactorAssignmentProgram.entryScratch, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact low_port j
  · exact Table.entry_ports_avoid i hi

private theorem initialize_avoids : AvoidsCmd H FactorAssignmentProgram.initialize_ := by
  apply avoids_liftProgram
  exact avoids_compiled H _ (avoids_clearMany H _ entry_scratch_avoids) 175 854

theorem assignment_avoids : AvoidsCmd H FactorAssignmentProgram.assignment :=
  ⟨initialize_avoids, setup_avoids, product_avoids⟩

namespace Head
open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open HeadSumProgram
open HeadEvaluationProgram.StagedGate (copy clear)



private theorem bank_clear_avoids (tmp : Fin 896) (ports : List (Fin 896))
    (ht : ¬ H tmp) (hp : ∀ i ∈ ports, ¬ H i) :
    AvoidsCmd H (BankRoutines.clearCmd tmp (0 : Fin 40) 1 ports) := by
  induction ports with
  | nil => exact avoids_clearProgram H tmp 0 1 ht
  | cons i ports ih =>
    exact ⟨avoids_clearProgram H i 0 1 (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

private theorem copy_avoids (src dst : Fin 896) (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (copy src dst) := avoids_copyProgram H src dst 31 0 1 hs hd (by decide)

private theorem clear_avoids (src : Fin 896) (hs : ¬ H src) :
    AvoidsCmd H (clear src) := avoids_clearProgram H src 0 1 hs

theorem clearWork_avoids : AvoidsCmd H HeadSumAssembly.clearWork := by
  refine ⟨clear_avoids 31 (by decide), bank_clear_avoids 31 _ (by decide) ?_⟩
  intro i hi
  rw [HeadSumAssembly.mem_workPorts] at hi
  rcases hi with hi | hi
  · omega
  · simp only [HeadSumAssembly.controllerPorts, List.mem_cons, List.mem_nil_iff,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide

theorem overlay_avoids : AvoidsCmd H HighQueryAdapter.NativeOverlay.prepare := by
  refine ⟨⟨avoids_clearProgram H 875 0 1 (by decide),
    bank_clear_avoids 875 _ (by decide) ?_⟩, ?_⟩
  · norm_num [HighQueryAdapter.NativeOverlay.changed, Fin.coe_ofNat_eq_mod]
  · apply avoids_call_lift_of_range
    intro i
    fin_cases i <;> decide

theorem accumulate_avoids : AvoidsCmd H accumulate := by
  refine ⟨?_, ?_⟩
  · apply avoids_call_lift_of_range
    intro i
    fin_cases i <;> decide
  · apply avoids_liftProgram
    apply avoids_compiled
    apply avoids_clearMany
    norm_num [FactorEnvironment.environmentPorts, Function.comp_def, Fin.coe_ofNat_eq_mod]

theorem gate_avoids : AvoidsCmd H HeadEvaluationProgram.StagedGate.command := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨copy_avoids _ _ (by decide) (by decide),
      copy_avoids _ _ (by decide) (by decide), copy_avoids _ _ (by decide) (by decide),
      copy_avoids _ _ (by decide) (by decide), copy_avoids _ _ (by decide) (by decide),
      copy_avoids _ _ (by decide) (by decide)⟩
  · apply avoids_call_lift_of_range
    intro i
    change ¬ ((i.val = 832 ∨ i.val = 833))
    have := i.isLt
    omega
  · exact ⟨clear_avoids _ (by decide), clear_avoids _ (by decide),
      clear_avoids _ (by decide), clear_avoids _ (by decide),
      clear_avoids _ (by decide), clear_avoids _ (by decide)⟩

private theorem counter_ports_avoid (p : CounterForPrograms.Ports 40 896)
    (hc : ¬ H p.counter) (hs : ¬ H p.scratch) (i : Fin 2) :
    ¬ H (CounterForPrograms.stackPorts p i) := by
  fin_cases i
  · exact hc
  · exact hs

/-- Every head-controller access is accounted for, including losing gates,
all binary counter tests and decrements, and final reclamation. -/
theorem head_avoids (accepted : Code) (ha : AvoidsCmd H accepted) :
    AvoidsCmd H (HeadSumAssembly.head accepted) := by
  have hpower : AvoidsCmd H power := by
    apply avoids_call_lift_of_range
    intro i
    fin_cases i <;> decide
  have hseed : AvoidsCmd H seed :=
    ⟨copy_avoids _ _ (by decide) (by decide),
      copy_avoids _ _ (by decide) (by decide), hpower, clear_avoids _ (by decide)⟩
  have hinc : AvoidsCmd H (Counters.incrementCmd cursorPorts) :=
    avoids_call_lift_of_range H _ _ _ (counter_ports_avoid cursorPorts (by decide) (by decide))
  have hbody : AvoidsCmd H (body accepted) := ⟨gate_avoids, ⟨ha, True.intro⟩, hinc⟩
  have hzero : AvoidsCmd H (CounterForPrograms.zeroCmd fuelPorts) :=
    avoids_call_lift_of_range H _ _ _ (counter_ports_avoid fuelPorts (by decide) (by decide))
  have hdec : AvoidsCmd H (CounterForPrograms.decrementCmd fuelPorts) :=
    avoids_call_lift_of_range H _ _ _ (counter_ports_avoid fuelPorts (by decide) (by decide))
  have htest : AvoidsCmd H (CounterForPrograms.testCmd fuelPorts) := ⟨hzero, True.intro⟩
  have hloop : AvoidsCmd H (HeadSumProgram.command accepted) := ⟨htest, hbody, hdec, htest⟩
  have hfinal : AvoidsCmd H finalize := by
    apply avoids_liftProgram
    apply avoids_compiled
    apply avoids_clearMany
    norm_num [Function.comp_def, Fin.coe_ofNat_eq_mod]
  exact ⟨clearWork_avoids,
    avoids_compiled H _ (show AvoidsCmd H (scan accepted) from ⟨hseed, hloop, hfinal⟩) _ _⟩

end Head

namespace Prepare

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open HighQueryAdapter

open SignatureHeadPrepareFootprint (bank_clear_avoids overwrite_avoids)

theorem key_avoids :
    AvoidsCmd H
      SignatureKeyNative.command := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

theorem reset_avoids :
    AvoidsCmd H
      SignatureHeadPrepare.reset := by
  refine ⟨avoids_clearProgram _ 841 0 1 (by decide),
    bank_clear_avoids _ 841 0 1 _ (by decide) ?_⟩
  intro i hi
  simp only [SignatureHeadPrepare.cleared, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem masters_avoids :
    AvoidsCmd H
      SignatureHeadPrepare.masters :=
  ⟨_root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepareFootprint.overwrite_avoids _ 141 864 (by decide) (by decide) (by decide),
    _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepareFootprint.overwrite_avoids _ 847 865 (by decide) (by decide) (by decide),
    _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepareFootprint.overwrite_avoids _ 671 175 (by decide) (by decide) (by decide)⟩

theorem select_avoids :
    AvoidsCmd H
      NativeHeadSelect.select := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

theorem selector_command_avoids :
    AvoidsCmd H
      NativeHeadSelect.command :=
  ⟨avoids_copyProgram _ 858 878 880 0 1 (by decide) (by decide) (by decide),
    avoids_copyProgram _ 670 879 880 0 1 (by decide) (by decide) (by decide),
    select_avoids⟩

theorem selector_reset_avoids :
    AvoidsCmd H
      NativeHeadSelect.reset := by
  refine ⟨avoids_clearProgram _ 880 0 1 (by decide),
    bank_clear_avoids _ 880 0 1 _ (by decide) ?_⟩
  intro i hi
  simp only [NativeHeadSelect.changed, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem selector_prepare_avoids :
    AvoidsCmd H
      NativeHeadSelect.prepare := ⟨selector_reset_avoids, selector_command_avoids⟩

theorem selector_program_avoids :
    AvoidsProgram H
      NativeHeadSelect.prepareProgram :=
  avoids_compiled _ _ selector_prepare_avoids 858 867

theorem command_avoids :
    AvoidsCmd H
      SignatureHeadPrepare.command :=
  ⟨reset_avoids, key_avoids, masters_avoids, selector_program_avoids⟩

end Prepare

/-- The accepted path is instantiated with the actual source-table assignment
and dense addition/reset programs, with no callback footprint premise. -/
theorem accepted_avoids : AvoidsCmd H HeadSumAssembly.accepted :=
  ⟨Head.overlay_avoids, assignment_avoids, Head.accumulate_avoids⟩

theorem head_avoids : AvoidsCmd H (HeadSumAssembly.head HeadSumAssembly.accepted) :=
  Head.head_avoids _ accepted_avoids

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame.Factor

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame.Control
open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog ProgramTapeReplay

private theorem isolated_avoids {r s l : ℕ}
    (p : Program r s l) (register : Fin r → Fin 16) (stack : Fin s → Fin 896)
    (tmp : Fin 896) (ports : List (Fin 896)) (inputs outputs : List (Fin 896 × Fin 896))
    (ht : ¬ ((tmp.val = 832 ∨ tmp.val = 833)))
    (hp : ∀ i ∈ ports, ¬ ((i.val = 832 ∨ i.val = 833)))
    (hi : ∀ q ∈ inputs, ¬ ((q.1.val = 832 ∨ q.1.val = 833)) ∧
      ¬ ((q.2.val = 832 ∨ q.2.val = 833)))
    (ho : ∀ q ∈ outputs, ¬ ((q.1.val = 832 ∨ q.1.val = 833)) ∧
      ¬ ((q.2.val = 832 ∨ q.2.val = 833)))
    (hs : ∀ i, ¬ (((stack i).val = 832 ∨ (stack i).val = 833))) :
    AvoidsCmd (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
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

theorem fillCommand_avoids (isE : Bool) :
    AvoidsCmd (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      (PairNativeSetup.fillCommand isE) := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillInput, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillOutput, Fin.coe_ofNat_eq_mod]
  · intro i
    change ¬ ((325+i.val = 832 ∨ 325+i.val = 833))
    omega

theorem expandCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      PairNativeSetup.expandCommand :=
  ⟨fillCommand_avoids true, fillCommand_avoids false⟩

theorem expandCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      PairNativeSetup.expandCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ expandCommand_avoids _ _)

theorem nodeAppendPrepare_avoids :
    AvoidsCmd (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      NodeAppendSpace.prepare := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  · exact ⟨avoids_copyProgram _ 194 5 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 202 12 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 204 39 89 0 1 (by decide) (by decide) (by decide)⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame.Control

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

local notation "H" => (fun i : Fin 896 => (Fin.val i = 832 ∨ Fin.val i = 833))

theorem tuple_port (i : Fin 12) : ¬ H (tupleStacks i) := by
  change ¬ ((836 + i.val = 832 ∨ 836 + i.val = 833))
  omega

theorem copy_avoids (src dst tmp : Fin 896)
    (hs : ¬ H src) (hd : ¬ H dst) (ht : ¬ H tmp) :
    AvoidsCmd H (copyWord src dst tmp) :=
  avoids_copyProgram H src dst tmp 0 1 hs hd ht

theorem clear_avoids (src : Fin 896) (hs : ¬ H src) :
    AvoidsCmd H (clearWord src) :=
  avoids_clearProgram H src 0 1 hs

private theorem SafeAvoids.intro {c : Cmd 40 896} (hc : AvoidsCmd H c) : SafeAvoids c :=
  ⟨hc⟩

private theorem SafeAvoids.seq {first second : Cmd 40 896}
    (hfirst : SafeAvoids first) (hsecond : SafeAvoids second) :
    SafeAvoids (.seq first second) :=
  ⟨⟨hfirst.proof, hsecond.proof⟩⟩

private theorem SafeAvoids.call {l : Nat} {p : Program 40 896 l}
    (hp : AvoidsProgram H p) :
    SafeAvoids (.call p) :=
  ⟨hp⟩

theorem clears_avoids (ports : List (Fin 896))
    (hp : ∀ i ∈ ports, ¬ H i) : AvoidsCmd H (clearWords ports) := by
  induction ports with
  | nil => exact True.intro
  | cons i is ih => exact ⟨clear_avoids i (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

theorem push_frame_avoids (src dst : Fin 896) (hne : src ≠ dst)
    (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (pushWordCommand src dst hne) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i
  · exact hs
  · exact hd

theorem pop_frame_avoids (src dst : Fin 896) (hne : src ≠ dst)
    (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (popWordCommand src dst hne) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i
  · exact hs
  · exact hd

theorem counter_ports_avoid (p : CounterForPrograms.Ports 40 896)
    (hc : ¬ H p.counter) (hs : ¬ H p.scratch) (i : Fin 2) :
    ¬ H (CounterForPrograms.stackPorts p i) := by
  fin_cases i
  · exact hc
  · exact hs

theorem counter_test_avoids (p : CounterForPrograms.Ports 40 896)
    (hc : ¬ H p.counter) (hs : ¬ H p.scratch) :
    AvoidsCmd H (CounterForPrograms.testCmd p) := by
  refine ⟨?_, True.intro⟩
  exact avoids_call_lift_of_range H _ _ _ (counter_ports_avoid p hc hs)

theorem counter_advance_avoids (p : CounterForPrograms.Ports 40 896)
    (hc : ¬ H p.counter) (hs : ¬ H p.scratch) :
    AvoidsCmd H (CounterForPrograms.advanceCmd p) := by
  refine ⟨?_, counter_test_avoids p hc hs⟩
  exact avoids_call_lift_of_range H _ _ _ (counter_ports_avoid p hc hs)

theorem advance_avoids : AvoidsCmd H advanceCommand := by
  refine ⟨?_, counter_advance_avoids remainingPorts (tuple_port 7) (tuple_port 5), True.intro⟩
  exact avoids_call_lift_of_range H _ _ _
    (counter_ports_avoid candidatePorts (tuple_port 2) (tuple_port 10))

theorem fuel_avoids : AvoidsCmd H initialFuelCommand :=
  avoids_call_lift_of_range H _ _ _
    (counter_ports_avoid initialFuelPorts (tuple_port 4) (tuple_port 7))

theorem reset_avoids : AvoidsCmd H resetCommand :=
  ⟨copy_avoids 651 _ _ (by decide) (tuple_port 2) (tuple_port 5),
    copy_avoids 651 _ _ (by decide) (tuple_port 4) (tuple_port 5),
    fuel_avoids, True.intro, True.intro⟩

theorem reset_generator_avoids : AvoidsCmd H resetGeneratorCommand :=
  ⟨reset_avoids, copy_avoids 651 _ _ (by decide) (tuple_port 8) (tuple_port 5)⟩

theorem save_cursor_avoids : AvoidsCmd H saveCursorCommand :=
  ⟨push_frame_avoids _ _ _ (tuple_port 2) (tuple_port 0),
    push_frame_avoids _ _ _ (tuple_port 7) (tuple_port 0)⟩

theorem restore_cursor_avoids : AvoidsCmd H restoreCursorCommand :=
  ⟨pop_frame_avoids _ _ _ (tuple_port 0) (tuple_port 7),
    pop_frame_avoids _ _ _ (tuple_port 0) (tuple_port 2)⟩

theorem record_representative_avoids : AvoidsCmd H recordRepresentativeCommand :=
  ⟨copy_avoids _ _ _ (tuple_port 2) (tuple_port 4) (tuple_port 5),
    push_frame_avoids _ _ _ (tuple_port 4) (tuple_port 1)⟩

theorem descend_level_avoids : AvoidsCmd H descendLevelCommand :=
  ⟨tuple_port 6, True.intro, tuple_port 9, tuple_port 6, True.intro⟩

theorem ascend_level_avoids : AvoidsCmd H ascendLevelCommand :=
  ⟨tuple_port 9, True.intro, tuple_port 6, True.intro⟩

theorem leave_head_avoids : AvoidsCmd H leaveHeadCommand := by
  apply clears_avoids
  intro i hi
  simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply tuple_port

theorem drop_representative_avoids : AvoidsCmd H dropRepresentativeCommand :=
  ⟨pop_frame_avoids _ _ _ (tuple_port 1) (tuple_port 4), clear_avoids _ (tuple_port 4)⟩

theorem test_parent_avoids : AvoidsCmd H testParentCommand := tuple_port 0

theorem test_available_avoids : AvoidsCmd H testAvailableCommand :=
  ⟨counter_test_avoids remainingPorts (tuple_port 7) (tuple_port 5), True.intro⟩

theorem initialize_levels_avoids : AvoidsCmd H initializeLevelsCommand :=
  ⟨copy_avoids 130 _ _ (by decide) (tuple_port 6) (tuple_port 5),
    copy_avoids 649 _ _ (by decide) (tuple_port 9) (tuple_port 5),
    tuple_port 6, True.intro, True.intro⟩

theorem initialize_fresh_avoids : AvoidsCmd H initializeFreshCommand :=
  ⟨clear_avoids _ (by decide), True.intro, show ¬ H (rescanStacks 22) from by decide⟩

theorem advance_candidate_avoids : AvoidsCmd H advanceCandidateCommand :=
  ⟨advance_avoids, clear_avoids _ (tuple_port 3)⟩

theorem reset_predecessor_avoids : AvoidsCmd H resetPredecessorCommand :=
  copy_avoids 651 _ _ (by decide) (tuple_port 8) (tuple_port 5)

theorem probe_avoids (predicate : Cmd 40 896) (hp : AvoidsCmd H predicate) :
    AvoidsCmd H (probeWith predicate) :=
  ⟨test_available_avoids, ⟨initialize_fresh_avoids, hp,
    show ¬ H (rescanStacks 22) from by decide⟩, True.intro⟩

theorem descend_avoids (loadHead : Cmd 40 896) (hl : AvoidsCmd H loadHead) :
    AvoidsCmd H (descendWith loadHead) :=
  ⟨record_representative_avoids, save_cursor_avoids, descend_level_avoids,
    leave_head_avoids, True.intro, hl, reset_generator_avoids⟩

theorem resume_parent_avoids (loadHead : Cmd 40 896) (hl : AvoidsCmd H loadHead) :
    AvoidsCmd H (resumeParentWith loadHead) :=
  ⟨drop_representative_avoids, restore_cursor_avoids, ascend_level_avoids,
    hl, reset_predecessor_avoids, advance_candidate_avoids⟩

theorem ascend_avoids (loadHead : Cmd 40 896) (hl : AvoidsCmd H loadHead) :
    AvoidsCmd H (ascendWith loadHead) :=
  ⟨leave_head_avoids, test_parent_avoids, resume_parent_avoids loadHead hl, True.intro⟩

theorem setup_avoids (loadHead : Cmd 40 896) (hl : AvoidsCmd H loadHead) :
    AvoidsCmd H (setupWith loadHead) := by
  refine ⟨?_, initialize_levels_avoids, True.intro, hl, reset_generator_avoids⟩
  apply clears_avoids
  intro i hi
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
  exact tuple_port j

/-- This covers the actual fixed attained-signature DFS, including all
presence tests, cursor scans and frame manipulation. -/
theorem tuple_controller_avoids (loadHead predicate visit : Cmd 40 896)
    (hl : AvoidsCmd H loadHead) (hp : AvoidsCmd H predicate)
    (hv : AvoidsCmd H visit) :
    AvoidsCmd H (SignatureTupleProgram.command controllerPorts
      (assembleRoutines loadHead predicate visit)) :=
  ⟨setup_avoids loadHead hl, ⟨hv, ascend_avoids loadHead hl⟩,
    probe_avoids predicate hp,
    ⟨descend_avoids loadHead hl, advance_candidate_avoids⟩,
    ascend_avoids loadHead hl⟩

private theorem SafeAvoids.tupleController
    {loadHead predicate visit : Cmd 40 896}
    (hl : SafeAvoids loadHead) (hp : SafeAvoids predicate)
    (hv : SafeAvoids visit) :
    SafeAvoids (SignatureTupleProgram.command controllerPorts
      (assembleRoutines loadHead predicate visit)) :=
  SafeAvoids.intro
    (tuple_controller_avoids loadHead predicate visit hl.proof hp.proof hv.proof)

theorem candidate_avoids : AvoidsCmd H candidateCall := by
  apply avoids_call_lift_of_range
  intro i
  change ¬ (((if i.val = 0 then 141 else if i.val = 15 then 847 else
    if i.val = 16 then 838 else if i.val = 17 then 839 else
    if i.val = 18 then 844 else 340 + i.val) = 832 ∨
    (if i.val = 0 then 141 else if i.val = 15 then 847 else
      if i.val = 16 then 838 else if i.val = 17 then 839 else
      if i.val = 18 then 844 else 340 + i.val) = 833))
  split_ifs <;> omega

theorem overwrite_avoids (src dst : Fin 896) (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (QueryTupleVisitor.overwrite src dst) :=
  ⟨avoids_clearProgram H dst 0 1 hd, copy_avoids src dst 841 hs hd (by decide)⟩

theorem replay_avoids (work : Cmd 40 896) (hw : AvoidsCmd H work) :
    AvoidsCmd H (QueryExecution.replay work) :=
  ⟨⟨overwrite_avoids 837 840 (by decide) (by decide),
    overwrite_avoids 845 843 (by decide) (by decide)⟩,
    show ¬ H 840 from by decide,
    ⟨pop_frame_avoids 840 838 (by decide) (by decide) (by decide),
      show ¬ H 843 from by decide⟩,
    hw, avoids_clearProgram H 838 0 1 (by decide), show ¬ H 840 from by decide⟩

private theorem SafeAvoids.replay {work : Cmd 40 896} (hw : SafeAvoids work) :
    SafeAvoids (QueryExecution.replay work) :=
  SafeAvoids.intro (replay_avoids work hw.proof)

theorem environment_avoids : AvoidsCmd H FactorEnvironment.bootstrap := by
  apply avoids_liftProgram
  apply avoids_compiled
  apply avoids_copyMany
  · decide
  · simp [FactorEnvironment.pairs, Fin.coe_ofNat_eq_mod]

theorem clear_pair_avoids : AvoidsCmd H QueryAssembler.clearPair := by
  apply avoids_liftProgram
  apply avoids_compiled
  apply avoids_clearMany
  intro i hi
  have hh := (QueryAssembler.pairScratch_mem i).mp hi
  rcases hh with hh | hh | rfl | rfl | rfl | rfl
  · change ¬ H i
    omega
  · change ¬ H i
    omega
  all_goals decide

theorem pair_sign_avoids : AvoidsCmd H QueryProgram.pairSignCall := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

theorem signed_accumulate_avoids : AvoidsCmd H QueryProgram.signedAccumulate := by
  constructor
  · apply avoids_call_lift_of_range
    intro i
    change ¬ H (QueryProgram.leafScalePorts i)
    simp only [QueryProgram.leafScalePorts]
    split_ifs <;> simp only [Fin.coe_ofNat_eq_mod] <;> have hi := i.isLt <;> omega
  · apply avoids_call_lift_of_range
    intro i
    change ¬ H (QueryProgram.leafNormalizePorts i)
    simp only [QueryProgram.leafNormalizePorts]
    split_ifs <;> simp only [Fin.coe_ofNat_eq_mod] <;> have hi := i.isLt <;> omega

theorem pair_update_avoids : AvoidsCmd H QueryProgram.pairUpdate :=
  ⟨pair_sign_avoids, signed_accumulate_avoids, show ¬ H 848 from by decide⟩

theorem commit_pair_avoids : AvoidsCmd H QueryAssembler.commitPair :=
  ⟨⟨clear_pair_avoids, environment_avoids,
    overwrite_avoids 211 34 (by decide) (by decide)⟩,
    pair_update_avoids, clear_pair_avoids⟩


theorem tuple_clear_bank_avoids (ports : List (Fin 896))
    (hp : ∀ i ∈ ports, ¬ H i) : AvoidsCmd H (QueryTupleInit.clearBank ports) := by
  apply avoids_liftProgram
  apply avoids_compiled
  exact avoids_clearMany H ports hp

theorem factor_move_avoids (K : Fin 768 → Prop) (src dst : Fin 768)
    (hs : ¬ K src) (hd : ¬ K dst) (ht : ¬ K 159) :
    AvoidsCmd K (SqrtLog.LeafProgram.Factor.move src dst) :=
  ⟨avoids_copyProgram K src dst 159 0 1 hs hd ht,
    avoids_clearProgram K src 0 1 hs⟩

theorem tuple_multiply_call_avoids : AvoidsCmd H QueryAssembler.TupleMultiply.multiply := by
  apply avoids_liftProgram
  apply avoids_compiled
  refine ⟨factor_move_avoids _ 67 61 (by decide) (by decide) (by decide),
    factor_move_avoids _ 151 67 (by decide) (by decide) (by decide), ?_,
    factor_move_avoids _ 67 151 (by decide) (by decide) (by decide)⟩
  apply avoids_call_lift_of_range
  intro i
  change ¬ H (QueryAssembler.TupleMultiply.ports (SqrtLog.LeafProgram.Factor.nativeStacks i))
  simp only [QueryAssembler.TupleMultiply.ports]
  split_ifs
  · decide
  · decide
  · change ¬ ((i.val = 832 ∨ i.val = 833))
    have hi := i.isLt
    omega

theorem tuple_multiply_avoids : AvoidsCmd H QueryAssembler.TupleMultiply.command := by
  refine ⟨⟨NodeFinishReplay.clearMany_avoids H [61,70] ?_,
    clear_pair_avoids, environment_avoids⟩,
    tuple_multiply_call_avoids, clear_pair_avoids⟩
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl <;> decide


open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

private theorem loader_clearMany_avoids (ps : List (Fin 896))
    (hp : ∀ p ∈ ps, ¬ ((p.val = 832 ∨ p.val = 833))) :
    AvoidsCmd (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833)) (clearMany ps) := by
  induction ps with
  | nil => exact True.intro
  | cons p ps ih =>
    exact ⟨avoids_clearProgram _ p 0 1 (hp p (by simp)),
      ih (fun q hq => hp q (by simp [hq]))⟩

theorem programFrom_avoids (src : Fin 896) (hs : ¬ ((src.val = 832 ∨ src.val = 833))) :
    AvoidsProgram (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      (SignatureHeadLoader.programFrom src) := by
  apply avoids_liftProgram
  apply avoids_compiled
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_⟩
  · exact loader_clearMany_avoids [649,659,846,847] (by norm_num [Fin.coe_ofNat_eq_mod])
  · exact avoids_copyProgram _ src 649 659 0 1 hs (by decide) (by decide)
  · apply avoids_liftProgram_of_range
    intro i hi
    have hv := i.isLt
    change (i.val = 832 ∨ i.val = 833) at hi
    omega
  · exact avoids_clearProgram _ 659 0 1 (by decide)
  · exact avoids_copyProgram _ 668 847 659 0 1 (by decide) (by decide) (by decide)
  · exact loader_clearMany_avoids [668,669,846] (by norm_num [Fin.coe_ofNat_eq_mod])

theorem program843_avoids :
    AvoidsProgram (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      (SignatureHeadLoader.programFrom 843) := programFrom_avoids 843 (by decide)

theorem program845_avoids :
    AvoidsProgram (fun i : Fin 896 => (i.val = 832 ∨ i.val = 833))
      (SignatureHeadLoader.programFrom 845) := programFrom_avoids 845 (by decide)


theorem tuple_sum_avoids : AvoidsCmd H QueryTupleSum.command := by
  refine ⟨⟨QueryPairControlFrame.Control.nodeAppendPrepare_avoids,
    NodeFinishReplay.clearMany_avoids H _ ?_⟩, ?_⟩
  · intro i hi
    have hh := QueryTupleSum.scratchPorts_low hi
    omega
  · apply avoids_call_lift_of_range
    intro i
    change ¬ H (QueryTupleSum.ports i)
    simp only [QueryTupleSum.ports]
    split_ifs <;> simp only [Fin.coe_ofNat_eq_mod] <;> have hi := i.isLt <;> omega

theorem tuple_end_avoids : AvoidsCmd H QueryExecution.TupleEnd.command := by
  refine ⟨tuple_sum_avoids, tuple_clear_bank_avoids _ ?_⟩
  intro i hi
  simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply tuple_port

theorem pair_start_avoids : AvoidsCmd H QueryExecution.PairStart.command :=
  ⟨clear_avoids 851 (by decide), QueryPairControlFrame.Control.expandCaller_avoids⟩

theorem representative_install_avoids : AvoidsCmd H QueryTupleVisitor.installRepresentative :=
  ⟨overwrite_avoids 838 859 (by decide) (by decide),
    avoids_compiled H _ (QueryPairControlFrame.Factor.Head.overlay_avoids) _ _,
    overwrite_avoids 145 869 (by decide) (by decide),
    avoids_clearProgram H 859 0 1 (by decide)⟩

theorem tuple_init_avoids
    (hsetup : AvoidsCmd H FactorAssignmentProgram.setup) :
    AvoidsCmd H QueryTupleInit.command := by
  have hlo : ∀ i ∈ QueryTupleInit.lowPorts, ¬ H i := by
    intro i hi
    have hh := (QueryTupleInit.mem_lowPorts i).mp hi
    omega
  refine ⟨tuple_clear_bank_avoids _ ?_, hsetup,
    overwrite_avoids 69 852 (by decide) (by decide),
    overwrite_avoids 703 869 (by decide) (by decide),
    tuple_clear_bank_avoids _ hlo⟩
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hlo i hi
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst i
    decide


theorem head_sum_avoids : AvoidsCmd H (HeadSumAssembly.head HeadSumAssembly.accepted) :=
  QueryPairControlFrame.Factor.head_avoids

theorem concrete_tuple_init_avoids : AvoidsCmd H QueryTupleInit.command :=
  tuple_init_avoids (QueryPairControlFrame.Factor.setup_avoids)

theorem head_prepare_avoids : AvoidsCmd H SignatureHeadPrepare.command :=
  QueryPairControlFrame.Factor.Prepare.command_avoids

/-- The fixed visitor composes the actual two passes and all arithmetic
without any access to the two suspended pair traversal words. -/
theorem visitor_avoids_of_loader
    (hload : AvoidsProgram H (SignatureHeadLoader.programFrom 843)) :
    AvoidsCmd H QueryVisitorProgram.visitor := by
  have hload' := SafeAvoids.call hload
  have hbaselineSafe := hload'.seq (SafeAvoids.intro representative_install_avoids)
  have hbaseline : AvoidsCmd H QueryVisitorProgram.baselineHead := by
    have hpack : ∃ c, c=QueryVisitorProgram.baselineHead ∧ SafeAvoids c := by
      refine ⟨_,?_,hbaselineSafe⟩
      rw [QueryVisitorProgram.baselineHead]
    obtain ⟨_,rfl,hc⟩ := hpack
    exact hc.proof
  have hevaluateSafe := hload'.seq ((SafeAvoids.intro head_prepare_avoids).seq
    ((SafeAvoids.intro head_sum_avoids).seq (SafeAvoids.intro tuple_multiply_avoids)))
  have hevaluate : AvoidsCmd H QueryVisitorProgram.evaluateHead := by
    have hpack : ∃ c, c=QueryVisitorProgram.evaluateHead ∧ SafeAvoids c := by
      refine ⟨_,?_,hevaluateSafe⟩
      rw [QueryVisitorProgram.evaluateHead,QueryVisitorProgram.loadHead,
        QueryVisitorProgram.evaluateLoadedHead]
    obtain ⟨_,rfl,hc⟩ := hpack
    exact hc.proof
  have hvisitor := (SafeAvoids.intro concrete_tuple_init_avoids).seq
    ((SafeAvoids.intro hbaseline).replay.seq
      ((SafeAvoids.intro hevaluate).replay.seq (SafeAvoids.intro tuple_end_avoids)))
  have hpack : ∃ c, c=QueryVisitorProgram.visitor ∧ SafeAvoids c := by
    refine ⟨_,?_,hvisitor⟩
    rw [QueryVisitorProgram.visitor]
  obtain ⟨_,rfl,hc⟩ := hpack
  exact hc.proof

theorem tuple_avoids_of_loader
    (hload : AvoidsProgram H (SignatureHeadLoader.programFrom 845))
    (hvisit : AvoidsCmd H QueryVisitorProgram.visitor) :
    AvoidsCmd H SignatureTupleComplete.command := by
  have htuple := (SafeAvoids.call hload).tupleController
    (SafeAvoids.intro candidate_avoids) (SafeAvoids.intro hvisit)
  have hpack : ∃ c, c=SignatureTupleComplete.command ∧ SafeAvoids c := by
    refine ⟨_,?_,htuple⟩
    rw [SignatureTupleComplete.command,SignatureTupleComplete.routines,
      SignatureTupleLoader.loadHead,SignatureTupleLoader.headAddress]
  obtain ⟨_,rfl,hc⟩ := hpack
  exact hc.proof


theorem visitor_avoids : AvoidsCmd H QueryVisitorProgram.visitor :=
  visitor_avoids_of_loader program843_avoids

theorem tuple_avoids : AvoidsCmd H SignatureTupleComplete.command :=
  tuple_avoids_of_loader program845_avoids visitor_avoids

private theorem tuple_safe : SafeAvoids SignatureTupleComplete.command :=
  ⟨tuple_avoids⟩

private theorem callback_safe : SafeAvoids QueryStreamProgram.pairCallback := by
  let hs := (SafeAvoids.intro (c := QueryExecution.PairStart.command)
      pair_start_avoids).seq
    (tuple_safe.seq (SafeAvoids.intro (c := QueryAssembler.commitPair)
      commit_pair_avoids))
  have hpack : ∃ c, c = QueryStreamProgram.pairCallback ∧ SafeAvoids c := by
    refine ⟨_, ?_, hs⟩
    rw [QueryStreamProgram.pairCallback]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc

theorem callback_avoids : AvoidsCmd H QueryStreamProgram.pairCallback :=
  callback_safe.proof

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReadyConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query-entry facts from the actual arithmetic and native cache
producers. Pair masks are installed by the paid pair-start command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram LeafProgram LeafProgram.PreparedSource
open LeafHeadSetupProgram QueryTupleState
open ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem CommonReady.frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {P : ℕ} {a b : State 40 896}
    (h : CommonReady q node H high P a) (hf : ∀ i∈commonPorts, b.stacks i=a.stacks i) :
    CommonReady q node H high P b := by
  refine {
    lifting := h.lifting
    generatedTheta := h.generatedTheta
    sourceMinus := h.sourceMinus
    ambient := (hf 128 (by decide)).trans h.ambient
    theta := (hf 78 (by decide)).trans h.theta
    modulus := (hf 194 (by decide)).trans h.modulus
    table := (hf 201 (by decide)).trans h.table
    width := (hf 202 (by decide)).trans h.width
    scalarZero := (hf 203 (by decide)).trans h.scalarZero
    degree := (hf 204 (by decide)).trans h.degree
    one := (hf 207 (by decide)).trans h.one
    minus := (hf 211 (by decide)).trans h.minus
    precision := (hf 212 (by decide)).trans h.precision
    order := (hf 243 (by decide)).trans h.order
    zero := (hf 280 (by decide)).trans h.zero
    code := (hf 281 (by decide)).trans h.code
    clauses := (hf 700 (by decide)).trans h.clauses
    rows := (hf 701 (by decide)).trans h.rows
    rowCount := (hf 704 (by decide)).trans h.rowCount
    markedIndex := (hf 705 (by decide)).trans h.markedIndex
    markedFlag := (hf 706 (by decide)).trans h.markedFlag
    indexModulus := (congrArg BinaryArithmetic.toNat (hf 707 (by decide))).trans h.indexModulus
    indexWidth := (congrArg List.length (hf 708 (by decide))).trans h.indexWidth
    highMask := (hf 702 (by decide)).trans h.highMask
    highBits := (hf 703 (by decide)).trans h.highBits
    colors := (hf 130 (by decide)).trans h.colors
    nodes := (hf 131 (by decide)).trans h.nodes
    typeWidth := (hf 132 (by decide)).trans h.typeWidth
    positive := (hf 710 (by decide)).trans h.positive
    negative := (hf 711 (by decide)).trans h.negative
    sourceWidth := (hf 140 (by decide)).trans h.sourceWidth
    power := (hf 712 (by decide)).trans h.power
    powerNegative := h.powerNegative
    radius := (hf 138 (by decide)).trans h.radius
    offset := (hf 139 (by decide)).trans h.offset
    metadata := (hf 135 (by decide)).trans h.metadata
    plans := (hf 136 (by decide)).trans h.plans
    inverses := (hf 713 (by decide)).trans h.inverses
    negatives := (hf 714 (by decide)).trans h.negatives
    differences := (hf 715 (by decide)).trans h.differences
    ringWidth := (hf 717 (by decide)).trans h.ringWidth
    rowWidth := (hf 716 (by decide)).trans h.rowWidth
    inverseDenominator := (hf 728 (by decide)).trans h.inverseDenominator
    cacheCaps := ?_
    ambientCap := ?_
    oneCap := ?_ }
  · intro p hp
    have hm : p.1.castAdd 128∈commonPorts := by
      simp only [LeafNodeCacheProgram.directCopies, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [hf _ hm]
    exact h.cacheCaps p hp
  · rw [hf 128 (by decide)]
    exact h.ambientCap
  · rw [hf 207 (by decide)]
    exact h.oneCap

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual finite-difference callback uses the physical pair masks and
one semantic node accumulator. The reference support decoding below is used
only in the proof; the executed controller retains its four finite words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram QueryTupleState QueryPairCommit QueryReadyConstruction
open SignatureTupleSource
open scoped BigOperators
open SqrtLog.ProgramTapeReplay

local notation "Hidden" => (fun i : Fin 896 => Fin.val i=832 ∨ Fin.val i=833)

theorem inner_subset (N : ℕ) (word : List (Option Bool)) :
    inner N word ⊆ outer N word := by
  intro i hi
  simp only [inner,Finset.mem_filter,Finset.mem_univ,true_and] at hi
  simp only [outer,Finset.mem_filter,Finset.mem_univ,true_and]
  change (word.getD i.val none).getD false=true at hi
  cases h : word.getD i.val none with
  | none => rw [h] at hi; cases hi
  | some b => simp

theorem encode_decoded (N : ℕ) (word : List (Option Bool)) (hlen : word.length=N) :
    DifferencePairs.encodePair (outer N word) (inner N word)=word := by
  subst N
  calc
    _=List.ofFn word.get := by
      unfold DifferencePairs.encodePair
      apply congrArg List.ofFn
      funext i
      have hd : word.getD i.val none=word.get i := List.getD_eq_getElem _ _ i.isLt
      simp only [outer,inner,Finset.mem_filter,Finset.mem_univ,true_and,hd]
      cases h : word.get i with
      | none => simp
      | some b => cases b <;> simp
    _=word := List.ofFn_get word

theorem Invariant.stable {r Q n d P F : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {source : ProducedSource}
    {origin a b : State 40 896} {total : Truncated (q.p.model.O q.p.t) q.J}
    (h : Invariant q node H high P F source origin total a)
    (hf : ∀ i,(∀ j,i≠QueryStreamProgram.pairPorts.stack j) → b.stacks i=a.stacks i) :
    Invariant q node H high P F source origin total b := by
  have hout (i : Fin 896) (hi : (i.val < 832) ∨ (836 ≤ i.val)) :
      ∀ j,i≠QueryStreamProgram.pairPorts.stack j := by
    intro j he
    have hv := congrArg Fin.val he
    change i.val=832+j.val at hv
    have hj := j.isLt
    omega
  refine ⟨h.common.frame ?_,h.accumulator.frame (hf 850 (hout 850 (by decide))),
    (fun i hi => by rw [hf i hi]; exact h.compact i hi),?_,?_⟩
  · intro i hi
    have hc : ∀ j ∈ commonPorts,j.val<832 := by simp [commonPorts,Fin.coe_ofNat_eq_mod]
    exact hf i (hout i (Or.inl (hc i hi)))
  · constructor
    intro i hi
    exact (hf (SignatureHeadLoader.lowStacks i) (hout _ (Or.inl (by
      change i.val<832
      have := i.isLt
      omega)))).trans (h.masters.stored i hi)
  · intro i hi
    have hc : ∀ j ∈ framePorts,(j.val < 832) ∨ (836 ≤ j.val) := by
      simp [framePorts,Fin.coe_ofNat_eq_mod]
    exact (hf i (hout i (hc i hi))).trans (h.frame i hi)

/-- The semantic invariant is independent of both opaque bookkeeping words. -/
theorem Invariant.rebase {r Q n d P F : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {source : ProducedSource}
    {origin a : State 40 896} {total : Truncated (q.p.model.O q.p.t) q.J}
    (h : Invariant q node H high P F source origin total a)
    (saved : Fin 896 → List Bool) :
    Invariant q node H high P F source origin total (rebaseState Hidden saved a) := by
  apply h.stable
  intro i hi
  change rebaseStacks Hidden saved a.stacks i=a.stacks i
  apply rebaseStacks_of_not_mem Hidden saved a.stacks i
  rintro (h0|h1)
  · exact hi 0 (Fin.ext h0)
  · exact hi 1 (Fin.ext h1)

/-- The callback's preliminary empty-depth pop changes registers only. -/
theorem cursor_popped_stacks (J : ℕ) (word : List (Option Bool)) (a : State 40 896)
    (ha : DifferencePairsProgram.Cursor QueryStreamProgram.pairPorts 0 J word true a) :
    (DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 a).stacks=a.stacks := by
  have hz : a.stacks (QueryStreamProgram.pairPorts.stack 0)=[] := ha.depth
  simp [DifferencePairsProgram.popped,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,BitProgram.execInstr,hz]

/-- At a callback the two live masks have exactly the active dimension;
erasing only the unread depth/budget words gives the fixed compact cap. -/
theorem cursor_shadow_bound {r Q n d P F : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {source : ProducedSource}
    {origin a : State 40 896} {total : Truncated (q.p.model.O q.p.t) q.J}
    (h : Invariant q node H high P F source origin total a)
    (J : ℕ) (word : List (Option Bool))
    (hc : DifferencePairsProgram.Cursor QueryStreamProgram.pairPorts 0 J word true a)
    (hlen : word.length=n-H.card) (hN : n-H.card ≤ F) :
    ∀ i,((rebaseState Hidden (fun _=>[])
      (DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 a)).stacks i).length ≤ F := by
  apply CommandStackTransport.shadow_stack_bound
  intro i hi
  rw [cursor_popped_stacks J word a hc]
  by_cases he : i=834
  · subst i
    change (a.stacks (QueryStreamProgram.pairPorts.stack 2)).length ≤ F
    rw [hc.outer,List.length_reverse,List.length_map,hlen]
    exact hN
  by_cases hu : i=835
  · subst i
    change (a.stacks (QueryStreamProgram.pairPorts.stack 3)).length ≤ F
    rw [hc.inner,List.length_reverse,List.length_map,hlen]
    exact hN
  apply h.compact
  intro j
  fin_cases j
  · intro h0; exact hi (Or.inl (congrArg Fin.val h0))
  · intro h1; exact hi (Or.inr (congrArg Fin.val h1))
  · exact he
  · exact hu

/-- The callback remains total when the untouched unary budget is arbitrary.
Only its proof-side shadow erases832/833; the actual run restores both words
and has exactly the same instruction count. -/
theorem callback_cursor_run_oai (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : SignatureTupleComplete.RetainedCap s F)
    (hheads : ∀ depth < s.input.r,s.headSize depth ≤ height)
    (origin a : State 40 896) (total : Truncated (q.p.model.O q.p.t) q.J)
    (hi : Invariant q s.input.node H high M F s origin total a)
    (hm : origin.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (haddress : origin.stacks 649=List.replicate s.base true)
    (J : ℕ) (word : List (Option Bool)) (hlen : word.length=s.input.n-H.card)
    (hc : DifferencePairsProgram.Cursor QueryStreamProgram.pairPorts 0 J word true a) :
    ∃ steps b,
      Eval QueryStreamProgram.pairCallback steps
        (DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 a) b ∧
      steps ≤ callbackBudget s q (s.input.n-H.card) F S Z B height ∧
      (∀ j,b.stacks (QueryStreamProgram.pairPorts.stack j)=a.stacks (QueryStreamProgram.pairPorts.stack j)) ∧
      Invariant q s.input.node H high M F s origin
        (visit (s.input.n-H.card) (pairValue s q H high owner head facts) word total) b ∧
      ((∀ i,(a.stacks i).length ≤ F) → (∀ i,(b.stacks i).length ≤ F) ∧
        QueryExecution.PrefixBound QueryStreamProgram.pairCallback (steps+1)
          (DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 a)
          (callbackSpace s q (s.input.n-H.card) F B)) := by
  let a₀ := DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 a
  let shadow := rebaseState Hidden (fun _=>[]) a₀
  have hsame : a₀.stacks=a.stacks := cursor_popped_stacks J word a hc
  have hi₀ : Invariant q s.input.node H high M F s origin total a₀ :=
    hi.stable (fun i _ => congrFun hsame i)
  have hiShadow := hi₀.rebase (fun _=>[])
  have hbound : ∀ i,(shadow.stacks i).length ≤ F :=
    cursor_shadow_bound hi J word hc hlen (by have := caps.count; omega)
  have hshadow (i : Fin 896) (hv : ¬ Hidden i) : shadow.stacks i=a.stacks i :=
    (rebaseStacks_of_not_mem Hidden (fun _=>[]) a₀.stacks i hv).trans (congrFun hsame i)
  have he : shadow.stacks 834=((DifferencePairs.encodePair
      (outer (s.input.n-H.card) word) (inner (s.input.n-H.card) word)).map Option.isSome).reverse := by
    rw [hshadow 834 (by decide),encode_decoded _ word hlen]
    exact hc.outer
  have hu : shadow.stacks 835=((DifferencePairs.encodePair
      (outer (s.input.n-H.card) word) (inner (s.input.n-H.card) word)).map (fun x=>x.getD false)).reverse := by
    rw [hshadow 835 (by decide),encode_decoded _ word hlen]
    exact hc.inner
  obtain ⟨steps,b,hEval,hI,hcontrol,hb,htime,hprefix⟩ :=
    callback_run s q H high owner head facts caps cap hheads origin shadow total hiShadow hm haddress
      (outer (s.input.n-H.card) word) (inner (s.input.n-H.card) word)
      (inner_subset _ word) he hu hbound
  let out := rebaseState Hidden a₀.stacks b
  have heval : Eval QueryStreamProgram.pairCallback steps a₀ out :=
    CommandStackTransport.eval_shadow Hidden QueryPairControlFrame.callback_avoids hEval
  refine ⟨steps,out,heval,htime,?_,hI.rebase a₀.stacks,?_⟩
  · intro j
    fin_cases j
    · exact congrFun hsame 832
    · exact congrFun hsame 833
    · exact (hcontrol 2).trans (hshadow 834 (by decide))
    · exact (hcontrol 3).trans (hshadow 835 (by decide))
  · intro ha
    have hframe : ∀ i,Hidden i → (a₀.stacks i).length ≤ F := by
      intro i _
      rw [hsame]
      exact ha i
    have hFD : F ≤ callbackSpace s q (s.input.n-H.card) F B := by
      exact (by omega : F ≤ 896*F+startBudget s.input.n F+commitBudget q (s.input.n-H.card) F).trans
        (Nat.le_max_right _ _)
    constructor
    · intro i
      by_cases hv : Hidden i
      · change (rebaseStacks Hidden a₀.stacks b.stacks i).length ≤ F
        rw [rebaseStacks_of_mem Hidden a₀.stacks b.stacks i hv]
        exact hframe i hv
      · change (rebaseStacks Hidden a₀.stacks b.stacks i).length ≤ F
        rw [rebaseStacks_of_not_mem Hidden a₀.stacks b.stacks i hv]
        exact hb i
    · constructor
      have hp := CommandStackTransport.eval_shadow_prefix_bound Hidden
        QueryPairControlFrame.callback_avoids 838 838 hEval
        (fun elapsed cfg he ht i _ => hprefix.bound elapsed cfg he ht i) hframe
      intro elapsed cfg he ht i
      exact (hp elapsed cfg he ht i).trans (max_le (Nat.le_refl _) hFD)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_cursor_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_cursor_run_oai
