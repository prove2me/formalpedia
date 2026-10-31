-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame.eval_top
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:56:28.026788+00:00
-- url     : https://prove2.me/submissions/a29e57bf-4d16-4f69-8359-457ca0db0ba3

import Mathlib
import Definitions.Def_OAIQ081S193

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

/-- All four real controller tapes and the actual callback account for every
read or write, including strict-budget peeks in the pruned DFS. -/
theorem differenceCommand_avoids {r s : ℕ} (H : Fin s → Prop)
    (p : DifferencePairsProgram.Ports r s) (callback : Cmd r s)
    (hp : ∀ i, ¬ H (p.stack i)) (hc : AvoidsCmd H callback) :
    AvoidsCmd H (DifferencePairsProgram.command p callback) := by
  simp [DifferencePairsProgram.command, DifferencePairsProgram.body,
    DifferencePairsProgram.descend, DifferencePairsProgram.backtrack,
    DifferencePairsProgram.nextOutside, DifferencePairsProgram.finishLevel,
    DifferencePairsProgram.enter, DifferencePairsProgram.pushBit,
    DifferencePairsProgram.atoms, AvoidsCmd, AvoidsBase, AvoidsAtom, hp, hc]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryElementaryReplay
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTopFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual conditioned stream never reads, peeks or writes stack895.
The fixed source-table, factor, head, loader and controller maps are checked
explicitly; no callback footprint or successful execution is assumed. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame.Factor
open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SqrtLog SqrtLog.LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

local notation "H" => (fun i : Fin 896 => Fin.val i = 895)

theorem low_port (i : Fin 768) : ¬ H (FactorAssignmentProgram.lowStack i) := by
  change ¬ (i.val = 895)
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
  change ¬ (340+i.val = 895)
  omega

theorem specialize_avoids : AvoidsCmd H specializeCall := by
  refine ⟨avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide), ?_⟩
  apply avoids_liftCommand_of_range
  intro i
  change ¬ (340+i.val = 895)
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
    change ¬ (i.val = 895)
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame.Factor

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame.Control

open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog
open ProgramTapeReplay

/-- Every actual instruction of a lifted lower-bank program is disjoint from
the reserved top stack. -/
theorem lowProgram_avoids {r l : ℕ} (p : Program r 768 l)
    (register : Fin r → Fin 40) :
    AvoidsProgram (fun i : Fin 896 => i.val = 895)
      (ProgramLinking.liftProgram p register (Fin.castAdd 128)) := by
  apply avoids_liftProgram_of_range
  intro i hi
  change i.val = 895 at hi
  omega

theorem lowCommand_avoids {r : ℕ} (c : Cmd r 768) (input output : Fin 768)
    (register : Fin r → Fin 40) :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      (liftCommand c input output register (Fin.castAdd 128)) :=
  lowProgram_avoids (compiled c input output) register

private theorem isolated_avoids {r s l : ℕ}
    (p : Program r s l) (register : Fin r → Fin 16) (stack : Fin s → Fin 896)
    (tmp : Fin 896) (ports : List (Fin 896)) (inputs outputs : List (Fin 896 × Fin 896))
    (ht : ¬ (tmp.val = 895))
    (hp : ∀ i ∈ ports, ¬ (i.val = 895))
    (hi : ∀ q ∈ inputs, ¬ (q.1.val = 895) ∧
      ¬ (q.2.val = 895))
    (ho : ∀ q ∈ outputs, ¬ (q.1.val = 895) ∧
      ¬ (q.2.val = 895))
    (hs : ∀ i, ¬ ((stack i).val = 895)) :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
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
    (ht : ¬ (tmp.val = 895))
    (hp : ∀ i ∈ ports, ¬ (i.val = 895)) :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      (BankRoutines.clearCmd tmp value present ports) := by
  induction ports with
  | nil => exact avoids_clearProgram _ tmp value present ht
  | cons i ports ih =>
    exact ⟨avoids_clearProgram _ i value present (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

theorem countCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      PairNativeSetup.countCommand := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · intro i
    fin_cases i <;> decide

theorem setupCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      PairNativeSetup.setupCommand :=
  ⟨countCommand_avoids, avoids_clearMany _ _ (by norm_num [Fin.coe_ofNat_eq_mod]),
    avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide)⟩

theorem fillCommand_avoids (isE : Bool) :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      (PairNativeSetup.fillCommand isE) := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillInput, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillOutput, Fin.coe_ofNat_eq_mod]
  · intro i
    change ¬ (325+i.val = 895)
    omega

theorem expandCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      PairNativeSetup.expandCommand :=
  ⟨fillCommand_avoids true, fillCommand_avoids false⟩

theorem setupCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      PairNativeSetup.setupCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ setupCommand_avoids _ _)

theorem expandCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      PairNativeSetup.expandCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ expandCommand_avoids _ _)

theorem prepareHigh_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      HighQueryAdapter.prepareHigh := by
  refine ⟨⟨avoids_clearProgram _ _ _ _ (by decide),
    bankClear_avoids _ _ _ _ (by decide)
      (by norm_num [HighQueryAdapter.highChanged, Fin.coe_ofNat_eq_mod])⟩, ?_⟩
  apply avoids_liftProgram_of_range
  intro i
  fin_cases i <;> decide

theorem nativeLayoutLoad_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
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
      change ¬ (j.val = 895)
      omega
  · exact lowCommand_avoids _ _ _ _

theorem initializeNodes_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      QueryAssembler.Nodes.initializeNodes := by
  refine ⟨lowCommand_avoids _ _ _ _, NodeFinishReplay.clearMany_avoids _ _ ?_⟩
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> decide

theorem beginNode_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      QueryAssembler.Nodes.beginNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, lowCommand_avoids _ _ _ _⟩
  intro i hi
  simp only [QueryAssembler.Nodes.nodeResetPorts, List.mem_cons, List.mem_nil_iff,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem readout_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
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
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      NodeAppendSpace.prepare := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  · exact ⟨avoids_copyProgram _ 194 5 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 202 12 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 204 39 89 0 1 (by decide) (by decide) (by decide)⟩

theorem append_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      NodeAppendSpace.append :=
  ⟨avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 862 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 863 0 1 (by decide) (by decide)⟩

theorem nodeAppend_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      NodeAppendSpace.command :=
  ⟨nodeAppendPrepare_avoids, readout_avoids, append_avoids⟩

theorem finishNode_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      QueryNodeFinish.finishNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ⟨⟨True.intro, ?_⟩, ?_⟩⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl <;> decide
  · change ¬ ((307 : Fin 896).val = 895)
    decide
  · change ¬ ((301 : Fin 896).val = 895)
    decide

theorem nodeFinish_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      QueryNodeFinish.command := ⟨nodeAppend_avoids, finishNode_avoids⟩

theorem handoff_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      NodeAppendSpace.handoff :=
  ⟨avoids_clearProgram _ 265 0 1 (by decide),
    avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 265 0 1 (by decide) (by decide)⟩

theorem reconstruction_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 895)
      QueryReconstruction.command := ⟨handoff_avoids, lowCommand_avoids _ _ _ _⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame.Control

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

local notation "H" => (fun i : Fin 896 => Fin.val i = 895)

theorem tuple_port (i : Fin 12) : ¬ H (tupleStacks i) := by
  change ¬ (836 + i.val = 895)
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

private theorem SafeAvoids.difference (p : DifferencePairsProgram.Ports 40 896)
    {callback : Cmd 40 896} (hc : SafeAvoids callback)
    (hp : ∀ i, ¬ H (p.stack i)) :
    SafeAvoids (DifferencePairsProgram.command p callback) :=
  SafeAvoids.intro
    (QueryElementaryReplay.differenceCommand_avoids H p callback hp hc.proof)

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
  change ¬ ((if i.val = 0 then 141 else if i.val = 15 then 847 else
    if i.val = 16 then 838 else if i.val = 17 then 839 else
    if i.val = 18 then 844 else 340 + i.val) = 895)
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
  · change ¬ (i.val = 895)
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
    (hp : ∀ p ∈ ps, ¬ (p.val = 895)) :
    AvoidsCmd (fun i : Fin 896 => i.val = 895) (clearMany ps) := by
  induction ps with
  | nil => exact True.intro
  | cons p ps ih =>
    exact ⟨avoids_clearProgram _ p 0 1 (hp p (by simp)),
      ih (fun q hq => hp q (by simp [hq]))⟩

theorem lower_avoids {r l : ℕ} (p : Program r 768 l) (reg : Fin r → Fin 40) :
    AvoidsProgram (fun i : Fin 896 => i.val = 895)
      (ProgramLinking.liftProgram p reg SignatureHeadLoader.lowStacks) := by
  apply avoids_liftProgram_of_range
  intro i hi
  have hv := i.isLt
  change i.val = 895 at hi
  omega

theorem programFrom_avoids (src : Fin 896) (hs : ¬ (src.val = 895)) :
    AvoidsProgram (fun i : Fin 896 => i.val = 895)
      (SignatureHeadLoader.programFrom src) := by
  apply avoids_liftProgram
  apply avoids_compiled
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_⟩
  · exact loader_clearMany_avoids [649,659,846,847] (by norm_num [Fin.coe_ofNat_eq_mod])
  · exact avoids_copyProgram _ src 649 659 0 1 hs (by decide) (by decide)
  · apply avoids_liftProgram_of_range
    intro i hi
    have hv := i.isLt
    change i.val = 895 at hi
    omega
  · exact avoids_clearProgram _ 659 0 1 (by decide)
  · exact avoids_copyProgram _ 668 847 659 0 1 (by decide) (by decide) (by decide)
  · exact loader_clearMany_avoids [668,669,846] (by norm_num [Fin.coe_ofNat_eq_mod])

theorem program843_avoids :
    AvoidsProgram (fun i : Fin 896 => i.val = 895)
      (SignatureHeadLoader.programFrom 843) := programFrom_avoids 843 (by decide)

theorem program845_avoids :
    AvoidsProgram (fun i : Fin 896 => i.val = 895)
      (SignatureHeadLoader.programFrom 845) := programFrom_avoids 845 (by decide)


theorem tuple_sum_avoids : AvoidsCmd H QueryTupleSum.command := by
  refine ⟨⟨QueryTopFrame.Control.nodeAppendPrepare_avoids,
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
  ⟨clear_avoids 851 (by decide), QueryTopFrame.Control.expandCaller_avoids⟩

theorem representative_install_avoids : AvoidsCmd H QueryTupleVisitor.installRepresentative :=
  ⟨overwrite_avoids 838 859 (by decide) (by decide),
    avoids_compiled H _ (QueryTopFrame.Factor.Head.overlay_avoids) _ _,
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
  QueryTopFrame.Factor.head_avoids

theorem concrete_tuple_init_avoids : AvoidsCmd H QueryTupleInit.command :=
  tuple_init_avoids (QueryTopFrame.Factor.setup_avoids)

theorem head_prepare_avoids : AvoidsCmd H SignatureHeadPrepare.command :=
  QueryTopFrame.Factor.Prepare.command_avoids

/-- The fixed visitor composes the actual two passes and all arithmetic
without any access to the reserved top stack. -/
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

private theorem pairCallback_safe : SafeAvoids QueryStreamProgram.pairCallback := by
  let hs := (SafeAvoids.intro (c := QueryExecution.PairStart.command)
      pair_start_avoids).seq
    (tuple_safe.seq (SafeAvoids.intro (c := QueryAssembler.commitPair)
      commit_pair_avoids))
  have hpack : ∃ c, c = QueryStreamProgram.pairCallback ∧ SafeAvoids c := by
    refine ⟨_, ?_, hs⟩
    rw [QueryStreamProgram.pairCallback]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc

private theorem pairs_safe : SafeAvoids QueryStreamProgram.pairs := by
  have hp : ∀ i, ¬ H (QueryStreamProgram.pairPorts.stack i) := by
    intro i
    change ¬ (832 + i.val = 895)
    omega
  let hs := pairCallback_safe.difference QueryStreamProgram.pairPorts hp
  have hpack : ∃ c, c = QueryStreamProgram.pairs ∧ SafeAvoids c := by
    refine ⟨_, ?_, hs⟩
    rw [QueryStreamProgram.pairs]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc

theorem pairs_avoids : AvoidsCmd H QueryStreamProgram.pairs := pairs_safe.proof


theorem bootstrap_avoids : AvoidsCmd H QueryStreamProgram.bootstrapNode :=
  lower_avoids SignatureHeadLoader.bootstrapProgram SignatureHeadLoader.leafRegs

theorem node_body_avoids : AvoidsCmd H QueryStreamProgram.nodeBody :=
  ⟨QueryTopFrame.Control.beginNode_avoids,
    QueryTopFrame.Control.nativeLayoutLoad_avoids, bootstrap_avoids,
    QueryTopFrame.Control.setupCaller_avoids, pairs_avoids,
    QueryTopFrame.Control.nodeFinish_avoids⟩

theorem nodes_avoids : AvoidsCmd H QueryStreamProgram.nodes := by
  refine ⟨QueryTopFrame.Control.initializeNodes_avoids, ?_, node_body_avoids⟩
  change ¬ H 301
  decide

/-- The actual fixed conditioned query excludes stack895, including every
invoked table and every peek. -/
theorem command_avoids : AvoidsCmd H QueryStreamProgram.command :=
  ⟨QueryTopFrame.Control.prepareHigh_avoids, nodes_avoids,
    QueryTopFrame.Control.reconstruction_avoids⟩

theorem program_avoids : AvoidsProgram H QueryStreamProgram.program :=
  avoids_compiled H _ command_avoids 330 323

/-- Every actual prefix preserves the entire reserved word, including prefixes
inside the finite subprogram calls. No halting premise is required. -/
theorem trace_top {steps : ℕ}
    {a b : Cfg 40 896 (size QueryStreamProgram.command + 1)}
    (ht : Trace QueryStreamProgram.program steps a b) :
    b.stacks 895 = a.stacks 895 := by
  have ha : rebaseCfg H a.stacks a = a := by
    cases a with
    | mk pc regs words =>
        apply congrArg (fun ws => (⟨pc, regs, ws⟩ : Cfg 40 896 (size QueryStreamProgram.command + 1)))
        funext i
        simp [rebaseStacks]
  have hr := trace_rebase H program_avoids ht a.stacks
  rw [ha] at hr
  have hu := trace_same_length_unique ht hr
  have hw := congrArg (fun c => c.stacks 895) hu
  simpa [rebaseCfg, rebaseStacks] using hw

/-- The actual fixed conditioned stream preserves stack895 at its endpoint. -/
theorem eval_top_oai {steps : ℕ} {a b : State 40 896}
    (he : Eval QueryStreamProgram.command steps a b) :
    b.stacks 895 = a.stacks 895 :=
  trace_top (compiled_halt_trace he 330 323)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame.eval_top_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame.eval_top_oai
