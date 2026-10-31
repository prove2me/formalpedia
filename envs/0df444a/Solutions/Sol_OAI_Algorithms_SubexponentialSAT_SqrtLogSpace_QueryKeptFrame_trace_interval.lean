-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.trace_interval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:44:11.367033+00:00
-- url     : https://prove2.me/submissions/17cfe1cb-4543-4f5a-99ba-53a9a3df377f

import Mathlib
import Definitions.Def_OAIQ081S193

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Protect the target-jet caches while the source-polynomial initializer
uses the same private local ports. Source length and target jet order are
independent runtime values. These are actual copy and clear programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem lowClear_iff (i : Fin 768) :
    i∈lowClearPorts ↔ ∃j : Fin 205, j∉retainedLow ∧ lowPort j=i := by
  simp [lowClearPorts,List.mem_map,List.mem_filter]

end SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceControls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid source-control copies into the isolated 340-stack worker. All inputs
come from runtime layout/ring masters; no source polynomial is supplied. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceControls
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem mem_extraPorts (i : Fin 768) : i ∈ extraPorts ↔
    (589 ≤ i.val ∧ i.val < 593) ∨ (596 ≤ i.val ∧ i.val < 680) := by
  have hr : i ∈ (List.finRange 84).map
      (fun j => (⟨596+j.val,by omega⟩ : Fin 768)) ↔ 596 ≤ i.val ∧ i.val < 680 := by
    simp only [List.mem_map,List.mem_finRange,true_and]
    constructor
    · rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      change 596+j.val=i.val at hv
      omega
    · intro hi
      refine ⟨⟨i.val-596,by omega⟩,?_⟩
      apply Fin.ext
      change 596+(i.val-596)=i.val
      omega
  have hc : i ∈ ([589,590,591,592] : List (Fin 768)) ↔ 589 ≤ i.val ∧ i.val < 593 := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false]
    constructor
    · intro h
      rcases h with rfl|rfl|rfl|rfl <;> decide
    · intro h
      have hv : i.val=589 ∨ i.val=590 ∨ i.val=591 ∨ i.val=592 := by omega
      rcases hv with h|h|h|h
      · left; exact Fin.ext h
      · right; left; exact Fin.ext h
      · right; right; left; exact Fin.ext h
      · right; right; right; exact Fin.ext h
  simp only [extraPorts,List.mem_append,hc,hr]

end SubexponentialSAT.SqrtLog.LeafProgram.SourceControls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The selected-factor incidence service with a concrete source generator.
All ring/layout inputs are copied from persistent masters, and the complete
private worker is reclaimed after exporting the actual lookup table. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Incidence
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem mem_workerPorts (i : Fin 768) : i ∈ workerPorts ↔ 340 ≤ i.val ∧ i.val < 680 := by
  simp only [workerPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change 340+j.val=i.val at hv
    omega
  · intro hi
    refine ⟨⟨i.val-340,by omega⟩,?_⟩
    apply Fin.ext
    change 340+(i.val-340)=i.val
    omega

end SubexponentialSAT.SqrtLog.LeafProgram.Incidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryFactorKeptFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual factor and source instructions preserve caller bank744–767.
The certificate inspects the 340-stack source embedding and every staging,
cache, dispatch, arithmetic and cleanup command; a generic 768-stack lift
alone does not establish this exclusion. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryFactorKeptFrame.SourceFrames

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SqrtLog.LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

local notation "H" => (fun i : Fin 768 => 744 ≤ Fin.val i ∧ Fin.val i < 768)

theorem low_port (i : Fin 768) (hi : i.val < 744) : ¬ H i := by omega

theorem source_before_avoids : AvoidsCmd H SourceStaging.before := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_, avoids_clearMany _ _ ?_⟩
  · simp [SourceStaging.savePairs]
  · simp [SourceStaging.cachePorts]

theorem source_after_avoids : AvoidsCmd H SourceStaging.after := by
  refine ⟨avoids_clearMany _ _ ?_, avoids_copyMany _ _ _ (by decide) ?_,
    avoids_clearMany _ _ ?_, avoids_clearMany _ _ ?_⟩
  · simp [SourceStaging.cachePorts]
  · simp [SourceStaging.restorePairs]
  · simp [SourceStaging.backupPorts]
  · intro i hi
    obtain ⟨j, _, rfl⟩ := (SourceStaging.lowClear_iff i).mp hi
    exact low_port _ (by change 340 + j.val < 744; omega)

theorem source_prepare_avoids : AvoidsCmd H SourceControls.prepare := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_, True.intro, ?_⟩
  · simp [SourceControls.pairs]
  · change ¬ H 365
    decide

theorem source_cleanup_avoids : AvoidsCmd H SourceControls.cleanup := by
  apply avoids_clearMany
  intro i hi
  have hh := (SourceControls.mem_extraPorts i).mp hi
  exact low_port i (by omega)

theorem source_avoids : AvoidsCmd H Source.command := by
  refine ⟨source_before_avoids, source_prepare_avoids, ?_,
    source_after_avoids, source_cleanup_avoids⟩
  apply avoids_call_lift_of_range
  intro i
  exact low_port _ (by change 340 + i.val < 744; omega)

theorem stage_avoids : AvoidsCmd H Incidence.stage := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_,
    avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide), True.intro, ?_⟩
  · simp [Incidence.pairs]
  · change ¬ H 550
    decide

theorem export_avoids : AvoidsCmd H Incidence.exportResult := by
  refine ⟨avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide),
    avoids_clearMany _ _ ?_⟩
  intro i hi
  exact low_port i (by have hh := (Incidence.mem_workerPorts i).mp hi; omega)

namespace Table
open FactorTableProgram
local notation "HW" => (fun i : Fin 896 => 744 ≤ Fin.val i ∧ Fin.val i < 768)

theorem base_predicate (i : Fin 768) : HW (basePort i) ↔ H i := by
  simp only [basePort]
  split_ifs <;> simp_all [Fin.ext_iff, Fin.coe_ofNat_eq_mod]

theorem base_avoids (i : Fin 768) (hi : i.val < 744) : ¬ HW (basePort i) := by
  rw [base_predicate]
  omega

theorem lift_base_avoids (c : Cmd 16 768) (hc : AvoidsCmd H c) :
    AvoidsCmd HW (liftBase c) := by
  apply avoids_liftProgram
  have hp : (fun i : Fin 768 => HW (basePort i)) = H := by
    funext i
    exact propext (base_predicate i)
  change AvoidsProgram (fun i : Fin 768 => HW (basePort i)) (compiled c 0 0)
  rw [hp]
  exact avoids_compiled _ _ hc _ _

theorem inner_avoids (c : Cmd 16 256) :
    AvoidsCmd HW (liftInner c) := by
  apply avoids_liftCommand_of_range
  intro i
  change ¬ (744 ≤ 340+i.val ∧ 340+i.val < 768)
  omega

theorem specialize_avoids : AvoidsCmd HW specializeCall := by
  refine ⟨avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide), ?_⟩
  apply avoids_liftCommand_of_range
  intro i
  change ¬ (744 ≤ 340+i.val ∧ 340+i.val < 768)
  omega

theorem low_payload_avoids : AvoidsCmd HW lowPayload :=
  ⟨lift_base_avoids _ source_avoids, specialize_avoids⟩

theorem literal_payload_avoids : AvoidsCmd HW literalPayload :=
  ⟨inner_avoids _, inner_avoids _, low_payload_avoids⟩

theorem literal_iteration_avoids : AvoidsCmd HW literalIteration :=
  ⟨inner_avoids _, literal_payload_avoids, inner_avoids _⟩

theorem prepare_factor_avoids : AvoidsCmd HW prepareFactor :=
  ⟨inner_avoids _, avoids_forCmd _ _ _ (by decide) literal_iteration_avoids,
    inner_avoids _⟩

theorem entry_avoids : AvoidsCmd HW initializeWorker := by
  apply avoids_clearMany
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have hj' := (Incidence.mem_workerPorts j).mp (List.mem_filter.mp hj).1
    exact base_avoids j (by omega)
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Table

theorem command_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768) FactorTableProgram.command :=
  ⟨Table.entry_avoids, Table.lift_base_avoids _ stage_avoids,
    Table.prepare_factor_avoids, Table.lift_base_avoids _ export_avoids⟩

theorem program_avoids :
    AvoidsProgram (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768) FactorTableProgram.program :=
  avoids_compiled _ _ command_avoids _ _

theorem caller_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768) FactorTableProgram.caller :=
  avoids_liftProgram _ _ _ _ program_avoids

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryFactorKeptFrame.SourceFrames

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryFactorKeptFrame

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SqrtLog SqrtLog.LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

local notation "H" => (fun i : Fin 768 => 744 ≤ Fin.val i ∧ Fin.val i < 768)
local notation "HW" => (fun i : Fin 896 => 744 ≤ Fin.val i ∧ Fin.val i < 768)

private theorem lift_low_avoids (c : Cmd 40 768) (input output : Fin 768)
    (hc : AvoidsCmd H c) :
    AvoidsCmd HW (FactorAssignmentProgram.liftLow c input output) :=
  avoids_liftProgram _ _ _ _ (avoids_compiled H c hc input output)

private theorem cache_local_avoids : AvoidsCmd H LeafNodeCacheProgram.localCommand := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_, ?_,
    avoids_copyMany _ _ _ (by decide) ?_, avoids_clearCmd _ _ (by decide)⟩
  · simp [LeafNodeCacheProgram.copies, LeafNodeCacheProgram.directCopies]
  · apply avoids_call_lift_of_range
    intro i
    change ¬ (744 ≤ 340 + i.val ∧ 340 + i.val < 768)
    omega
  · simp

/-- The actual paid cache constructor excludes every word in bank744–767. -/
theorem setup_avoids : AvoidsCmd HW FactorAssignmentProgram.setup := by
  apply avoids_liftProgram
  exact avoids_compiled H FactorAssignmentProgram.setupLocal
    ⟨avoids_clearMany _ _ (by
      simp [FactorAssignmentProgram.cachePorts, LeafNodeCacheProgram.cachePorts,
        LeafNodeCacheProgram.pocket]), cache_local_avoids⟩ 128 69

private theorem factor_copy_avoids (src dst : Fin 768)
    (hs : ¬ H src) (hd : ¬ H dst) : AvoidsCmd H (Factor.copy src dst) :=
  avoids_copyProgram H src dst 159 0 1 hs hd (by decide)

private theorem factor_clear_avoids (src : Fin 768) (hs : ¬ H src) :
    AvoidsCmd H (Factor.clear src) := avoids_clearProgram H src 0 1 hs

private theorem factor_move_avoids (src dst : Fin 768)
    (hs : ¬ H src) (hd : ¬ H dst) : AvoidsCmd H (Factor.move src dst) :=
  ⟨factor_copy_avoids src dst hs hd, factor_clear_avoids src hs⟩

private theorem multiply_avoids : AvoidsCmd H Factor.multiply := by
  apply avoids_call_lift_of_range
  intro i
  change ¬ (744 ≤ i.val ∧ i.val < 768)
  omega

private theorem accumulate_avoids : AvoidsCmd H Factor.accumulate :=
  ⟨factor_move_avoids _ _ (by decide) (by decide),
    factor_move_avoids _ _ (by decide) (by decide), multiply_avoids,
    factor_move_avoids _ _ (by decide) (by decide)⟩

private theorem indicator_avoids : AvoidsCmd H Factor.indicator := by
  refine ⟨⟨True.intro, True.intro, True.intro⟩, ?_⟩
  apply avoids_call_lift_of_range
  decide

private theorem clause_avoids : AvoidsCmd H Clause.caller := by
  apply avoids_call_lift_of_range
  intro i
  change ¬ (744 ≤ i.val ∧ i.val < 768)
  omega

theorem hash_arithmetic_avoids : AvoidsCmd H FactorEvaluationSpace.hashArithmetic :=
  ⟨indicator_avoids, factor_clear_avoids _ (by decide),
    factor_clear_avoids _ (by decide), accumulate_avoids⟩

theorem marked_arithmetic_avoids : AvoidsCmd H FactorEvaluationSpace.markedArithmetic :=
  ⟨clause_avoids, factor_clear_avoids _ (by decide), accumulate_avoids⟩

private theorem expansion_avoids : AvoidsCmd H Expansion.forwardCommand := by
  constructor
  · intro q
    fin_cases q <;> simp [AvoidsInstr]
  · apply avoids_call_lift_of_range
    decide

private theorem factor_id_avoids : AvoidsCmd H FactorID.command :=
  ⟨avoids_copyProgram H 149 556 359 0 1 (by decide) (by decide) (by decide),
    by change ¬ H 556; decide⟩

private theorem dispatcher_avoids : AvoidsCmd H FactorDispatch.command := by
  refine ⟨⟨avoids_copyProgram H 149 152 359 0 1 (by decide) (by decide) (by decide),
    (by change ¬ H 706; decide)⟩, ?_⟩
  apply avoids_call_lift_of_range
  decide

private theorem callback_scratch_avoids :
    ∀ i ∈ FactorAssignmentProgram.callbackScratch, ¬ H i := by
  simp [FactorAssignmentProgram.callbackScratch, FactorServices.indicatorScratch,
    Factor.indicatorStacks, Factor.nativeStacks, FactorDispatch.scratch, Expansion.scratch,
    Equiv.swap_apply_def]

private theorem clear_callback_avoids : AvoidsCmd HW FactorAssignmentProgram.clearCallback := by
  apply avoids_liftProgram
  exact avoids_compiled H FactorAssignmentProgram.clearCallbackLocal
    (avoids_clearMany H _ callback_scratch_avoids) 149 149

theorem prepare_incidence_avoids :
    AvoidsCmd HW FactorAssignmentProgram.prepareIncidence :=
  ⟨lift_low_avoids _ _ _ factor_id_avoids, SourceFrames.caller_avoids⟩

private theorem choose_avoids : AvoidsCmd HW FactorAssignmentProgram.choose :=
  ⟨⟨prepare_incidence_avoids,
      lift_low_avoids _ _ _ ⟨expansion_avoids, hash_arithmetic_avoids⟩⟩,
    ⟨prepare_incidence_avoids,
      lift_low_avoids _ _ _
        ⟨factor_move_avoids _ _ (by decide) (by decide), marked_arithmetic_avoids⟩⟩,
    True.intro⟩

private theorem copy_avoids (src dst : Fin 896)
    (hs : ¬ HW src) (hd : ¬ HW dst) :
    AvoidsCmd HW (FactorAssignmentProgram.copy src dst) :=
  avoids_copyProgram HW src dst 159 0 1 hs hd (by decide)

private theorem clear_avoids (src : Fin 896) (hs : ¬ HW src) :
    AvoidsCmd HW (FactorAssignmentProgram.clear src) := avoids_clearProgram HW src 0 1 hs

private theorem move_avoids (src dst : Fin 896)
    (hs : ¬ HW src) (hd : ¬ HW dst) :
    AvoidsCmd HW (FactorAssignmentProgram.move src dst) :=
  ⟨copy_avoids src dst hs hd, clear_avoids src hs⟩

theorem callback_avoids : AvoidsCmd HW FactorAssignmentProgram.callback :=
  ⟨clear_callback_avoids, lift_low_avoids _ _ _ dispatcher_avoids,
    choose_avoids, clear_avoids _ (by decide), True.intro, True.intro, True.intro⟩

private theorem loop_avoids : AvoidsCmd HW FactorAssignmentProgram.loop :=
  avoids_record_iterate HW FactorAssignmentProgram.ports FactorAssignmentProgram.callback
    (by decide) (by decide) callback_avoids

private theorem product_avoids : AvoidsCmd HW FactorAssignmentProgram.product :=
  ⟨copy_avoids _ _ (by decide) (by decide), copy_avoids _ _ (by decide) (by decide),
    loop_avoids, move_avoids _ _ (by decide) (by decide)⟩

private theorem entry_ports_avoids : ∀ i ∈ FactorTableProgram.entryPorts, ¬ HW i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have hj' := (Incidence.mem_workerPorts j).mp (List.mem_filter.mp hj).1
    exact SourceFrames.Table.base_avoids j (by omega)
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem entry_scratch_avoids :
    ∀ i ∈ FactorAssignmentProgram.entryScratch, ¬ HW i := by
  intro i hi
  simp only [FactorAssignmentProgram.entryScratch, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact callback_scratch_avoids j hj
  · exact entry_ports_avoids i hi

private theorem initialize_avoids : AvoidsCmd HW FactorAssignmentProgram.initialize_ := by
  apply avoids_liftProgram
  exact avoids_compiled HW _ (avoids_clearMany HW _ entry_scratch_avoids) 175 854

/-- The fixed accepted-assignment implementation excludes bank744–767, including reads. -/
theorem assignment_avoids : AvoidsCmd HW FactorAssignmentProgram.assignment :=
  ⟨initialize_avoids, setup_avoids, product_avoids⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryFactorKeptFrame
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCountPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual reclamation of node-work scratch before Hermite reconstruction.
The static port set includes both the native CRT work ports and the scalar/
polynomial arithmetic readiness ports, together with the reader temporaries. Runtime data are cleared by real
stack loops; persistent node and jet inputs remain outside this set. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare

open SubexponentialSAT BitProgram StructuredCalls

private theorem ports_lt_aux (i : Fin 768) (hi : i ∈ ports) : i.val < 330 := by
  simp only [ports,List.mem_dedup,List.mem_append] at hi
  rcases hi with hi | hi
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    change j.val < 330
    omega
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with h|h|h|h|h|h|h <;> subst i <;> norm_num

theorem ports_lt (i : Fin 768) (hi : i ∈ ports) : i.val < 330 := by
  exact ports_lt_aux i hi

end SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryKeptFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete preservation of the retained interval744..767 by the fixed
conditioned query. Every certificate examines actual call ports. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.Loader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem copyMany_avoids {s : ℕ} (H : Fin s → Prop) (tmp : Fin s)
    (ps : List (Fin s × Fin s)) (ht : ¬ H tmp)
    (hp : ∀ p∈ps,¬ H p.1 ∧ ¬ H p.2) : AvoidsCmd H (copyMany tmp ps) := by
  induction ps with
  | nil => exact True.intro
  | cons p ps ih =>
    exact ⟨avoids_copyProgram H p.1 p.2 tmp 0 1 (hp p (by simp)).1
      (hp p (by simp)).2 ht,ih (fun q hq=>hp q (by norm_num [hq]))⟩

private theorem clearMany_avoids {s : ℕ} (H : Fin s → Prop) (ps : List (Fin s))
    (hp : ∀ p∈ps,¬ H p) : AvoidsCmd H (clearMany ps) := by
  induction ps with
  | nil => exact True.intro
  | cons p ps ih =>
    exact ⟨avoids_clearProgram H p 0 1 (hp p (by simp)),ih (fun q hq=>hp q (by norm_num [hq]))⟩

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
    ¬ (744 ≤ (workPort hs i).val ∧ (workPort hs i).val < 768) := by
  simp only [workPort]
  omega

private theorem stage_avoids {r s l : ℕ} (p : Program r s l) (reg : Fin r → Fin 16)
    (hs : s≤288) (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (hi : ∀ q∈ins,¬ (744 ≤ q.1.val ∧ q.1.val < 768))
    (ho : ∀ q∈outs,¬ (744 ≤ q.2.val ∧ q.2.val < 768)) :
    AvoidsCmd (fun i : Fin 768=>744 ≤ i.val ∧ i.val < 768) (stage p reg hs ins outs) := by
  let H := fun i : Fin 768=>744 ≤ i.val ∧ i.val < 768
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

theorem prepareHead_avoids :
    AvoidsCmd (fun i : Fin 768=>744 ≤ i.val ∧ i.val < 768) prepareHead := by
  refine ⟨?_,⟨?_,?_⟩,?_⟩
  · exact stage_avoids _ _ _ _ _ (by norm_num [headInputs]) (by norm_num [headOutputs])
  · exact stage_avoids _ _ _ _ _ (by norm_num [countInputs]) (by norm_num [countOutputs])
  · exact stage_avoids _ _ _ _ _ (by norm_num [scatterInputs]) (by norm_num [scatterOutputs])
  · exact stage_avoids _ _ _ _ _ (by norm_num [factorInputs]) (by norm_num [factorOutputs])

theorem bootstrap_avoids :
    AvoidsProgram (fun i : Fin 768=>744 ≤ i.val ∧ i.val < 768) SignatureHeadLoader.bootstrapProgram := by
  apply avoids_compiled
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · exact stage_avoids _ _ _ _ _ (by norm_num [addressInputs]) (by norm_num [addressOutputs])
  · exact stage_avoids _ _ _ _ _ (by norm_num [rowCountInputs]) (by norm_num [rowCountOutputs])
  · exact stage_avoids _ _ _ _ _ (by norm_num [cacheInputs]) (by norm_num [cacheOutputs])
  · exact clearMany_avoids _ retainedPorts (by norm_num [retainedPorts])
  · exact copyMany_avoids _ temporary retainedCopies (by decide) (by norm_num [retainedCopies])

theorem local_avoids :
    AvoidsProgram (fun i : Fin 768=>744 ≤ i.val ∧ i.val < 768) SignatureHeadLoader.localProgram := by
  apply avoids_compiled
  refine ⟨prepareHead_avoids,?_,?_,?_⟩
  · exact stage_avoids _ _ _ _ _ (by norm_num [SignatureHeadLoader.matrixInputs])
      (by norm_num [SignatureHeadLoader.rawOutputs])
  · exact stage_avoids _ _ _ _ _ (by norm_num [SignatureHeadLoader.shiftInputs])
      (by norm_num [SignatureHeadLoader.shiftOutputs])
  · exact avoids_clearProgram _ 669 0 1 (by decide)

theorem programFrom_avoids (src : Fin 896) (hs : ¬ (744 ≤ src.val ∧ src.val < 768)) :
    AvoidsProgram (fun i : Fin 896=>744 ≤ i.val ∧ i.val < 768) (SignatureHeadLoader.programFrom src) := by
  apply avoids_liftProgram
  apply avoids_compiled
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_⟩
  · exact clearMany_avoids _ [649,659,846,847] (by simp)
  · exact avoids_copyProgram _ src 649 659 0 1 hs (by decide) (by decide)
  · apply avoids_liftProgram
    exact local_avoids
  · exact avoids_clearProgram _ 659 0 1 (by decide)
  · exact avoids_copyProgram _ 668 847 659 0 1 (by decide) (by decide) (by decide)
  · exact clearMany_avoids _ [668,669,846] (by simp)

theorem program843_avoids :
    AvoidsProgram (fun i : Fin 896=>744 ≤ i.val ∧ i.val < 768) (SignatureHeadLoader.programFrom 843) :=
  programFrom_avoids 843 (by decide)

theorem program845_avoids :
    AvoidsProgram (fun i : Fin 896=>744 ≤ i.val ∧ i.val < 768) (SignatureHeadLoader.programFrom 845) :=
  programFrom_avoids 845 (by decide)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.Loader

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.Factor
open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SqrtLog SqrtLog.LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod
local notation "H" => (fun i : Fin 896 => 744 ≤ Fin.val i ∧ Fin.val i < 768)
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
    change ¬ (744 ≤ i.val ∧ i.val < 768)
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
  ⟨Head.overlay_avoids, QueryFactorKeptFrame.assignment_avoids, Head.accumulate_avoids⟩

theorem head_avoids : AvoidsCmd H (HeadSumAssembly.head HeadSumAssembly.accepted) :=
  Head.head_avoids _ accepted_avoids


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.Factor

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.Control

open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog
open ProgramTapeReplay

theorem lowCommand_avoids {r : ℕ} (c : Cmd r 768) (input output : Fin 768)
    (register : Fin r → Fin 40)
    (hc : AvoidsCmd (fun i : Fin 768 => 744 ≤ i.val ∧ i.val < 768) c) :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      (liftCommand c input output register (Fin.castAdd 128)) := by
  apply avoids_liftProgram
  exact avoids_compiled _ _ hc _ _

private theorem isolated_avoids {r s l : ℕ}
    (p : Program r s l) (register : Fin r → Fin 16) (stack : Fin s → Fin 896)
    (tmp : Fin 896) (ports : List (Fin 896)) (inputs outputs : List (Fin 896 × Fin 896))
    (ht : ¬ (744 ≤ tmp.val ∧ tmp.val < 768))
    (hp : ∀ i ∈ ports, ¬ (744 ≤ i.val ∧ i.val < 768))
    (hi : ∀ q ∈ inputs, ¬ (744 ≤ q.1.val ∧ q.1.val < 768) ∧
      ¬ (744 ≤ q.2.val ∧ q.2.val < 768))
    (ho : ∀ q ∈ outputs, ¬ (744 ≤ q.1.val ∧ q.1.val < 768) ∧
      ¬ (744 ≤ q.2.val ∧ q.2.val < 768))
    (hs : ∀ i, ¬ (744 ≤ (stack i).val ∧ (stack i).val < 768)) :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
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
    (ht : ¬ (744 ≤ tmp.val ∧ tmp.val < 768))
    (hp : ∀ i ∈ ports, ¬ (744 ≤ i.val ∧ i.val < 768)) :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      (BankRoutines.clearCmd tmp value present ports) := by
  induction ports with
  | nil => exact avoids_clearProgram _ tmp value present ht
  | cons i ports ih =>
    exact ⟨avoids_clearProgram _ i value present (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

theorem countCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      PairNativeSetup.countCommand := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · intro i
    fin_cases i <;> decide

theorem setupCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      PairNativeSetup.setupCommand :=
  ⟨countCommand_avoids, avoids_clearMany _ _ (by norm_num [Fin.coe_ofNat_eq_mod]),
    avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide)⟩

theorem fillCommand_avoids (isE : Bool) :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      (PairNativeSetup.fillCommand isE) := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillInput, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillOutput, Fin.coe_ofNat_eq_mod]
  · intro i
    change ¬ (744 ≤ 325+i.val ∧ 325+i.val < 768)
    omega

theorem expandCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      PairNativeSetup.expandCommand :=
  ⟨fillCommand_avoids true, fillCommand_avoids false⟩

theorem setupCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      PairNativeSetup.setupCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ setupCommand_avoids _ _)

theorem expandCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      PairNativeSetup.expandCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ expandCommand_avoids _ _)

theorem prepareHigh_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      HighQueryAdapter.prepareHigh := by
  refine ⟨⟨avoids_clearProgram _ _ _ _ (by decide),
    bankClear_avoids _ _ _ _ (by decide)
      (by norm_num [HighQueryAdapter.highChanged, Fin.coe_ofNat_eq_mod])⟩, ?_⟩
  apply avoids_liftProgram_of_range
  intro i
  fin_cases i <;> decide

theorem nativeLayoutLoad_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
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
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp ‹j ∈ SqrtLog.LeafProgram.LayoutMasters.lowPorts›
      change ¬ (744 ≤ 128+k.val ∧ 128+k.val < 768)
      omega
  · apply lowCommand_avoids
    apply avoids_liftProgram
    apply avoids_compiled
    apply avoids_copyMany
    · decide
    · intro q hq
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
      change (¬ (744 ≤ 730+j.val ∧ 730+j.val < 768)) ∧
        ¬ (744 ≤ 128+j.val ∧ 128+j.val < 768)
      omega

theorem initializeNodes_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      QueryAssembler.Nodes.initializeNodes := by
  refine ⟨lowCommand_avoids _ _ _ _ ?_, NodeFinishReplay.clearMany_avoids _ _ ?_⟩
  · exact ⟨avoids_clearProgram _ 301 0 1 (by decide),
      avoids_clearProgram _ 302 0 1 (by decide),
      avoids_clearProgram _ 305 0 1 (by decide),
      avoids_clearProgram _ 307 0 1 (by decide),
      avoids_clearProgram _ 78 0 1 (by decide),
      avoids_copyProgram _ 300 301 305 0 1 (by decide) (by decide) (by decide)⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> decide

theorem beginNode_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      QueryAssembler.Nodes.beginNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, lowCommand_avoids _ _ _ _ ?_⟩
  · intro i hi
    simp only [QueryAssembler.Nodes.nodeResetPorts, List.mem_cons, List.mem_nil_iff,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · refine ⟨?_, avoids_record_reader _ SqrtLog.LeafNodeSamplesProgram.ports
      (by decide) (by decide), avoids_transferProgram _ 302 78 0 1 (by decide) (by decide)⟩
    change ¬ (744 ≤ (301 : Fin 768).val ∧ (301 : Fin 768).val < 768)
    decide
/-- Physical readout uses only its explicit scalar bank. -/


theorem readout_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
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
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      NodeAppendSpace.prepare := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  · exact ⟨avoids_copyProgram _ 194 5 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 202 12 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 204 39 89 0 1 (by decide) (by decide) (by decide)⟩

theorem append_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      NodeAppendSpace.append :=
  ⟨avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 862 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 863 0 1 (by decide) (by decide)⟩

theorem nodeAppend_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      NodeAppendSpace.command :=
  ⟨nodeAppendPrepare_avoids, readout_avoids, append_avoids⟩

theorem finishNode_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      QueryNodeFinish.finishNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ⟨⟨True.intro, ?_⟩, ?_⟩⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl <;> decide
  · change ¬ (744 ≤ (307 : Fin 896).val ∧ (307 : Fin 896).val < 768)
    decide
  · change ¬ (744 ≤ (301 : Fin 896).val ∧ (301 : Fin 896).val < 768)
    decide

theorem nodeFinish_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      QueryNodeFinish.command := ⟨nodeAppend_avoids, finishNode_avoids⟩

theorem handoff_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      NodeAppendSpace.handoff :=
  ⟨avoids_clearProgram _ 265 0 1 (by decide),
    avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 265 0 1 (by decide) (by decide)⟩

theorem reconstruction_avoids :
    AvoidsCmd (fun i : Fin 896 => 744 ≤ i.val ∧ i.val < 768)
      QueryReconstruction.command := by
  refine ⟨handoff_avoids, lowCommand_avoids _ _ _ _ ⟨?_, ?_⟩⟩
  · unfold SqrtLog.LeafProgram.Count.Prepare.command
    generalize hports : SqrtLog.LeafProgram.Count.Prepare.ports = ports
    refine ⟨avoids_clearProgram _ 699 0 1 (by decide), ?_⟩
    have clear (ps : List (Fin 768))
        (hp : ∀ i ∈ ps, ¬ (744 ≤ i.val ∧ i.val < 768)) :
        AvoidsCmd (fun i : Fin 768 => 744 ≤ i.val ∧ i.val < 768)
          (BankRoutines.clearCmd 699 (0 : Fin 40) 1 ps) := by
      induction ps with
      | nil => exact avoids_clearProgram _ 699 0 1 (by decide)
      | cons i ps ih =>
          exact ⟨avoids_clearProgram _ i 0 1 (hp i (by simp)),
            ih (fun j hj => hp j (by simp [hj]))⟩
    exact clear ports (by
      intro i hi
      rw [← hports] at hi
      have hh := SqrtLog.LeafProgram.Count.Prepare.ports_lt i hi
      omega)
  · refine ⟨?_, ?_, avoids_clearProgram _ 5 0 1 (by decide),
      avoids_clearProgram _ 10 0 1 (by decide)⟩
    · apply avoids_call_lift_of_range
      intro i
      change ¬ (744 ≤ i.val ∧ i.val < 768)
      omega
    · apply avoids_call_lift_of_range
      intro i
      change ¬ (744 ≤ i.val ∧ i.val < 768)
      omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.Control

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

local notation "H" => (fun i : Fin 896 => 744 ≤ Fin.val i ∧ Fin.val i < 768)

theorem tuple_port (i : Fin 12) : ¬ H (tupleStacks i) := by
  change ¬ (744 ≤ 836 + i.val ∧ 836 + i.val < 768)
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
  fin_cases i <;> decide

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
  · change ¬ (744 ≤ i.val ∧ i.val < 768)
    have hi := i.isLt
    omega

theorem tuple_multiply_avoids : AvoidsCmd H QueryAssembler.TupleMultiply.command := by
  refine ⟨⟨NodeFinishReplay.clearMany_avoids H [61,70] ?_,
    clear_pair_avoids, environment_avoids⟩,
    tuple_multiply_call_avoids, clear_pair_avoids⟩
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl <;> decide


theorem tuple_sum_avoids : AvoidsCmd H QueryTupleSum.command := by
  refine ⟨⟨Control.nodeAppendPrepare_avoids,
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
  ⟨clear_avoids 851 (by decide), Control.expandCaller_avoids⟩

theorem representative_install_avoids : AvoidsCmd H QueryTupleVisitor.installRepresentative :=
  ⟨overwrite_avoids 838 859 (by decide) (by decide),
    avoids_compiled H _ (Factor.Head.overlay_avoids) _ _,
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
  Factor.head_avoids

theorem concrete_tuple_init_avoids : AvoidsCmd H QueryTupleInit.command :=
  tuple_init_avoids (QueryFactorKeptFrame.setup_avoids)

theorem head_prepare_avoids : AvoidsCmd H SignatureHeadPrepare.command :=
  Factor.Prepare.command_avoids

/-- The fixed visitor composes the actual two passes and all arithmetic
without any access to the retained interval744..767. -/
theorem visitor_avoids_of_loader
    (hload : AvoidsProgram H (SignatureHeadLoader.programFrom 843)) :
    AvoidsCmd H QueryVisitorProgram.visitor := by
  have hload' := SafeAvoids.call hload
  have hbaselineSafe := hload'.seq (SafeAvoids.intro representative_install_avoids)
  have hbaseline : AvoidsCmd H QueryVisitorProgram.baselineHead := by
    have hpack : ∃ c, c = QueryVisitorProgram.baselineHead ∧ SafeAvoids c := by
      refine ⟨_, ?_, hbaselineSafe⟩
      rw [QueryVisitorProgram.baselineHead]
    obtain ⟨_, rfl, hc⟩ := hpack
    exact hc.proof
  have hevaluateSafe := hload'.seq ((SafeAvoids.intro head_prepare_avoids).seq
    ((SafeAvoids.intro head_sum_avoids).seq (SafeAvoids.intro tuple_multiply_avoids)))
  have hevaluate : AvoidsCmd H QueryVisitorProgram.evaluateHead := by
    have hpack : ∃ c, c = QueryVisitorProgram.evaluateHead ∧ SafeAvoids c := by
      refine ⟨_, ?_, hevaluateSafe⟩
      rw [QueryVisitorProgram.evaluateHead, QueryVisitorProgram.loadHead,
        QueryVisitorProgram.evaluateLoadedHead]
    obtain ⟨_, rfl, hc⟩ := hpack
    exact hc.proof
  have hvisitor := (SafeAvoids.intro concrete_tuple_init_avoids).seq
    ((SafeAvoids.intro hbaseline).replay.seq
      ((SafeAvoids.intro hevaluate).replay.seq (SafeAvoids.intro tuple_end_avoids)))
  have hpack : ∃ c, c = QueryVisitorProgram.visitor ∧ SafeAvoids c := by
    refine ⟨_, ?_, hvisitor⟩
    rw [QueryVisitorProgram.visitor]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc.proof

theorem tuple_avoids_of_loader
    (hload : AvoidsProgram H (SignatureHeadLoader.programFrom 845))
    (hvisit : AvoidsCmd H QueryVisitorProgram.visitor) :
    AvoidsCmd H SignatureTupleComplete.command := by
  have htuple := (SafeAvoids.call hload).tupleController
    (SafeAvoids.intro candidate_avoids) (SafeAvoids.intro hvisit)
  have hpack : ∃ c, c = SignatureTupleComplete.command ∧ SafeAvoids c := by
    refine ⟨_, ?_, htuple⟩
    rw [SignatureTupleComplete.command, SignatureTupleComplete.routines,
      SignatureTupleLoader.loadHead, SignatureTupleLoader.headAddress]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc.proof


theorem visitor_avoids : AvoidsCmd H QueryVisitorProgram.visitor :=
  visitor_avoids_of_loader Loader.program843_avoids

theorem tuple_avoids : AvoidsCmd H SignatureTupleComplete.command :=
  tuple_avoids_of_loader Loader.program845_avoids visitor_avoids

theorem pair_callback_avoids : AvoidsCmd H QueryStreamProgram.pairCallback :=
  ⟨pair_start_avoids, tuple_avoids, commit_pair_avoids⟩

theorem pairs_avoids : AvoidsCmd H QueryStreamProgram.pairs := by
  apply QueryElementaryReplay.differenceCommand_avoids
  · intro i
    change ¬ (744 ≤ 832+i.val ∧ 832+i.val < 768)
    omega
  · exact pair_callback_avoids


theorem bootstrap_avoids : AvoidsCmd H QueryStreamProgram.bootstrapNode := by
  apply avoids_liftProgram
  exact Loader.bootstrap_avoids

theorem node_body_avoids : AvoidsCmd H QueryStreamProgram.nodeBody :=
  ⟨Control.beginNode_avoids,
    Control.nativeLayoutLoad_avoids, bootstrap_avoids,
    Control.setupCaller_avoids, pairs_avoids,
    Control.nodeFinish_avoids⟩

theorem nodes_avoids : AvoidsCmd H QueryStreamProgram.nodes := by
  refine ⟨Control.initializeNodes_avoids, ?_, node_body_avoids⟩
  change ¬ H 301
  decide

/-- The actual fixed conditioned query excludes the retained interval744..767,
including every invoked table and every peek. -/
theorem command_avoids : AvoidsCmd H QueryStreamProgram.command :=
  ⟨Control.prepareHigh_avoids, nodes_avoids,
    Control.reconstruction_avoids⟩

theorem program_avoids : AvoidsProgram H QueryStreamProgram.program :=
  avoids_compiled H _ command_avoids 330 323


/-- Actual instruction avoidance preserves a word at every trace prefix.
No successful-run or evaluator premise is required. -/
theorem trace_avoided {r s l steps : ℕ} (K : Fin s → Prop) [DecidablePred K]
    {p : Program r s l} (hp : AvoidsProgram K p) {a b : Cfg r s l}
    (ht : Trace p steps a b) (i : Fin s) (hi : K i) :
    b.stacks i = a.stacks i := by
  have ha : rebaseCfg K a.stacks a = a := by
    cases a with
    | mk pc regs words =>
        apply congrArg (fun ws => (⟨pc, regs, ws⟩ : Cfg r s l))
        funext j
        simp [rebaseStacks]
  have hr := trace_rebase K hp ht a.stacks
  rw [ha] at hr
  have hu := trace_same_length_unique ht hr
  have hw := congrArg (fun c => c.stacks i) hu
  simpa [rebaseCfg, rebaseStacks, hi] using hw

/-- The previously uncovered retained interval is unchanged inside every call. -/
theorem trace_interval_oai {steps : ℕ}
    {a b : Cfg 40 896 (size QueryStreamProgram.command + 1)}
    (ht : Trace QueryStreamProgram.program steps a b)
    (i : Fin 896) (hlo : 744 ≤ i.val) (hhi : i.val < 768) :
    b.stacks i = a.stacks i := trace_avoided H program_avoids ht i ⟨hlo,hhi⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.trace_interval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.trace_interval_oai
