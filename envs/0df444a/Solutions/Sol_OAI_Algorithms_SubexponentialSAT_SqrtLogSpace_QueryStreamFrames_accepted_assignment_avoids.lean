-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.accepted_assignment_avoids
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:42:52.654722+00:00
-- url     : https://prove2.me/submissions/8058b1b0-154c-4ea1-9621-949774fec35a

import Mathlib
import Definitions.Def_OAIQ081S191

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QuerySourceReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual source-emitter reads and writes exclude the two collector tapes.
The exclusion includes staging, restoration, arithmetic calls and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceReplay

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SqrtLog.LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

local notation "H" => (fun i : Fin 768 => Fin.val i = 320 ∨ Fin.val i = 322)

theorem high_port (i : Fin 768) (hi : 340 ≤ i.val) : ¬ H i := by omega

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
    exact high_port _ (by change 340 ≤ 340 + j.val; omega)

theorem source_prepare_avoids : AvoidsCmd H SourceControls.prepare := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_, True.intro, ?_⟩
  · simp [SourceControls.pairs]
  · change ¬ H 365
    decide

theorem source_cleanup_avoids : AvoidsCmd H SourceControls.cleanup := by
  apply avoids_clearMany
  intro i hi
  have hh := (SourceControls.mem_extraPorts i).mp hi
  exact high_port i (by omega)

theorem source_avoids : AvoidsCmd H Source.command := by
  refine ⟨source_before_avoids, source_prepare_avoids, ?_,
    source_after_avoids, source_cleanup_avoids⟩
  apply avoids_call_lift_of_range
  intro i
  exact high_port _ (by change 340 ≤ 340 + i.val; omega)

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
  exact high_port i ((Incidence.mem_workerPorts i).mp hi).1

namespace Table
open FactorTableProgram
local notation "HW" => (fun i : Fin 896 => Fin.val i = 320 ∨ Fin.val i = 322)

theorem base_predicate (i : Fin 768) : HW (basePort i) ↔ H i := by
  simp only [basePort]
  split_ifs <;> simp_all [Fin.ext_iff, Fin.coe_ofNat_eq_mod]

theorem base_high (i : Fin 768) (hi : 340 ≤ i.val) : 340 ≤ (basePort i).val := by
  simp only [basePort]
  split_ifs <;> simp_all [Fin.coe_ofNat_eq_mod]

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
  change ¬ (340+i.val=320 ∨ 340+i.val=322)
  omega

theorem specialize_avoids : AvoidsCmd HW specializeCall := by
  refine ⟨avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide), ?_⟩
  apply avoids_liftCommand_of_range
  intro i
  change ¬ (340+i.val=320 ∨ 340+i.val=322)
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
    have hh := base_high j hj'.1
    omega
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Table

theorem command_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322) FactorTableProgram.command :=
  ⟨Table.entry_avoids, Table.lift_base_avoids _ stage_avoids,
    Table.prepare_factor_avoids, Table.lift_base_avoids _ export_avoids⟩

theorem program_avoids :
    AvoidsProgram (fun i : Fin 896 => i.val=320 ∨ i.val=322) FactorTableProgram.program :=
  avoids_compiled _ _ command_avoids _ _

theorem caller_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322) FactorTableProgram.caller :=
  avoids_liftProgram _ _ _ _ program_avoids

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceReplay
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorQueryReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual assignment program neither reads nor writes collector tapes320
and322. Certificates include the cache constructor, dispatcher peeks, source
specialization, arithmetic, parser iterations and all cleanup instructions. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorQueryReplay

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SqrtLog SqrtLog.LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

local notation "H" => (fun i : Fin 768 => Fin.val i = 320 ∨ Fin.val i = 322)
local notation "HW" => (fun i : Fin 896 => Fin.val i = 320 ∨ Fin.val i = 322)

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
    change ¬ (340 + i.val = 320 ∨ 340 + i.val = 322)
    omega
  · simp

/-- The concrete constant encoder and every paid cache copy avoid the
collector words, including any temporary reads in their implementations. -/
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
  change ¬ (i.val = 320 ∨ i.val = 322)
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
  change ¬ (i.val = 320 ∨ i.val = 322)
  omega

private theorem hash_arithmetic_avoids : AvoidsCmd H FactorEvaluationSpace.hashArithmetic :=
  ⟨indicator_avoids, factor_clear_avoids _ (by decide),
    factor_clear_avoids _ (by decide), accumulate_avoids⟩

private theorem marked_arithmetic_avoids : AvoidsCmd H FactorEvaluationSpace.markedArithmetic :=
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

private theorem prepare_incidence_avoids :
    AvoidsCmd HW FactorAssignmentProgram.prepareIncidence :=
  ⟨lift_low_avoids _ _ _ factor_id_avoids, QuerySourceReplay.caller_avoids⟩

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
    have hh := QuerySourceReplay.Table.base_high j hj'.1
    omega
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

/-- No tape operation in the fixed accepted-assignment implementation touches
an outer collector tape. This includes reads, not only final-state framing. -/
theorem assignment_avoids : AvoidsCmd HW FactorAssignmentProgram.assignment :=
  ⟨initialize_avoids, setup_avoids, product_avoids⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorQueryReplay
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadStreamFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual head scan neither reads nor writes the retained collector words.
This syntactic certificate supports replay with exactly the same number of steps. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadStreamFrames
open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open HeadSumProgram
open HeadEvaluationProgram.StagedGate (copy clear)

local notation "H" => (fun i : Fin 896 => Fin.val i = 320 ∨ Fin.val i = 322)

private theorem bank_clear_avoids (tmp : Fin 896) (ports : List (Fin 896))
    (ht : ¬ H tmp) (hp : ∀ i ∈ ports, ¬ H i) :
    AvoidsCmd H (BankRoutines.clearCmd tmp (0 : Fin 40) 1 ports) := by
  induction ports with
  | nil => exact avoids_clearProgram H tmp 0 1 ht
  | cons i ports ih =>
    exact ⟨avoids_clearProgram H i 0 1 (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadStreamFrames
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

/-- All accepted assignments use the actual fixed factor command; the
collector frame is excluded even from dispatcher and arithmetic reads. -/
theorem accepted_assignment_avoids_oai : AvoidsCmd H HeadSumAssembly.accepted :=
  ⟨HeadStreamFrames.overlay_avoids, FactorQueryReplay.assignment_avoids,
    HeadStreamFrames.accumulate_avoids⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.accepted_assignment_avoids_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.accepted_assignment_avoids_oai
