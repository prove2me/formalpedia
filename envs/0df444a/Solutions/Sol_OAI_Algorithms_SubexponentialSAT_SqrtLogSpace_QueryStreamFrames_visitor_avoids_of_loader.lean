-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.visitor_avoids_of_loader
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:46:18.342777+00:00
-- url     : https://prove2.me/submissions/33265aa5-d3a4-4b17-ab8b-a72fa1b60b0f

import Mathlib
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryStreamFrames_accepted_assignment_avoids

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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorQueryReplay
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

theorem gate_avoids : AvoidsCmd H HeadEvaluationProgram.StagedGate.command := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨copy_avoids _ _ (by decide) (by decide),
      copy_avoids _ _ (by decide) (by decide), copy_avoids _ _ (by decide) (by decide),
      copy_avoids _ _ (by decide) (by decide), copy_avoids _ _ (by decide) (by decide),
      copy_avoids _ _ (by decide) (by decide)⟩
  · apply avoids_call_lift_of_range
    intro i
    change ¬ (i.val = 320 ∨ i.val = 322)
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadStreamFrames
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

theorem key_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      SignatureKeyNative.command := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

theorem reset_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      SignatureHeadPrepare.reset := by
  refine ⟨avoids_clearProgram _ 841 0 1 (by decide),
    bank_clear_avoids _ 841 0 1 _ (by decide) ?_⟩
  intro i hi
  simp only [SignatureHeadPrepare.cleared, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem overwrite_avoids (H : Fin 896 → Prop) (src dst : Fin 896)
    (hs : ¬ H src) (hd : ¬ H dst) (ht : ¬ H 841) :
    AvoidsCmd H (QueryTupleVisitor.overwrite src dst) :=
  ⟨avoids_clearProgram H dst 0 1 hd, avoids_copyProgram H src dst 841 0 1 hs hd ht⟩

theorem masters_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      SignatureHeadPrepare.masters :=
  ⟨overwrite_avoids _ 141 864 (by decide) (by decide) (by decide),
    overwrite_avoids _ 847 865 (by decide) (by decide) (by decide),
    overwrite_avoids _ 671 175 (by decide) (by decide) (by decide)⟩

theorem select_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      NativeHeadSelect.select := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

theorem selector_command_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      NativeHeadSelect.command :=
  ⟨avoids_copyProgram _ 858 878 880 0 1 (by decide) (by decide) (by decide),
    avoids_copyProgram _ 670 879 880 0 1 (by decide) (by decide) (by decide),
    select_avoids⟩

theorem selector_reset_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      NativeHeadSelect.reset := by
  refine ⟨avoids_clearProgram _ 880 0 1 (by decide),
    bank_clear_avoids _ 880 0 1 _ (by decide) ?_⟩
  intro i hi
  simp only [NativeHeadSelect.changed, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem selector_prepare_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      NativeHeadSelect.prepare := ⟨selector_reset_avoids, selector_command_avoids⟩

theorem selector_program_avoids :
    AvoidsProgram (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      NativeHeadSelect.prepareProgram :=
  avoids_compiled _ _ selector_prepare_avoids 858 867

theorem command_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      SignatureHeadPrepare.command :=
  ⟨reset_avoids, key_avoids, masters_avoids, selector_program_avoids⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepareFootprint
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

theorem tuple_port (i : Fin 12) : ¬ H (tupleStacks i) := by
  change ¬ (836 + i.val = 320 ∨ 836 + i.val = 322)
  omega

theorem copy_avoids (src dst tmp : Fin 896)
    (hs : ¬ H src) (hd : ¬ H dst) (ht : ¬ H tmp) :
    AvoidsCmd H (copyWord src dst tmp) :=
  avoids_copyProgram H src dst tmp 0 1 hs hd ht

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

theorem pop_frame_avoids (src dst : Fin 896) (hne : src ≠ dst)
    (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (popWordCommand src dst hne) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i
  · exact hs
  · exact hd

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

theorem tuple_sum_avoids : AvoidsCmd H QueryTupleSum.command := by
  refine ⟨⟨NodeFinishReplay.prepare_avoids,
    NodeFinishReplay.clearMany_avoids H _ ?_⟩, ?_⟩
  · intro i hi
    have hh := QueryTupleSum.scratchPorts_low hi
    omega
  · apply avoids_call_lift_of_range
    intro i
    change ¬ H (QueryTupleSum.ports i)
    simp only [QueryTupleSum.ports]
    split_ifs <;> simp only [Fin.coe_ofNat_eq_mod] <;> have hi := i.isLt <;> omega

theorem tuple_clear_bank_avoids (ports : List (Fin 896))
    (hp : ∀ i ∈ ports, ¬ H i) : AvoidsCmd H (QueryTupleInit.clearBank ports) := by
  apply avoids_liftProgram
  apply avoids_compiled
  exact avoids_clearMany H ports hp

theorem tuple_end_avoids : AvoidsCmd H QueryExecution.TupleEnd.command := by
  refine ⟨tuple_sum_avoids, tuple_clear_bank_avoids _ ?_⟩
  intro i hi
  simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply tuple_port

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
  · change ¬ (i.val = 320 ∨ i.val = 322)
    have hi := i.isLt
    omega

theorem tuple_multiply_avoids : AvoidsCmd H QueryAssembler.TupleMultiply.command := by
  refine ⟨⟨NodeFinishReplay.clearMany_avoids H [61,70] ?_,
    clear_pair_avoids, environment_avoids⟩,
    tuple_multiply_call_avoids, clear_pair_avoids⟩
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl <;> decide

theorem representative_install_avoids : AvoidsCmd H QueryTupleVisitor.installRepresentative :=
  ⟨overwrite_avoids 838 859 (by decide) (by decide),
    avoids_compiled H _ HeadStreamFrames.overlay_avoids _ _,
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

theorem head_sum_avoids :
    AvoidsCmd H (HeadSumAssembly.head HeadSumAssembly.accepted) :=
  HeadStreamFrames.head_avoids _ accepted_assignment_avoids

theorem concrete_tuple_init_avoids : AvoidsCmd H QueryTupleInit.command :=
  tuple_init_avoids FactorQueryReplay.setup_avoids

theorem head_prepare_avoids : AvoidsCmd H SignatureHeadPrepare.command :=
  SignatureHeadPrepareFootprint.command_avoids

/-- The fixed visitor composes the actual two passes and all arithmetic
without any access to the suspended outer collector. -/
theorem visitor_avoids_of_loader_oai
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.visitor_avoids_of_loader_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.visitor_avoids_of_loader_oai
