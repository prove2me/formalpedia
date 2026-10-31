-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.pairs_avoids
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:45:09.924312+00:00
-- url     : https://prove2.me/submissions/310ca8b9-43ef-458f-8586-ea3732e3577f

import Mathlib
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryStreamFrames_visitor_avoids_of_loader

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

theorem fillCommand_avoids (isE : Bool) :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      (PairNativeSetup.fillCommand isE) := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillInput, Fin.coe_ofNat_eq_mod]
  · cases isE <;> norm_num [PairNativeSetup.fillOutput, Fin.coe_ofNat_eq_mod]
  · intro i
    change ¬ (325+i.val=320 ∨ 325+i.val=322)
    omega

theorem expandCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      PairNativeSetup.expandCommand :=
  ⟨fillCommand_avoids true, fillCommand_avoids false⟩

theorem expandCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val=320 ∨ i.val=322)
      PairNativeSetup.expandCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ expandCommand_avoids _ _)

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

theorem prepareHead_avoids :
    AvoidsCmd (fun i : Fin 768=>i=320 ∨ i=322) prepareHead := by
  refine ⟨?_,⟨?_,?_⟩,?_⟩
  · exact stage_avoids _ _ _ _ _ (by simp [headInputs]) (by simp [headOutputs])
  · exact stage_avoids _ _ _ _ _ (by simp [countInputs]) (by simp [countOutputs])
  · exact stage_avoids _ _ _ _ _ (by simp [scatterInputs]) (by simp [scatterOutputs])
  · exact stage_avoids _ _ _ _ _ (by simp [factorInputs]) (by simp [factorOutputs])

theorem local_avoids :
    AvoidsProgram (fun i : Fin 768=>i=320 ∨ i=322) SignatureHeadLoader.localProgram := by
  apply avoids_compiled
  refine ⟨prepareHead_avoids,?_,?_,?_⟩
  · exact stage_avoids _ _ _ _ _ (by simp [SignatureHeadLoader.matrixInputs])
      (by simp [SignatureHeadLoader.rawOutputs])
  · exact stage_avoids _ _ _ _ _ (by simp [SignatureHeadLoader.shiftInputs])
      (by simp [SignatureHeadLoader.shiftOutputs])
  · exact avoids_clearProgram _ 669 0 1 (by decide)

theorem programFrom_avoids (src : Fin 896) (hs : src≠320) (ht : src≠322) :
    AvoidsProgram (fun i : Fin 896=>i=320 ∨ i=322) (SignatureHeadLoader.programFrom src) := by
  apply avoids_liftProgram
  apply avoids_compiled
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_⟩
  · exact clearMany_avoids _ [649,659,846,847] (by simp)
  · exact avoids_copyProgram _ src 649 659 0 1 (by simp [hs,ht]) (by decide) (by decide)
  · apply avoids_liftProgram
    change AvoidsProgram
      (fun i : Fin 768 => SignatureHeadLoader.lowStacks i = 320 ∨
        SignatureHeadLoader.lowStacks i = 322) SignatureHeadLoader.localProgram
    have hpred :
        (fun i : Fin 768 => SignatureHeadLoader.lowStacks i = 320 ∨
          SignatureHeadLoader.lowStacks i = 322) =
        (fun i : Fin 768 => i = 320 ∨ i = 322) := by
      funext i
      apply propext
      constructor
      · intro h
        rcases h with h | h
        · left
          apply Fin.ext
          have hv := congrArg Fin.val h
          change i.val = 320 at hv
          exact hv
        · right
          apply Fin.ext
          have hv := congrArg Fin.val h
          change i.val = 322 at hv
          exact hv
      · intro h
        rcases h with rfl | rfl
        · left
          apply Fin.ext
          rfl
        · right
          apply Fin.ext
          rfl
    rw [hpred]
    exact local_avoids
  · exact avoids_clearProgram _ 659 0 1 (by decide)
  · exact avoids_copyProgram _ 668 847 659 0 1 (by decide) (by decide) (by decide)
  · exact clearMany_avoids _ [668,669,846] (by simp)

theorem program843_avoids :
    AvoidsProgram (fun i : Fin 896=>i=320 ∨ i=322) (SignatureHeadLoader.programFrom 843) :=
  programFrom_avoids 843 (by decide) (by decide)

theorem program845_avoids :
    AvoidsProgram (fun i : Fin 896=>i=320 ∨ i=322) (SignatureHeadLoader.programFrom 845) :=
  programFrom_avoids 845 (by decide) (by decide)

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

theorem tuple_port (i : Fin 12) : ¬ H (tupleStacks i) := by
  change ¬ (836 + i.val = 320 ∨ 836 + i.val = 322)
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
  change ¬ ((if i.val = 0 then 141 else if i.val = 15 then 847 else
    if i.val = 16 then 838 else if i.val = 17 then 839 else
    if i.val = 18 then 844 else 340 + i.val) = 320 ∨
    (if i.val = 0 then 141 else if i.val = 15 then 847 else
      if i.val = 16 then 838 else if i.val = 17 then 839 else
      if i.val = 18 then 844 else 340 + i.val) = 322)
  split_ifs <;> omega

theorem overwrite_avoids (src dst : Fin 896) (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsCmd H (QueryTupleVisitor.overwrite src dst) :=
  ⟨avoids_clearProgram H dst 0 1 hd, copy_avoids src dst 841 hs hd (by decide)⟩

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

theorem pair_start_avoids : AvoidsCmd H QueryExecution.PairStart.command :=
  ⟨clear_avoids 851 (by decide), QueryElementaryReplay.expandCaller_avoids⟩

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

/-- The actual loader certificate closes the fixed visitor's only external
footprint obligation. -/
theorem visitor_avoids :
    AvoidsCmd H QueryVisitorProgram.visitor := by
  apply visitor_avoids_of_loader
  simpa only [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Nat.reduceMod] using
    SignatureLoaderReplay.program843_avoids

theorem tuple_avoids :
    AvoidsCmd H SignatureTupleComplete.command := by
  apply tuple_avoids_of_loader _ visitor_avoids
  simpa only [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Nat.reduceMod] using
    SignatureLoaderReplay.program845_avoids

theorem pair_callback_avoids : AvoidsCmd H QueryStreamProgram.pairCallback := by
  unfold QueryStreamProgram.pairCallback
  exact ⟨pair_start_avoids,tuple_avoids,commit_pair_avoids⟩

theorem pairs_avoids_oai : AvoidsCmd H QueryStreamProgram.pairs := by
  apply QueryElementaryReplay.differenceCommand_avoids
  · intro i
    change ¬ (832+i.val=320 ∨ 832+i.val=322)
    omega
  · exact pair_callback_avoids

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.pairs_avoids_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.pairs_avoids_oai
