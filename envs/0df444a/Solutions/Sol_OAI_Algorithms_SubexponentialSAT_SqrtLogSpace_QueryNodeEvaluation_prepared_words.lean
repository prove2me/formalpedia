-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepared_words
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:24:24.604393+00:00
-- url     : https://prove2.me/submissions/4e1bbad5-1d9f-47a3-bbd7-d6781d43c869

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185

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

theorem prepare_frame {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (ht : i ≠ tmp) (hp : i ∉ ports) (hi : ∀ p ∈ inputs, i ≠ p.2) :
    (prepareState tmp ports inputs a).stacks i = a.stacks i := by
  unfold prepareState beforeCopies
  rw [copyMany_frame _ _ _ hi, resetMany_stacks, clearMany_stacks,
    ite_eq_right hp, clearMany_stacks]
  simp [ht]

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

theorem finish_value {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S)
    (hdup : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (p : Fin S × Fin S) (hp : p ∈ outputs) (hport : p.2 ∉ ports) :
    (finishState ports outputs a).stacks p.2 = a.stacks p.1 := by
  have hc : ∀ q ∈ outputs, (clearManyState (outputs.map Prod.snd) a).stacks q.2 = [] := by
    intro q hq
    rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨q, hq, rfl⟩)]
  have hs : p.1 ∉ outputs.map Prod.snd := by
    intro hm
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    exact hsep p hp q hq he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hport,
    copyMany_value _ _ hdup hc hsep p hp, clearMany_stacks, ite_eq_right hs]

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
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

open SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram
open TruncatedRingProgram


/-! The interpolation-node cursor is the actual framed table emitted by the
ring producer. Its low-bank loader is embedded into the common leaf bank;
all high pair/tuple state is preserved by the injective port map. -/
namespace Nodes



theorem installed_at (a : Data) (b : LowData) (i : Fin 896) (hi : i.val<768) :
    (installed a b).stacks i=b.stacks ⟨i.val,hi⟩ := by
  have hh : lowPort ⟨i.val,hi⟩=i := Fin.ext rfl
  simpa only [hh] using installed_low a b ⟨i.val,hi⟩

theorem readLow_stacks (a : Data) (bits : List Bool) (tail : List (List Bool)) (i : Fin 768) :
    (readLow a bits tail).stacks i=
      if i=301 then Encoding.encodeList id tail else if i=302 then [] else
        if i=78 then bits else (low (clearedNode a)).stacks i := by
  by_cases h301 : i=301
  · subst i
    simp [readLow,RingNodeSetup.nodeRead,OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes]
  by_cases h302 : i=302
  · subst i
    simp [readLow,RingNodeSetup.nodeRead,OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes]
  by_cases h78 : i=78
  · subst i
    simp [readLow,RingNodeSetup.nodeRead,OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes]
  simp only [h301,h302,h78,ite_false]
  exact readLow_frame a bits tail i h301 h302 h78

theorem begunNode_stacks (a : Data) (bits : List Bool) (tail : List (List Bool)) (i : Fin 896) :
    (begunNode a bits tail).stacks i=
      if i=301 then Encoding.encodeList id tail else if i=78 then bits else
        if i∈nodeResetPorts then [] else a.stacks i := by
  by_cases hlo : i.val<768
  · let j : Fin 768 := ⟨i.val,hlo⟩
    have hj : lowPort j=i := Fin.ext rfl
    have h301 : (j=301) ↔ (i=301) := by simp [j,Fin.ext_iff]
    have h302 : (j=302) ↔ (i=302) := by simp [j,Fin.ext_iff]
    have h78 : (j=78) ↔ (i=78) := by simp [j,Fin.ext_iff]
    rw [begunNode,installed_at _ _ i hlo]
    change (readLow a bits tail).stacks j=_
    rw [readLow_stacks]
    simp only [h301,h302,h78]
    change (if i=301 then Encoding.encodeList id tail else if i=302 then [] else
      if i=78 then bits else (clearedNode a).stacks (lowPort j))=_
    rw [hj,clearedNode,NodeReadoutSpace.clearedMany_stack]
    by_cases h : i=302
    · simp [h,nodeResetPorts]
    · simp only [h,ite_false]
  · have hh := installed_high (clearedNode a) (readLow a bits tail) i (by omega)
    rw [begunNode,hh,clearedNode,NodeReadoutSpace.clearedMany_stack]
    have h301 : i≠301 := by intro h; subst i; exact hlo (by decide)
    have h78 : i≠78 := by intro h; subst i; exact hlo (by decide)
    simp [h301,h78]


end Nodes


/-! Native multiplication of one completed head sum into the tuple product.
The original accumulator is relocated only at its two persistent operands. -/

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
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

theorem workPort_injective {s : ℕ} (hs : s ≤ 288) : Function.Injective (workPort hs) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [workPort] at this
  omega

theorem protected_ne_work {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) (j : Fin s) : i ≠ workPort hs j := by
  intro h
  have := congrArg Fin.val h
  have := j.isLt
  simp only [workPort] at *
  rcases hi.1 with h | h <;> omega

theorem protected_not_workPorts {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) : i ∉ workPorts hs := by
  simp only [workPorts,List.mem_ofFn,not_exists]
  intro j h
  exact protected_ne_work hs hi j h.symm

theorem prepared_frame {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (i : Fin 768) (hi : Protected i) : (prepared hs ins a).stacks i = a.stacks i := by
  apply prepare_frame _ _ _ _ _ hi.2 (protected_not_workPorts hs hi)
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact protected_ne_work hs hi q.2

theorem returned_word {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (ho : ∀ q ∈ outs,Protected q.2)
    (hd : (outs.map Prod.snd).Nodup) (p : Fin s × Fin 768) (hp : p ∈ outs) :
    (returned reg hs ins outs a b).stacks p.2=b.stacks p.1 := by
  have hd' : ((outputCopies hs outs).map Prod.snd).Nodup := by
    simpa only [outputCopies,List.map_map,Function.comp_def] using hd
  have hsep : ∀ q ∈ outputCopies hs outs,∀ z ∈ outputCopies hs outs,q.1≠z.2 := by
    intro q hq z hz
    obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
    obtain ⟨z',hz',rfl⟩ := List.mem_map.mp hz
    exact (protected_ne_work hs (ho z' hz') q'.1).symm
  exact (finish_value (workPorts hs) (outputCopies hs outs) _ hd' hsep
    (workPort hs p.1,p.2) (List.mem_map.mpr ⟨p,hp,rfl⟩)
    (protected_not_workPorts hs (ho p hp))).trans
      (embedState_stack reg (workPort hs) _ b (workPort_injective hs) p.1)

theorem returned_frame {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (i : Fin 768) (hi : Protected i)
    (hn : ∀ p ∈ outs,i≠p.2) : (returned reg hs ins outs a b).stacks i=a.stacks i := by
  have hno : ∀ p ∈ outputCopies hs outs,i≠p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hn q hq
  exact (finish_frame _ _ _ _ (protected_not_workPorts hs hi) hno).trans
    ((embedState_stack_frame _ _ _ _ _ (by
      rintro ⟨j,hj⟩; exact protected_ne_work hs hi j hj.symm)).trans
      (prepared_frame hs ins a i hi))

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-node paid bootstrap: address multiplication, actual plan-record
counting, and construction of the integer interpolation coefficient cache. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem cacheOutputs_protected : ∀ p∈cacheOutputs,Protected p.2 := by simp [cacheOutputs,Protected,temporary]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramRetain
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserve the paid interpolation cache for the later source-polynomial
worker. These three copies are charged before the private head bank is cleared. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem retainedState_positive (a : Data) (h : a.stacks 710=[]) : (retainedState a).stacks 710=a.stacks 640 := by
  simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
    clearMany_stacks,retainedPorts,h]
theorem retainedState_negative (a : Data) (h : a.stacks 711=[]) : (retainedState a).stacks 711=a.stacks 641 := by
  simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
    clearMany_stacks,retainedPorts,h]
theorem retainedState_denominator (a : Data) (h : a.stacks 712=[]) : (retainedState a).stacks 712=a.stacks 642 := by
  simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
    clearMany_stacks,retainedPorts,h]

theorem retainedState_frame (a : Data) (i : Fin 768)
    (h659 : i≠659) (h710 : i≠710) (h711 : i≠711) (h712 : i≠712) :
    (retainedState a).stacks i=a.stacks i := by
  rw [retainedState,copyMany_frame]
  · simp [clearMany_stacks,retainedPorts,h659]
  · simp [retainedCopies,h710,h711,h712]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBootRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact state and cost of the paid per-node bootstrap. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog
namespace LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem addressState_frame (a : Data) (regs : Fin 3 → Bool) (r t : ℕ) (i : Fin 768)
    (hi : Protected i) (h648 : i≠648) (h649 : i≠649) :
    (addressState a regs r t).stacks i=a.stacks i := by
  apply returned_frame addressRegs (by decide) addressInputs addressOutputs a _ i hi
  intro p hp
  simp only [addressOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl
  · exact h648
  · exact h649

theorem countedState_frame (a : Data) (regs : Fin 8 → Bool) (records : List (List Bool))
    (i : Fin 768) (hi : Protected i) (h647 : i≠647) :
    (countedState a regs records).stacks i=a.stacks i := by
  apply returned_frame rowCountRegs (by decide) rowCountInputs rowCountOutputs a _ i hi
  intro p hp
  simp only [rowCountOutputs,List.mem_singleton] at hp
  subst p
  exact h647

theorem bootState_frame (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool))
    (i : Fin 768) (hi : Protected i)
    (hne : i∉([640,641,642,643,647,648,649] : List (Fin 768))) :
    (bootState a ra rd rc r t records height R width words).stacks i=a.stacks i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
  rcases hne with ⟨h640,h641,h642,h643,h647,h648,h649⟩
  rw [bootState,returned_frame cacheRegs (by decide) cacheInputs cacheOutputs _ _ i hi,
    countedState_frame _ _ _ _ hi h647,addressState_frame _ _ _ _ _ hi h648 h649]
  intro p hp
  simp only [cacheOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact h640
  · exact h641
  · exact h642
  · exact h643


theorem bootState_positive (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (bootState a ra rd rc r t records height R width words).stacks 640=words.flatten :=
  returned_word cacheRegs (by decide) cacheInputs cacheOutputs _ _ cacheOutputs_protected
    (by decide) (0,640) (by simp [cacheOutputs])


theorem bootState_negative (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (bootState a ra rd rc r t records height R width words).stacks 641=List.replicate (R.length*width.length) false :=
  returned_word cacheRegs (by decide) cacheInputs cacheOutputs _ _ cacheOutputs_protected
    (by decide) (1,641) (by simp [cacheOutputs])


theorem bootState_denominator (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (bootState a ra rd rc r t records height R width words).stacks 642=LayoutProgram.IntegerCache.denominatorWord R.length :=
  returned_word cacheRegs (by decide) cacheInputs cacheOutputs _ _ cacheOutputs_protected
    (by decide) (2,642) (by simp [cacheOutputs])

end LeafHeadSetupProgram

end SqrtLog

end SubexponentialSAT

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramInitialize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Initialization of one node's physical Cartesian head loop. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem nodeStart_frame (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool))
    (i : Fin 768) (hi : Protected i)
    (hne : i∉([640,641,642,643,647,648,649,660,665,710,711,712] : List (Fin 768))) :
    (nodeStart a ra rd rc r t records height R width words).stacks i=a.stacks i := by
  have h659 : i≠659 := hi.2
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
  obtain ⟨h640,h641,h642,h643,h647,h648,h649,h660,h665,h710,h711,h712⟩ := hne
  simp only [nodeStart,tupleInitialized,Function.update_of_ne h665,Function.update_of_ne h660]
  rw [retainedState_frame _ i h659 h710 h711 h712]
  apply bootState_frame a ra rd rc r t records height R width words i hi
  simp [h640,h641,h642,h643,h647,h648,h649]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native entry cache is the actual output of the paid node bootstrap. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open RowSelectionProgram

theorem start_low (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 768) (hi : i.val < 340) : (start s a ra rd rc words).stacks i=a.stacks i := by
  apply nodeStart_frame
  · constructor
    · left; exact hi
    · intro h; have hh := congrArg Fin.val h; simp [temporary] at hh; omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    omega

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
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

/-- The cache bootstrap preserves the live source bank exactly. -/
theorem bootstrap_low (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 768) (hi : i.val < 340) :
    (SignatureHeadLoader.bootstrapResult s a ra rd rc words).stacks i = a.stacks i := by
  have hn660 : i ≠ 660 := by intro h; subst i; norm_num at hi
  have hn665 : i ≠ 665 := by intro h; subst i; norm_num at hi
  have he : (SignatureHeadLoader.bootstrapResult s a ra rd rc words).stacks i =
      (Native.start s a ra rd rc words).stacks i := by
    simp only [SignatureHeadLoader.bootstrapResult, Native.start, nodeStart,
      tupleInitialized, Function.update_of_ne hn660, Function.update_of_ne hn665]
  exact he.trans (Native.start_low s a ra rd rc words i hi)

/-- Paid empty destinations receive precisely the source cache words used
by the genuine factor specification. -/
theorem bootstrap_source_cache (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (h710 : a.stacks 710 = []) (h711 : a.stacks 711 = []) (h712 : a.stacks 712 = []) :
    let b := SignatureHeadLoader.bootstrapResult s a ra rd rc words
    let saved := LayoutProgramScalar.FromCounts.unsignedSaved words s.width s.power s.R s.height
    b.stacks 710 = saved.hp ∧ b.stacks 711 = saved.hn ∧ b.stacks 712 = s.power.1 := by
  dsimp only
  let b := bootState a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words
  have hf (i : Fin 768) (hi : 700 ≤ i.val) : b.stacks i = a.stacks i := by
    apply bootState_frame
    · exact ⟨Or.inr (by omega), by intro he; subst i; norm_num [temporary] at hi⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at *
      intro he
      rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num at hi
  have hp := (retainedState_positive b ((hf 710 (by decide)).trans h710)).trans
    (bootState_positive a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words)
  have hn := (retainedState_negative b ((hf 711 (by decide)).trans h711)).trans
    (bootState_negative a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words)
  have hd := (retainedState_denominator b ((hf 712 (by decide)).trans h712)).trans
    (bootState_denominator a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words)
  refine ⟨hp, ?_, ?_⟩
  · simpa only [SignatureHeadLoader.bootstrapResult, b,
      LayoutProgramScalar.FromCounts.unsignedSaved, unary, List.length_replicate] using hn
  · simpa only [SignatureHeadLoader.bootstrapResult, b, unary, List.length_replicate,
      Native.Inputs.power] using hd

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of a node evaluation. The paid node read, layout
load, native cache bootstrap and pair setup are the fixed commands used by the
streaming query; no evaluator is supplied to these constructions. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram QueryTupleState

/-- The paid reset, rather than an entry assumption, empties the node sum and caches. -/
theorem loadedNode_empty (a : Data) (bits : List Bool) (tail : List (List Bool))
    (i : Fin 896) (hi : i ∈ ([710,711,712,850,851] : List (Fin 896))) :
    (loadedNode a bits tail).stacks i=[] := by
  have hn : i ∉ NativeLayoutLoad.clearPorts := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
  rw [loadedNode,NativeLayoutLoad.result_frame _ i hn,
    QueryAssembler.Nodes.begunNode_stacks]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> simp [QueryAssembler.Nodes.nodeResetPorts]

theorem bootstrapped_low (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) (i : Fin 768) :
    (bootstrapped s a ra rd rc words).stacks (QueryAssembler.Nodes.lowPort i)=
      (SignatureHeadLoader.bootstrapResult s
        (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a) ra rd rc words).stacks i :=
  embedState_stack _ _ _ _ (Fin.castAdd_injective 768 128) i

theorem bootstrapped_high (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 896) (hi : 768 ≤ i.val) :
    (bootstrapped s a ra rd rc words).stacks i=a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  omega

/-- The bootstrap touches neither the low query data nor the retained upper
masters outside its three deliberately replaced cache words. -/
theorem bootstrapped_frame (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 896) (hi : i.val<340 ∨ 700 ≤ i.val)
    (h710 : i ≠ 710) (h711 : i ≠ 711) (h712 : i ≠ 712) :
    (bootstrapped s a ra rd rc words).stacks i=a.stacks i := by
  by_cases hlo : i.val<768
  · let j : Fin 768 := ⟨i.val,hlo⟩
    have hj : QueryAssembler.Nodes.lowPort j=i := Fin.ext rfl
    rw [←hj,bootstrapped_low]
    rcases hi with hi|hi
    · exact QueryReadyConstruction.bootstrap_low s _ ra rd rc words j hi
    · have hj710 : j ≠ 710 := fun h => h710 (hj.symm.trans (congrArg QueryAssembler.Nodes.lowPort h))
      have hj711 : j ≠ 711 := fun h => h711 (hj.symm.trans (congrArg QueryAssembler.Nodes.lowPort h))
      have hj712 : j ≠ 712 := fun h => h712 (hj.symm.trans (congrArg QueryAssembler.Nodes.lowPort h))
      have hj659 : j ≠ 659 := by intro h; have hh:=congrArg Fin.val h; change i.val=659 at hh; omega
      rw [SignatureHeadLoader.bootstrapResult,retainedState_frame _ j hj659 hj710 hj711 hj712]
      apply bootState_frame
      · exact ⟨Or.inr (by change 700 ≤ j.val at hi; omega),by
          intro h; have hh:=congrArg Fin.val h; change i.val=659 at hh; omega⟩
      · simp only [List.mem_cons,List.not_mem_nil,or_false]
        intro h
        rcases h with h|h|h|h|h|h|h
        all_goals have hh:=congrArg Fin.val h
        all_goals simp only [Fin.coe_ofNat_eq_mod,Nat.reduceMod] at hh
        all_goals change 700 ≤ j.val at hi
        all_goals omega
  · exact bootstrapped_high s a ra rd rc words i (by omega)

theorem bootstrapped_framePorts (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 896) (hi : i ∈ framePorts) :
    (bootstrapped s a ra rd rc words).stacks i=a.stacks i := by
  have hp : (i.val<340 ∨ 700 ≤ i.val) ∧ i ≠ 710 ∧ i ≠ 711 ∧ i ≠ 712 := by
    simp only [framePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact bootstrapped_frame s a ra rd rc words i hp.1 hp.2.1 hp.2.2.1 hp.2.2.2

/-- Exact node/cache words at the returned prefix state. The premises are
only the frame equations returned by its actual setup execution. -/
theorem prepared_words_oai (s : Native.Inputs) (a : Data)
    (bits : List Bool) (tail : List (List Bool))
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) (b : Data)
    (hf : ∀ i, i ∉ PairNativeSetup.scratch → i ≠ 832 → i ≠ 833 → i ≠ 834 → i ≠ 835 →
      b.stacks i=(bootstrapped s (loadedNode a bits tail) ra rd rc words).stacks i) :
    b.stacks 78=bits ∧ b.stacks 301=Encoding.encodeList id tail ∧
      (∀ i ∈ framePorts,b.stacks i=a.stacks i) ∧
      b.stacks 710=(LayoutProgramScalar.FromCounts.unsignedSaved words s.width s.power s.R s.height).hp ∧
      b.stacks 711=(LayoutProgramScalar.FromCounts.unsignedSaved words s.width s.power s.R s.height).hn ∧
      b.stacks 712=s.power.1 := by
  have h78 := hf 78 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h301 := hf 301 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hcache := QueryReadyConstruction.bootstrap_source_cache s
    (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort (loadedNode a bits tail))
    ra rd rc words (loadedNode_empty a bits tail 710 (by decide))
      (loadedNode_empty a bits tail 711 (by decide)) (loadedNode_empty a bits tail 712 (by decide))
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [h78,bootstrapped_frame s _ ra rd rc words 78 (by decide) (by decide) (by decide) (by decide),
      loadedNode,NativeLayoutLoad.result_frame _ 78 (by decide),QueryAssembler.Nodes.begunNode_stacks]
    simp
  · rw [h301,bootstrapped_frame s _ ra rd rc words 301 (by decide) (by decide) (by decide) (by decide),
      loadedNode,NativeLayoutLoad.result_frame _ 301 (by decide),QueryAssembler.Nodes.begunNode_stacks]
    simp
  · intro i hi
    have hn : i ∉ PairNativeSetup.scratch ∧ i ≠ 832 ∧ i ≠ 833 ∧ i ≠ 834 ∧ i ≠ 835 := by
      simp only [framePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    exact (hf i hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2).trans
      ((bootstrapped_framePorts s _ ra rd rc words i hi).trans (loadedNode_frame a bits tail i hi))
  · rw [hf 710 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact (bootstrapped_low s _ ra rd rc words 710).trans hcache.1
  · rw [hf 711 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact (bootstrapped_low s _ ra rd rc words 711).trans hcache.2.1
  · rw [hf 712 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact (bootstrapped_low s _ ra rd rc words 712).trans hcache.2.2

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepared_words_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepared_words_oai
