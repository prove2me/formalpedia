-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.start_cache
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:49:43.123953+00:00
-- url     : https://prove2.me/submissions/a79d5405-b539-4a9b-ab1e-6c4e13a6ee02

import Mathlib
import Definitions.Def_OAIQ081S168

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

theorem start_positive (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    (start s a ra rd rc words).stacks 640=words.flatten := by
  unfold start nodeStart
  simp only [tupleInitialized,Function.update_of_ne (show (640:Fin 768)≠665 by decide),
    Function.update_of_ne (show (640:Fin 768)≠660 by decide)]
  rw [retainedState_frame _ 640 (by decide) (by decide) (by decide) (by decide)]
  exact bootState_positive _ _ _ _ _ _ _ _ _ _ _

theorem start_negative (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    (start s a ra rd rc words).stacks 641=List.replicate (s.R*s.width.length) false := by
  unfold start nodeStart
  simp only [tupleInitialized,Function.update_of_ne (show (641:Fin 768)≠665 by decide),
    Function.update_of_ne (show (641:Fin 768)≠660 by decide)]
  rw [retainedState_frame _ 641 (by decide) (by decide) (by decide) (by decide)]
  simpa [unary] using bootState_negative a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words

theorem start_denominator (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    (start s a ra rd rc words).stacks 642=s.power.1 := by
  unfold start nodeStart
  simp only [tupleInitialized,Function.update_of_ne (show (642:Fin 768)≠665 by decide),
    Function.update_of_ne (show (642:Fin 768)≠660 by decide)]
  rw [retainedState_frame _ 642 (by decide) (by decide) (by decide) (by decide)]
  simpa [unary,Inputs.power] using bootState_denominator a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words

theorem start_cache_oai (s : Inputs) (a : LeafHeadSetupProgram.Data) (ha : Ready s a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    LayoutProgram.EntryBank.CacheWords (r:=s.r)
      (LayoutFiberSumProgram.matrixBase (matrixBase (start s a ra rd rc words)) 0)
      (LayoutProgramScalar.FromCounts.unsignedSaved words s.width s.power s.R s.height) s.node := by
  have hf := start_low s a ra rd rc words
  constructor
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort,LayoutProgramScalar.FromCounts.unsignedSaved]
      using start_positive s a ra rd rc words
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort,LayoutProgramScalar.FromCounts.unsignedSaved]
      using start_negative s a ra rd rc words
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort,LayoutProgramScalar.FromCounts.unsignedSaved]
      using (hf 140 (by decide)).trans ha.width
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort,LayoutProgramScalar.FromCounts.unsignedSaved]
      using start_denominator s a ra rd rc words
  · rfl
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort,LayoutProgramScalar.FromCounts.unsignedSaved]
      using (hf 138 (by decide)).trans ha.order
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort,LayoutProgramScalar.FromCounts.unsignedSaved]
      using (hf 139 (by decide)).trans ha.height
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort] using (hf 130 (by decide)).trans ha.colors
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort] using (hf 131 (by decide)).trans ha.nodes
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort] using (hf 307 (by decide)).trans ha.node
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort] using (hf 132 (by decide)).trans ha.wordWidth

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.start_cache_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.start_cache_oai
