-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.initializeCost_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:52:15.589219+00:00
-- url     : https://prove2.me/submissions/d49664f9-97f3-4346-a73d-b0624bebcbda

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S168
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadSetupProgram_stageCost_linear

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramAddress
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The node index and palette size are runtime inputs. This fixed program
initializes the head countdown and computes the first physical color address
by real unary multiplication. Subsequent heads increment that address. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Address
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BasisTransposePlanProgram

theorem budget_polynomial (r t : ℕ) : budget r t ≤ 40*(r+t+1)^2 := by
  unfold budget
  nlinarith [Nat.zero_le ((r-t)^2)]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Address

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorageCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Cost of the concrete setup storage instructions

Copying and cleanup are charged by the lengths of the words physically read.
The final stage bound is linear in a common word bound; its coefficients depend
only on the statically allocated ports and copy lists.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem resetMany_wordBound {S : ℕ} (rs : List (Fin 16)) (a : Data S) (B : ℕ)
    (ha : WordBound B a) : WordBound B (resetManyState rs a) := by
  intro i
  simpa only [resetMany_stacks] using ha i

theorem beforeCopies_wordBound {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (a : Data S) (B : ℕ) (ha : WordBound B a) :
    WordBound B (beforeCopies tmp ports a) :=
  resetMany_wordBound _ _ B
    (clearMany_wordBound ports _ B (clearMany_wordBound [tmp] a B ha))

theorem prepare_wordBound {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hd : (inputs.map Prod.snd).Nodup)
    (hp : ∀ p ∈ inputs, p.2 ∈ ports)
    (hsep : ∀ p ∈ inputs, ∀ q ∈ inputs, p.1 ≠ q.2)
    (ha : WordBound B a) : WordBound B (prepareState tmp ports inputs a) := by
  apply copyMany_wordBound inputs _ B hd _ hsep (beforeCopies_wordBound tmp ports a B ha)
  intro p hm
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks, ite_eq_left (hp p hm)]

theorem finishCopies_wordBound {S : ℕ} (outputs : List (Fin S × Fin S))
    (a : Data S) (B : ℕ) (hd : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (ha : WordBound B a) :
    WordBound B (copyManyState outputs (clearManyState (outputs.map Prod.snd) a)) := by
  apply copyMany_wordBound outputs _ B hd _ hsep
    (clearMany_wordBound (outputs.map Prod.snd) a B ha)
  intro p hp
  rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨p, hp, rfl⟩)]

theorem finish_wordBound {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hd : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (ha : WordBound B a) : WordBound B (finishState ports outputs a) :=
  resetMany_wordBound _ _ B
    (clearMany_wordBound ports _ B (finishCopies_wordBound outputs a B hd hsep ha))

theorem embedState_wordBound {r s S : ℕ} (register : Fin r → Fin 16)
    (stack : Fin s → Fin S) (frame : Data S) (out : State r s) (B : ℕ)
    (hs : Function.Injective stack) (hf : WordBound B frame) (ho : WordBound B out) :
    WordBound B (embedState register stack frame out) := by
  intro i
  by_cases hm : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hm
    rw [embedState_stack register stack frame out hs j]
    exact ho j
  · rw [embedState_stack_frame register stack frame out i hm]
    exact hf i

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

theorem work_mem_workPorts {s : ℕ} (hs : s ≤ 288) (j : Fin s) :
    workPort hs j ∈ workPorts hs := by
  simp only [workPorts,List.mem_ofFn]
  exact ⟨j,rfl⟩

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

theorem addressInputs_protected : ∀ p∈addressInputs,Protected p.1 := by simp [addressInputs,Protected,temporary]
theorem addressOutputs_protected : ∀ p∈addressOutputs,Protected p.2 := by simp [addressOutputs,Protected,temporary]

theorem rowCountInputs_protected : ∀ p∈rowCountInputs,Protected p.1 := by simp [rowCountInputs,Protected,temporary]
theorem rowCountOutputs_protected : ∀ p∈rowCountOutputs,Protected p.2 := by simp [rowCountOutputs,Protected,temporary]

theorem cacheInputs_protected : ∀ p∈cacheInputs,Protected p.1 := by simp [cacheInputs,Protected,temporary]
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


theorem retainedState_positive_append (a : Data) :
    (retainedState a).stacks 710=a.stacks 640++a.stacks 710 := by
  simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
    clearMany_stacks,retainedPorts]


theorem retainedState_negative_append (a : Data) :
    (retainedState a).stacks 711=a.stacks 641++a.stacks 711 := by
  simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
    clearMany_stacks,retainedPorts]


theorem retainedState_denominator_append (a : Data) :
    (retainedState a).stacks 712=a.stacks 642++a.stacks 712 := by
  simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
    clearMany_stacks,retainedPorts]

theorem retainedState_frame (a : Data) (i : Fin 768)
    (h659 : i≠659) (h710 : i≠710) (h711 : i≠711) (h712 : i≠712) :
    (retainedState a).stacks i=a.stacks i := by
  rw [retainedState,copyMany_frame]
  · simp [clearMany_stacks,retainedPorts,h659]
  · simp [retainedCopies,h710,h711,h712]

theorem retainCost_linear (a : Data) : retainCost a=
    2*(a.stacks 659).length+
    7*((a.stacks 640).length+(a.stacks 641).length+(a.stacks 642).length)+18 := by
  simp [retainCost,retainedPorts,retainedCopies,clearManyCost,clearManyState,clearState,
    copyManyCost,copyState,StackRoutines.copyStacks]
  ring

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorageBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Linear paid staging overhead. This bound counts the copied words and
cleared cells, including produced output streams. It adds no unit-cost data
movement to any of the native service bounds. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem inputCopies_separated {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (hi : ∀ p∈ins,Protected p.1) :
    ∀ p∈inputCopies hs ins,∀ q∈inputCopies hs ins,p.1≠q.2 := by
  intro p hp q hq
  obtain ⟨p',hp',rfl⟩ := List.mem_map.mp hp
  obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
  exact protected_ne_work hs (hi p' hp') q'.2

theorem outputCopies_separated {s : ℕ} (hs : s ≤ 288) (outs : List (Fin s × Fin 768))
    (ho : ∀ p∈outs,Protected p.2) :
    ∀ p∈outputCopies hs outs,∀ q∈outputCopies hs outs,p.1≠q.2 := by
  intro p hp q hq
  obtain ⟨p',hp',rfl⟩ := List.mem_map.mp hp
  obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
  exact (protected_ne_work hs (ho q' hq') p'.1).symm

theorem prepared_wordBound {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (B : ℕ) (hi : ∀ p∈ins,Protected p.1) (hd : (ins.map Prod.snd).Nodup)
    (ha : WordBound B a) : WordBound B (prepared hs ins a) := by
  apply prepare_wordBound _ _ _ _ B _ _ (inputCopies_separated hs ins hi) ha
  · simpa only [inputCopies,List.map_map,Function.comp_def] using hd.map (workPort_injective hs)
  · intro p hp
    obtain ⟨p',hp',rfl⟩ := List.mem_map.mp hp
    exact work_mem_workPorts hs p'.2

theorem returned_wordBound {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (B : ℕ)
    (hi : ∀ p∈ins,Protected p.1) (ho : ∀ p∈outs,Protected p.2)
    (hdi : (ins.map Prod.snd).Nodup) (hdo : (outs.map Prod.snd).Nodup)
    (ha : WordBound B a) (hb : WordBound B b) :
    WordBound B (returned reg hs ins outs a b) := by
  have hd : ((outputCopies hs outs).map Prod.snd).Nodup := by
    simpa only [outputCopies,List.map_map,Function.comp_def] using hdo
  exact finish_wordBound _ _ _ B hd (outputCopies_separated hs outs ho)
    (embedState_wordBound reg (workPort hs) (prepared hs ins a) b B
      (workPort_injective hs) (prepared_wordBound hs ins a B hi hdi ha) hb)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBootResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid node bootstrap has ordinary polynomial cost, including the copies
retained for subsequent source-polynomial evaluation. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem boot_wordBound_mono {r s A B : ℕ} {a : State r s}
    (ha : WordBound A a) (h : A ≤ B) : WordBound B a := fun i => (ha i).trans h

theorem addressResult_wordBound (regs : Fin 3 → Bool) (r t K : ℕ)
    (hr : r ≤ K) (ht : t ≤ K) (hrt : t*r ≤ K) :
    WordBound K (Address.result regs r t) := by
  intro i
  fin_cases i <;> simp_all [Address.result,SubexponentialSAT.Subexp.BasisTransposePlanProgram.unary]

theorem rowCountState_wordBound (regs : Fin 8 → Bool) (records : List (List Bool)) (K : ℕ)
    (hb : (SubexponentialSAT.Encoding.encodeList id records).length ≤ K) (hn : records.length ≤ K) :
    WordBound K (rowCountState regs records (List.replicate records.length true)) := by
  intro i
  by_cases h1 : i=1
  · subst i; simpa [rowCountState] using hb
  by_cases h2 : i=2
  · subst i; simpa [rowCountState] using hn
  simp [rowCountState,h1,h2]

theorem cacheState_wordBound (regs : Fin 8 → Bool) (height R width : List Bool)
    (words : List (List Bool)) (K : ℕ)
    (hh : height.length ≤ K) (hr : R.length ≤ K) (hw : width.length ≤ K)
    (hp : words.flatten.length ≤ K) (hn : R.length*width.length ≤ K)
    (hd : (LayoutProgram.IntegerCache.denominatorWord R.length).length ≤ K) :
    WordBound K (cacheState regs height R width words) := by
  intro i
  fin_cases i <;> simp_all [cacheState,LayoutProgram.IntegerCache.state]

theorem bootState_wordBound (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool)
    (r t : ℕ) (records : List (List Bool)) (height R width : List Bool)
    (words : List (List Bool)) (K : ℕ) (ha : WordBound K a)
    (hab : WordBound K (Address.result ra r t))
    (hdb : WordBound K (rowCountState rd records (List.replicate records.length true)))
    (hcb : WordBound K (cacheState rc height R width words)) :
    WordBound K (bootState a ra rd rc r t records height R width words) := by
  have hb : WordBound K (addressState a ra r t) := returned_wordBound _ _ _ _ _ _ K
    addressInputs_protected addressOutputs_protected (by decide) (by decide) ha hab
  have hc : WordBound K (countedState (addressState a ra r t) rd records) :=
    returned_wordBound _ _ _ _ _ _ K rowCountInputs_protected rowCountOutputs_protected
      (by decide) (by decide) hb hdb
  exact returned_wordBound _ _ _ _ _ _ K cacheInputs_protected cacheOutputs_protected
    (by decide) (by decide) hc hcb

theorem bootCost_staging (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool)
    (r t : ℕ) (records : List (List Bool)) (height R width : List Bool)
    (words : List (List Bool)) (K : ℕ) (ha : WordBound K a)
    (hab : WordBound K (Address.result ra r t))
    (hdb : WordBound K (rowCountState rd records (List.replicate records.length true)))
    (hcb : WordBound K (cacheState rc height R width words)) :
    bootCost a ra rd rc r t records height R width words ≤
      Address.budget r t+(SubexponentialSAT.SubexpScopeCountSetup.countBudget records+1)+cacheBound height R width+
        451*(K+1) := by
  have hb : WordBound K (addressState a ra r t) := returned_wordBound _ _ _ _ _ _ K
    addressInputs_protected addressOutputs_protected (by decide) (by decide) ha hab
  have hc : WordBound K (countedState (addressState a ra r t) rd records) :=
    returned_wordBound _ _ _ _ _ _ K rowCountInputs_protected rowCountOutputs_protected
      (by decide) (by decide) hb hdb
  have h1 := stageCost_linear addressRegs (by decide) addressInputs addressOutputs a
    (Address.result ra r t) (Address.budget r t) K addressInputs_protected addressOutputs_protected
    (by decide) (by decide) ha hab
  have h2 := stageCost_linear rowCountRegs (by decide) rowCountInputs rowCountOutputs
    (addressState a ra r t) (rowCountState rd records (List.replicate records.length true))
    (SubexponentialSAT.SubexpScopeCountSetup.countBudget records+1) K rowCountInputs_protected rowCountOutputs_protected
    (by decide) (by decide) hb hdb
  have h3 := stageCost_linear cacheRegs (by decide) cacheInputs cacheOutputs
    (countedState (addressState a ra r t) rd records) (cacheState rc height R width words)
    (cacheBound height R width) K cacheInputs_protected cacheOutputs_protected
    (by decide) (by decide) hc hcb
  norm_num [addressInputs,addressOutputs,rowCountInputs,rowCountOutputs,cacheInputs,cacheOutputs] at h1 h2 h3
  unfold bootCost addressInputs addressOutputs rowCountInputs rowCountOutputs cacheInputs cacheOutputs
  omega

theorem retainedState_wordBound (a : Data) (K : ℕ) (ha : WordBound K a) :
    WordBound (2*K) (retainedState a) := by
  intro i
  by_cases h710 : i=710
  · subst i; rw [retainedState_positive_append,List.length_append]; have := ha 640; have := ha 710; omega
  by_cases h711 : i=711
  · subst i; rw [retainedState_negative_append,List.length_append]; have := ha 641; have := ha 711; omega
  by_cases h712 : i=712
  · subst i; rw [retainedState_denominator_append,List.length_append]; have := ha 642; have := ha 712; omega
  by_cases h659 : i=659
  · subst i
    simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
      clearMany_stacks,retainedPorts]
  rw [retainedState_frame a i h659 h710 h711 h712]
  have := ha i
  omega

theorem tupleInitialized_wordBound (a : Data) (K : ℕ) (ha : WordBound K a) :
    WordBound (K+3) (tupleInitialized a) := by
  intro i
  by_cases h665 : i=665
  · subst i
    simp only [tupleInitialized,Function.update_self,List.length_cons]
    have := ha 665
    omega
  by_cases h660 : i=660
  · subst i
    simpa [tupleInitialized] using ha 660
  simpa [tupleInitialized,h660,h665] using (ha i).trans (Nat.le_add_right K 3)

theorem initializeCost_staging (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool)
    (r t : ℕ) (records : List (List Bool)) (height R width : List Bool)
    (words : List (List Bool)) (K : ℕ) (ha : WordBound K a)
    (hab : WordBound K (Address.result ra r t))
    (hdb : WordBound K (rowCountState rd records (List.replicate records.length true)))
    (hcb : WordBound K (cacheState rc height R width words)) :
    initializeCost a ra rd rc r t records height R width words ≤
      Address.budget r t+(SubexponentialSAT.SubexpScopeCountSetup.countBudget records+1)+cacheBound height R width+
        500*(K+1) ∧
      WordBound (2*K+3) (nodeStart a ra rd rc r t records height R width words) := by
  have hb := bootState_wordBound a ra rd rc r t records height R width words K ha hab hdb hcb
  constructor
  · have hc := bootCost_staging a ra rd rc r t records height R width words K ha hab hdb hcb
    have h0 := hb 659
    have h1 := hb 640
    have h2 := hb 641
    have h3 := hb 642
    unfold initializeCost
    rw [retainCost_linear]
    omega
  · exact tupleInitialized_wordBound _ (2*K) (retainedState_wordBound _ K hb)

theorem records_lengths_bound (records : List (List Bool)) :
    (records.map List.length).sum ≤ (SubexponentialSAT.Encoding.encodeList id records).length := by
  induction records with
  | nil => simp
  | cons row rows ih => simp only [List.map_cons,List.sum_cons,SubexponentialSAT.Encoding.length_encodeList_cons,id_eq]; omega

theorem rowCountBudget_linear (records : List (List Bool)) :
    SubexponentialSAT.SubexpScopeCountSetup.countBudget records ≤ 17*(SubexponentialSAT.Encoding.encodeList id records).length+10 := by
  have hs := records_lengths_bound records
  have hn := SubexponentialSAT.Encoding.length_encodeList_lower id records
  unfold SubexponentialSAT.SubexpScopeCountSetup.countBudget SubexponentialSAT.SubexpSunflowerProgram.CountRecords.loopSteps
  omega

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBootPolynomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A uniform ordinary polynomial envelope for the actually executed cache
and address initialization. Parameters are charged by their runtime lengths. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem cacheBound_polynomial (height R width : List Bool) (S : ℕ)
    (hh : height.length ≤ S) (hr : R.length ≤ S) (hw : width.length ≤ S) :
    cacheBound height R width ≤ 10000*(S+1)^4 := by
  have hb : cacheBound height R width ≤
      7*(S+S+S)+(12*S+400*(S+1)*(S+1)*(2*S*S+5)+
        110*(S+1)*(S+(1+2*S*S)+4)+16)+11*S+27 := by
    unfold cacheBound LayoutProgram.IntegerCache.flatCost
    gcongr
  calc
    _ ≤ _ := hb
    _ ≤ _ := by nlinarith [Nat.zero_le (S^2),Nat.zero_le (S^3),Nat.zero_le (S^4)]

theorem cacheWords_flat_length (words : List (List Bool)) (W : ℕ)
    (hw : ∀ word∈words,word.length=W) : words.flatten.length=words.length*W := by
  induction words with
  | nil => simp
  | cons word words ih =>
      rw [List.flatten_cons,List.length_append,ih (by intro w h; exact hw w (by simp [h]))]
      rw [hw word (by simp)]
      simp [Nat.add_mul,Nat.add_comm]

theorem initializeCost_polynomial_oai (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool)
    (r t : ℕ) (records : List (List Bool)) (height R width : List Bool)
    (words : List (List Bool)) (S : ℕ)
    (ha : WordBound S a) (hr : r ≤ S) (ht : t ≤ S)
    (hb : (SubexponentialSAT.Encoding.encodeList id records).length ≤ S)
    (hh : height.length ≤ S) (hR : R.length ≤ S) (hw : width.length ≤ S)
    (hlen : words.length=R.length) (hwords : ∀ word∈words,word.length=width.length) :
    initializeCost a ra rd rc r t records height R width words ≤ 20000*(S+1)^4 ∧
      WordBound (2*(S+1)^2+3) (nodeStart a ra rd rc r t records height R width words) := by
  let K := (S+1)^2
  have hSK : S ≤ K := by dsimp [K]; nlinarith
  have hSK' : S+1 ≤ K := by dsimp [K]; nlinarith
  have hprod : S*S ≤ K := by dsimp [K]; nlinarith
  have hrt : t*r ≤ K := (Nat.mul_le_mul ht hr).trans hprod
  have hn : records.length ≤ K := (Nat.le_trans
    (Nat.le_of_succ_le (SubexponentialSAT.Encoding.length_encodeList_lower id records)) hb).trans hSK
  have hflat : words.flatten.length ≤ K := by
    rw [cacheWords_flat_length words width.length hwords,hlen]
    exact (Nat.mul_le_mul hR hw).trans hprod
  have hneg : R.length*width.length ≤ K := (Nat.mul_le_mul hR hw).trans hprod
  have hden : (LayoutProgram.IntegerCache.denominatorWord R.length).length ≤ K := by
    simp only [LayoutProgram.IntegerCache.denominatorWord,List.length_append,List.length_replicate,
      List.length_singleton]
    omega
  have he := initializeCost_staging a ra rd rc r t records height R width words K
    (boot_wordBound_mono ha hSK)
    (addressResult_wordBound ra r t K (hr.trans hSK) (ht.trans hSK) hrt)
    (rowCountState_wordBound rd records K (hb.trans hSK) hn)
    (cacheState_wordBound rc height R width words K (hh.trans hSK) (hR.trans hSK)
      (hw.trans hSK) hflat hneg hden)
  refine ⟨?_,he.2⟩
  have had := Address.budget_polynomial r t
  have ha2 : 40*(r+t+1)^2 ≤ 40*(S+S+1)^2 := by gcongr
  have hc := cacheBound_polynomial height R width S hh hR hw
  have hd := rowCountBudget_linear records
  have hcost := he.1
  dsimp [K] at hcost
  nlinarith [Nat.zero_le (S^2),Nat.zero_le (S^3),Nat.zero_le (S^4)]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.initializeCost_polynomial_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.initializeCost_polynomial_oai
