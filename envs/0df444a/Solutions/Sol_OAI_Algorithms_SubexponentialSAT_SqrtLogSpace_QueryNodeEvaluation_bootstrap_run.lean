-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.bootstrap_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:21:33.942993+00:00
-- url     : https://prove2.me/submissions/c2e9c597-723e-47e8-b8a9-6bbb65009018

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadSetupProgram_boot_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadSetupProgram_initializeCost_polynomial

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BitProgramSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Data-size bounds for the concrete Boolean-stack machine. A single
instruction can allocate at most one new bit. These bounds concern the actual
configurations on measured traces, not an auxiliary cost annotation. -/

namespace SubexponentialSAT.BitProgram

open scoped BigOperators

theorem stackBits_update {s : ℕ} (stk : Fin s → List Bool) (k : Fin s)
    (word : List Bool) :
    stackBits (Function.update stk k word) + (stk k).length = stackBits stk + word.length := by
  have lengths : (fun i => (Function.update stk k word i).length) =
      Function.update (fun i => (stk i).length) k word.length := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp only [Function.update_of_ne hi]
  unfold stackBits
  rw [lengths, Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun i => (stk i).length) (Finset.mem_univ k)
  omega

theorem execInstr_dataBits {r s l : ℕ} (i : Instr r s l) (c : Cfg r s l) :
    dataBits (execInstr i c) ≤ dataBits c + 1 := by
  cases i <;> try simp [dataBits, execInstr]
  · rename_i stack src next
    have h := stackBits_update c.stacks stack (c.regs src :: c.stacks stack)
    simp only [List.length_cons] at h
    change stackBits (Function.update c.stacks stack (c.regs src :: c.stacks stack)) ≤ _
    omega
  · rename_i stack value present next
    have h := stackBits_update c.stacks stack (c.stacks stack).tail
    have htail : (c.stacks stack).tail.length ≤ (c.stacks stack).length := by
      cases c.stacks stack <;> simp
    change stackBits (Function.update c.stacks stack (c.stacks stack).tail) ≤ _
    omega

theorem step_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l}
    (h : step p a = some b) : dataBits b ≤ dataBits a + 1 := by
  cases hp : a.pc with
  | none => simp [step, hp] at h
  | some label =>
      simp [step, hp] at h
      rw [← h]
      exact execInstr_dataBits _ _

theorem trace_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l} {n : ℕ}
    (h : Trace p n a b) : dataBits b ≤ dataBits a + n := by
  induction h with
  | refl a => simp
  | cons hs ht ih =>
      have hstep := step_dataBits p hs
      omega

end SubexponentialSAT.BitProgram

end OAI.Algorithms
end

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

end SubexponentialSAT.SubexpSetupStorage

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

theorem protected_not_workPorts {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) : i ∉ workPorts hs := by
  simp only [workPorts,List.mem_ofFn,not_exists]
  intro j h
  exact protected_ne_work hs hi j h.symm

theorem work_mem_workPorts {s : ℕ} (hs : s ≤ 288) (j : Fin s) :
    workPort hs j ∈ workPorts hs := by
  simp only [workPorts,List.mem_ofFn]
  exact ⟨j,rfl⟩

theorem prepared_frame {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (i : Fin 768) (hi : Protected i) : (prepared hs ins a).stacks i = a.stacks i := by
  apply prepare_frame _ _ _ _ _ hi.2 (protected_not_workPorts hs hi)
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact protected_ne_work hs hi q.2

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

open BitProgram

/-- Summing the port bounds counts every simultaneously live buffer. -/
theorem dataBits_le_mul {r s l bound : ℕ} (c : Cfg r s l)
    (h : ∀ i, (c.stacks i).length ≤ bound) : dataBits c ≤ s * bound := by
  simpa [dataBits, stackBits] using Finset.sum_le_card_nsmul Finset.univ
    (fun i => (c.stacks i).length) bound (fun i _ => h i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
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

theorem retainCache_eval (a : Data) : Eval retainCache (retainCost a) a (retainedState a) := by
  apply (clearMany_eval retainedPorts a).seq
  apply copyMany_eval
  · simp [retainedCopies,temporary]
  · simp [clearMany_stacks,retainedPorts,temporary]


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

end LeafHeadSetupProgram

end SqrtLog

end SubexponentialSAT

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

theorem cacheWords_flat_length (words : List (List Bool)) (W : ℕ)
    (hw : ∀ word∈words,word.length=W) : words.flatten.length=words.length*W := by
  induction words with
  | nil => simp
  | cons word words ih =>
      rw [List.flatten_cons,List.length_append,ih (by intro w h; exact hw w (by simp [h]))]
      rw [hw word (by simp)]
      simp [Nat.add_mul,Nat.add_comm]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeInputs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime source facts for the closed head setup. No cache output, matrix,
entry evaluator, or running-time witness is supplied in this interface. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

theorem Inputs.records_bytes (s : Inputs) :
    SubexponentialSAT.Encoding.encodeList id s.records=LayoutOwnerFiberProgram.stream s.plans := by
  unfold Inputs.records LayoutOwnerFiberProgram.stream
  induction s.plans with
  | nil => rfl
  | cons p ps ih => simpa [SubexponentialSAT.Encoding.encodeList] using congrArg (fun x => true :: (SubexponentialSAT.Encoding.frame (LayoutOwnerFiberProgram.pairPayload p.1 p.2) ++ x)) ih

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete head-loader is specialized to actual node bootstrap data.
All physical entry contracts are discharged by the native cache producer. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem bootstrapResult_length_le_start (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) (i : Fin 768) :
    ((bootstrapResult s a ra rd rc words).stacks i).length ≤
      ((Native.start s a ra rd rc words).stacks i).length := by
  by_cases h660 : i=660
  · subst i; simp [Native.start,nodeStart,tupleInitialized,bootstrapResult]; omega
  by_cases h665 : i=665
  · subst i; simp [Native.start,nodeStart,tupleInitialized,bootstrapResult]
  simp [Native.start,nodeStart,tupleInitialized,bootstrapResult,h660,h665]

/-- The cache words used by all subsequent head calls are produced by this
paid run. Its all-stack prefix bound includes the retained cache copies. -/
theorem native_bootstrap_run_space (s : Native.Inputs) (a : Data)
    (ha : Native.Ready s a) (S : ℕ) (hS : WordBound S a) :
    ∃ ra rd rc words steps,
      CacheCorrect s.height (unary s.R) s.width words ∧
      steps ≤ 20000*(S+1)^4+1 ∧
      Trace bootstrapProgram steps (a.withPC (some bootstrapProgram.entry))
        ((bootstrapResult s a ra rd rc words).withPC none) ∧
      WordBound (2*(S+1)^2+3) (bootstrapResult s a ra rd rc words) ∧
      ∀ prefixSteps intermediate,prefixSteps ≤ steps →
        Trace bootstrapProgram prefixSteps (a.withPC (some bootstrapProgram.entry)) intermediate →
        dataBits intermediate ≤ 768*S+20000*(S+1)^4+1 := by
  obtain ⟨ra,rd,rc,words,t,ht,he,hlen,hwords,hvalues⟩ :=
    boot_eval a s.r s.node.val s.records s.height (unary s.R) s.width
      ha.colors ha.node (ha.plans.trans s.records_bytes.symm) ha.height ha.order ha.width
      (by simpa [unary] using s.width_boot)
  have hr : s.r ≤ S := by simpa [ha.colors,unary] using hS 130
  have hnode : s.node.val ≤ S := by simpa [ha.node,unary] using hS 307
  have hrecords : (OAI.Algorithms.SubexponentialSAT.Encoding.encodeList id s.records).length ≤ S := by
    simpa [s.records_bytes,ha.plans] using hS 136
  have hheight : s.height.length ≤ S := by simpa [ha.height] using hS 139
  have hR : (unary s.R).length ≤ S := by simpa [ha.order] using hS 138
  have hwidth : s.width.length ≤ S := by simpa [ha.width] using hS 140
  have hb := initializeCost_polynomial a ra rd rc s.r s.node.val s.records s.height
    (unary s.R) s.width words S hS hr hnode hrecords hheight hR hwidth hlen hwords
  let b := bootState a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words
  have htime : t+retainCost b ≤ 20000*(S+1)^4 := by
    have hc := hb.1
    unfold initializeCost at hc
    dsimp [b]
    omega
  have hout : WordBound (2*(S+1)^2+3) (bootstrapResult s a ra rd rc words) :=
    fun i => (bootstrapResult_length_le_start s a ra rd rc words i).trans (hb.2 i)
  refine ⟨ra,rd,rc,words,t+retainCost b+1,⟨hlen,hwords,hvalues⟩,
    Nat.add_le_add_right htime 1,compiled_halt_trace (he.seq (retainCache_eval b)) 307 647,
    hout,?_⟩
  have hin : dataBits (a.withPC (some bootstrapProgram.entry)) ≤ 768*S :=
    StreamResources.dataBits_le_mul _ hS
  intro prefixSteps intermediate hp hpre
  have hg := trace_dataBits bootstrapProgram hpre
  omega

/-- Paid clearing of the three cache destinations permits one fixed maximum
bound at every node boundary. The old tuple markers are never generated. -/
theorem native_bootstrap_retained_bound (s : Native.Inputs) (a : Data)
    (ha : Native.Ready s a) (A : ℕ) (hA : WordBound A a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (h710 : a.stacks 710=[]) (h711 : a.stacks 711=[]) (h712 : a.stacks 712=[]) :
    WordBound (max A (bootstrapOutputBound s)) (bootstrapResult s a ra rd rc words) := by
  let K := max A (bootstrapOutputBound s)
  have hK : bootstrapOutputBound s ≤ K := Nat.le_max_right _ _
  have haK : WordBound K a := fun i => (hA i).trans (Nat.le_max_left _ _)
  have hr : s.r ≤ K := by unfold bootstrapOutputBound at hK; omega
  have ht : s.node.val ≤ K := by simpa [ha.node,unary] using haK 307
  have htr : s.node.val*s.r ≤ K := by
    have h := Nat.mul_le_mul_right s.r s.node.isLt.le
    unfold bootstrapOutputBound at hK
    omega
  have hrecords : (OAI.Algorithms.SubexponentialSAT.Encoding.encodeList id s.records).length ≤ K := by
    simpa [s.records_bytes,ha.plans] using haK 136
  have hD : s.records.length ≤ K := by
    rw [s.records_length]
    unfold bootstrapOutputBound at hK
    omega
  have hh : s.height.length ≤ K := by unfold bootstrapOutputBound at hK; omega
  have hR : (unary s.R).length ≤ K := by
    simp only [unary,List.length_replicate]
    unfold bootstrapOutputBound at hK
    omega
  have hwidth : s.width.length ≤ K := by unfold bootstrapOutputBound at hK; omega
  have hneg : (unary s.R).length*s.width.length ≤ K := by
    simp only [unary,List.length_replicate]
    unfold bootstrapOutputBound at hK
    omega
  have hflat : words.flatten.length ≤ K := by
    rw [cacheWords_flat_length words s.width.length hw.2.1,hw.1]
    exact hneg
  have hden : (LayoutProgram.IntegerCache.denominatorWord (unary s.R).length).length ≤ K := by
    simp only [LayoutProgram.IntegerCache.denominatorWord,List.length_append,
      List.length_replicate,List.length_singleton,unary]
    unfold bootstrapOutputBound at hK
    omega
  let b := bootState a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words
  have hb : WordBound K b := bootState_wordBound a ra rd rc s.r s.node.val s.records
    s.height (unary s.R) s.width words K haK
    (addressResult_wordBound ra s.r s.node.val K hr ht htr)
    (rowCountState_wordBound rd s.records K hrecords hD)
    (cacheState_wordBound rc s.height (unary s.R) s.width words K hh hR hwidth hflat hneg hden)
  have bf (i : Fin 768) (hi : Protected i)
      (hne : i∉([640,641,642,643,647,648,649] : List (Fin 768))) : b.stacks i=a.stacks i :=
    bootState_frame a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words i hi hne
  have hret : WordBound K (retainedState b) := by
    intro i
    by_cases hp : i=710
    · subst i
      rw [retainedState_positive_append,bf 710 (by decide) (by decide),h710,List.append_nil]
      exact hb 640
    by_cases hn : i=711
    · subst i
      rw [retainedState_negative_append,bf 711 (by decide) (by decide),h711,List.append_nil]
      exact hb 641
    by_cases hd : i=712
    · subst i
      rw [retainedState_denominator_append,bf 712 (by decide) (by decide),h712,List.append_nil]
      exact hb 642
    by_cases htmp : i=659
    · subst i
      simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
        clearMany_stacks,retainedPorts]
    rw [retainedState_frame b i htmp hp hn hd]
    exact hb i
  exact hret

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
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

/-- The actual finite bootstrap call creates its cache on the same returned
state. Its retained cap is fixed per source, independently of the node index. -/
theorem bootstrap_run_oai (s : Native.Inputs) (a : Data) (B : ℕ)
    (ha : Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a))
    (hb : WordBound B a) (hcap : SignatureHeadLoader.bootstrapOutputBound s ≤ B)
    (h710 : a.stacks 710=[]) (h711 : a.stacks 711=[]) (h712 : a.stacks 712=[]) :
    ∃ ra rd rc words ticks,
      CacheCorrect s.height (unary s.R) s.width words ∧
      ticks ≤ 20000*(B+1)^4+1 ∧
      Eval QueryStreamProgram.bootstrapNode ticks a (bootstrapped s a ra rd rc words) ∧
      WordBound B (bootstrapped s a ra rd rc words) := by
  have hp : WordBound B (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a) :=
    fun i => hb (QueryAssembler.Nodes.lowPort i)
  obtain ⟨ra,rd,rc,words,ticks,hw,ht,hr,_hb,_hp⟩ :=
    SignatureHeadLoader.native_bootstrap_run_space s _ ha B hp
  have he := eval_call_from_state SignatureHeadLoader.bootstrapProgram
    SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a
    SignatureHeadLoader.leafRegs.injective (Fin.castAdd_injective 768 128) hr
  have hbound := SignatureHeadLoader.native_bootstrap_retained_bound s _ ha B hp
    ra rd rc words hw h710 h711 h712
  rw [max_eq_left hcap] at hbound
  refine ⟨ra,rd,rc,words,ticks,hw,ht,he,?_⟩
  intro i
  by_cases hi : i.val < 768
  · let j : Fin 768 := ⟨i.val,hi⟩
    have hj : QueryAssembler.Nodes.lowPort j=i := Fin.ext rfl
    rw [←hj,bootstrapped_low]
    exact hbound j
  · rw [bootstrapped_high s a ra rd rc words i (by omega)]
    exact hb i

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.bootstrap_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.bootstrap_run_oai
