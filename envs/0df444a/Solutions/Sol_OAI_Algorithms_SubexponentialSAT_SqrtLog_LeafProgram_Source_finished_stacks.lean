-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.finished_stacks
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:15:26.697799+00:00
-- url     : https://prove2.me/submissions/60501eb3-39da-4221-8940-204456b5c73d

import Mathlib
import Definitions.Def_OAIQ081S159

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

theorem saved_values (a : Data) (h : ∀i∈backupPorts,a.stacks i=[]) :
    (saved a).stacks 680=a.stacks 532 ∧
    (saved a).stacks 681=a.stacks 533 ∧
    (saved a).stacks 682=a.stacks 582 ∧
    (saved a).stacks 683=a.stacks 583 := by
  have h0:=h 680 (by simp [backupPorts])
  have h1:=h 681 (by simp [backupPorts])
  have h2:=h 682 (by simp [backupPorts])
  have h3:=h 683 (by simp [backupPorts])
  simp [saved,clearMany_stacks,cachePorts,savePairs,copyManyState,copyState,
    StackRoutines.copyStacks,h0,h1,h2,h3]

theorem lowClear_iff (i : Fin 768) :
    i∈lowClearPorts ↔ ∃j : Fin 205, j∉retainedLow ∧ lowPort j=i := by
  simp [lowClearPorts,List.mem_map,List.mem_filter]

theorem retained_not_cleared (j : Fin 205) (hj : j∈retainedLow) :
    lowPort j∉lowClearPorts := by
  rw [lowClear_iff]
  rintro ⟨k,hk,hkj⟩
  have hv:=congrArg Fin.val hkj
  have he : k=j := by apply Fin.ext; simpa [lowPort] using hv
  exact hk (he ▸ hj)

theorem outside_not_cleared (i : Fin 768) (hi : 545 ≤ i.val) : i∉lowClearPorts := by
  rw [lowClear_iff]
  rintro ⟨j,_,he⟩
  have hv:=congrArg Fin.val he
  simp only [lowPort] at hv
  omega

theorem finished_values (a : Data) :
    (finished a).stacks 532=a.stacks 680 ∧
    (finished a).stacks 533=a.stacks 681 ∧
    (finished a).stacks 582=a.stacks 682 ∧
    (finished a).stacks 583=a.stacks 683 := by
  have h532 : (532 : Fin 768)∉lowClearPorts := retained_not_cleared 192 (by simp [retainedLow])
  have h533 : (533 : Fin 768)∉lowClearPorts := retained_not_cleared 193 (by simp [retainedLow])
  have h582 := outside_not_cleared 582 (by decide)
  have h583 := outside_not_cleared 583 (by decide)
  simp [finished,restored,clearMany_stacks,cachePorts,backupPorts,restorePairs,
    copyManyState,copyState,StackRoutines.copyStacks,h532,h533,h582,h583]

theorem finished_backups (a : Data) (i : Fin 768) (hi : i∈backupPorts) :
    (finished a).stacks i=[] := by
  simp [finished,clearMany_stacks,restored,hi]

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

theorem delta_stacks (a : Data) :
    (deltaState a).stacks = Function.update a.stacks 365 (true :: a.stacks 365) := by
  rfl

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

theorem cleaned_frame (a : Data) (i : Fin 768)
    (hi : ¬((589 ≤ i.val ∧ i.val < 593) ∨ (596 ≤ i.val ∧ i.val < 680))) :
    (cleaned a).stacks i = a.stacks i := by
  rw [cleaned,clearMany_stacks,ite_eq_right (fun h => hi ((mem_extraPorts i).mp h))]

end SubexponentialSAT.SqrtLog.LeafProgram.SourceControls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source callback used by the actual incidence-table loop. The fixed
command stages source controls, protects all four target caches, invokes the
concrete source-row instruction table, restores the target caches, and clears
source-only controls. The local source correctness theorem is joined below
through its actual execution, never through a supplied polynomial oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
theorem workerPort_injective : Function.Injective workerPort := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 340+i.val=340+j.val at hv
  omega

private theorem saved_tmp (a : Data) :
    (SourceStaging.saved a).stacks 684 = a.stacks 684 := by
  rw [SourceStaging.saved,clearMany_stacks,ite_eq_right (by decide)]
  apply copyMany_frame
  intro p hp
  simp only [SourceStaging.savePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with h|h|h|h <;> subst p <;> decide

theorem finished_rows (a : Data) (b : State 16 340) :
    (finished a b).stacks 545 = b.stacks 205 := by
  unfold finished
  rw [SourceControls.cleaned_frame _ _ (by decide)]
  rw [SourceStaging.finished,clearMany_stacks,
    ite_eq_right (SourceStaging.outside_not_cleared 545 (by decide))]
  unfold SourceStaging.restored
  rw [clearMany_stacks,ite_eq_right (by decide)]
  rw [copyMany_frame _ _ _ (by
    intro p hp
    simp only [SourceStaging.restorePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with h|h|h|h <;> subst p <;> decide)]
  rw [clearMany_stacks,ite_eq_right (by decide)]
  exact embedState_stack id workerPort (prepared a) b workerPort_injective 205

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact store restoration for the executed source callback. The source
kernel may change its four initialized caches and source output; the wrapper
restores all four caches and removes every staged source control. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

private theorem control_classified (p : Fin 768 × Fin 768) (hp : p ∈ SourceControls.pairs) :
    p.2 ∈ SourceStaging.lowClearPorts ∨ p.2 ∈ SourceControls.extraPorts := by
  simp only [SourceControls.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide

private theorem controls_frame (a : Data) (i : Fin 768)
    (hlow : i ∉ SourceStaging.lowClearPorts) (hextra : i ∉ SourceControls.extraPorts) :
    (SourceControls.prepared a).stacks i = a.stacks i := by
  have hi365 : i ≠ 365 := by intro h; subst i; exact hlow (by decide)
  unfold SourceControls.prepared
  rw [SourceControls.delta_stacks,Function.update_of_ne hi365]
  apply copyMany_frame
  intro p hp he
  rcases control_classified p hp with h|h
  · exact hlow (he.symm ▸ h)
  · exact hextra (he.symm ▸ h)

private theorem saved_frame (a : Data) (i : Fin 768)
    (hc : i ∉ SourceStaging.cachePorts) (hb : i ∉ SourceStaging.backupPorts) :
    (SourceStaging.saved a).stacks i = a.stacks i := by
  rw [SourceStaging.saved,clearMany_stacks,ite_eq_right hc]
  apply copyMany_frame
  intro p hp he
  have hdest : p.2 ∈ SourceStaging.backupPorts := by
    simp only [SourceStaging.savePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with h|h|h|h <;> subst p <;> decide
  exact hb (he.symm ▸ hdest)

private theorem prepared_frame (a : Data) (i : Fin 768)
    (hlow : i ∉ SourceStaging.lowClearPorts) (hextra : i ∉ SourceControls.extraPorts)
    (hc : i ∉ SourceStaging.cachePorts) (hb : i ∉ SourceStaging.backupPorts) :
    (prepared a).stacks i = a.stacks i :=
  (controls_frame _ i hlow hextra).trans (saved_frame a i hc hb)

private theorem restored_frame (a : Data) (i : Fin 768)
    (hc : i ∉ SourceStaging.cachePorts) (hb : i ∉ SourceStaging.backupPorts) :
    (SourceStaging.restored a).stacks i = a.stacks i := by
  rw [SourceStaging.restored,clearMany_stacks,ite_eq_right hb]
  rw [copyMany_frame _ _ _ (by
    intro p hp he
    have hdest : p.2 ∈ SourceStaging.cachePorts := by
      simp only [SourceStaging.restorePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with h|h|h|h <;> subst p <;> decide
    exact hc (he.symm ▸ hdest))]
  rw [clearMany_stacks,ite_eq_right hc]

private theorem prepared_backups (a : Data)
    (hb : ∀ i ∈ SourceStaging.backupPorts, a.stacks i = []) :
    (prepared a).stacks 680 = a.stacks 532 ∧
    (prepared a).stacks 681 = a.stacks 533 ∧
    (prepared a).stacks 682 = a.stacks 582 ∧
    (prepared a).stacks 683 = a.stacks 583 := by
  have h := SourceStaging.saved_values a hb
  simpa only [prepared,controls_frame _ 680 (by decide) (by decide),
    controls_frame _ 681 (by decide) (by decide),
    controls_frame _ 682 (by decide) (by decide),
    controls_frame _ 683 (by decide) (by decide)] using h

private theorem finished_caches (a : Data) (b : State 16 340)
    (hf : CoreFrame a b) (hb : ∀ i ∈ SourceStaging.backupPorts, a.stacks i = []) :
    (finished a b).stacks 532 = a.stacks 532 ∧
    (finished a b).stacks 533 = a.stacks 533 ∧
    (finished a b).stacks 582 = a.stacks 582 ∧
    (finished a b).stacks 583 = a.stacks 583 := by
  have hv := SourceStaging.finished_values (coreOutput a b)
  have hp := prepared_backups a hb
  have h680 := hf 680 (by decide)
  have h681 := hf 681 (by decide)
  have h682 := hf 682 (by decide)
  have h683 := hf 683 (by decide)
  rw [h680,h681,h682,h683] at hv
  rw [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2] at hv
  simpa only [finished,SourceControls.cleaned_frame _ 532 (by decide),
    SourceControls.cleaned_frame _ 533 (by decide),
    SourceControls.cleaned_frame _ 582 (by decide),
    SourceControls.cleaned_frame _ 583 (by decide)] using hv

theorem finished_stacks_oai (a : Data) (b : State 16 340)
    (hf : CoreFrame a b)
    (hlow : ∀ i ∈ SourceStaging.lowClearPorts, a.stacks i = [])
    (hextra : ∀ i ∈ SourceControls.extraPorts, a.stacks i = [])
    (hb : ∀ i ∈ SourceStaging.backupPorts, a.stacks i = []) :
    (finished a b).stacks = Function.update a.stacks 545 (b.stacks 205) := by
  funext i
  by_cases hi : i = 545
  · subst i; simpa using finished_rows a b
  rw [Function.update_of_ne hi]
  by_cases he : i ∈ SourceControls.extraPorts
  · rw [finished,SourceControls.cleaned,clearMany_stacks,ite_eq_left he,hextra i he]
  by_cases hl : i ∈ SourceStaging.lowClearPorts
  · rw [finished,SourceControls.cleaned,clearMany_stacks,ite_eq_right he,
      SourceStaging.finished,clearMany_stacks,ite_eq_left hl,hlow i hl]
  by_cases hbackup : i ∈ SourceStaging.backupPorts
  · rw [finished,SourceControls.cleaned,clearMany_stacks,ite_eq_right he,
      SourceStaging.finished_backups _ i hbackup,hb i hbackup]
  by_cases hc : i ∈ SourceStaging.cachePorts
  · have hv := finished_caches a b hf hb
    simp only [SourceStaging.cachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with h|h|h|h <;> subst i
    · exact hv.1
    · exact hv.2.1
    · exact hv.2.2.1
    · exact hv.2.2.2
  · rw [finished,SourceControls.cleaned,clearMany_stacks,ite_eq_right he,
      SourceStaging.finished,clearMany_stacks,ite_eq_right hl,restored_frame _ i hc hbackup]
    rw [hf i (by simpa [coreChanged,SourceStaging.cachePorts,hi] using hc)]
    exact prepared_frame a i hl he hc hbackup

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.finished_stacks_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.finished_stacks_oai
