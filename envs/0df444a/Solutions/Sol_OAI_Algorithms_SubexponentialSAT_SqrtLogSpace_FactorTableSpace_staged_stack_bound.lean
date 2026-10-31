-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.staged_stack_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:05:40.17173+00:00
-- url     : https://prove2.me/submissions/6d1c2c97-41c4-4340-8d5c-77784b8d4a0c

import Mathlib
import Definitions.Def_OAIQ081S165
import Definitions.Def_OAIQ081S169
import Definitions.Def_OAIQ081S170
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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

theorem cutoff_eval (a : Data) (htmp : a.stacks 684 = []) :
    Eval cutoff (7*(a.stacks 138).length+7) a (cutoffState a) := by
  have hc := SubexpSetupStorage.copy_eval 138 550 684 a
    (by decide) (by decide) (by decide) htmp
  have hs := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 16) true)
    (copyState 138 550 a))
  have hp := Eval.base (StructuredProgram.Eval.atom (.push (550 : Fin 768) (0 : Fin 16))
    ((StructuredProgram.Atom.set (0 : Fin 16) true).eval (copyState 138 550 a)))
  have hstate : (StructuredProgram.Atom.push (550 : Fin 768) (0 : Fin 16)).eval
      ((StructuredProgram.Atom.set (0 : Fin 16) true).eval (copyState 138 550 a)) =
      cutoffState a := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i = 550
      · subst i
        simp [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,execInstr,
          copyState,StackRoutines.copyStacks]
      · simp [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,execInstr,
          copyState,StackRoutines.copyStacks,hi]
  rw [hstate] at hp
  convert hc.seq (hs.seq hp) using 1
  all_goals try with_reducible_and_instances rfl

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

theorem pairs_valid : ∀ p ∈ pairs, p.1 ≠ p.2 ∧ p.1 ≠ 684 ∧ (684 : Fin 768) ≠ p.2 := by
  intro p hp
  simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide

theorem stage_eval (a : Data) (htmp : a.stacks 684 = []) :
    Eval stage (stageCost a) a (staged a) := by
  have htmp' : (copyManyState pairs a).stacks 684 = [] := by
    rw [copyMany_frame _ _ _ (fun p hp => (pairs_valid p hp).2.2)]
    exact htmp
  have hR : (copyManyState pairs a).stacks 138 = a.stacks 138 := by
    apply copyMany_frame
    intro p hp
    simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide
  have h := (copyMany_eval 684 pairs a pairs_valid htmp).seq
    (SourceControls.cutoff_eval (copyManyState pairs a) htmp')
  simpa only [hR,stageCost,Nat.add_assoc,stage,staged] using h

end SubexponentialSAT.SqrtLog.LeafProgram.Incidence

end OAI.Algorithms
end

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

private theorem decodeBasePort_low (i : Fin 896) (hi : i.val < 768) :
    decodeBasePort i = i.val := by
  have h885 : i ≠ 885 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h886 : i ≠ 886 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h887 : i ≠ 887 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h888 : i ≠ 888 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h889 : i ≠ 889 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h890 : i ≠ 890 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h891 : i ≠ 891 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h892 : i ≠ 892 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  simp only [decodeBasePort, ite_eq_right h885, ite_eq_right h886, ite_eq_right h887,
    ite_eq_right h888, ite_eq_right h889, ite_eq_right h890, ite_eq_right h891,
    ite_eq_right h892]

private theorem decodeBasePort_basePort (i : Fin 768) : decodeBasePort (basePort i) = i.val := by
  unfold basePort
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · exact decodeBasePort_low _ i.isLt

theorem basePort_injective : Function.Injective basePort := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg decodeBasePort hij
  simpa only [decodeBasePort_basePort] using hv

theorem initialized_temporary (a : OuterData) : (initialized a).stacks 684 = [] := by
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_left]
  exact List.mem_append_right _ (by simp)

theorem stage_eval (a : OuterData) :
    Eval (liftBase LeafProgram.Incidence.stage) (stageCost a) (initialized a) (staged a) := by
  apply eval_liftCommand_from_state _ 0 0 id basePort (initialized a)
    Function.injective_id basePort_injective
  apply LeafProgram.Incidence.stage_eval
  simpa only [projectState, Function.comp_apply,
    show basePort 684 = (684 : Fin 896) from rfl] using initialized_temporary a

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Space for one actual ambient-coordinate table construction. Its unary
traversal has only n iterations, so its polynomial local time bounds every
source prefix. No outer signature or finite-difference iteration count occurs
in this estimate. The concrete literal and staging traces are instantiated by
the factor-table producer, rather than supplied to a final counting endpoint. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace

open SqrtLog

open BitProgram StructuredCalls FactorTableProgram

/-- The eighteen physical copies have sources disjoint from every destination. -/
theorem original_stageCost_le (a : LeafProgram.Incidence.Data) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    LeafProgram.Incidence.stageCost a ≤ 133 * B + 97 := by
  have hc := SubexpSetupStorage.copyManyCost_le LeafProgram.Incidence.pairs a B
    (ha := fun p _ => hb p.1) (by
      intro p hp q hq
      have hsource : p.1.val < 340 ∨ 700 ≤ p.1.val := by
        simp only [LeafProgram.Incidence.pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide
      have hdest : 340 ≤ q.2.val ∧ q.2.val < 700 := by
        simp only [LeafProgram.Incidence.pairs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst q <;> decide
      intro he
      have hv := congrArg Fin.val he
      omega)
  have hr := hb 138
  change SubexpSetupStorage.copyManyCost LeafProgram.Incidence.pairs a ≤ 18 * (7 * B + 5) at hc
  dsimp only [LeafProgram.Incidence.stageCost]
  omega

/-- Clearing private scratch cannot increase any incoming stack. -/
theorem initialized_stack_bound (a : OuterData) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((initialized a).stacks i).length ≤ B := by
  intro i
  rw [initialized, SubexpSetupStorage.clearMany_stacks]
  split
  · simp
  · exact hb i

/-- The relocated stage includes its compiled call instruction. -/
theorem stageCost_le (a : OuterData) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) : stageCost a ≤ 133 * B + 98 := by
  have h := original_stageCost_le (projectState id basePort (initialized a)) B
    (fun i => initialized_stack_bound a B hb (basePort i))
  dsimp only [stageCost]
  omega

/-- All staging copies, the cutoff copy and both call and halt instructions
are counted on the same source run. -/
theorem stage_resources (a : OuterData) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    let p := compiled (liftBase LeafProgram.Incidence.stage) 556 62
    ∃ steps, steps ≤ 133 * B + 99 ∧
      Trace p steps ((initialized a).withPC (some p.entry)) ((staged a).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace p prefixSteps ((initialized a).withPC (some p.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896 * B + (133 * B + 99) := by
  dsimp only
  have hc : stageCost a + 1 ≤ 133 * B + 99 := by have := stageCost_le a B hb; omega
  refine ⟨stageCost a + 1, hc, compiled_halt_trace (stage_eval a) 556 62, ?_⟩
  intro prefixSteps intermediate hp ht i
  exact StructuredSpace.local_stack_bound (compiled (liftBase LeafProgram.Incidence.stage) 556 62)
    (StreamResources.dataBits_le_mul _ (initialized_stack_bound a B hb))
    prefixSteps intermediate (hp.trans hc) ht i

/-- Staging ends within its paid local source-prefix bound. -/
theorem staged_stack_bound_oai (a : OuterData) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((staged a).stacks i).length ≤ 1029 * B + 99 := by
  obtain ⟨steps, _, ht, hprefix⟩ := stage_resources a B hb
  intro i
  have hi := hprefix steps ((staged a).withPC none) le_rfl ht i
  change ((staged a).stacks i).length ≤ 896 * B + (133 * B + 99) at hi
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.staged_stack_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.staged_stack_bound_oai
