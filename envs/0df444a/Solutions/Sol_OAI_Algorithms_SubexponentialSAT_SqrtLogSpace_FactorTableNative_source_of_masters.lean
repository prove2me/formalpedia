-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.source_of_masters
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:03:59.971832+00:00
-- url     : https://prove2.me/submissions/6cb1cbab-a5e7-413b-bfe0-71b94fd9dc83

import Mathlib
import Definitions.Def_OAIQ081S170
import Definitions.Def_OAIQ081S172
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableSpace_staged_stack_bound

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

theorem cutoff_value (a : Data) (R : ℕ)
    (hR : a.stacks 138 = List.replicate R true) (hempty : a.stacks 550 = []) :
    (cutoffState a).stacks 550 = List.replicate (R+1) true := by
  simp [cutoffState,hR,hempty,List.replicate_succ]

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

theorem initialized_empty (a : OuterData) (i : Fin 768)
    (hlo : 340 ≤ i.val) (hhi : i.val < 680) (hne : i ≠ 556) :
    (initialized a).stacks (basePort i) = [] := by
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_left]
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨i, List.mem_filter.mpr ⟨(LeafProgram.Incidence.mem_workerPorts i).mpr ⟨hlo,hhi⟩,
    by simpa using hne⟩, rfl⟩

theorem initialized_temporary (a : OuterData) : (initialized a).stacks 684 = [] := by
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_left]
  exact List.mem_append_right _ (by simp)

theorem initialized_selected (a : OuterData) : (initialized a).stacks 556 = a.stacks 556 := by
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_right]
  simp only [entryPorts, List.mem_append]
  rintro (h | h)
  · obtain ⟨i, hi, he⟩ := List.mem_map.mp h
    have hne : i ≠ 556 := by simpa using (List.mem_filter.mp hi).2
    apply hne
    apply basePort_injective
    exact he
  · norm_num [Fin.ext_iff, Fin.coe_ofNat_eq_mod] at h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramIncidenceFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact byte placement and reclamation for the executed incidence worker.
The source cutoff is computed by the staging command, independently of J. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Incidence
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage


private theorem destination_nodup : (pairs.map Prod.snd).Nodup := by
  simp [pairs]

private theorem separated : ∀ p ∈ pairs, ∀ q ∈ pairs, p.1 ≠ q.2 := by
  intro p hp q hq
  have hs : p.1.val < 340 ∨ 700 ≤ p.1.val := by
    simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide
  have hd : 340 ≤ q.2.val ∧ q.2.val < 700 := by
    simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hq
    rcases hq with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst q <;> decide
  intro he
  have hv := congrArg Fin.val he
  omega

private theorem destination_ne_cutoff : ∀ p ∈ pairs, p.2 ≠ 550 := by
  intro p hp
  simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide

/-- All eighteen cache/master copies are exact when their destinations start
empty. This includes runtime theta, the merged assignment, and high context. -/
theorem staged_copy (a : Data) (hz : ∀ p ∈ pairs,a.stacks p.2 = [])
    (p : Fin 768 × Fin 768) (hp : p ∈ pairs) :
    (staged a).stacks p.2 = a.stacks p.1 := by
  change Function.update (copyManyState pairs a).stacks 550 _ p.2 = _
  rw [Function.update_of_ne (destination_ne_cutoff p hp)]
  exact copyMany_value pairs a destination_nodup hz separated p hp

theorem staged_frame (a : Data) (i : Fin 768) (hcut : i ≠ 550)
    (hi : ∀ p ∈ pairs,i ≠ p.2) : (staged a).stacks i = a.stacks i := by
  change Function.update (copyManyState pairs a).stacks 550 _ i = _
  rw [Function.update_of_ne hcut]
  exact copyMany_frame pairs a i hi

theorem staged_cutoff (a : Data) (R : ℕ)
    (hR : a.stacks 138 = List.replicate R true) (hz : a.stacks 550 = []) :
    (staged a).stacks 550 = List.replicate (R+1) true := by
  apply SourceControls.cutoff_value
  · rw [copyMany_frame pairs a 138]
    · exact hR
    · intro p hp
      simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide
  · rw [copyMany_frame pairs a 550]
    · exact hz
    · intro p hp
      exact (destination_ne_cutoff p hp).symm

end SubexponentialSAT.SqrtLog.LeafProgram.Incidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The common perturbation input invariant follows from the actual paid leaf
staging copies and a clean worker. The full source count is built as R+1. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {t d : ℕ} {a : RingModel.Data d}
  {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
  {J R : ℕ} {theta : Coeff (baseWidth 3 t) d} {s : OuterData} {n : ℕ}

theorem CallerInput.destinations_empty (h : CallerInput t a M cache J R theta s n) :
    ∀ p∈LeafProgram.Incidence.pairs,s.stacks p.2=[] := by
  intro p hp
  have hb : 340 ≤ p.2.val ∧ p.2.val < 680 ∧ p.2≠556 := by
    simp only [LeafProgram.Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp <;> subst p <;> decide
  exact h.workerEmpty p.2 hb.1 hb.2.1 hb.2.2

private theorem innerPort_ne_550_of_small (i : Fin 256) (hi : i.val < 205) :
    innerPort i ≠ 550 := by
  intro h
  have hv := congrArg Fin.val h
  simp [innerPort] at hv
  omega

private theorem innerPort_ne_556_of_small (i : Fin 256) (hi : i.val < 205) :
    innerPort i ≠ 556 := by
  intro h
  have hv := congrArg Fin.val h
  simp [innerPort] at hv
  omega

private theorem innerPort_ne_incidence_of_small (i : Fin 256) (hi : i.val < 205)
    (hn : i ∉ arithmeticCachePorts) (p : Fin 768 × Fin 768)
    (hp : p ∈ LeafProgram.Incidence.pairs) : innerPort i ≠ p.2 := by
  simp only [LeafProgram.Incidence.pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp <;>
    subst p <;> intro h
  all_goals
    have hv := congrArg Fin.val h
    simp [innerPort] at hv
    simp [arithmeticCachePorts] at hn
    omega

private theorem innerPort_ne_550_of_lowScratch (i : Fin 256) (hi : i ∈ lowScratch) :
    innerPort i ≠ 550 := by
  intro h
  have hv := congrArg Fin.val h
  simp [innerPort] at hv
  simp [lowScratch, PerturbationBetaProgram.workPorts, originScratch, targetScratch,
    coordinateLoadScratch, shiftScratch, coordinateEmitScratch] at hi
  omega

private theorem innerPort_ne_556_of_lowScratch (i : Fin 256) (hi : i ∈ lowScratch) :
    innerPort i ≠ 556 := by
  intro h
  have hv := congrArg Fin.val h
  simp [innerPort] at hv
  simp [lowScratch, PerturbationBetaProgram.workPorts, originScratch, targetScratch,
    coordinateLoadScratch, shiftScratch, coordinateEmitScratch] at hi
  omega

private theorem innerPort_ne_incidence_of_lowScratch (i : Fin 256) (hi : i ∈ lowScratch)
    (hlarge : 205 ≤ i.val) (p : Fin 768 × Fin 768)
    (hp : p ∈ LeafProgram.Incidence.pairs) : innerPort i ≠ p.2 := by
  simp [lowScratch, PerturbationBetaProgram.workPorts, originScratch, targetScratch,
    coordinateLoadScratch, shiftScratch, coordinateEmitScratch] at hi
  simp only [LeafProgram.Incidence.pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp <;>
    subst p <;> intro h
  all_goals
    have hv := congrArg Fin.val h
    simp [innerPort] at hv
    omega

theorem CallerInput.staged (h : CallerInput t a M cache J R theta s n) :
    StagedInput t a M cache J (R+1) theta (LeafProgram.Incidence.staged s).stacks n := by
  have hc := LeafProgram.Incidence.staged_copy s h.destinations_empty
  have ht := LeafProgram.Incidence.staged_cutoff s R h.radius (h.workerEmpty 550 (by decide) (by decide) (by decide))
  have hwidth : (LeafProgram.Incidence.staged s).stacks 551=s.stacks 280 := hc (280,551) (by decide)
  refine ⟨?_,h.widthPositive,h.zeroCanonical,h.zeroBits,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (hc (194,534) (by decide)).trans h.modulus
    · change (LeafProgram.Incidence.staged s).stacks 345=(LeafProgram.Incidence.staged s).stacks 534
      rw [hc (194,345) (by decide),hc (194,534) (by decide)]
    · change ((LeafProgram.Incidence.staged s).stacks 542).length=_
      rw [hc (202,542) (by decide)]; exact h.width
    · change (LeafProgram.Incidence.staged s).stacks 350=(LeafProgram.Incidence.staged s).stacks 542
      rw [hc (202,350) (by decide),hc (202,542) (by decide)]
    · exact (hc (203,543) (by decide)).trans h.zero
    · exact (hc (201,541) (by decide)).trans h.table
    · change ((LeafProgram.Incidence.staged s).stacks 544).length=_
      rw [hc (204,544) (by decide)]; exact h.degree
    · exact ((hc (280,444) (by decide)).trans h.zeroWord).trans h.zeroBits
    · intro i hi hn
      have hp : innerPort i≠550 ∧ ∀ p∈LeafProgram.Incidence.pairs,innerPort i≠p.2 := by
        constructor
        · exact innerPort_ne_550_of_small i hi
        · intro p hmem
          exact innerPort_ne_incidence_of_small i hi hn p hmem
      change (LeafProgram.Incidence.staged s).stacks (innerPort i)=[]
      rw [LeafProgram.Incidence.staged_frame s (innerPort i) hp.1 hp.2]
      apply h.workerEmpty
      · dsimp [innerPort]; omega
      · dsimp [innerPort]; omega
      · exact innerPort_ne_556_of_small i hi
  · rw [hc (145,546) (by decide)]; exact h.choicesLength
  · exact (hc (280,547) (by decide)).trans h.zeroWord
  · exact (hc (207,548) (by decide)).trans h.oneWord
  · exact (hc (78,549) (by decide)).trans h.thetaWord
  · simp [ht]
  · rw [hwidth,h.zeroWord]; exact RingProgram.flat_length _
  · exact (hc (128,552) (by decide)).trans h.ambientCount
  · exact (hc (243,553) (by decide)).trans h.targetCount
  · intro i hi hlarge
    have hp : innerPort i≠550 ∧ ∀ p∈LeafProgram.Incidence.pairs,innerPort i≠p.2 := by
      constructor
      · exact innerPort_ne_550_of_lowScratch i hi
      · intro p hmem
        exact innerPort_ne_incidence_of_lowScratch i hi hlarge p hmem
    rw [LeafProgram.Incidence.staged_frame s (innerPort i) hp.1 hp.2]
    apply h.workerEmpty
    · dsimp [innerPort]; omega
    · dsimp [innerPort]; omega
    · exact innerPort_ne_556_of_lowScratch i hi

theorem CallerInput.staged_empty (h : CallerInput t a M cache J R theta s n)
    (i : Fin 768) (hi : i∈([460,545,555,557,561,569,573,585] : List (Fin 768))) :
    (LeafProgram.Incidence.staged s).stacks i=[] := by
  have hb : 340 ≤ i.val ∧ i.val < 680 ∧ i≠556 := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with hi|hi|hi|hi|hi|hi|hi|hi <;> subst i <;> decide
  have hc : i≠550 := by
    intro he; subst i; norm_num [Fin.ext_iff] at hi
  have hp : ∀ p∈LeafProgram.Incidence.pairs,i≠p.2 := by
    intro p hmem
    simp only [LeafProgram.Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hmem
    rcases hmem with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;> subst p
    all_goals intro he; subst i; norm_num [Fin.ext_iff] at hi
  rw [LeafProgram.Incidence.staged_frame s i hc hp]
  exact h.workerEmpty i hb.1 hb.2.1 hb.2.2

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
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

/-- Every actual external source master survives entry clearing, including
masters702/703 and710..728; no initial scratch-blank premise is used. -/
theorem initialized_base_external (a : OuterData) (i : Fin 768)
    (hi : (i.val < 340 ∧ i ≠ 62) ∨ 684 < i.val) :
    (initialized a).stacks (basePort i) = a.stacks (basePort i) := by
  have hn (j : Fin 768) (hj : 340 ≤ j.val ∧ j.val ≤ 684) : i ≠ j := by
    intro hij
    subst j
    rcases hi with hi | hi <;> omega
  have hbase : basePort i = i.castAdd 128 := by
    simp only [basePort, ite_eq_right (hn 640 (by decide)), ite_eq_right (hn 641 (by decide)),
      ite_eq_right (hn 642 (by decide)), ite_eq_right (hn 647 (by decide)),
      ite_eq_right (hn 650 (by decide)), ite_eq_right (hn 651 (by decide)),
      ite_eq_right (hn 670 (by decide)), ite_eq_right (hn 671 (by decide))]
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_right]
  simp only [entryPorts, List.mem_append]
  rintro (h | h)
  · obtain ⟨j, hj, he⟩ := List.mem_map.mp h
    have hji : j = i := basePort_injective he
    subst j
    have hw := (LeafProgram.Incidence.mem_workerPorts i).mp (List.mem_filter.mp hj).1
    rcases hi with hi | hi <;> omega
  · rw [hbase] at h
    have hnum : (i.val < 340 ∧ i.val ≠ 62) ∨ 684 < i.val := by
      rcases hi with ⟨hlt, hne⟩ | hgt
      · exact Or.inl ⟨hlt, fun hv => hne (Fin.ext hv)⟩
      · exact Or.inr hgt
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Fin.ext_iff,
      Fin.val_castAdd, Fin.coe_ofNat_eq_mod] at h
    norm_num at h
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical source preparation for the specialized factor table. The old
master-word argument is generalized to the actually selected unary factor,
then transported through the fixed protected-port embedding. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod


/-- Entry clearing reconstructs the ordinary caller cleanliness rather than
assuming the private worker survived a previous head reload. -/
theorem ScalarMasters.initialized {t d J R n : ℕ} {model : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d}
    (a : FactorTableProgram.OuterData)
    (h : ScalarMasters t model M cache J R theta
      (projectState id FactorTableProgram.basePort a) n) :
    CallerInput t model M cache J R theta
      (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)) n := by
  have frame (i : Fin 768) (hi : (i.val < 340 ∧ i ≠ 62) ∨ 684 < i.val) :
      (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)).stacks i =
        (projectState id FactorTableProgram.basePort a).stacks i :=
    FactorTableSpace.initialized_base_external a i hi
  refine ⟨h.widthPositive,h.zeroCanonical,h.zeroBits,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [frame 194 (by decide)]; exact h.modulus
  · rw [frame 202 (by decide)]; exact h.width
  · rw [frame 203 (by decide)]; exact h.zero
  · rw [frame 201 (by decide)]; exact h.table
  · rw [frame 204 (by decide)]; exact h.degree
  · rw [frame 145 (by decide)]; exact h.choicesLength
  · rw [frame 280 (by decide)]; exact h.zeroWord
  · rw [frame 207 (by decide)]; exact h.oneWord
  · rw [frame 78 (by decide)]; exact h.thetaWord
  · rw [frame 128 (by decide)]; exact h.ambientCount
  · rw [frame 243 (by decide)]; exact h.targetCount
  · rw [frame 138 (by decide)]; exact h.radius
  · rw [frame 703 (by decide)]; exact h.highLength
  · intro i hlo hhi hn
    exact FactorTableProgram.initialized_empty a i hlo hhi hn

/-- Every source master lies outside the concretely cleared private bank. -/
theorem SourceMasters.initialized {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    (a : FactorTableProgram.OuterData)
    (h : SourceMasters p ps P (projectState id FactorTableProgram.basePort a)) :
    SourceMasters p ps P
      (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)) := by
  have frame (i : Fin 768) (hi : (i.val < 340 ∧ i ≠ 62) ∨ 684 < i.val) :
      (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)).stacks i =
        (projectState id FactorTableProgram.basePort a).stacks i :=
    FactorTableSpace.initialized_base_external a i hi
  constructor
  · rw [frame 130 (by decide)]; exact h.colors
  · rw [frame 131 (by decide)]; exact h.nodes
  · rw [frame 132 (by decide)]; exact h.typeWidth
  · rw [frame 710 (by decide)]; exact h.positive
  · rw [frame 711 (by decide)]; exact h.negative
  · rw [frame 140 (by decide)]; exact h.scalarWidth
  · rw [frame 712 (by decide)]; exact h.power
  · exact h.powerNegative
  · rw [frame 138 (by decide)]; exact h.radius
  · rw [frame 139 (by decide)]; exact h.offset
  · rw [frame 135 (by decide)]; exact h.metadata
  · rw [frame 136 (by decide)]; exact h.plans
  · rw [frame 713 (by decide)]; exact h.inverses
  · rw [frame 714 (by decide)]; exact h.negatives
  · rw [frame 715 (by decide)]; exact h.differences
  · rw [frame 717 (by decide)]; exact h.ringWidth
  · rw [frame 716 (by decide)]; exact h.rowWidth
  · rw [frame 280 (by decide)]; exact h.zero
  · rw [frame 207 (by decide)]; exact h.one
  · rw [frame 211 (by decide)]; exact h.minusOne
  · rw [frame 728 (by decide)]; exact h.inverseDenominator

theorem staged_external (a : SourceReady.Data) (i : Fin 768)
    (hi : i.val < 340 ∨ 680 ≤ i.val) : (Incidence.staged a).stacks i=a.stacks i := by
  apply Incidence.staged_frame
  · intro he; subst i; norm_num at hi
  · intro p hp
    have hb : 340 ≤ p.2.val ∧ p.2.val < 680 := by
      simp only [Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    intro he
    subst i
    omega

variable {r Q d n J S f : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : SourceReady.Data} {theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d}

theorem source_of_staged (h : CallerInput p.t p.model p.modulus p.cache J p.R theta a n)
    (hm : SourceMasters p ps P a)
    (hf : a.stacks 556=List.replicate f true) (htmp : a.stacks 684=[])
    (hback : ∀ i∈SourceStaging.backupPorts,a.stacks i=[])
    (hsize : WordBound S (Incidence.staged a))
    (harray : (p.R+1)*(d*baseWidth 3 p.t) ≤ S) (hcount : p.R+1 ≤ S)
    (hmetadata : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S)
    (hinc : ps.length ≤ S) :
    SourceReady.Input p ps P (Incidence.staged a) 0 n f S := by
  have hc := Incidence.staged_copy a h.destinations_empty
  have hex := staged_external a
  have hclean : ∀ i : Fin 340,i∉SourceReady.physicalLive →
      (Incidence.staged a).stacks (SourceReady.localPort i)=[] := by
    intro i hi
    have h550 : SourceReady.localPort i≠550 := by
      intro he
      have hv : i=210 := Fin.ext (by have := congrArg Fin.val he; dsimp [SourceReady.localPort] at this; omega)
      exact hi (by simp [hv,SourceReady.physicalLive])
    have hdest : ∀ z∈Incidence.pairs,SourceReady.localPort i≠z.2 := by
      intro z hz he
      have hv := congrArg Fin.val he
      simp only [Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals dsimp [SourceReady.localPort] at hv
      all_goals apply hi; simp only [SourceReady.physicalLive,List.mem_cons,List.mem_nil_iff,or_false]
      all_goals simp only [Fin.ext_iff,Fin.coe_ofNat_eq_mod]; omega
    rw [Incidence.staged_frame a _ h550 hdest]
    apply h.workerEmpty
    · dsimp [SourceReady.localPort]; omega
    · dsimp [SourceReady.localPort]; omega
    · intro he
      have hv : i=216 := Fin.ext (by have := congrArg Fin.val he; dsimp [SourceReady.localPort] at this; omega)
      exact hi (by simp [hv,SourceReady.physicalLive])
  have hfactor : (Incidence.staged a).stacks 556=List.replicate f true := by
    rw [Incidence.staged_frame a 556 (by decide) (by
      intro z hz
      simp only [Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
    exact hf
  refine ⟨h.staged.arithmetic,hclean,(hex 684 (Or.inr (by decide))).trans htmp,?_,?_,?_,hfactor,?_,
    ?_,?_,?_,?_,?_,?_,?_,hm.powerNegative,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    hsize,harray,hcount,hmetadata,hinc⟩
  · intro i hi
    have hg : 680 ≤ i.val := by
      simp only [SourceStaging.backupPorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> decide
    exact (hex i (Or.inr hg)).trans (hback i hi)
  · exact Incidence.staged_cutoff a p.R h.radius (h.workerEmpty 550 (by decide) (by decide) (by decide))
  · exact (hc (128,552) (by decide)).trans h.ambientCount
  · exact h.staged_empty 573 (by decide)
  · exact (hex _ (Or.inl (by decide))).trans hm.colors
  · exact (hex _ (Or.inl (by decide))).trans hm.nodes
  · exact (hex _ (Or.inl (by decide))).trans hm.typeWidth
  · exact (hex _ (Or.inr (by decide))).trans hm.positive
  · exact (hex _ (Or.inr (by decide))).trans hm.negative
  · exact (hex _ (Or.inl (by decide))).trans hm.scalarWidth
  · exact (hex _ (Or.inr (by decide))).trans hm.power
  · exact (hex _ (Or.inl (by decide))).trans hm.radius
  · exact (hex _ (Or.inl (by decide))).trans hm.offset
  · exact (hex _ (Or.inl (by decide))).trans hm.metadata
  · exact (hex _ (Or.inl (by decide))).trans hm.plans
  · exact (hex _ (Or.inr (by decide))).trans hm.inverses
  · exact (hex _ (Or.inr (by decide))).trans hm.negatives
  · exact (hex _ (Or.inr (by decide))).trans hm.differences
  · exact (hex _ (Or.inr (by decide))).trans hm.ringWidth
  · exact (hex _ (Or.inr (by decide))).trans hm.rowWidth
  · exact (hex _ (Or.inl (by decide))).trans hm.zero
  · exact (hex _ (Or.inl (by decide))).trans hm.one
  · exact (hex _ (Or.inl (by decide))).trans hm.minusOne
  · exact (hex _ (Or.inr (by decide))).trans hm.inverseDenominator




theorem project_staged (a : FactorTableProgram.OuterData) :
    projectState id FactorTableProgram.basePort (FactorTableProgram.staged a) =
      Incidence.staged (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)) := by
  exact projectState_embed id FactorTableProgram.basePort _ _ Function.injective_id FactorTableProgram.basePort_injective

/-- The generalized factor identifier is retained through paid staging;
all native source prerequisites follow from concrete stored masters. -/
theorem source_of_remapped_staged {r Q d n J S f : ℕ}
    (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : FactorTableProgram.OuterData) (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (h : CallerInput p.t p.model p.modulus p.cache J p.R theta
      (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)) n)
    (hm : SourceMasters p ps P (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)))
    (hf : a.stacks 556 = List.replicate f true)
    (hsize : WordBound S (projectState id FactorTableProgram.basePort (FactorTableProgram.staged a)))
    (harray : (p.R+1)*(d*baseWidth 3 p.t) ≤ S) (hcount : p.R+1 ≤ S)
    (hmetadata : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S)
    (hinc : ps.length ≤ S) :
    SourceReady.Input p ps P (projectState id FactorTableProgram.basePort (FactorTableProgram.staged a)) 0 n f S := by
  rw [project_staged] at hsize ⊢
  apply source_of_staged h hm
  · simpa only [projectState, Function.comp_apply,
      show FactorTableProgram.basePort 556 = (556 : Fin 896) from rfl, FactorTableProgram.initialized_selected] using hf
  · simpa only [projectState, Function.comp_apply,
      show FactorTableProgram.basePort 684 = (684 : Fin 896) from rfl] using FactorTableProgram.initialized_temporary a
  · intro i hi
    simp only [SourceStaging.backupPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals
      simp only [projectState, Function.comp_apply]
      rw [FactorTableProgram.initialized, clearMany_stacks, ite_eq_left]
      exact List.mem_append_right _ (by decide)
  · exact hsize
  · exact harray
  · exact hcount
  · exact hmetadata
  · exact hinc


/-- Initial physical masters and their measured word sizes establish source
readiness after the actual clear-and-stage commands, for the chosen factor. -/
theorem source_of_masters_oai {r Q d n J S f B : ℕ}
    (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : FactorTableProgram.OuterData) (theta : Coeff (baseWidth 3 p.t) d)
    (hscalar : ScalarMasters p.t p.model p.modulus p.cache J p.R theta
      (projectState id FactorTableProgram.basePort a) n)
    (hmasters : SourceMasters p ps P (projectState id FactorTableProgram.basePort a))
    (hf : a.stacks 556 = List.replicate f true)
    (hincoming : ∀ i, (a.stacks i).length ≤ B)
    (hsize : 1029*B+99 ≤ S)
    (harray : (p.R+1)*(d*baseWidth 3 p.t) ≤ S) (hcount : p.R+1 ≤ S)
    (hmetadata : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S)
    (hinc : ps.length ≤ S) :
    SourceReady.Input p ps P (projectState id FactorTableProgram.basePort
      (FactorTableProgram.staged a)) 0 n f S := by
  apply source_of_remapped_staged p ps P a theta (hscalar.initialized a)
    (hmasters.initialized a) hf
  · intro i
    exact (FactorTableSpace.staged_stack_bound a B hincoming
      (FactorTableProgram.basePort i)).trans hsize
  · exact harray
  · exact hcount
  · exact hmetadata
  · exact hinc

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.source_of_masters_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.source_of_masters_oai
