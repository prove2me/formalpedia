-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.staged_factorJet
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:11:43.43529+00:00
-- url     : https://prove2.me/submissions/6ec1b703-e9d0-4bea-9a76-405ec9980433

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S170
import Definitions.Def_OAIQ081S177
import Definitions.Def_OAIQ081S178
import Definitions.Def_OAIQ081S181

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorDispatch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The factor dispatcher in the native leaf's actual bank.  The parsed ID
is retained for incidence preparation.  The mark flag is read from a tape,
not inserted as a program parameter. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem stackMap_injective : Function.Injective stackMap := by decide

end SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorDispatchFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact byte-store frame for the paid factor dispatcher. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem finished_stacks (a : Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark)
    (hwork : ∀ i ∈ scratch, a.stacks i = []) :
    (finished a rf rows clauses marked mark factor).stacks =
      Function.update a.stacks 154
        (LeafFactorDispatchProgram.selectedPayload rows clauses marked mark factor) := by
  funext i
  by_cases hin : ∃ j, stackMap j = i
  · obtain ⟨j,rfl⟩ := hin
    rw [show (finished a rf rows clauses marked mark factor).stacks (stackMap j) =
        LeafFactorDispatchProgram.outputStacks rows clauses marked mark factor j from
      embedState_stack register stackMap (staged a) _ stackMap_injective j]
    fin_cases j <;>
      simp_all [stackMap,LeafFactorDispatchProgram.outputStacks,
        LeafFactorDispatchProgram.baseStacks,LeafFactorDispatchProgram.unary,scratch]
  · have h152 : i ≠ 152 := by intro h; subst i; exact hin ⟨2,rfl⟩
    have h154 : i ≠ 154 := by intro h; subst i; exact hin ⟨15,rfl⟩
    rw [show (finished a rf rows clauses marked mark factor).stacks i = (staged a).stacks i from
      embedState_stack_frame register stackMap (staged a) _ i hin]
    simp [staged,copied,afterCopy,StackRoutines.copyStacks,h152,h154]

end SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted-assignment factor product uses the original finite-ring
indicator and clause programs after the concrete specialized table producer.
Every cache is rebuilt from persistent source words by paid native copies;
neutral factor IDs leave the running multiplicative identity unchanged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram
noncomputable section

theorem callbackInitial_low (a : Data) (i : Fin 768) :
    (callbackInitial a).stacks (lowStack i) =
      if i ∈ callbackScratch then [] else a.stacks (lowStack i) := by
  exact (embedState_stack localRegister lowStack a
    (clearManyState callbackScratch (projectState localRegister lowStack a))
    (Fin.castAdd_injective _ _) i).trans
    (clearMany_stacks callbackScratch (projectState localRegister lowStack a) i)

theorem callbackInitial_frame (a : Data) (i : Fin 896)
    (hi : i ∉ callbackScratch.map lowStack) :
    (callbackInitial a).stacks i = a.stacks i := by
  by_cases hlt : i.val < 768
  · let j : Fin 768 := ⟨i.val, hlt⟩
    have hj : lowStack j = i := Fin.ext rfl
    have hn : j ∉ callbackScratch := by
      intro hm
      exact hi (List.mem_map.mpr ⟨j, hm, hj⟩)
    rw [← hj, callbackInitial_low, ite_eq_right hn]
  · apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

variable {r Q d n J S f : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : SourceReady.Data} {theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d}

theorem project_staged (a : FactorTableProgram.OuterData) :
    projectState id FactorTableProgram.basePort (FactorTableProgram.staged a) =
      Incidence.staged (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)) := by
  exact projectState_embed id FactorTableProgram.basePort _ _ Function.injective_id FactorTableProgram.basePort_injective

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual ordinary and marked factor branches. The physical factor ID is
converted to the unary source counter, then the specialized table is produced
before the original finite-ring arithmetic is run. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

theorem identified_stacks (a : FactorAssignmentProgram.Data) (factor : ℕ) :
    (identified a factor).stacks = Function.update a.stacks 556 (List.replicate factor true) := by
  funext i
  by_cases hi : i.val < 768
  · let j : Fin 768 := ⟨i.val, hi⟩
    have hj : lowStack j = i := Fin.ext rfl
    rw [← hj, identified, embedState_stack id lowStack a _ (Fin.castAdd_injective _ _) j]
    by_cases h556 : j = 556
    · rw [h556]
      rfl
    · have hne : lowStack j ≠ (556 : Fin 896) := by
        intro he
        apply h556
        apply Fin.ext
        have hv := congrArg (fun k : Fin 896 => k.val) he
        exact hv
      simp [FactorID.output, Function.update_of_ne h556,
        Function.update_of_ne hne, projectState]
  · have h556 : i ≠ 556 := by
      intro he
      have hv := congrArg (fun k : Fin 896 => k.val) he
      change i.val = 556 at hv
      omega
    rw [identified, embedState_stack_frame _ _ _ _ i, Function.update_of_ne h556]
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual specialized callback dispatches one stored original factor ID.
The general dispatch theorem fixes its physical payload, flags and exact frame;
hash and marked branch correctness is supplied by their concrete native proofs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback

open OAI BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafProgram MomentsProgram FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The paid clear preserves an already established callback boundary. -/
theorem callbackInitial_stacks (a : FactorAssignmentProgram.Data)
    (hclean : ∀ i ∈ callbackScratch, a.stacks (lowStack i) = []) :
    (callbackInitial a).stacks = a.stacks := by
  funext i
  by_cases hi : i ∈ callbackScratch.map lowStack
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    rw [callbackInitial_low, ite_eq_left hj, hclean j hj]
  · exact callbackInitial_frame a i hi

private theorem dispatchInput_frame (a : FactorAssignmentProgram.Data) (i : Fin 768)
    (hi : i ∉ callbackScratch) :
    (dispatchInput a).stacks i = a.stacks (lowStack i) :=
  (callbackInitial_low a i).trans (ite_eq_right hi)

private theorem dispatchInput_work (a : FactorAssignmentProgram.Data) :
    ∀ i ∈ FactorDispatch.scratch, (dispatchInput a).stacks i = [] := by
  intro i hi
  have hmem : i ∈ callbackScratch := by
    simp only [callbackScratch, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hi))
  exact (callbackInitial_low a i).trans (ite_eq_left hmem)

/-- All caller stacks are restored except the actual selected payload154.
This frame applies to hash, marked and neutral IDs, without an early exit. -/
theorem dispatched_stacks (a : FactorAssignmentProgram.Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark) :
    (dispatched a rf rows clauses marked mark factor).stacks =
      Function.update (callbackInitial a).stacks 154
        (LeafFactorDispatchProgram.selectedPayload rows clauses marked mark factor) := by
  have hr : (dispatchInput a).stacks 701 = Encoding.encodeList id rows :=
    (dispatchInput_frame a 701 (by decide)).trans hrows
  have hc : (dispatchInput a).stacks 700 = Encoding.encodeList id clauses :=
    (dispatchInput_frame a 700 (by decide)).trans hclauses
  have hn : (dispatchInput a).stacks 704 = List.replicate rows.length true :=
    (dispatchInput_frame a 704 (by decide)).trans hcount
  have hm : (dispatchInput a).stacks 705 = Encoding.encodeNat mark :=
    (dispatchInput_frame a 705 (by decide)).trans hmark
  have hlow := FactorDispatch.finished_stacks (dispatchInput a) rf rows clauses
    marked mark factor hr hc hn hm (dispatchInput_work a)
  funext i
  by_cases hi : i.val < 768
  · let j : Fin 768 := ⟨i.val, hi⟩
    have hj : lowStack j = i := Fin.ext rfl
    rw [← hj]
    change (embedState id lowStack (callbackInitial a)
      (FactorDispatch.finished (dispatchInput a) rf rows clauses marked mark factor)).stacks
      (lowStack j) = _
    rw [embedState_stack id lowStack _ _ (Fin.castAdd_injective _ _) j, hlow]
    by_cases h154 : j = 154
    · rw [h154]
      simp [lowStack]
    · have hwide : lowStack j ≠ 154 := by
        intro he
        apply h154
        exact Fin.ext (congrArg (fun k : Fin 896 => k.val) he)
      simp only [Function.update_of_ne h154, Function.update_of_ne hwide]
      rfl
  · have h154 : i ≠ 154 := by intro he; subst i; norm_num at hi
    rw [Function.update_of_ne h154]
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorJet
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The incidence meaning depends only on the merged assignment and the
fixed-high context. Parser and accumulator contents do not enter it. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram

theorem factorJet_staged {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (J n f j : ℕ) (theta : Coeff (baseWidth 3 p.t) d) (a : OuterData)
    (h : CallerInput p.t p.model p.modulus p.cache J p.R theta a n) :
    sourceIncidenceJet p ps P n f j theta (Incidence.staged a).stacks =
      factorJet p ps P n f j theta a.stacks := by
  have hc := Incidence.staged_copy a h.destinations_empty
  unfold sourceIncidenceJet factorJet
  rw [hc (702,574) (by decide),hc (703,575) (by decide),hc (145,546) (by decide)]
  simp [sourceIncidenceJet,choiceStore]

theorem factorJet_frame {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (theta : Coeff (baseWidth 3 p.t) d) (a b : Fin 768 → List Bool)
    (h145 : a 145=b 145) (h702 : a 702=b 702) (h703 : a 703=b 703) :
    factorJet p ps P n f j theta a=factorJet p ps P n f j theta b := by
  unfold factorJet sourceIncidenceJet
  simp only [choiceStore,show (574:Fin 768)≠546 by decide,show (575:Fin 768)≠546 by decide,
    show (575:Fin 768)≠574 by decide,ite_false,ite_true, if_true]
  rw [h145,h702,h703]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallbackNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete physical inputs for the streamed factor callback. The source
context is the actual q.ctx, and the dispatcher determines every selected row
and clause. These predicates contain stored words and finite size bounds only.
Their construction from the actual loader/cache run remains an integration step. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

noncomputable section

variable {r Q n d A S : ℕ} {q : Factor.Spec r Q n d}
  {one seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d}
  {a : FactorAssignmentProgram.Data} {f : ℕ}

theorem Input.fetched_stacks (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    (fetched q a f rf).stacks = Function.update a.stacks 154
      (LeafFactorDispatchProgram.selectedPayload q.rawRows q.clauses q.marked q.mark f) := by
  rw [fetched, dispatched_stacks a rf q.rawRows q.clauses q.marked q.mark f
    h.rows h.clauses h.count h.mark, callbackInitial_stacks a h.blank]

theorem Input.fetched_frame (h : Input q A S one seed a f) (rf : Fin 8 → Bool)
    (i : Fin 896) (hi : i ≠ 154) : (fetched q a f rf).stacks i = a.stacks i := by
  rw [h.fetched_stacks rf, Function.update_of_ne hi]

/-- Source master words survive dispatch and the concrete unary factor-ID
conversion; only the selected payload154 and selected-factor word556 change. -/
theorem Input.table_frame (h : Input q A S one seed a f) (rf : Fin 8 → Bool)
    (i : Fin 768) (hi154 : FactorTableProgram.basePort i ≠ 154)
    (hi556 : FactorTableProgram.basePort i ≠ 556) :
    (projectState id FactorTableProgram.basePort
      (FactorAssignmentBranches.tableInput (fetched q a f rf) f)).stacks i =
      (projectState localRegister FactorTableProgram.basePort a).stacks i := by
  change (FactorAssignmentBranches.identified (fetched q a f rf) f).stacks
    (FactorTableProgram.basePort i) = a.stacks (FactorTableProgram.basePort i)
  rw [FactorAssignmentBranches.identified_stacks, Function.update_of_ne hi556,
    h.fetched_frame rf _ hi154]

theorem Input.table_scalar (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    FactorTableNative.ScalarMasters q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R
      q.theta (projectState id FactorTableProgram.basePort
        (FactorAssignmentBranches.tableInput (fetched q a f rf) f)) n := by
  have H := h.table_frame rf
  refine ⟨h.scalar.widthPositive, h.scalar.zeroCanonical, h.scalar.zeroBits,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [H 194 (by decide) (by decide)]; exact h.scalar.modulus
  · rw [H 202 (by decide) (by decide)]; exact h.scalar.width
  · rw [H 203 (by decide) (by decide)]; exact h.scalar.zero
  · rw [H 201 (by decide) (by decide)]; exact h.scalar.table
  · rw [H 204 (by decide) (by decide)]; exact h.scalar.degree
  · rw [H 145 (by decide) (by decide)]; exact h.scalar.choicesLength
  · rw [H 280 (by decide) (by decide)]; exact h.scalar.zeroWord
  · rw [H 207 (by decide) (by decide)]; exact h.scalar.oneWord
  · rw [H 78 (by decide) (by decide)]; exact h.scalar.thetaWord
  · rw [H 128 (by decide) (by decide)]; exact h.scalar.ambientCount
  · rw [H 243 (by decide) (by decide)]; exact h.scalar.targetCount
  · rw [H 138 (by decide) (by decide)]; exact h.scalar.radius
  · rw [H 703 (by decide) (by decide)]; exact h.scalar.highLength

/-- The source-table projection uses the current ambient assignment and fixed
high data, exactly as the original source factor does. -/
theorem Input.staged_factorJet_oai (h : Input q A S one seed a f)
    (rf : Fin 8 → Bool) (j : ℕ) :
    PerturbationAssembly.sourceIncidenceJet q.p q.ps q.packing n f j q.theta
      (FactorTableProgram.projectBase
        (FactorTableProgram.staged
          (FactorAssignmentBranches.tableInput (fetched q a f rf) f)).stacks) =
      Factor.factorJet q.p q.ps q.packing n f j q.theta (a.stacks ∘ lowStack) := by
  let input := FactorAssignmentBranches.tableInput (fetched q a f rf) f
  let old := projectState id FactorTableProgram.basePort (FactorTableProgram.initialized input)
  have hp := congrArg StructuredProgram.State.stacks (FactorTableNative.project_staged input)
  change FactorTableProgram.projectBase (FactorTableProgram.staged input).stacks =
    (Incidence.staged old).stacks at hp
  rw [hp]
  have he := Factor.factorJet_staged q.p q.ps q.packing q.J n f j q.theta old
    ((h.table_scalar rf).initialized input)
  apply he.trans
  refine Factor.factorJet_frame q.p q.ps q.packing n f j q.theta old.stacks
    (a.stacks ∘ lowStack) ?_ ?_ ?_
  all_goals dsimp only [old, projectState, Function.comp_apply]
  · exact (FactorTableSpace.initialized_base_external input 145 (by decide)).trans
      (h.table_frame rf 145 (by decide) (by decide))
  · exact (FactorTableSpace.initialized_base_external input 702 (by decide)).trans
      (h.table_frame rf 702 (by decide) (by decide))
  · exact (FactorTableSpace.initialized_base_external input 703 (by decide)).trans
      (h.table_frame rf 703 (by decide) (by decide))

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.staged_factorJet_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.staged_factorJet_oai
