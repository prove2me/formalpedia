-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.prepareIncidence_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:21:34.817624+00:00
-- url     : https://prove2.me/submissions/22161c66-0535-4305-9a87-a7e1a1411f25

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableNative_command_native_resources
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorID
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Retain the parsed factor ID and prepare the bare unary counter expected
by the isolated source-row/incidence worker.  Zero is represented by the
empty unary tape; it is not confused with a missing source record. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorID

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem command_eval (a : Data) (factor : ℕ)
    (hid : a.stacks 149=(Encoding.encodeNat factor).reverse)
    (hout : a.stacks 556=[]) (htmp : a.stacks 359=[]) :
    Eval command (7*(factor+1)+6) a (output a factor) := by
  have hc := copy_eval a 149 556 359 0 1
    (by decide) (by decide) (by decide) (by decide) htmp
  let b := afterCopy a 149 556 0 1
  have hs : b.stacks 556=false::List.replicate factor true := by
    simp [b,afterCopy,StackRoutines.copyStacks,hout,hid,Encoding.encodeNat]
  have hp := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.pop (556 : Fin 768) (0 : Fin 40) 1) b)
  have he : (StructuredProgram.Atom.pop (556 : Fin 768) (0 : Fin 40) 1).eval b=output a factor := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [StructuredProgram.Atom.instr,execInstr,b,afterCopy,
        hid,hout,Encoding.encodeNat]
    · funext i
      by_cases hi : i=556
      · subst i
        simp [StructuredProgram.Atom.instr,execInstr,hs]
      · simp [StructuredProgram.Atom.instr,execInstr,
          b,afterCopy,StackRoutines.copyStacks,hi]
  rw [he] at hp
  convert hc.seq hp using 1
  all_goals try with_reducible_and_instances rfl
  simp [hid,Encoding.encodeNat]

end SubexponentialSAT.SqrtLog.LeafProgram.FactorID

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

variable {r Q d n J S f : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : SourceReady.Data} {theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d}


/-- Returned cleanliness and the off-port frame identify the whole store,
not just a selected output tape. The selected factor ID is consumed. -/
theorem restored_stacks (a e : FactorTableProgram.OuterData) (bytes : List Bool)
    (hout : e.stacks 62 = bytes)
    (hframe : ∀ i, i ∉ FactorTableSpace.writtenPorts → e.stacks i = a.stacks i)
    (hclean : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → e.stacks i = [])
    (hblank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = []) :
    e.stacks = Function.update (Function.update a.stacks 556 []) 62 bytes := by
  funext i
  by_cases h62 : i = 62
  · subst i
    simpa only [Function.update_self] using hout
  by_cases h556 : i = 556
  · subst i
    have hm : (556 : Fin 896) ∈ FactorTableSpace.writtenPorts := by
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨556,
        (Incidence.mem_workerPorts 556).mpr (by decide), rfl⟩
    simpa only [Function.update_of_ne h62,Function.update_self] using hclean 556 hm h62
  rw [Function.update_of_ne h62,Function.update_of_ne h556]
  by_cases hm : i ∈ FactorTableSpace.writtenPorts
  · rw [hclean i hm h62,hblank i hm h62 h556]
  · exact hframe i hm

theorem callerRegisters_injective : Function.Injective FactorTableProgram.callerRegisters := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  exact hv

/-- The actual fixed40-register caller exports the same typed dictionaries,
consumes only factor556, restores the remaining initially blank private bank,
and frames all registers outside its16-register instruction table. -/
theorem caller_native_resources {r Q d u J n f B S : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {theta : Coeff (baseWidth 3 p.t) d} (a : State 40 896)
    (h : Ready p ps P u J n f B S theta
      (projectState FactorTableProgram.callerRegisters id a))
    (hblank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = []) :
    let localInput := projectState FactorTableProgram.callerRegisters id a
    let K := specializedLiteralWork p u J n S ((FactorTableProgram.staged localInput).stacks 574).length
    let L := specializedPayloadBound n u J (baseWidth 3 p.t) d
    ∃ (incidence : Fin n → List (MomentsProgram.Product.Entry n (baseWidth 3 p.t) d))
      (steps : ℕ) (e : State 40 896),
      (∀ v, TruncatedRingProgram.Good ∅ u J (incidence v)) ∧
      (∀ v, (MomentsProgram.Product.bytes (incidence v)).length ≤ L) ∧
      (∀ v, PayloadMeaning p ps P u J n f theta (FactorTableProgram.staged localInput).stacks
        v.val (MomentsProgram.Product.bytes (incidence v))) ∧
      steps ≤ FactorTableSpace.commandBudget B n K L ∧
      Eval FactorTableProgram.caller steps a e ∧
      e.stacks = Function.update (Function.update a.stacks 556 []) 62
        (Squarefree.Program.lookupRecords (HashCircuitProgram.incidenceEntries
          (fun (_ : Unit) v => MomentsProgram.Product.bytes (incidence v)) ())) ∧
      (∀ i : Fin 40, 16 ≤ i.val → e.regs i = a.regs i) ∧
      Trace (compiled FactorTableProgram.caller 556 62) (steps+1)
        (a.withPC (some (compiled FactorTableProgram.caller 556 62).entry)) (e.withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps+1 →
        Trace (compiled FactorTableProgram.caller 556 62) prefixSteps
          (a.withPC (some (compiled FactorTableProgram.caller 556 62).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          896*B+FactorTableSpace.commandBudget B n K L+1 := by
  dsimp only
  obtain ⟨incidence,steps,b,hgood,hlen,hmeaning,hsteps,htrace,hout,hframe,hclean,_⟩ :=
    command_native_resources h
  let e := embedState FactorTableProgram.callerRegisters id a b
  have he : Eval FactorTableProgram.caller steps a e :=
    eval_call_from_state FactorTableProgram.program FactorTableProgram.callerRegisters id a
      callerRegisters_injective Function.injective_id htrace
  have hs : e.stacks=b.stacks := by
    funext i
    exact embedState_stack _ _ _ _ Function.injective_id i
  have hstore := restored_stacks (projectState FactorTableProgram.callerRegisters id a) b _
    hout hframe hclean hblank
  have hrun := compiled_halt_trace he 556 62
  refine ⟨incidence,steps,e,hgood,hlen,hmeaning,hsteps,he,?_,?_,hrun,?_⟩
  · rw [hs,hstore]
    rfl
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    have hlt := j.isLt
    change j.val=i.val at hv
    omega
  · intro prefixSteps intermediate hp ht i
    have hb : ∀ i, (a.stacks i).length ≤ B := h.incoming
    have hbound := StructuredSpace.local_stack_bound
      (compiled FactorTableProgram.caller 556 62)
      (StreamResources.dataBits_le_mul _ hb) prefixSteps intermediate
      (hp.trans (Nat.add_le_add_right hsteps 1)) ht i
    simpa only [Nat.add_assoc] using hbound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
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

theorem identify_eval (a : FactorAssignmentProgram.Data) (factor : ℕ)
    (hid : a.stacks 149 = (Encoding.encodeNat factor).reverse)
    (hout : a.stacks 556 = []) (htmp : a.stacks 359 = []) :
    Eval (liftLow FactorID.command 149 556) (7 * (factor + 1) + 7)
      a (identified a factor) := by
  have he := FactorID.command_eval (projectState id lowStack a) factor hid hout htmp
  have hh := eval_liftCommand_from_state FactorID.command 149 556 id lowStack a
    Function.injective_id (Fin.castAdd_injective _ _) he
  unfold liftLow identified
  convert hh using 1
  all_goals try with_reducible_and_instances rfl

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


/-- The source table is generated on this very run after the unary factor ID
has been constructed. Its actual dictionary witnesses are returned unchanged. -/
theorem prepareIncidence_eval_oai {r Q d n : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J f B S : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (a : FactorAssignmentProgram.Data)
    (hid : a.stacks 149 = (Encoding.encodeNat f).reverse)
    (hout : a.stacks 556 = []) (htmp : a.stacks 359 = [])
    (hready : FactorTableNative.Ready p ps P u J n f B S theta (tableInput a f))
    (hblank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = []) :
    ∃ (incidence : Fin n → List (Product.Entry n (baseWidth 3 p.t) d)), ∃ steps e,
      (∀ v, TruncatedRingProgram.Good ∅ u J (incidence v)) ∧
      (∀ v, (Product.bytes (incidence v)).length ≤
        FactorTableNative.specializedPayloadBound n u J (baseWidth 3 p.t) d) ∧
      (∀ v, FactorTableNative.PayloadMeaning p ps P u J n f theta
        (FactorTableProgram.staged (tableInput a f)).stacks v.val (Product.bytes (incidence v))) ∧
      steps ≤ 7 * (f + 1) + 7 + tableTime p u J n B S a f ∧
      Eval FactorAssignmentProgram.prepareIncidence steps a e ∧
      e.stacks = Function.update a.stacks 62
        (Squarefree.Program.lookupRecords (Cost.entries incidence)) := by
  have hclean : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 →
      (identified a f).stacks i = [] := by
    intro i hi h62 h556
    rw [identified_stacks, Function.update_of_ne h556]
    exact hblank i hi h62 h556
  obtain ⟨incidence,steps,e,hgood,hlen,hmeaning,hsteps,he,hstore,_,_,_⟩ :=
    FactorTableNative.caller_native_resources (identified a f) hready hclean
  refine ⟨incidence,7*(f+1)+7+steps,e,hgood,hlen,hmeaning,
    Nat.add_le_add_left hsteps _,(identify_eval a f hid hout htmp).seq he,?_⟩
  rw [hstore, identified_stacks]
  funext i
  by_cases h62 : i = 62
  · subst i; rfl
  · by_cases h556 : i = 556
    · subst i; simp [hout]
    · simp [Function.update_of_ne h62, Function.update_of_ne h556]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.prepareIncidence_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.prepareIncidence_eval_oai
