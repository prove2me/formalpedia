-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.command_resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:29:45.867338+00:00
-- url     : https://prove2.me/submissions/144624b0-4b60-4992-93eb-fddc26473e0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableSpace_staged_stack_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialConstructor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable physical construction of a padded polynomial from two scalar
cells and a cached unary dimension. The native constructor buffers are
cleared on return; an order-preserving move writes the chosen cache slot. -/

namespace SubexponentialSAT.SubexpPolynomialConstructor

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpPolynomialServiceControl (transfer transfer_run)

theorem move_run (s : Store) (src dst : Fin 256)
    (hs : src ≠ 245) (hd : dst ≠ 245) (hsd : src ≠ dst)
    (htmp : s 245 = []) (hout : s dst = []) :
    ExecutesIn (move src dst) (6 * (s src).length + 6) s
      (Function.update (Function.update s src []) dst (s src)) := by
  let middle := Function.update (Function.update s src []) 245 (s src).reverse
  have h₁ : ExecutesIn (transfer src 245) (3 * (s src).length + 3) s middle := by
    simpa [middle, htmp] using transfer_run src 245 s hs
  have he : Function.update (Function.update middle 245 []) dst
      ((middle 245).reverse ++ middle dst) =
      Function.update (Function.update s src []) dst (s src) := by
    funext j
    by_cases hj : j = 245 <;>
      simp [middle, Function.update_apply, hd, Ne.symm hs, Ne.symm hd, Ne.symm hsd, htmp, hout, hj]
  have h₂ : ExecutesIn (transfer 245 dst) (3 * (s src).length + 3) middle
      (Function.update (Function.update s src []) dst (s src)) := by
    have h := transfer_run 245 dst middle (Ne.symm hd)
    rw [he] at h
    simpa [middle] using h
  have h := h₁.seq h₂
  have hcost : (3 * (s src).length + 3) + (3 * (s src).length + 3) =
      6 * (s src).length + 6 := by omega
  simpa only [move, hcost] using h

end SubexponentialSAT.SubexpPolynomialConstructor

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

theorem export_eval (a : Data) (htmp : a.stacks 684 = []) :
    Eval exportResult (exportCost a) a (exported a) :=
  (SubexpSetupStorage.copy_eval 561 62 684 a (by decide) (by decide) (by decide) htmp).seq
    (clearMany_eval workerPorts (copyState 561 62 a))

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

theorem exported_output (a : Data) (h62 : a.stacks 62 = []) :
    (exported a).stacks 62 = a.stacks 561 := by
  rw [exported,clearMany_stacks,ite_eq_right (by decide)]
  simp [copyState,StackRoutines.copyStacks,h62]

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

theorem innerPort_injective : Function.Injective innerPort := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [innerPort] at this
  omega

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

theorem basePort_protected (i : Fin 768) :
    basePort i ≠ 640 ∧ basePort i ≠ 641 ∧ basePort i ≠ 642 ∧ basePort i ≠ 647 ∧
      basePort i ≠ 650 ∧ basePort i ≠ 651 ∧ basePort i ≠ 670 ∧ basePort i ≠ 671 := by
  simp only [basePort]
  split_ifs <;> simp_all [Fin.ext_iff, Fin.coe_ofNat_eq_mod]

theorem basePort_high (i : Fin 768) :
    (basePort i).val < 768 ∨ (885 ≤ (basePort i).val ∧ (basePort i).val ≤ 892) := by
  simp only [basePort]
  split_ifs <;> simp_all only [Fin.val_castAdd, Fin.coe_ofNat_eq_mod] <;> omega

theorem basePort_outside (i : Fin 896)
    (hi : i ∈ protectedPorts ∨ (768 ≤ i.val ∧ (i.val < 885 ∨ 892 < i.val))) :
    ¬ ∃ j, basePort j = i := by
  rintro ⟨j, hj⟩
  rcases hi with hi | hi
  · simp only [protectedPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    have hp := basePort_protected j
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.1 hj
    · exact hp.2.1 hj
    · exact hp.2.2.1 hj
    · exact hp.2.2.2.1 hj
    · exact hp.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.2.2 hj
  · have hm := basePort_high j
    rw [hj] at hm
    omega

theorem replaceInner_project (s : OuterStore) : replaceInner s (projectInner s)=s := by
  have h := embedState_project id innerPort (⟨fun _=>false,s⟩ : OuterData)
    Function.injective_id innerPort_injective
  exact congrArg StructuredProgram.State.stacks h

theorem replaceInner_update (s : OuterStore) (u : Store) (i : Fin 256) (bits : List Bool) :
    replaceInner s (Function.update u i bits)=Function.update (replaceInner s u) (innerPort i) bits :=
  ProgramLinking.extend_update innerPort_injective _ _ _ _

theorem liftInner_run (s : OuterStore) (code : Code) (K : ℕ) (u : Store)
    (h : ExecutesIn code K (projectInner s) u) :
    ExecutesOuter (liftInner code) (K+1) s (replaceInner s u) := by
  constructor
  intro regs
  obtain ⟨k,rf,hk,he⟩ := h regs
  have hl := eval_liftCommand_from_state code 0 0 id innerPort (⟨regs,s⟩ : OuterData)
    Function.injective_id innerPort_injective he
  refine ⟨k+1,rf,by omega,?_⟩
  unfold liftInner
  convert hl using 1
  all_goals try with_reducible_and_instances rfl
  apply state_ext
  · simp [embedState]
  · rfl

/-- A common single-result service remains a single-result service after
relocation, with the exact one-step compiled-call overhead. -/
theorem liftInner_update_run (s : OuterStore) (code : Code) (K : ℕ)
    (i : Fin 256) (bits : List Bool)
    (h : ExecutesIn code K (projectInner s) (Function.update (projectInner s) i bits)) :
    ExecutesOuter (liftInner code) (K+1) s (Function.update s (innerPort i) bits) := by
  have hh := liftInner_run s code K _ h
  simpa only [replaceInner_update,replaceInner_project] using hh

theorem literalPopped (s : OuterStore) (count acc : List Bool) (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped literalPorts (⟨regs,literalReady s count acc⟩ : OuterData)=
      (⟨readRegs regs 0 1 count.head?,literalReady s count.tail acc⟩ : OuterData) := by
  apply state_ext
  · simp [UnaryForPrograms.popped,literalPorts,literalReady]
  · funext i
    by_cases h573 : i=573 <;> by_cases h569 : i=569 <;>
      simp [UnaryForPrograms.popped, literalPorts, literalReady, h573, h569]

theorem literalRecord_length_le (n L j : ℕ) (hj : j<n)
    (bits : List Bool) (hb : bits.length≤L) :
    (Encoding.frame (Encoding.encodeNat j)++Encoding.frame bits).length≤
      literalRecordBound n L := by
  simp only [List.length_append,Encoding.length_frame,Encoding.encodeNat,
    List.length_replicate,List.length_singleton,literalRecordBound]
  omega

theorem rel_tableResult_congr (f g : ℕ → List Bool) (j : ℕ)
    (h : ∀ i,i<j → f i=g i) (acc : List Bool) :
    tableResult f j acc=tableResult g j acc := by
  induction j generalizing acc with
  | zero => rfl
  | succ j ih =>
      have he : tableRecord f j=tableRecord g j := by
        simp only [tableRecord,h j (by omega)]
      simp only [tableResult,he]
      exact ih (fun i hi=>h i (by omega)) _

theorem rel_tableResult_length_le (f : ℕ → List Bool) (n L j : ℕ)
    (hj : j≤n) (h : ∀ i,i<j → (f i).length≤L) (acc : List Bool) :
    (tableResult f j acc).length≤acc.length+j*literalRecordBound n L := by
  induction j generalizing acc with
  | zero => simp [tableResult]
  | succ j ih =>
      have hr := literalRecord_length_le n L j (by omega) (f j) (h j (by omega))
      have ht := ih (by omega) (fun i hi=>h i (by omega)) (tableRecord f j++acc)
      change (tableRecord f j).length≤literalRecordBound n L at hr
      simp only [tableResult,List.length_append] at ht ⊢
      nlinarith

/-- Every witness is chosen along this actual run. The capacity invariant
reserves room for all remaining records before invoking the bounded body. -/
theorem literalLoop_rel_visits (s : OuterStore) (body : OuterCode)
    (P : ℕ → List Bool → Prop) (K n L : ℕ)
    (hbody : RelLiteralBody s body P K n L)
    (j : ℕ) (hj : j≤n) (acc : List Bool)
    (hcap : acc.length+j*literalRecordBound n L≤n*literalRecordBound n L)
    (regs : Fin 16 → Bool) :
    ∃ payload costs k rf,
      (∀ i,i<j → (payload i).length≤L ∧ P i (payload i)) ∧
      k≤j*(K+2)+2 ∧
      UnaryForPrograms.Visits literalPorts body costs k
        (⟨regs,literalReady s (List.replicate j true) acc⟩ : OuterData)
        (⟨rf,literalReady s [] (tableResult payload j acc)⟩ : OuterData) := by
  induction j generalizing acc regs with
  | zero =>
      refine ⟨fun _=>[],[],2,readRegs regs 0 1 none,?_,by simp,?_⟩
      · intro i hi; omega
      · simpa [literalPopped,tableResult] using
          UnaryForPrograms.Visits.done (p:=literalPorts) (body:=body)
            (⟨regs,literalReady s [] acc⟩ : OuterData) (by simp [literalReady,literalPorts])
  | succ j ih =>
      have hac : acc.length≤n*literalRecordBound n L := by nlinarith
      obtain ⟨bits,kb,rb,hkb,hbits,hP,hbe⟩ :=
        hbody.run j (by omega) acc hac (readRegs regs 0 1 (some true))
      let next := Encoding.frame (Encoding.encodeNat j)++Encoding.frame bits++acc
      have hr := literalRecord_length_le n L j (by omega) bits hbits
      have hn : next.length≤literalRecordBound n L+acc.length := by
        simpa only [next,List.length_append] using Nat.add_le_add_right hr acc.length
      have hnext : next.length+j*literalRecordBound n L≤n*literalRecordBound n L := by
        nlinarith
      obtain ⟨f,costs,kt,rt,hf,hkt,ht⟩ := ih (by omega) next hnext rb
      let payload := Function.update f j bits
      have hp : ∀ i,i<j+1 → (payload i).length≤L ∧ P i (payload i) := by
        intro i hi
        by_cases he : i=j
        · subst i; simpa [payload] using And.intro hbits hP
        · simpa [payload,he] using hf i (by omega)
      have htable : tableResult payload (j+1) acc=tableResult f j next := by
        change tableResult payload j (tableRecord payload j++acc)=_
        have he : tableRecord payload j++acc=next := by
          simp [payload,tableRecord,next,List.append_assoc]
        rw [he]
        apply rel_tableResult_congr
        intro i hi
        simp [payload,show i≠j by omega]
      refine ⟨payload,kb::costs,kb+kt+2,rt,hp,?_,?_⟩
      · nlinarith
      · rw [htable]
        apply UnaryForPrograms.Visits.step (p:=literalPorts) (body:=body)
          (d:=(⟨regs,literalReady s (List.replicate (j+1) true) acc⟩ : OuterData))
          (by simp [literalReady,literalPorts])
          (by simpa only [literalPopped,List.replicate_succ,List.head?_cons,List.tail_cons,next] using hbe)
          (by simp [literalReady,literalPorts,UnaryForPrograms.popped,List.replicate_succ]) ht

/-- Relational counted loop with an explicit actual-register execution. -/
theorem literalLoop_rel_run (s : OuterStore) (body : OuterCode)
    (P : ℕ → List Bool → Prop) (K n L : ℕ)
    (hbody : RelLiteralBody s body P K n L)
    (j : ℕ) (hj : j≤n) (acc : List Bool)
    (hcap : acc.length+j*literalRecordBound n L≤n*literalRecordBound n L)
    (regs : Fin 16 → Bool) :
    ∃ (payload : ℕ → List Bool) (k : ℕ) (rf : Fin 16 → Bool),
      (∀ i,i<j → (payload i).length≤L ∧ P i (payload i)) ∧
      k≤j*(K+2)+2 ∧
      Eval (UnaryForPrograms.forCmd literalPorts body) k
        (⟨regs,literalReady s (List.replicate j true) acc⟩ : OuterData)
        (⟨rf,literalReady s [] (tableResult payload j acc)⟩ : OuterData) := by
  obtain ⟨payload,costs,k,rf,hp,hk,hv⟩ :=
    literalLoop_rel_visits s body P K n L hbody j hj acc hcap regs
  exact ⟨payload,k,rf,hp,hk,hv.eval⟩

/-- Full native table producer with actual-run witnesses, measured master copy,
loop, and output move. No payload family uniform over registers is required. -/
theorem prepareFactor_rel_run (s : OuterStore) (P : ℕ → List Bool → Prop) (K n L : ℕ)
    (hn : s 552=List.replicate n true)
    (h460 : s 460=[]) (h573 : s 573=[]) (h569 : s 569=[])
    (h561 : s 561=[]) (h585 : s 585=[])
    (hbody : RelLiteralBody s literalIteration P K n L)
    (regs : Fin 16 → Bool) :
    ∃ (payload : ℕ → List Bool) (k : ℕ) (rf : Fin 16 → Bool),
      (∀ j,j<n → (payload j).length≤L ∧ P j (payload j)) ∧
      k≤7*n+n*(K+2)+6*n*literalRecordBound n L+15 ∧
      Eval prepareFactor k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update s 561 (tableResult payload n [])⟩ : OuterData) := by
  let a := literalReady s (List.replicate n true) []
  have hc : ExecutesOuter (liftInner (copy 212 233)) (7*n+6) s a := by
    have h := liftInner_update_run s (copy 212 233) (7*n+5) 233 (List.replicate n true) (by
      simpa [projectInner,Function.comp_def,innerPort,hn,h573] using
        copy_run 212 233 (projectInner s) (by decide) (by decide) (by decide)
          (by simpa [projectInner,Function.comp_def,innerPort] using h460))
    have heq : Function.update s (innerPort 233) (List.replicate n true)=a := by
      funext i
      by_cases hi : i=569 <;> simp [a,literalReady,Function.update_apply,innerPort,hi,h569]
    simpa [heq] using h
  obtain ⟨kc,rc,hkc,hec⟩ := hc.run regs
  obtain ⟨payload,kl,rl,hp,hkl,hel⟩ :=
    literalLoop_rel_run s literalIteration P K n L hbody n (by omega) [] (by simp) rc
  let b := literalReady s [] (tableResult payload n [])
  have hm : ExecutesOuter (liftInner (SubexpPolynomialConstructor.move 229 221))
      (6*(tableResult payload n []).length+7) b
      (Function.update s 561 (tableResult payload n [])) := by
    have h := liftInner_run b (SubexpPolynomialConstructor.move 229 221)
      (6*(tableResult payload n []).length+6)
      (Function.update (Function.update (projectInner b) 229 []) 221 (tableResult payload n [])) (by
        simpa [projectInner,Function.comp_def,innerPort,b,literalReady] using
          SubexpPolynomialConstructor.move_run (projectInner b) 229 221
            (by decide) (by decide) (by decide)
            (by simp [projectInner, innerPort, b, literalReady, h585])
            (by simp [projectInner, innerPort, b, literalReady, h561]))
    rw [replaceInner_update,replaceInner_update,replaceInner_project] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    by_cases h561' : i=561
    · subst i; simp [innerPort]
    by_cases h569' : i=569
    · subst i; simp [innerPort,h569]
    by_cases h573' : i=573
    · subst i; simp [innerPort,b,literalReady,h573]
    simp [innerPort, b, literalReady, h561', h569', h573']
  obtain ⟨km,rm,hkm,hem⟩ := hm.run rl
  have hlen := rel_tableResult_length_le payload n L n (by omega) (fun i hi=>(hp i hi).1) []
  simp only [List.length_nil,Nat.zero_add] at hlen
  refine ⟨payload,kc+(kl+km),rm,hp,?_,hec.seq (hel.seq hem)⟩
  nlinarith

theorem initialize_eval (a : OuterData) :
    Eval initializeWorker (SubexpSetupStorage.clearManyCost entryPorts a) a (initialized a) :=
  SubexpSetupStorage.clearMany_eval entryPorts a

theorem initialized_output (a : OuterData) : (initialized a).stacks 62 = [] := by
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_left]
  exact List.mem_append_right _ (by simp)

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

theorem export_eval (a : OuterData) (htmp : a.stacks 684 = []) :
    Eval (liftBase LeafProgram.Incidence.exportResult) (exportCost a) a (exported a) := by
  apply eval_liftCommand_from_state _ 0 0 id basePort a
    Function.injective_id basePort_injective
  apply LeafProgram.Incidence.export_eval
  exact htmp

theorem exported_output (a : OuterData) (h62 : a.stacks 62 = []) :
    (exported a).stacks 62 = a.stacks 561 := by
  change (exported a).stacks (basePort 62) = a.stacks 561
  rw [exported, embedState_stack _ _ _ _ basePort_injective]
  exact LeafProgram.Incidence.exported_output _ h62

/-- Every initialization, staging, table iteration, export and cleanup
instruction belongs to this same fixed program. -/
theorem command_eval (a b : OuterData) (steps : ℕ)
    (he : Eval prepareFactor steps (staged a) b) (htmp : b.stacks 684 = []) :
    Eval command (SubexpSetupStorage.clearManyCost entryPorts a +
      (stageCost a + (steps + exportCost b))) a (exported b) :=
  (initialize_eval a).seq ((stage_eval a).seq (he.seq (export_eval b htmp)))

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

/-- The output is copied into its freshly cleared destination before all340
private source stacks are reclaimed. -/
theorem original_exportCost_le (a : LeafProgram.Incidence.Data) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) (h62 : a.stacks 62 = []) :
    LeafProgram.Incidence.exportCost a ≤ 687 * B + 1025 := by
  have hcopy : ∀ i, ((SubexpSetupStorage.copyState 561 62 a).stacks i).length ≤ B := by
    intro i
    by_cases hi : i = 62
    · subst i
      simpa [SubexpSetupStorage.copyState_stack, h62] using hb 561
    · simpa [SubexpSetupStorage.copyState_stack, hi] using hb i
  have hc := SubexpSetupStorage.clearManyCost_le LeafProgram.Incidence.workerPorts
    (SubexpSetupStorage.copyState 561 62 a) B hcopy
  have hlen : LeafProgram.Incidence.workerPorts.length = 340 := by
    simp only [LeafProgram.Incidence.workerPorts, List.length_map, List.length_finRange]
  rw [hlen] at hc
  have hr := hb 561
  dsimp only [LeafProgram.Incidence.exportCost]
  omega

/-- One additional instruction invokes the relocated exporter. -/
theorem exportCost_le (a : OuterData) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) (h62 : a.stacks 62 = []) :
    exportCost a ≤ 687 * B + 1026 := by
  have h := original_exportCost_le (projectState id basePort a) B
    (fun i => hb (basePort i)) h62
  dsimp only [exportCost]
  omega

private theorem original_staged_frame (a : LeafProgram.Incidence.Data) (i : Fin 768)
    (hi : i = 62 ∨ i = 684) : (LeafProgram.Incidence.staged a).stacks i = a.stacks i := by
  have h550 : i ≠ 550 := by rcases hi with rfl | rfl <;> decide
  change Function.update (SubexpSetupStorage.copyManyState LeafProgram.Incidence.pairs a).stacks
    550 _ i = a.stacks i
  rw [Function.update_of_ne h550]
  apply SubexpSetupStorage.copyMany_frame
  intro p hp
  simp only [LeafProgram.Incidence.pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;>
    rcases hi with rfl | rfl <;> decide

/-- Entry clearing and the paid staging leave the export destination empty. -/
theorem staged_output (a : OuterData) : (staged a).stacks 62 = [] := by
  change (staged a).stacks (basePort 62) = []
  rw [staged, embedState_stack _ _ _ _ basePort_injective,
    original_staged_frame _ 62 (Or.inl rfl)]
  simpa only [projectState, Function.comp_apply,
    show basePort 62 = (62 : Fin 896) from rfl] using initialized_output a

/-- The stage also returns the physical copy temporary empty. -/
theorem staged_temporary (a : OuterData) : (staged a).stacks 684 = [] := by
  change (staged a).stacks (basePort 684) = []
  rw [staged, embedState_stack _ _ _ _ basePort_injective,
    original_staged_frame _ 684 (Or.inr rfl)]
  simpa only [projectState, Function.comp_apply,
    show basePort 684 = (684 : Fin 896) from rfl] using initialized_temporary a

theorem initialized_frame (a : OuterData) (i : Fin 896) (hi : i ∉ writtenPorts) :
    (initialized a).stacks i = a.stacks i := by
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_right]
  intro he
  apply hi
  rcases List.mem_append.mp he with he | he
  · obtain ⟨j, hj, hji⟩ := List.mem_map.mp he
    exact List.mem_append_left _ (List.mem_map.mpr ⟨j, (List.mem_filter.mp hj).1, hji⟩)
  · exact List.mem_append_right _ he

private theorem original_staged_worker_frame (a : LeafProgram.Incidence.Data) (i : Fin 768)
    (hi : i ∉ LeafProgram.Incidence.workerPorts) :
    (LeafProgram.Incidence.staged a).stacks i = a.stacks i := by
  have h550 : i ≠ 550 := by
    intro he
    subst i
    exact hi ((LeafProgram.Incidence.mem_workerPorts 550).mpr (by decide))
  change Function.update (SubexpSetupStorage.copyManyState LeafProgram.Incidence.pairs a).stacks
    550 _ i = a.stacks i
  rw [Function.update_of_ne h550]
  apply SubexpSetupStorage.copyMany_frame
  intro p hp he
  apply hi
  rw [he]
  apply (LeafProgram.Incidence.mem_workerPorts p.2).mpr
  simp only [LeafProgram.Incidence.pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide

/-- All caller masters outside the finite write set survive actual staging. -/
theorem staged_frame (a : OuterData) (i : Fin 896) (hi : i ∉ writtenPorts) :
    (staged a).stacks i = a.stacks i := by
  by_cases himage : ∃ j, basePort j = i
  · obtain ⟨j, rfl⟩ := himage
    have hj : j ∉ LeafProgram.Incidence.workerPorts := by
      intro hj
      exact hi (List.mem_append_left _ (List.mem_map.mpr ⟨j, hj, rfl⟩))
    rw [staged, embedState_stack _ _ _ _ basePort_injective,
      original_staged_worker_frame _ j hj]
    simpa only [projectState, Function.comp_apply] using initialized_frame a (basePort j) hi
  · change (embedState id basePort (initialized a) _).stacks i = a.stacks i
    rw [embedState_stack_frame _ _ _ _ i himage]
    exact initialized_frame a i hi

/-- Export and cleanup preserve every caller port outside the write set. -/
theorem exported_frame (a : OuterData) (i : Fin 896) (hi : i ∉ writtenPorts) :
    (exported a).stacks i = a.stacks i := by
  by_cases himage : ∃ j, basePort j = i
  · obtain ⟨j, rfl⟩ := himage
    have hj : j ∉ LeafProgram.Incidence.workerPorts := by
      intro hj
      exact hi (List.mem_append_left _ (List.mem_map.mpr ⟨j, hj, rfl⟩))
    have hj62 : j ≠ 62 := by
      intro he
      subst j
      apply hi
      exact List.mem_append_right _ (by simp [basePort])
    rw [exported, embedState_stack _ _ _ _ basePort_injective,
      LeafProgram.Incidence.exported, SubexpSetupStorage.clearMany_stacks, ite_eq_right hj,
      SubexpSetupStorage.copyState_frame _ _ _ _ hj62]
    rfl
  · exact embedState_stack_frame _ _ _ _ i himage

/-- The exact output state used by the whole command preserves the node
ports, source masters and all other caller words outside its private writes. -/
theorem command_output_frame (a : OuterData) (rf : Fin 16 → Bool) (bytes : List Bool)
    (i : Fin 896) (hi : i ∉ writtenPorts) :
    (exported (⟨rf, Function.update (staged a).stacks 561 bytes⟩ : OuterData)).stacks i =
      a.stacks i := by
  have hi561 : i ≠ 561 := by
    intro he
    subst i
    apply hi
    exact List.mem_append_left _ (List.mem_map.mpr ⟨561,
      (LeafProgram.Incidence.mem_workerPorts 561).mpr (by decide), rfl⟩)
  rw [exported_frame _ i hi]
  change Function.update (staged a).stacks 561 bytes i = a.stacks i
  rw [Function.update_of_ne hi561]
  exact staged_frame a i hi

/-- Actual export clears the complete private worker and every initialized
backup, leaving only the full table on output62. -/
theorem command_output_clean (a : OuterData) (rf : Fin 16 → Bool) (bytes : List Bool)
    (i : Fin 896) (hi : i ∈ writtenPorts) (hne : i ≠ 62) :
    (exported (⟨rf, Function.update (staged a).stacks 561 bytes⟩ : OuterData)).stacks i = [] := by
  have hbase (j : Fin 768) (hj : j ∉ LeafProgram.Incidence.workerPorts)
      (hj62 : j≠62) (hj561 : basePort j≠561) (hentry : basePort j ∈ entryPorts) :
      (exported (⟨rf, Function.update (staged a).stacks 561 bytes⟩ : OuterData)).stacks
        (basePort j) = [] := by
    rw [exported,embedState_stack _ _ _ _ basePort_injective,
      LeafProgram.Incidence.exported,SubexpSetupStorage.clearMany_stacks,ite_eq_right hj,
      SubexpSetupStorage.copyState_frame _ _ _ _ hj62]
    change Function.update (staged a).stacks 561 bytes (basePort j) = []
    rw [Function.update_of_ne hj561,staged,embedState_stack _ _ _ _ basePort_injective,
      original_staged_worker_frame _ j hj]
    change (initialized a).stacks (basePort j) = []
    rw [initialized,SubexpSetupStorage.clearMany_stacks,ite_eq_left hentry]
  have hhigh (j : Fin 896) (hj : j=881 ∨ j=882) :
      (exported (⟨rf, Function.update (staged a).stacks 561 bytes⟩ : OuterData)).stacks j = [] := by
    have hout : ¬∃ v, basePort v=j := by
      apply basePort_outside j
      rcases hj with rfl|rfl <;> exact Or.inr ⟨by decide,Or.inl (by decide)⟩
    have h561 : j≠561 := by rcases hj with rfl|rfl <;> decide
    have hentry : j ∈ entryPorts := by
      apply List.mem_append_right
      rcases hj with rfl|rfl <;> simp
    rw [exported,embedState_stack_frame _ _ _ _ j hout]
    change Function.update (staged a).stacks 561 bytes j = []
    rw [Function.update_of_ne h561,staged,embedState_stack_frame _ _ _ _ j hout,
      initialized,SubexpSetupStorage.clearMany_stacks,ite_eq_left hentry]
  rcases List.mem_append.mp hi with hi|hi
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    rw [exported,embedState_stack _ _ _ _ basePort_injective,
      LeafProgram.Incidence.exported,SubexpSetupStorage.clearMany_stacks,ite_eq_left hj]
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact (hne rfl).elim
    · exact hbase 680 (by rw [LeafProgram.Incidence.mem_workerPorts]; decide)
        (by decide) (by decide) (List.mem_append_right _ (by simp [basePort]))
    · exact hbase 681 (by rw [LeafProgram.Incidence.mem_workerPorts]; decide)
        (by decide) (by decide) (List.mem_append_right _ (by simp [basePort]))
    · exact hbase 682 (by rw [LeafProgram.Incidence.mem_workerPorts]; decide)
        (by decide) (by decide) (List.mem_append_right _ (by simp [basePort]))
    · exact hbase 683 (by rw [LeafProgram.Incidence.mem_workerPorts]; decide)
        (by decide) (by decide) (List.mem_append_right _ (by simp [basePort]))
    · exact hbase 684 (by rw [LeafProgram.Incidence.mem_workerPorts]; decide)
        (by decide) (by decide) (List.mem_append_right _ (by simp [basePort]))
    · exact hhigh 881 (Or.inl rfl)
    · exact hhigh 882 (Or.inr rfl)

/-- Exact table output, runtime and every source prefix of the same closed
command. The relational literal contract is instantiated by the concrete
producer; it is not an extra premise of the final counting theorem. -/
theorem command_resources_oai (a : OuterData) (B n K L : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B)
    (hn : (staged a).stacks 552 = List.replicate n true)
    (h460 : (staged a).stacks 460 = []) (h573 : (staged a).stacks 573 = [])
    (h569 : (staged a).stacks 569 = []) (h561 : (staged a).stacks 561 = [])
    (h585 : (staged a).stacks 585 = [])
    (P : ℕ → List Bool → Prop)
    (hbody : RelLiteralBody (staged a).stacks literalIteration P K n L) :
    ∃ (payload : ℕ → List Bool) (steps : ℕ) (e : OuterData),
      (∀ j, j < n → (payload j).length ≤ L ∧ P j (payload j)) ∧
      steps ≤ commandBudget B n K L ∧
      Trace program steps (a.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks 62 = tableResult payload n [] ∧
      (∀ i, i ∉ writtenPorts → e.stacks i = a.stacks i) ∧
      (∀ i ∈ writtenPorts, i≠62 → e.stacks i=[]) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896 * B + commandBudget B n K L := by
  obtain ⟨payload, k, rf, hpayload, hk, he⟩ :=
    prepareFactor_rel_run (staged a).stacks P K n L hn h460 h573 h569 h561 h585 hbody
      (staged a).regs
  let middle : OuterData := ⟨rf, Function.update (staged a).stacks 561 (tableResult payload n [])⟩
  have hlen := rel_tableResult_length_le payload n L n le_rfl
    (fun i hi => (hpayload i hi).1) []
  simp only [List.length_nil, Nat.zero_add] at hlen
  have hmiddle : ∀ i, (middle.stacks i).length ≤ middleBound B n L := by
    intro i
    have hs := staged_stack_bound a B hb i
    by_cases hi : i = 561
    · subst i
      change (tableResult payload n []).length ≤ middleBound B n L
      dsimp only [middleBound]
      omega
    · change (Function.update (staged a).stacks 561 (tableResult payload n []) i).length ≤ _
      rw [Function.update_of_ne hi]
      dsimp only [middleBound]
      omega
  have hm62 : middle.stacks 62 = [] := by simpa [middle] using staged_output a
  have hmtmp : middle.stacks 684 = [] := by simpa [middle] using staged_temporary a
  have hrun := command_eval a middle k he hmtmp
  have hkc : k ≤ tableBudget n K L := by
    dsimp only [tableBudget, literalRecordBound] at hk ⊢
    nlinarith only [hk]
  have hclear := SubexpSetupStorage.clearManyCost_le entryPorts a B hb
  have hstage := stageCost_le a B hb
  have hexport := exportCost_le middle (middleBound B n L) hmiddle hm62
  have htotal : SubexpSetupStorage.clearManyCost entryPorts a +
      (stageCost a + (k + exportCost middle)) + 1 ≤ commandBudget B n K L := by
    dsimp only [commandBudget]
    omega
  refine ⟨payload, _, exported middle, hpayload, htotal,
    compiled_halt_trace hrun 556 62, ?_, ?_, ?_, ?_⟩
  · exact (exported_output middle hm62).trans (by simp [middle])
  · intro i hi
    exact command_output_frame a rf (tableResult payload n []) i hi
  · intro i hi hne
    exact command_output_clean a rf (tableResult payload n []) i hi hne
  · intro prefixSteps intermediate hp ht i
    exact StructuredSpace.local_stack_bound program (StreamResources.dataBits_le_mul _ hb)
      prefixSteps intermediate (hp.trans htotal) ht i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.command_resources_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.command_resources_oai
