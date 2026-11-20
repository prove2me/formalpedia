-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.fresh_child_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:26:07.299232+00:00
-- url     : https://prove2.me/submissions/de29de95-9a51-480a-8811-809f8ffbc50c

import Batteries.Data.BinomialHeap
import Definitions.Def_NearlyOptimalPPR_Computation_compiler_runtime
import Definitions.Def_NearlyOptimalPPR_Computation_machine
import Definitions.Def_NearlyOptimalPPR_Computation_proof_invariants
import Definitions.Def_NearlyOptimalPPR_Computation_push
import Definitions.Def_NearlyOptimalPPR_Computation_recursive
import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Theorems.Thm_NearlyOptimalPPR_Computation_active_region_potentials
import Theorems.Thm_NearlyOptimalPPR_Computation_normalization_composes
import Theorems.Thm_NearlyOptimalPPR_Computation_push_correctness_work
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_level_work
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_residual_error
set_option linter.all false
-- Proof module: Solutions.StructuredMachine

set_option autoImplicit false
open Finset Matrix MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def straightInstruction (i : Instruction) : Prop :=
  match i with
  | .scalar (.core (.jle ..)) | .scalar (.core (.pjle ..)) |
    .scalar (.core .accept) | .scalar (.core .reject) | .scalar .halt => False
  | _ => True


namespace MachineCode

def size : MachineCode → ℕ
  | .skip => 0
  | .atom _ => 1
  | .seq a b => size a + size b
  | .branchReal _ a b | .branchPointer _ _ a b => size a + size b + 2
  | .whileReal _ b | .whilePointer _ _ b => size b + 2


def wellFormed : MachineCode → Prop
  | .skip => True
  | .atom i => straightInstruction i ∧ admissible [i]
  | .seq a b | .branchReal _ a b | .branchPointer _ _ a b => wellFormed a ∧ wellFormed b
  | .whileReal _ b | .whilePointer _ _ b => wellFormed b

end MachineCode
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MachineRelocation

set_option autoImplicit false
open Finset Matrix MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


@[simp] lemma pcSet_pc (st : MachineState) (pc : ℕ) : (pcSet st pc).scalar.core.pc=pc := rfl
@[simp] lemma pcSet_halted (st : MachineState) (pc : ℕ) : (pcSet st pc).scalar.halted=st.scalar.halted := rfl
@[simp] lemma pcSet_work (st : MachineState) (pc : ℕ) : (pcSet st pc).work=st.work := rfl
@[simp] lemma pcSet_set (st : MachineState) (a b : ℕ) : pcSet (pcSet st a) b=pcSet st b := rfl
@[simp] lemma pcSet_self (st : MachineState) : pcSet st st.scalar.core.pc=st := rfl

@[simp] lemma suppliedMatrix_PC (st : LocalPush.State) (pc : ℕ) (r : SolveRegisters) (k q : ℕ) :
    suppliedMatrix {st with core := {st.core with pc := pc}} r k q = suppliedMatrix st r k q := rfl

set_option maxRecDepth 4096 in
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MachineBranches

set_option autoImplicit false
open Finset Matrix MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


@[simp] lemma payUnit_pcSet (st : MachineState) (k : ℕ) : payUnit (pcSet st k)=payUnit st := rfl

@[simp] lemma pcSet_regs (st : MachineState) (k : ℕ) : (pcSet st k).scalar.core.regs=st.scalar.core.regs := rfl
@[simp] lemma pcSet_ptrs (st : MachineState) (k : ℕ) : (pcSet st k).scalar.core.ptrs=st.scalar.core.ptrs := rfl

@[simp] lemma payUnit_pc (st : MachineState) : (payUnit st).scalar.core.pc=0 := rfl
@[simp] lemma payUnit_halted (st : MachineState) : (payUnit st).scalar.halted=st.scalar.halted := rfl
@[simp] lemma payUnit_regs (st : MachineState) : (payUnit st).scalar.core.regs=st.scalar.core.regs := rfl
@[simp] lemma payUnit_ptrs (st : MachineState) : (payUnit st).scalar.core.ptrs=st.scalar.core.ptrs := rfl
@[simp] lemma payUnit_work (st : MachineState) : (payUnit st).work=st.work+1 := rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MachineCodeSemantics

set_option autoImplicit false
open Finset Matrix MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma atomState_halted (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (i : Instruction) (st : MachineState) (hs : straightInstruction i) :
    (atomState m g ω i st).scalar.halted=st.scalar.halted := by
  classical
  by_cases hh : st.scalar.halted=true
  · simp [atomState,machineStep,hh]
  have hh : st.scalar.halted=false := Bool.eq_false_iff.mpr hh
  cases i with
  | solve r => simp [atomState,machineStep,pcSet,hh]; split_ifs <;> rfl
  | emit a b => simp [atomState,machineStep,pcSet,hh]
  | scalar i =>
    cases i with
    | halt => simp [straightInstruction] at hs
    | core c =>
      cases c <;> simp_all [atomState,machineStep,pcSet,LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep]
    | _ => simp [atomState,machineStep,pcSet,hh,LocalPush.step,scalarProgram]

lemma MachineEval.halted {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {code : MachineCode} {st out : MachineState} {u : ℕ}
    (e : MachineEval m g ω code st u out) (h : code.wellFormed) :
    out.scalar.halted=st.scalar.halted := by
  induction e <;> simp_all [MachineCode.wellFormed,atomState_halted]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ScalarCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


def realWrite (st : MachineState) (r : ℕ) (x : ℝ) : MachineState :=
  {st with scalar := {st.scalar with core := {st.scalar.core with regs := Function.update st.scalar.core.regs r x}}}

def pointerWrite (st : MachineState) (r : ℕ) (x : ℤ) : MachineState :=
  {st with scalar := {st.scalar with core := {st.scalar.core with ptrs := Function.update st.scalar.core.ptrs r x}}}

@[simp] lemma pcSet_payUnit_zero (st : MachineState) : pcSet (payUnit st) 0=payUnit st := rfl

lemma const_atomState (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r : ℕ) (x : ℝ) (hh : st.scalar.halted=false) :
    atomState m g ω (.scalar (.core (.const r x))) st=pcSet (payUnit (realWrite st r x)) 1 := by
  simp [atomState,machineStep,pcSet,payUnit,realWrite,hh,LocalPush.step,scalarProgram,
    LocalPush.coreProgram,SmaleNinth.RAMStep]

lemma const_eval (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r : ℕ) (x : ℝ) (hh : st.scalar.halted=false) :
    MachineEval m g ω (.atom (.scalar (.core (.const r x)))) st 1 (payUnit (realWrite st r x)) := by
  have h := MachineEval.atom (.scalar (.core (.const r x))) st
    (by rw [const_atomState m g ω st r x hh]; rfl)
  simpa only [const_atomState m g ω st r x hh,pcSet_set,pcSet_payUnit_zero] using h

lemma binary_atomState (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (op : RealOperation) (r a b : ℕ) (hh : st.scalar.halted=false) :
    atomState m g ω (op.instruction r a b) st=pcSet
      (payUnit (realWrite st r (op.value (st.scalar.core.regs a) (st.scalar.core.regs b)))) 1 := by
  cases op <;> simp [RealOperation.instruction,RealOperation.value,atomState,machineStep,pcSet,payUnit,
    realWrite,hh,LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep]

lemma binary_eval (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (op : RealOperation) (r a b : ℕ) (hh : st.scalar.halted=false) :
    MachineEval m g ω (.atom (op.instruction r a b)) st 1
      (payUnit (realWrite st r (op.value (st.scalar.core.regs a) (st.scalar.core.regs b)))) := by
  have h := MachineEval.atom (op.instruction r a b) st
    (by rw [binary_atomState m g ω st op r a b hh]; rfl)
  simpa only [binary_atomState m g ω st op r a b hh,pcSet_set,pcSet_payUnit_zero] using h

lemma pset_atomState (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r : ℕ) (x : ℤ) (hh : st.scalar.halted=false) :
    atomState m g ω (.scalar (.core (.pset r x))) st=pcSet (payUnit (pointerWrite st r x)) 1 := by
  simp [atomState,machineStep,pcSet,payUnit,pointerWrite,hh,LocalPush.step,scalarProgram,
    LocalPush.coreProgram,SmaleNinth.RAMStep]

lemma pset_eval (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r : ℕ) (x : ℤ) (hh : st.scalar.halted=false) :
    MachineEval m g ω (.atom (.scalar (.core (.pset r x)))) st 1 (payUnit (pointerWrite st r x)) := by
  have h := MachineEval.atom (.scalar (.core (.pset r x))) st
    (by rw [pset_atomState m g ω st r x hh]; rfl)
  simpa only [pset_atomState m g ω st r x hh,pcSet_set,pcSet_payUnit_zero] using h

lemma pinc_atomState (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r : ℕ) (hh : st.scalar.halted=false) :
    atomState m g ω (.scalar (.core (.pinc r))) st=
      pcSet (payUnit (pointerWrite st r (st.scalar.core.ptrs r+1))) 1 := by
  simp [atomState,machineStep,pcSet,payUnit,pointerWrite,hh,LocalPush.step,scalarProgram,
    LocalPush.coreProgram,SmaleNinth.RAMStep]

lemma pinc_eval (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r : ℕ) (hh : st.scalar.halted=false) :
    MachineEval m g ω (.atom (.scalar (.core (.pinc r)))) st 1
      (payUnit (pointerWrite st r (st.scalar.core.ptrs r+1))) := by
  have h := MachineEval.atom (.scalar (.core (.pinc r))) st
    (by rw [pinc_atomState m g ω st r hh]; rfl)
  simpa only [pinc_atomState m g ω st r hh,pcSet_set,pcSet_payUnit_zero] using h

lemma pcopy_atomState (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r a : ℕ) (hh : st.scalar.halted=false) :
    atomState m g ω (.scalar (.core (.pcopy r a))) st=
      pcSet (payUnit (pointerWrite st r (st.scalar.core.ptrs a))) 1 := by
  simp [atomState,machineStep,pcSet,payUnit,pointerWrite,hh,LocalPush.step,scalarProgram,
    LocalPush.coreProgram,SmaleNinth.RAMStep]

lemma pcopy_eval (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r a : ℕ) (hh : st.scalar.halted=false) :
    MachineEval m g ω (.atom (.scalar (.core (.pcopy r a)))) st 1
      (payUnit (pointerWrite st r (st.scalar.core.ptrs a))) := by
  have h := MachineEval.atom (.scalar (.core (.pcopy r a))) st
    (by rw [pcopy_atomState m g ω st r a hh]; rfl)
  simpa only [pcopy_atomState m g ω st r a hh,pcSet_set,pcSet_payUnit_zero] using h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PowerCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma powerCode_wellFormed : powerCode.wellFormed := by
  simp [powerCode,powerLoop,powerBody,MachineCode.wellFormed,RealOperation.instruction,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨1,by norm_num⟩

set_option maxHeartbeats 500000 in
lemma power_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (k a : ℕ) (x y : ℝ) (st : MachineState) (hh : st.scalar.halted=false)
    (hcounter : st.scalar.core.ptrs 0=(a : ℤ))
    (hlimit : st.scalar.core.ptrs 1=((a+k : ℕ) : ℤ))
    (hbase : st.scalar.core.regs 0=x) (hacc : st.scalar.core.regs 1=y) :
    ∃ out, MachineEval m g ω powerLoop st (4*k+1) out ∧
      out.scalar.core.ptrs 0=((a+k : ℕ) : ℤ) ∧ out.scalar.core.ptrs 1=((a+k : ℕ) : ℤ) ∧
      out.scalar.core.regs 0=x ∧ out.scalar.core.regs 1=y*x^k ∧
      out.work=st.work+(4*k+1 : ℕ) ∧ out.output=st.output := by
  induction k generalizing a y st with
  | zero =>
    refine ⟨payUnit st,?_,?_,?_,?_,?_,?_,?_⟩
    · exact MachineEval.pointerDone hh (by simp [hcounter,hlimit])
    all_goals simp_all [payUnit,pcSet]
  | succ k ih =>
    let first := payUnit (realWrite (payUnit st) 1 (y*x))
    let second := payUnit (pointerWrite first 0 ((a : ℤ)+1))
    let next := payUnit second
    have hf : first.scalar.halted=false := by simp [first,payUnit,pcSet,realWrite,hh]
    have eb1 : MachineEval m g ω (.atom (RealOperation.mul.instruction 1 1 0)) (payUnit st) 1 first := by
      simpa [first,RealOperation.value,hbase,hacc] using
        binary_eval m g ω (payUnit st) .mul 1 1 0 (by simpa using hh)
    have eb2 : MachineEval m g ω (.atom (.scalar (.core (.pinc 0)))) first 1 second := by
      simpa [second,first,payUnit,pcSet,realWrite,hcounter] using pinc_eval m g ω first 0 hf
    have eb : MachineEval m g ω powerBody (payUnit st) 2 second := MachineEval.seq eb1 eb2
    have hn : next.scalar.halted=false := by simp [next,second,payUnit,pcSet,pointerWrite,hf]
    have hc : next.scalar.core.ptrs 0=((a+1 : ℕ) : ℤ) := by simp [next,second,payUnit,pcSet,pointerWrite]
    have hl : next.scalar.core.ptrs 1=((a+1+k : ℕ) : ℤ) := by
      simp [next,second,first,payUnit,pcSet,pointerWrite,realWrite,hlimit]
      omega
    have hb : next.scalar.core.regs 0=x := by
      simp [next,second,first,payUnit,pcSet,pointerWrite,realWrite,hbase]
    have hy : next.scalar.core.regs 1=y*x := by
      simp [next,second,first,payUnit,pcSet,pointerWrite,realWrite]
    obtain ⟨out,er,hc',hl',hb',hy',hw',ho'⟩ := ih (a+1) (y*x) next hn hc hl hb hy
    have he := MachineEval.pointerNext hh (by rw [hlimit,hcounter]; push_cast; omega) eb er
    refine ⟨out,?_,?_,?_,hb',?_,?_,?_⟩
    · convert he using 1 <;> simp [powerLoop] <;> omega
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc'
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hl'
    · rw [hy',pow_succ]
      ring
    · rw [hw']
      simp [next,second,first,payUnit,pcSet,pointerWrite,realWrite]
      push_cast
      ring
    · simpa [next,second,first,payUnit,pcSet,pointerWrite,realWrite] using ho'

set_option maxHeartbeats 500000 in
lemma power_code_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (k : ℕ) (x : ℝ) (st : MachineState) (hh : st.scalar.halted=false)
    (hlimit : st.scalar.core.ptrs 1=(k : ℤ)) (hbase : st.scalar.core.regs 0=x) :
    ∃ out, MachineEval m g ω powerCode st (4*k+3) out ∧
      out.scalar.core.regs 1=x^k ∧ out.scalar.core.regs 0=x ∧
      out.scalar.core.ptrs 0=(k : ℤ) ∧ out.scalar.core.ptrs 1=(k : ℤ) ∧
      out.work=st.work+(4*k+3 : ℕ) ∧ out.output=st.output := by
  let first := payUnit (realWrite st 1 1)
  let init := payUnit (pointerWrite first 0 0)
  have e1 := const_eval m g ω st 1 1 hh
  have hf : first.scalar.halted=false := by simp [first,payUnit,pcSet,realWrite,hh]
  have e2 := pset_eval m g ω first 0 0 hf
  have hi : init.scalar.halted=false := by simp [init,payUnit,pcSet,pointerWrite,hf]
  obtain ⟨out,el,hc,hl,hb,hy,hw,ho⟩ := power_loop_exec m g ω k 0 x 1 init hi
    (by simp [init,payUnit,pcSet,pointerWrite])
    (by simp [init,first,payUnit,pcSet,pointerWrite,realWrite,hlimit])
    (by simp [init,first,payUnit,pcSet,pointerWrite,realWrite,hbase])
    (by simp [init,first,payUnit,pcSet,pointerWrite,realWrite])
  refine ⟨out,?_,by simpa using hy,hb,by simpa using hc,by simpa using hl,?_,?_⟩
  · have ee := MachineEval.seq e1 (MachineEval.seq e2 el)
    unfold powerCode
    rw [show 4*k+3=1+(1+(4*k+1)) by omega]
    exact ee
  · rw [hw]
    simp [init,first,payUnit,pcSet,pointerWrite,realWrite]
    ring
  · simpa [init,first,payUnit,pcSet,pointerWrite,realWrite] using ho

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CodeFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def MachineCode.allAtoms (P : Instruction → Prop) : MachineCode → Prop
  | .skip => True
  | .atom i => P i
  | .seq a b | .branchReal _ a b | .branchPointer _ _ a b => a.allAtoms P ∧ b.allAtoms P
  | .whileReal _ b | .whilePointer _ _ b => b.allAtoms P

lemma MachineEval.frame {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {code : MachineCode} {st out : MachineState} {u : ℕ}
    (e : MachineEval m g ω code st u out) {β : Type} (F : MachineState → β)
    (hpc : ∀ st pc, F (pcSet st pc)=F st) (hpay : ∀ st, F (payUnit st)=F st)
    (ha : code.allAtoms (fun i => ∀ st, F (atomState m g ω i st)=F st)) : F out=F st := by
  induction e <;> simp_all [MachineCode.allAtoms]

lemma power_code_frame (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    {st out : MachineState} {u : ℕ} (e : MachineEval m g ω powerCode st u out)
    {β : Type} (F : MachineState → β)
    (hpc : ∀ st pc, F (pcSet st pc)=F st) (hpay : ∀ st, F (payUnit st)=F st)
    (hr : ∀ st x, F (realWrite st 1 x)=F st)
    (hp : ∀ st x, F (pointerWrite st 0 x)=F st) : F out=F st := by
  apply e.frame F hpc hpay
  simp only [powerCode,powerLoop,powerBody,MachineCode.allAtoms]
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    intro z
    by_cases hh : z.scalar.halted=true
    · simp [atomState,machineStep,hh,hpc]
    · have hh : z.scalar.halted=false := Bool.eq_false_iff.mpr hh
      first
      | rw [const_atomState m g ω z 1 1 hh,hpc,hpay,hr]
      | rw [pset_atomState m g ω z 0 0 hh,hpc,hpay,hp]
      | rw [binary_atomState m g ω z .mul 1 1 0 hh,hpc,hpay,hr]
      | rw [pinc_atomState m g ω z 0 hh,hpc,hpay,hp]

lemma power_code_real_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    {st out : MachineState} {u : ℕ} (e : MachineEval m g ω powerCode st u out) :
    out.scalar.core.mem=st.scalar.core.mem :=
  power_code_frame m g ω e (fun z => z.scalar.core.mem) (by intros; rfl)
    (by intro; rfl) (by intros; rfl) (by intros; rfl)

lemma power_code_integer_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    {st out : MachineState} {u : ℕ} (e : MachineEval m g ω powerCode st u out) :
    out.scalar.integerMemory=st.scalar.integerMemory :=
  power_code_frame m g ω e (fun z => z.scalar.integerMemory) (by intros; rfl)
    (by intro; rfl) (by intros; rfl) (by intros; rfl)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PointerEffects

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def pointerTargets (i : Instruction) : Finset ℕ :=
  match i with
  | .scalar (.core (.pset r _)) | .scalar (.core (.pcopy r _)) |
    .scalar (.core (.pinc r)) | .scalar (.core (.pdec r)) |
    .scalar (.pointerAdd r _ _) | .scalar (.pointerSub r _ _) |
    .scalar (.integerLoad r _) | .scalar (.deg r _) | .scalar (.nbr r _ _) => {r}
  | _ => ∅

def MachineCode.pointerTargets : MachineCode → Finset ℕ
  | .skip => ∅
  | .atom i => NearlyOptimalPPR.Computation.pointerTargets i
  | .seq a b | .branchReal _ a b | .branchPointer _ _ a b => a.pointerTargets ∪ b.pointerTargets
  | .whileReal _ b | .whilePointer _ _ b => b.pointerTargets

lemma atomState_pointer_frame (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (i : Instruction) (st : MachineState) (r : ℕ) (hr : r ∉ pointerTargets i) :
    (atomState m g ω i st).scalar.core.ptrs r=st.scalar.core.ptrs r := by
  classical
  by_cases hh : st.scalar.halted=true
  · simp [atomState,machineStep,pcSet,hh]
  have hh : st.scalar.halted=false := Bool.eq_false_iff.mpr hh
  cases i with
  | emit a b => simp [atomState,machineStep,pcSet,hh]
  | solve s => simp [atomState,machineStep,pcSet,hh]; split_ifs <;> simp [writeAnswer]
  | scalar i =>
    cases i with
    | core i =>
      cases i <;> simp_all [pointerTargets,atomState,machineStep,pcSet,LocalPush.step,scalarProgram,
        LocalPush.coreProgram,SmaleNinth.RAMStep] <;> split_ifs <;> rfl
    | _ => simp_all [pointerTargets,atomState,machineStep,pcSet,LocalPush.step,scalarProgram]

lemma MachineCode.allAtoms_pointerTargets (code : MachineCode) (r : ℕ) (hr : r ∉ code.pointerTargets) :
    code.allAtoms (fun i => r ∉ NearlyOptimalPPR.Computation.pointerTargets i) := by
  induction code <;> simp_all [MachineCode.allAtoms,MachineCode.pointerTargets]

lemma MachineCode.allAtoms_mono (code : MachineCode) (P Q : Instruction → Prop)
    (h : ∀ i, P i → Q i) (ha : code.allAtoms P) : code.allAtoms Q := by
  induction code <;> simp_all [MachineCode.allAtoms]

lemma MachineEval.pointer_frame {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {code : MachineCode} {st out : MachineState} {u : ℕ} (e : MachineEval m g ω code st u out)
    (r : ℕ) (hr : r ∉ code.pointerTargets) : out.scalar.core.ptrs r=st.scalar.core.ptrs r := by
  apply e.frame (fun z => z.scalar.core.ptrs r) (by intros; rfl) (by intro; rfl)
  have ha := code.allAtoms_pointerTargets r hr
  exact code.allAtoms_mono _ _ (fun i hi z => atomState_pointer_frame m g ω i z r hi) ha

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ScalarQueries

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pointerAdd_atomState (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r a b : ℕ) (hh : st.scalar.halted=false) :
    atomState m g ω (.scalar (.pointerAdd r a b)) st=
      pcSet (payUnit (pointerWrite st r (st.scalar.core.ptrs a+st.scalar.core.ptrs b))) 1 := by
  simp [atomState,machineStep,pcSet,payUnit,pointerWrite,hh,LocalPush.step,scalarProgram]

lemma pointerAdd_eval (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r a b : ℕ) (hh : st.scalar.halted=false) :
    MachineEval m g ω (.atom (.scalar (.pointerAdd r a b))) st 1
      (payUnit (pointerWrite st r (st.scalar.core.ptrs a+st.scalar.core.ptrs b))) := by
  have h := MachineEval.atom (.scalar (.pointerAdd r a b)) st
    (by rw [pointerAdd_atomState m g ω st r a b hh]; rfl)
  simpa only [pointerAdd_atomState m g ω st r a b hh,pcSet_set,pcSet_payUnit_zero] using h

lemma pointerReal_atomState (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r a : ℕ) (hh : st.scalar.halted=false) :
    atomState m g ω (.scalar (.pointerReal r a)) st=
      pcSet (payUnit (realWrite st r (st.scalar.core.ptrs a : ℝ))) 1 := by
  simp [atomState,machineStep,pcSet,payUnit,realWrite,hh,LocalPush.step,scalarProgram]

lemma pointerReal_eval (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r a : ℕ) (hh : st.scalar.halted=false) :
    MachineEval m g ω (.atom (.scalar (.pointerReal r a))) st 1
      (payUnit (realWrite st r (st.scalar.core.ptrs a : ℝ))) := by
  have h := MachineEval.atom (.scalar (.pointerReal r a)) st
    (by rw [pointerReal_atomState m g ω st r a hh]; rfl)
  simpa only [pointerReal_atomState m g ω st r a hh,pcSet_set,pcSet_payUnit_zero] using h

lemma load_atomState (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r a : ℕ) (hh : st.scalar.halted=false) :
    atomState m g ω (.scalar (.core (.load r a))) st=
      pcSet (payUnit (realWrite st r (st.scalar.core.mem (st.scalar.core.ptrs a)))) 1 := by
  simp [atomState,machineStep,pcSet,payUnit,realWrite,hh,LocalPush.step,scalarProgram,
    LocalPush.coreProgram,SmaleNinth.RAMStep]

lemma load_eval (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r a : ℕ) (hh : st.scalar.halted=false) :
    MachineEval m g ω (.atom (.scalar (.core (.load r a)))) st 1
      (payUnit (realWrite st r (st.scalar.core.mem (st.scalar.core.ptrs a)))) := by
  have h := MachineEval.atom (.scalar (.core (.load r a))) st
    (by rw [load_atomState m g ω st r a hh]; rfl)
  simpa only [load_atomState m g ω st r a hh,pcSet_set,pcSet_payUnit_zero] using h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MemoryCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def integerWrite (st : MachineState) (a x : ℤ) : MachineState :=
  {st with scalar := {st.scalar with integerMemory := Function.update st.scalar.integerMemory a x}}

def memoryWrite (st : MachineState) (a : ℤ) (x : ℝ) : MachineState :=
  {st with scalar := {st.scalar with core := {st.scalar.core with mem := Function.update st.scalar.core.mem a x}}}

lemma integerLoad_atomState (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r a : ℕ) (hh : st.scalar.halted=false) :
    atomState m g ω (.scalar (.integerLoad r a)) st=pcSet
      (payUnit (pointerWrite st r (st.scalar.integerMemory (st.scalar.core.ptrs a)))) 1 := by
  simp [atomState,machineStep,pcSet,payUnit,pointerWrite,hh,LocalPush.step,scalarProgram]

lemma integerLoad_eval (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r a : ℕ) (hh : st.scalar.halted=false) :
    MachineEval m g ω (.atom (.scalar (.integerLoad r a))) st 1
      (payUnit (pointerWrite st r (st.scalar.integerMemory (st.scalar.core.ptrs a)))) := by
  have h := MachineEval.atom (.scalar (.integerLoad r a)) st
    (by rw [integerLoad_atomState m g ω st r a hh]; rfl)
  simpa only [integerLoad_atomState m g ω st r a hh,pcSet_set,pcSet_payUnit_zero] using h

lemma integerStore_atomState (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (a r : ℕ) (hh : st.scalar.halted=false) :
    atomState m g ω (.scalar (.integerStore a r)) st=pcSet
      (payUnit (integerWrite st (st.scalar.core.ptrs a) (st.scalar.core.ptrs r))) 1 := by
  simp [atomState,machineStep,pcSet,payUnit,integerWrite,hh,LocalPush.step,scalarProgram]

lemma integerStore_eval (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (a r : ℕ) (hh : st.scalar.halted=false) :
    MachineEval m g ω (.atom (.scalar (.integerStore a r))) st 1
      (payUnit (integerWrite st (st.scalar.core.ptrs a) (st.scalar.core.ptrs r))) := by
  have h := MachineEval.atom (.scalar (.integerStore a r)) st
    (by rw [integerStore_atomState m g ω st a r hh]; rfl)
  simpa only [integerStore_atomState m g ω st a r hh,pcSet_set,pcSet_payUnit_zero] using h

lemma store_atomState (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (a r : ℕ) (hh : st.scalar.halted=false) :
    atomState m g ω (.scalar (.core (.store a r))) st=pcSet
      (payUnit (memoryWrite st (st.scalar.core.ptrs a) (st.scalar.core.regs r))) 1 := by
  simp [atomState,machineStep,pcSet,payUnit,memoryWrite,hh,LocalPush.step,scalarProgram,
    LocalPush.coreProgram,SmaleNinth.RAMStep]

lemma store_eval (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (a r : ℕ) (hh : st.scalar.halted=false) :
    MachineEval m g ω (.atom (.scalar (.core (.store a r)))) st 1
      (payUnit (memoryWrite st (st.scalar.core.ptrs a) (st.scalar.core.regs r))) := by
  have h := MachineEval.atom (.scalar (.core (.store a r))) st
    (by rw [store_atomState m g ω st a r hh]; rfl)
  simpa only [store_atomState m g ω st a r hh,pcSet_set,pcSet_payUnit_zero] using h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PointerRoutine

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def PointerOp.destination : PointerOp → ℕ
  | .set r _ | .copy r _ | .inc r | .add r _ _ | .load r _ => r


def PointerOp.result (I : ℤ → ℤ) (P : ℕ → ℤ) : PointerOp → ℤ
  | .set _ z => z
  | .copy _ s => P s
  | .inc r => P r+1
  | .add _ s t => P s+P t
  | .load _ s => I (P s)

def PointerOp.update (op : PointerOp) (I : ℤ → ℤ) (P : ℕ → ℤ) : ℕ → ℤ :=
  Function.update P op.destination (op.result I P)

lemma PointerOp.execute (op : PointerOp) (m : SolveModel) {n : ℕ} (g : InputGraph n)
    (ω : ℕ → Bool) (st : MachineState) (hh : st.scalar.halted=false) :
    MachineEval m g ω (.atom op.instruction) st 1
      (payUnit (pointerWrite st op.destination (op.result st.scalar.integerMemory st.scalar.core.ptrs))) := by
  cases op with
  | set r z => exact pset_eval m g ω st r z hh
  | copy r s => exact pcopy_eval m g ω st r s hh
  | inc r => exact pinc_eval m g ω st r hh
  | add r s t => exact pointerAdd_eval m g ω st r s t hh
  | load r s => exact integerLoad_eval m g ω st r s hh

def PointerRoutine.run (I : ℤ → ℤ) : PointerRoutine → (ℕ → ℤ) → ℕ × (ℕ → ℤ)
  | .skip,P => (0,P)
  | .atom op,P => (1,op.update I P)
  | .seq a b,P => let u := a.run I P; let v := b.run I u.2; (u.1+v.1,v.2)
  | .branch r s a b,P => if P r ≤ P s then let u := a.run I P; (1+u.1,u.2)
      else let u := b.run I P; (1+u.1+1,u.2)

lemma PointerRoutine.execute (routine : PointerRoutine) (m : SolveModel) {n : ℕ} (g : InputGraph n)
    (ω : ℕ → Bool) (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω routine.code st (routine.run st.scalar.integerMemory st.scalar.core.ptrs).1 out ∧
      out.scalar.core.ptrs=(routine.run st.scalar.integerMemory st.scalar.core.ptrs).2 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+(routine.run st.scalar.integerMemory st.scalar.core.ptrs).1 ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  induction routine generalizing st with
  | skip => exact ⟨st,MachineEval.skip st,rfl,rfl,rfl,by simp [run],rfl,hh⟩
  | atom op =>
    refine ⟨_,op.execute m g ω st hh,rfl,rfl,rfl,?_,rfl,?_⟩
    · simp [run,payUnit,pcSet,pointerWrite]
    · exact hh
  | seq a b ha hb =>
    obtain ⟨mid,ea,hp,hi,hr,hw,ho,hhm⟩ := ha st hh
    obtain ⟨out,eb,hp',hi',hr',hw',ho',hho⟩ := hb mid hhm
    simp only [hi,hp] at eb hp' hw'
    refine ⟨out,MachineEval.seq ea eb,hp',hi'.trans hi,hr'.trans hr,?_,ho'.trans ho,hho⟩
    simp only [run,Nat.cast_add]
    rw [hw',hw]
    exact add_assoc _ _ _
  | branch r s a b ha hb =>
    have hhp : (payUnit st).scalar.halted=false := hh
    by_cases h : st.scalar.core.ptrs r ≤ st.scalar.core.ptrs s
    · obtain ⟨out,ea,hp,hi,hr,hw,ho,hho⟩ := ha (payUnit st) hhp
      refine ⟨out,?_,?_,hi,hr,?_,ho,hho⟩
      · simpa only [code,run,if_pos h,payUnit,pcSet] using MachineEval.pointerLe (r:=r) (s:=s) (b:=b.code) hh h ea
      · simpa only [run,if_pos h,payUnit,pcSet] using hp
      · simp only [run,if_pos h,Nat.cast_add,Nat.cast_one]
        rw [hw,payUnit_work]
        ac_rfl
    · obtain ⟨mid,eb,hp,hi,hr,hw,ho,hho⟩ := hb (payUnit st) hhp
      refine ⟨payUnit mid,?_,?_,hi,hr,?_,ho,hho⟩
      · simpa only [code,run,if_neg h,payUnit,pcSet] using MachineEval.pointerGt (r:=r) (s:=s) (a:=a.code) hh h eb
      · simpa only [run,if_neg h,payUnit,pcSet] using hp
      · simp only [run,if_neg h,Nat.cast_add,Nat.cast_one]
        rw [payUnit_work,hw,payUnit_work]
        ac_rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section


lemma ForestRep.frame {I J : ℤ → ℤ} {p : ℤ} {t : HeapNode ℕ} {F : Finset ℤ}
    (h : ForestRep I p t F) (he : ∀ a ∈ F, J a=I a) : ForestRep J p t F := by
  induction h with
  | nil => exact ForestRep.nil
  | node p a cp sp c s C S hp hk hc hs rc rs hdC hdS hdCS ic is =>
    apply ForestRep.node p a cp sp c s C S hp
    · rw [he p (by simp [nodeCells]),hk]
    · rw [he (p+1) (by simp [nodeCells]),hc]
    · rw [he (p+2) (by simp [nodeCells]),hs]
    · exact ic (fun a ha => he a (by simp [ha]))
    · exact is (fun a ha => he a (by simp [ha]))
    · exact hdC
    · exact hdS
    · exact hdCS

lemma ForestRep.positive_cells {I : ℤ → ℤ} {p : ℤ} {t : HeapNode ℕ} {F : Finset ℤ}
    (h : ForestRep I p t F) : ∀ a ∈ F, 2 ≤ a := by
  induction h with
  | nil => simp
  | node p a cp sp c s C S hp hk hc hs rc rs hdC hdS hdCS ic is =>
    intro z hz
    simp only [Finset.mem_union] at hz
    rcases hz with (hz|hz)|hz
    · simp only [nodeCells,Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl|rfl <;> omega
    · exact ic z hz
    · exact is z hz

lemma ForestRep.nil_iff {I : ℤ → ℤ} {p : ℤ} {F : Finset ℤ}
    (h : ForestRep I p .nil F) : p=0 ∧ F=∅ := by cases h; exact ⟨rfl,rfl⟩

lemma ForestRep.root_cells {I : ℤ → ℤ} {p : ℤ} {a : ℕ} {c s : HeapNode ℕ} {F : Finset ℤ}
    (h : ForestRep I p (.node a c s) F) : nodeCells p ⊆ F := by
  cases h
  intro z hz
  simp [hz]

lemma ForestRep.frame_write_outside {I : ℤ → ℤ} {p a v : ℤ} {t : HeapNode ℕ} {F : Finset ℤ}
    (h : ForestRep I p t F) (ha : a ∉ F) : ForestRep (Function.update I a v) p t F := by
  apply h.frame
  intro z hz
  exact Function.update_of_ne (by intro he; subst z; exact ha hz) _ _

lemma nodeCells_card (p : ℤ) : (nodeCells p).card=3 := by
  simp [nodeCells]

lemma ForestRep.card {I : ℤ → ℤ} {p : ℤ} {t : HeapNode ℕ} {F : Finset ℤ}
    (h : ForestRep I p t F) : F.card=3*t.realSize := by
  induction h with
  | nil => simp
  | node p a cp sp c s C S hp hk hc hs rc rs hdC hdS hdCS ic is =>
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdS,hdCS⟩),
      Finset.card_union_of_disjoint hdC,nodeCells_card,ic,is]
    simp only [HeapNode.realSize]
    omega

lemma ForestRep.root_view {I : ℤ → ℤ} {p : ℤ} {a : ℕ} {c : HeapNode ℕ} {F : Finset ℤ}
    (h : ForestRep I p (.node a c .nil) F) :
    ∃ cp C, 2 ≤ p ∧ I p=(a : ℤ) ∧ I (p+1)=cp ∧ I (p+2)=0 ∧
      ForestRep I cp c C ∧ Disjoint (nodeCells p) C ∧ F=nodeCells p ∪ C := by
  cases h with
  | node p a cp sp c s C S hp hk hc hs rc rs hdC hdS hdCS =>
    obtain ⟨rfl,rfl⟩ := rs.nil_iff
    exact ⟨cp,C,hp,hk,hc,hs,rc,hdC,by simp⟩

lemma nodeCells_mem_iff (p a : ℤ) : a ∈ nodeCells p ↔ p ≤ a ∧ a ≤ p+2 := by
  simp only [nodeCells,Finset.mem_insert,Finset.mem_singleton]
  omega

lemma disjoint_cells_ne {F G : Finset ℤ} {p q x y : ℤ}
    (hd : Disjoint F G) (hp : nodeCells p ⊆ F) (hq : nodeCells q ⊆ G)
    (hx : p ≤ x ∧ x ≤ p+2) (hy : q ≤ y ∧ y ≤ q+2) : x ≠ y := by
  intro he
  subst y
  exact Finset.disjoint_left.mp hd (hp ((nodeCells_mem_iff p x).mpr hx)) (hq ((nodeCells_mem_iff q x).mpr hy))

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapLinkCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def linkMemory (I : ℤ → ℤ) (winner loser : ℤ) : ℤ → ℤ :=
  Function.update (Function.update I (loser+2) (I (winner+1))) (winner+1) loser

lemma heapLinkCode_wellFormed : heapLinkCode.wellFormed := by
  simp [heapLinkCode,sequenceCode,coreCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 800000 in
lemma heap_link_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω heapLinkCode st 8 out ∧
      out.scalar.integerMemory=linkMemory st.scalar.integerMemory (st.scalar.core.ptrs 5) (st.scalar.core.ptrs 6) ∧
      out.scalar.core.ptrs 5=st.scalar.core.ptrs 5 ∧ out.scalar.core.ptrs 6=st.scalar.core.ptrs 6 ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+8 ∧ out.output=st.output := by
  let W := st.scalar.core.ptrs 5
  let L := st.scalar.core.ptrs 6
  let I := st.scalar.integerMemory
  let A := payUnit (pointerWrite st 7 W)
  let B := payUnit (pointerWrite A 7 (W+1))
  let C := payUnit (pointerWrite B 8 (I (W+1)))
  let D := payUnit (pointerWrite C 9 L)
  let E := payUnit (pointerWrite D 9 (L+1))
  let F := payUnit (pointerWrite E 9 (L+2))
  let G := payUnit (integerWrite F (L+2) (I (W+1)))
  let out := payUnit (integerWrite G (W+1) L)
  have ah : A.scalar.halted=false := by simp [A,payUnit,pcSet,pointerWrite,hh]
  have bh : B.scalar.halted=false := by simp [B,payUnit,pcSet,pointerWrite,ah]
  have ch : C.scalar.halted=false := by simp [C,payUnit,pcSet,pointerWrite,bh]
  have dh : D.scalar.halted=false := by simp [D,payUnit,pcSet,pointerWrite,ch]
  have eh : E.scalar.halted=false := by simp [E,payUnit,pcSet,pointerWrite,dh]
  have fh : F.scalar.halted=false := by simp [F,payUnit,pcSet,pointerWrite,eh]
  have gh : G.scalar.halted=false := by simp [G,payUnit,pcSet,integerWrite,fh]
  have ea := pcopy_eval m g ω st 7 5 hh
  have eb : MachineEval m g ω (coreCode (.pinc 7)) A 1 B := by
    have hp : A.scalar.core.ptrs 7=W := by simp [A,payUnit,pcSet,pointerWrite]
    simpa only [coreCode,B,hp] using pinc_eval m g ω A 7 ah
  have ec : MachineEval m g ω (.atom (.scalar (.integerLoad 8 7))) B 1 C := by
    have hv : B.scalar.integerMemory (B.scalar.core.ptrs 7)=I (W+1) := by simp [B,A,payUnit,pcSet,pointerWrite,I]
    simpa only [hv] using integerLoad_eval m g ω B 8 7 bh
  have ed : MachineEval m g ω (coreCode (.pcopy 9 6)) C 1 D := by
    have hp : C.scalar.core.ptrs 6=L := by simp [C,B,A,payUnit,pcSet,pointerWrite,L]
    simpa only [coreCode,D,hp] using pcopy_eval m g ω C 9 6 ch
  have ee : MachineEval m g ω (coreCode (.pinc 9)) D 1 E := by
    have hp : D.scalar.core.ptrs 9=L := by simp [D,payUnit,pcSet,pointerWrite]
    simpa only [coreCode,E,hp] using pinc_eval m g ω D 9 dh
  have ef : MachineEval m g ω (coreCode (.pinc 9)) E 1 F := by
    have hp : E.scalar.core.ptrs 9=L+1 := by simp [E,payUnit,pcSet,pointerWrite]
    simpa [coreCode,F,hp,Int.add_assoc] using pinc_eval m g ω E 9 eh
  have eg : MachineEval m g ω (.atom (.scalar (.integerStore 9 8))) F 1 G := by
    have hp : F.scalar.core.ptrs 9=L+2 := by simp [F,payUnit,pcSet,pointerWrite]
    have hv : F.scalar.core.ptrs 8=I (W+1) := by simp [F,E,D,C,payUnit,pcSet,pointerWrite]
    simpa only [hp,hv] using integerStore_eval m g ω F 9 8 fh
  have eo : MachineEval m g ω (.atom (.scalar (.integerStore 7 6))) G 1 out := by
    have hp : G.scalar.core.ptrs 7=W+1 := by simp [G,F,E,D,C,B,payUnit,pcSet,pointerWrite,integerWrite]
    have hv : G.scalar.core.ptrs 6=L := by simp [G,F,E,D,C,B,A,payUnit,pcSet,pointerWrite,integerWrite,L]
    simpa only [hp,hv] using integerStore_eval m g ω G 7 6 gh
  refine ⟨out,?_,?_,?_,?_,?_,?_,?_⟩
  · unfold heapLinkCode sequenceCode
    exact MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed
      (MachineEval.seq ee (MachineEval.seq ef (MachineEval.seq eg (MachineEval.seq eo (MachineEval.skip out))))))))
  all_goals simp [out,G,F,E,D,C,B,A,payUnit,pcSet,pointerWrite,integerWrite,linkMemory,W,L,I] <;> ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapLinkRepresentation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section

set_option maxHeartbeats 800000 in
lemma ForestRep.link {I : ℤ → ℤ} {p q : ℤ} {a b : ℕ} {c d : HeapNode ℕ} {F G : Finset ℤ}
    (hp : ForestRep I p (.node a c .nil) F) (hq : ForestRep I q (.node b d .nil) G)
    (hd : Disjoint F G) :
    ForestRep (linkMemory I p q) p (.node a (.node b d c) .nil) (F ∪ G) := by
  obtain ⟨cp,C,hp0,hpk,hpc,hps,rc,hpC,rfl⟩ := hp.root_view
  obtain ⟨cq,D,hq0,hqk,hqc,hqs,rd,hqD,rfl⟩ := hq.root_view
  have sep (x : ℤ) (hx : x ∈ nodeCells p ∪ C) (hy : x ∈ nodeCells q ∪ D) : False :=
    Finset.disjoint_left.mp hd hx hy
  have cross (i j : ℤ) (hi : 0 ≤ i ∧ i ≤ 2) (hj : 0 ≤ j ∧ j ≤ 2) : p+i ≠ q+j :=
    disjoint_cells_ne hd Finset.subset_union_left Finset.subset_union_left (by omega) (by omega)
  have hpC1 : p+1 ∉ C := by
    intro h
    exact Finset.disjoint_left.mp hpC (by simp [nodeCells]) h
  have hqC2 : q+2 ∉ C := by
    intro h
    exact sep (q+2) (by simp [h]) (by simp [nodeCells])
  have hpD1 : p+1 ∉ D := by
    intro h
    exact sep (p+1) (by simp [nodeCells]) (by simp [h])
  have hqD2 : q+2 ∉ D := by
    intro h
    exact Finset.disjoint_left.mp hqD (by simp [nodeCells]) h
  have rC : ForestRep (linkMemory I p q) cp c C :=
    (rc.frame_write_outside hqC2).frame_write_outside hpC1
  have rD : ForestRep (linkMemory I p q) cq d D :=
    (rd.frame_write_outside hqD2).frame_write_outside hpD1
  have hqC : Disjoint (nodeCells q) C := by
    apply Finset.disjoint_left.mpr
    intro x hx hc
    exact sep x (by simp [hc]) (by simp [hx])
  have hDC : Disjoint D C := by
    apply Finset.disjoint_left.mpr
    intro x hd' hc
    exact sep x (by simp [hc]) (by simp [hd'])
  have hnew : Disjoint (nodeCells p) (nodeCells q ∪ D ∪ C) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_union] at hy
    rcases hy with (hy|hy)|hy
    · exact sep x (by simp [hx]) (by simp [hy])
    · exact sep x (by simp [hx]) (by simp [hy])
    · exact Finset.disjoint_left.mp hpC hx hy
  have jk : linkMemory I p q p=(a : ℤ) := by
    simp [linkMemory,Function.update_of_ne (by omega : p ≠ p+1),
      show p ≠ q+2 from by simpa using cross 0 2 (by omega) (by omega),hpk]
  have qk : linkMemory I p q q=(b : ℤ) := by
    simp [linkMemory,show q ≠ p+1 from by have h := cross 1 0 (by omega) (by omega); simpa using h.symm,
      Function.update_of_ne (by omega : q ≠ q+2),hqk]
  have qc : linkMemory I p q (q+1)=cq := by
    simp [linkMemory,show q+1 ≠ p+1 from (cross 1 1 (by omega) (by omega)).symm,
      Function.update_of_ne (by omega : q+1 ≠ q+2),hqc]
  have qs : linkMemory I p q (q+2)=cp := by
    simp [linkMemory,(cross 1 2 (by omega) (by omega)).symm,hpc]
  have pc : linkMemory I p q (p+1)=q := by simp [linkMemory]
  have ps : linkMemory I p q (p+2)=0 := by
    simp [linkMemory,Function.update_of_ne (by omega : p+2 ≠ p+1),cross 2 2 (by omega) (by omega),hps]
  have rChild : ForestRep (linkMemory I p q) q (.node b d c) (nodeCells q ∪ D ∪ C) :=
    ForestRep.node q b cq cp d c D C hq0 qk qc qs rD rC hqD hqC hDC
  have result := ForestRep.node p a q 0 (.node b d c) .nil (nodeCells q ∪ D ∪ C) ∅ hp0 jk pc ps rChild
    ForestRep.nil hnew (by simp) (by simp)
  convert result using 1 <;> ext x <;> simp [or_assoc,or_left_comm,or_comm]

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RankArrayQueue

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp

def RankedTree.link (a b : RankedTree) : RankedTree :=
  if a.key ≤ b.key then ⟨a.key,.node b.key b.children a.children⟩
  else ⟨b.key,.node a.key a.children b.children⟩

lemma RankedTree.link_valid (a b : RankedTree) (r : ℕ) (ha : a.valid r) (hb : b.valid r) :
    (a.link b).valid (r+1) := by
  unfold link
  split_ifs with hab
  · exact ⟨r,rfl,by simpa only [keyLE,decide_eq_true_eq] using hab,hb,ha⟩
  · exact ⟨r,rfl,by simpa only [keyLE,decide_eq_true_eq] using (Nat.le_of_not_ge hab),ha,hb⟩

lemma RankedTree.link_support (a b : RankedTree) : (a.link b).support=a.support ∪ b.support := by
  unfold link
  split <;> ext v <;> simp [support,nodeSupport,or_assoc,or_comm,or_left_comm]

lemma RankedTree.size_eq_pow (r : ℕ) (t : RankedTree) (h : t.valid r) : t.size=2^r :=
  HeapNode.WF.realSize_eq h

end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RankQueueContents

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue

noncomputable section

def slotsSupport (slots : RankSlots) : Set ℕ := {x | ∃ r t, slots r=some t ∧ x ∈ t.support}
def awaySupport (slots : RankSlots) (r : ℕ) : Set ℕ := {x | ∃ i t, i ≠ r ∧ slots i=some t ∧ x ∈ t.support}
def optionSupport : Option RankedTree → Set ℕ
  | none => ∅
  | some t => ↑t.support

lemma slotsSupport_split (slots : RankSlots) (r : ℕ) :
    slotsSupport slots=awaySupport slots r ∪ optionSupport (slots r) := by
  ext x
  constructor
  · rintro ⟨i,t,hi,hx⟩
    by_cases he : i=r
    · subst i
      right
      simp [optionSupport,hi,hx]
    · exact Or.inl ⟨i,t,he,hi,hx⟩
  · intro h
    rcases h with ⟨i,t,he,hi,hx⟩|h
    · exact ⟨i,t,hi,hx⟩
    · cases hr : slots r with
      | none => simp [optionSupport,hr] at h
      | some t => exact ⟨r,t,hr,by simpa [optionSupport,hr] using h⟩

lemma slotsSupport_update (slots : RankSlots) (r : ℕ) (v : Option RankedTree) :
    slotsSupport (Function.update slots r v)=awaySupport slots r ∪ optionSupport v := by
  ext x
  constructor
  · rintro ⟨i,t,hi,hx⟩
    by_cases he : i=r
    · subst i
      rw [Function.update_self] at hi
      exact Or.inr (by simp [hi,optionSupport,hx])
    · rw [Function.update_of_ne he] at hi
      exact Or.inl ⟨i,t,he,hi,hx⟩
  · intro h
    rcases h with ⟨i,t,he,hi,hx⟩|h
    · exact ⟨i,t,by simpa [Function.update_of_ne he] using hi,hx⟩
    · cases v with
      | none => simp [optionSupport] at h
      | some t => exact ⟨r,t,by simp,by simpa [optionSupport] using h⟩

lemma clear_link_support (slots : RankSlots) (r : ℕ) (t u : RankedTree) (hr : slots r=some u) :
    slotsSupport (Function.update slots r none) ∪ ↑(t.link u).support=slotsSupport slots ∪ ↑t.support := by
  rw [slotsSupport_update,slotsSupport_split slots r,hr,RankedTree.link_support]
  ext x
  simp [optionSupport,or_assoc,or_left_comm,or_comm]

lemma slotsSupport_store_none (slots : RankSlots) (r : ℕ) (t : RankedTree) (hr : slots r=none) :
    slotsSupport (Function.update slots r (some t))=slotsSupport slots ∪ ↑t.support := by
  rw [slotsSupport_update,slotsSupport_split slots r,hr]
  simp [optionSupport]

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RankArrayMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma mem_arrayCells (base z : ℤ) (length : ℕ) :
    z ∈ arrayCells base length ↔ ∃ i : ℕ, i < length ∧ z=base+(i : ℤ) := by
  simp [arrayCells,Finset.mem_image,eq_comm]

lemma SlotRep.frame {I J : ℤ → ℤ} {p : ℤ} {v : Option RankedTree} {F : Finset ℤ}
    (h : SlotRep I p v F) (he : ∀ a ∈ F, J a=I a) : SlotRep J p v F := by
  cases v with
  | none => exact h
  | some t => exact ForestRep.frame h he

lemma RankArrayRep.frame {I J : ℤ → ℤ} {base : ℤ} {length : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} (h : RankArrayRep I base length slots roots feet)
    (he : ∀ a ∈ queueCells base length feet, J a=I a) : RankArrayRep J base length slots roots feet := by
  refine ⟨h.positive,?_,?_,h.separate,h.pairwise,h.bounded,h.valid⟩
  · intro i hi
    rw [he _ (Finset.mem_union_left _ ((mem_arrayCells _ _ _).mpr ⟨i,hi,rfl⟩)),h.array i hi]
  · intro i hi
    apply (h.node i hi).frame
    intro a ha
    apply he
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_range.mpr hi,ha⟩)

lemma RankArrayRep.empty (I : ℤ → ℤ) (base : ℤ) (length : ℕ) (hb : 2 ≤ base)
    (hz : ∀ i < length, I (base+(i : ℤ))=0) :
    RankArrayRep I base length (fun _ => none) (fun _ => 0) (fun _ => ∅) := by
  refine ⟨hb,hz,?_,?_,?_,by simp,?_⟩
  · intro i hi; exact ⟨rfl,rfl⟩
  · simp
  · simp
  · intro i t ht; simp at ht

set_option maxHeartbeats 700000 in
lemma RankArrayRep.clear {I : ℤ → ℤ} {base : ℤ} {length : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} (h : RankArrayRep I base length slots roots feet)
    (r : ℕ) (hr : r < length) :
    RankArrayRep (Function.update I (base+(r : ℤ)) 0) base length
      (Function.update slots r none) (Function.update roots r 0) (Function.update feet r ∅) := by
  have hcell : base+(r : ℤ) ∈ arrayCells base length := (mem_arrayCells _ _ _).mpr ⟨r,hr,rfl⟩
  refine ⟨h.positive,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    by_cases he : i=r
    · subst i
      simp
    · have haddr : base+(i : ℤ) ≠ base+(r : ℤ) := by omega
      simp [Function.update_of_ne he,Function.update_of_ne haddr,h.array i hi]
  · intro i hi
    by_cases he : i=r
    · subst i
      simp [SlotRep]
    · simp only [Function.update_of_ne he]
      apply (h.node i hi).frame
      intro a ha
      apply Function.update_of_ne
      intro heq
      subst a
      exact Finset.disjoint_left.mp (h.separate i hi) hcell ha
  · intro i hi
    by_cases he : i=r
    · simp [he]
    · simpa [Function.update_of_ne he] using h.separate i hi
  · intro i hi j hj hij
    by_cases he : i=r
    · simp [he]
    · by_cases he' : j=r
      · simp [he']
      · simpa [Function.update_of_ne he,Function.update_of_ne he'] using h.pairwise i hi j hj hij
  · intro i hi
    have he : i ≠ r := by omega
    simpa [Function.update_of_ne he] using h.bounded i hi
  · intro i t ht
    by_cases he : i=r
    · subst i
      simp at ht
    · exact h.valid i t (by simpa [Function.update_of_ne he] using ht)

set_option maxHeartbeats 800000 in
lemma RankArrayRep.store {I : ℤ → ℤ} {base p : ℤ} {length : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} (h : RankArrayRep I base length slots roots feet)
    (r : ℕ) (hr : r < length) (t : RankedTree) (ht : t.valid r) (F : Finset ℤ)
    (hrep : ForestRep I p (.node t.key t.children .nil) F)
    (hd : Disjoint F (queueCells base length feet)) :
    RankArrayRep (Function.update I (base+(r : ℤ)) p) base length
      (Function.update slots r (some t)) (Function.update roots r p) (Function.update feet r F) := by
  have hcell : base+(r : ℤ) ∈ arrayCells base length := (mem_arrayCells _ _ _).mpr ⟨r,hr,rfl⟩
  have houtside : base+(r : ℤ) ∉ F := by
    intro hf
    exact Finset.disjoint_left.mp hd hf (Finset.mem_union_left _ hcell)
  have hFi (i : ℕ) (hi : i < length) : Disjoint F (feet i) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact Finset.disjoint_left.mp hd ha (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i,Finset.mem_range.mpr hi,hb⟩))
  have hFA : Disjoint (arrayCells base length) F := by
    apply Finset.disjoint_left.mpr
    intro a ha hf
    exact Finset.disjoint_left.mp hd hf (Finset.mem_union_left _ ha)
  refine ⟨h.positive,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    by_cases he : i=r
    · subst i; simp
    · have haddr : base+(i : ℤ) ≠ base+(r : ℤ) := by omega
      simp [Function.update_of_ne he,Function.update_of_ne haddr,h.array i hi]
  · intro i hi
    by_cases he : i=r
    · subst i
      simp only [Function.update_self,SlotRep]
      exact hrep.frame_write_outside houtside
    · simp only [Function.update_of_ne he]
      apply (h.node i hi).frame
      intro a ha
      apply Function.update_of_ne
      intro heq
      subst a
      exact Finset.disjoint_left.mp (h.separate i hi) hcell ha
  · intro i hi
    by_cases he : i=r
    · simpa [he] using hFA
    · simpa [Function.update_of_ne he] using h.separate i hi
  · intro i hi j hj hij
    by_cases he : i=r
    · subst i
      have hjr : j ≠ r := Ne.symm hij
      simpa [Function.update_of_ne hjr] using hFi j hj
    · by_cases he' : j=r
      · subst j
        simpa [Function.update_of_ne he] using (hFi i hi).symm
      · simpa [Function.update_of_ne he,Function.update_of_ne he'] using h.pairwise i hi j hj hij
  · intro i hi
    have he : i ≠ r := by omega
    simpa [Function.update_of_ne he] using h.bounded i hi
  · intro i u hu
    by_cases he : i=r
    · subst i
      simp only [Function.update_self,Option.some.injEq] at hu
      subst u
      exact ht
    · exact h.valid i u (by simpa [Function.update_of_ne he] using hu)

lemma queueCells_clear_subset (base : ℤ) (length r : ℕ) (feet : ℕ → Finset ℤ) :
    queueCells base length (Function.update feet r ∅) ⊆ queueCells base length feet := by
  intro a ha
  simp only [queueCells,Finset.mem_union,Finset.mem_biUnion,Finset.mem_range] at ha ⊢
  rcases ha with ha|⟨i,hi,ha⟩
  · exact Or.inl ha
  · right
    by_cases he : i=r
    · subst i; simp at ha
    · exact ⟨i,hi,by simpa [Function.update_of_ne he] using ha⟩

lemma RankArrayRep.removed_disjoint {I : ℤ → ℤ} {base : ℤ} {length : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} (h : RankArrayRep I base length slots roots feet)
    (r : ℕ) (hr : r < length) :
    Disjoint (feet r) (queueCells base length (Function.update feet r ∅)) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  simp only [queueCells,Finset.mem_union,Finset.mem_biUnion,Finset.mem_range] at hb
  rcases hb with hb|⟨i,hi,hbi⟩
  · exact Finset.disjoint_left.mp (h.separate r hr) hb ha
  · by_cases he : i=r
    · subst i; simp at hbi
    · exact Finset.disjoint_left.mp (h.pairwise r hr i hi (Ne.symm he)) ha
        (by simpa [Function.update_of_ne he] using hbi)

lemma RankArrayRep.node_survives_array_write {I : ℤ → ℤ} {base : ℤ} {length : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} (h : RankArrayRep I base length slots roots feet)
    (r i : ℕ) (hr : r < length) (hi : i < length) (value : ℤ) :
    SlotRep (Function.update I (base+(r : ℤ)) value) (roots i) (slots i) (feet i) := by
  apply (h.node i hi).frame
  intro a ha
  apply Function.update_of_ne
  intro heq
  subst a
  exact Finset.disjoint_left.mp (h.separate i hi) ((mem_arrayCells _ _ _).mpr ⟨r,hr,rfl⟩) ha

lemma queueCells_clear_union (base : ℤ) (length r : ℕ) (feet : ℕ → Finset ℤ) (hr : r < length) :
    queueCells base length (Function.update feet r ∅) ∪ feet r=queueCells base length feet := by
  apply Finset.Subset.antisymm
  · exact Finset.union_subset (queueCells_clear_subset _ _ _ _) (fun a ha => Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,Finset.mem_range.mpr hr,ha⟩))
  · intro a ha
    simp only [queueCells,Finset.mem_union,Finset.mem_biUnion,Finset.mem_range] at ha
    rcases ha with ha|⟨i,hi,ha⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ha)
    · by_cases he : i=r
      · subst i; exact Finset.mem_union_right _ ha
      · apply Finset.mem_union_left
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_range.mpr hi,by simpa [Function.update_of_ne he] using ha⟩)

lemma queueCells_update (base : ℤ) (length r : ℕ) (feet : ℕ → Finset ℤ) (F : Finset ℤ) (hr : r < length) :
    queueCells base length (Function.update feet r F)=
      queueCells base length (Function.update feet r ∅) ∪ F := by
  ext a
  constructor
  · intro ha
    simp only [queueCells,Finset.mem_union,Finset.mem_biUnion,Finset.mem_range] at ha
    rcases ha with ha|⟨i,hi,ha⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ha)
    · by_cases he : i=r
      · subst i; exact Finset.mem_union_right _ (by simpa using ha)
      · apply Finset.mem_union_left
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_range.mpr hi,
          by simpa [Function.update_of_ne he] using ha⟩)
  · intro ha
    rcases Finset.mem_union.mp ha with ha|ha
    · simp only [queueCells,Finset.mem_union,Finset.mem_biUnion,Finset.mem_range] at ha
      rcases ha with ha|⟨i,hi,ha⟩
      · exact Finset.mem_union_left _ ha
      · by_cases he : i=r
        · subst i; simp at ha
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_range.mpr hi,
            by simpa [Function.update_of_ne he] using ha⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,Finset.mem_range.mpr hr,by simpa using ha⟩)

lemma queueCells_store_none (base : ℤ) (length r : ℕ) (feet : ℕ → Finset ℤ) (F : Finset ℤ)
    (hr : r < length) (he : feet r=∅) :
    queueCells base length (Function.update feet r F)=queueCells base length feet ∪ F := by
  rw [queueCells_update _ _ _ _ _ hr]
  have hh := queueCells_clear_union base length r feet hr
  rw [he,Finset.union_empty] at hh
  rw [hh]

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PointerSwapCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma swapRootsCode_wellFormed : swapRootsCode.wellFormed := by
  simp [swapRootsCode,sequenceCode,coreCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 500000 in
lemma swap_roots_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω swapRootsCode st 3 out ∧
      out.scalar.core.ptrs 5=st.scalar.core.ptrs 6 ∧ out.scalar.core.ptrs 6=st.scalar.core.ptrs 5 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+3 ∧ out.output=st.output := by
  let A := payUnit (pointerWrite st 12 (st.scalar.core.ptrs 5))
  let B := payUnit (pointerWrite A 5 (st.scalar.core.ptrs 6))
  let out := payUnit (pointerWrite B 6 (st.scalar.core.ptrs 5))
  have ea := pcopy_eval m g ω st 12 5 hh
  have ah : A.scalar.halted=false := by simp [A,payUnit,pcSet,pointerWrite,hh]
  have bh : B.scalar.halted=false := by simp [B,payUnit,pcSet,pointerWrite,ah]
  have eb : MachineEval m g ω (coreCode (.pcopy 5 6)) A 1 B := by
    have hv : A.scalar.core.ptrs 6=st.scalar.core.ptrs 6 := by simp [A,payUnit,pcSet,pointerWrite]
    simpa only [coreCode,B,hv] using pcopy_eval m g ω A 5 6 ah
  have ec : MachineEval m g ω (coreCode (.pcopy 6 12)) B 1 out := by
    have hv : B.scalar.core.ptrs 12=st.scalar.core.ptrs 5 := by simp [B,A,payUnit,pcSet,pointerWrite]
    simpa only [coreCode,out,hv] using pcopy_eval m g ω B 6 12 bh
  refine ⟨out,?_,?_,?_,?_,?_,?_,?_⟩
  · unfold swapRootsCode sequenceCode
    exact MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.skip out)))
  all_goals simp [out,B,A,payUnit,pcSet,pointerWrite] <;> ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapCombineCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma heapCombineCode_wellFormed : heapCombineCode.wellFormed := by
  refine ⟨?_,?_,heapLinkCode_wellFormed,swapRootsCode_wellFormed,heapLinkCode_wellFormed⟩ <;>
    simp [MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 1000000 in
lemma heap_combine_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    let W := st.scalar.core.ptrs 5
    let L := st.scalar.core.ptrs 6
    let I := st.scalar.integerMemory
    ∃ steps out, MachineEval m g ω heapCombineCode st steps out ∧ steps ≤ 15 ∧
      out.scalar.core.ptrs 5=(if I W ≤ I L then W else L) ∧
      out.scalar.core.ptrs 6=(if I W ≤ I L then L else W) ∧
      out.scalar.integerMemory=(if I W ≤ I L then linkMemory I W L else linkMemory I L W) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+steps ∧ out.output=st.output := by
  intro W L I
  let A := payUnit (pointerWrite st 10 (I W))
  let B := payUnit (pointerWrite A 11 (I L))
  have ah : A.scalar.halted=false := by simp [A,payUnit,pcSet,pointerWrite,hh]
  have bh : B.scalar.halted=false := by simp [B,payUnit,pcSet,pointerWrite,ah]
  have ea := integerLoad_eval m g ω st 10 5 hh
  have eb : MachineEval m g ω (.atom (.scalar (.integerLoad 11 6))) A 1 B := by
    have hv : A.scalar.integerMemory (A.scalar.core.ptrs 6)=I L := by simp [A,payUnit,pcSet,pointerWrite,I,L]
    simpa only [B,hv] using integerLoad_eval m g ω A 11 6 ah
  have bw : B.scalar.core.ptrs 5=W := by simp [B,A,payUnit,pcSet,pointerWrite,W]
  have bl : B.scalar.core.ptrs 6=L := by simp [B,A,payUnit,pcSet,pointerWrite,L]
  have bm : B.scalar.integerMemory=I := by simp [B,A,payUnit,pcSet,pointerWrite,I]
  have bg : B.scalar.core.ptrs 10=I W ∧ B.scalar.core.ptrs 11=I L := by simp [B,A,payUnit,pcSet,pointerWrite]
  by_cases hc : I W ≤ I L
  · obtain ⟨out,el,hm,hp,hq,hr,hw,ho⟩ := heap_link_exec m g ω (payUnit B) (by simpa using bh)
    have ebranch := MachineEval.pointerLe (r := 10) (s := 11) (b := .seq swapRootsCode heapLinkCode) bh (by simpa only [bg.1,bg.2] using hc) el
    refine ⟨11,out,?_,by omega,?_,?_,?_,?_,?_,?_⟩
    · exact MachineEval.seq ea (MachineEval.seq eb ebranch)
    · simpa [hc,payUnit,pcSet,bw] using hp
    · simpa [hc,payUnit,pcSet,bl] using hq
    · simpa [hc,payUnit,pcSet,bm,bw,bl] using hm
    · simpa [payUnit,pcSet,B,A,pointerWrite] using hr
    · rw [hw]
      simp [B,A,payUnit,pcSet,pointerWrite]
      ring
    · simpa [payUnit,pcSet,B,A,pointerWrite] using ho
  · obtain ⟨mid,es,sp,sq,sm,sr,sw,so⟩ := swap_roots_exec m g ω (payUnit B) (by simpa using bh)
    have sh : mid.scalar.halted=false := (es.halted swapRootsCode_wellFormed).trans (by simpa using bh)
    obtain ⟨out,el,hm,hp,hq,hr,hw,ho⟩ := heap_link_exec m g ω mid sh
    have ebody := MachineEval.seq es el
    have ebranch := MachineEval.pointerGt (r := 10) (s := 11) (a := heapLinkCode) bh (by simpa only [bg.1,bg.2] using hc) ebody
    refine ⟨15,payUnit out,?_,by omega,?_,?_,?_,?_,?_,?_⟩
    · exact MachineEval.seq ea (MachineEval.seq eb ebranch)
    · simp only [hc,ite_false,payUnit_ptrs,hp]
      simpa [payUnit,pcSet,bl] using sp
    · simp only [hc,ite_false,payUnit_ptrs,hq]
      simpa [payUnit,pcSet,bw] using sq
    · simp only [hc,ite_false]
      change out.scalar.integerMemory=linkMemory I L W
      rw [hm,sm,sp,sq]
      simp [payUnit,pcSet,bm,bw,bl]
    · change out.scalar.core.mem=st.scalar.core.mem
      rw [hr,sr]
      simp [payUnit,pcSet,B,A,pointerWrite]
    · rw [payUnit_work,hw,sw]
      simp [B,A,payUnit,pcSet,pointerWrite]
      ring
    · change out.output=st.output
      rw [ho,so]
      simp [payUnit,pcSet,B,A,pointerWrite]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapCarryCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma heapCarryCode_wellFormed : heapCarryCode.wellFormed := by
  simp [heapCarryCode,heapCarryLoopCode,heapCarryBodyCode,sequenceCode,coreCode,
    MachineCode.wellFormed,heapCombineCode_wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

lemma heapCarryBodyCode_wellFormed : heapCarryBodyCode.wellFormed := heapCarryCode_wellFormed.2.2.2.1

lemma heapCombine_preserves_queue_pointers {m : SolveModel} {n : ℕ} {g : InputGraph n}
    {ω : ℕ → Bool} {st out : MachineState} {u : ℕ}
    (e : MachineEval m g ω heapCombineCode st u out) :
    out.scalar.core.ptrs 0=st.scalar.core.ptrs 0 ∧
    out.scalar.core.ptrs 13=st.scalar.core.ptrs 13 ∧
    out.scalar.core.ptrs 14=st.scalar.core.ptrs 14 ∧
    out.scalar.core.ptrs 15=st.scalar.core.ptrs 15 := by
  have hh (r : ℕ) (hr : r=0 ∨ r=13 ∨ r=14 ∨ r=15) :
      out.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    apply e.pointer_frame r
    rcases hr with rfl|rfl|rfl|rfl <;>
      norm_num [MachineCode.pointerTargets,heapCombineCode,heapLinkCode,swapRootsCode,
        sequenceCode,coreCode,pointerTargets]
  exact ⟨hh 0 (by simp),hh 13 (by simp),hh 14 (by simp),hh 15 (by simp)⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapCarryComposition

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1000000 in
lemma heap_carry_body_of_combine (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (u : ℕ) (mid : MachineState)
    (ec : MachineEval m g ω heapCombineCode
      (payUnit (integerWrite st (st.scalar.core.ptrs 15) (st.scalar.core.ptrs 0))) u mid)
    (hreal : mid.scalar.core.mem=st.scalar.core.mem)
    (hwork : mid.work=st.work+1+u) (houtput : mid.output=st.output) :
    ∃ out, MachineEval m g ω heapCarryBodyCode st (u+4) out ∧
      out.scalar.integerMemory=mid.scalar.integerMemory ∧
      out.scalar.core.ptrs 5=mid.scalar.core.ptrs 5 ∧
      out.scalar.core.ptrs 0=st.scalar.core.ptrs 0 ∧
      out.scalar.core.ptrs 13=st.scalar.core.ptrs 13 ∧
      out.scalar.core.ptrs 14=st.scalar.core.ptrs 14+1 ∧
      out.scalar.core.ptrs 15=st.scalar.core.ptrs 13+st.scalar.core.ptrs 14+1 ∧
      out.scalar.core.ptrs 6=out.scalar.integerMemory (out.scalar.core.ptrs 15) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+(u+4 : ℕ) ∧ out.output=st.output := by
  let A := payUnit (integerWrite st (st.scalar.core.ptrs 15) (st.scalar.core.ptrs 0))
  have ea := integerStore_eval m g ω st 15 0 hh
  have ah : A.scalar.halted=false := by simp [A,payUnit,pcSet,integerWrite,hh]
  have frames := heapCombine_preserves_queue_pointers ec
  have mh : mid.scalar.halted=false := (ec.halted heapCombineCode_wellFormed).trans ah
  let B := payUnit (pointerWrite mid 14 (st.scalar.core.ptrs 14+1))
  let C := payUnit (pointerWrite B 15 (st.scalar.core.ptrs 13+st.scalar.core.ptrs 14+1))
  let out := payUnit (pointerWrite C 6 (mid.scalar.integerMemory (st.scalar.core.ptrs 13+st.scalar.core.ptrs 14+1)))
  have eb : MachineEval m g ω (coreCode (.pinc 14)) mid 1 B := by
    have hh14 : mid.scalar.core.ptrs 14=st.scalar.core.ptrs 14 := by simpa [A,payUnit,pcSet,integerWrite] using frames.2.2.1
    simpa only [coreCode,B,hh14] using pinc_eval m g ω mid 14 mh
  have bh : B.scalar.halted=false := by simp [B,payUnit,pcSet,pointerWrite,mh]
  have eC : MachineEval m g ω (.atom (.scalar (.pointerAdd 15 13 14))) B 1 C := by
    have hb13 : B.scalar.core.ptrs 13=st.scalar.core.ptrs 13 := by simpa [B,A,payUnit,pcSet,pointerWrite,integerWrite] using frames.2.1
    have hb14 : B.scalar.core.ptrs 14=st.scalar.core.ptrs 14+1 := by simp [B,payUnit,pcSet,pointerWrite]
    simpa [C,hb13,hb14,Int.add_assoc] using pointerAdd_eval m g ω B 15 13 14 bh
  have ch : C.scalar.halted=false := by simp [C,payUnit,pcSet,pointerWrite,bh]
  have eout : MachineEval m g ω (.atom (.scalar (.integerLoad 6 15))) C 1 out := by
    have hv : C.scalar.integerMemory (C.scalar.core.ptrs 15)=mid.scalar.integerMemory (st.scalar.core.ptrs 13+st.scalar.core.ptrs 14+1) := by
      simp [C,B,payUnit,pcSet,pointerWrite]
    simpa only [out,hv] using integerLoad_eval m g ω C 6 15 ch
  refine ⟨out,?_,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · unfold heapCarryBodyCode sequenceCode
    have e := MachineEval.seq ea (MachineEval.seq ec (MachineEval.seq eb (MachineEval.seq eC (MachineEval.seq eout (MachineEval.skip out)))))
    convert e using 1 <;> (first | rfl | omega)
  · simp [out,C,B,payUnit,pcSet,pointerWrite]
  · simpa [out,C,B,A,payUnit,pcSet,pointerWrite,integerWrite] using frames.1
  · simpa [out,C,B,A,payUnit,pcSet,pointerWrite,integerWrite] using frames.2.1
  · simp [out,C,B,payUnit,pcSet,pointerWrite]
  · simp [out,C,B,payUnit,pcSet,pointerWrite]
  · simp [out,C,B,payUnit,pcSet,pointerWrite]
  · simpa [out,C,B,payUnit,pcSet,pointerWrite] using hreal
  · simp only [out,payUnit_work,C,B,pointerWrite]
    rw [hwork]
    push_cast
    ring
  · simpa [out,C,B,payUnit,pcSet,pointerWrite] using houtput

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapCombineRepresentation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section

set_option maxHeartbeats 700000 in
lemma heap_combine_represented (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (a b : RankedTree) (F G : Finset ℤ)
    (ha : ForestRep st.scalar.integerMemory (st.scalar.core.ptrs 5) (.node a.key a.children .nil) F)
    (hb : ForestRep st.scalar.integerMemory (st.scalar.core.ptrs 6) (.node b.key b.children .nil) G)
    (hd : Disjoint F G) :
    ∃ steps out, MachineEval m g ω heapCombineCode st steps out ∧ steps ≤ 15 ∧
      ForestRep out.scalar.integerMemory (out.scalar.core.ptrs 5)
        (.node (a.link b).key (a.link b).children .nil) (F ∪ G) ∧
      (∀ z, z ∉ F ∪ G → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+steps ∧ out.output=st.output := by
  obtain ⟨u,out,e,hu,hp,hq,hm,hr,hw,ho⟩ := heap_combine_exec m g ω st hh
  have hunchanged : ∀ z, z ∉ F ∪ G → out.scalar.integerMemory z=st.scalar.integerMemory z := by
    intro z hz
    have hzp : z ∉ nodeCells (st.scalar.core.ptrs 5) := by
      intro h
      exact hz (Finset.mem_union_left _ (ha.root_cells h))
    have hzq : z ∉ nodeCells (st.scalar.core.ptrs 6) := by
      intro h
      exact hz (Finset.mem_union_right _ (hb.root_cells h))
    have hp1 : z ≠ st.scalar.core.ptrs 5+1 := by intro he; subst z; exact hzp (by simp [nodeCells])
    have hp2 : z ≠ st.scalar.core.ptrs 5+2 := by intro he; subst z; exact hzp (by simp [nodeCells])
    have hq1 : z ≠ st.scalar.core.ptrs 6+1 := by intro he; subst z; exact hzq (by simp [nodeCells])
    have hq2 : z ≠ st.scalar.core.ptrs 6+2 := by intro he; subst z; exact hzq (by simp [nodeCells])
    rw [hm]
    split <;> simp [linkMemory,Function.update_of_ne hp1,Function.update_of_ne hp2,
      Function.update_of_ne hq1,Function.update_of_ne hq2]
  refine ⟨u,out,e,hu,?_,hunchanged,hr,hw,ho⟩
  have ka : st.scalar.integerMemory (st.scalar.core.ptrs 5)=(a.key : ℤ) := ha.root_view.choose_spec.choose_spec.2.1
  have kb : st.scalar.integerMemory (st.scalar.core.ptrs 6)=(b.key : ℤ) := hb.root_view.choose_spec.choose_spec.2.1
  have hc : (st.scalar.integerMemory (st.scalar.core.ptrs 5) ≤ st.scalar.integerMemory (st.scalar.core.ptrs 6)) ↔ a.key ≤ b.key := by
    rw [ka,kb]
    exact_mod_cast (Iff.rfl : a.key ≤ b.key ↔ a.key ≤ b.key)
  by_cases hab : a.key ≤ b.key
  · have hi := hc.mpr hab
    simp only [hi,ite_true] at hp hm
    rw [hp,hm]
    simpa [RankedTree.link,hab] using ha.link hb hd
  · have hi : ¬st.scalar.integerMemory (st.scalar.core.ptrs 5) ≤ st.scalar.integerMemory (st.scalar.core.ptrs 6) :=
      fun h => hab (hc.mp h)
    simp only [hi,ite_false] at hp hm
    rw [hp,hm]
    simpa [RankedTree.link,hab,Finset.union_comm] using hb.link ha hd.symm

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapCarryInvariant

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section

structure CarryInv (st : MachineState) (base : ℤ) (length rank : ℕ) (slots : RankSlots)
    (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ) (tree : RankedTree) (F : Finset ℤ) : Prop where
  zero : st.scalar.core.ptrs 0=0
  basePointer : st.scalar.core.ptrs 13=base
  rankPointer : st.scalar.core.ptrs 14=(rank : ℤ)
  address : st.scalar.core.ptrs 15=base+(rank : ℤ)
  current : st.scalar.core.ptrs 6=roots rank
  queue : RankArrayRep st.scalar.integerMemory base length slots roots feet
  treeRep : ForestRep st.scalar.integerMemory (st.scalar.core.ptrs 5) (.node tree.key tree.children .nil) F
  separate : Disjoint F (queueCells base length feet)
  valid : tree.valid rank

lemma foot_subset_queueCells (base : ℤ) (length : ℕ) (feet : ℕ → Finset ℤ)
    (r : ℕ) (hr : r < length) : feet r ⊆ queueCells base length feet := by
  intro a ha
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,Finset.mem_range.mpr hr,ha⟩)

lemma CarryInv.slot_disjoint {st : MachineState} {base : ℤ} {length rank : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} {tree : RankedTree} {F : Finset ℤ}
    (h : CarryInv st base length rank slots roots feet tree F) (hr : rank < length) :
    Disjoint F (feet rank) := h.separate.mono_right (foot_subset_queueCells _ _ _ _ hr)

lemma CarryInv.removed_separate {st : MachineState} {base : ℤ} {length rank : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} {tree : RankedTree} {F : Finset ℤ}
    (h : CarryInv st base length rank slots roots feet tree F) (hr : rank < length) :
    Disjoint (F ∪ feet rank) (queueCells base length (Function.update feet rank ∅)) := by
  apply Finset.disjoint_union_left.mpr
  exact ⟨h.separate.mono_right (queueCells_clear_subset _ _ _ _),h.queue.removed_disjoint rank hr⟩

lemma CarryInv.occupied_positive {st : MachineState} {base : ℤ} {length rank : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} {tree : RankedTree} {F : Finset ℤ}
    (h : CarryInv st base length rank slots roots feet tree F) (hr : rank < length)
    (u : RankedTree) (hu : slots rank=some u) : 0 < st.scalar.core.ptrs 6 := by
  have hn := h.queue.node rank hr
  rw [hu] at hn
  have hp := hn.root_view.choose_spec.choose_spec.1
  rw [h.current]
  omega

lemma CarryInv.pay {st : MachineState} {base : ℤ} {length rank : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} {tree : RankedTree} {F : Finset ℤ}
    (h : CarryInv st base length rank slots roots feet tree F) :
    CarryInv (payUnit st) base length rank slots roots feet tree F :=
  ⟨h.zero,h.basePointer,h.rankPointer,h.address,h.current,h.queue,h.treeRep,h.separate,h.valid⟩

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapCarryStep

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section

set_option maxHeartbeats 1200000 in
lemma heap_carry_step (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base : ℤ) (length rank : ℕ)
    (slots : RankSlots) (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ) (tree : RankedTree) (F : Finset ℤ)
    (h : CarryInv st base length rank slots roots feet tree F) (hr : rank+1 < length)
    (u : RankedTree) (hu : slots rank=some u) :
    ∃ steps out, MachineEval m g ω heapCarryBodyCode st steps out ∧ steps ≤ 19 ∧
      CarryInv out base length (rank+1) (Function.update slots rank none)
        (Function.update roots rank 0) (Function.update feet rank ∅) (tree.link u) (F ∪ feet rank) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+steps ∧ out.output=st.output ∧
      (F ∪ feet rank) ∪ queueCells base length (Function.update feet rank ∅)=F ∪ queueCells base length feet ∧
      (∀ z, z ∉ F ∪ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z) := by
  have hr0 : rank < length := by omega
  let A := payUnit (integerWrite st (base+(rank : ℤ)) 0)
  have ah : A.scalar.halted=false := by simp [A,payUnit,pcSet,integerWrite,hh]
  have hcell : base+(rank : ℤ) ∈ queueCells base length feet :=
    Finset.mem_union_left _ ((mem_arrayCells _ _ _).mpr ⟨rank,hr0,rfl⟩)
  have houtside : base+(rank : ℤ) ∉ F := by
    intro hf
    exact Finset.disjoint_left.mp h.separate hf hcell
  have htreeA : ForestRep A.scalar.integerMemory (A.scalar.core.ptrs 5)
      (.node tree.key tree.children .nil) F := h.treeRep.frame_write_outside houtside
  have huA : ForestRep A.scalar.integerMemory (A.scalar.core.ptrs 6)
      (.node u.key u.children .nil) (feet rank) := by
    have hh := h.queue.node_survives_array_write rank rank hr0 hr0 0
    rw [hu] at hh
    change ForestRep _ (st.scalar.core.ptrs 6) _ _
    rw [h.current]
    exact hh
  obtain ⟨c,mid,ec,hc,hrep,hframe,hreal,hwork,houtput⟩ :=
    heap_combine_represented m g ω A ah tree u F (feet rank) htreeA huA (h.slot_disjoint hr0)
  have hclear : RankArrayRep A.scalar.integerMemory base length
      (Function.update slots rank none) (Function.update roots rank 0) (Function.update feet rank ∅) :=
    h.queue.clear rank hr0
  have hsep := h.removed_separate hr0
  have hqmid : RankArrayRep mid.scalar.integerMemory base length
      (Function.update slots rank none) (Function.update roots rank 0) (Function.update feet rank ∅) := by
    apply hclear.frame
    intro a ha
    apply hframe
    intro hf
    exact Finset.disjoint_left.mp hsep hf ha
  have ec' : MachineEval m g ω heapCombineCode
      (payUnit (integerWrite st (st.scalar.core.ptrs 15) (st.scalar.core.ptrs 0))) c mid := by
    simpa only [h.address,h.zero] using ec
  have hreal' : mid.scalar.core.mem=st.scalar.core.mem := hreal
  have hwork' : mid.work=st.work+1+c := by simpa [A,payUnit,pcSet,integerWrite] using hwork
  have houtput' : mid.output=st.output := houtput
  obtain ⟨out,eb,omem,op5,o0,o13,o14,o15,o6,oreal,owork,ooutput⟩ :=
    heap_carry_body_of_combine m g ω st hh c mid ec' hreal' hwork' houtput'
  have hqout : RankArrayRep out.scalar.integerMemory base length
      (Function.update slots rank none) (Function.update roots rank 0) (Function.update feet rank ∅) := by
    rw [omem]
    exact hqmid
  have howned : (F ∪ feet rank) ∪ queueCells base length (Function.update feet rank ∅)=
      F ∪ queueCells base length feet := by
    rw [←queueCells_clear_union base length rank feet hr0]
    ext z
    simp [or_assoc,or_comm,or_left_comm]
  have hunchanged : ∀ z, z ∉ F ∪ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z := by
    intro z hz
    rw [omem]
    have hn : z ∉ F ∪ feet rank := by
      intro hmem
      rcases Finset.mem_union.mp hmem with hf|hg
      · exact hz (Finset.mem_union_left _ hf)
      · exact hz (Finset.mem_union_right _ (foot_subset_queueCells _ _ _ _ hr0 hg))
    rw [hframe z hn]
    change Function.update st.scalar.integerMemory (base+(rank : ℤ)) 0 z=st.scalar.integerMemory z
    apply Function.update_of_ne
    intro heq
    subst z
    exact hz (Finset.mem_union_right _ hcell)
  refine ⟨c+4,out,eb,by omega,?_,oreal,owork,ooutput,howned,hunchanged⟩
  refine ⟨o0.trans h.zero,o13.trans h.basePointer,?_,?_,?_,hqout,?_,hsep,?_⟩
  · simpa [h.rankPointer,Nat.cast_add] using o14
  · simpa [h.basePointer,h.rankPointer,Nat.cast_add,Int.add_assoc] using o15
  · rw [o6]
    have ha : out.scalar.core.ptrs 15=base+((rank+1 : ℕ) : ℤ) := by
      simpa [h.basePointer,h.rankPointer,Nat.cast_add,Int.add_assoc] using o15
    rw [ha]
    exact hqout.array (rank+1) hr
  · rw [omem,op5]
    exact hrep
  · exact tree.link_valid u rank h.valid (h.queue.valid rank u hu)

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapCarryLoop

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 1200000 in
lemma heap_carry_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base : ℤ) (length fuel rank : ℕ)
    (slots : RankSlots) (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ) (tree : RankedTree) (F : Finset ℤ)
    (h : CarryInv st base length rank slots roots feet tree F)
    (hcap : rank+fuel < length) (hfree : slots (rank+fuel)=none) :
    ∃ steps out j slots' roots' feet' tree' F',
      MachineEval m g ω heapCarryLoopCode st steps out ∧ steps ≤ 21*fuel+1 ∧
      rank ≤ j ∧ j ≤ rank+fuel ∧ CarryInv out base length j slots' roots' feet' tree' F' ∧
      slots' j=none ∧ slotsSupport slots' ∪ ↑tree'.support=slotsSupport slots ∪ ↑tree.support ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+steps ∧ out.output=st.output ∧
      F' ∪ queueCells base length feet'=F ∪ queueCells base length feet ∧
      (∀ z, z ∉ F ∪ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z) := by
  have hr : rank < length := by omega
  by_cases hempty : slots rank=none
  · have hn := h.queue.node rank hr
    rw [hempty] at hn
    have hz : st.scalar.core.ptrs 6=0 := h.current.trans hn.1
    have ed : MachineEval m g ω heapCarryLoopCode st 1 (payUnit st) :=
      MachineEval.pointerDone (r := 6) (s := 0) (body := heapCarryBodyCode) hh
        (by rw [hz,h.zero])
    exact ⟨1,payUnit st,rank,slots,roots,feet,tree,F,ed,by omega,le_rfl,by omega,
      h.pay,hempty,rfl,rfl,by simp,rfl,rfl,(by intros; rfl)⟩
  · cases hs : slots rank with
    | none => exact False.elim (hempty hs)
    | some u =>
      cases fuel with
      | zero => exact False.elim (hempty (by simpa using hfree))
      | succ fuel =>
        have hp : 0 < st.scalar.core.ptrs 6 := h.occupied_positive hr u hs
        obtain ⟨v,mid,eb,hv,hm,hrm,hwm,hom,hownstep,hframestep⟩ :=
          heap_carry_step m g ω (payUnit st) (by simpa using hh) base length rank slots roots feet tree F
            h.pay (by omega) u hs
        have mh : mid.scalar.halted=false := (eb.halted heapCarryBodyCode_wellFormed).trans (by simpa using hh)
        have hfree' : (Function.update slots rank none) (rank+1+fuel)=none := by
          rw [Function.update_of_ne (by omega)]
          rw [show rank+1+fuel=rank+(fuel+1) by omega]
          exact hfree
        obtain ⟨w,out,j,s',r',f',t',F',er,hw,hj,hj',hi,he,hcontents,hr',hwork,houtput,hownrec,hframerec⟩ :=
          heap_carry_loop_exec m g ω (payUnit mid) (by simpa using mh) base length fuel (rank+1)
            (Function.update slots rank none) (Function.update roots rank 0) (Function.update feet rank ∅)
            (tree.link u) (F ∪ feet rank) hm.pay (by omega) hfree'
        refine ⟨1+v+1+w,out,j,s',r',f',t',F',?_,by omega,by omega,by omega,hi,he,?_,?_,?_,?_,hownrec.trans hownstep,?_⟩
        · exact MachineEval.pointerNext (r := 6) (s := 0) hh (by rw [h.zero]; omega) eb er
        · exact hcontents.trans (clear_link_support slots rank tree u hs)
        · exact hr'.trans hrm
        · rw [hwork,payUnit_work,hwm,payUnit_work]
          push_cast
          ring
        · exact houtput.trans hom
        · intro z hz
          have hn : z ∉ (F ∪ feet rank) ∪ queueCells base length (Function.update feet rank ∅) := by
            rw [hownstep]
            exact hz
          rw [hframerec z hn]
          exact hframestep z hz
termination_by fuel

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapCarryExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section

set_option maxHeartbeats 1500000 in
lemma heap_carry_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base : ℤ) (length fuel rank : ℕ)
    (slots : RankSlots) (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ) (tree : RankedTree) (F : Finset ℤ)
    (hbase : st.scalar.core.ptrs 13=base) (hrank : st.scalar.core.ptrs 14=(rank : ℤ))
    (hq : RankArrayRep st.scalar.integerMemory base length slots roots feet)
    (ht : ForestRep st.scalar.integerMemory (st.scalar.core.ptrs 5) (.node tree.key tree.children .nil) F)
    (hsep : Disjoint F (queueCells base length feet)) (hvalid : tree.valid rank)
    (hcap : rank+fuel < length) (hfree : slots (rank+fuel)=none) :
    ∃ steps out slots' roots' feet', MachineEval m g ω heapCarryCode st steps out ∧
      steps ≤ 21*fuel+5 ∧ RankArrayRep out.scalar.integerMemory base length slots' roots' feet' ∧
      slotsSupport slots'=slotsSupport slots ∪ ↑tree.support ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+steps ∧ out.output=st.output ∧
      queueCells base length feet'=F ∪ queueCells base length feet ∧
      (∀ z, z ∉ F ∪ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z) := by
  let A := payUnit (pointerWrite st 0 0)
  let B := payUnit (pointerWrite A 15 (base+(rank : ℤ)))
  let C := payUnit (pointerWrite B 6 (roots rank))
  have ea := pset_eval m g ω st 0 0 hh
  have ah : A.scalar.halted=false := by simp [A,payUnit,pcSet,pointerWrite,hh]
  have bh : B.scalar.halted=false := by simp [B,payUnit,pcSet,pointerWrite,ah]
  have ch : C.scalar.halted=false := by simp [C,payUnit,pcSet,pointerWrite,bh]
  have eb : MachineEval m g ω (.atom (.scalar (.pointerAdd 15 13 14))) A 1 B := by
    have hb : A.scalar.core.ptrs 13=base := by simp [A,payUnit,pcSet,pointerWrite,hbase]
    have hr : A.scalar.core.ptrs 14=(rank : ℤ) := by simp [A,payUnit,pcSet,pointerWrite,hrank]
    simpa only [B,hb,hr] using pointerAdd_eval m g ω A 15 13 14 ah
  have ec : MachineEval m g ω (.atom (.scalar (.integerLoad 6 15))) B 1 C := by
    have hv : B.scalar.integerMemory (B.scalar.core.ptrs 15)=roots rank := by
      simpa [B,A,payUnit,pcSet,pointerWrite] using hq.array rank (by omega)
    simpa only [C,hv] using integerLoad_eval m g ω B 6 15 bh
  have hi : CarryInv C base length rank slots roots feet tree F := by
    refine ⟨?_,?_,?_,?_,?_,hq,ht,hsep,hvalid⟩
    all_goals simp [C,B,A,payUnit,pcSet,pointerWrite,hbase,hrank]
  obtain ⟨v,mid,j,s',r',f',t',F',el,hv,hj,hj',hm,hempty,hcontents,hreal,hwork,houtput,howned,hframe⟩ :=
    heap_carry_loop_exec m g ω C ch base length fuel rank slots roots feet tree F hi hcap hfree
  have mh : mid.scalar.halted=false := (el.halted heapCarryCode_wellFormed.2.2.2.1).trans ch
  let out := payUnit (integerWrite mid (base+(j : ℤ)) (mid.scalar.core.ptrs 5))
  have eo : MachineEval m g ω (.atom (.scalar (.integerStore 15 5))) mid 1 out := by
    simpa only [out,hm.address] using integerStore_eval m g ω mid 15 5 mh
  have hstored := hm.queue.store j (by omega) t' hm.valid F' hm.treeRep hm.separate
  have hout : RankArrayRep out.scalar.integerMemory base length
      (Function.update s' j (some t')) (Function.update r' j (mid.scalar.core.ptrs 5)) (Function.update f' j F') := hstored
  have hjlength : j < length := by omega
  have hemptyFoot : f' j=∅ := by
    have hn := hm.queue.node j hjlength
    rw [hempty] at hn
    exact hn.2
  have hfinalowned : queueCells base length (Function.update f' j F')=F ∪ queueCells base length feet := by
    rw [queueCells_store_none _ _ _ _ _ hjlength hemptyFoot,Finset.union_comm]
    exact howned
  have hfinalframe : ∀ z, z ∉ F ∪ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z := by
    intro z hz
    have haddr : z ≠ base+(j : ℤ) := by
      intro heq
      subst z
      apply hz
      rw [←howned]
      exact Finset.mem_union_right _ (Finset.mem_union_left _ ((mem_arrayCells _ _ _).mpr ⟨j,hjlength,rfl⟩))
    change Function.update mid.scalar.integerMemory (base+(j : ℤ)) (mid.scalar.core.ptrs 5) z=st.scalar.integerMemory z
    rw [Function.update_of_ne haddr]
    exact hframe z hz
  refine ⟨v+4,out,_,_,_,?_,by omega,hout,?_,?_,?_,?_,hfinalowned,hfinalframe⟩
  · unfold heapCarryCode sequenceCode
    have e := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq el (MachineEval.seq eo (MachineEval.skip out)))))
    convert e using 1 <;> (first | rfl | omega)
  · exact (slotsSupport_store_none s' j t' hempty).trans hcontents
  · simpa [out,C,B,A,payUnit,pcSet,pointerWrite,integerWrite] using hreal
  · simp only [out,payUnit_work,integerWrite]
    rw [hwork]
    simp [C,B,A,payUnit,pcSet,pointerWrite]
    push_cast
    ring
  · simpa [out,C,B,A,payUnit,pcSet,pointerWrite,integerWrite] using houtput

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IntegerScaleCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


set_option maxHeartbeats 800000 in
lemma integer_scale_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω integerScaleBodyCode st 2 out ∧
      out.scalar.core.ptrs 42=st.scalar.core.ptrs 42+st.scalar.core.ptrs 40 ∧
      out.scalar.core.ptrs 43=st.scalar.core.ptrs 43+1 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+2 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨out,e,hp,hi,hr,hw,ho,hho⟩ := integerScaleBodyRoutine.execute m g ω st hh
  refine ⟨out,e,?_,?_,hi,hr,hw,ho,hho⟩
  all_goals rw [hp]; simp [integerScaleBodyRoutine,PointerRoutine.sequence,PointerRoutine.run,
    PointerOp.update,PointerOp.destination,PointerOp.result]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IntegerScaleExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1000000 in
lemma integer_scale_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (x : ℤ) (count remaining i : ℕ) (y : ℤ) (st : MachineState)
    (hh : st.scalar.halted=false) (hx : st.scalar.core.ptrs 40=x)
    (hc : st.scalar.core.ptrs 41=(count : ℤ)) (hi : st.scalar.core.ptrs 43=(i : ℤ))
    (hy : st.scalar.core.ptrs 42=y) (hlen : i+remaining=count) :
    ∃ out, MachineEval m g ω integerScaleLoopCode st (4*remaining+1) out ∧
      out.scalar.core.ptrs 40=x ∧ out.scalar.core.ptrs 41=(count : ℤ) ∧
      out.scalar.core.ptrs 43=(count : ℤ) ∧ out.scalar.core.ptrs 42=y+x*(remaining : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+(4*remaining+1 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction remaining generalizing st i y with
  | zero =>
    have he : i=count := by omega
    refine ⟨payUnit st,?_,hx,hc,?_,?_,rfl,rfl,by simp,rfl,hh⟩
    · exact MachineEval.pointerDone (r:=41) (s:=43) (body:=integerScaleBodyCode) hh (by rw [hc,hi,he])
    · simpa [he] using hi
    · simpa using hy
  | succ remaining ih =>
    obtain ⟨mid,eb,hacc,hindex,hmI,hmR,hmW,hmO,hmH⟩ := integer_scale_body_exec m g ω (payUnit st) hh
    have hm40 : mid.scalar.core.ptrs 40=x := (eb.pointer_frame 40 (by decide)).trans hx
    have hm41 : mid.scalar.core.ptrs 41=(count : ℤ) := (eb.pointer_frame 41 (by decide)).trans hc
    have hm43 : mid.scalar.core.ptrs 43=(i+1 : ℕ) := by simpa only [payUnit,pcSet,hi,Nat.cast_add,Nat.cast_one] using hindex
    have hm42 : mid.scalar.core.ptrs 42=y+x := by simpa only [payUnit,pcSet,hy,hx] using hacc
    obtain ⟨out,er,ho40,ho41,ho43,ho42,hoI,hoR,hoW,hoO,hoH⟩ :=
      ih (i+1) (y+x) (payUnit mid) hmH hm40 hm41 hm43 hm42 (by omega)
    refine ⟨out,?_,ho40,ho41,ho43,?_,hoI.trans hmI,hoR.trans hmR,?_,hoO.trans hmO,hoH⟩
    · have e := MachineEval.pointerNext (r:=41) (s:=43) hh (by rw [hc,hi]; omega) eb er
      convert e using 1 <;> (first | rfl | omega)
    · rw [ho42]
      push_cast
      ring
    · rw [hoW,payUnit_work,hmW,payUnit_work]
      push_cast
      ring

set_option maxHeartbeats 1000000 in
lemma integer_scale_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (x : ℤ) (count : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (hx : st.scalar.core.ptrs 40=x) (hc : st.scalar.core.ptrs 41=(count : ℤ)) :
    ∃ out, MachineEval m g ω integerScaleCode st (4*count+3) out ∧
      out.scalar.core.ptrs 40=x ∧ out.scalar.core.ptrs 41=(count : ℤ) ∧
      out.scalar.core.ptrs 43=(count : ℤ) ∧ out.scalar.core.ptrs 42=x*(count : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+(4*count+3 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let A := payUnit (pointerWrite st 42 0)
  let B := payUnit (pointerWrite A 43 0)
  have ea := pset_eval m g ω st 42 0 hh
  have ah : A.scalar.halted=false := hh
  have eb : MachineEval m g ω (coreCode (.pset 43 0)) A 1 B := pset_eval m g ω A 43 0 ah
  have bh : B.scalar.halted=false := hh
  have bx : B.scalar.core.ptrs 40=x := by simpa [B,A,payUnit,pcSet,pointerWrite] using hx
  have bc : B.scalar.core.ptrs 41=(count : ℤ) := by simpa [B,A,payUnit,pcSet,pointerWrite] using hc
  obtain ⟨out,el,ho40,ho41,ho43,ho42,hoI,hoR,hoW,hoO,hoH⟩ :=
    integer_scale_loop_exec m g ω x count count 0 0 B bh bx bc (by simp [B,payUnit,pcSet,pointerWrite])
      (by simp [B,A,payUnit,pcSet,pointerWrite]) (by omega)
  refine ⟨out,?_,ho40,ho41,ho43,by simpa using ho42,hoI,hoR,?_,hoO,hoH⟩
  · have e := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq el (MachineEval.skip out)))
    convert e using 1 <;> (first | rfl | omega)
  · rw [hoW]
    simp only [B,A,payUnit_work,pointerWrite]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LinearRoutine

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def unitInstruction (i : Instruction) : Prop :=
  match i with
  | .solve _ => False
  | _ => straightInstruction i

lemma unitInstruction_straight {i : Instruction} (h : unitInstruction i) : straightInstruction i := by
  cases i <;> simp_all [unitInstruction]

lemma unitInstruction_advances (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (i : Instruction) (hi : unitInstruction i) (st : MachineState) (hh : st.scalar.halted=false) :
    (atomState m g ω i st).scalar.core.pc=1 := by
  cases i with
  | solve r => exact False.elim hi
  | emit r s => simp [atomState,machineStep,pcSet,hh]
  | scalar i =>
    cases i with
    | core c =>
      cases c <;> simp_all [unitInstruction,straightInstruction,atomState,machineStep,pcSet,
        hh,LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep]
    | _ => simp_all [unitInstruction,straightInstruction,atomState,machineStep,pcSet,hh,LocalPush.step,scalarProgram]

lemma unitInstruction_work (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (i : Instruction) (hi : unitInstruction i) (st : MachineState) (hh : st.scalar.halted=false) :
    (atomState m g ω i st).work=st.work+1 := by
  cases i <;> simp_all [unitInstruction,atomState,machineStep,pcSet,hh]

def linearRun (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool) : List Instruction → MachineState → MachineState
  | [],st => st
  | i::rest,st => linearRun m g ω rest (pcSet (atomState m g ω i st) 0)

lemma linear_execute (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (instructions : List Instruction) (h : ∀ i ∈ instructions, unitInstruction i)
    (st : MachineState) (hh : st.scalar.halted=false) :
    MachineEval m g ω (linearCode instructions) st instructions.length (linearRun m g ω instructions st) ∧
      (linearRun m g ω instructions st).work=st.work+instructions.length ∧
      (linearRun m g ω instructions st).scalar.halted=false := by
  induction instructions generalizing st with
  | nil => exact ⟨MachineEval.skip st,by simp [linearRun],hh⟩
  | cons i rest ih =>
    have hu := h i (by simp)
    have hr : ∀ j ∈ rest, unitInstruction j := by intro j hj; exact h j (by simp [hj])
    have hm : (pcSet (atomState m g ω i st) 0).scalar.halted=false :=
      (atomState_halted m g ω i st (unitInstruction_straight hu)).trans hh
    obtain ⟨er,hw,hhout⟩ := ih hr _ hm
    have ea := MachineEval.atom (m:=m) (g:=g) (ω:=ω) i st (unitInstruction_advances m g ω i hu st hh)
    refine ⟨?_,?_,hhout⟩
    · simpa [linearCode,sequenceCode,linearRun,Nat.add_comm] using MachineEval.seq ea er
    · rw [linearRun,hw,pcSet_work,unitInstruction_work m g ω i hu st hh]
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      ac_rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RegisterEffects

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def registerReadOnly : Instruction → Prop
  | .scalar (.core (.const ..)) | .scalar (.core (.add ..)) | .scalar (.core (.sub ..)) |
    .scalar (.core (.mul ..)) | .scalar (.core (.div ..)) | .scalar (.core (.load ..)) |
    .scalar (.pointerReal ..) | .scalar (.coin ..) => False
  | _ => True

lemma atomState_register_readOnly (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (i : Instruction) (st : MachineState) (h : registerReadOnly i) :
    (atomState m g ω i st).scalar.core.regs=st.scalar.core.regs := by
  by_cases hh : st.scalar.halted=true
  · simp [atomState,machineStep,pcSet,hh]
  have hh : st.scalar.halted=false := Bool.eq_false_iff.mpr hh
  cases i with
  | emit a b => simp [atomState,machineStep,pcSet,hh]
  | solve r =>
    simp only [atomState,machineStep,pcSet_halted,pcSet_pc,hh,Bool.false_eq_true,if_false,List.getElem?_cons_zero]
    split_ifs <;> rfl
  | scalar i =>
    cases i with
    | core c => cases c <;> simp_all [registerReadOnly,atomState,machineStep,pcSet,hh,LocalPush.step,scalarProgram,
        LocalPush.coreProgram,SmaleNinth.RAMStep] <;> split_ifs <;> rfl
    | _ => simp_all [registerReadOnly,atomState,machineStep,pcSet,hh,LocalPush.step,scalarProgram]

lemma MachineEval.register_frame {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {code : MachineCode} {st out : MachineState} {u : ℕ} (e : MachineEval m g ω code st u out)
    (h : code.allAtoms registerReadOnly) : out.scalar.core.regs=st.scalar.core.regs := by
  apply e.frame (fun z => z.scalar.core.regs) (by intros; rfl) (by intro; rfl)
  exact code.allAtoms_mono _ _ (fun i hi z => atomState_register_readOnly m g ω i z hi) h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RegisterTargets

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def registerTargets : Instruction → Finset ℕ
  | .scalar (.core (.const r _)) | .scalar (.core (.load r _)) |
    .scalar (.core (.add r _ _)) | .scalar (.core (.sub r _ _)) |
    .scalar (.core (.mul r _ _)) | .scalar (.core (.div r _ _)) |
    .scalar (.pointerReal r _) | .scalar (.coin r) => {r}
  | _ => ∅

def MachineCode.registerTargets : MachineCode → Finset ℕ
  | .skip => ∅
  | .atom i => NearlyOptimalPPR.Computation.registerTargets i
  | .seq a b | .branchReal _ a b | .branchPointer _ _ a b => a.registerTargets ∪ b.registerTargets
  | .whileReal _ b | .whilePointer _ _ b => b.registerTargets

lemma atomState_register_target_frame (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (i : Instruction) (st : MachineState) (r : ℕ) (hr : r ∉ registerTargets i) :
    (atomState m g ω i st).scalar.core.regs r=st.scalar.core.regs r := by
  by_cases hh : st.scalar.halted=true
  · simp [atomState,machineStep,pcSet,hh]
  have hh : st.scalar.halted=false := Bool.eq_false_iff.mpr hh
  cases i with
  | emit a b => simp [atomState,machineStep,pcSet,hh]
  | solve s =>
    simp only [atomState,machineStep,pcSet_halted,pcSet_pc,hh,Bool.false_eq_true,if_false,List.getElem?_cons_zero]
    split_ifs <;> rfl
  | scalar i =>
    cases i with
    | core c => cases c <;> simp_all [registerTargets,atomState,machineStep,pcSet,hh,LocalPush.step,scalarProgram,
        LocalPush.coreProgram,SmaleNinth.RAMStep] <;> split_ifs <;> rfl
    | _ => simp_all [registerTargets,atomState,machineStep,pcSet,hh,LocalPush.step,scalarProgram]

lemma MachineCode.allAtoms_registerTargets (code : MachineCode) (r : ℕ) (hr : r ∉ code.registerTargets) :
    code.allAtoms (fun i => r ∉ NearlyOptimalPPR.Computation.registerTargets i) := by
  induction code <;> simp_all [MachineCode.allAtoms,MachineCode.registerTargets]

lemma MachineEval.real_register_frame {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {code : MachineCode} {st out : MachineState} {u : ℕ} (e : MachineEval m g ω code st u out)
    (r : ℕ) (hr : r ∉ code.registerTargets) : out.scalar.core.regs r=st.scalar.core.regs r := by
  apply e.frame (fun z => z.scalar.core.regs r) (by intros; rfl) (by intro; rfl)
  exact code.allAtoms_mono _ _ (fun i hi z => atomState_register_target_frame m g ω i z r hi)
    (code.allAtoms_registerTargets r hr)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueryEffects

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def queryReadOnly : Instruction → Prop
  | .scalar (.deg ..) | .scalar (.nbr ..) => False
  | _ => True

lemma atomState_query_readOnly (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (i : Instruction) (st : MachineState) (h : queryReadOnly i) :
    (atomState m g ω i st).scalar.queries=st.scalar.queries := by
  by_cases hh : st.scalar.halted=true
  · simp [atomState,machineStep,pcSet,hh]
  have hh : st.scalar.halted=false := Bool.eq_false_iff.mpr hh
  cases i with
  | emit a b => simp [atomState,machineStep,pcSet,hh]
  | solve r =>
    simp only [atomState,machineStep,pcSet_halted,pcSet_pc,hh,Bool.false_eq_true,if_false,List.getElem?_cons_zero]
    split_ifs <;> rfl
  | scalar i =>
    cases i with
    | core c => cases c <;> simp_all [queryReadOnly,atomState,machineStep,pcSet,hh,LocalPush.step,scalarProgram,
        LocalPush.coreProgram,SmaleNinth.RAMStep] <;> split_ifs <;> rfl
    | _ => simp_all [queryReadOnly,atomState,machineStep,pcSet,hh,LocalPush.step,scalarProgram]

lemma MachineEval.query_frame {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {code : MachineCode} {st out : MachineState} {u : ℕ} (e : MachineEval m g ω code st u out)
    (h : code.allAtoms queryReadOnly) : out.scalar.queries=st.scalar.queries := by
  apply e.frame (fun z => z.scalar.queries) (by intros; rfl) (by intro; rfl)
  exact code.allAtoms_mono _ _ (fun i hi z => atomState_query_readOnly m g ω i z hi) h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CodePredicateDecidable

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

instance queryReadOnlyDecidable (i : Instruction) : Decidable (queryReadOnly i) := by
  cases i with
  | scalar i => cases i <;> simp [queryReadOnly] <;> infer_instance
  | solve r => exact isTrue trivial
  | emit a b => exact isTrue trivial

def MachineCode.decideAllAtoms (P : Instruction → Prop) [DecidablePred P] :
    (code : MachineCode) → Decidable (code.allAtoms P)
  | .skip => isTrue trivial
  | .atom i => inferInstanceAs (Decidable (P i))
  | .seq a b | .branchReal _ a b | .branchPointer _ _ a b =>
      letI := a.decideAllAtoms P
      letI := b.decideAllAtoms P
      inferInstanceAs (Decidable (a.allAtoms P ∧ b.allAtoms P))
  | .whileReal _ body | .whilePointer _ _ body => body.decideAllAtoms P

instance MachineCode.allAtomsDecidable (P : Instruction → Prop) [DecidablePred P] (code : MachineCode) :
    Decidable (code.allAtoms P) := code.decideAllAtoms P

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma levelHeaderAddress_injective (level level' slot slot' : ℕ) (hs : slot < 32) (hs' : slot' < 32)
    (he : levelHeaderAddress level slot=levelHeaderAddress level' slot') : level=level' ∧ slot=slot' := by
  unfold levelHeaderAddress at he
  omega

lemma levelHeaderAddress_positive (level slot : ℕ) : 128 ≤ levelHeaderAddress level slot := by
  unfold levelHeaderAddress
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderExecution

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1600000 in
lemma level_header_address_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level slot : ℕ) (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω (levelHeaderAddressCode slot) st 8 out ∧
      out.scalar.core.ptrs 102=levelHeaderAddress level slot ∧
      out.scalar.core.ptrs 40=st.scalar.core.ptrs 40 ∧ out.scalar.core.ptrs 41=st.scalar.core.ptrs 41 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+8 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω (levelHeaderAddressInstructions slot)
    (by simp [levelHeaderAddressInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,ex.pointer_frame 40 (by simp [linearCode,levelHeaderAddressInstructions,sequenceCode,MachineCode.pointerTargets,pointerTargets]),
    ex.pointer_frame 41 (by simp [linearCode,levelHeaderAddressInstructions,sequenceCode,MachineCode.pointerTargets,pointerTargets]),
    ?_,?_,ex.query_frame (by simp [linearCode,levelHeaderAddressInstructions,sequenceCode,MachineCode.allAtoms,queryReadOnly]),hW,?_,hH⟩
  all_goals simp [linearRun,levelHeaderAddressInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hl,levelHeaderAddress,Int.add_assoc,Int.add_left_comm,Int.add_comm] <;> omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderAccess

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderAddressCode_registerReadOnly (slot : ℕ) : (levelHeaderAddressCode slot).allAtoms registerReadOnly := by
  simp [levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,MachineCode.allAtoms,registerReadOnly]

set_option maxHeartbeats 1600000 in
lemma level_header_integer_load_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level slot : ℕ) (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω (levelHeaderIntegerLoadCode slot) st 9 out ∧
      out.scalar.core.ptrs 105=st.scalar.integerMemory (levelHeaderAddress level slot) ∧
      out.scalar.core.ptrs 40=st.scalar.core.ptrs 40 ∧ out.scalar.core.ptrs 41=st.scalar.core.ptrs 41 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+9 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a102,a40,a41,aI,aR,aQ,aW,aO,aH⟩ := level_header_address_exec m g ω st hh level slot hl
  let out := payUnit (pointerWrite a 105 (st.scalar.integerMemory (levelHeaderAddress level slot)))
  have eb : MachineEval m g ω (.atom (.scalar (.integerLoad 105 102))) a 1 out := by
    simpa only [out,a102,aI] using integerLoad_eval m g ω a 105 102 aH
  refine ⟨out,MachineEval.seq ea eb,by simp [out,payUnit,pcSet,pointerWrite],?_,?_,aI,aR,?_,aO,aH⟩
  · exact (eb.pointer_frame 40 (by decide)).trans a40
  · exact (eb.pointer_frame 41 (by decide)).trans a41
  · change a.work+1= _
    rw [aW]; norm_num; ring

set_option maxHeartbeats 1600000 in
lemma level_header_integer_store_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level slot : ℕ) (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω (levelHeaderIntegerStoreCode slot) st 9 out ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (levelHeaderAddress level slot) (st.scalar.core.ptrs 105) ∧
      out.scalar.core.ptrs 40=st.scalar.core.ptrs 40 ∧ out.scalar.core.ptrs 41=st.scalar.core.ptrs 41 ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+9 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a102,a40,a41,aI,aR,aQ,aW,aO,aH⟩ := level_header_address_exec m g ω st hh level slot hl
  have a105 := ea.pointer_frame 105 (by simp [levelHeaderAddressCode,levelHeaderAddressInstructions,
    linearCode,sequenceCode,MachineCode.pointerTargets,pointerTargets])
  let out := payUnit (integerWrite a (levelHeaderAddress level slot) (st.scalar.core.ptrs 105))
  have eb : MachineEval m g ω (.atom (.scalar (.integerStore 102 105))) a 1 out := by
    simpa only [out,a102,a105] using integerStore_eval m g ω a 102 105 aH
  refine ⟨out,MachineEval.seq ea eb,?_,?_,?_,aR,?_,aO,aH⟩
  · change Function.update a.scalar.integerMemory _ _= _
    rw [aI]
  · exact (eb.pointer_frame 40 (by decide)).trans a40
  · exact (eb.pointer_frame 41 (by decide)).trans a41
  · change a.work+1= _
    rw [aW]; norm_num; ring

set_option maxHeartbeats 1600000 in
lemma level_header_real_load_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level slot : ℕ) (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω (levelHeaderRealLoadCode slot) st 9 out ∧
      out.scalar.core.regs 10=st.scalar.core.mem (levelHeaderAddress level slot) ∧
      out.scalar.core.ptrs 40=st.scalar.core.ptrs 40 ∧ out.scalar.core.ptrs 41=st.scalar.core.ptrs 41 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+9 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a102,a40,a41,aI,aR,aQ,aW,aO,aH⟩ := level_header_address_exec m g ω st hh level slot hl
  let out := payUnit (realWrite a 10 (st.scalar.core.mem (levelHeaderAddress level slot)))
  have eb : MachineEval m g ω (coreCode (.load 10 102)) a 1 out := by
    simpa only [out,coreCode,a102,aR] using load_eval m g ω a 10 102 aH
  refine ⟨out,MachineEval.seq ea eb,by simp [out,payUnit,pcSet,realWrite],?_,?_,aI,aR,?_,aO,aH⟩
  · exact (eb.pointer_frame 40 (by decide)).trans a40
  · exact (eb.pointer_frame 41 (by decide)).trans a41
  · change a.work+1= _
    rw [aW]; norm_num; ring

set_option maxHeartbeats 1600000 in
lemma level_header_real_store_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level slot : ℕ) (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω (levelHeaderRealStoreCode slot) st 9 out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (levelHeaderAddress level slot) (st.scalar.core.regs 10) ∧
      out.scalar.core.ptrs 40=st.scalar.core.ptrs 40 ∧ out.scalar.core.ptrs 41=st.scalar.core.ptrs 41 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.work=st.work+9 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a102,a40,a41,aI,aR,aQ,aW,aO,aH⟩ := level_header_address_exec m g ω st hh level slot hl
  have aRegs := ea.register_frame (levelHeaderAddressCode_registerReadOnly slot)
  let out := payUnit (memoryWrite a (levelHeaderAddress level slot) (st.scalar.core.regs 10))
  have eb : MachineEval m g ω (coreCode (.store 102 10)) a 1 out := by
    simpa only [out,coreCode,a102,aRegs] using store_eval m g ω a 102 10 aH
  refine ⟨out,MachineEval.seq ea eb,?_,?_,?_,aI,?_,aO,aH⟩
  · change Function.update a.scalar.core.mem _ _= _
    rw [aR]
  · exact (eb.pointer_frame 40 (by decide)).trans a40
  · exact (eb.pointer_frame 41 (by decide)).trans a41
  · change a.work+1= _
    rw [aW]; norm_num; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderRealFrom

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderRealFromCode_queryReadOnly (slot source : ℕ) : (levelHeaderRealFromCode slot source).allAtoms queryReadOnly := by
  simp [levelHeaderRealFromCode,levelHeaderRealStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
    linearCode,sequenceCode,coreCode,MachineCode.allAtoms,queryReadOnly]

set_option maxHeartbeats 1600000 in
lemma level_header_real_from_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level slot source : ℕ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) (h1 : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω (levelHeaderRealFromCode slot source) st 10 out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (levelHeaderAddress level slot) (st.scalar.core.regs source) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+10 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := payUnit (realWrite st 10 (st.scalar.core.regs source))
  have ea : MachineEval m g ω (coreCode (.mul 10 source 31)) st 1 a := by
    simpa only [a,coreCode,RealOperation.instruction,RealOperation.value,h1,mul_one] using
      binary_eval m g ω st .mul 10 source 31 hh
  have a100 := (ea.pointer_frame 100 (by simp [coreCode,MachineCode.pointerTargets,pointerTargets])).trans hl
  obtain ⟨out,eb,bR,b40,b41,bI,bW,bO,bH⟩ := level_header_real_store_exec m g ω a hh level slot a100
  have ex : MachineEval m g ω (levelHeaderRealFromCode slot source) st 10 out := MachineEval.seq ea eb
  refine ⟨out,ex,?_,bI,ex.query_frame (levelHeaderRealFromCode_queryReadOnly slot source),?_,bO,bH⟩
  · rw [bR]
    simp only [a,payUnit,pcSet,realWrite,Function.update_self]
  · rw [bW]
    change st.work+1+9= _
    norm_num
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderSet

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1400000 in
lemma level_header_integer_set_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level slot : ℕ) (value : ℤ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω (levelHeaderIntegerSetCode slot value) st 10 out ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (levelHeaderAddress level slot) value ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+10 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := payUnit (pointerWrite st 105 value)
  have ea : MachineEval m g ω (coreCode (.pset 105 value)) st 1 a := pset_eval m g ω st 105 value hh
  have a100 := (ea.pointer_frame 100 (by simp [coreCode,MachineCode.pointerTargets,pointerTargets])).trans hl
  obtain ⟨out,eb,bI,b40,b41,bR,bW,bO,bH⟩ := level_header_integer_store_exec m g ω a hh level slot a100
  refine ⟨out,MachineEval.seq ea eb,?_,bR,?_,bO,bH⟩
  · rw [bI]
    simp only [a,payUnit,pcSet,pointerWrite,Function.update_self]
  · rw [bW]
    change st.work+1+9= _
    norm_num
    ring

set_option maxHeartbeats 1400000 in
lemma level_header_real_zero_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level slot : ℕ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω (levelHeaderRealZeroCode slot) st 10 out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (levelHeaderAddress level slot) 0 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.work=st.work+10 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := payUnit (realWrite st 10 0)
  have ea : MachineEval m g ω (coreCode (.const 10 0)) st 1 a := const_eval m g ω st 10 0 hh
  have a100 := (ea.pointer_frame 100 (by simp [coreCode,MachineCode.pointerTargets,pointerTargets])).trans hl
  obtain ⟨out,eb,bR,b40,b41,bI,bW,bO,bH⟩ := level_header_real_store_exec m g ω a hh level slot a100
  refine ⟨out,MachineEval.seq ea eb,?_,bI,?_,bO,bH⟩
  · rw [bR]
    simp only [a,payUnit,pcSet,realWrite,Function.update_self]
  · rw [bW]
    change st.work+1+9= _
    norm_num
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderSets

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelHeaderIntegerSetsMemory (I : ℤ → ℤ) (level : ℕ) (assignments : List (ℕ × ℤ)) : ℤ → ℤ :=
  assignments.foldl (fun J kv => Function.update J (levelHeaderAddress level kv.1) kv.2) I

lemma levelHeaderIntegerSetCode_level_frame (slot : ℕ) (value : ℤ) :
    100 ∉ (levelHeaderIntegerSetCode slot value).pointerTargets := by
  simp [levelHeaderIntegerSetCode,levelHeaderIntegerStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
    linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets]
lemma levelHeaderIntegerSetCode_queryReadOnly (slot : ℕ) (value : ℤ) :
    (levelHeaderIntegerSetCode slot value).allAtoms queryReadOnly := by
  simp [levelHeaderIntegerSetCode,levelHeaderIntegerStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
    linearCode,sequenceCode,coreCode,MachineCode.allAtoms,queryReadOnly]
set_option maxHeartbeats 1800000 in
lemma level_header_integer_sets_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (assignments : List (ℕ × ℤ)) (st : MachineState) (hh : st.scalar.halted=false) (level : ℕ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω (levelHeaderIntegerSetsCode assignments) st (10*assignments.length) out ∧
      out.scalar.integerMemory=levelHeaderIntegerSetsMemory st.scalar.integerMemory level assignments ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(10*assignments.length : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction assignments generalizing st with
  | nil => exact ⟨st,MachineEval.skip st,rfl,rfl,rfl,by simp,rfl,hh⟩
  | cons kv rest ih =>
    obtain ⟨a,ea,aI,aR,aW,aO,aH⟩ := level_header_integer_set_exec m g ω st hh level kv.1 kv.2 hl
    have a100 := (ea.pointer_frame 100 (levelHeaderIntegerSetCode_level_frame kv.1 kv.2)).trans hl
    obtain ⟨out,eb,bI,bR,bQ,bW,bO,bH⟩ := ih a aH a100
    have ex : MachineEval m g ω (levelHeaderIntegerSetsCode (kv::rest)) st (10*(kv::rest).length) out := by
      have e := MachineEval.seq ea eb
      convert e using 1 <;> (first | rfl | simp [List.length_cons]; omega)
    refine ⟨out,ex,?_,bR.trans aR,?_,?_,bO.trans aO,bH⟩
    · rw [bI,aI]
      rfl
    · rw [bQ]; exact ea.query_frame (levelHeaderIntegerSetCode_queryReadOnly kv.1 kv.2)
    · rw [bW,aW]
      simp only [List.length_cons]
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderRealZeros

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelHeaderRealZerosMemory (R : ℤ → ℝ) (level : ℕ) (slots : List ℕ) : ℤ → ℝ :=
  slots.foldl (fun S slot => Function.update S (levelHeaderAddress level slot) 0) R

lemma levelHeaderRealZeroCode_level_frame (slot : ℕ) : 100 ∉ (levelHeaderRealZeroCode slot).pointerTargets := by
  simp [levelHeaderRealZeroCode,levelHeaderRealStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
    linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets]
lemma levelHeaderRealZeroCode_queryReadOnly (slot : ℕ) : (levelHeaderRealZeroCode slot).allAtoms queryReadOnly := by
  simp [levelHeaderRealZeroCode,levelHeaderRealStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
    linearCode,sequenceCode,coreCode,MachineCode.allAtoms,queryReadOnly]
set_option maxHeartbeats 1800000 in
lemma level_header_real_zeros_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (slots : List ℕ) (st : MachineState) (hh : st.scalar.halted=false) (level : ℕ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω (levelHeaderRealZerosCode slots) st (10*slots.length) out ∧
      out.scalar.core.mem=levelHeaderRealZerosMemory st.scalar.core.mem level slots ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(10*slots.length : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction slots generalizing st with
  | nil => exact ⟨st,MachineEval.skip st,rfl,rfl,rfl,by simp,rfl,hh⟩
  | cons slot rest ih =>
    obtain ⟨a,ea,aR,aI,aW,aO,aH⟩ := level_header_real_zero_exec m g ω st hh level slot hl
    have a100 := (ea.pointer_frame 100 (levelHeaderRealZeroCode_level_frame slot)).trans hl
    obtain ⟨out,eb,bR,bI,bQ,bW,bO,bH⟩ := ih a aH a100
    have ex : MachineEval m g ω (levelHeaderRealZerosCode (slot::rest)) st (10*(slot::rest).length) out := by
      have e := MachineEval.seq ea eb
      convert e using 1 <;> (first | rfl | simp [List.length_cons]; omega)
    refine ⟨out,ex,?_,bI.trans aI,?_,?_,bO.trans aO,bH⟩
    · rw [bR,aR]
      rfl
    · rw [bQ]; exact ea.query_frame (levelHeaderRealZeroCode_queryReadOnly slot)
    · rw [bW,aW]
      simp only [List.length_cons]
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderProjection

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

@[simp] lemma level_header_same_level (level a b : ℕ) :
    levelHeaderAddress level a=levelHeaderAddress level b ↔ a=b := by
  unfold levelHeaderAddress
  omega

@[simp] lemma level_header_update_read {β : Type} (memory : ℤ → β) (level slot other : ℕ) (value : β) :
    Function.update memory (levelHeaderAddress level slot) value (levelHeaderAddress level other)=
      if other=slot then value else memory (levelHeaderAddress level other) := by
  simp [Function.update_apply]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameScalarParameters

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1600000 in
lemma frame_scalar_parameters_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level : ℕ) (N q : ℝ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) (h1 : st.scalar.core.regs 31=1)
    (hN : st.scalar.core.regs 12=N) (hq : st.scalar.core.regs 13=q) :
    ∃ out, MachineEval m g ω frameScalarParametersCode st 20 out ∧
      out.scalar.core.mem=Function.update (Function.update st.scalar.core.mem (levelHeaderAddress level 0) N)
        (levelHeaderAddress level 1) q ∧
      out.scalar.core.mem (levelHeaderAddress level 0)=N ∧ out.scalar.core.mem (levelHeaderAddress level 1)=q ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+20 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,aR,aI,aQ,aW,aO,aH⟩ := level_header_real_from_exec m g ω st hh level 0 12 hl h1
  have a100 := (ea.pointer_frame 100 (by decide)).trans hl
  have a31 := (ea.real_register_frame 31 (by decide)).trans h1
  have a13 := (ea.real_register_frame 13 (by decide)).trans hq
  obtain ⟨out,eb,bR,bI,bQ,bW,bO,bH⟩ := level_header_real_from_exec m g ω a aH level 1 13 a100 a31
  have hMem : out.scalar.core.mem=Function.update (Function.update st.scalar.core.mem (levelHeaderAddress level 0) N)
      (levelHeaderAddress level 1) q := by rw [bR,a13,aR,hN]
  refine ⟨out,MachineEval.seq ea eb,hMem,?_,?_,bI.trans aI,bQ.trans aQ,?_,bO.trans aO,bH⟩
  · rw [hMem]; simp
  · rw [hMem]; simp
  · rw [bW,aW]; norm_num; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshHeaderDefaultsExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1800000 in
lemma fresh_header_defaults_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level : ℕ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω freshHeaderDefaultsCode st 130 out ∧
      out.scalar.integerMemory=levelHeaderIntegerSetsMemory st.scalar.integerMemory level freshHeaderIntegerDefaults ∧
      out.scalar.core.mem=levelHeaderRealZerosMemory st.scalar.core.mem level [3,4,5] ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+130 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,aI,aR,aQ,aW,aO,aH⟩ := level_header_integer_sets_exec m g ω freshHeaderIntegerDefaults st hh level hl
  have a100 := (ea.pointer_frame 100 (by decide)).trans hl
  obtain ⟨out,eb,bR,bI,bQ,bW,bO,bH⟩ := level_header_real_zeros_exec m g ω [3,4,5] a aH level a100
  have ex : MachineEval m g ω freshHeaderDefaultsCode st 130 out := by
    have e := MachineEval.seq ea eb
    convert e using 1 <;> rfl
  refine ⟨out,ex,bI.trans aI,?_,bQ.trans aQ,?_,bO.trans aO,bH⟩
  · rw [bR,aR]
  · rw [bW,aW]
    norm_num [freshHeaderIntegerDefaults]
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderIntegerFrom

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderIntegerFromCode_queryReadOnly (slot source : ℕ) : (levelHeaderIntegerFromCode slot source).allAtoms queryReadOnly := by
  simp [levelHeaderIntegerFromCode,levelHeaderIntegerStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
    linearCode,sequenceCode,coreCode,MachineCode.allAtoms,queryReadOnly]

set_option maxHeartbeats 1400000 in
lemma level_header_integer_from_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level slot source : ℕ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω (levelHeaderIntegerFromCode slot source) st 10 out ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (levelHeaderAddress level slot) (st.scalar.core.ptrs source) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+10 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := payUnit (pointerWrite st 105 (st.scalar.core.ptrs source))
  have ea : MachineEval m g ω (coreCode (.pcopy 105 source)) st 1 a := pcopy_eval m g ω st 105 source hh
  have a100 := (ea.pointer_frame 100 (by simp [coreCode,MachineCode.pointerTargets,pointerTargets])).trans hl
  obtain ⟨out,eb,bI,b40,b41,bR,bW,bO,bH⟩ := level_header_integer_store_exec m g ω a hh level slot a100
  have ex : MachineEval m g ω (levelHeaderIntegerFromCode slot source) st 10 out := MachineEval.seq ea eb
  refine ⟨out,ex,?_,bR,ex.query_frame (levelHeaderIntegerFromCode_queryReadOnly slot source),?_,bO,bH⟩
  · rw [bI]
    simp only [a,payUnit,pcSet,pointerWrite,Function.update_self]
  · rw [bW]
    change st.work+1+9= _
    norm_num
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BlockCandidatePower

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma blockCandidatePowerCode_wellFormed : blockCandidatePowerCode.wellFormed := by
  refine ⟨?_,powerCode_wellFormed⟩
  simp [blockCandidatePrefixCode,linearCode,blockCandidatePrefixInstructions,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma blockCandidatePowerCode_queryReadOnly : blockCandidatePowerCode.allAtoms queryReadOnly := by
  simp [blockCandidatePowerCode,blockCandidatePrefixCode,linearCode,blockCandidatePrefixInstructions,
    sequenceCode,powerCode,powerLoop,powerBody,RealOperation.instruction,MachineCode.allAtoms,queryReadOnly]

set_option maxHeartbeats 1700000 in
lemma block_candidate_prefix_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (r candidate : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (hr : st.scalar.core.ptrs 84=(r : ℤ)) (hc : st.scalar.core.ptrs 85=(candidate : ℤ)) :
    ∃ out, MachineEval m g ω blockCandidatePrefixCode st 6 out ∧
      out.scalar.core.ptrs 1=((r+2 : ℕ) : ℤ) ∧ out.scalar.core.regs 0=((candidate+1 : ℕ) : ℝ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+6 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω blockCandidatePrefixInstructions
    (by simp [blockCandidatePrefixInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,blockCandidatePrefixInstructions,atomState,machineStep,pcSet,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hr,hc] <;> push_cast <;> ring

set_option maxHeartbeats 1000000 in
lemma block_candidate_power_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (r candidate : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (hr : st.scalar.core.ptrs 84=(r : ℤ)) (hc : st.scalar.core.ptrs 85=(candidate : ℤ)) :
    ∃ out, MachineEval m g ω blockCandidatePowerCode st (4*r+17) out ∧
      out.scalar.core.regs 1=((candidate+1 : ℕ) : ℝ)^(r+2) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*r+17 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,ep,hp1,hp0,hpI,hpR,hpW,hpO,hpH⟩ := block_candidate_prefix_exec m g ω r candidate st hh hr hc
  obtain ⟨out,el,ho1,ho0,hoP0,hoP1,hoW,hoO⟩ := power_code_exec m g ω (r+2) ((candidate+1 : ℕ) : ℝ) pre hpH hp1 hp0
  have eRun : MachineEval m g ω blockCandidatePowerCode st (4*r+17) out := by
    have ee := MachineEval.seq ep el
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,ho1,(power_code_integer_memory m g ω el).trans hpI,
    (power_code_real_memory m g ω el).trans hpR,eRun.query_frame blockCandidatePowerCode_queryReadOnly,?_,hoO.trans hpO,
    (eRun.halted blockCandidatePowerCode_wellFormed).trans hh⟩
  · rw [hoW,hpW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BlockCandidateDecision

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma blockCandidateTestCode_queryReadOnly : blockCandidateTestCode.allAtoms queryReadOnly := by
  simp [blockCandidateTestCode,blockCandidateDecisionCode,MachineCode.allAtoms,
    blockCandidatePowerCode_queryReadOnly,coreCode,RealOperation.instruction,queryReadOnly]

set_option maxHeartbeats 1500000 in
lemma block_candidate_decision_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (x y : ℝ) (candidate : ℕ)
    (hx : st.scalar.core.regs 1=x) (hy : st.scalar.core.regs 21=y)
    (hc : st.scalar.core.ptrs 85=(candidate : ℤ)) (hflag : st.scalar.core.regs 24=1) :
    ∃ steps out, MachineEval m g ω blockCandidateDecisionCode st steps out ∧
      steps=(if x ≤ y then 3 else 4) ∧
      out.scalar.core.ptrs 85=(if x ≤ y then ((candidate+1 : ℕ) : ℤ) else (candidate : ℤ)) ∧
      out.scalar.core.regs 24=(if x ≤ y then 1 else 0) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  classical
  let pre := payUnit (realWrite st 22 (x-y))
  have ep : MachineEval m g ω (.atom (RealOperation.sub.instruction 22 1 21)) st 1 pre := by
    simpa only [pre,RealOperation.value,hx,hy] using binary_eval m g ω st .sub 22 1 21 hh
  have hpH : pre.scalar.halted=false := hh
  have hp22 : pre.scalar.core.regs 22=x-y := by simp [pre,payUnit,pcSet,realWrite]
  by_cases hxy : x ≤ y
  · let out := payUnit (pointerWrite (payUnit pre) 85 ((candidate+1 : ℕ) : ℤ))
    have ep85 : (payUnit pre).scalar.core.ptrs 85=(candidate : ℤ) := hc
    have ea : MachineEval m g ω (coreCode (.pinc 85)) (payUnit pre) 1 out := by
      simpa only [out,coreCode,ep85,Nat.cast_add,Nat.cast_one] using pinc_eval m g ω (payUnit pre) 85 hpH
    have eb : MachineEval m g ω (.branchReal 22 (coreCode (.pinc 85)) (coreCode (.const 24 0))) pre 2 out :=
      MachineEval.realNonpos hpH (by rw [hp22]; linarith) ea
    refine ⟨3,out,MachineEval.seq ep eb,by simp [hxy],?_,?_,rfl,rfl,?_,rfl,hh⟩
    · simp [out,payUnit,pcSet,pointerWrite,hxy]
    · simp [out,pre,payUnit,pcSet,pointerWrite,realWrite,hxy,hflag]
    · simp [out,pre,payUnit,pcSet,pointerWrite,realWrite]
      ring
  · let mid := payUnit (realWrite (payUnit pre) 24 0)
    have ea : MachineEval m g ω (coreCode (.const 24 0)) (payUnit pre) 1 mid := const_eval m g ω (payUnit pre) 24 0 hpH
    have eb : MachineEval m g ω (.branchReal 22 (coreCode (.pinc 85)) (coreCode (.const 24 0))) pre 3 (payUnit mid) :=
      MachineEval.realPos hpH (by rw [hp22]; linarith) ea
    refine ⟨4,payUnit mid,MachineEval.seq ep eb,by simp [hxy],?_,?_,rfl,rfl,?_,rfl,hh⟩
    · simpa [mid,pre,payUnit,pcSet,realWrite,hxy] using hc
    · simp [mid,payUnit,pcSet,realWrite,hxy]
    · simp [mid,pre,payUnit,pcSet,realWrite]
      ring

set_option maxHeartbeats 1600000 in
lemma block_candidate_test_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (r candidate : ℕ) (target : ℝ) (st : MachineState) (hh : st.scalar.halted=false)
    (hr : st.scalar.core.ptrs 84=(r : ℤ)) (hc : st.scalar.core.ptrs 85=(candidate : ℤ))
    (ht : st.scalar.core.regs 21=target) (hflag : st.scalar.core.regs 24=1) :
    let accepts := ((candidate+1 : ℕ) : ℝ)^(r+2) ≤ target
    ∃ steps out, MachineEval m g ω blockCandidateTestCode st steps out ∧
      steps=(if accepts then 4*r+20 else 4*r+21) ∧
      out.scalar.core.ptrs 85=(if accepts then ((candidate+1 : ℕ) : ℤ) else (candidate : ℤ)) ∧
      out.scalar.core.regs 24=(if accepts then 1 else 0) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  classical
  dsimp only
  obtain ⟨pre,ep,hp1,hpI,hpR,hpQ,hpW,hpO,hpH⟩ := block_candidate_power_exec m g ω r candidate st hh hr hc
  have hp85 := (ep.pointer_frame 85 (by decide)).trans hc
  have hp21 := (ep.real_register_frame 21 (by decide)).trans ht
  have hp24 := (ep.real_register_frame 24 (by decide)).trans hflag
  obtain ⟨u,out,ed,hu,ho85,ho24,hoI,hoR,hoW,hoO,hoH⟩ := block_candidate_decision_exec m g ω pre hpH
    (((candidate+1 : ℕ) : ℝ)^(r+2)) target candidate hp1 hp21 hp85 hp24
  have eRun := MachineEval.seq ep ed
  refine ⟨4*r+17+u,out,eRun,?_,ho85,ho24,hoI.trans hpI,hoR.trans hpR,
    eRun.query_frame blockCandidateTestCode_queryReadOnly,?_,hoO.trans hpO,hoH⟩
  · rw [hu]; split_ifs <;> omega
  · rw [hoW,hpW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BlockSearchExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1900000 in
lemma block_search_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (r K : ℕ) (target : ℝ)
    (hcond : ∀ c : ℕ, (c : ℝ)^(r+2) ≤ target ↔ c ≤ K)
    (remaining candidate : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (hr : st.scalar.core.ptrs 84=(r : ℤ)) (hc : st.scalar.core.ptrs 85=(candidate : ℤ))
    (ht : st.scalar.core.regs 21=target) (hflag : st.scalar.core.regs 24=1)
    (hlen : candidate+remaining=K) :
    ∃ out, MachineEval m g ω blockSearchLoopCode st (remaining*(4*r+22)+4*r+24) out ∧
      out.scalar.core.ptrs 85=(K : ℤ) ∧ out.scalar.core.regs 24=0 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(remaining*(4*r+22)+4*r+24 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  classical
  induction remaining generalizing candidate st with
  | zero =>
    have hcK : candidate=K := by omega
    have hNo : ¬((candidate+1 : ℕ) : ℝ)^(r+2) ≤ target := by rw [hcond]; omega
    obtain ⟨u,mid,eb,hu,hm85,hm24,hmI,hmR,hmQ,hmW,hmO,hmH⟩ :=
      block_candidate_test_exec m g ω r candidate target (payUnit st) hh hr hc ht hflag
    simp only [if_neg hNo] at hu hm85 hm24
    subst u
    have er : MachineEval m g ω blockSearchLoopCode (payUnit mid) 1 (payUnit (payUnit mid)) :=
      MachineEval.realDone hmH (by simpa only [payUnit_regs,hm24] using (le_refl (0 : ℝ)))
    have eRun : MachineEval m g ω blockSearchLoopCode st (0*(4*r+22)+4*r+24) (payUnit (payUnit mid)) := by
      have ee := MachineEval.realNext hh (by rw [hflag]; norm_num) eb er
      convert ee using 1 <;> (first | rfl | omega)
    refine ⟨payUnit (payUnit mid),eRun,by simpa only [payUnit_ptrs,hcK] using hm85,
      hm24,hmI,hmR,hmQ,?_,hmO,hmH⟩
    · change mid.work+1+1= _
      rw [hmW,payUnit_work]
      push_cast
      ring
  | succ remaining ih =>
    have hYes : ((candidate+1 : ℕ) : ℝ)^(r+2) ≤ target := (hcond _).mpr (by omega)
    obtain ⟨u,mid,eb,hu,hm85,hm24,hmI,hmR,hmQ,hmW,hmO,hmH⟩ :=
      block_candidate_test_exec m g ω r candidate target (payUnit st) hh hr hc ht hflag
    simp only [if_pos hYes] at hu hm85 hm24
    subst u
    have hm84 := (eb.pointer_frame 84 (by decide)).trans hr
    have hm21 := (eb.real_register_frame 21 (by decide)).trans ht
    obtain ⟨out,er,ho85,ho24,hoI,hoR,hoQ,hoW,hoO,hoH⟩ :=
      ih (candidate+1) (payUnit mid) hmH hm84 hm85 hm21 hm24 (by omega)
    have eRun : MachineEval m g ω blockSearchLoopCode st ((remaining+1)*(4*r+22)+4*r+24) out := by
      have ee := MachineEval.realNext hh (by rw [hflag]; norm_num) eb er
      convert ee using 1 <;> (first | rfl | ring)
    refine ⟨out,eRun,ho85,ho24,hoI.trans hmI,hoR.trans hmR,hoQ.trans hmQ,?_,hoO.trans hmO,hoH⟩
    · rw [hoW,payUnit_work,hmW,payUnit_work]
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BlockTargetPreparation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma blockTargetPreparationCode_queryReadOnly : blockTargetPreparationCode.allAtoms queryReadOnly := by
  simp [blockTargetPreparationCode,blockTargetPrefixCode,blockTargetTailCode,linearCode,
    blockTargetPrefixInstructions,blockTargetTailInstructions,sequenceCode,powerCode,powerLoop,powerBody,
    RealOperation.instruction,MachineCode.allAtoms,queryReadOnly]

set_option maxHeartbeats 1600000 in
lemma block_target_prefix_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (r : ℕ) (N : ℝ) (st : MachineState) (hh : st.scalar.halted=false)
    (hr : st.scalar.core.ptrs 84=(r : ℤ)) (hN : st.scalar.core.regs 20=N) :
    ∃ out, MachineEval m g ω blockTargetPrefixCode st 4 out ∧
      out.scalar.core.ptrs 1=((r+1 : ℕ) : ℤ) ∧ out.scalar.core.regs 0=N ∧ out.scalar.core.regs 30=1 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+4 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω blockTargetPrefixInstructions
    (by simp [blockTargetPrefixInstructions,RealOperation.instruction,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,blockTargetPrefixInstructions,RealOperation.instruction,atomState,machineStep,pcSet,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hr,hN]

set_option maxHeartbeats 1600000 in
lemma block_target_tail_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (x : ℝ)
    (hx : st.scalar.core.regs 1=x) (h1 : st.scalar.core.regs 30=1) :
    ∃ out, MachineEval m g ω blockTargetTailCode st 3 out ∧
      out.scalar.core.regs 21=x ∧ out.scalar.core.ptrs 85=0 ∧ out.scalar.core.regs 24=1 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+3 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω blockTargetTailInstructions
    (by simp [blockTargetTailInstructions,RealOperation.instruction,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,blockTargetTailInstructions,RealOperation.instruction,atomState,machineStep,pcSet,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hx,h1]

set_option maxHeartbeats 1300000 in
lemma block_target_preparation_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (r : ℕ) (N : ℝ) (st : MachineState) (hh : st.scalar.halted=false)
    (hr : st.scalar.core.ptrs 84=(r : ℤ)) (hN : st.scalar.core.regs 20=N) :
    ∃ out, MachineEval m g ω blockTargetPreparationCode st (4*r+14) out ∧
      out.scalar.core.regs 21=N^(r+1) ∧ out.scalar.core.ptrs 85=0 ∧ out.scalar.core.regs 24=1 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*r+14 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,ep,hp1,hp0,hp30,hpI,hpR,hpW,hpO,hpH⟩ := block_target_prefix_exec m g ω r N st hh hr hN
  obtain ⟨mid,el,hm1,hm0,hmP0,hmP1,hmW,hmO⟩ := power_code_exec m g ω (r+1) N pre hpH hp1 hp0
  have hmH := (el.halted powerCode_wellFormed).trans hpH
  have hm30 := (el.real_register_frame 30 (by decide)).trans hp30
  obtain ⟨out,et,ho21,ho85,ho24,hoI,hoR,hoW,hoO,hoH⟩ := block_target_tail_exec m g ω mid hmH (N^(r+1)) hm1 hm30
  have eRun : MachineEval m g ω blockTargetPreparationCode st (4*r+14) out := by
    have ee := MachineEval.seq ep (MachineEval.seq el et)
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,ho21,ho85,ho24,hoI.trans ((power_code_integer_memory m g ω el).trans hpI),
    hoR.trans ((power_code_real_memory m g ω el).trans hpR),eRun.query_frame blockTargetPreparationCode_queryReadOnly,
    ?_,hoO.trans (hmO.trans hpO),hoH⟩
  · rw [hoW,hmW,hpW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BalancedBlocks

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma blockSearch_exact (N : ℝ) (r K fuel candidate : ℕ)
    (hcond : ∀ k : ℕ, (k : ℝ)^(r+2) ≤ N^(r+1) ↔ k ≤ K)
    (hc : candidate ≤ K) (hf : K < candidate+fuel) :
    blockSearch N r fuel candidate = K := by
  induction fuel generalizing candidate with
  | zero => omega
  | succ fuel ih =>
    unfold blockSearch
    by_cases he : candidate+1 ≤ K
    · rw [if_pos ((hcond _).mpr he)]
      exact ih (candidate+1) he (by omega)
    · rw [if_neg (fun h => he ((hcond _).mp h))]
      omega

lemma block_power_condition (N : ℝ) (hN : 1 ≤ N) (r k : ℕ) :
    (k : ℝ)^(r+2) ≤ N^(r+1) ↔
      (k : ℝ) ≤ N^((r+1 : ℝ)/(r+2)) := by
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hden : (r+2 : ℝ) ≠ 0 := by positivity
  have hp : (N^((r+1 : ℝ)/(r+2)))^(r+2 : ℕ) = N^(r+1) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN0]
    have he : ((r+1 : ℝ)/(r+2))*((r+2 : ℕ) : ℝ) = (r+1 : ℕ) := by
      push_cast
      field_simp
    rw [he,Real.rpow_natCast]
  rw [←hp]
  exact pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hN0 _) (by omega)

lemma balanced_block_exact (N : ℝ) (hN : 1 ≤ N) (r : ℕ) :
    blockSearch N r (⌈N⌉₊+1) 0 = ⌊N^((r+1 : ℝ)/(r+2))⌋₊ := by
  let x := N^((r+1 : ℝ)/(r+2))
  have hx0 : 0 ≤ x := Real.rpow_nonneg (le_trans zero_le_one hN) _
  have hxN : x ≤ N := Real.rpow_le_self_of_one_le hN ((div_le_one (by positivity)).mpr (by linarith))
  apply blockSearch_exact N r ⌊x⌋₊ _ 0
  · intro k
    rw [block_power_condition N hN r k]
    exact (Nat.le_floor_iff hx0).symm
  · exact Nat.zero_le _
  · have hf : (⌊x⌋₊ : ℝ) ≤ N := (Nat.floor_le hx0).trans hxN
    have hc : N ≤ (⌈N⌉₊ : ℝ) := Nat.le_ceil N
    have : ⌊x⌋₊ ≤ ⌈N⌉₊ := by exact_mod_cast hf.trans hc
    omega

lemma blockScale_balanced (ℓ j : ℕ) (N : ℝ) (hN : 1 ≤ N) :
    blockScale [] ℓ j N = ⌊N^(((ℓ-j : ℕ)+1 : ℝ)/((ℓ-j : ℕ)+2))⌋₊ := by
  unfold blockScale
  simp only [List.getElem?_nil]
  rw [balanced_block_exact N hN]
  have hx : 1 ≤ N^(((ℓ-j : ℕ)+1 : ℝ)/((ℓ-j : ℕ)+2)) :=
    Real.one_le_rpow hN (by positivity)
  have hf : 1 ≤ ⌊N^(((ℓ-j : ℕ)+1 : ℝ)/((ℓ-j : ℕ)+2))⌋₊ := by
    exact (Nat.le_floor_iff (by positivity)).mpr (by simpa using hx)
  exact max_eq_right hf

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BalancedBlockExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2000000 in
lemma balanced_block_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (ℓ j : ℕ) (N : ℝ) (hN : 1 ≤ N) (st : MachineState) (hh : st.scalar.halted=false)
    (hr : st.scalar.core.ptrs 84=((ℓ-j : ℕ) : ℤ)) (hregN : st.scalar.core.regs 20=N) :
    ∃ steps out, MachineEval m g ω balancedBlockCode st steps out ∧
      steps ≤ (⌈N⌉₊+2)*(4*(ℓ-j)+22) ∧
      out.scalar.core.ptrs 85=((blockScale [] ℓ j N : ℕ) : ℤ) ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let r := ℓ-j
  let x := N^((r+1 : ℝ)/(r+2))
  let K := ⌊x⌋₊
  have hx0 : 0 ≤ x := Real.rpow_nonneg (le_trans zero_le_one hN) _
  have hcond : ∀ c : ℕ, (c : ℝ)^(r+2) ≤ N^(r+1) ↔ c ≤ K := by
    intro c
    rw [block_power_condition N hN r c]
    exact (Nat.le_floor_iff hx0).symm
  have hKN : K ≤ ⌈N⌉₊ := by
    have hxN : x ≤ N := Real.rpow_le_self_of_one_le hN ((div_le_one (by positivity)).mpr (by linarith))
    exact_mod_cast (Nat.floor_le hx0).trans (hxN.trans (Nat.le_ceil N))
  obtain ⟨pre,ep,hp21,hp85,hp24,hpI,hpR,hpQ,hpW,hpO,hpH⟩ := block_target_preparation_exec m g ω r N st hh hr hregN
  have hp84 := (ep.pointer_frame 84 (by decide)).trans hr
  obtain ⟨mid,el,hm85,hm24,hmI,hmR,hmQ,hmW,hmO,hmH⟩ := block_search_loop_exec m g ω r K (N^(r+1)) hcond K 0 pre hpH hp84 hp85 hp21 hp24 (by omega)
  let out := payUnit (pointerWrite mid 0 0)
  have ef : MachineEval m g ω (coreCode (.pset 0 0)) mid 1 out := pset_eval m g ω mid 0 0 hmH
  have eRun := MachineEval.seq ep (MachineEval.seq el ef)
  have hKblock : K=blockScale [] ℓ j N := by
    rw [blockScale_balanced ℓ j N hN]
  refine ⟨(4*r+14)+(K*(4*r+22)+4*r+24+1),out,eRun,?_,?_,?_,hmI.trans hpI,hmR.trans hpR,
    hmQ.trans hpQ,?_,hmO.trans hpO,hmH⟩
  · change (4*r+14)+(K*(4*r+22)+4*r+24+1) ≤ (⌈N⌉₊+2)*(4*r+22)
    have hmul := Nat.mul_le_mul_right (4*r+22) hKN
    nlinarith
  · exact (ef.pointer_frame 85 (by decide)).trans (hm85.trans (congrArg (fun a : ℕ => (a : ℤ)) hKblock))
  · simp [out,payUnit,pcSet,pointerWrite]
  · change mid.work+1= _
    rw [hmW,hpW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameBlockCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1600000 in
lemma frame_block_prep_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (ell j : ℕ) (N : ℝ) (hj : j ≤ ell)
    (hDepth : st.scalar.integerMemory 2=((ell+2 : ℕ) : ℤ)) (hLevel : st.scalar.core.ptrs 100=(j : ℤ))
    (hN : st.scalar.core.regs 10=N) (h1 : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω frameBlockPrepCode st 6 out ∧
      out.scalar.core.ptrs 84=((ell-j : ℕ) : ℤ) ∧ out.scalar.core.regs 20=N ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+6 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω frameBlockPrepInstructions
    (by simp [frameBlockPrepInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,frameBlockPrepInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hDepth,hLevel,hN,h1] <;> omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameThresholdRestore

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1600000 in
lemma frame_threshold_restore_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level : ℕ) (q : ℝ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) (hq : st.scalar.core.mem (levelHeaderAddress level 1)=q)
    (h1 : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω frameThresholdRestoreCode st 10 out ∧ out.scalar.core.regs 20=q ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+10 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a10,a40,a41,aI,aR,aW,aO,aH⟩ := level_header_real_load_exec m g ω st hh level 1 hl
  have a31 := (ea.real_register_frame 31 (by decide)).trans h1
  have a10' : a.scalar.core.regs 10=q := a10.trans hq
  let out := payUnit (realWrite a 20 q)
  have eb : MachineEval m g ω (coreCode (.mul 20 10 31)) a 1 out := by
    simpa only [out,coreCode,RealOperation.instruction,RealOperation.value,a10',a31,mul_one] using
      binary_eval m g ω a .mul 20 10 31 aH
  have ex : MachineEval m g ω frameThresholdRestoreCode st 10 out := MachineEval.seq ea eb
  refine ⟨out,ex,by simp [out,payUnit,pcSet,realWrite],aI,aR,ex.query_frame (by decide),?_,aO,aH⟩
  change a.work+1= _
  rw [aW]; norm_num; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameBlockExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2600000 in
lemma frame_block_preparation_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (ell j : ℕ) (N q : ℝ) (hj : j ≤ ell) (hN : 1 ≤ N)
    (hDepth : st.scalar.integerMemory 2=((ell+2 : ℕ) : ℤ)) (hLevel : st.scalar.core.ptrs 100=(j : ℤ))
    (hNMem : st.scalar.core.mem (levelHeaderAddress j 0)=N)
    (hqMem : st.scalar.core.mem (levelHeaderAddress j 1)=q) (h1 : st.scalar.core.regs 31=1) :
    ∃ steps out, MachineEval m g ω frameBlockPreparationCode st steps out ∧
      steps ≤ (⌈N⌉₊+2)*(4*(ell-j)+22)+35 ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (levelHeaderAddress j 14) ((blockScale [] ell j N : ℕ) : ℤ) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.regs 20=q ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a10,a40,a41,aI,aR,aW,aO,aH⟩ := level_header_real_load_exec m g ω st hh j 0 hLevel
  have aDepth : a.scalar.integerMemory 2=((ell+2 : ℕ) : ℤ) := by rw [aI]; exact hDepth
  have a100 := (ea.pointer_frame 100 (by decide)).trans hLevel
  have a31 := (ea.real_register_frame 31 (by decide)).trans h1
  obtain ⟨b,eb,b84,b20,bI,bR,bW,bO,bH⟩ := frame_block_prep_exec m g ω a aH ell j N hj aDepth a100 (a10.trans hNMem) a31
  have b100 := (eb.pointer_frame 100 (by decide)).trans a100
  obtain ⟨u,c,ec,hu,c85,c0,cI,cR,cQ,cW,cO,cH⟩ := balanced_block_exec m g ω ell j N hN b bH b84 b20
  have c100 := (ec.pointer_frame 100 (by decide)).trans b100
  obtain ⟨d,ed,dI,dR,dQ,dW,dO,dH⟩ := level_header_integer_from_exec m g ω c cH j 14 85 c100
  have d100 := (ed.pointer_frame 100 (by decide)).trans c100
  have d31 := (ed.real_register_frame 31 (by decide)).trans ((ec.real_register_frame 31 (by decide)).trans ((eb.real_register_frame 31 (by decide)).trans a31))
  have dMem : d.scalar.core.mem=st.scalar.core.mem := dR.trans (cR.trans (bR.trans aR))
  have dQMem : d.scalar.core.mem (levelHeaderAddress j 1)=q := by rw [dMem]; exact hqMem
  obtain ⟨out,ee,e20,eI,eR,eQ,eW,eO,eH⟩ := frame_threshold_restore_exec m g ω d dH j q d100 dQMem d31
  have ex := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed ee)))
  refine ⟨9+(6+(u+(10+10))),out,ex,by omega,?_,eR.trans dMem,e20,?_,?_,?_,eO.trans (dO.trans (cO.trans (bO.trans aO))),eH⟩
  · rw [eI,dI,c85,cI,bI,aI]
  · exact (ee.pointer_frame 0 (by decide)).trans ((ed.pointer_frame 0 (by decide)).trans c0)
  · rw [eQ,dQ,cQ]
    rw [eb.query_frame (by decide),ea.query_frame (by decide)]
  · rw [eW,dW,cW,bW,aW]; push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.GraphRecordAddress

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation


lemma vertexRecordAddress_negative (width vertex offset : ℕ) :
    vertexRecordAddress width vertex offset < 0 := by
  unfold vertexRecordAddress
  omega

lemma vertexRecordAddress_injective (width v v' i i' : ℕ)
    (hi : i < width) (hi' : i' < width)
    (he : vertexRecordAddress width v i=vertexRecordAddress width v' i') :
    v=v' ∧ i=i' := by
  have henc : v*width+i=v'*width+i' := by unfold vertexRecordAddress at he; omega
  have hquot := congrArg (fun z => z / width) henc
  have hrem := congrArg (fun z => z % width) henc
  have hw : 0 < width := by omega
  simp [Nat.add_div,hw,hi,hi',Nat.div_eq_of_lt hi,Nat.div_eq_of_lt hi'] at hquot
  simp [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hi',Nat.not_le_of_lt hi,Nat.not_le_of_lt hi'] at hquot
  simp [Nat.add_mod,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hi'] at hrem
  exact ⟨hquot,hrem⟩

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshAllocation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma reserveArrayCode_wellFormed : reserveArrayCode.wellFormed := by
  simp [reserveArrayCode,coreCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

lemma reserve_array_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (free : ℤ) (length : ℕ)
    (hf : st.scalar.core.ptrs 20=free) (hL : st.scalar.core.ptrs 18=(length : ℤ)) :
    ∃ out, MachineEval m g ω reserveArrayCode st 2 out ∧
      out.scalar.core.ptrs 13=free ∧ out.scalar.core.ptrs 20=free+(length : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+2 ∧ out.output=st.output := by
  let A := payUnit (pointerWrite st 13 free)
  let out := payUnit (pointerWrite A 20 (free+(length : ℤ)))
  have ea : MachineEval m g ω (coreCode (.pcopy 13 20)) st 1 A := by
    simpa only [coreCode,A,hf] using pcopy_eval m g ω st 13 20 hh
  have ah : A.scalar.halted=false := by simp [A,payUnit,pcSet,pointerWrite,hh]
  have eb : MachineEval m g ω (.atom (.scalar (.pointerAdd 20 20 18))) A 1 out := by
    have a20 : A.scalar.core.ptrs 20=free := by simp [A,payUnit,pcSet,pointerWrite,hf]
    have a18 : A.scalar.core.ptrs 18=(length : ℤ) := by simp [A,payUnit,pcSet,pointerWrite,hL]
    simpa only [out,a20,a18] using pointerAdd_eval m g ω A 20 20 18 ah
  refine ⟨out,MachineEval.seq ea eb,?_,?_,?_,?_,?_,?_⟩
  all_goals simp [out,A,payUnit,pcSet,pointerWrite] <;> ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RankArrayInitialize

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma rankZeroBodyCode_queryReadOnly : rankZeroBodyCode.allAtoms queryReadOnly := by
  simp [rankZeroBodyCode,linearCode,rankZeroInstructions,sequenceCode,MachineCode.allAtoms,queryReadOnly]

lemma rank_zero_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (hz : st.scalar.core.ptrs 0=0) :
    ∃ out, MachineEval m g ω rankZeroBodyCode st 3 out ∧
      out.scalar.core.ptrs 17=st.scalar.core.ptrs 17+1 ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (st.scalar.core.ptrs 13+st.scalar.core.ptrs 17) 0 ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+3 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let out := linearRun m g ω rankZeroInstructions st
  obtain ⟨e,hw,hH⟩ := linear_execute m g ω rankZeroInstructions
    (by simp [rankZeroInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨out,e,?_,?_,?_,e.query_frame rankZeroBodyCode_queryReadOnly,hw,?_,hH⟩
  all_goals simp [out,linearRun,rankZeroInstructions,atomState,machineStep,pcSet,hh,hz,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep]

set_option maxHeartbeats 1600000 in
lemma rank_zero_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (base : ℤ) (length remaining i : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (hz : st.scalar.core.ptrs 0=0) (hb : st.scalar.core.ptrs 13=base)
    (hl : st.scalar.core.ptrs 18=(length : ℤ)) (hi : st.scalar.core.ptrs 17=(i : ℤ))
    (hlen : i+remaining=length) (hzero : ∀ j < i, st.scalar.integerMemory (base+(j : ℤ))=0) :
    ∃ out, MachineEval m g ω rankZeroLoopCode st (5*remaining+1) out ∧
      (∀ j < length, out.scalar.integerMemory (base+(j : ℤ))=0) ∧
      (∀ z, z ∉ arrayCells base length → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(5*remaining+1 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction remaining generalizing st i with
  | zero =>
    have he : i=length := by omega
    refine ⟨payUnit st,?_,?_,(by intros; rfl),rfl,rfl,by simp,rfl,hh⟩
    · exact MachineEval.pointerDone (r:=18) (s:=17) (body:=rankZeroBodyCode) hh (by rw [hl,hi,he])
    · simpa only [he,payUnit,pcSet] using hzero
  | succ remaining ih =>
    have hil : i < length := by omega
    obtain ⟨mid,eb,hm17,hmI,hmR,hmQ,hmW,hmO,hmH⟩ := rank_zero_body_exec m g ω (payUnit st) hh hz
    have hm0 := (eb.pointer_frame 0 (by decide)).trans hz
    have hm13 := (eb.pointer_frame 13 (by decide)).trans hb
    have hm18 := (eb.pointer_frame 18 (by decide)).trans hl
    have hm17' : mid.scalar.core.ptrs 17=(i+1 : ℕ) := by simpa only [payUnit,pcSet,hi,Nat.cast_add,Nat.cast_one] using hm17
    change mid.scalar.integerMemory=Function.update st.scalar.integerMemory
      (st.scalar.core.ptrs 13+st.scalar.core.ptrs 17) 0 at hmI
    rw [hb,hi] at hmI
    have hmZero : ∀ j < i+1, mid.scalar.integerMemory (base+(j : ℤ))=0 := by
      intro j hj
      rw [hmI]
      by_cases he : j=i
      · subst j; simp
      · rw [Function.update_of_ne (by omega : base+(j : ℤ) ≠ base+(i : ℤ))]
        exact hzero j (by omega)
    obtain ⟨out,er,hoZero,hoFrame,hoR,hoQ,hoW,hoO,hoH⟩ :=
      ih (i+1) (payUnit mid) hmH hm0 hm13 hm18 hm17' (by omega) hmZero
    refine ⟨out,?_,hoZero,?_,hoR.trans hmR,hoQ.trans hmQ,?_,hoO.trans hmO,hoH⟩
    · have eRun := MachineEval.pointerNext (r:=18) (s:=17) hh (by rw [hl,hi]; omega) eb er
      convert eRun using 1 <;> (first | rfl | omega)
    · intro z hz'
      have hn : z ≠ base+(i : ℤ) := by
        intro he; apply hz'; exact (mem_arrayCells _ _ _).mpr ⟨i,hil,he⟩
      have hmFrame : mid.scalar.integerMemory z=st.scalar.integerMemory z := by rw [hmI,Function.update_of_ne hn]
      exact (hoFrame z hz').trans hmFrame
    · rw [hoW,payUnit_work,hmW,payUnit_work]
      push_cast
      ring

set_option maxHeartbeats 1000000 in
lemma rank_array_initialize_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (base : ℤ) (length : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (hp : 2 ≤ base) (hb : st.scalar.core.ptrs 13=base) (hl : st.scalar.core.ptrs 18=(length : ℤ)) :
    ∃ out, MachineEval m g ω rankArrayInitializeCode st (5*length+3) out ∧
      RankArrayRep out.scalar.integerMemory base length (fun _ => none) (fun _ => 0) (fun _ => ∅) ∧
      (∀ z, z ∉ arrayCells base length → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(5*length+3 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let A := payUnit (pointerWrite st 0 0)
  let B := payUnit (pointerWrite A 17 0)
  have ea := pset_eval m g ω st 0 0 hh
  have ah : A.scalar.halted=false := hh
  have eb : MachineEval m g ω (coreCode (.pset 17 0)) A 1 B := pset_eval m g ω A 17 0 ah
  have bh : B.scalar.halted=false := hh
  have b0 : B.scalar.core.ptrs 0=0 := by simp [B,A,payUnit,pcSet,pointerWrite]
  have b13 : B.scalar.core.ptrs 13=base := by simpa [B,A,payUnit,pcSet,pointerWrite] using hb
  have b18 : B.scalar.core.ptrs 18=(length : ℤ) := by simpa [B,A,payUnit,pcSet,pointerWrite] using hl
  have b17 : B.scalar.core.ptrs 17=0 := by simp [B,payUnit,pcSet,pointerWrite]
  obtain ⟨out,el,hoZero,hoFrame,hoR,hoQ,hoW,hoO,hoH⟩ :=
    rank_zero_loop_exec m g ω base length length 0 B bh b0 b13 b18 b17 (by omega) (by intro j hj; omega)
  refine ⟨out,?_,RankArrayRep.empty _ _ _ hp hoZero,hoFrame,hoR,hoQ,?_,hoO,hoH⟩
  · have ee := MachineEval.seq ea (MachineEval.seq eb el)
    convert ee using 1 <;> (first | rfl | omega)
  · rw [hoW]
    change st.work+1+1+(5*length+1 : ℕ)= _
    push_cast
    ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RankQueueAllocation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma rank_array_initialize_zero {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {st out : MachineState} {u : ℕ} (hh : st.scalar.halted=false)
    (e : MachineEval m g ω rankArrayInitializeCode st u out) : out.scalar.core.ptrs 0=0 := by
  change MachineEval m g ω (.seq (coreCode (.pset 0 0)) _) st u out at e
  cases e with
  | seq ea er =>
    cases ea with
    | atom i st hready =>
      have hm : (pcSet (atomState m g ω (.scalar (.core (.pset 0 0))) st) 0).scalar.core.ptrs 0=0 := by
        rw [pset_atomState m g ω st 0 0 hh]
        simp [pcSet,payUnit,pointerWrite]
      exact (er.pointer_frame 0 (by decide)).trans hm

set_option maxHeartbeats 1000000 in
lemma rank_queue_allocation_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (free : ℤ) (length : ℕ)
    (hp : 2 ≤ free) (hf : st.scalar.core.ptrs 20=free) (hl : st.scalar.core.ptrs 18=(length : ℤ)) :
    ∃ out, MachineEval m g ω rankQueueAllocationCode st (5*length+5) out ∧
      out.scalar.core.ptrs 13=free ∧ out.scalar.core.ptrs 20=free+(length : ℤ) ∧ out.scalar.core.ptrs 0=0 ∧
      RankArrayRep out.scalar.integerMemory free length (fun _ => none) (fun _ => 0) (fun _ => ∅) ∧
      (∀ z, z ∉ arrayCells free length → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(5*length+5 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,ep,hp13,hp20,hpI,hpR,hpW,hpO⟩ := reserve_array_exec m g ω st hh free length hf hl
  have hpH : pre.scalar.halted=false := (ep.halted reserveArrayCode_wellFormed).trans hh
  have hp18 := (ep.pointer_frame 18 (by decide)).trans hl
  obtain ⟨out,ei,hoRep,hoFrame,hoR,hoQ,hoW,hoO,hoH⟩ := rank_array_initialize_exec m g ω free length pre hpH hp hp13 hp18
  have eRun : MachineEval m g ω rankQueueAllocationCode st (5*length+5) out := by
    have ee := MachineEval.seq ep ei
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,(ei.pointer_frame 13 (by decide)).trans hp13,(ei.pointer_frame 20 (by decide)).trans hp20,
    rank_array_initialize_zero hpH ei,hoRep,?_,hoR.trans hpR,?_,?_,hoO.trans hpO,hoH⟩
  · intro z hz
    exact (hoFrame z hz).trans (congrFun hpI z)
  · apply eRun.query_frame
    simp [rankQueueAllocationCode,reserveArrayCode,rankArrayInitializeCode,rankZeroLoopCode,
      MachineCode.allAtoms,rankZeroBodyCode_queryReadOnly,coreCode,queryReadOnly]
  · rw [hoW,hpW]
    push_cast
    ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeaderQueueAllocation

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 2400000 in
lemma header_queue_allocation_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (count level slot length : ℕ) (free : ℤ)
    (hc : level < count) (hs : slot < 32) (hfree : 128+32*(count : ℤ) ≤ free)
    (hf : st.scalar.core.ptrs 20=free) (hl : st.scalar.core.ptrs 100=(level : ℤ))
    (hlen : st.scalar.core.ptrs 18=(length : ℤ)) :
    ∃ out, MachineEval m g ω (headerQueueAllocationCode slot) st (5*length+15) out ∧
      out.scalar.core.ptrs 13=free ∧ out.scalar.core.ptrs 20=free+(length : ℤ) ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.integerMemory (levelHeaderAddress level slot)=free ∧
      RankArrayRep out.scalar.integerMemory free length (fun _ => none) (fun _ => 0) (fun _ => ∅) ∧
      (∀ z, z ∉ arrayCells free length → z ≠ levelHeaderAddress level slot → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(5*length+15 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  have hp : 2 ≤ free := by have hn : 0 ≤ (count : ℤ) := Int.natCast_nonneg count; omega
  obtain ⟨a,ea,a13,a20,a0,aRep,aFrame,aR,aQ,aW,aO,aH⟩ := rank_queue_allocation_exec m g ω st hh free length hp hf hlen
  have a100 := (ea.pointer_frame 100 (by decide)).trans hl
  obtain ⟨out,eb,bI,bR,bQ,bW,bO,bH⟩ := level_header_integer_from_exec m g ω a aH level slot 13 a100
  have hb : levelHeaderAddress level slot < free := by unfold levelHeaderAddress; omega
  have rep : RankArrayRep out.scalar.integerMemory free length (fun _ => none) (fun _ => 0) (fun _ => ∅) := by
    apply aRep.frame
    intro z hz
    have hm : z ∈ arrayCells free length := by simpa [queueCells] using hz
    obtain ⟨i,hi,he⟩ := (mem_arrayCells free z length).mp hm
    rw [bI]
    simp only [Function.update_of_ne (by omega : z ≠ levelHeaderAddress level slot)]
  have ex : MachineEval m g ω (headerQueueAllocationCode slot) st (5*length+15) out := by
    have e := MachineEval.seq ea eb
    convert e using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,?_,?_,?_,?_,rep,?_,bR.trans aR,bQ.trans aQ,?_,bO.trans aO,bH⟩
  · exact (eb.pointer_frame 13 (by simp [levelHeaderIntegerFromCode,levelHeaderIntegerStoreCode,
      levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets])).trans a13
  · exact (eb.pointer_frame 20 (by simp [levelHeaderIntegerFromCode,levelHeaderIntegerStoreCode,
      levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets])).trans a20
  · exact (eb.pointer_frame 0 (by simp [levelHeaderIntegerFromCode,levelHeaderIntegerStoreCode,
      levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets])).trans a0
  · rw [bI]; simp [a13]
  · intro z hz hn
    rw [bI,Function.update_of_ne hn]
    exact aFrame z hz
  · rw [bW,aW]; push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshQueuePair

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 2600000 in
lemma fresh_queue_pair_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (count level length : ℕ) (free : ℤ)
    (hc : level < count) (hfree : 128+32*(count : ℤ) ≤ free)
    (hf : st.scalar.core.ptrs 20=free) (hl : st.scalar.core.ptrs 100=(level : ℤ))
    (hlen : st.scalar.core.ptrs 18=(length : ℤ)) :
    ∃ out, MachineEval m g ω freshQueuePairCode st (10*length+30) out ∧
      out.scalar.core.ptrs 20=free+2*(length : ℤ) ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.integerMemory (levelHeaderAddress level 7)=free ∧
      out.scalar.integerMemory (levelHeaderAddress level 8)=free+(length : ℤ) ∧
      RankArrayRep out.scalar.integerMemory free length (fun _ => none) (fun _ => 0) (fun _ => ∅) ∧
      RankArrayRep out.scalar.integerMemory (free+(length : ℤ)) length (fun _ => none) (fun _ => 0) (fun _ => ∅) ∧
      (∀ z, z ∉ arrayCells free length → z ∉ arrayCells (free+(length : ℤ)) length →
        z ≠ levelHeaderAddress level 7 → z ≠ levelHeaderAddress level 8 → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(10*length+30 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a13,a20,a0,a7,aRep,aFrame,aR,aQ,aW,aO,aH⟩ := header_queue_allocation_exec m g ω st hh count level 7 length free hc (by decide) hfree hf hl hlen
  have a100 := (ea.pointer_frame 100 (by decide)).trans hl
  have a18 := (ea.pointer_frame 18 (by decide)).trans hlen
  have hfree' : 128+32*(count : ℤ) ≤ free+(length : ℤ) := by have := Int.natCast_nonneg length; omega
  obtain ⟨out,eb,b13,b20,b0,b8,bRep,bFrame,bR,bQ,bW,bO,bH⟩ := header_queue_allocation_exec m g ω a aH count level 8 length (free+(length : ℤ)) hc (by decide) hfree' a20 a100 a18
  have h7Bound : levelHeaderAddress level 7 < free := by unfold levelHeaderAddress; omega
  have h8Bound : levelHeaderAddress level 8 < free := by unfold levelHeaderAddress; omega
  have rep1 : RankArrayRep out.scalar.integerMemory free length (fun _ => none) (fun _ => 0) (fun _ => ∅) := by
    apply aRep.frame
    intro z hz
    have hm : z ∈ arrayCells free length := by simpa [queueCells] using hz
    obtain ⟨i,hi,he⟩ := (mem_arrayCells free z length).mp hm
    apply bFrame z
    · intro hz'
      obtain ⟨j,hj,he'⟩ := (mem_arrayCells (free+(length : ℤ)) z length).mp hz'
      omega
    · have hi0 := Int.natCast_nonneg i
      omega
  have h7 : out.scalar.integerMemory (levelHeaderAddress level 7)=free := by
    rw [bFrame _ ?_ (by simp)]
    · exact a7
    · intro hm
      obtain ⟨i,hi,he⟩ := (mem_arrayCells (free+(length : ℤ)) (levelHeaderAddress level 7) length).mp hm
      have hi0 := Int.natCast_nonneg i
      have hl0 := Int.natCast_nonneg length
      omega
  have ex : MachineEval m g ω freshQueuePairCode st (10*length+30) out := by
    have e := MachineEval.seq ea eb
    convert e using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,?_,b0,h7,b8,rep1,bRep,?_,bR.trans aR,bQ.trans aQ,?_,bO.trans aO,bH⟩
  · rw [b20]; ring
  · intro z hA hB h7 h8
    exact (bFrame z hB h8).trans (aFrame z hA h7)
  · rw [bW,aW]; push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelContextPreparation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1800000 in
lemma level_context_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level width : ℕ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) (hw : st.scalar.core.ptrs 50=(width : ℤ)) :
    ∃ out, MachineEval m g ω levelContextCode st 8 out ∧
      out.scalar.core.ptrs 87=((16*(level+1) : ℕ) : ℤ) ∧
      out.scalar.core.ptrs 89=((16*(level+1) : ℕ) : ℤ) ∧ out.scalar.core.ptrs 41=(width : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+8 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω levelContextInstructions
    (by simp [levelContextInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,?_,ex.query_frame (by decide),hW,?_,hH⟩
  all_goals simp [linearRun,levelContextInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hl,hw] <;> omega

lemma frame_rank_load_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (length : ℕ)
    (hLength : st.scalar.integerMemory 5=(length : ℤ)) :
    ∃ out, MachineEval m g ω frameRankLoadCode st 3 out ∧
      out.scalar.core.ptrs 18=(length : ℤ) ∧ out.scalar.core.ptrs 25=(length : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+3 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω frameRankLoadInstructions
    (by simp [frameRankLoadInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,ex.query_frame (by decide),hW,?_,hH⟩
  all_goals simp [linearRun,frameRankLoadInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hLength]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeaderMemoryFrames

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma header_integer_sets_frame (I : ℤ → ℤ) (level : ℕ) (assignments : List (ℕ × ℤ)) (z : ℤ)
    (hz : ∀ kv ∈ assignments, z ≠ levelHeaderAddress level kv.1) :
    levelHeaderIntegerSetsMemory I level assignments z=I z := by
  induction assignments generalizing I with
  | nil => rfl
  | cons kv rest ih =>
    change levelHeaderIntegerSetsMemory (Function.update I (levelHeaderAddress level kv.1) kv.2) level rest z=I z
    rw [ih _ (fun v hv => hz v (by simp [hv]))]
    simp only [Function.update_of_ne (hz kv (by simp))]

lemma header_integer_sets_low (I : ℤ → ℤ) (level : ℕ) (assignments : List (ℕ × ℤ)) (z : ℤ) (hz : z < 128) :
    levelHeaderIntegerSetsMemory I level assignments z=I z := by
  apply header_integer_sets_frame
  intro kv hk
  have hp := levelHeaderAddress_positive level kv.1
  omega

lemma header_real_zeros_frame (R : ℤ → ℝ) (level : ℕ) (slots : List ℕ) (z : ℤ)
    (hz : ∀ slot ∈ slots, z ≠ levelHeaderAddress level slot) :
    levelHeaderRealZerosMemory R level slots z=R z := by
  induction slots generalizing R with
  | nil => rfl
  | cons slot rest ih =>
    change levelHeaderRealZerosMemory (Function.update R (levelHeaderAddress level slot) 0) level rest z=R z
    rw [ih _ (fun k hk => hz k (by simp [hk]))]
    simp only [Function.update_of_ne (hz slot (by simp))]

lemma header_real_zeros_low (R : ℤ → ℝ) (level : ℕ) (slots : List ℕ) (z : ℤ) (hz : z < 128) :
    levelHeaderRealZerosMemory R level slots z=R z := by
  apply header_real_zeros_frame
  intro slot hk
  have hp := levelHeaderAddress_positive level slot
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshHeaderCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def freshHeaderSlots : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,14]
def freshHeaderIntegerValue (free : ℤ) (length block slot : ℕ) : ℤ :=
  if slot=7 then free else if slot=8 then free+(length : ℤ) else
    if slot=14 then (block : ℤ) else if slot=10 then 1 else 0

def FreshHeaderScalars (R : ℤ → ℝ) (level : ℕ) (N q : ℝ) : Prop :=
  R (levelHeaderAddress level 0)=N ∧ R (levelHeaderAddress level 1)=q ∧
    R (levelHeaderAddress level 3)=0 ∧ R (levelHeaderAddress level 4)=0 ∧ R (levelHeaderAddress level 5)=0

structure FreshHeaderMemory (I : ℤ → ℤ) (R : ℤ → ℝ) (level length block : ℕ) (N q : ℝ) (free : ℤ) : Prop where
  integers : ∀ slot ∈ freshHeaderSlots, I (levelHeaderAddress level slot)=freshHeaderIntegerValue free length block slot
  scalars : FreshHeaderScalars R level N q
  exterior : RankArrayRep I free length (fun _ => none) (fun _ => 0) (fun _ => ∅)
  high : RankArrayRep I (free+(length : ℤ)) length (fun _ => none) (fun _ => 0) (fun _ => ∅)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ScalarPointerDecrement

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pdec_atomState (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r : ℕ) (hh : st.scalar.halted=false) :
    atomState m g ω (.scalar (.core (.pdec r))) st=
      pcSet (payUnit (pointerWrite st r (st.scalar.core.ptrs r-1))) 1 := by
  simp [atomState,machineStep,pcSet,payUnit,pointerWrite,hh,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep]

lemma pdec_eval (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r : ℕ) (hh : st.scalar.halted=false) :
    MachineEval m g ω (.atom (.scalar (.core (.pdec r)))) st 1
      (payUnit (pointerWrite st r (st.scalar.core.ptrs r-1))) := by
  have e := MachineEval.atom (m:=m) (g:=g) (ω:=ω) (.scalar (.core (.pdec r))) st
    (by rw [pdec_atomState m g ω st r hh]; rfl)
  simpa only [pdec_atomState m g ω st r hh,pcSet_set,pcSet_payUnit_zero] using e

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexAddressExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pointerSub_atomState (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r a b : ℕ) (hh : st.scalar.halted=false) :
    atomState m g ω (.scalar (.pointerSub r a b)) st=
      pcSet (payUnit (pointerWrite st r (st.scalar.core.ptrs a-st.scalar.core.ptrs b))) 1 := by
  simp [atomState,machineStep,pcSet,payUnit,pointerWrite,hh,LocalPush.step,scalarProgram]

lemma pointerSub_eval (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (r a b : ℕ) (hh : st.scalar.halted=false) :
    MachineEval m g ω (.atom (.scalar (.pointerSub r a b))) st 1
      (payUnit (pointerWrite st r (st.scalar.core.ptrs a-st.scalar.core.ptrs b))) := by
  have e := MachineEval.atom (m:=m) (g:=g) (ω:=ω) (.scalar (.pointerSub r a b)) st
    (by rw [pointerSub_atomState m g ω st r a b hh]; rfl)
  simpa only [pointerSub_atomState m g ω st r a b hh,pcSet_set,pcSet_payUnit_zero] using e


lemma vertex_address_tail_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (hz : st.scalar.core.ptrs 0=0) :
    ∃ out, MachineEval m g ω vertexAddressTailCode st 3 out ∧
      out.scalar.core.ptrs 45= -1-(st.scalar.core.ptrs 42+st.scalar.core.ptrs 44) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+3 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let p := st.scalar.core.ptrs 42+st.scalar.core.ptrs 44
  let A := payUnit (pointerWrite st 45 p)
  let B := payUnit (pointerWrite A 45 (-p))
  let out := payUnit (pointerWrite B 45 (-p-1))
  have ah : A.scalar.halted=false := hh
  have bh : B.scalar.halted=false := hh
  have ea := pointerAdd_eval m g ω st 45 42 44 hh
  have eb : MachineEval m g ω (.atom (.scalar (.pointerSub 45 0 45))) A 1 B := by
    have ha0 : A.scalar.core.ptrs 0=0 := by simpa [A,payUnit,pcSet,pointerWrite] using hz
    have ha45 : A.scalar.core.ptrs 45=p := by simp [A,payUnit,pcSet,pointerWrite]
    simpa only [B,ha0,ha45,zero_sub] using pointerSub_eval m g ω A 45 0 45 ah
  have eo : MachineEval m g ω (coreCode (.pdec 45)) B 1 out := by
    have hb45 : B.scalar.core.ptrs 45= -p := by simp [B,payUnit,pcSet,pointerWrite]
    simpa only [out,coreCode,hb45] using pdec_eval m g ω B 45 bh
  refine ⟨out,MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq eo (MachineEval.skip out))),?_,rfl,rfl,?_,rfl,hh⟩
  all_goals simp [out,B,A,p,payUnit,pcSet,pointerWrite] <;> ring

set_option maxHeartbeats 1000000 in
lemma vertex_address_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex offset : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hi : st.scalar.core.ptrs 44=(offset : ℤ)) :
    ∃ out, MachineEval m g ω vertexAddressCode st (4*width+6) out ∧
      out.scalar.core.ptrs 45=vertexRecordAddress width vertex offset ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+(4*width+6 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨mid,em,h40,h41,h43,h42,hI,hR,hW,hO,hH⟩ := integer_scale_exec m g ω vertex width st hh hv hw
  have hm0 : mid.scalar.core.ptrs 0=0 := (em.pointer_frame 0 (by decide)).trans hz
  have hm44 : mid.scalar.core.ptrs 44=(offset : ℤ) := (em.pointer_frame 44 (by decide)).trans hi
  obtain ⟨out,eo,haddr,hoI,hoR,hoW,hoO,hoH⟩ := vertex_address_tail_exec m g ω mid hH hm0
  refine ⟨out,?_,?_,hoI.trans hI,hoR.trans hR,?_,hoO.trans hO,hoH⟩
  · have e := MachineEval.seq em eo
    convert e using 1 <;> (first | rfl | omega)
  · rw [haddr,h42,hm44]
    simp [vertexRecordAddress]
  · rw [hoW,hW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexRecordAccess

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexAddressCode_registerReadOnly : vertexAddressCode.allAtoms registerReadOnly := by
  simp [vertexAddressCode,vertexAddressTailCode,integerScaleCode,integerScaleLoopCode,integerScaleBodyCode,
    integerScaleBodyRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    sequenceCode,coreCode,MachineCode.allAtoms,registerReadOnly]

set_option maxHeartbeats 800000 in
lemma vertex_real_load_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex offset : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hi : st.scalar.core.ptrs 44=(offset : ℤ)) :
    ∃ out, MachineEval m g ω vertexRealLoadCode st (4*width+7) out ∧
      out.scalar.core.regs 10=st.scalar.core.mem (vertexRecordAddress width vertex offset) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+(4*width+7 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨mid,ea,haddr,hI,hR,hW,hO,hH⟩ := vertex_address_exec m g ω st hh width vertex offset hz hv hw hi
  let out := payUnit (realWrite mid 10 (st.scalar.core.mem (vertexRecordAddress width vertex offset)))
  have eb : MachineEval m g ω (coreCode (.load 10 45)) mid 1 out := by
    simpa only [out,coreCode,haddr,hR] using load_eval m g ω mid 10 45 hH
  refine ⟨out,?_,by simp [out,payUnit,pcSet,realWrite],hI,hR,?_,hO,hH⟩
  · have e := MachineEval.seq ea eb
    convert e using 1 <;> (first | rfl | omega)
  · change mid.work+1= _
    rw [hW]
    push_cast
    ring

set_option maxHeartbeats 800000 in
lemma vertex_real_store_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex offset : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hi : st.scalar.core.ptrs 44=(offset : ℤ)) :
    ∃ out, MachineEval m g ω vertexRealStoreCode st (4*width+7) out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width vertex offset) (st.scalar.core.regs 10) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.regs=st.scalar.core.regs ∧
      out.work=st.work+(4*width+7 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨mid,ea,haddr,hI,hR,hW,hO,hH⟩ := vertex_address_exec m g ω st hh width vertex offset hz hv hw hi
  have hRegs := ea.register_frame vertexAddressCode_registerReadOnly
  let out := payUnit (memoryWrite mid (vertexRecordAddress width vertex offset) (st.scalar.core.regs 10))
  have eb : MachineEval m g ω (coreCode (.store 45 10)) mid 1 out := by
    simpa only [out,coreCode,haddr,hRegs] using store_eval m g ω mid 45 10 hH
  refine ⟨out,?_,?_,hI,hRegs,?_,hO,hH⟩
  · have e := MachineEval.seq ea eb
    convert e using 1 <;> (first | rfl | omega)
  · change Function.update mid.scalar.core.mem _ _= _
    rw [hR]
  · change mid.work+1= _
    rw [hW]
    push_cast
    ring

set_option maxHeartbeats 800000 in
lemma vertex_integer_load_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex offset : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hi : st.scalar.core.ptrs 44=(offset : ℤ)) :
    ∃ out, MachineEval m g ω vertexIntegerLoadCode st (4*width+7) out ∧
      out.scalar.core.ptrs 51=st.scalar.integerMemory (vertexRecordAddress width vertex offset) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+(4*width+7 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨mid,ea,haddr,hI,hR,hW,hO,hH⟩ := vertex_address_exec m g ω st hh width vertex offset hz hv hw hi
  let out := payUnit (pointerWrite mid 51 (st.scalar.integerMemory (vertexRecordAddress width vertex offset)))
  have eb : MachineEval m g ω (.atom (.scalar (.integerLoad 51 45))) mid 1 out := by
    simpa only [out,haddr,hI] using integerLoad_eval m g ω mid 51 45 hH
  refine ⟨out,?_,by simp [out,payUnit,pcSet,pointerWrite],hI,hR,?_,hO,hH⟩
  · have e := MachineEval.seq ea eb
    convert e using 1 <;> (first | rfl | omega)
  · change mid.work+1= _
    rw [hW]
    push_cast
    ring

set_option maxHeartbeats 800000 in
lemma vertex_integer_store_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex offset : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hi : st.scalar.core.ptrs 44=(offset : ℤ)) :
    ∃ out, MachineEval m g ω vertexIntegerStoreCode st (4*width+7) out ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (vertexRecordAddress width vertex offset) (st.scalar.core.ptrs 51) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+(4*width+7 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨mid,ea,haddr,hI,hR,hW,hO,hH⟩ := vertex_address_exec m g ω st hh width vertex offset hz hv hw hi
  have h51 := ea.pointer_frame 51 (by decide)
  let out := payUnit (integerWrite mid (vertexRecordAddress width vertex offset) (st.scalar.core.ptrs 51))
  have eb : MachineEval m g ω (.atom (.scalar (.integerStore 45 51))) mid 1 out := by
    simpa only [out,haddr,h51] using integerStore_eval m g ω mid 45 51 hH
  refine ⟨out,?_,?_,hR,?_,hO,hH⟩
  · have e := MachineEval.seq ea eb
    convert e using 1 <;> (first | rfl | omega)
  · change Function.update mid.scalar.integerMemory _ _= _
    rw [hI]
  · change mid.work+1= _
    rw [hW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexFieldWrite

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexAddressCode_queryReadOnly : vertexAddressCode.allAtoms queryReadOnly := by
  simp [vertexAddressCode,vertexAddressTailCode,integerScaleCode,integerScaleLoopCode,integerScaleBodyCode,
    integerScaleBodyRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    sequenceCode,coreCode,MachineCode.allAtoms,queryReadOnly]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.GraphCacheFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma GraphCache.frame {n : ℕ} (g : InputGraph n) (I J : ℤ → ℤ) (width : ℕ)
    (stored : Finset (Fin n)) (free : ℤ) (h : GraphCache g I width stored free)
    (hfields : ∀ v : Fin n, ∀ field < 3,
      J (vertexRecordAddress width v.val field)=I (vertexRecordAddress width v.val field))
    (hadj : ∀ v ∈ stored, ∀ i < (g.neighbors v).length,
      J (I (vertexRecordAddress width v.val 1)+(i : ℤ))=I (I (vertexRecordAddress width v.val 1)+(i : ℤ))) :
    GraphCache g J width stored free := by
  refine ⟨h.widthBound,h.freeBound,?_,?_,?_,?_,?_⟩
  · intro v
    rw [hfields v 2 (by omega)]
    exact h.flag v
  · intro v hv
    rw [hfields v 0 (by omega)]
    exact h.degree v hv
  · intro v hv
    rw [hfields v 1 (by omega)]
    exact h.basePositive v hv
  · intro v hv
    rw [hfields v 1 (by omega)]
    intro i hi hi'
    rw [hadj v hv i hi']
    exact h.adjacency v hv i hi hi'
  · intro v hv i hi
    rw [hfields v 1 (by omega)]
    exact h.belowFree v hv i hi

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.GraphCacheOwnership

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma GraphCache.mono_free {n : ℕ} {g : InputGraph n} {I : ℤ → ℤ} {width : ℕ}
    {stored : Finset (Fin n)} {free next : ℤ} (h : GraphCache g I width stored free)
    (hle : free ≤ next) : GraphCache g I width stored next := by
  refine ⟨h.widthBound,le_trans h.freeBound hle,h.flag,h.degree,h.basePositive,h.adjacency,?_⟩
  intro v hv i hi
  exact lt_of_lt_of_le (h.belowFree v hv i hi) hle

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexFieldMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertex_integer_update_other_field (I : ℤ → ℤ) (width vertex other offset field : ℕ)
    (value : ℤ) (ho : offset < width) (hf : field < width) (hne : field ≠ offset) :
    Function.update I (vertexRecordAddress width vertex offset) value (vertexRecordAddress width other field)=
      I (vertexRecordAddress width other field) := by
  have hn : vertexRecordAddress width other field ≠ vertexRecordAddress width vertex offset := by
    intro he
    exact hne (vertexRecordAddress_injective width other vertex field offset hf ho he).2
  simp only [Function.update_of_ne hn]

lemma vertex_integer_update_other_vertex (I : ℤ → ℤ) (width vertex other offset field : ℕ)
    (value : ℤ) (ho : offset < width) (hf : field < width) (hne : other ≠ vertex) :
    Function.update I (vertexRecordAddress width vertex offset) value (vertexRecordAddress width other field)=
      I (vertexRecordAddress width other field) := by
  have hn : vertexRecordAddress width other field ≠ vertexRecordAddress width vertex offset := by
    intro he
    exact hne (vertexRecordAddress_injective width other vertex field offset hf ho he).1
  simp only [Function.update_of_ne hn]


lemma QueuedFlags.frame {n : ℕ} {I J : ℤ → ℤ} {width offset : ℕ} {domain : Finset (Fin n)} {queued : Finset ℕ}
    (h : QueuedFlags I width offset domain queued)
    (he : ∀ v ∈ domain, J (vertexRecordAddress width v.val offset)=I (vertexRecordAddress width v.val offset)) :
    QueuedFlags J width offset domain queued := fun v hv => (he v hv).trans (h v hv)

lemma QueuedFlags.insert {n : ℕ} {I : ℤ → ℤ} {width offset : ℕ} {domain : Finset (Fin n)} {queued : Finset ℕ}
    (h : QueuedFlags I width offset domain queued) (hoff : offset < width) (v : Fin n) :
    QueuedFlags (Function.update I (vertexRecordAddress width v.val offset) 1)
      width offset domain (insert v.val queued) := by
  intro u hu
  by_cases he : u=v
  · subst u
    simp
  · have hval : u.val ≠ v.val := by intro h; exact he (Fin.ext h)
    rw [vertex_integer_update_other_vertex I width v.val u.val offset offset 1 hoff hoff hval,h u hu]
    simp [hval]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RankQueueMass

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section
open Finset

lemma slotKeySet_coe (slots : RankSlots) (length : ℕ) (hbound : ∀ r, length ≤ r → slots r=none) :
    (slotKeySet slots length : Set ℕ)=slotsSupport slots := by
  ext x
  constructor
  · intro hx
    obtain ⟨r,hr,hx⟩ := Finset.mem_biUnion.mp hx
    cases hs : slots r with
    | none => simp [hs] at hx
    | some t => exact ⟨r,t,hs,by simpa [hs] using hx⟩
  · rintro ⟨r,t,hr,hx⟩
    have hrl : r < length := by
      by_contra hn
      have hh := hbound r (by omega)
      rw [hr] at hh
      contradiction
    apply Finset.mem_biUnion.mpr
    exact ⟨r,Finset.mem_range.mpr hrl,by simpa [hr] using hx⟩

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RankArrayMemoryCard

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp Finset
noncomputable section

lemma arrayCells_card (base : ℤ) (length : ℕ) : (arrayCells base length).card=length := by
  unfold arrayCells
  have hf : Function.Injective (fun i : ℕ => base + (i : ℤ)) := by
    intro i j hij
    exact Int.ofNat.inj (add_left_cancel hij)
  rw [Finset.card_image_of_injective _ hf]
  simp

lemma SlotRep.card {I : ℤ → ℤ} {p : ℤ} {v : Option RankedTree} {F : Finset ℤ}
    (h : SlotRep I p v F) : F.card=3*v.elim 0 RankedTree.size := by
  cases v with
  | none => rcases h with ⟨hp,rfl⟩; simp
  | some t => simpa [Batteries.BinomialHeap.Imp.HeapNode.realSize,RankedTree.size] using ForestRep.card h

lemma RankArrayRep.queue_card {I : ℤ → ℤ} {base : ℤ} {length : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} (h : RankArrayRep I base length slots roots feet) :
    (queueCells base length feet).card=length+3*slotMass slots length := by
  have hd : Disjoint (arrayCells base length) ((range length).biUnion feet) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨i,hi,hb⟩ := Finset.mem_biUnion.mp hb
    exact Finset.disjoint_left.mp (h.separate i (Finset.mem_range.mp hi)) ha hb
  have hp : (range length : Set ℕ).PairwiseDisjoint feet := by
    intro i hi j hj hij
    exact h.pairwise i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
  rw [queueCells,Finset.card_union_of_disjoint hd,arrayCells_card,Finset.card_biUnion hp]
  congr 1
  rw [slotMass,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (h.node i (Finset.mem_range.mp hi)).card

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapCarryMass

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp Finset
noncomputable section

lemma carry_mass_conservation {I J : ℤ → ℤ} {base : ℤ} {length : ℕ}
    {slots slots' : RankSlots} {roots roots' : ℕ → ℤ} {feet feet' : ℕ → Finset ℤ}
    {p : ℤ} {tree : RankedTree} {F : Finset ℤ}
    (h : RankArrayRep I base length slots roots feet)
    (h' : RankArrayRep J base length slots' roots' feet')
    (ht : ForestRep I p (.node tree.key tree.children .nil) F)
    (hs : Disjoint F (queueCells base length feet))
    (ho : queueCells base length feet'=F ∪ queueCells base length feet) :
    slotMass slots' length=slotMass slots length+tree.size := by
  have hc := congrArg Finset.card ho
  rw [h'.queue_card,Finset.card_union_of_disjoint hs,h.queue_card] at hc
  have htcard : F.card=3*tree.size := by
    simpa [HeapNode.realSize,RankedTree.size] using ForestRep.card ht
  omega

lemma carry_keys_conservation {slots slots' : RankSlots} {length : ℕ} {tree : RankedTree}
    (hb : ∀ r, length ≤ r → slots r=none)
    (hb' : ∀ r, length ≤ r → slots' r=none)
    (hc : slotsSupport slots'=slotsSupport slots ∪ ↑tree.support) :
    slotKeySet slots' length=slotKeySet slots length ∪ tree.support := by
  apply Finset.coe_injective
  rw [Finset.coe_union,slotKeySet_coe slots length hb,slotKeySet_coe slots' length hb',hc]

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueueRankCapacity

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp Finset
noncomputable section

lemma rank_weight_le_mass (slots : RankSlots) (length r : ℕ) (t : RankedTree)
    (hv : SlotsValid slots) (hr : r < length) (ht : slots r=some t) :
    2^r ≤ slotMass slots length := by
  have hs : (slots r).elim 0 RankedTree.size ≤ slotMass slots length := by
    unfold slotMass
    exact Finset.single_le_sum (fun i _ => Nat.zero_le ((slots i).elim 0 RankedTree.size)) (mem_range.mpr hr)
  simpa [ht,t.size_eq_pow r (hv r t ht)] using hs

lemma free_rank_of_mass (slots : RankSlots) (length R N : ℕ)
    (hv : SlotsValid slots) (hr : R < length) (hm : slotMass slots length ≤ N)
    (hp : N < 2^R) : slots R=none := by
  cases he : slots R with
  | none => rfl
  | some t => have h := rank_weight_le_mass slots length R t hv hr he; omega

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexFieldRead

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexFieldReadCode_queryReadOnly (field destination : ℕ) :
    (vertexFieldReadCode field destination).allAtoms queryReadOnly := by
  simp [vertexFieldReadCode,vertexIntegerLoadCode,MachineCode.allAtoms,coreCode,
    queryReadOnly,vertexAddressCode_queryReadOnly]

set_option maxHeartbeats 800000 in
lemma vertex_field_read_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex field destination : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) :
    ∃ out, MachineEval m g ω (vertexFieldReadCode field destination) st (4*width+9) out ∧
      out.scalar.core.ptrs destination=st.scalar.integerMemory (vertexRecordAddress width vertex field) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*width+9 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  let pre := payUnit (pointerWrite st 44 field)
  have ep : MachineEval m g ω (coreCode (.pset 44 field)) st 1 pre := pset_eval m g ω st 44 field hh
  have hpH : pre.scalar.halted=false := hh
  have hp0 : pre.scalar.core.ptrs 0=0 := by simpa [pre,payUnit,pcSet,pointerWrite] using hz
  have hp40 : pre.scalar.core.ptrs 40=(vertex : ℤ) := by simpa [pre,payUnit,pcSet,pointerWrite] using hv
  have hp41 : pre.scalar.core.ptrs 41=(width : ℤ) := by simpa [pre,payUnit,pcSet,pointerWrite] using hw
  obtain ⟨mid,em,hm51,hmI,hmR,hmW,hmO,hmH⟩ := vertex_integer_load_exec m g ω pre hpH width vertex field
    hp0 hp40 hp41 (by simp [pre,payUnit,pcSet,pointerWrite])
  let out := payUnit (pointerWrite mid destination (st.scalar.integerMemory (vertexRecordAddress width vertex field)))
  have eo : MachineEval m g ω (coreCode (.pcopy destination 51)) mid 1 out := by
    have hm51' : mid.scalar.core.ptrs 51=st.scalar.integerMemory (vertexRecordAddress width vertex field) := hm51
    simpa only [out,coreCode,hm51'] using pcopy_eval m g ω mid destination 51 hmH
  have e : MachineEval m g ω (vertexFieldReadCode field destination) st (4*width+9) out := by
    have ee := MachineEval.seq ep (MachineEval.seq em eo)
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,e,by simp [out,payUnit,pcSet,pointerWrite],hmI,hmR,
    e.query_frame (vertexFieldReadCode_queryReadOnly field destination),?_,hmO,hmH⟩
  · change mid.work+1= _
    rw [hmW]
    change st.work+1+(4*width+7 : ℕ)+1= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorEligibility

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma exteriorEligibilityCode_queryReadOnly : exteriorEligibilityCode.allAtoms queryReadOnly := by
  simp [exteriorEligibilityCode,exteriorInactiveCode,exteriorDegreeProductCode,linearCode,
    exteriorDegreeProductInstructions,exteriorActiveOffsetRoutine,exteriorResidualOffsetRoutine,
    PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,sequenceCode,vertexIntegerLoadCode,
    vertexRealLoadCode,vertexAddressCode_queryReadOnly,vertexFieldReadCode_queryReadOnly,
    MachineCode.allAtoms,RealOperation.instruction,coreCode,queryReadOnly]

set_option maxHeartbeats 1200000 in
lemma exterior_degree_product_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω exteriorDegreeProductCode st 2 out ∧
      out.scalar.core.regs 22=st.scalar.core.regs 20*(st.scalar.core.ptrs 60 : ℝ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+2 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω exteriorDegreeProductInstructions
    (by simp [exteriorDegreeProductInstructions,RealOperation.instruction,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,exteriorDegreeProductInstructions,RealOperation.instruction,atomState,machineStep,pcSet,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorInactiveExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2000000 in
lemma exterior_inactive_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex levelBase : ℕ) (q : ℝ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hlevel : st.scalar.core.ptrs 87=(levelBase : ℤ))
    (hq : st.scalar.core.regs 20=q) :
    ∃ out, MachineEval m g ω exteriorInactiveCode st (8*width+21) out ∧
      out.scalar.core.regs 23=st.scalar.core.mem (vertexRecordAddress width vertex (levelBase+1))-
        q*(st.scalar.integerMemory (vertexRecordAddress width vertex 0) : ℝ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(8*width+21 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,ha60,haI,haR,haQ,haW,haO,haH⟩ := vertex_field_read_exec m g ω st hh width vertex 0 60 hz hv hw
  have ha20 := (ea.real_register_frame 20 (by decide)).trans hq
  obtain ⟨b,eb,hb22,hbI,hbR,hbW,hbO,hbH⟩ := exterior_degree_product_exec m g ω a haH
  have hb22' : b.scalar.core.regs 22=q*(st.scalar.integerMemory (vertexRecordAddress width vertex 0) : ℝ) := by
    rw [hb22,ha20,ha60]
  obtain ⟨c,ec,hp,hcI,hcR,hcW,hcO,hcH⟩ := exteriorResidualOffsetRoutine.execute m g ω b hbH
  have ec2 : MachineEval m g ω exteriorResidualOffsetRoutine.code b 2 c := ec
  have hb87 : b.scalar.core.ptrs 87=(levelBase : ℤ) :=
    (eb.pointer_frame 87 (by decide)).trans ((ea.pointer_frame 87 (by decide)).trans hlevel)
  have hc44 : c.scalar.core.ptrs 44=((levelBase+1 : ℕ) : ℤ) := by
    rw [hp]
    simp [exteriorResidualOffsetRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
      PointerOp.destination,PointerOp.result,hb87]
  have hc0 : c.scalar.core.ptrs 0=0 :=
    (ec.pointer_frame 0 (by decide)).trans ((eb.pointer_frame 0 (by decide)).trans ((ea.pointer_frame 0 (by decide)).trans hz))
  have hc40 : c.scalar.core.ptrs 40=(vertex : ℤ) :=
    (ec.pointer_frame 40 (by decide)).trans ((eb.pointer_frame 40 (by decide)).trans ((ea.pointer_frame 40 (by decide)).trans hv))
  have hc41 : c.scalar.core.ptrs 41=(width : ℤ) :=
    (ec.pointer_frame 41 (by decide)).trans ((eb.pointer_frame 41 (by decide)).trans ((ea.pointer_frame 41 (by decide)).trans hw))
  obtain ⟨d,ed,hd10,hdI,hdR,hdW,hdO,hdH⟩ := vertex_real_load_exec m g ω c hcH width vertex (levelBase+1) hc0 hc40 hc41 hc44
  have hd22 : d.scalar.core.regs 22=q*(st.scalar.integerMemory (vertexRecordAddress width vertex 0) : ℝ) :=
    (ed.real_register_frame 22 (by decide)).trans ((ec.real_register_frame 22 (by decide)).trans hb22')
  have hd10' : d.scalar.core.regs 10=st.scalar.core.mem (vertexRecordAddress width vertex (levelBase+1)) := by
    rw [hd10,hcR,hbR,haR]
  let out := payUnit (realWrite d 23 (st.scalar.core.mem (vertexRecordAddress width vertex (levelBase+1))-
    q*(st.scalar.integerMemory (vertexRecordAddress width vertex 0) : ℝ)))
  have ef : MachineEval m g ω (.atom (RealOperation.sub.instruction 23 10 22)) d 1 out := by
    simpa only [out,RealOperation.value,hd10',hd22] using binary_eval m g ω d .sub 23 10 22 hdH
  have eRun : MachineEval m g ω exteriorInactiveCode st (8*width+21) out := by
    have ee := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec2 (MachineEval.seq ed ef)))
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,by simp [out,payUnit,pcSet,realWrite],hdI.trans (hcI.trans (hbI.trans haI)),
    hdR.trans (hcR.trans (hbR.trans haR)),?_,?_,hdO.trans (hcO.trans (hbO.trans haO)),hdH⟩
  · apply eRun.query_frame
    simp [exteriorInactiveCode,exteriorDegreeProductCode,linearCode,exteriorDegreeProductInstructions,
      exteriorResidualOffsetRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
      sequenceCode,vertexRealLoadCode,vertexAddressCode_queryReadOnly,vertexFieldReadCode_queryReadOnly,
      RealOperation.instruction,MachineCode.allAtoms,coreCode,queryReadOnly]
  · change d.work+1= _
    rw [hdW,hcW,hbW,haW]
    change st.work+(4*width+9 : ℕ)+2+(2 : ℕ)+(4*width+7 : ℕ)+1= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorEligibilityExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2100000 in
lemma exterior_eligibility_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex levelBase : ℕ) (q : ℝ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hlevel : st.scalar.core.ptrs 87=(levelBase : ℤ))
    (hq : st.scalar.core.regs 20=q)
    (hactive : 0 ≤ st.scalar.integerMemory (vertexRecordAddress width vertex (levelBase+2))) :
    ∃ steps out, MachineEval m g ω exteriorEligibilityCode st steps out ∧ steps ≤ 12*width+32 ∧
      out.scalar.core.regs 23=(if st.scalar.integerMemory (vertexRecordAddress width vertex (levelBase+2))=0 then
        st.scalar.core.mem (vertexRecordAddress width vertex (levelBase+1))-
          q*(st.scalar.integerMemory (vertexRecordAddress width vertex 0) : ℝ) else 0) ∧
      (0 < out.scalar.core.regs 23 ↔ st.scalar.integerMemory (vertexRecordAddress width vertex (levelBase+2))=0 ∧
        q*(st.scalar.integerMemory (vertexRecordAddress width vertex 0) : ℝ) <
          st.scalar.core.mem (vertexRecordAddress width vertex (levelBase+1))) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  classical
  obtain ⟨a,ea,hp,haI,haR,haW,haO,haH⟩ := exteriorActiveOffsetRoutine.execute m g ω st hh
  have ea3 : MachineEval m g ω exteriorActiveOffsetRoutine.code st 3 a := ea
  have ha44 : a.scalar.core.ptrs 44=((levelBase+2 : ℕ) : ℤ) := by
    rw [hp]
    simp [exteriorActiveOffsetRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
      PointerOp.destination,PointerOp.result,hlevel]
    ring
  have ha0 := (ea.pointer_frame 0 (by decide)).trans hz
  have ha40 := (ea.pointer_frame 40 (by decide)).trans hv
  have ha41 := (ea.pointer_frame 41 (by decide)).trans hw
  obtain ⟨b,eb,hb51,hbI,hbR,hbW,hbO,hbH⟩ := vertex_integer_load_exec m g ω a haH width vertex (levelBase+2) ha0 ha40 ha41 ha44
  have hb51' : b.scalar.core.ptrs 51=st.scalar.integerMemory (vertexRecordAddress width vertex (levelBase+2)) := by rw [hb51,haI]
  have hb0 := (eb.pointer_frame 0 (by decide)).trans ha0
  have hb40 := (eb.pointer_frame 40 (by decide)).trans ha40
  have hb41 := (eb.pointer_frame 41 (by decide)).trans ha41
  have hb87 := (eb.pointer_frame 87 (by decide)).trans ((ea.pointer_frame 87 (by decide)).trans hlevel)
  have hb20 := (eb.real_register_frame 20 (by decide)).trans ((ea.real_register_frame 20 (by decide)).trans hq)
  by_cases he : st.scalar.integerMemory (vertexRecordAddress width vertex (levelBase+2))=0
  · obtain ⟨out,ec,hc23,hcI,hcR,hcQ,hcW,hcO,hcH⟩ := exterior_inactive_exec m g ω (payUnit b) hbH width vertex levelBase q hb0 hb40 hb41 hb87 hb20
    have ebranch : MachineEval m g ω (.branchPointer 51 0 exteriorInactiveCode (coreCode (.const 23 0))) b (1+(8*width+21)) out :=
      MachineEval.pointerLe hbH (by rw [hb51',hb0,he]) ec
    have eRun := MachineEval.seq ea3 (MachineEval.seq eb ebranch)
    have ho23 : out.scalar.core.regs 23=st.scalar.core.mem (vertexRecordAddress width vertex (levelBase+1))-
        q*(st.scalar.integerMemory (vertexRecordAddress width vertex 0) : ℝ) := by
      change out.scalar.core.regs 23=b.scalar.core.mem _-q*(b.scalar.integerMemory _ : ℝ) at hc23
      rw [hc23,hbR,haR,hbI,haI]
    refine ⟨3+((4*width+7)+(1+(8*width+21))),out,eRun,by omega,by simpa only [if_pos he] using ho23,?_,
      hcI.trans (hbI.trans haI),hcR.trans (hbR.trans haR),eRun.query_frame exteriorEligibilityCode_queryReadOnly,
      ?_,hcO.trans (hbO.trans haO),hcH⟩
    · rw [ho23]
      simp only [he,true_and]
      exact sub_pos
    · rw [hcW,payUnit_work,hbW,haW]
      change st.work+(3 : ℕ)+(4*width+7 : ℕ)+1+(8*width+21 : ℕ)= _
      push_cast
      ring
  · let mid := payUnit (realWrite (payUnit b) 23 0)
    have ec : MachineEval m g ω (coreCode (.const 23 0)) (payUnit b) 1 mid := const_eval m g ω (payUnit b) 23 0 hbH
    have ebranch : MachineEval m g ω (.branchPointer 51 0 exteriorInactiveCode (coreCode (.const 23 0))) b 3 (payUnit mid) :=
      MachineEval.pointerGt hbH (by rw [hb51',hb0]; omega) ec
    have eRun := MachineEval.seq ea3 (MachineEval.seq eb ebranch)
    have ho23 : (payUnit mid).scalar.core.regs 23=0 := by simp [mid,payUnit,pcSet,realWrite]
    refine ⟨3+((4*width+7)+3),payUnit mid,eRun,by omega,by simp only [ho23,if_neg he],?_,
      hbI.trans haI,hbR.trans haR,eRun.query_frame exteriorEligibilityCode_queryReadOnly,?_,hbO.trans haO,hbH⟩
    · simp only [ho23,lt_self_iff_false,he,false_and]
    · change b.work+1+1+1= _
      rw [hbW,haW]
      change st.work+(3 : ℕ)+(4*width+7 : ℕ)+1+1+1= _
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexFlagClear

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma vertexFlagClearCode_registerReadOnly : vertexFlagClearCode.allAtoms registerReadOnly := by
  simp [vertexFlagClearCode,vertexIntegerStoreCode,vertexAddressCode_registerReadOnly,
    coreCode,MachineCode.allAtoms,registerReadOnly]

lemma vertexFlagClearCode_queryReadOnly : vertexFlagClearCode.allAtoms queryReadOnly := by
  simp [vertexFlagClearCode,vertexIntegerStoreCode,vertexAddressCode_queryReadOnly,
    coreCode,MachineCode.allAtoms,queryReadOnly]

set_option maxHeartbeats 1200000 in
lemma vertex_flag_clear_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex offset : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hOff : st.scalar.core.ptrs 88=(offset : ℤ)) :
    ∃ out, MachineEval m g ω vertexFlagClearCode st (4*width+9) out ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (vertexRecordAddress width vertex offset) 0 ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.regs=st.scalar.core.regs ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*width+9 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  let a := payUnit (pointerWrite st 44 (offset : ℤ))
  have ea : MachineEval m g ω (coreCode (.pcopy 44 88)) st 1 a := by
    simpa only [a,coreCode,hOff] using pcopy_eval m g ω st 44 88 hh
  let b := payUnit (pointerWrite a 51 0)
  have eb : MachineEval m g ω (coreCode (.pcopy 51 0)) a 1 b := by
    have ha0 : a.scalar.core.ptrs 0=0 := (ea.pointer_frame 0 (by decide)).trans hz
    simpa only [b,coreCode,ha0] using pcopy_eval m g ω a 51 0 hh
  have b0 := (eb.pointer_frame 0 (by decide)).trans ((ea.pointer_frame 0 (by decide)).trans hz)
  have b40 := (eb.pointer_frame 40 (by decide)).trans ((ea.pointer_frame 40 (by decide)).trans hv)
  have b41 := (eb.pointer_frame 41 (by decide)).trans ((ea.pointer_frame 41 (by decide)).trans hw)
  have b44 : b.scalar.core.ptrs 44=(offset : ℤ) := by simp [b,a,payUnit,pcSet,pointerWrite]
  have b51 : b.scalar.core.ptrs 51=0 := by simp [b,payUnit,pcSet,pointerWrite]
  obtain ⟨out,ec,hoI,hoR,hoW,hoO,hoH⟩ := vertex_integer_store_exec m g ω b hh width vertex offset b0 b40 b41 b44
  have eRun : MachineEval m g ω vertexFlagClearCode st (4*width+9) out := by
    have ee := MachineEval.seq ea (MachineEval.seq eb ec)
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,?_,hoR,eRun.register_frame vertexFlagClearCode_registerReadOnly,
    eRun.query_frame vertexFlagClearCode_queryReadOnly,?_,hoO,hoH⟩
  · rw [hoI,b51]
    rfl
  · rw [hoW]
    change st.work+1+1+(4*width+7 : ℕ)= _
    push_cast
    ring

lemma SparseQueue.SlotRep.positive_cells {I : ℤ → ℤ} {p : ℤ} {v : Option RankedTree} {F : Finset ℤ}
    (h : SlotRep I p v F) : ∀ z ∈ F, 2 ≤ z := by
  cases v with
  | none => intro z hz; rw [h.2] at hz; simp at hz
  | some t => exact ForestRep.positive_cells h

lemma SparseQueue.RankArrayRep.positive_cells {I : ℤ → ℤ} {base : ℤ} {length : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} (h : RankArrayRep I base length slots roots feet) :
    ∀ z ∈ queueCells base length feet, 2 ≤ z := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz|hz
  · obtain ⟨i,hi,rfl⟩ := (mem_arrayCells _ _ _).mp hz
    have hp := h.positive
    omega
  · obtain ⟨i,hi,hz⟩ := Finset.mem_biUnion.mp hz
    exact SparseQueue.SlotRep.positive_cells (h.node i (Finset.mem_range.mp hi)) z hz

lemma SparseQueue.RankArrayRep.negative_write {I : ℤ → ℤ} {base : ℤ} {length : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} (h : RankArrayRep I base length slots roots feet)
    (z value : ℤ) (hz : z < 0) : RankArrayRep (Function.update I z value) base length slots roots feet := by
  apply h.frame
  intro a ha
  have hp := h.positive_cells a ha
  simp only [Function.update_of_ne (by omega : a ≠ z)]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorQueueMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma ExteriorQueueMemory.frame {n : ℕ} {I J : ℤ → ℤ} {R S : ℤ → ℝ}
    {width levelBase flagOffset : ℕ} {q : ℝ} {domain : Finset (Fin n)} {valid queued : Finset ℕ}
    (h : ExteriorQueueMemory I R width levelBase flagOffset q domain valid queued)
    (hI : ∀ z, z < 0 → J z=I z) (hR : ∀ z, z < 0 → S z=R z) :
    ExteriorQueueMemory J S width levelBase flagOffset q domain valid queued := by
  refine ⟨h.queuedDomain,h.flags.frame (fun v hv => hI _ (vertexRecordAddress_negative _ _ _)),?_,?_⟩
  · intro v hv
    rw [hI _ (vertexRecordAddress_negative _ _ _)]
    exact h.activeNonnegative v hv
  · intro v hv
    rw [hI _ (vertexRecordAddress_negative _ _ _),hI _ (vertexRecordAddress_negative _ _ _),
      hR _ (vertexRecordAddress_negative _ _ _)]
    exact h.eligibility v hv

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RankQueueObject

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section


namespace RankQueueObject

def frame {I J : ℤ → ℤ} {base : ℤ} {length : ℕ} {free nextFree floor : ℤ}
    (obj : RankQueueObject I base length free floor)
    (hI : ∀ z ∈ obj.cells, J z=I z) (hFree : free ≤ nextFree) :
    RankQueueObject J base length nextFree floor := {
  slots := obj.slots
  roots := obj.roots
  feet := obj.feet
  representation := obj.representation.frame hI
  unique := obj.unique
  below := fun z hz => (obj.below z hz).trans_le hFree
  above := obj.above
}

def lower_floor {I : ℤ → ℤ} {base free floor nextFloor : ℤ} {length : ℕ}
    (obj : RankQueueObject I base length free floor) (hFloor : nextFloor ≤ floor) :
    RankQueueObject I base length free nextFloor := {
  slots := obj.slots
  roots := obj.roots
  feet := obj.feet
  representation := obj.representation
  unique := obj.unique
  below := obj.below
  above := fun z hz => hFloor.trans (obj.above z hz)
}

end RankQueueObject

structure ExteriorQueueContext (st : MachineState) (width levelBase flagOffset length : ℕ)
    (base floor : ℤ) (q : ℝ) : Prop where
  zero : st.scalar.core.ptrs 0=0
  basePointer : st.scalar.core.ptrs 13=base
  lengthPointer : st.scalar.core.ptrs 25=(length : ℤ)
  widthPointer : st.scalar.core.ptrs 50=(width : ℤ)
  levelPointer : st.scalar.core.ptrs 87=(levelBase : ℤ)
  flagPointer : st.scalar.core.ptrs 88=(flagOffset : ℤ)
  threshold : st.scalar.core.regs 20=q
  floorBound : floor ≤ st.scalar.core.ptrs 20

def ExteriorQueueContext.payUnit {st : MachineState} {width levelBase flagOffset length : ℕ}
    {base floor : ℤ} {q : ℝ} (ctx : ExteriorQueueContext st width levelBase flagOffset length base floor q) :
    ExteriorQueueContext (NearlyOptimalPPR.Computation.payUnit st) width levelBase flagOffset length base floor q := {
  zero := ctx.zero
  basePointer := ctx.basePointer
  lengthPointer := ctx.lengthPointer
  widthPointer := ctx.widthPointer
  levelPointer := ctx.levelPointer
  flagPointer := ctx.flagPointer
  threshold := ctx.threshold
  floorBound := ctx.floorBound
}

lemma ExteriorQueueContext.change_floor {st : MachineState} {width levelBase flagOffset length : ℕ}
    {base floor nextFloor : ℤ} {q : ℝ} (ctx : ExteriorQueueContext st width levelBase flagOffset length base floor q)
    (hFloor : nextFloor ≤ st.scalar.core.ptrs 20) : ExteriorQueueContext st width levelBase flagOffset length base nextFloor q := {
  zero := ctx.zero
  basePointer := ctx.basePointer
  lengthPointer := ctx.lengthPointer
  widthPointer := ctx.widthPointer
  levelPointer := ctx.levelPointer
  flagPointer := ctx.flagPointer
  threshold := ctx.threshold
  floorBound := hFloor
}

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.KeyListRepresentation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section


lemma KeyListRep.nil {I : ℤ → ℤ} {head : ℤ} {F : Finset ℤ} (h : KeyListRep I head [] F) :
    head=0 ∧ F=∅ := h.nil_iff

lemma KeyListRep.cons_view {I : ℤ → ℤ} {head : ℤ} {a : ℕ} {keys : List ℕ} {F : Finset ℤ}
    (h : KeyListRep I head (a::keys) F) :
    ∃ next S, 2 ≤ head ∧ I head=(a : ℤ) ∧ I (head+1)=0 ∧ I (head+2)=next ∧
      KeyListRep I next keys S ∧ F=nodeCells head ∪ S ∧ Disjoint (nodeCells head) S := by
  cases h with
  | node p a cp sp c s C S hp hk hc hs hC hS hdC hdS hdCS =>
    obtain ⟨rfl,rfl⟩ := hC.nil_iff
    exact ⟨sp,S,hp,hk,hc,hs,hS,by simp,hdS⟩

lemma KeyListRep.frame {I J : ℤ → ℤ} {head : ℤ} {keys : List ℕ} {F : Finset ℤ}
    (h : KeyListRep I head keys F) (he : ∀ z ∈ F, J z=I z) : KeyListRep J head keys F :=
  ForestRep.frame h he

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexListRepresentation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma VertexListRep.nil {n : ℕ} {I : ℤ → ℤ} {head : ℤ} {F : Finset ℤ}
    (h : VertexListRep (n:=n) I head [] F) : head=0 ∧ F=∅ := KeyListRep.nil h

lemma VertexListRep.cons_view {n : ℕ} {I : ℤ → ℤ} {head : ℤ} {v : Fin n} {vertices : List (Fin n)} {F : Finset ℤ}
    (h : VertexListRep I head (v::vertices) F) :
    ∃ next S, 2 ≤ head ∧ I head=(v.val : ℤ) ∧ I (head+1)=0 ∧ I (head+2)=next ∧
      VertexListRep I next vertices S ∧ F=nodeCells head ∪ S ∧ Disjoint (nodeCells head) S :=
  KeyListRep.cons_view h

lemma VertexListRep.frame {n : ℕ} {I J : ℤ → ℤ} {head : ℤ} {vertices : List (Fin n)} {F : Finset ℤ}
    (h : VertexListRep I head vertices F) (he : ∀ z ∈ F, J z=I z) : VertexListRep J head vertices F := KeyListRep.frame h he

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FramePendingKeys

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section


structure FramePendingKeys {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (j width length : ℕ) (machine : MachineState) (floor : ℤ) where
  N : machine.scalar.core.mem (levelHeaderAddress j 0)=(logical.frames j).N
  q : machine.scalar.core.mem (levelHeaderAddress j 1)=(logical.frames j).q
  Q : machine.scalar.core.mem (levelHeaderAddress j 3)=(logical.frames j).Q
  W : machine.scalar.core.mem (levelHeaderAddress j 4)=(logical.frames j).W
  theta : machine.scalar.core.mem (levelHeaderAddress j 5)=(logical.frames j).theta
  block : machine.scalar.integerMemory (levelHeaderAddress j 14)=((logical.frames j).block : ℤ)
  pc : machine.scalar.integerMemory (levelHeaderAddress j 0)=(normalizePCNumber (logical.frames j).pc : ℤ)
  openBudget : machine.scalar.integerMemory (levelHeaderAddress j 9)=if (logical.frames j).openBudget then 1 else 0
  needFull : machine.scalar.integerMemory (levelHeaderAddress j 10)=if (logical.frames j).needFull then 1 else 0
  children : machine.scalar.integerMemory (levelHeaderAddress j 11)=((logical.frames j).childrenThisEpisode : ℤ)
  reference : ∀ v ∈ parentDomain logical j,
    machine.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)))=(logical.frames j).reference v
  residual : ∀ v ∈ parentDomain logical j,
    machine.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)+1))=(logical.frames j).residual v
  activeFlags : ∀ v ∈ parentDomain logical j,
    machine.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+2))=if v ∈ (logical.frames j).active then 1 else 0
  cacheFlags : ∀ v ∈ parentDomain logical j,
    machine.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+4))=if v ∈ (logical.frames j).cache then 1 else 0
  activeVertices : List (Fin n)
  activeFoot : Finset ℤ
  activeRep : VertexListRep machine.scalar.integerMemory (machine.scalar.integerMemory (levelHeaderAddress j 1)) activeVertices activeFoot
  activeNodup : activeVertices.Nodup
  activeSet : activeVertices.toFinset=(logical.frames j).active
  activeCount : machine.scalar.integerMemory (levelHeaderAddress j 3)=((logical.frames j).active.card : ℤ)
  activeVolume : machine.scalar.integerMemory (levelHeaderAddress j 2)=(volumeNat g (logical.frames j).active : ℤ)
  activeBelow : ∀ z ∈ activeFoot, z < machine.scalar.core.ptrs 20
  activeAbove : ∀ z ∈ activeFoot, floor ≤ z
  cacheVertices : List (Fin n)
  cacheFoot : Finset ℤ
  cacheRep : VertexListRep machine.scalar.integerMemory (machine.scalar.integerMemory (levelHeaderAddress j 4)) cacheVertices cacheFoot
  cacheNodup : cacheVertices.Nodup
  cacheSet : cacheVertices.toFinset=(logical.frames j).cache
  cacheCount : machine.scalar.integerMemory (levelHeaderAddress j 5)=((logical.frames j).cache.card : ℤ)
  cacheVolume : machine.scalar.integerMemory (levelHeaderAddress j 6)=(volumeNat g (logical.frames j).cache : ℤ)
  cacheBelow : ∀ z ∈ cacheFoot, z < machine.scalar.core.ptrs 20
  cacheAbove : ∀ z ∈ cacheFoot, floor ≤ z
  exteriorBase : ℤ
  highBase : ℤ
  exteriorPointer : machine.scalar.integerMemory (levelHeaderAddress j 7)=exteriorBase
  highPointer : machine.scalar.integerMemory (levelHeaderAddress j 8)=highBase
  exteriorObject : RankQueueObject machine.scalar.integerMemory exteriorBase length (machine.scalar.core.ptrs 20) floor
  highObject : RankQueueObject machine.scalar.integerMemory highBase length (machine.scalar.core.ptrs 20) floor
  exteriorData : ExteriorQueueMemory machine.scalar.integerMemory machine.scalar.core.mem width
    (16*(j+1)) (16*(j+1)+3) (logical.frames j).q (parentDomain logical j)
    ((logical.frames j).exterior.image Fin.val) exteriorObject.keys
  virtualExcluded : ∀ v ∈ parentDomain logical j,
    machine.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+5))=0
  highFlags : QueuedFlags machine.scalar.integerMemory width (16*(j+1)+6) (parentDomain logical j) highObject.keys
  highDomain : highObject.keys ⊆ (parentDomain logical j).image Fin.val
  highValid : ∀ v ∈ parentDomain logical j, v.val ∈ (logical.frames j).high.image Fin.val ↔
    machine.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+2)) ≠ 0 ∧
      3*(logical.frames j).theta*(machine.scalar.integerMemory (vertexRecordAddress width v.val 0) : ℝ) ≤
        machine.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)+1))

namespace FramePendingKeys

def owned {n : ℕ} {g : InputGraph n} {logical : RecursiveState n} {j width length : ℕ}
    {machine : MachineState} {floor : ℤ} (f : FramePendingKeys g logical j width length machine floor) : Finset ℤ :=
  f.activeFoot ∪ f.cacheFoot ∪ f.exteriorObject.cells ∪ f.highObject.cells

def pieces {n : ℕ} {g : InputGraph n} {logical : RecursiveState n} {j width length : ℕ}
    {machine : MachineState} {floor : ℤ} (f : FramePendingKeys g logical j width length machine floor) : List (Finset ℤ) :=
  [f.activeFoot,f.cacheFoot,f.exteriorObject.cells,f.highObject.cells]

end FramePendingKeys
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveFrameTransport

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def RecursiveFrameMemory.logical_frame {n : ℕ} {g : InputGraph n} {a b : RecursiveState n}
    {j width length : ℕ} {machine : MachineState} {floor : ℤ}
    (f : RecursiveFrameMemory g a j width length machine floor)
    (hFrame : b.frames j=a.frames j) (hDomain : parentDomain b j=parentDomain a j) :
    RecursiveFrameMemory g b j width length machine floor := {
  N := by rw [hFrame]; exact f.N
  q := by rw [hFrame]; exact f.q
  Q := by rw [hFrame]; exact f.Q
  W := by rw [hFrame]; exact f.W
  theta := by rw [hFrame]; exact f.theta
  block := by rw [hFrame]; exact f.block
  pc := by rw [hFrame]; exact f.pc
  openBudget := by rw [hFrame]; exact f.openBudget
  needFull := by rw [hFrame]; exact f.needFull
  children := by rw [hFrame]; exact f.children
  reference := by rw [hFrame,hDomain]; exact f.reference
  residual := by rw [hFrame,hDomain]; exact f.residual
  activeFlags := by rw [hFrame,hDomain]; exact f.activeFlags
  cacheFlags := by rw [hFrame,hDomain]; exact f.cacheFlags
  activeVertices := f.activeVertices
  activeFoot := f.activeFoot
  activeRep := f.activeRep
  activeNodup := f.activeNodup
  activeSet := by rw [hFrame]; exact f.activeSet
  activeCount := by rw [hFrame]; exact f.activeCount
  activeVolume := by rw [hFrame]; exact f.activeVolume
  activeBelow := f.activeBelow
  activeAbove := f.activeAbove
  cacheVertices := f.cacheVertices
  cacheFoot := f.cacheFoot
  cacheRep := f.cacheRep
  cacheNodup := f.cacheNodup
  cacheSet := by rw [hFrame]; exact f.cacheSet
  cacheCount := by rw [hFrame]; exact f.cacheCount
  cacheVolume := by rw [hFrame]; exact f.cacheVolume
  cacheBelow := f.cacheBelow
  cacheAbove := f.cacheAbove
  exteriorBase := f.exteriorBase
  highBase := f.highBase
  exteriorPointer := f.exteriorPointer
  highPointer := f.highPointer
  exteriorObject := f.exteriorObject
  highObject := f.highObject
  exteriorData := by rw [hFrame,hDomain]; exact f.exteriorData
  exteriorCover := by rw [hFrame]; exact f.exteriorCover
  highBoolean := by rw [hFrame,hDomain]; exact f.highBoolean
  virtualExcluded := by rw [hDomain]; exact f.virtualExcluded
  highFlags := by rw [hDomain]; exact f.highFlags
  highDomain := by rw [hDomain]; exact f.highDomain
  highValid := by rw [hFrame,hDomain]; exact f.highValid
  highCover := by rw [hFrame]; exact f.highCover
}

def RecursiveFrameMemory.memory_frame {n : ℕ} {g : InputGraph n} {logical : RecursiveState n}
    {j width length : ℕ} {st out : MachineState} {floor : ℤ}
    (f : RecursiveFrameMemory g logical j width length st floor)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hHeaderI : ∀ slot < 32, out.scalar.integerMemory (levelHeaderAddress j slot)=st.scalar.integerMemory (levelHeaderAddress j slot))
    (hHeaderR : ∀ slot < 32, out.scalar.core.mem (levelHeaderAddress j slot)=st.scalar.core.mem (levelHeaderAddress j slot))
    (hFieldsI : ∀ v ∈ parentDomain logical j, ∀ field < 16*(j+1)+7,
      out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field))
    (hFieldsR : ∀ v ∈ parentDomain logical j, ∀ field < 16*(j+1)+7,
      out.scalar.core.mem (vertexRecordAddress width v.val field)=st.scalar.core.mem (vertexRecordAddress width v.val field))
    (hOwned : ∀ z ∈ f.owned, out.scalar.integerMemory z=st.scalar.integerMemory z) :
    RecursiveFrameMemory g logical j width length out floor := by
  let ext := f.exteriorObject.frame
    (fun z hz => hOwned z (Finset.mem_union_left _ (Finset.mem_union_right _ hz))) hFree
  let high := f.highObject.frame (fun z hz => hOwned z (Finset.mem_union_right _ hz)) hFree
  refine {
    N := (hHeaderR 0 (by decide)).trans f.N
    q := (hHeaderR 1 (by decide)).trans f.q
    Q := (hHeaderR 3 (by decide)).trans f.Q
    W := (hHeaderR 4 (by decide)).trans f.W
    theta := (hHeaderR 5 (by decide)).trans f.theta
    block := (hHeaderI 14 (by decide)).trans f.block
    pc := (hHeaderI 0 (by decide)).trans f.pc
    openBudget := (hHeaderI 9 (by decide)).trans f.openBudget
    needFull := (hHeaderI 10 (by decide)).trans f.needFull
    children := (hHeaderI 11 (by decide)).trans f.children
    reference := fun v hv => (hFieldsR v hv _ (by omega)).trans (f.reference v hv)
    residual := fun v hv => (hFieldsR v hv _ (by omega)).trans (f.residual v hv)
    activeFlags := fun v hv => (hFieldsI v hv _ (by omega)).trans (f.activeFlags v hv)
    cacheFlags := fun v hv => (hFieldsI v hv _ (by omega)).trans (f.cacheFlags v hv)
    activeVertices := f.activeVertices
    activeFoot := f.activeFoot
    activeRep := ?_
    activeNodup := f.activeNodup
    activeSet := f.activeSet
    activeCount := (hHeaderI 3 (by decide)).trans f.activeCount
    activeVolume := (hHeaderI 2 (by decide)).trans f.activeVolume
    activeBelow := fun z hz => (f.activeBelow z hz).trans_le hFree
    activeAbove := f.activeAbove
    cacheVertices := f.cacheVertices
    cacheFoot := f.cacheFoot
    cacheRep := ?_
    cacheNodup := f.cacheNodup
    cacheSet := f.cacheSet
    cacheCount := (hHeaderI 5 (by decide)).trans f.cacheCount
    cacheVolume := (hHeaderI 6 (by decide)).trans f.cacheVolume
    cacheBelow := fun z hz => (f.cacheBelow z hz).trans_le hFree
    cacheAbove := f.cacheAbove
    exteriorBase := f.exteriorBase
    highBase := f.highBase
    exteriorPointer := (hHeaderI 7 (by decide)).trans f.exteriorPointer
    highPointer := (hHeaderI 8 (by decide)).trans f.highPointer
    exteriorObject := ext
    highObject := high
    exteriorData := ?_
    exteriorCover := f.exteriorCover
    highBoolean := ?_
    virtualExcluded := fun v hv => (hFieldsI v hv _ (by omega)).trans (f.virtualExcluded v hv)
    highFlags := ?_
    highDomain := f.highDomain
    highValid := ?_
    highCover := f.highCover
  }
  · rw [hHeaderI 1 (by decide)]
    apply f.activeRep.frame
    intro z hz
    apply hOwned
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hz))
  · rw [hHeaderI 4 (by decide)]
    apply f.cacheRep.frame
    intro z hz
    apply hOwned
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hz))
  · refine ⟨f.exteriorData.queuedDomain,?_,?_,?_⟩
    · intro v hv
      rw [hFieldsI v hv _ (by omega)]
      exact f.exteriorData.flags v hv
    · intro v hv
      rw [hFieldsI v hv _ (by omega)]
      exact f.exteriorData.activeNonnegative v hv
    · intro v hv
      rw [hFieldsI v hv _ (by omega),hFieldsI v hv 0 (by omega),hFieldsR v hv _ (by omega)]
      exact f.exteriorData.eligibility v hv
  · intro v hv
    rw [hFieldsR v hv _ (by omega),hFieldsI v hv _ (by omega),hFieldsI v hv 0 (by omega),hFieldsR v hv _ (by omega)]
    exact f.highBoolean v hv
  · intro v hv
    rw [hFieldsI v hv _ (by omega)]
    exact f.highFlags v hv
  · intro v hv
    rw [hFieldsI v hv _ (by omega),hFieldsI v hv 0 (by omega),hFieldsR v hv _ (by omega)]
    exact f.highValid v hv

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ChildState

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


@[simp] lemma spawnChild_top {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n) :
    (spawnChildState g ell logical).top=logical.top+1 := rfl
@[simp] lemma spawnChild_x {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n) :
    (spawnChildState g ell logical).x=logical.x := rfl
@[simp] lemma spawnChild_stored {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n) :
    (spawnChildState g ell logical).stored=logical.stored := rfl
@[simp] lemma spawnChild_boundary {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n) :
    (spawnChildState g ell logical).boundaryEdges=logical.boundaryEdges := rfl

lemma spawnChild_child {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n) :
    (spawnChildState g ell logical).frames (logical.top+1)=
      freshFrame g [] ell (logical.top+1) logical.nextId (logical.frames logical.top).block
        (logical.frames logical.top).theta (logical.frames logical.top).active logical.x
        (logical.frames logical.top).residual := by simp [spawnChildState]

lemma spawnChild_parent {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n) :
    (spawnChildState g ell logical).frames logical.top={logical.frames logical.top with
      pc := .afterChild,childrenThisEpisode := (logical.frames logical.top).childrenThisEpisode+1} := by
  simp [spawnChildState,changeFrame,debit]

lemma spawnChild_other {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n)
    (i : ℕ) (hi : i ≠ logical.top) (hc : i ≠ logical.top+1) :
    (spawnChildState g ell logical).frames i=logical.frames i := by
  simp [spawnChildState,changeFrame,debit,Function.update_of_ne hi,Function.update_of_ne hc]

lemma spawnChild_active_old {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n)
    (i : ℕ) (hi : i ≤ logical.top) :
    ((spawnChildState g ell logical).frames i).active=(logical.frames i).active := by
  by_cases he : i=logical.top
  · subst i; rw [spawnChild_parent]
  · rw [spawnChild_other g ell logical i he (by omega)]

lemma spawnChild_domain_old {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n)
    (i : ℕ) (hi : i ≤ logical.top) :
    parentDomain (spawnChildState g ell logical) i=parentDomain logical i := by
  unfold parentDomain
  split_ifs with he
  · rfl
  · rw [spawnChild_active_old g ell logical (i-1) (by omega)]

lemma spawnChild_domain_child {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n) :
    parentDomain (spawnChildState g ell logical) (logical.top+1)=(logical.frames logical.top).active := by
  simp [parentDomain,spawnChild_parent]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveMachineFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def RecursiveMachineMemory.frame {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hI : out.scalar.integerMemory=st.scalar.integerMemory) (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : RecursiveMachineMemory g s α ε ell length logical out := {
  zero := (hP 0 (by simp)).trans pm.zero
  top := (hP 100 (by simp)).trans pm.top
  width := (hP 50 (by simp)).trans pm.width
  alphaRegister := (hG 30 (by simp)).trans pm.alphaRegister
  one := (hG 31 (by simp)).trans pm.one
  alphaMemory := by rw [hR]; exact pm.alphaMemory
  epsilonMemory := by rw [hR]; exact pm.epsilonMemory
  depthMemory := by rw [hI]; exact pm.depthMemory
  lengthMemory := by rw [hI]; exact pm.lengthMemory
  seedMemory := by rw [hI]; exact pm.seedMemory
  allocator := by rw [hP 20 (by simp)]; exact pm.allocator
  potential := by rw [hR]; exact pm.potential
  seedMarker := by rw [hR]; exact pm.seedMarker
  boundary := by rw [hI]; exact pm.boundary
  graphCache := by rw [hI,hP 20 (by simp)]; exact pm.graphCache
  rowAbove := by rw [hI]; exact pm.rowAbove
  knownDegree := by rw [hI]; exact pm.knownDegree
  unknownDegree := by rw [hI]; exact pm.unknownDegree
  frames := fun i hi => (pm.frames i hi).memory_frame (by rw [hP 20 (by simp)])
    (by intros; exact congrFun hI _) (by intros; exact congrFun hR _)
    (by intros; exact congrFun hI _) (by intros; exact congrFun hR _) (by intros; exact congrFun hI _)
  pieceSeparation := pm.pieceSeparation
  frameSeparation := pm.frameSeparation
  cacheSeparation := by
    intro i hi
    change Disjoint (pm.frames i hi).owned (cachedRowCells g out.scalar.integerMemory (16*(ell+3)) logical.stored)
    rw [hI]
    exact pm.cacheSeparation i hi
  output := hO.trans pm.output
}

def RecursiveMachineMemory.payUnit {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st) :
    RecursiveMachineMemory g s α ε ell length logical (NearlyOptimalPPR.Computation.payUnit st) :=
  pm.frame rfl rfl (by intros; rfl) (by intros; rfl) rfl

def RecursiveMachineMemory.pointerWrite {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (r : ℕ) (value : ℤ)
    (hr : r ∉ ([0,20,50,100] : List ℕ)) :
    RecursiveMachineMemory g s α ε ell length logical (NearlyOptimalPPR.Computation.pointerWrite st r value) :=
  pm.frame rfl rfl (by
    intro i hi
    apply Function.update_of_ne
    intro he
    subst i
    exact hr hi) (by intros; rfl) rfl

@[simp] lemma RecursiveMachineMemory.frame_queueMass {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hI : out.scalar.integerMemory=st.scalar.integerMemory) (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : (pm.frame hI hR hP hG hO).queueMass=pm.queueMass := rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapNodeAllocation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def nodeAllocMemory (I : ℤ → ℤ) (p key : ℤ) : ℤ → ℤ :=
  Function.update (Function.update (Function.update I p key) (p+1) 0) (p+2) 0

lemma heapNodeAllocCode_wellFormed : heapNodeAllocCode.wellFormed := by
  simp [heapNodeAllocCode,sequenceCode,coreCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 1000000 in
lemma heap_node_alloc_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω heapNodeAllocCode st 8 out ∧
      out.scalar.core.ptrs 0=0 ∧ out.scalar.core.ptrs 5=st.scalar.core.ptrs 20 ∧
      out.scalar.core.ptrs 20=st.scalar.core.ptrs 20+3 ∧
      out.scalar.integerMemory=nodeAllocMemory st.scalar.integerMemory (st.scalar.core.ptrs 20) (st.scalar.core.ptrs 4) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+8 ∧ out.output=st.output := by
  let p := st.scalar.core.ptrs 20
  let key := st.scalar.core.ptrs 4
  let A := payUnit (pointerWrite st 0 0)
  let B := payUnit (pointerWrite A 5 p)
  let C := payUnit (integerWrite B p key)
  let D := payUnit (pointerWrite C 20 (p+1))
  let E := payUnit (integerWrite D (p+1) 0)
  let F := payUnit (pointerWrite E 20 (p+2))
  let H := payUnit (integerWrite F (p+2) 0)
  let out := payUnit (pointerWrite H 20 (p+3))
  have ah : A.scalar.halted=false := hh
  have bh : B.scalar.halted=false := hh
  have ch : C.scalar.halted=false := hh
  have dh : D.scalar.halted=false := hh
  have eh : E.scalar.halted=false := hh
  have fh : F.scalar.halted=false := hh
  have hh' : H.scalar.halted=false := hh
  have ea := pset_eval m g ω st 0 0 hh
  have eb : MachineEval m g ω (coreCode (.pcopy 5 20)) A 1 B := by
    simpa [coreCode,B,A,p,key,payUnit,pcSet,pointerWrite] using pcopy_eval m g ω A 5 20 ah
  have ec : MachineEval m g ω (.atom (.scalar (.integerStore 5 4))) B 1 C := by
    simpa [C,B,A,p,key,payUnit,pcSet,pointerWrite] using integerStore_eval m g ω B 5 4 bh
  have ed : MachineEval m g ω (coreCode (.pinc 20)) C 1 D := by
    simpa [coreCode,D,C,B,A,p,key,payUnit,pcSet,pointerWrite,integerWrite] using pinc_eval m g ω C 20 ch
  have ee : MachineEval m g ω (.atom (.scalar (.integerStore 20 0))) D 1 E := by
    simpa [E,D,C,B,A,p,key,payUnit,pcSet,pointerWrite,integerWrite] using integerStore_eval m g ω D 20 0 dh
  have ef : MachineEval m g ω (coreCode (.pinc 20)) E 1 F := by
    simpa [coreCode,F,E,D,C,B,A,p,key,payUnit,pcSet,pointerWrite,integerWrite,Int.add_assoc] using pinc_eval m g ω E 20 eh
  have eg : MachineEval m g ω (.atom (.scalar (.integerStore 20 0))) F 1 H := by
    simpa [H,F,E,D,C,B,A,p,key,payUnit,pcSet,pointerWrite,integerWrite] using integerStore_eval m g ω F 20 0 fh
  have eo : MachineEval m g ω (coreCode (.pinc 20)) H 1 out := by
    simpa [coreCode,out,H,F,E,D,C,B,A,p,key,payUnit,pcSet,pointerWrite,integerWrite,Int.add_assoc] using pinc_eval m g ω H 20 hh'
  refine ⟨out,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed
      (MachineEval.seq ee (MachineEval.seq ef (MachineEval.seq eg (MachineEval.seq eo (MachineEval.skip out))))))))
  all_goals simp [out,H,F,E,D,C,B,A,p,key,payUnit,pcSet,pointerWrite,integerWrite,nodeAllocMemory] <;> ring

lemma node_alloc_rep (I : ℤ → ℤ) (p : ℤ) (key : ℕ) (hp : 2 ≤ p) :
    ForestRep (nodeAllocMemory I p key) p (.node key .nil .nil) (nodeCells p) := by
  have hk : nodeAllocMemory I p key p=(key : ℤ) := by
    simp [nodeAllocMemory,Function.update_of_ne (by omega : p ≠ p+2),Function.update_of_ne (by omega : p ≠ p+1)]
  have hc : nodeAllocMemory I p key (p+1)=0 := by
    simp [nodeAllocMemory,Function.update_of_ne (by omega : p+1 ≠ p+2)]
  have hs : nodeAllocMemory I p key (p+2)=0 := by simp [nodeAllocMemory]
  simpa using ForestRep.node p key 0 0 .nil .nil ∅ ∅ hp hk hc hs ForestRep.nil ForestRep.nil
    (by simp) (by simp) (by simp)

lemma node_alloc_frame (I : ℤ → ℤ) (p key z : ℤ) (hz : z ∉ nodeCells p) :
    nodeAllocMemory I p key z=I z := by
  have hz' : z ≠ p ∧ z ≠ p+1 ∧ z ≠ p+2 := by simpa [nodeCells] using hz
  simp [nodeAllocMemory,Function.update_of_ne hz'.1,Function.update_of_ne hz'.2.1,Function.update_of_ne hz'.2.2]

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapInsertOwned

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 1800000 in
lemma heap_insert_owned_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base free : ℤ) (length N R key : ℕ)
    (slots : RankSlots) (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ)
    (hq : RankArrayRep st.scalar.integerMemory base length slots roots feet)
    (hb : st.scalar.core.ptrs 13=base) (hf : st.scalar.core.ptrs 20=free) (hfree : 2 ≤ free)
    (hk : st.scalar.core.ptrs 4=(key : ℤ))
    (hbelow : ∀ z ∈ queueCells base length feet, z < free)
    (hu : (slotKeySet slots length).card=slotMass slots length)
    (hnot : key ∉ slotKeySet slots length)
    (hmass : slotMass slots length ≤ N) (hcap : R < length) (hpow : N < 2^R) :
    ∃ steps out slots' roots' feet', MachineEval m g ω heapInsertCode st steps out ∧ steps ≤ 21*R+14 ∧
      RankArrayRep out.scalar.integerMemory base length slots' roots' feet' ∧
      slotKeySet slots' length=insert key (slotKeySet slots length) ∧
      slotMass slots' length=slotMass slots length+1 ∧
      (slotKeySet slots' length).card=slotMass slots' length ∧
      out.scalar.core.ptrs 20=free+3 ∧
      (∀ z ∈ queueCells base length feet', z < free+3) ∧
      queueCells base length feet'=nodeCells free ∪ queueCells base length feet ∧
      (∀ z, z ∉ nodeCells free ∪ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+steps ∧ out.output=st.output ∧
      out.scalar.halted=false := by
  obtain ⟨alloc,ea,hza,hpa,hfa,hia,hrealA,hworkA,houtA⟩ := heap_node_alloc_exec m g ω st hh
  rw [hf] at hpa hfa hia
  rw [hk] at hia
  have hha : alloc.scalar.halted=false := (ea.halted heapNodeAllocCode_wellFormed).trans hh
  have hsep : Disjoint (nodeCells free) (queueCells base length feet) := by
    apply Finset.disjoint_left.mpr
    intro z hz hqz
    have hlo := (nodeCells_mem_iff free z).mp hz
    have hhi := hbelow z hqz
    omega
  have hqa : RankArrayRep alloc.scalar.integerMemory base length slots roots feet := by
    apply hq.frame
    intro z hz
    rw [hia]
    exact node_alloc_frame _ _ _ _ (by intro hn; exact Finset.disjoint_left.mp hsep hn hz)
  have hta : ForestRep alloc.scalar.integerMemory (alloc.scalar.core.ptrs 5) (.node key .nil .nil) (nodeCells free) := by
    rw [hia,hpa]
    exact node_alloc_rep _ _ _ hfree
  let pre := payUnit (pointerWrite alloc 14 0)
  have ep : MachineEval m g ω (coreCode (.pcopy 14 0)) alloc 1 pre := by
    simpa only [coreCode,pre,hza] using pcopy_eval m g ω alloc 14 0 hha
  have hhp : pre.scalar.halted=false := hha
  have hbp : pre.scalar.core.ptrs 13=base :=
    (ep.pointer_frame 13 (by decide)).trans ((ea.pointer_frame 13 (by decide)).trans hb)
  have hweightFree := free_rank_of_mass slots length R N hq.valid hcap hmass hpow
  obtain ⟨u,out,slots',roots',feet',ec,huSteps,hqo,hcontents,hrealC,hworkC,houtC,howned,hframe⟩ :=
    heap_carry_exec m g ω pre hhp base length R 0 slots roots feet ⟨key,.nil⟩ (nodeCells free)
      hbp (by simp [pre,payUnit,pcSet,pointerWrite]) hqa hta hsep rfl (by omega) (by simpa using hweightFree)
  have hmass' := carry_mass_conservation (tree:=⟨key,.nil⟩) hqa hqo hta hsep howned
  have hkeys := carry_keys_conservation hq.bounded hqo.bounded hcontents
  have hkeys' : slotKeySet slots' length=insert key (slotKeySet slots length) := by
    simpa [RankedTree.support,nodeSupport,Finset.union_comm] using hkeys
  have hmass'' : slotMass slots' length=slotMass slots length+1 := by
    simpa [RankedTree.size] using hmass'
  have hbelow' : ∀ z ∈ queueCells base length feet', z < free+3 := by
    rw [howned]
    intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · have he := (nodeCells_mem_iff free z).mp hz; omega
    · have he := hbelow z hz; omega
  refine ⟨8+(1+u),out,slots',roots',feet',MachineEval.seq ea (MachineEval.seq ep ec),by omega,
    hqo,hkeys',hmass'',?_,?_,hbelow',howned,?_,hrealC.trans hrealA,?_,houtC.trans houtA,?_⟩
  · rw [hkeys',Finset.card_insert_of_notMem hnot,hu,hmass'']
  · exact (ec.pointer_frame 20 (by decide)).trans ((ep.pointer_frame 20 (by decide)).trans hfa)
  · intro z hz
    rw [hframe z hz]
    change alloc.scalar.integerMemory z=st.scalar.integerMemory z
    rw [hia]
    exact node_alloc_frame _ _ _ _ (by intro he; exact hz (Finset.mem_union_left _ he))
  · rw [hworkC]
    change (alloc.work+1)+u=st.work+((8+(1+u) : ℕ) : ℝ≥0∞)
    rw [hworkA]
    push_cast
    ring
  · exact (ec.halted heapCarryCode_wellFormed).trans hhp


end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorQueueInsertMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma ExteriorQueueMemory.insert {n : ℕ} {I : ℤ → ℤ} {R : ℤ → ℝ}
    {width levelBase flagOffset : ℕ} {q : ℝ} {domain : Finset (Fin n)} {valid queued : Finset ℕ}
    (h : ExteriorQueueMemory I R width levelBase flagOffset q domain valid queued)
    (hflag : flagOffset < width) (hactive : levelBase+2 < width)
    (hneqActive : flagOffset ≠ levelBase+2) (hneqDegree : flagOffset ≠ 0) (v : Fin n) (hv : v ∈ domain) :
    ExteriorQueueMemory (Function.update I (vertexRecordAddress width v.val flagOffset) 1) R
      width levelBase flagOffset q domain valid (insert v.val queued) := by
  have hdegree : 0 < width := by omega
  have fieldFrame (u : Fin n) (field : ℕ) (hf : field < width) (hne : field ≠ flagOffset) :=
    vertex_integer_update_other_field I width v.val u.val flagOffset field 1 hflag hf hne
  refine ⟨?_,h.flags.insert hflag v,?_,?_⟩
  · intro key hk
    rcases Finset.mem_insert.mp hk with rfl|hk
    · exact Finset.mem_image.mpr ⟨v,hv,rfl⟩
    · exact h.queuedDomain hk
  · intro u hu
    rw [fieldFrame u (levelBase+2) hactive (Ne.symm hneqActive)]
    exact h.activeNonnegative u hu
  · intro u hu
    rw [fieldFrame u (levelBase+2) hactive (Ne.symm hneqActive),fieldFrame u 0 hdegree (Ne.symm hneqDegree)]
    exact h.eligibility u hu

lemma negative_frame_from_insert {I J : ℤ → ℤ} {base free : ℤ} {length : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} (h : RankArrayRep I base length slots roots feet)
    (hf : 2 ≤ free) (he : ∀ z, z ∉ nodeCells free ∪ queueCells base length feet → J z=I z) :
    ∀ z, z < 0 → J z=I z := by
  intro z hz
  apply he
  intro hm
  rcases Finset.mem_union.mp hm with hm|hm
  · have hh := (nodeCells_mem_iff free z).mp hm
    omega
  · have hh := h.positive_cells z hm
    omega

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexFlagSet

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexFlagSetCode_registerReadOnly : vertexFlagSetCode.allAtoms registerReadOnly := by
  simp [vertexFlagSetCode,vertexIntegerStoreCode,vertexAddressCode_registerReadOnly,
    coreCode,MachineCode.allAtoms,registerReadOnly]

lemma vertexFlagSetCode_queryReadOnly : vertexFlagSetCode.allAtoms queryReadOnly := by
  simp [vertexFlagSetCode,vertexIntegerStoreCode,vertexAddressCode_queryReadOnly,
    coreCode,MachineCode.allAtoms,queryReadOnly]

set_option maxHeartbeats 1200000 in
lemma vertex_flag_set_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex offset : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hOff : st.scalar.core.ptrs 88=(offset : ℤ)) :
    ∃ out, MachineEval m g ω vertexFlagSetCode st (4*width+9) out ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (vertexRecordAddress width vertex offset) 1 ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.regs=st.scalar.core.regs ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*width+9 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  let a := payUnit (pointerWrite st 44 (offset : ℤ))
  have ea : MachineEval m g ω (coreCode (.pcopy 44 88)) st 1 a := by
    simpa only [a,coreCode,hOff] using pcopy_eval m g ω st 44 88 hh
  let b := payUnit (pointerWrite a 51 1)
  have eb : MachineEval m g ω (coreCode (.pset 51 1)) a 1 b := pset_eval m g ω a 51 1 hh
  have b0 := (eb.pointer_frame 0 (by decide)).trans ((ea.pointer_frame 0 (by decide)).trans hz)
  have b40 := (eb.pointer_frame 40 (by decide)).trans ((ea.pointer_frame 40 (by decide)).trans hv)
  have b41 := (eb.pointer_frame 41 (by decide)).trans ((ea.pointer_frame 41 (by decide)).trans hw)
  have b44 : b.scalar.core.ptrs 44=(offset : ℤ) := by simp [b,a,payUnit,pcSet,pointerWrite]
  have b51 : b.scalar.core.ptrs 51=1 := by simp [b,payUnit,pcSet,pointerWrite]
  obtain ⟨out,ec,hoI,hoR,hoW,hoO,hoH⟩ := vertex_integer_store_exec m g ω b hh width vertex offset b0 b40 b41 b44
  have eRun : MachineEval m g ω vertexFlagSetCode st (4*width+9) out := by
    have ee := MachineEval.seq ea (MachineEval.seq eb ec)
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,?_,hoR,eRun.register_frame vertexFlagSetCode_registerReadOnly,
    eRun.query_frame vertexFlagSetCode_queryReadOnly,?_,hoO,hoH⟩
  · rw [hoI,b51]
    rfl
  · rw [hoW]
    change st.work+1+1+(4*width+7 : ℕ)= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FlaggedHeapInsert

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 2600000 in
lemma flagged_heap_insert_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width levelBase flagOffset : ℕ)
    (hflag : flagOffset < width) (hactive : levelBase+2 < width)
    (hneqActive : flagOffset ≠ levelBase+2) (hneqDegree : flagOffset ≠ 0)
    (base free : ℤ) (length N R : ℕ) (slots : RankSlots) (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ)
    (q : ℝ) (domain : Finset (Fin n)) (valid : Finset ℕ) (v : Fin n) (hv : v ∈ domain)
    (hqueue : RankArrayRep st.scalar.integerMemory base length slots roots feet)
    (hdata : ExteriorQueueMemory st.scalar.integerMemory st.scalar.core.mem width levelBase flagOffset q
      domain valid (slotKeySet slots length))
    (hb : st.scalar.core.ptrs 13=base) (hf : st.scalar.core.ptrs 20=free) (hfree : 2 ≤ free)
    (hvertex : st.scalar.core.ptrs 40=(v.val : ℤ)) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hFlagOffset : st.scalar.core.ptrs 88=(flagOffset : ℤ))
    (hbelow : ∀ z ∈ queueCells base length feet, z < free)
    (hu : (slotKeySet slots length).card=slotMass slots length) (hnot : v.val ∉ slotKeySet slots length)
    (hmass : slotMass slots length ≤ N) (hcap : R < length) (hpow : N < 2^R) :
    ∃ steps out slots' roots' feet', MachineEval m g ω flaggedHeapInsertCode st steps out ∧
      steps ≤ 21*R+4*width+25 ∧ RankArrayRep out.scalar.integerMemory base length slots' roots' feet' ∧
      slotKeySet slots' length=insert v.val (slotKeySet slots length) ∧
      slotMass slots' length=slotMass slots length+1 ∧ (slotKeySet slots' length).card=slotMass slots' length ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase flagOffset q
        domain valid (slotKeySet slots' length) ∧
      out.scalar.core.ptrs 20=free+3 ∧ out.scalar.core.ptrs 0=0 ∧ (∀ z ∈ queueCells base length feet', z < free+3) ∧
      (∀ r ∈ ({13,25,40,41,50,87,88} : Finset ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧
      queueCells base length feet'=nodeCells free ∪ queueCells base length feet ∧
      (∀ other : Fin n, ∀ field < width, field ≠ flagOffset → out.scalar.integerMemory (vertexRecordAddress width other.val field)=st.scalar.integerMemory (vertexRecordAddress width other.val field)) ∧
      (∀ z, 0 ≤ z → z < free → z ∉ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let pre := payUnit (pointerWrite st 4 (v.val : ℤ))
  have ep : MachineEval m g ω (coreCode (.pcopy 4 40)) st 1 pre := by
    simpa only [pre,coreCode,hvertex] using pcopy_eval m g ω st 4 40 hh
  have hp4 : pre.scalar.core.ptrs 4=(v.val : ℤ) := by simp [pre,payUnit,pcSet,pointerWrite]
  have hp13 := (ep.pointer_frame 13 (by decide)).trans hb
  have hp20 := (ep.pointer_frame 20 (by decide)).trans hf
  obtain ⟨u,mid,ss,rr,ff,ei,huSteps,hqmid,hkeys,hmass',hUnique,hm20,hmBelow,hOwned,hmI,hmR,hmW,hmO,hmH⟩ :=
    heap_insert_owned_exec m g ω pre hh base free length N R v.val slots roots feet hqueue hp13 hp20 hfree hp4 hbelow hu hnot hmass hcap hpow
  have hNeg := negative_frame_from_insert hqueue hfree hmI
  have hmData : ExteriorQueueMemory mid.scalar.integerMemory mid.scalar.core.mem width levelBase flagOffset q
      domain valid (slotKeySet slots length) := hdata.frame hNeg (fun z hz => congrFun hmR z)
  let a := payUnit (pointerWrite mid 0 0)
  have ez : MachineEval m g ω (coreCode (.pset 0 0)) mid 1 a := pset_eval m g ω mid 0 0 hmH
  have a0 : a.scalar.core.ptrs 0=0 := by simp [a,payUnit,pcSet,pointerWrite]
  have a40 := (ez.pointer_frame 40 (by decide)).trans ((ei.pointer_frame 40 (by decide)).trans ((ep.pointer_frame 40 (by decide)).trans hvertex))
  have a41 := (ez.pointer_frame 41 (by decide)).trans ((ei.pointer_frame 41 (by decide)).trans ((ep.pointer_frame 41 (by decide)).trans hw))
  have a88 := (ez.pointer_frame 88 (by decide)).trans ((ei.pointer_frame 88 (by decide)).trans ((ep.pointer_frame 88 (by decide)).trans hFlagOffset))
  obtain ⟨out,es,hoI,hoR,hoRegs,hoQ,hoW,hoO,hoH⟩ := vertex_flag_set_exec m g ω a hmH width v.val flagOffset a0 a40 a41 a88
  have eRun := MachineEval.seq ep (MachineEval.seq ei (MachineEval.seq ez es))
  have hoQueue : RankArrayRep out.scalar.integerMemory base length ss rr ff := by
    rw [hoI]
    exact hqmid.negative_write _ _ (vertexRecordAddress_negative _ _ _)
  have hoData : ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase flagOffset q
      domain valid (slotKeySet ss length) := by
    rw [hoI,hoR,hkeys]
    exact hmData.insert hflag hactive hneqActive hneqDegree v hv
  refine ⟨1+(u+(1+(4*width+9))),out,ss,rr,ff,eRun,by omega,hoQueue,hkeys,hmass',hUnique,hoData,
    (es.pointer_frame 20 (by decide)).trans ((ez.pointer_frame 20 (by decide)).trans hm20),(es.pointer_frame 0 (by decide)).trans a0,hmBelow,?_,
    hoR.trans hmR,hOwned,?_,?_,eRun.query_frame (by decide),?_,hoO.trans hmO,hoH⟩
  · intro r hr
    exact eRun.pointer_frame r (by revert r; decide)
  · intro other field hf' hne
    rw [hoI]
    change Function.update mid.scalar.integerMemory (vertexRecordAddress width v.val flagOffset) 1
      (vertexRecordAddress width other.val field)=st.scalar.integerMemory _
    rw [vertex_integer_update_other_field _ _ _ _ _ _ _ hflag hf' hne]
    exact hNeg _ (vertexRecordAddress_negative _ _ _)
  · intro z hz' hzFree hn
    rw [hoI]
    change Function.update mid.scalar.integerMemory (vertexRecordAddress width v.val flagOffset) 1 z=st.scalar.integerMemory z
    have hnFlag := vertexRecordAddress_negative width v.val flagOffset
    rw [Function.update_of_ne (by omega : z ≠ vertexRecordAddress width v.val flagOffset)]
    apply hmI
    intro hm
    rcases Finset.mem_union.mp hm with hm|hm
    · have hh := (nodeCells_mem_iff free z).mp hm
      omega
    · exact hn hm
  · rw [hoW]
    change mid.work+1+(4*width+9 : ℕ)= _
    rw [hmW]
    change st.work+1+u+1+(4*width+9 : ℕ)= _
    push_cast
    ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueuedFlagRead

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma queuedFlagReadCode_registerReadOnly : queuedFlagReadCode.allAtoms registerReadOnly := by
  simp [queuedFlagReadCode,vertexIntegerLoadCode,vertexAddressCode_registerReadOnly,
    coreCode,MachineCode.allAtoms,registerReadOnly]

lemma queuedFlagReadCode_queryReadOnly : queuedFlagReadCode.allAtoms queryReadOnly := by
  simp [queuedFlagReadCode,vertexIntegerLoadCode,vertexAddressCode_queryReadOnly,
    coreCode,MachineCode.allAtoms,queryReadOnly]

set_option maxHeartbeats 1000000 in
lemma queued_flag_read_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex offset : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hOff : st.scalar.core.ptrs 88=(offset : ℤ)) :
    ∃ out, MachineEval m g ω queuedFlagReadCode st (4*width+8) out ∧
      out.scalar.core.ptrs 51=st.scalar.integerMemory (vertexRecordAddress width vertex offset) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.core.regs=st.scalar.core.regs ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(4*width+8 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let pre := payUnit (pointerWrite st 44 (offset : ℤ))
  have ep : MachineEval m g ω (coreCode (.pcopy 44 88)) st 1 pre := by
    simpa only [pre,coreCode,hOff] using pcopy_eval m g ω st 44 88 hh
  have hp0 := (ep.pointer_frame 0 (by decide)).trans hz
  have hp40 := (ep.pointer_frame 40 (by decide)).trans hv
  have hp41 := (ep.pointer_frame 41 (by decide)).trans hw
  have hp44 : pre.scalar.core.ptrs 44=(offset : ℤ) := by simp [pre,payUnit,pcSet,pointerWrite]
  obtain ⟨out,el,ho51,hoI,hoR,hoW,hoO,hoH⟩ := vertex_integer_load_exec m g ω pre hh width vertex offset hp0 hp40 hp41 hp44
  have eRun : MachineEval m g ω queuedFlagReadCode st (4*width+8) out := by
    have ee := MachineEval.seq ep el
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,ho51,hoI,hoR,eRun.register_frame queuedFlagReadCode_registerReadOnly,
    eRun.query_frame queuedFlagReadCode_queryReadOnly,?_,hoO,hoH⟩
  · rw [hoW]
    change st.work+1+(4*width+7 : ℕ)= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueuedInsertCode

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 2800000 in
lemma queued_insert_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width levelBase flagOffset : ℕ)
    (hflag : flagOffset < width) (hactive : levelBase+2 < width)
    (hneqActive : flagOffset ≠ levelBase+2) (hneqDegree : flagOffset ≠ 0)
    (base free : ℤ) (length N R : ℕ) (slots : RankSlots) (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ)
    (q : ℝ) (domain : Finset (Fin n)) (valid : Finset ℕ) (v : Fin n) (hv : v ∈ domain)
    (hqueue : RankArrayRep st.scalar.integerMemory base length slots roots feet)
    (hdata : ExteriorQueueMemory st.scalar.integerMemory st.scalar.core.mem width levelBase flagOffset q
      domain valid (slotKeySet slots length))
    (hz : st.scalar.core.ptrs 0=0) (hb : st.scalar.core.ptrs 13=base) (hf : st.scalar.core.ptrs 20=free) (hfree : 2 ≤ free)
    (hvertex : st.scalar.core.ptrs 40=(v.val : ℤ)) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hFlagOffset : st.scalar.core.ptrs 88=(flagOffset : ℤ))
    (hbelow : ∀ z ∈ queueCells base length feet, z < free)
    (hu : (slotKeySet slots length).card=slotMass slots length)
    (hmass : slotMass slots length ≤ N) (hcap : R < length) (hpow : N < 2^R) :
    ∃ steps out slots' roots' feet', MachineEval m g ω queuedInsertCode st steps out ∧
      steps ≤ 21*R+8*width+34 ∧ RankArrayRep out.scalar.integerMemory base length slots' roots' feet' ∧
      slotKeySet slots' length=insert v.val (slotKeySet slots length) ∧
      slotMass slots' length=slotMass slots length+(if v.val ∈ slotKeySet slots length then 0 else 1) ∧
      (slotKeySet slots' length).card=slotMass slots' length ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase flagOffset q
        domain valid (slotKeySet slots' length) ∧
      out.scalar.core.ptrs 20=free+(if v.val ∈ slotKeySet slots length then 0 else 3) ∧ out.scalar.core.ptrs 0=0 ∧
      (∀ z ∈ queueCells base length feet', z < out.scalar.core.ptrs 20) ∧
      (∀ r ∈ ({13,25,40,41,50,87,88} : Finset ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧
      queueCells base length feet' ⊆ nodeCells free ∪ queueCells base length feet ∧
      (∀ other : Fin n, ∀ field < width, field ≠ flagOffset → out.scalar.integerMemory (vertexRecordAddress width other.val field)=st.scalar.integerMemory (vertexRecordAddress width other.val field)) ∧
      (∀ z, 0 ≤ z → z < free → z ∉ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨mid,ep,hm51,hmI,hmR,hmRegs,hmQ,hmW,hmO,hmH⟩ := queued_flag_read_exec m g ω st hh width v.val flagOffset hz hvertex hw hFlagOffset
  have hm51' : mid.scalar.core.ptrs 51=if v.val ∈ slotKeySet slots length then 1 else 0 :=
    hm51.trans (hdata.flags v hv)
  have hm0 := (ep.pointer_frame 0 (by decide)).trans hz
  have hm13 := (ep.pointer_frame 13 (by decide)).trans hb
  have hm20 := (ep.pointer_frame 20 (by decide)).trans hf
  have hm40 := (ep.pointer_frame 40 (by decide)).trans hvertex
  have hm41 := (ep.pointer_frame 41 (by decide)).trans hw
  have hm88 := (ep.pointer_frame 88 (by decide)).trans hFlagOffset
  have hmQueue : RankArrayRep mid.scalar.integerMemory base length slots roots feet := by rw [hmI]; exact hqueue
  have hmData : ExteriorQueueMemory mid.scalar.integerMemory mid.scalar.core.mem width levelBase flagOffset q domain valid (slotKeySet slots length) := by rw [hmI,hmR]; exact hdata
  by_cases hmem : v.val ∈ slotKeySet slots length
  · have eb : MachineEval m g ω (.branchPointer 51 0 flaggedHeapInsertCode .skip) mid 2 (payUnit (payUnit mid)) :=
      MachineEval.pointerGt hmH (by rw [hm51',if_pos hmem,hm0]; norm_num) (MachineEval.skip (payUnit mid))
    have eRun := MachineEval.seq ep eb
    refine ⟨4*width+8+2,payUnit (payUnit mid),slots,roots,feet,eRun,by omega,hmQueue,?_,?_,hu,hmData,?_,hm0,?_,?_,hmR,Finset.subset_union_right,
      (fun other field hfield hne => congrFun hmI _),(fun z hz hzF hn => congrFun hmI z),?_,?_,hmO,hmH⟩
    · simp [hmem]
    · simp [hmem]
    · simpa only [payUnit_ptrs,if_pos hmem,add_zero] using hm20
    · intro z hz'
      change z < mid.scalar.core.ptrs 20
      rw [hm20]
      exact hbelow z hz'
    · intro r hr
      exact eRun.pointer_frame r (by revert r; decide)
    · exact eRun.query_frame (by decide)
    · change mid.work+1+1= _
      rw [hmW]
      push_cast
      ring
  · obtain ⟨u,out,ss,rr,ff,ei,huSteps,hqo,hKeys,hMass,hUnique,hoData,ho20,ho0,hoBelow,hoCtx,hoR,hoOwned,hoFields,hoPos,hoQ,hoW,hoO,hoH⟩ :=
      flagged_heap_insert_exec m g ω (payUnit mid) hmH width levelBase flagOffset hflag hactive hneqActive hneqDegree base free length N R
        slots roots feet q domain valid v hv hmQueue hmData hm13 hm20 hfree hm40 hm41 hm88 hbelow hu hmem hmass hcap hpow
    have eb : MachineEval m g ω (.branchPointer 51 0 flaggedHeapInsertCode .skip) mid (1+u) out :=
      MachineEval.pointerLe hmH (by rw [hm51',if_neg hmem,hm0]) ei
    have eRun := MachineEval.seq ep eb
    refine ⟨4*width+8+(1+u),out,ss,rr,ff,eRun,by omega,hqo,hKeys,by simpa only [if_neg hmem] using hMass,
      hUnique,hoData,by simpa only [if_neg hmem] using ho20,ho0,?_,?_,hoR.trans hmR,hoOwned.le,
      (fun other field hfield hne => (hoFields other field hfield hne).trans (congrFun hmI _)),
      (fun z hz hzF hn => (hoPos z hz hzF hn).trans (congrFun hmI z)),?_,?_,hoO.trans hmO,hoH⟩
    · intro z hz'
      rw [ho20]
      exact hoBelow z hz'
    · intro r hr
      exact eRun.pointer_frame r (by revert r; decide)
    · exact eRun.query_frame (by decide)
    · rw [hoW,payUnit_work,hmW]
      push_cast
      ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorQueueRefreshWeak

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 3000000 in
lemma exterior_queue_refresh_weak_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width levelBase flagOffset : ℕ)
    (hflag : flagOffset < width) (hactive : levelBase+2 < width)
    (hneqActive : flagOffset ≠ levelBase+2) (hneqDegree : flagOffset ≠ 0)
    (base free : ℤ) (length N R : ℕ) (slots : RankSlots) (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ)
    (q : ℝ) (domain : Finset (Fin n)) (valid : Finset ℕ) (v : Fin n) (hv : v ∈ domain)
    (hqueue : RankArrayRep st.scalar.integerMemory base length slots roots feet)
    (hdata : ExteriorQueueMemory st.scalar.integerMemory st.scalar.core.mem width levelBase flagOffset q
      domain valid (slotKeySet slots length))
    (hz : st.scalar.core.ptrs 0=0) (hb : st.scalar.core.ptrs 13=base) (hf : st.scalar.core.ptrs 20=free) (hfree : 2 ≤ free)
    (hvertex : st.scalar.core.ptrs 40=(v.val : ℤ)) (hw : st.scalar.core.ptrs 50=(width : ℤ))
    (hlevel : st.scalar.core.ptrs 87=(levelBase : ℤ)) (hFlagOffset : st.scalar.core.ptrs 88=(flagOffset : ℤ))
    (hq : st.scalar.core.regs 20=q) (hbelow : ∀ z ∈ queueCells base length feet, z < free)
    (hu : (slotKeySet slots length).card=slotMass slots length)
    (hmass : slotMass slots length ≤ N) (hcap : R < length) (hpow : N < 2^R) :
    ∃ steps out slots' roots' feet', MachineEval m g ω exteriorQueueRefreshCode st steps out ∧
      steps ≤ 21*R+20*width+70 ∧ RankArrayRep out.scalar.integerMemory base length slots' roots' feet' ∧
      slotKeySet slots' length=(if v.val ∈ valid then insert v.val (slotKeySet slots length) else slotKeySet slots length) ∧
      slotMass slots' length=slotMass slots length+(if v.val ∈ valid ∧ v.val ∉ slotKeySet slots length then 1 else 0) ∧
      (slotKeySet slots' length).card=slotMass slots' length ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase flagOffset q
        domain valid (slotKeySet slots' length) ∧
      out.scalar.core.ptrs 20=free+(if v.val ∈ valid ∧ v.val ∉ slotKeySet slots length then 3 else 0) ∧
      out.scalar.core.ptrs 0=0 ∧ (∀ z ∈ queueCells base length feet', z < out.scalar.core.ptrs 20) ∧
      (∀ r ∈ ({13,25,40,50,87,88} : Finset ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r) ∧
      out.scalar.core.regs 20=q ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      queueCells base length feet' ⊆ nodeCells free ∪ queueCells base length feet ∧
      (∀ other : Fin n, ∀ field < width, field ≠ flagOffset → out.scalar.integerMemory (vertexRecordAddress width other.val field)=st.scalar.integerMemory (vertexRecordAddress width other.val field)) ∧
      (∀ z, 0 ≤ z → z < free → z ∉ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let pre := payUnit (pointerWrite st 41 (width : ℤ))
  have ep : MachineEval m g ω (coreCode (.pcopy 41 50)) st 1 pre := by
    simpa only [pre,coreCode,hw] using pcopy_eval m g ω st 41 50 hh
  have hp0 := (ep.pointer_frame 0 (by decide)).trans hz
  have hp40 := (ep.pointer_frame 40 (by decide)).trans hvertex
  have hp41 : pre.scalar.core.ptrs 41=(width : ℤ) := by simp [pre,payUnit,pcSet,pointerWrite]
  have hp87 := (ep.pointer_frame 87 (by decide)).trans hlevel
  have hp20 := (ep.real_register_frame 20 (by decide)).trans hq
  obtain ⟨u,mid,em,huSteps,hm23,hmTest,hmI,hmR,hmQ,hmW,hmO,hmH⟩ := exterior_eligibility_exec m g ω pre hh
    width v.val levelBase q hp0 hp40 hp41 hp87 hp20 (hdata.activeNonnegative v hv)
  have hmValid : 0 < mid.scalar.core.regs 23 ↔ v.val ∈ valid := hmTest.trans (hdata.eligibility v hv).symm
  have hm0 := (em.pointer_frame 0 (by decide)).trans hp0
  have hm13 := (em.pointer_frame 13 (by decide)).trans ((ep.pointer_frame 13 (by decide)).trans hb)
  have hm20 := (em.pointer_frame 20 (by decide)).trans ((ep.pointer_frame 20 (by decide)).trans hf)
  have hm40 := (em.pointer_frame 40 (by decide)).trans hp40
  have hm41 := (em.pointer_frame 41 (by decide)).trans hp41
  have hm88 := (em.pointer_frame 88 (by decide)).trans ((ep.pointer_frame 88 (by decide)).trans hFlagOffset)
  have hmQueue : RankArrayRep mid.scalar.integerMemory base length slots roots feet := by rw [hmI]; exact hqueue
  have hmData : ExteriorQueueMemory mid.scalar.integerMemory mid.scalar.core.mem width levelBase flagOffset q domain valid (slotKeySet slots length) := by rw [hmI,hmR]; exact hdata
  by_cases hValid : v.val ∈ valid
  · obtain ⟨t,out,ss,rr,ff,et,ht,hqo,hKeys,hMass,hUnique,hoData,ho20,ho0,hoBelow,hoCtx,hoR,hoOwned,hoFields,hoPos,hoQ,hoW,hoO,hoH⟩ :=
      queued_insert_exec m g ω (payUnit mid) hmH width levelBase flagOffset hflag hactive hneqActive hneqDegree base free length N R
        slots roots feet q domain valid v hv hmQueue hmData hm0 hm13 hm20 hfree hm40 hm41 hm88 hbelow hu hmass hcap hpow
    have eb : MachineEval m g ω (.branchReal 23 .skip queuedInsertCode) mid (1+t+1) (payUnit out) :=
      MachineEval.realPos hmH (not_le.mpr (hmValid.mpr hValid)) et
    have eRun := MachineEval.seq ep (MachineEval.seq em eb)
    refine ⟨1+(u+(1+t+1)),payUnit out,ss,rr,ff,eRun,by omega,hqo,?_,?_,hUnique,hoData,?_,ho0,hoBelow,?_,?_,
      hoR.trans hmR,hoOwned,
      (fun other field hfield hne => (hoFields other field hfield hne).trans (congrFun hmI _)),
      (fun z hz hzF hn => (hoPos z hz hzF hn).trans (congrFun hmI z)),?_,?_,hoO.trans hmO,hoH⟩
    · simpa only [if_pos hValid] using hKeys
    · rw [hMass]
      by_cases hmem : v.val ∈ slotKeySet slots length <;> simp [hValid,hmem]
    · change out.scalar.core.ptrs 20= _
      rw [ho20]
      by_cases hmem : v.val ∈ slotKeySet slots length <;> simp [hValid,hmem]
    · intro r hr
      exact eRun.pointer_frame r (by revert r; decide)
    · exact (eRun.real_register_frame 20 (by decide)).trans hq
    · exact eRun.query_frame (by decide)
    · change out.work+1= _
      rw [hoW,payUnit_work,hmW]
      change st.work+1+u+1+t+1= _
      push_cast
      ring
  · have hg : mid.scalar.core.regs 23 ≤ 0 := le_of_not_gt (fun h => hValid (hmValid.mp h))
    have eb : MachineEval m g ω (.branchReal 23 .skip queuedInsertCode) mid 1 (payUnit mid) :=
      MachineEval.realNonpos hmH hg (MachineEval.skip (payUnit mid))
    have eRun := MachineEval.seq ep (MachineEval.seq em eb)
    refine ⟨1+(u+1),payUnit mid,slots,roots,feet,eRun,by omega,hmQueue,by simp [hValid],by simp [hValid],hu,hmData,
      ?_,hm0,?_,?_,?_,hmR,Finset.subset_union_right,
      (fun other field hfield hne => congrFun hmI _),(fun z hz hzF hn => congrFun hmI z),?_,?_,hmO,hmH⟩
    · simpa [payUnit_ptrs,hValid] using hm20
    · intro z hz'
      change z < mid.scalar.core.ptrs 20
      rw [hm20]
      exact hbelow z hz'
    · intro r hr
      exact eRun.pointer_frame r (by revert r; decide)
    · exact (eRun.real_register_frame 20 (by decide)).trans hq
    · exact eRun.query_frame (by decide)
    · change mid.work+1= _
      rw [hmW]
      change st.work+1+u+1= _
      push_cast
      ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorRefreshObject

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 3000000 in
lemma exterior_refresh_object_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width levelBase flagOffset length N R : ℕ)
    (hflag : flagOffset < width) (hactive : levelBase+2 < width)
    (hneqActive : flagOffset ≠ levelBase+2) (hneqDegree : flagOffset ≠ 0)
    (base floor : ℤ) (hfloor : 2 ≤ floor) (q : ℝ) (domain : Finset (Fin n)) (valid : Finset ℕ)
    (obj : RankQueueObject st.scalar.integerMemory base length (st.scalar.core.ptrs 20) floor)
    (ctx : ExteriorQueueContext st width levelBase flagOffset length base floor q)
    (hdata : ExteriorQueueMemory st.scalar.integerMemory st.scalar.core.mem width levelBase flagOffset q domain valid obj.keys)
    (v : Fin n) (hv : v ∈ domain) (hvertex : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hmass : obj.mass ≤ N) (hcap : R < length) (hpow : N < 2^R) :
    ∃ steps out, ∃ next : RankQueueObject out.scalar.integerMemory base length (out.scalar.core.ptrs 20) floor,
      MachineEval m g ω exteriorQueueRefreshCode st steps out ∧ steps ≤ 21*R+20*width+70 ∧
      ExteriorQueueContext out width levelBase flagOffset length base floor q ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase flagOffset q domain valid next.keys ∧
      next.keys=(if v.val ∈ valid then insert v.val obj.keys else obj.keys) ∧ next.mass ≤ obj.mass+1 ∧
      st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 ∧ out.scalar.core.ptrs 20 ≤ st.scalar.core.ptrs 20+3 ∧
      next.cells ⊆ nodeCells (st.scalar.core.ptrs 20) ∪ obj.cells ∧
      (∀ other : Fin n, ∀ field < width, field ≠ flagOffset → out.scalar.integerMemory (vertexRecordAddress width other.val field)=st.scalar.integerMemory (vertexRecordAddress width other.val field)) ∧
      (∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 → z ∉ obj.cells → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨u,out,ss,rr,ff,ex,hu,hRep,hKeys,hMass,hUnique,hData,h20,h0,hBelow,hCtx,hq,hR,hOwned,hFields,hPos,hQ,hW,hO,hH⟩ :=
    exterior_queue_refresh_weak_exec m g ω st hh width levelBase flagOffset hflag hactive hneqActive hneqDegree
      base (st.scalar.core.ptrs 20) length N R obj.slots obj.roots obj.feet q domain valid v hv
      obj.representation hdata ctx.zero ctx.basePointer rfl (hfloor.trans ctx.floorBound) hvertex ctx.widthPointer ctx.levelPointer ctx.flagPointer
      ctx.threshold obj.below obj.unique hmass hcap hpow
  let newObj : RankQueueObject out.scalar.integerMemory base length (out.scalar.core.ptrs 20) floor := {
    slots := ss
    roots := rr
    feet := ff
    representation := hRep
    unique := hUnique
    below := hBelow
    above := by
      intro z hz
      rcases Finset.mem_union.mp (hOwned hz) with hn|ho
      · have hm := (nodeCells_mem_iff (st.scalar.core.ptrs 20) z).mp hn
        have hf := ctx.floorBound
        omega
      · exact obj.above z ho
  }
  have newCtx : ExteriorQueueContext out width levelBase flagOffset length base floor q := {
    zero := h0
    basePointer := (hCtx 13 (by simp)).trans ctx.basePointer
    lengthPointer := (hCtx 25 (by simp)).trans ctx.lengthPointer
    widthPointer := (hCtx 50 (by simp)).trans ctx.widthPointer
    levelPointer := (hCtx 87 (by simp)).trans ctx.levelPointer
    flagPointer := (hCtx 88 (by simp)).trans ctx.flagPointer
    threshold := hq
    floorBound := by rw [h20]; have hf := ctx.floorBound; split_ifs <;> omega
  }
  refine ⟨u,out,newObj,ex,hu,newCtx,hData,hKeys,?_,?_,?_,hOwned,hFields,hPos,hR,hQ,hW,hO,hH⟩
  · change slotMass ss length ≤ slotMass obj.slots length+1
    rw [hMass]; split_ifs <;> omega
  · rw [h20]; split_ifs <;> omega
  · rw [h20]; split_ifs <;> omega

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderTo

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1600000 in
lemma level_header_integer_to_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level slot target : ℕ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω (levelHeaderIntegerToCode slot target) st 10 out ∧
      out.scalar.core.ptrs target=st.scalar.integerMemory (levelHeaderAddress level slot) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+10 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a105,a40,a41,aI,aR,aW,aO,aH⟩ := level_header_integer_load_exec m g ω st hh level slot hl
  let out := payUnit (pointerWrite a target (st.scalar.integerMemory (levelHeaderAddress level slot)))
  have eb : MachineEval m g ω (coreCode (.pcopy target 105)) a 1 out := by
    simpa only [out,coreCode,a105] using pcopy_eval m g ω a target 105 aH
  refine ⟨out,MachineEval.seq ea eb,by simp [out,payUnit,pcSet,pointerWrite],aI,aR,?_,aO,aH⟩
  change a.work+1= _
  rw [aW]; norm_num; ring

set_option maxHeartbeats 1600000 in
lemma level_header_real_to_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level slot target : ℕ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) (h1 : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω (levelHeaderRealToCode slot target) st 10 out ∧
      out.scalar.core.regs target=st.scalar.core.mem (levelHeaderAddress level slot) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+10 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a10,a40,a41,aI,aR,aW,aO,aH⟩ := level_header_real_load_exec m g ω st hh level slot hl
  have a31 := (ea.real_register_frame 31 (by simp [levelHeaderRealLoadCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
    linearCode,sequenceCode,coreCode,MachineCode.registerTargets,registerTargets])).trans h1
  let out := payUnit (realWrite a target (st.scalar.core.mem (levelHeaderAddress level slot)))
  have eb : MachineEval m g ω (coreCode (.mul target 10 31)) a 1 out := by
    simpa only [out,coreCode,RealOperation.instruction,RealOperation.value,a10,a31,mul_one] using
      binary_eval m g ω a .mul target 10 31 aH
  refine ⟨out,MachineEval.seq ea eb,by simp [out,payUnit,pcSet,realWrite],aI,aR,?_,aO,aH⟩
  change a.work+1= _
  rw [aW]; norm_num; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelVertexFlagClear

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma level_vertex_offset_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base offset : ℕ) (hb : st.scalar.core.ptrs 87=(base : ℤ)) :
    ∃ out, MachineEval m g ω (levelVertexOffsetCode offset) st 2 out ∧
      out.scalar.core.ptrs 88=((base+offset : ℕ) : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+2 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω (levelVertexOffsetInstructions offset)
    (by simp [levelVertexOffsetInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,levelVertexOffsetInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hb]

set_option maxHeartbeats 1600000 in
lemma level_vertex_flag_clear_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex base offset : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hb : st.scalar.core.ptrs 87=(base : ℤ)) :
    ∃ out, MachineEval m g ω (levelVertexFlagClearCode offset) st (4*width+11) out ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (vertexRecordAddress width vertex (base+offset)) 0 ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.regs=st.scalar.core.regs ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*width+11 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a88,aI,aR,aW,aO,aH⟩ := level_vertex_offset_exec m g ω st hh base offset hb
  have a0 := (ea.pointer_frame 0 (by simp [levelVertexOffsetCode,linearCode,levelVertexOffsetInstructions,sequenceCode,MachineCode.pointerTargets,pointerTargets])).trans hz
  have a40 := (ea.pointer_frame 40 (by simp [levelVertexOffsetCode,linearCode,levelVertexOffsetInstructions,sequenceCode,MachineCode.pointerTargets,pointerTargets])).trans hv
  have a41 := (ea.pointer_frame 41 (by simp [levelVertexOffsetCode,linearCode,levelVertexOffsetInstructions,sequenceCode,MachineCode.pointerTargets,pointerTargets])).trans hw
  obtain ⟨out,eb,bI,bR,bRegs,bQ,bW,bO,bH⟩ := vertex_flag_clear_exec m g ω a aH width vertex (base+offset) a0 a40 a41 a88
  have ex : MachineEval m g ω (levelVertexFlagClearCode offset) st (4*width+11) out := by
    have e := MachineEval.seq ea eb
    convert e using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,?_,bR.trans aR,?_,?_,?_,bO.trans aO,bH⟩
  · rw [bI,aI]
  · exact bRegs.trans (ea.register_frame (by simp [levelVertexOffsetCode,levelVertexOffsetInstructions,linearCode,sequenceCode,MachineCode.allAtoms,registerReadOnly]))
  · rw [bQ]; exact ea.query_frame (by simp [levelVertexOffsetCode,levelVertexOffsetInstructions,linearCode,sequenceCode,MachineCode.allAtoms,queryReadOnly])
  · rw [bW,aW]; push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameQueueContext

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderIntegerToCode_pointer_context (slot r : ℕ) (hr : r ∈ ([0,20,25,31,40,41,50,87,89,100] : List ℕ)) :
    r ∉ (levelHeaderIntegerToCode slot 13).pointerTargets := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [levelHeaderIntegerToCode,levelHeaderIntegerLoadCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
      linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets]
lemma levelHeaderRealToCode_pointer_context (slot r : ℕ) (hr : r ∈ ([0,13,18,20,25,40,41,50,87,89,100] : List ℕ)) :
    r ∉ (levelHeaderRealToCode slot 20).pointerTargets := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [levelHeaderRealToCode,levelHeaderRealLoadCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
      linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameQueueContextExecution

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2200000 in
lemma frame_queue_context_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level width length queueSlot scalarSlot : ℕ)
    (base : ℤ) (threshold : ℝ) (hl : st.scalar.core.ptrs 100=(level : ℤ))
    (hw : st.scalar.core.ptrs 50=(width : ℤ)) (hLen : st.scalar.integerMemory 5=(length : ℤ))
    (hBase : st.scalar.integerMemory (levelHeaderAddress level queueSlot)=base)
    (hScalar : st.scalar.core.mem (levelHeaderAddress level scalarSlot)=threshold) (h1 : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω (frameQueueContextCode queueSlot scalarSlot) st 31 out ∧
      out.scalar.core.ptrs 13=base ∧ out.scalar.core.ptrs 25=(length : ℤ) ∧ out.scalar.core.ptrs 18=(length : ℤ) ∧
      out.scalar.core.ptrs 87=((16*(level+1) : ℕ) : ℤ) ∧ out.scalar.core.ptrs 89=((16*(level+1) : ℕ) : ℤ) ∧
      out.scalar.core.ptrs 41=(width : ℤ) ∧ out.scalar.core.regs 20=threshold ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+31 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a87,a89,a41,aI,aR,aQ,aW,aO,aH⟩ := level_context_exec m g ω st hh level width hl hw
  have a100 := (ea.pointer_frame 100 (by decide)).trans hl
  obtain ⟨b,eb,b13,bI,bR,bW,bO,bH⟩ := level_header_integer_to_exec m g ω a aH level queueSlot 13 a100
  have b13' : b.scalar.core.ptrs 13=base := by rw [b13,aI]; exact hBase
  have bLen : b.scalar.integerMemory 5=(length : ℤ) := by rw [bI,aI]; exact hLen
  obtain ⟨c,ec,c18,c25,cI,cR,cQ,cW,cO,cH⟩ := frame_rank_load_exec m g ω b bH length bLen
  have b100 := (eb.pointer_frame 100 (levelHeaderIntegerToCode_pointer_context queueSlot 100 (by simp))).trans a100
  have c100 := (ec.pointer_frame 100 (by decide)).trans b100
  have c31 : c.scalar.core.regs 31=1 := by
    rw [ec.real_register_frame 31 (by decide),eb.real_register_frame 31 (by simp [levelHeaderIntegerToCode,levelHeaderIntegerLoadCode,
      levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,coreCode,MachineCode.registerTargets,registerTargets]),ea.real_register_frame 31 (by decide)]
    exact h1
  obtain ⟨out,ed,d20,dI,dR,dW,dO,dH⟩ := level_header_real_to_exec m g ω c cH level scalarSlot 20 c100 c31
  have ex : MachineEval m g ω (frameQueueContextCode queueSlot scalarSlot) st 31 out := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  have d20' : out.scalar.core.regs 20=threshold := by rw [d20,cR,bR,aR]; exact hScalar
  have hPost (r : ℕ) (hr : r ∈ ([87,89,41] : List ℕ)) : out.scalar.core.ptrs r=a.scalar.core.ptrs r := by
    have he : r ∈ ([0,20,25,31,40,41,50,87,89,100] : List ℕ) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      tauto
    have hd : r ∈ ([0,13,18,20,25,40,41,50,87,89,100] : List ℕ) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      tauto
    rw [ed.pointer_frame r (levelHeaderRealToCode_pointer_context scalarSlot r hd)]
    rw [ec.pointer_frame r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl|rfl <;> decide)]
    exact eb.pointer_frame r (levelHeaderIntegerToCode_pointer_context queueSlot r he)
  refine ⟨out,ex,?_,?_,?_,(hPost 87 (by simp)).trans a87,(hPost 89 (by simp)).trans a89,
    (hPost 41 (by simp)).trans a41,d20',dI.trans (cI.trans (bI.trans aI)),dR.trans (cR.trans (bR.trans aR)),?_,dO.trans (cO.trans (bO.trans aO)),dH⟩
  · exact (ed.pointer_frame 13 (levelHeaderRealToCode_pointer_context scalarSlot 13 (by simp))).trans ((ec.pointer_frame 13 (by decide)).trans b13')
  · exact (ed.pointer_frame 25 (levelHeaderRealToCode_pointer_context scalarSlot 25 (by simp))).trans c25
  · exact (ed.pointer_frame 18 (levelHeaderRealToCode_pointer_context scalarSlot 18 (by simp))).trans c18
  · rw [dW,cW,bW,aW]; norm_num; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorFrameContextExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 1800000 in
lemma exterior_frame_context_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level width length : ℕ) (base floor : ℤ) (q : ℝ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) (hw : st.scalar.core.ptrs 50=(width : ℤ))
    (hLen : st.scalar.integerMemory 5=(length : ℤ))
    (hBase : st.scalar.integerMemory (levelHeaderAddress level 7)=base)
    (hScalar : st.scalar.core.mem (levelHeaderAddress level 1)=q) (h1 : st.scalar.core.regs 31=1)
    (hz : st.scalar.core.ptrs 0=0) (hf : floor ≤ st.scalar.core.ptrs 20) :
    ∃ out, MachineEval m g ω exteriorFrameContextCode st 33 out ∧
      ExteriorQueueContext out width (16*(level+1)) (16*(level+1)+3) length base floor q ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.core.ptrs 20=st.scalar.core.ptrs 20 ∧
      out.work=st.work+33 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a13,a25,a18,a87,a89,a41,a20,aI,aR,aW,aO,aH⟩ := frame_queue_context_exec m g ω st hh level width length 7 1 base q hl hw hLen hBase hScalar h1
  obtain ⟨out,eb,b88,bI,bR,bW,bO,bH⟩ := level_vertex_offset_exec m g ω a aH (16*(level+1)) 3 a87
  have ex : MachineEval m g ω exteriorFrameContextCode st 33 out := MachineEval.seq ea eb
  have hptr (r : ℕ) (hr : r ∈ ([0,20,100] : List ℕ)) : out.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    apply ex.pointer_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl <;> decide
  have ctx : ExteriorQueueContext out width (16*(level+1)) (16*(level+1)+3) length base floor q := {
    zero := (hptr 0 (by simp)).trans hz
    basePointer := (eb.pointer_frame 13 (by decide)).trans a13
    lengthPointer := (eb.pointer_frame 25 (by decide)).trans a25
    widthPointer := (ex.pointer_frame 50 (by decide)).trans hw
    levelPointer := (eb.pointer_frame 87 (by decide)).trans a87
    flagPointer := b88
    threshold := (eb.real_register_frame 20 (by decide)).trans a20
    floorBound := by rw [hptr 20 (by simp)]; exact hf
  }
  refine ⟨out,ex,ctx,bI.trans aI,bR.trans aR,hptr 20 (by simp),?_,bO.trans aO,bH⟩
  rw [bW,aW]; norm_num; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveFrameOwnership

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma RecursiveFrameMemory.owned_above {n : ℕ} {g : InputGraph n} {logical : RecursiveState n}
    {j width length : ℕ} {machine : MachineState} {floor : ℤ}
    (f : RecursiveFrameMemory g logical j width length machine floor) : ∀ z ∈ f.owned, floor ≤ z := by
  intro z hz
  rcases Finset.mem_union.mp hz with habc|hd
  · rcases Finset.mem_union.mp habc with hab|hc
    · rcases Finset.mem_union.mp hab with ha|hb
      · exact f.activeAbove z ha
      · exact f.cacheAbove z hb
    · exact f.exteriorObject.above z hc
  · exact f.highObject.above z hd

lemma RecursiveFrameMemory.owned_below {n : ℕ} {g : InputGraph n} {logical : RecursiveState n}
    {j width length : ℕ} {machine : MachineState} {floor : ℤ}
    (f : RecursiveFrameMemory g logical j width length machine floor) : ∀ z ∈ f.owned, z < machine.scalar.core.ptrs 20 := by
  intro z hz
  rcases Finset.mem_union.mp hz with habc|hd
  · rcases Finset.mem_union.mp habc with hab|hc
    · rcases Finset.mem_union.mp hab with ha|hb
      · exact f.activeBelow z ha
      · exact f.cacheBelow z hb
    · exact f.exteriorObject.below z hc
  · exact f.highObject.below z hd

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OwnedFIFOFrames

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma VertexListRep.positive_cells {n : ℕ} {I : ℤ → ℤ} {head : ℤ} {vertices : List (Fin n)} {F : Finset ℤ}
    (h : VertexListRep I head vertices F) : ∀ z ∈ F, 2 ≤ z := ForestRep.positive_cells h

lemma owned_positive_frame {I J : ℤ → ℤ} {F Q : Finset ℤ} {free : ℤ}
    (hp : ∀ z ∈ F, 0 ≤ z) (hf : ∀ z ∈ F, z < free) (hd : Disjoint F Q)
    (he : ∀ z, 0 ≤ z → z < free → z ∉ Q → J z=I z) : ∀ z ∈ F, J z=I z := by
  intro z hz
  exact he z (hp z hz) (hf z hz) (fun hq => Finset.disjoint_left.mp hd hz hq)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueueObjectFrames

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma vertex_list_queue_frame {n : ℕ} {I J : ℤ → ℤ} {head free : ℤ} {vertices : List (Fin n)} {F Q : Finset ℤ}
    (list : VertexListRep I head vertices F) (hBelow : ∀ z ∈ F, z < free) (hSep : Disjoint F Q)
    (hFrame : ∀ z, 0 ≤ z → z < free → z ∉ Q → J z=I z) : VertexListRep J head vertices F := by
  apply list.frame
  apply owned_positive_frame (fun z hz => by have := list.positive_cells z hz; omega) hBelow hSep hFrame

def RankQueueObject.other_frame {I J : ℤ → ℤ} {base free nextFree floor : ℤ} {length : ℕ}
    (other : RankQueueObject I base length free floor) (Q : Finset ℤ) (hFloor : 2 ≤ floor)
    (hSep : Disjoint other.cells Q) (hFree : free ≤ nextFree)
    (hFrame : ∀ z, 0 ≤ z → z < free → z ∉ Q → J z=I z) : RankQueueObject J base length nextFree floor :=
  other.frame (owned_positive_frame (fun z hz => by have := other.above z hz; omega) other.below hSep hFrame) hFree

lemma queue_disjoint_after_growth {F Q next : Finset ℤ} {free : ℤ}
    (hBelow : ∀ z ∈ F, z < free) (hSep : Disjoint F Q)
    (hOld : ∀ z ∈ next, z < free → z ∈ Q) : Disjoint F next := by
  apply Finset.disjoint_left.mpr
  intro z hz hn
  exact Finset.disjoint_left.mp hSep hz (hOld z hn (hBelow z hz))

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveFrameControl

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def RecursiveFrameMemory.control_frame {n : ℕ} {g : InputGraph n} {a b : RecursiveState n}
    {j width length : ℕ} {st out : MachineState} {floor : ℤ}
    (f : RecursiveFrameMemory g a j width length st floor)
    (pc : NormalizePC) (budget need : Bool) (children : ℕ)
    (hFrame : b.frames j={a.frames j with pc := pc,openBudget := budget,needFull := need,childrenThisEpisode := children})
    (hDomain : parentDomain b j=parentDomain a j)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hHeaderI : ∀ slot < 32, slot ∉ ([0,9,10,11] : List ℕ) →
      out.scalar.integerMemory (levelHeaderAddress j slot)=st.scalar.integerMemory (levelHeaderAddress j slot))
    (hHeaderR : ∀ slot < 32, out.scalar.core.mem (levelHeaderAddress j slot)=st.scalar.core.mem (levelHeaderAddress j slot))
    (hPC : out.scalar.integerMemory (levelHeaderAddress j 0)=(normalizePCNumber pc : ℤ))
    (hBudget : out.scalar.integerMemory (levelHeaderAddress j 9)=if budget then 1 else 0)
    (hNeed : out.scalar.integerMemory (levelHeaderAddress j 10)=if need then 1 else 0)
    (hChildren : out.scalar.integerMemory (levelHeaderAddress j 11)=(children : ℤ))
    (hFieldsI : ∀ v ∈ parentDomain a j, ∀ field < 16*(j+1)+7,
      out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field))
    (hFieldsR : ∀ v ∈ parentDomain a j, ∀ field < 16*(j+1)+7,
      out.scalar.core.mem (vertexRecordAddress width v.val field)=st.scalar.core.mem (vertexRecordAddress width v.val field))
    (hOwned : ∀ z ∈ f.owned, out.scalar.integerMemory z=st.scalar.integerMemory z) :
    RecursiveFrameMemory g b j width length out floor := by
  let ext := f.exteriorObject.frame
    (fun z hz => hOwned z (Finset.mem_union_left _ (Finset.mem_union_right _ hz))) hFree
  let high := f.highObject.frame (fun z hz => hOwned z (Finset.mem_union_right _ hz)) hFree
  refine {
    N := by simpa only [hFrame] using (hHeaderR 0 (by decide)).trans f.N
    q := by simpa only [hFrame] using (hHeaderR 1 (by decide)).trans f.q
    Q := by simpa only [hFrame] using (hHeaderR 3 (by decide)).trans f.Q
    W := by simpa only [hFrame] using (hHeaderR 4 (by decide)).trans f.W
    theta := by simpa only [hFrame] using (hHeaderR 5 (by decide)).trans f.theta
    block := by simpa only [hFrame] using (hHeaderI 14 (by decide) (by decide)).trans f.block
    pc := by simpa only [hFrame] using hPC
    openBudget := by simpa only [hFrame] using hBudget
    needFull := by simpa only [hFrame] using hNeed
    children := by simpa only [hFrame] using hChildren
    reference := by rw [hDomain,hFrame]; exact fun v hv => (hFieldsR v hv _ (by omega)).trans (f.reference v hv)
    residual := by rw [hDomain,hFrame]; exact fun v hv => (hFieldsR v hv _ (by omega)).trans (f.residual v hv)
    activeFlags := by rw [hDomain,hFrame]; exact fun v hv => (hFieldsI v hv _ (by omega)).trans (f.activeFlags v hv)
    cacheFlags := by rw [hDomain,hFrame]; exact fun v hv => (hFieldsI v hv _ (by omega)).trans (f.cacheFlags v hv)
    activeVertices := f.activeVertices
    activeFoot := f.activeFoot
    activeRep := ?_
    activeNodup := f.activeNodup
    activeSet := by rw [hFrame]; exact f.activeSet
    activeCount := by simpa only [hFrame] using (hHeaderI 3 (by decide) (by decide)).trans f.activeCount
    activeVolume := by simpa only [hFrame] using (hHeaderI 2 (by decide) (by decide)).trans f.activeVolume
    activeBelow := fun z hz => (f.activeBelow z hz).trans_le hFree
    activeAbove := f.activeAbove
    cacheVertices := f.cacheVertices
    cacheFoot := f.cacheFoot
    cacheRep := ?_
    cacheNodup := f.cacheNodup
    cacheSet := by rw [hFrame]; exact f.cacheSet
    cacheCount := by simpa only [hFrame] using (hHeaderI 5 (by decide) (by decide)).trans f.cacheCount
    cacheVolume := by simpa only [hFrame] using (hHeaderI 6 (by decide) (by decide)).trans f.cacheVolume
    cacheBelow := fun z hz => (f.cacheBelow z hz).trans_le hFree
    cacheAbove := f.cacheAbove
    exteriorBase := f.exteriorBase
    highBase := f.highBase
    exteriorPointer := (hHeaderI 7 (by decide) (by decide)).trans f.exteriorPointer
    highPointer := (hHeaderI 8 (by decide) (by decide)).trans f.highPointer
    exteriorObject := ext
    highObject := high
    exteriorData := ?_
    exteriorCover := by rw [hFrame]; exact f.exteriorCover
    highBoolean := ?_
    virtualExcluded := by rw [hDomain]; exact fun v hv => (hFieldsI v hv _ (by omega)).trans (f.virtualExcluded v hv)
    highFlags := ?_
    highDomain := by rw [hDomain]; exact f.highDomain
    highValid := ?_
    highCover := by rw [hFrame]; exact f.highCover
  }
  · rw [hHeaderI 1 (by decide) (by decide)]
    apply f.activeRep.frame
    intro z hz
    apply hOwned
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hz))
  · rw [hHeaderI 4 (by decide) (by decide)]
    apply f.cacheRep.frame
    intro z hz
    apply hOwned
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hz))
  · rw [hFrame,hDomain]
    refine ⟨f.exteriorData.queuedDomain,?_,?_,?_⟩
    · intro v hv
      rw [hFieldsI v hv _ (by omega)]
      exact f.exteriorData.flags v hv
    · intro v hv
      rw [hFieldsI v hv _ (by omega)]
      exact f.exteriorData.activeNonnegative v hv
    · intro v hv
      rw [hFieldsI v hv _ (by omega),hFieldsI v hv 0 (by omega),hFieldsR v hv _ (by omega)]
      exact f.exteriorData.eligibility v hv
  · rw [hFrame,hDomain]
    intro v hv
    rw [hFieldsR v hv _ (by omega),hFieldsI v hv _ (by omega),hFieldsI v hv 0 (by omega),hFieldsR v hv _ (by omega)]
    exact f.highBoolean v hv
  · rw [hDomain]
    intro v hv
    rw [hFieldsI v hv _ (by omega)]
    exact f.highFlags v hv
  · rw [hFrame,hDomain]
    intro v hv
    rw [hFieldsI v hv _ (by omega),hFieldsI v hv 0 (by omega),hFieldsR v hv _ (by omega)]
    exact f.highValid v hv

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MachinePendingKeys

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

structure MachinePendingKeys {n : ℕ} (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (logical : RecursiveState n) (machine : MachineState) where
  zero : machine.scalar.core.ptrs 0=0
  top : machine.scalar.core.ptrs 100=(logical.top : ℤ)
  width : machine.scalar.core.ptrs 50=((16*(ell+3) : ℕ) : ℤ)
  alphaRegister : machine.scalar.core.regs 30=α
  one : machine.scalar.core.regs 31=1
  alphaMemory : machine.scalar.core.mem 0=α
  epsilonMemory : machine.scalar.core.mem 1=ε
  depthMemory : machine.scalar.integerMemory 2=((ell+2 : ℕ) : ℤ)
  lengthMemory : machine.scalar.integerMemory 5=(length : ℤ)
  seedMemory : machine.scalar.integerMemory 0=(s.val : ℤ)
  allocator : 128+32*((ell+2 : ℕ) : ℤ) ≤ machine.scalar.core.ptrs 20
  potential : ∀ v : Fin n, machine.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val 0)=logical.x v
  seedMarker : ∀ v : Fin n, machine.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val 2)=LocalPush.e s v
  boundary : machine.scalar.integerMemory 7=logical.boundaryEdges
  graphCache : GraphCache g machine.scalar.integerMemory (16*(ell+3)) logical.stored (machine.scalar.core.ptrs 20)
  rowAbove : ∀ v ∈ logical.stored,
    128+32*((ell+2 : ℕ) : ℤ) ≤ machine.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 1)
  knownDegree : ∀ v ∈ recursiveDegreeDomain g s logical,
    machine.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)=((g.neighbors v).length : ℤ)
  unknownDegree : ∀ v ∉ recursiveDegreeDomain g s logical,
    machine.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)=0
  frames : ∀ j ≤ logical.top, FramePendingKeys g logical j (16*(ell+3)) length machine (128+32*((ell+2 : ℕ) : ℤ))
  pieceSeparation : ∀ j, ∀ hj : j ≤ logical.top,
    ((frames j hj).pieces).Pairwise Disjoint
  frameSeparation : ∀ i, ∀ hi : i ≤ logical.top, ∀ j, ∀ hj : j ≤ logical.top, i ≠ j →
    Disjoint (frames i hi).owned (frames j hj).owned
  cacheSeparation : ∀ j, ∀ hj : j ≤ logical.top,
    Disjoint (frames j hj).owned (cachedRowCells g machine.scalar.integerMemory (16*(ell+3)) logical.stored)
  output : machine.output=[]

namespace MachinePendingKeys

end MachinePendingKeys
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EligibleInsertList

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def eligibleInsertList {n : ℕ} (valid queued : Finset ℕ) (vertices : List (Fin n)) : Finset ℕ :=
  vertices.foldl (fun Q v => if v.val ∈ valid then insert v.val Q else Q) queued

lemma eligible_insert_list_eq {n : ℕ} (valid queued : Finset ℕ) (vertices : List (Fin n)) :
    eligibleInsertList valid queued vertices=queued ∪ (valid ∩ (vertices.map Fin.val).toFinset) := by
  classical
  induction vertices generalizing queued with
  | nil => simp [eligibleInsertList]
  | cons v rest ih =>
    change eligibleInsertList valid (if v.val ∈ valid then insert v.val queued else queued) rest= _
    rw [ih]
    ext x
    by_cases hv : v.val ∈ valid <;> by_cases hx : x=v.val <;> simp_all

lemma eligible_insert_list_complete {n : ℕ} (valid : Finset ℕ) (vertices : List (Fin n))
    (hv : valid ⊆ (vertices.map Fin.val).toFinset) : eligibleInsertList valid ∅ vertices=valid := by
  rw [eligible_insert_list_eq]
  simp only [Finset.empty_union]
  exact Finset.inter_eq_left.mpr hv

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HighBooleanMemoryUpdate

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma vertex_memory_update_other_field {β : Type} (M : ℤ → β) (width vertex other offset field : ℕ)
    (value : β) (ho : offset < width) (hf : field < width) (hne : field ≠ offset) :
    Function.update M (vertexRecordAddress width vertex offset) value (vertexRecordAddress width other field)=
      M (vertexRecordAddress width other field) := by
  have hn : vertexRecordAddress width other field ≠ vertexRecordAddress width vertex offset := by
    intro he
    exact hne (vertexRecordAddress_injective width other vertex field offset hf ho he).2
  simp only [Function.update_of_ne hn]

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FramePendingScopedTransport

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def FramePendingKeys.scoped_frame {n : ℕ} {g : InputGraph n} {logical : RecursiveState n}
    {j width length : ℕ} {st out : MachineState} {floor : ℤ}
    (f : FramePendingKeys g logical j width length st floor)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hHeaderI : ∀ slot < 32, out.scalar.integerMemory (levelHeaderAddress j slot)=st.scalar.integerMemory (levelHeaderAddress j slot))
    (hHeaderR : ∀ slot < 32, out.scalar.core.mem (levelHeaderAddress j slot)=st.scalar.core.mem (levelHeaderAddress j slot))
    (hFieldsI : ∀ v ∈ parentDomain logical j, ∀ field < 16*(j+1)+7, (field=0 ∨ 16*(j+1) ≤ field) →
      out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field))
    (hFieldsR : ∀ v ∈ parentDomain logical j, ∀ field < 16*(j+1)+7, (field=0 ∨ 16*(j+1) ≤ field) →
      out.scalar.core.mem (vertexRecordAddress width v.val field)=st.scalar.core.mem (vertexRecordAddress width v.val field))
    (hOwned : ∀ z ∈ f.owned, out.scalar.integerMemory z=st.scalar.integerMemory z) :
    FramePendingKeys g logical j width length out floor := by
  let ext := f.exteriorObject.frame
    (fun z hz => hOwned z (Finset.mem_union_left _ (Finset.mem_union_right _ hz))) hFree
  let high := f.highObject.frame (fun z hz => hOwned z (Finset.mem_union_right _ hz)) hFree
  refine {
    N := (hHeaderR 0 (by decide)).trans f.N
    q := (hHeaderR 1 (by decide)).trans f.q
    Q := (hHeaderR 3 (by decide)).trans f.Q
    W := (hHeaderR 4 (by decide)).trans f.W
    theta := (hHeaderR 5 (by decide)).trans f.theta
    block := (hHeaderI 14 (by decide)).trans f.block
    pc := (hHeaderI 0 (by decide)).trans f.pc
    openBudget := (hHeaderI 9 (by decide)).trans f.openBudget
    needFull := (hHeaderI 10 (by decide)).trans f.needFull
    children := (hHeaderI 11 (by decide)).trans f.children
    reference := fun v hv => (hFieldsR v hv _ (by omega) (by omega)).trans (f.reference v hv)
    residual := fun v hv => (hFieldsR v hv _ (by omega) (by omega)).trans (f.residual v hv)
    activeFlags := fun v hv => (hFieldsI v hv _ (by omega) (by omega)).trans (f.activeFlags v hv)
    cacheFlags := fun v hv => (hFieldsI v hv _ (by omega) (by omega)).trans (f.cacheFlags v hv)
    activeVertices := f.activeVertices
    activeFoot := f.activeFoot
    activeRep := ?_
    activeNodup := f.activeNodup
    activeSet := f.activeSet
    activeCount := (hHeaderI 3 (by decide)).trans f.activeCount
    activeVolume := (hHeaderI 2 (by decide)).trans f.activeVolume
    activeBelow := fun z hz => (f.activeBelow z hz).trans_le hFree
    activeAbove := f.activeAbove
    cacheVertices := f.cacheVertices
    cacheFoot := f.cacheFoot
    cacheRep := ?_
    cacheNodup := f.cacheNodup
    cacheSet := f.cacheSet
    cacheCount := (hHeaderI 5 (by decide)).trans f.cacheCount
    cacheVolume := (hHeaderI 6 (by decide)).trans f.cacheVolume
    cacheBelow := fun z hz => (f.cacheBelow z hz).trans_le hFree
    cacheAbove := f.cacheAbove
    exteriorBase := f.exteriorBase
    highBase := f.highBase
    exteriorPointer := (hHeaderI 7 (by decide)).trans f.exteriorPointer
    highPointer := (hHeaderI 8 (by decide)).trans f.highPointer
    exteriorObject := ext
    highObject := high
    exteriorData := ?_
    virtualExcluded := fun v hv => (hFieldsI v hv _ (by omega) (by omega)).trans (f.virtualExcluded v hv)
    highFlags := ?_
    highDomain := f.highDomain
    highValid := ?_
  }
  · rw [hHeaderI 1 (by decide)]
    apply f.activeRep.frame
    intro z hz
    apply hOwned
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hz))
  · rw [hHeaderI 4 (by decide)]
    apply f.cacheRep.frame
    intro z hz
    apply hOwned
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hz))
  · refine ⟨f.exteriorData.queuedDomain,?_,?_,?_⟩
    · intro v hv
      rw [hFieldsI v hv _ (by omega) (by omega)]
      exact f.exteriorData.flags v hv
    · intro v hv
      rw [hFieldsI v hv _ (by omega) (by omega)]
      exact f.exteriorData.activeNonnegative v hv
    · intro v hv
      rw [hFieldsI v hv _ (by omega) (by omega),hFieldsI v hv 0 (by omega) (by omega),hFieldsR v hv _ (by omega) (by omega)]
      exact f.exteriorData.eligibility v hv
  · intro v hv
    rw [hFieldsI v hv _ (by omega) (by omega)]
    exact f.highFlags v hv
  · intro v hv
    rw [hFieldsI v hv _ (by omega) (by omega),hFieldsI v hv 0 (by omega) (by omega),hFieldsR v hv _ (by omega) (by omega)]
    exact f.highValid v hv

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingQueuePotential

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def FramePendingKeys.queueMass {n : ℕ} {g : InputGraph n} {logical : RecursiveState n}
    {j width length : ℕ} {machine : MachineState} {floor : ℤ}
    (frame : FramePendingKeys g logical j width length machine floor) : ℕ :=
  frame.exteriorObject.mass+frame.highObject.mass

def MachinePendingKeys.queueMass {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {machine : MachineState}
    (memory : MachinePendingKeys g s α ε ell length logical machine) : ℕ :=
  ∑ i ∈ Finset.range (logical.top+1), if hi : i ≤ logical.top then (memory.frames i hi).queueMass else 0

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MachinePendingFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def MachinePendingKeys.frame {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st out : MachineState}
    (pm : MachinePendingKeys g s α ε ell length logical st)
    (hI : out.scalar.integerMemory=st.scalar.integerMemory) (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : MachinePendingKeys g s α ε ell length logical out := {
  zero := (hP 0 (by simp)).trans pm.zero
  top := (hP 100 (by simp)).trans pm.top
  width := (hP 50 (by simp)).trans pm.width
  alphaRegister := (hG 30 (by simp)).trans pm.alphaRegister
  one := (hG 31 (by simp)).trans pm.one
  alphaMemory := by rw [hR]; exact pm.alphaMemory
  epsilonMemory := by rw [hR]; exact pm.epsilonMemory
  depthMemory := by rw [hI]; exact pm.depthMemory
  lengthMemory := by rw [hI]; exact pm.lengthMemory
  seedMemory := by rw [hI]; exact pm.seedMemory
  allocator := by rw [hP 20 (by simp)]; exact pm.allocator
  potential := by rw [hR]; exact pm.potential
  seedMarker := by rw [hR]; exact pm.seedMarker
  boundary := by rw [hI]; exact pm.boundary
  graphCache := by rw [hI,hP 20 (by simp)]; exact pm.graphCache
  rowAbove := by rw [hI]; exact pm.rowAbove
  knownDegree := by rw [hI]; exact pm.knownDegree
  unknownDegree := by rw [hI]; exact pm.unknownDegree
  frames := fun i hi => (pm.frames i hi).scoped_frame (by rw [hP 20 (by simp)])
    (by intros; exact congrFun hI _) (by intros; exact congrFun hR _)
    (by intros; exact congrFun hI _) (by intros; exact congrFun hR _) (by intros; exact congrFun hI _)
  pieceSeparation := pm.pieceSeparation
  frameSeparation := pm.frameSeparation
  cacheSeparation := by
    intro i hi
    change Disjoint (pm.frames i hi).owned (cachedRowCells g out.scalar.integerMemory (16*(ell+3)) logical.stored)
    rw [hI]
    exact pm.cacheSeparation i hi
  output := hO.trans pm.output
}

def MachinePendingKeys.payUnit {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st : MachineState}
    (pm : MachinePendingKeys g s α ε ell length logical st) :
    MachinePendingKeys g s α ε ell length logical (NearlyOptimalPPR.Computation.payUnit st) :=
  pm.frame rfl rfl (by intros; rfl) (by intros; rfl) rfl

def MachinePendingKeys.pointerWrite {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st : MachineState}
    (pm : MachinePendingKeys g s α ε ell length logical st) (r : ℕ) (value : ℤ)
    (hr : r ∉ ([0,20,50,100] : List ℕ)) :
    MachinePendingKeys g s α ε ell length logical (NearlyOptimalPPR.Computation.pointerWrite st r value) :=
  pm.frame rfl rfl (by
    intro i hi
    apply Function.update_of_ne
    intro he
    subst i
    exact hr hi) (by intros; rfl) rfl

@[simp] lemma MachinePendingKeys.frame_queueMass {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st out : MachineState}
    (pm : MachinePendingKeys g s α ε ell length logical st)
    (hI : out.scalar.integerMemory=st.scalar.integerMemory) (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : (pm.frame hI hR hP hG hO).queueMass=pm.queueMass := rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingIntegerFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


structure PendingIntegerFrame {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st out : MachineState}
    (old : MachinePendingKeys g s α ε ell length logical st)
    (next : MachinePendingKeys g s α ε ell length logical out) : Prop where
  free : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20
  oldOwned : ∀ i, ∀ hi : i ≤ logical.top, ∀ z ∈ (next.frames i hi).owned,
    z < st.scalar.core.ptrs 20 → z ∈ (old.frames i hi).owned
  integerFrame : ∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 →
    (∀ i, ∀ hi : i ≤ logical.top, z ∉ (old.frames i hi).owned) →
      out.scalar.integerMemory z=st.scalar.integerMemory z
  indexFrame : ∀ v : Fin n,
    out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
      st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)

namespace PendingIntegerFrame

lemma trans {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st mid out : MachineState}
    {old : MachinePendingKeys g s α ε ell length logical st}
    {middle : MachinePendingKeys g s α ε ell length logical mid}
    {next : MachinePendingKeys g s α ε ell length logical out}
    (a : PendingIntegerFrame old middle) (b : PendingIntegerFrame middle next) : PendingIntegerFrame old next := by
  refine ⟨a.free.trans b.free,?_,?_,fun v => (b.indexFrame v).trans (a.indexFrame v)⟩
  · intro i hi z hz hBelow
    exact a.oldOwned i hi z (b.oldOwned i hi z hz (hBelow.trans_le a.free)) hBelow
  · intro z hz hBelow hOutside
    have hMid : ∀ i, ∀ hi : i ≤ logical.top, z ∉ (middle.frames i hi).owned := by
      intro i hi hm
      exact hOutside i hi (a.oldOwned i hi z hm hBelow)
    exact (b.integerFrame z hz (hBelow.trans_le a.free) hMid).trans (a.integerFrame z hz hBelow hOutside)

lemma payUnit {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (pm : MachinePendingKeys g s α ε ell length logical st) :
    PendingIntegerFrame pm pm.payUnit := ⟨le_rfl,by intros i hi z hz; exact fun _ => hz,by intros; rfl,by intros; rfl⟩

lemma frame {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState}
    (pm : MachinePendingKeys g s α ε ell length logical st)
    (hI : out.scalar.integerMemory=st.scalar.integerMemory) (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : PendingIntegerFrame pm (pm.frame hI hR hP hG hO) := by
  refine ⟨le_of_eq (hP 20 (by simp)).symm,?_,?_,fun v => congrFun hI _⟩
  · intro i hi z hz hBelow
    exact hz
  · intro z hz hBelow hOutside
    exact congrFun hI z

lemma pointerWrite {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (pm : MachinePendingKeys g s α ε ell length logical st)
    (r : ℕ) (value : ℤ) (hr : r ∉ ([0,20,50,100] : List ℕ)) :
    PendingIntegerFrame pm (pm.pointerWrite r value hr) := by
  have h20 : (20 : ℕ) ≠ r := by intro he; subst r; simp at hr
  refine ⟨?_,by intros i hi z hz hBelow; exact hz,by intros; rfl,by intros; rfl⟩
  change st.scalar.core.ptrs 20 ≤ Function.update st.scalar.core.ptrs r value 20
  rw [Function.update_of_ne h20]

end PendingIntegerFrame
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingVisitedKeys

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

structure PendingVisitedKeys {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {machine : MachineState}
    (memory : MachinePendingKeys g s α ε ell length logical machine) (visited : Finset (Fin n)) : Prop where
  boolean : ∀ j ≤ logical.top, HighBooleanRecords machine.scalar.integerMemory machine.scalar.core.mem (16*(ell+3)) (16*(j+1))
    (logical.frames j).theta (parentDomain logical j ∩ visited)
  exterior : ∀ j, ∀ hj : j ≤ logical.top, ∀ v ∈ visited, v ∈ (logical.frames j).exterior → v.val ∈ (memory.frames j hj).exteriorObject.keys
  high : ∀ j, ∀ hj : j ≤ logical.top, ∀ v ∈ visited, v ∈ (logical.frames j).high → v.val ∈ (memory.frames j hj).highObject.keys

namespace PendingVisitedKeys

def frame {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState} {visited : Finset (Fin n)}
    {pm : MachinePendingKeys g s α ε ell length logical st} (inv : PendingVisitedKeys pm visited)
    (hI : out.scalar.integerMemory=st.scalar.integerMemory) (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : PendingVisitedKeys (pm.frame hI hR hP hG hO) visited := by
  refine ⟨?_,inv.exterior,inv.high⟩
  rw [hI,hR]
  exact inv.boolean

def payUnit {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} {visited : Finset (Fin n)}
    {pm : MachinePendingKeys g s α ε ell length logical st} (inv : PendingVisitedKeys pm visited) :
    PendingVisitedKeys pm.payUnit visited := ⟨inv.boolean,inv.exterior,inv.high⟩

def pointerWrite {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} {visited : Finset (Fin n)}
    {pm : MachinePendingKeys g s α ε ell length logical st} (inv : PendingVisitedKeys pm visited)
    (r : ℕ) (value : ℤ) (hr : r ∉ ([0,20,50,100] : List ℕ)) :
    PendingVisitedKeys (pm.pointerWrite r value hr) visited := ⟨inv.boolean,inv.exterior,inv.high⟩

end PendingVisitedKeys
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MemoryBufferFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

structure MemoryBufferFrame {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical nextLogical : RecursiveState n} {st out : MachineState}
    (old : RecursiveMachineMemory g s α ε ell length logical st)
    (next : RecursiveMachineMemory g s α ε ell length nextLogical out) : Prop where
  top : nextLogical.top=logical.top
  free : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20
  oldOwned : ∀ i, ∀ hi : i ≤ logical.top, ∀ hn : i ≤ nextLogical.top,
    ∀ z ∈ (next.frames i hn).owned, z < st.scalar.core.ptrs 20 → z ∈ (old.frames i hi).owned
  integerFrame : ∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 →
    (∀ i, ∀ hi : i ≤ logical.top, z ∉ (old.frames i hi).owned) →
      out.scalar.integerMemory z=st.scalar.integerMemory z
  realPositive : ∀ z, 0 ≤ z → out.scalar.core.mem z=st.scalar.core.mem z
  indexFrame : ∀ v : Fin n,
    out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
      st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)

namespace MemoryBufferFrame

lemma trans {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical middleLogical nextLogical : RecursiveState n} {st mid out : MachineState}
    {old : RecursiveMachineMemory g s α ε ell length logical st}
    {middle : RecursiveMachineMemory g s α ε ell length middleLogical mid}
    {next : RecursiveMachineMemory g s α ε ell length nextLogical out}
    (a : MemoryBufferFrame old middle) (b : MemoryBufferFrame middle next) : MemoryBufferFrame old next := by
  refine ⟨b.top.trans a.top,a.free.trans b.free,?_,?_,?_,fun v => (b.indexFrame v).trans (a.indexFrame v)⟩
  · intro i hi hn z hz hBelow
    have hm : i ≤ middleLogical.top := by rw [a.top]; exact hi
    exact a.oldOwned i hi hm z (b.oldOwned i hm hn z hz (hBelow.trans_le a.free)) hBelow
  · intro z hz hBelow hOutside
    have hMid : ∀ i, ∀ hi : i ≤ middleLogical.top, z ∉ (middle.frames i hi).owned := by
      intro i hi hOwned
      have ho : i ≤ logical.top := by rw [←a.top]; exact hi
      exact hOutside i ho (a.oldOwned i ho hi z hOwned hBelow)
    exact (b.integerFrame z hz (hBelow.trans_le a.free) hMid).trans (a.integerFrame z hz hBelow hOutside)
  · intro z hz
    exact (b.realPositive z hz).trans (a.realPositive z hz)

lemma frame {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hI : out.scalar.integerMemory=st.scalar.integerMemory) (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : MemoryBufferFrame pm (pm.frame hI hR hP hG hO) := by
  refine ⟨rfl,le_of_eq (hP 20 (by simp)).symm,?_,?_,?_,fun v => congrFun hI _⟩
  · intros i hi hn z hz hBelow
    exact hz
  · intros z hz hBelow hOutside
    exact congrFun hI z
  · intros z hz
    exact congrFun hR z

lemma payUnit {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (pm : RecursiveMachineMemory g s α ε ell length logical st) :
    MemoryBufferFrame pm pm.payUnit := ⟨rfl,le_rfl,by intros i hi hn z hz hBelow; exact hz,by intros; rfl,by intros; rfl,by intros; rfl⟩

lemma pointerWrite {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (r : ℕ) (value : ℤ) (hr : r ∉ ([0,20,50,100] : List ℕ)) :
    MemoryBufferFrame pm (pm.pointerWrite r value hr) := by
  have h20 : (20 : ℕ) ≠ r := by intro he; subst r; simp at hr
  refine ⟨rfl,?_,by intros i hi hn z hz hBelow; exact hz,by intros; rfl,by intros; rfl,by intros; rfl⟩
  change st.scalar.core.ptrs 20 ≤ Function.update st.scalar.core.ptrs r value 20
  rw [Function.update_of_ne h20]

end MemoryBufferFrame
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderArithmetic

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1800000 in
lemma level_header_increment_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level slot : ℕ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω (levelHeaderIncrementCode slot) st 19 out ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (levelHeaderAddress level slot)
        (st.scalar.integerMemory (levelHeaderAddress level slot)+1) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+19 ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a105,a40,a41,aI,aR,aW,aO,aH⟩ := level_header_integer_load_exec m g ω st hh level slot hl
  let b := payUnit (pointerWrite a 105 (a.scalar.core.ptrs 105+1))
  have eb : MachineEval m g ω (coreCode (.pinc 105)) a 1 b := pinc_eval m g ω a 105 aH
  have b100 := ((MachineEval.seq ea eb).pointer_frame 100 (by
    simp [levelHeaderIntegerLoadCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
      linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets])).trans hl
  obtain ⟨out,ec,cI,c40,c41,cR,cW,cO,cH⟩ := level_header_integer_store_exec m g ω b aH level slot b100
  refine ⟨out,MachineEval.seq ea (MachineEval.seq eb ec),?_,cR.trans aR,?_,cO.trans aO,cH⟩
  · rw [cI]
    change Function.update a.scalar.integerMemory _ (a.scalar.core.ptrs 105+1)= _
    rw [aI,a105]
  · rw [cW]
    change a.work+1+9= _
    rw [aW]; norm_num; ring

set_option maxHeartbeats 1800000 in
lemma level_header_integer_real_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level slot target : ℕ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω (levelHeaderIntegerRealCode slot target) st 10 out ∧
      out.scalar.core.regs target=(st.scalar.integerMemory (levelHeaderAddress level slot) : ℝ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+10 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a105,a40,a41,aI,aR,aW,aO,aH⟩ := level_header_integer_load_exec m g ω st hh level slot hl
  let out := payUnit (realWrite a target (a.scalar.core.ptrs 105 : ℝ))
  have eb : MachineEval m g ω (.atom (.scalar (.pointerReal target 105))) a 1 out :=
    pointerReal_eval m g ω a target 105 aH
  refine ⟨out,MachineEval.seq ea eb,?_,aI,aR,?_,aO,aH⟩
  · simpa [out,payUnit,pcSet,realWrite] using congrArg (fun z : ℤ => (z : ℝ)) a105
  · change a.work+1= _
    rw [aW]; norm_num; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushOutputRead

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1400000 in
lemma push_output_read_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (head next : ℤ) (v : Fin n)
    (hhead : st.scalar.core.ptrs 94=head) (hkey : st.scalar.integerMemory head=(v.val : ℤ))
    (hnext : st.scalar.integerMemory (head+2)=next) :
    ∃ out, MachineEval m g ω pushOutputReadCode st 6 out ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧ out.scalar.core.ptrs 94=next ∧ out.scalar.core.ptrs 44=0 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+6 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω pushOutputReadInstructions
    (by simp [pushOutputReadInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,?_,ex.query_frame (by decide),hW,?_,hH⟩
  all_goals simp [linearRun,pushOutputReadInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hhead,hkey,hnext,Int.add_assoc]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushAnalysisHelpers

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

variable {n : ℕ}

lemma input_degree (g : InputGraph n) (v : Fin n) :
    (g.neighbors v).length = g.graph.degree v := by
  have he : (g.neighbors v).toFinset = g.graph.neighborFinset v := by
    ext u
    simp [g.correct]
  rw [← List.toFinset_card_of_nodup (g.nodup v), he,
    SimpleGraph.card_neighborFinset_eq_degree]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexRealCopy

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


set_option maxHeartbeats 1800000 in
lemma vertex_real_copy_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex source target : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hs : st.scalar.core.ptrs 89=(source : ℤ)) (ht : st.scalar.core.ptrs 88=(target : ℤ)) :
    ∃ out, MachineEval m g ω vertexRealCopyCode st (8*width+16) out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width vertex target)
        (st.scalar.core.mem (vertexRecordAddress width vertex source)) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(8*width+16 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := payUnit (pointerWrite st 44 (source : ℤ))
  have ea : MachineEval m g ω (coreCode (.pcopy 44 89)) st 1 a := by simpa only [a,hs,coreCode] using pcopy_eval m g ω st 44 89 hh
  have a0 := (ea.pointer_frame 0 (by decide)).trans hz
  have a40 := (ea.pointer_frame 40 (by decide)).trans hv
  have a41 := (ea.pointer_frame 41 (by decide)).trans hw
  have a44 : a.scalar.core.ptrs 44=(source : ℤ) := by simp [a,payUnit,pcSet,pointerWrite]
  obtain ⟨b,eb,b10,bI,bR,bW,bO,bH⟩ := vertex_real_load_exec m g ω a hh width vertex source a0 a40 a41 a44
  have b88 := (eb.pointer_frame 88 (by decide)).trans ((ea.pointer_frame 88 (by decide)).trans ht)
  let c := payUnit (pointerWrite b 44 (target : ℤ))
  have ec : MachineEval m g ω (coreCode (.pcopy 44 88)) b 1 c := by simpa only [c,b88,coreCode] using pcopy_eval m g ω b 44 88 bH
  have ePre := MachineEval.seq ea (MachineEval.seq eb ec)
  have c0 := (ePre.pointer_frame 0 (by decide)).trans hz
  have c40 := (ePre.pointer_frame 40 (by decide)).trans hv
  have c41 := (ePre.pointer_frame 41 (by decide)).trans hw
  have c44 : c.scalar.core.ptrs 44=(target : ℤ) := by simp [c,payUnit,pcSet,pointerWrite]
  have c10 := ec.real_register_frame 10 (by decide)
  obtain ⟨out,ed,dR,dI,dRegs,dW,dO,dH⟩ := vertex_real_store_exec m g ω c bH width vertex target c0 c40 c41 c44
  have ex : MachineEval m g ω vertexRealCopyCode st (8*width+16) out := by
    have e := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
    convert e using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,?_,dI.trans bI,ex.query_frame (by decide),?_,dO.trans bO,dH⟩
  · rw [dR,c10,b10]
    change Function.update b.scalar.core.mem _ (a.scalar.core.mem _)= _
    rw [bR]
    rfl
  · rw [dW]
    change b.work+1+(4*width+7 : ℕ)= _
    rw [bW]
    change st.work+1+(4*width+7 : ℕ)+1+(4*width+7 : ℕ)= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexRealZero

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1600000 in
lemma vertex_real_zero_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex offset : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (ho : st.scalar.core.ptrs 88=(offset : ℤ)) :
    ∃ out, MachineEval m g ω vertexRealZeroCode st (4*width+9) out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width vertex offset) 0 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(4*width+9 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := payUnit (pointerWrite st 44 (offset : ℤ))
  have ea : MachineEval m g ω (coreCode (.pcopy 44 88)) st 1 a := by simpa only [a,ho,coreCode] using pcopy_eval m g ω st 44 88 hh
  let b := payUnit (realWrite a 10 0)
  have eb : MachineEval m g ω (coreCode (.const 10 0)) a 1 b := const_eval m g ω a 10 0 hh
  have ePre := MachineEval.seq ea eb
  have b0 := (ePre.pointer_frame 0 (by decide)).trans hz
  have b40 := (ePre.pointer_frame 40 (by decide)).trans hv
  have b41 := (ePre.pointer_frame 41 (by decide)).trans hw
  have b44 : b.scalar.core.ptrs 44=(offset : ℤ) := by simp [b,a,payUnit,pcSet,pointerWrite,realWrite]
  obtain ⟨out,ec,cR,cI,cRegs,cW,cO,cH⟩ := vertex_real_store_exec m g ω b hh width vertex offset b0 b40 b41 b44
  have ex : MachineEval m g ω vertexRealZeroCode st (4*width+9) out := by
    have e := MachineEval.seq ea (MachineEval.seq eb ec)
    convert e using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,?_,cI,ex.query_frame (by decide),?_,cO,cH⟩
  · rw [cR]
    rfl
  · rw [cW]
    change st.work+1+1+(4*width+7 : ℕ)= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelVertexFlagsClear

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def clearLevelVertexFlagsMemory (I : ℤ → ℤ) (width vertex base : ℕ) (offsets : List ℕ) : ℤ → ℤ :=
  offsets.foldl (fun J offset => Function.update J (vertexRecordAddress width vertex (base+offset)) 0) I

lemma levelVertexFlagClearCode_context (offset r : ℕ) (hr : r ∈ ([0,40,41,87] : List ℕ)) :
    r ∉ (levelVertexFlagClearCode offset).pointerTargets := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl <;>
    simp [levelVertexFlagClearCode,levelVertexOffsetCode,levelVertexOffsetInstructions,vertexFlagClearCode,
      vertexIntegerStoreCode,vertexAddressCode,vertexAddressTailCode,integerScaleCode,
      integerScaleLoopCode,integerScaleBodyCode,integerScaleBodyRoutine,PointerRoutine.sequence,
      PointerRoutine.code,PointerOp.instruction,linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets]

set_option maxHeartbeats 2200000 in
lemma level_vertex_flags_clear_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (offsets : List ℕ) (st : MachineState) (hh : st.scalar.halted=false) (width vertex base : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hb : st.scalar.core.ptrs 87=(base : ℤ)) :
    ∃ out, MachineEval m g ω (levelVertexFlagsClearCode offsets) st (offsets.length*(4*width+11)) out ∧
      out.scalar.integerMemory=clearLevelVertexFlagsMemory st.scalar.integerMemory width vertex base offsets ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.regs=st.scalar.core.regs ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(offsets.length*(4*width+11) : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  induction offsets generalizing st with
  | nil => exact ⟨st,by simpa [levelVertexFlagsClearCode,sequenceCode] using (MachineEval.skip (m:=m) (g:=g) (ω:=ω) st),rfl,rfl,rfl,rfl,by simp,rfl,hh⟩
  | cons offset rest ih =>
    obtain ⟨a,ea,aI,aR,aRegs,aQ,aW,aO,aH⟩ := level_vertex_flag_clear_exec m g ω st hh width vertex base offset hz hv hw hb
    have a0 := (ea.pointer_frame 0 (levelVertexFlagClearCode_context offset 0 (by simp))).trans hz
    have a40 := (ea.pointer_frame 40 (levelVertexFlagClearCode_context offset 40 (by simp))).trans hv
    have a41 := (ea.pointer_frame 41 (levelVertexFlagClearCode_context offset 41 (by simp))).trans hw
    have a87 := (ea.pointer_frame 87 (levelVertexFlagClearCode_context offset 87 (by simp))).trans hb
    obtain ⟨out,eb,bI,bR,bRegs,bQ,bW,bO,bH⟩ := ih a aH a0 a40 a41 a87
    have ex : MachineEval m g ω (levelVertexFlagsClearCode (offset::rest)) st ((offset::rest).length*(4*width+11)) out := by
      have e := MachineEval.seq ea eb
      convert e using 1 <;> (first | rfl | simp [List.length_cons,Nat.add_mul,Nat.add_comm])
    refine ⟨out,ex,?_,bR.trans aR,bRegs.trans aRegs,bQ.trans aQ,?_,bO.trans aO,bH⟩
    · rw [bI,aI]
      rfl
    · rw [bW,aW]
      simp only [List.length_cons]
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshVertexPrep

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma fresh_reference_prep_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base : ℕ) (hb : st.scalar.core.ptrs 87=(base : ℤ)) :
    ∃ out, MachineEval m g ω freshReferencePrepCode st 2 out ∧ out.scalar.core.ptrs 89=0 ∧
      out.scalar.core.ptrs 88=(base : ℤ) ∧ out.scalar.integerMemory=st.scalar.integerMemory ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+2 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω freshReferencePrepInstructions
    (by simp [freshReferencePrepInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,freshReferencePrepInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hb]

lemma fresh_residual_prep_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (parent : ℕ) (hb : st.scalar.core.ptrs 87=((parent+16 : ℕ) : ℤ)) :
    ∃ out, MachineEval m g ω freshResidualPrepCode st 4 out ∧ out.scalar.core.ptrs 89=((parent+1 : ℕ) : ℤ) ∧
      out.scalar.core.ptrs 88=((parent+17 : ℕ) : ℤ) ∧ out.scalar.integerMemory=st.scalar.integerMemory ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+4 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω freshResidualPrepInstructions
    (by simp [freshResidualPrepInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,freshResidualPrepInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hb] <;> omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshVertexCopies

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1800000 in
lemma fresh_reference_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex base : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hb : st.scalar.core.ptrs 87=(base : ℤ)) :
    ∃ out, MachineEval m g ω freshReferenceCode st (8*width+18) out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width vertex base)
        (st.scalar.core.mem (vertexRecordAddress width vertex 0)) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(8*width+18 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a89,a88,aI,aR,aW,aO,aH⟩ := fresh_reference_prep_exec m g ω st hh base hb
  have a0 := (ea.pointer_frame 0 (by decide)).trans hz
  have a40 := (ea.pointer_frame 40 (by decide)).trans hv
  have a41 := (ea.pointer_frame 41 (by decide)).trans hw
  obtain ⟨out,eb,bR,bI,bQ,bW,bO,bH⟩ := vertex_real_copy_exec m g ω a aH width vertex 0 base a0 a40 a41 a89 a88
  have ex : MachineEval m g ω freshReferenceCode st (8*width+18) out := by
    have e := MachineEval.seq ea eb
    convert e using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,?_,bI.trans aI,?_,?_,bO.trans aO,bH⟩
  · rw [bR,aR]
  · rw [bQ]; exact ea.query_frame (by decide)
  · rw [bW,aW]; push_cast; ring

set_option maxHeartbeats 1800000 in
lemma fresh_residual_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex parent : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hb : st.scalar.core.ptrs 87=((parent+16 : ℕ) : ℤ)) :
    ∃ out, MachineEval m g ω freshResidualCode st (8*width+20) out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width vertex (parent+17))
        (st.scalar.core.mem (vertexRecordAddress width vertex (parent+1))) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(8*width+20 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a89,a88,aI,aR,aW,aO,aH⟩ := fresh_residual_prep_exec m g ω st hh parent hb
  have a0 := (ea.pointer_frame 0 (by decide)).trans hz
  have a40 := (ea.pointer_frame 40 (by decide)).trans hv
  have a41 := (ea.pointer_frame 41 (by decide)).trans hw
  obtain ⟨out,eb,bR,bI,bQ,bW,bO,bH⟩ := vertex_real_copy_exec m g ω a aH width vertex (parent+1) (parent+17) a0 a40 a41 a89 a88
  have ex : MachineEval m g ω freshResidualCode st (8*width+20) out := by
    have e := MachineEval.seq ea eb
    convert e using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,?_,bI.trans aI,?_,?_,bO.trans aO,bH⟩
  · rw [bR,aR]
  · rw [bQ]; exact ea.query_frame (by decide)
  · rw [bW,aW]; push_cast; ring

set_option maxHeartbeats 1800000 in
lemma fresh_high_zero_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex base : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hb : st.scalar.core.ptrs 87=(base : ℤ)) :
    ∃ out, MachineEval m g ω freshHighZeroCode st (4*width+11) out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width vertex (base+4)) 0 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(4*width+11 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a88,aI,aR,aW,aO,aH⟩ := level_vertex_offset_exec m g ω st hh base 4 hb
  have a0 := (ea.pointer_frame 0 (by decide)).trans hz
  have a40 := (ea.pointer_frame 40 (by decide)).trans hv
  have a41 := (ea.pointer_frame 41 (by decide)).trans hw
  obtain ⟨out,eb,bR,bI,bQ,bW,bO,bH⟩ := vertex_real_zero_exec m g ω a aH width vertex (base+4) a0 a40 a41 a88
  have ex : MachineEval m g ω freshHighZeroCode st (4*width+11) out := by
    have e := MachineEval.seq ea eb
    convert e using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,?_,bI.trans aI,?_,?_,bO.trans aO,bH⟩
  · rw [bR,aR]
  · rw [bQ]; exact ea.query_frame (by decide)
  · rw [bW,aW]; push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ClearVertexFlagsMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma clear_level_flags_frame (I : ℤ → ℤ) (width vertex base : ℕ) (offsets : List ℕ) (z : ℤ)
    (hz : ∀ k ∈ offsets, z ≠ vertexRecordAddress width vertex (base+k)) :
    clearLevelVertexFlagsMemory I width vertex base offsets z=I z := by
  induction offsets generalizing I with
  | nil => rfl
  | cons offset rest ih =>
    change clearLevelVertexFlagsMemory (Function.update I (vertexRecordAddress width vertex (base+offset)) 0) width vertex base rest z=I z
    rw [ih _ (fun k hk => hz k (by simp [hk]))]
    simp only [Function.update_of_ne (hz offset (by simp))]


lemma clear_level_flags_at (I : ℤ → ℤ) (width vertex base : ℕ) (offsets : List ℕ)
    (hw : ∀ k ∈ offsets, base+k < width) (k : ℕ) (hk : k ∈ offsets) :
    clearLevelVertexFlagsMemory I width vertex base offsets (vertexRecordAddress width vertex (base+k))=0 := by
  classical
  induction offsets generalizing I with
  | nil => simp at hk
  | cons offset rest ih =>
    change clearLevelVertexFlagsMemory (Function.update I (vertexRecordAddress width vertex (base+offset)) 0) width vertex base rest _= _
    by_cases hr : k ∈ rest
    · exact ih _ (fun j hj => hw j (by simp [hj])) hr
    · have he : k=offset := (List.mem_cons.mp hk).resolve_right hr
      subst k
      rw [clear_level_flags_frame]
      · simp
      · intro j hj he
        have hp := hw offset (by simp)
        have hp' := hw j (by simp [hj])
        have he' := (vertexRecordAddress_injective width vertex vertex (base+offset) (base+j) hp hp' he).2
        have hj' : offset=j := by omega
        exact hr (hj' ▸ hj)


end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshVertexExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def freshVertexRealMemory (R : ℤ → ℝ) (width vertex parent : ℕ) : ℤ → ℝ :=
  Function.update (Function.update (Function.update R (vertexRecordAddress width vertex (parent+16))
    (R (vertexRecordAddress width vertex 0))) (vertexRecordAddress width vertex (parent+17))
    (R (vertexRecordAddress width vertex (parent+1)))) (vertexRecordAddress width vertex (parent+20)) 0

set_option maxHeartbeats 2800000 in
lemma fresh_vertex_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex parent : ℕ) (hWidth : parent+22 < width)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hb : st.scalar.core.ptrs 87=((parent+16 : ℕ) : ℤ)) :
    ∃ out, MachineEval m g ω freshVertexCode st (40*width+104) out ∧
      out.scalar.core.mem=freshVertexRealMemory st.scalar.core.mem width vertex parent ∧
      out.scalar.integerMemory=clearLevelVertexFlagsMemory st.scalar.integerMemory width vertex (parent+16) [2,3,4,5,6] ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(40*width+104 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,aR,aI,aQ,aW,aO,aH⟩ := fresh_reference_exec m g ω st hh width vertex (parent+16) hz hv hw hb
  have a0 := (ea.pointer_frame 0 (by decide)).trans hz
  have a40 := (ea.pointer_frame 40 (by decide)).trans hv
  have a41 := (ea.pointer_frame 41 (by decide)).trans hw
  have a87 := (ea.pointer_frame 87 (by decide)).trans hb
  have aParent : a.scalar.core.mem (vertexRecordAddress width vertex (parent+1))=st.scalar.core.mem (vertexRecordAddress width vertex (parent+1)) := by
    rw [aR]
    exact vertex_memory_update_other_field _ width vertex vertex (parent+16) (parent+1) _ (by omega) (by omega) (by omega)
  obtain ⟨b,eb,bR,bI,bQ,bW,bO,bH⟩ := fresh_residual_exec m g ω a aH width vertex parent a0 a40 a41 a87
  have b0 := (eb.pointer_frame 0 (by decide)).trans a0
  have b40 := (eb.pointer_frame 40 (by decide)).trans a40
  have b41 := (eb.pointer_frame 41 (by decide)).trans a41
  have b87 := (eb.pointer_frame 87 (by decide)).trans a87
  obtain ⟨c,ec,cR,cI,cQ,cW,cO,cH⟩ := fresh_high_zero_exec m g ω b bH width vertex (parent+16) b0 b40 b41 b87
  have c0 := (ec.pointer_frame 0 (by decide)).trans b0
  have c40 := (ec.pointer_frame 40 (by decide)).trans b40
  have c41 := (ec.pointer_frame 41 (by decide)).trans b41
  have c87 := (ec.pointer_frame 87 (by decide)).trans b87
  obtain ⟨out,ed,dI,dR,dRegs,dQ,dW,dO,dH⟩ := level_vertex_flags_clear_exec m g ω [2,3,4,5,6] c cH width vertex (parent+16) c0 c40 c41 c87
  have ex : MachineEval m g ω freshVertexCode st (40*width+104) out := by
    have e := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
    convert e using 1 <;> (first | rfl | simp only [List.length_cons,List.length_nil]; omega)
  refine ⟨out,ex,?_,?_,dQ.trans (cQ.trans (bQ.trans aQ)),?_,dO.trans (cO.trans (bO.trans aO)),dH⟩
  · rw [dR,cR,bR,aParent,aR]
    rfl
  · rw [dI,cI,bI,aI]
  · rw [dW,cW,bW,aW]
    simp only [List.length_cons,List.length_nil]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshVertexMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma fresh_vertex_real_reference (R : ℤ → ℝ) (width vertex parent : ℕ) (hw : parent+22 < width) :
    freshVertexRealMemory R width vertex parent (vertexRecordAddress width vertex (parent+16))=
      R (vertexRecordAddress width vertex 0) := by
  unfold freshVertexRealMemory
  rw [vertex_memory_update_other_field _ width vertex vertex (parent+20) (parent+16) _ (by omega) (by omega) (by omega),
    vertex_memory_update_other_field _ width vertex vertex (parent+17) (parent+16) _ (by omega) (by omega) (by omega)]
  simp

lemma fresh_vertex_real_residual (R : ℤ → ℝ) (width vertex parent : ℕ) (hw : parent+22 < width) :
    freshVertexRealMemory R width vertex parent (vertexRecordAddress width vertex (parent+17))=
      R (vertexRecordAddress width vertex (parent+1)) := by
  unfold freshVertexRealMemory
  rw [vertex_memory_update_other_field _ width vertex vertex (parent+20) (parent+17) _ (by omega) (by omega) (by omega)]
  simp

lemma fresh_vertex_real_high (R : ℤ → ℝ) (width vertex parent : ℕ) :
    freshVertexRealMemory R width vertex parent (vertexRecordAddress width vertex (parent+20))=0 := by
  simp [freshVertexRealMemory]

lemma fresh_vertex_integer_flags (I : ℤ → ℤ) (width vertex parent : ℕ) (hw : parent+22 < width)
    (k : ℕ) (hk : 2 ≤ k ∧ k ≤ 6) :
    clearLevelVertexFlagsMemory I width vertex (parent+16) [2,3,4,5,6]
      (vertexRecordAddress width vertex (parent+16+k))=0 := by
  apply clear_level_flags_at
  · intro offset ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl <;> omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false]
    omega

lemma fresh_vertex_real_frame (R : ℤ → ℝ) (width vertex parent : ℕ) (z : ℤ)
    (h0 : z ≠ vertexRecordAddress width vertex (parent+16))
    (h1 : z ≠ vertexRecordAddress width vertex (parent+17))
    (h4 : z ≠ vertexRecordAddress width vertex (parent+20)) :
    freshVertexRealMemory R width vertex parent z=R z := by
  simp only [freshVertexRealMemory,Function.update_of_ne h0,Function.update_of_ne h1,Function.update_of_ne h4]

lemma fresh_vertex_real_other_vertex (R : ℤ → ℝ) (width vertex parent other field : ℕ)
    (hw : parent+22 < width) (hf : field < width) (hne : other ≠ vertex) :
    freshVertexRealMemory R width vertex parent (vertexRecordAddress width other field)=
      R (vertexRecordAddress width other field) := by
  apply fresh_vertex_real_frame
  all_goals
    intro he
    exact hne (vertexRecordAddress_injective width other vertex field _ hf (by omega) he).1

lemma fresh_vertex_real_positive (R : ℤ → ℝ) (width vertex parent : ℕ) (z : ℤ) (hz : 0 ≤ z) :
    freshVertexRealMemory R width vertex parent z=R z := by
  have hneg (offset : ℕ) : z ≠ vertexRecordAddress width vertex offset := by
    have hn := vertexRecordAddress_negative width vertex offset
    omega
  exact fresh_vertex_real_frame R width vertex parent z (hneg _) (hneg _) (hneg _)

lemma fresh_vertex_integer_positive (I : ℤ → ℤ) (width vertex parent : ℕ) (z : ℤ) (hz : 0 ≤ z) :
    clearLevelVertexFlagsMemory I width vertex (parent+16) [2,3,4,5,6] z=I z := by
  apply clear_level_flags_frame
  intro k hk
  have hn := vertexRecordAddress_negative width vertex (parent+16+k)
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshVertexList

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def freshVertexListRealMemory {n : ℕ} (R : ℤ → ℝ) (width parent : ℕ) (vertices : List (Fin n)) : ℤ → ℝ :=
  vertices.foldl (fun R v => freshVertexRealMemory R width v.val parent) R

def freshVertexListIntegerMemory {n : ℕ} (I : ℤ → ℤ) (width parent : ℕ) (vertices : List (Fin n)) : ℤ → ℤ :=
  vertices.foldl (fun I v => clearLevelVertexFlagsMemory I width v.val (parent+16) [2,3,4,5,6]) I

set_option maxHeartbeats 3000000 in
lemma fresh_vertex_list_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (vertices : List (Fin n)) (head : ℤ) (F : Finset ℤ) (width parent : ℕ) (hWidth : parent+22 < width)
    (st : MachineState) (hh : st.scalar.halted=false) (hz : st.scalar.core.ptrs 0=0)
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hb : st.scalar.core.ptrs 87=((parent+16 : ℕ) : ℤ))
    (hhead : st.scalar.core.ptrs 94=head) (h : VertexListRep st.scalar.integerMemory head vertices F) :
    ∃ out, MachineEval m g ω freshVertexListCode st (vertices.length*(40*width+112)+1) out ∧
      out.scalar.integerMemory=freshVertexListIntegerMemory st.scalar.integerMemory width parent vertices ∧
      out.scalar.core.mem=freshVertexListRealMemory st.scalar.core.mem width parent vertices ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(vertices.length*(40*width+112)+1 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  induction vertices generalizing st head F with
  | nil =>
    have h94 : st.scalar.core.ptrs 94=0 := hhead.trans h.nil.1
    refine ⟨payUnit st,?_,rfl,rfl,rfl,by simp [payUnit,pcSet],rfl,hh⟩
    simpa only [freshVertexListCode,List.length_nil,Nat.zero_mul,Nat.zero_add] using
      (MachineEval.pointerDone (body:=freshVertexListBodyCode) hh (by rw [h94,hz]))
  | cons v vertices ih =>
    obtain ⟨next,S,hpos,hkey,hchild,hnext,hTail,hF,hsep⟩ := h.cons_view
    obtain ⟨a,ea,a40,a94,a44,aI,aR,aQ,aW,aO,aH⟩ := push_output_read_exec m g ω (payUnit st) hh head next v hhead hkey hnext
    have a0 := (ea.pointer_frame 0 (by decide)).trans hz
    have a41 := (ea.pointer_frame 41 (by decide)).trans hw
    have a87 := (ea.pointer_frame 87 (by decide)).trans hb
    obtain ⟨b,eb,bR,bI,bQ,bW,bO,bH⟩ := fresh_vertex_exec m g ω a aH width v.val parent hWidth a0 a40 a41 a87
    have b0 := (eb.pointer_frame 0 (by decide)).trans a0
    have b41 := (eb.pointer_frame 41 (by decide)).trans a41
    have b87 := (eb.pointer_frame 87 (by decide)).trans a87
    have b94 := (eb.pointer_frame 94 (by decide)).trans a94
    have bTail : VertexListRep b.scalar.integerMemory next vertices S := by
      apply hTail.frame
      intro z hzS
      rw [bI,fresh_vertex_integer_positive _ width v.val parent z (by have := hTail.positive_cells z hzS; omega),aI]
      rfl
    obtain ⟨out,er,cI,cR,cQ,cW,cO,cH⟩ := ih next S (payUnit b) bH b0 b41 b87 b94 bTail
    have eBody := MachineEval.seq ea eb
    have ex : MachineEval m g ω freshVertexListCode st ((v::vertices).length*(40*width+112)+1) out := by
      have e := MachineEval.pointerNext (r:=94) (s:=0) hh (by rw [hhead,hz]; omega) eBody er
      convert e using 1 <;> (first | rfl | simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega)
    refine ⟨out,ex,?_,?_,cQ.trans (bQ.trans aQ),?_,cO.trans (bO.trans aO),cH⟩
    · change out.scalar.integerMemory=freshVertexListIntegerMemory _ _ _ _
      rw [cI]
      change freshVertexListIntegerMemory b.scalar.integerMemory _ _ _= _
      rw [bI,aI]
      rfl
    · rw [cR]
      change freshVertexListRealMemory b.scalar.core.mem _ _ _= _
      rw [bR,aR]
      rfl
    · rw [cW,payUnit_work,bW,aW,payUnit_work]
      simp only [List.length_cons]
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorPopulateCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma exterior_context_after_reader {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {st out : MachineState} {width levelBase flagOffset length : ℕ} {base floor : ℤ} {q : ℝ}
    (ctx : ExteriorQueueContext st width levelBase flagOffset length base floor q)
    (ex : MachineEval m g ω pushOutputReadCode st 6 out) :
    ExteriorQueueContext out width levelBase flagOffset length base floor q := by
  constructor
  · exact (ex.pointer_frame 0 (by decide)).trans ctx.zero
  · exact (ex.pointer_frame 13 (by decide)).trans ctx.basePointer
  · exact (ex.pointer_frame 25 (by decide)).trans ctx.lengthPointer
  · exact (ex.pointer_frame 50 (by decide)).trans ctx.widthPointer
  · exact (ex.pointer_frame 87 (by decide)).trans ctx.levelPointer
  · exact (ex.pointer_frame 88 (by decide)).trans ctx.flagPointer
  · exact (ex.real_register_frame 20 (by decide)).trans ctx.threshold
  · rw [ex.pointer_frame 20 (by decide)]
    exact ctx.floorBound

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshChildPreparation

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 3500000 in
lemma fresh_child_preparation_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (j : ℕ)
    (hLevel : st.scalar.core.ptrs 100=(j : ℤ)) (hOne : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω freshChildPreparationCode st 60 out ∧
      out.scalar.core.ptrs 100=((j+1 : ℕ) : ℤ) ∧
      out.scalar.core.ptrs 113=st.scalar.integerMemory (levelHeaderAddress j 1) ∧
      out.scalar.core.regs 12=(st.scalar.integerMemory (levelHeaderAddress j 14) : ℝ) ∧
      out.scalar.core.regs 13=st.scalar.core.mem (levelHeaderAddress j 5) ∧
      out.scalar.integerMemory=Function.update
        (Function.update st.scalar.integerMemory (levelHeaderAddress j 11)
          (st.scalar.integerMemory (levelHeaderAddress j 11)+1)) (levelHeaderAddress j 0) 5 ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+60 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a113,aI,aR,aW,aO,aH⟩ := level_header_integer_to_exec m g ω st hh j 1 113 hLevel
  have a100 := (ea.pointer_frame 100 (by decide)).trans hLevel
  obtain ⟨b,eb,b12,bI,bR,bW,bO,bH⟩ := level_header_integer_real_exec m g ω a aH j 14 12 a100
  have b100 := (eb.pointer_frame 100 (by decide)).trans a100
  have b31 := ((MachineEval.seq ea eb).real_register_frame 31 (by decide)).trans hOne
  obtain ⟨c,ec,c13,cI,cR,cW,cO,cH⟩ := level_header_real_to_exec m g ω b bH j 5 13 b100 b31
  have c100 := (ec.pointer_frame 100 (by decide)).trans b100
  obtain ⟨d,ed,dI,dR,dW,dO,dH⟩ := level_header_increment_exec m g ω c cH j 11 c100
  have d100 := (ed.pointer_frame 100 (by decide)).trans c100
  obtain ⟨e,ee,eI,eR,eW,eO,eH⟩ := level_header_integer_set_exec m g ω d dH j 0 5 d100
  have e100 := (ee.pointer_frame 100 (by decide)).trans d100
  let out := payUnit (pointerWrite e 100 (e.scalar.core.ptrs 100+1))
  have ep : MachineEval m g ω (coreCode (.pinc 100)) e 1 out := pinc_eval m g ω e 100 eH
  have ex : MachineEval m g ω freshChildPreparationCode st 60 out :=
    MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee ep))))
  refine ⟨out,ex,?_,?_,?_,?_,?_,eR.trans (dR.trans (cR.trans (bR.trans aR))),
    ex.query_frame (by decide),?_,eO.trans (dO.trans (cO.trans (bO.trans aO))),eH⟩
  · simp [out,payUnit,pcSet,pointerWrite,e100]
  · exact ((MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee ep)))).pointer_frame 113 (by decide)).trans a113
  · rw [(MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee ep))).real_register_frame 12 (by decide),b12,aI]
  · rw [(MachineEval.seq ed (MachineEval.seq ee ep)).real_register_frame 13 (by decide),c13,bR,aR]
  · change e.scalar.integerMemory= _
    rw [eI,dI,cI,bI,aI]
  · change e.work+1= _
    rw [eW,dW,cW,bW,aW]
    norm_num
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshHeaderValues

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def freshHeaderBeforeQueues (I : ℤ → ℤ) (level block : ℕ) : ℤ → ℤ :=
  Function.update (levelHeaderIntegerSetsMemory I level freshHeaderIntegerDefaults)
    (levelHeaderAddress level 14) (block : ℤ)

lemma fresh_header_before_queue_value (I : ℤ → ℤ) (level block slot length : ℕ) (free : ℤ)
    (hs : slot ∈ freshHeaderSlots) (h7 : slot ≠ 7) (h8 : slot ≠ 8) :
    freshHeaderBeforeQueues I level block (levelHeaderAddress level slot)=freshHeaderIntegerValue free length block slot := by
  simp only [freshHeaderSlots,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp_all [freshHeaderBeforeQueues,levelHeaderIntegerSetsMemory,freshHeaderIntegerDefaults,freshHeaderIntegerValue]

lemma fresh_header_before_queue_low (I : ℤ → ℤ) (level block : ℕ) (z : ℤ) (hz : z < 128) :
    freshHeaderBeforeQueues I level block z=I z := by
  unfold freshHeaderBeforeQueues
  have hp := levelHeaderAddress_positive level 14
  rw [Function.update_of_ne (by omega : z ≠ levelHeaderAddress level 14),header_integer_sets_low I level _ z hz]

lemma fresh_header_scalar_defaults (R : ℤ → ℝ) (level : ℕ) (N q : ℝ) :
    FreshHeaderScalars (levelHeaderRealZerosMemory
      (Function.update (Function.update R (levelHeaderAddress level 0) N) (levelHeaderAddress level 1) q)
      level [3,4,5]) level N q := by
  simp [FreshHeaderScalars,levelHeaderRealZerosMemory]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeaderRealLow

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma header_parameters_real_low (R : ℤ → ℝ) (level : ℕ) (N q : ℝ) (z : ℤ) (hz : z < 128) :
    (Function.update (Function.update R (levelHeaderAddress level 0) N) (levelHeaderAddress level 1) q) z=R z := by
  have h0 := levelHeaderAddress_positive level 0
  have h1 := levelHeaderAddress_positive level 1
  rw [Function.update_of_ne (by omega : z ≠ levelHeaderAddress level 1),
    Function.update_of_ne (by omega : z ≠ levelHeaderAddress level 0)]

lemma header_defaults_parameters_real_low (R : ℤ → ℝ) (level : ℕ) (N q : ℝ) (z : ℤ) (hz : z < 128) :
    levelHeaderRealZerosMemory (Function.update (Function.update R (levelHeaderAddress level 0) N)
      (levelHeaderAddress level 1) q) level [3,4,5] z=R z := by
  rw [header_real_zeros_low _ level _ z hz,header_parameters_real_low R level N q z hz]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderOutside

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def OutsideLevelHeader (level : ℕ) (z : ℤ) : Prop := ∀ slot < 32, z ≠ levelHeaderAddress level slot

lemma outside_header_above (count level : ℕ) (hl : level < count) (z : ℤ) (hz : 128+32*(count : ℤ) ≤ z) :
    OutsideLevelHeader level z := by
  intro slot hs
  unfold levelHeaderAddress
  omega
lemma outside_header_low (level : ℕ) (z : ℤ) (hz : z < 128) : OutsideLevelHeader level z := by
  intro slot hs
  have hp := levelHeaderAddress_positive level slot
  omega
lemma outside_header_other (level other slot : ℕ) (hLevel : other ≠ level) (hs : slot < 32) :
    OutsideLevelHeader level (levelHeaderAddress other slot) := by
  intro k hk he
  exact hLevel (levelHeaderAddress_injective other level slot k hs hk he).1

lemma fresh_header_before_queue_outside (I : ℤ → ℤ) (level block : ℕ) (z : ℤ) (hz : OutsideLevelHeader level z) :
    freshHeaderBeforeQueues I level block z=I z := by
  unfold freshHeaderBeforeQueues
  rw [Function.update_of_ne (hz 14 (by decide))]
  apply header_integer_sets_frame
  intro kv hk
  apply hz kv.1
  simp only [freshHeaderIntegerDefaults,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

lemma header_parameters_defaults_outside (R : ℤ → ℝ) (level : ℕ) (N q : ℝ) (z : ℤ)
    (hz : OutsideLevelHeader level z) :
    levelHeaderRealZerosMemory (Function.update (Function.update R (levelHeaderAddress level 0) N)
      (levelHeaderAddress level 1) q) level [3,4,5] z=R z := by
  rw [header_real_zeros_frame]
  · rw [Function.update_of_ne (hz 1 (by decide)),Function.update_of_ne (hz 0 (by decide))]
  · intro slot hs
    apply hz slot
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl <;> decide

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshHeaderExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 4200000 in
lemma fresh_header_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (ell j length width : ℕ) (N q : ℝ) (free : ℤ)
    (hj : j ≤ ell) (hN : 1 ≤ N) (hFree : 128+32*((ell+2 : ℕ) : ℤ) ≤ free)
    (hDepth : st.scalar.integerMemory 2=((ell+2 : ℕ) : ℤ)) (hLength : st.scalar.integerMemory 5=(length : ℤ))
    (hLevel : st.scalar.core.ptrs 100=(j : ℤ)) (hf : st.scalar.core.ptrs 20=free)
    (hw : st.scalar.core.ptrs 50=(width : ℤ)) (h1 : st.scalar.core.regs 31=1)
    (hNR : st.scalar.core.regs 12=N) (hqR : st.scalar.core.regs 13=q) :
    ∃ steps out, MachineEval m g ω freshHeaderCode st steps out ∧
      steps ≤ (⌈N⌉₊+2)*(4*(ell-j)+22)+10*length+226 ∧
      FreshHeaderMemory out.scalar.integerMemory out.scalar.core.mem j length (blockScale [] ell j N) N q free ∧
      out.scalar.core.mem=levelHeaderRealZerosMemory
        (Function.update (Function.update st.scalar.core.mem (levelHeaderAddress j 0) N) (levelHeaderAddress j 1) q) j [3,4,5] ∧
      out.scalar.core.ptrs 20=free+2*(length : ℤ) ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.core.ptrs 87=((16*(j+1) : ℕ) : ℤ) ∧ out.scalar.core.ptrs 89=((16*(j+1) : ℕ) : ℤ) ∧
      out.scalar.core.ptrs 41=(width : ℤ) ∧
      (∀ z, z < 128 → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ z, z < free → OutsideLevelHeader j z → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,aR,aN,aq,aI,aQ,aW,aO,aH⟩ := frame_scalar_parameters_exec m g ω st hh j N q hLevel h1 hNR hqR
  have a100 := (ea.pointer_frame 100 (by decide)).trans hLevel
  obtain ⟨b,eb,bI,bR,bQ,bW,bO,bH⟩ := fresh_header_defaults_exec m g ω a aH j a100
  have b100 := (eb.pointer_frame 100 (by decide)).trans a100
  have bScalars : FreshHeaderScalars b.scalar.core.mem j N q := by
    rw [bR,aR]
    exact fresh_header_scalar_defaults st.scalar.core.mem j N q
  have bDepth : b.scalar.integerMemory 2=((ell+2 : ℕ) : ℤ) := by
    rw [bI,header_integer_sets_low _ j _ 2 (by norm_num),aI]
    exact hDepth
  have b31 := (eb.real_register_frame 31 (by decide)).trans ((ea.real_register_frame 31 (by decide)).trans h1)
  obtain ⟨u,c,ec,hu,cI,cR,c20,c0,cQ,cW,cO,cH⟩ := frame_block_preparation_exec m g ω b bH ell j N q hj hN bDepth b100 bScalars.1 bScalars.2.1 b31
  have c100 := (ec.pointer_frame 100 (by decide)).trans b100
  have cBefore : c.scalar.integerMemory=freshHeaderBeforeQueues st.scalar.integerMemory j (blockScale [] ell j N) := by
    rw [cI,bI,aI]
    rfl
  have cLength : c.scalar.integerMemory 5=(length : ℤ) := by
    rw [cBefore,fresh_header_before_queue_low _ j _ 5 (by norm_num)]
    exact hLength
  obtain ⟨d,ed,d18,d25,dI,dR,dQ,dW,dO,dH⟩ := frame_rank_load_exec m g ω c cH length cLength
  have ePrefix := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  have d100 := (ed.pointer_frame 100 (by decide)).trans c100
  have dFree := (ePrefix.pointer_frame 20 (by decide)).trans hf
  have dWidth := (ePrefix.pointer_frame 50 (by decide)).trans hw
  obtain ⟨f,ef,fFree,f0,f7,f8,fExt,fHigh,fFrame,fR,fQ,fW,fO,fH⟩ := fresh_queue_pair_exec m g ω d dH (ell+2) j length free (by omega) hFree dFree d100 d18
  have f100 := (ef.pointer_frame 100 (by decide)).trans d100
  have f50 := (ef.pointer_frame 50 (by decide)).trans dWidth
  obtain ⟨out,eg,g87,g89,g41,gI,gR,gQ,gW,gO,gH⟩ := level_context_exec m g ω f fH j width f100 f50
  have finalI : out.scalar.integerMemory=f.scalar.integerMemory := gI
  have finalR : out.scalar.core.mem=b.scalar.core.mem := gR.trans (fR.trans (dR.trans cR))
  have headerBound (slot : ℕ) (hs : slot < 32) : levelHeaderAddress j slot < free := by unfold levelHeaderAddress; omega
  have noArray (z base : ℤ) (hz : z < free) (hb : free ≤ base) : z ∉ arrayCells base length := by
    intro hm
    obtain ⟨i,hi,he⟩ := (mem_arrayCells base z length).mp hm
    have hi0 := Int.natCast_nonneg i
    omega
  have memory : FreshHeaderMemory out.scalar.integerMemory out.scalar.core.mem j length (blockScale [] ell j N) N q free := by
    constructor
    · intro slot hs
      rw [finalI]
      by_cases h7 : slot=7
      · subst slot; simpa [freshHeaderIntegerValue] using f7
      by_cases h8 : slot=8
      · subst slot; simpa [freshHeaderIntegerValue] using f8
      have hs32 : slot < 32 := by simp only [freshHeaderSlots,List.mem_cons,List.not_mem_nil,or_false] at hs; omega
      have hb := headerBound slot hs32
      rw [fFrame _ (noArray _ free hb le_rfl) (noArray _ (free+(length : ℤ)) hb (by have := Int.natCast_nonneg length; omega))
        (by simpa using h7) (by simpa using h8),dI,cBefore]
      exact fresh_header_before_queue_value st.scalar.integerMemory j _ slot length free hs h7 h8
    · rw [finalR]; exact bScalars
    · rw [finalI]; exact fExt
    · rw [finalI]; exact fHigh
  have ex := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ef eg))))
  refine ⟨20+(130+(u+(3+((10*length+30)+8)))),out,ex,by omega,memory,?_,?_,?_,g87,g89,g41,?_,?_,gQ.trans (fQ.trans (dQ.trans (cQ.trans (bQ.trans aQ)))),?_,gO.trans (fO.trans (dO.trans (cO.trans (bO.trans aO)))),gH⟩
  · rw [finalR,bR,aR]
  · exact (eg.pointer_frame 20 (by decide)).trans fFree
  · exact (eg.pointer_frame 0 (by decide)).trans f0
  · intro z hz
    have hzFree : z < free := by have hc0 := Int.natCast_nonneg (ell+2); omega
    have h7 := levelHeaderAddress_positive j 7
    have h8 := levelHeaderAddress_positive j 8
    rw [finalI,fFrame z (noArray z free hzFree le_rfl)
      (noArray z (free+(length : ℤ)) hzFree (by have := Int.natCast_nonneg length; omega)) (by omega) (by omega),dI,cBefore]
    exact fresh_header_before_queue_low st.scalar.integerMemory j _ z hz
  · intro z hz hOutside
    rw [finalI,fFrame z (noArray z free hz le_rfl)
      (noArray z (free+(length : ℤ)) hz (by have := Int.natCast_nonneg length; omega))
      (hOutside 7 (by decide)) (hOutside 8 (by decide)),dI,cBefore]
    exact fresh_header_before_queue_outside st.scalar.integerMemory j _ z hOutside
  · rw [gW,fW,dW,cW,bW,aW]; push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshHeaderFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma FreshHeaderMemory.positive_frame {I J : ℤ → ℤ} {R S : ℤ → ℝ} {level length block : ℕ}
    {N q : ℝ} {free : ℤ} (h : FreshHeaderMemory I R level length block N q free)
    (hI : ∀ z, 0 ≤ z → J z=I z) (hR : ∀ z, 0 ≤ z → S z=R z) :
    FreshHeaderMemory J S level length block N q free := by
  have hp (slot : ℕ) : 0 ≤ levelHeaderAddress level slot := by have := levelHeaderAddress_positive level slot; omega
  constructor
  · intro slot hs
    rw [hI _ (hp slot)]
    exact h.integers slot hs
  · rcases h.scalars with ⟨hN,hq,hQ,hW,ht⟩
    exact ⟨(hR _ (hp 0)).trans hN,(hR _ (hp 1)).trans hq,(hR _ (hp 3)).trans hQ,
      (hR _ (hp 4)).trans hW,(hR _ (hp 5)).trans ht⟩
  · apply h.exterior.frame
    intro z hz
    exact hI z (by have := h.exterior.positive_cells z hz; omega)
  · apply h.high.frame
    intro z hz
    exact hI z (by have := h.high.positive_cells z hz; omega)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshQueueRecords

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def exteriorEligibleKeys {n : ℕ} (I : ℤ → ℤ) (R : ℤ → ℝ) (width base : ℕ)
    (q : ℝ) (domain : Finset (Fin n)) : Finset ℕ :=
  (domain.filter (fun v => I (vertexRecordAddress width v.val (base+2))=0 ∧
    q*(I (vertexRecordAddress width v.val 0) : ℝ) < R (vertexRecordAddress width v.val (base+1)))).image Fin.val

lemma mem_exteriorEligibleKeys {n : ℕ} (I : ℤ → ℤ) (R : ℤ → ℝ) (width base : ℕ)
    (q : ℝ) (domain : Finset (Fin n)) (v : Fin n) (hv : v ∈ domain) :
    v.val ∈ exteriorEligibleKeys I R width base q domain ↔
      I (vertexRecordAddress width v.val (base+2))=0 ∧
      q*(I (vertexRecordAddress width v.val 0) : ℝ) < R (vertexRecordAddress width v.val (base+1)) := by
  classical
  simp only [exteriorEligibleKeys,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨u,⟨hu,hTest⟩,he⟩
    have he' : u=v := Fin.ext he
    simpa only [he'] using hTest
  · intro hTest
    exact ⟨v,⟨hv,hTest⟩,rfl⟩

lemma exterior_memory_fresh {n : ℕ} (I : ℤ → ℤ) (R : ℤ → ℝ) (width base : ℕ)
    (q : ℝ) (domain : Finset (Fin n))
    (hActive : ∀ v ∈ domain, I (vertexRecordAddress width v.val (base+2))=0)
    (hQueued : ∀ v ∈ domain, I (vertexRecordAddress width v.val (base+3))=0) :
    ExteriorQueueMemory I R width base (base+3) q domain
      (exteriorEligibleKeys I R width base q domain) ∅ := by
  refine ⟨Finset.empty_subset _,?_,?_,?_⟩
  · intro v hv
    simpa using hQueued v hv
  · intro v hv
    rw [hActive v hv]
  · intro v hv
    exact mem_exteriorEligibleKeys I R width base q domain v hv

lemma high_boolean_fresh {n : ℕ} (I : ℤ → ℤ) (R : ℤ → ℝ) (width base : ℕ)
    (theta : ℝ) (domain : Finset (Fin n))
    (hActive : ∀ v ∈ domain, I (vertexRecordAddress width v.val (base+2))=0)
    (hHigh : ∀ v ∈ domain, R (vertexRecordAddress width v.val (base+4))=0) :
    HighBooleanRecords I R width base theta domain := by
  intro v hv
  rw [hActive v hv,if_pos rfl,hHigh v hv]

lemma high_flags_fresh {n : ℕ} (I : ℤ → ℤ) (width base : ℕ) (domain : Finset (Fin n))
    (hQueued : ∀ v ∈ domain, I (vertexRecordAddress width v.val (base+6))=0) :
    QueuedFlags I width (base+6) domain ∅ := by
  intro v hv
  simpa using hQueued v hv

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshVertexListFrames

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma fresh_vertex_real_lower (R : ℤ → ℝ) (width vertex parent other field : ℕ)
    (hw : parent+22 < width) (hf : field < parent+16) :
    freshVertexRealMemory R width vertex parent (vertexRecordAddress width other field)=
      R (vertexRecordAddress width other field) := by
  apply fresh_vertex_real_frame
  all_goals
    intro he
    have he' := (vertexRecordAddress_injective width other vertex field _ (by omega) (by omega) he).2
    omega

lemma fresh_list_real_other {n : ℕ} (R : ℤ → ℝ) (width parent : ℕ) (vertices : List (Fin n))
    (hw : parent+22 < width) (v : Fin n) (hv : v ∉ vertices) (field : ℕ) (hf : field < width) :
    freshVertexListRealMemory R width parent vertices (vertexRecordAddress width v.val field)=
      R (vertexRecordAddress width v.val field) := by
  induction vertices generalizing R with
  | nil => rfl
  | cons u rest ih =>
    have hn : v ≠ u ∧ v ∉ rest := by simpa only [List.mem_cons,not_or] using hv
    change freshVertexListRealMemory (freshVertexRealMemory R width u.val parent) width parent rest _= _
    rw [ih _ hn.2]
    exact fresh_vertex_real_other_vertex R width u.val parent v.val field hw hf
      (fun he => hn.1 (Fin.ext he))

lemma fresh_list_real_lower {n : ℕ} (R : ℤ → ℝ) (width parent : ℕ) (vertices : List (Fin n))
    (hw : parent+22 < width) (v : Fin n) (field : ℕ) (hf : field < parent+16) :
    freshVertexListRealMemory R width parent vertices (vertexRecordAddress width v.val field)=
      R (vertexRecordAddress width v.val field) := by
  induction vertices generalizing R with
  | nil => rfl
  | cons u rest ih =>
    change freshVertexListRealMemory (freshVertexRealMemory R width u.val parent) width parent rest _= _
    rw [ih]
    exact fresh_vertex_real_lower R width u.val parent v.val field hw hf

lemma fresh_vertex_integer_other (I : ℤ → ℤ) (width vertex parent other field : ℕ)
    (hw : parent+22 < width) (hf : field < width) (hne : other ≠ vertex) :
    clearLevelVertexFlagsMemory I width vertex (parent+16) [2,3,4,5,6] (vertexRecordAddress width other field)=
      I (vertexRecordAddress width other field) := by
  apply clear_level_flags_frame
  intro k hk he
  have hk' : k ≤ 6 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; omega
  exact hne (vertexRecordAddress_injective width other vertex field (parent+16+k) hf (by omega) he).1

lemma fresh_list_integer_other {n : ℕ} (I : ℤ → ℤ) (width parent : ℕ) (vertices : List (Fin n))
    (hw : parent+22 < width) (v : Fin n) (hv : v ∉ vertices) (field : ℕ) (hf : field < width) :
    freshVertexListIntegerMemory I width parent vertices (vertexRecordAddress width v.val field)=
      I (vertexRecordAddress width v.val field) := by
  induction vertices generalizing I with
  | nil => rfl
  | cons u rest ih =>
    have hn : v ≠ u ∧ v ∉ rest := by simpa only [List.mem_cons,not_or] using hv
    change freshVertexListIntegerMemory (clearLevelVertexFlagsMemory I width u.val (parent+16) [2,3,4,5,6]) width parent rest _= _
    rw [ih _ hn.2]
    exact fresh_vertex_integer_other I width u.val parent v.val field hw hf
      (fun he => hn.1 (Fin.ext he))

lemma fresh_vertex_integer_lower (I : ℤ → ℤ) (width vertex parent other field : ℕ)
    (hw : parent+22 < width) (hf : field < parent+16) :
    clearLevelVertexFlagsMemory I width vertex (parent+16) [2,3,4,5,6] (vertexRecordAddress width other field)=
      I (vertexRecordAddress width other field) := by
  apply clear_level_flags_frame
  intro k hk he
  have hk' : k ≤ 6 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; omega
  have he' := (vertexRecordAddress_injective width other vertex field (parent+16+k) (by omega) (by omega) he).2
  omega

lemma fresh_list_integer_lower {n : ℕ} (I : ℤ → ℤ) (width parent : ℕ) (vertices : List (Fin n))
    (hw : parent+22 < width) (v : Fin n) (field : ℕ) (hf : field < parent+16) :
    freshVertexListIntegerMemory I width parent vertices (vertexRecordAddress width v.val field)=
      I (vertexRecordAddress width v.val field) := by
  induction vertices generalizing I with
  | nil => rfl
  | cons u rest ih =>
    change freshVertexListIntegerMemory (clearLevelVertexFlagsMemory I width u.val (parent+16) [2,3,4,5,6]) width parent rest _= _
    rw [ih]
    exact fresh_vertex_integer_lower I width u.val parent v.val field hw hf

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshVertexListRecords

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1800000 in
lemma fresh_list_real_records {n : ℕ} (R : ℤ → ℝ) (width parent : ℕ) (vertices : List (Fin n))
    (hw : parent+22 < width) (hn : vertices.Nodup) (v : Fin n) (hv : v ∈ vertices) :
    let S := freshVertexListRealMemory R width parent vertices
    S (vertexRecordAddress width v.val (parent+16))=R (vertexRecordAddress width v.val 0) ∧
    S (vertexRecordAddress width v.val (parent+17))=R (vertexRecordAddress width v.val (parent+1)) ∧
    S (vertexRecordAddress width v.val (parent+20))=0 := by
  induction vertices generalizing R with
  | nil => simp at hv
  | cons u rest ih =>
    have hN := List.nodup_cons.mp hn
    dsimp only
    change freshVertexListRealMemory (freshVertexRealMemory R width u.val parent) width parent rest _= _ ∧
      freshVertexListRealMemory (freshVertexRealMemory R width u.val parent) width parent rest _= _ ∧
      freshVertexListRealMemory (freshVertexRealMemory R width u.val parent) width parent rest _=0
    rcases List.mem_cons.mp hv with he|hv
    · subst v
      rw [fresh_list_real_other _ width parent rest hw u hN.1 (parent+16) (by omega),
        fresh_list_real_other _ width parent rest hw u hN.1 (parent+17) (by omega),
        fresh_list_real_other _ width parent rest hw u hN.1 (parent+20) (by omega)]
      exact ⟨fresh_vertex_real_reference R width u.val parent hw,
        fresh_vertex_real_residual R width u.val parent hw,fresh_vertex_real_high R width u.val parent⟩
    · obtain ⟨h0,h1,h4⟩ := ih (freshVertexRealMemory R width u.val parent) hN.2 hv
      refine ⟨h0.trans ?_,h1.trans ?_,h4⟩
      · exact fresh_vertex_real_lower R width u.val parent v.val 0 hw (by omega)
      · exact fresh_vertex_real_lower R width u.val parent v.val (parent+1) hw (by omega)

set_option maxHeartbeats 1800000 in
lemma fresh_list_integer_records {n : ℕ} (I : ℤ → ℤ) (width parent : ℕ) (vertices : List (Fin n))
    (hw : parent+22 < width) (hn : vertices.Nodup) (v : Fin n) (hv : v ∈ vertices)
    (k : ℕ) (hk : 2 ≤ k ∧ k ≤ 6) :
    freshVertexListIntegerMemory I width parent vertices (vertexRecordAddress width v.val (parent+16+k))=0 := by
  induction vertices generalizing I with
  | nil => simp at hv
  | cons u rest ih =>
    have hN := List.nodup_cons.mp hn
    change freshVertexListIntegerMemory (clearLevelVertexFlagsMemory I width u.val (parent+16) [2,3,4,5,6]) width parent rest _= _
    rcases List.mem_cons.mp hv with he|hv
    · subst v
      rw [fresh_list_integer_other _ width parent rest hw u hN.1 (parent+16+k) (by omega)]
      exact fresh_vertex_integer_flags I width u.val parent hw k hk
    · exact ih _ hN.2 hv

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshCallRecords

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

structure FreshCallRecords {n : ℕ} (g : InputGraph n) (I : ℤ → ℤ) (R : ℤ → ℝ)
    (width base : ℕ) (domain : Finset (Fin n)) (x r : Fin n → ℝ) : Prop where
  reference : ∀ v ∈ domain, R (vertexRecordAddress width v.val base)=x v
  residual : ∀ v ∈ domain, R (vertexRecordAddress width v.val (base+1))=r v
  highBoolean : ∀ v ∈ domain, R (vertexRecordAddress width v.val (base+4))=0
  active : ∀ v ∈ domain, I (vertexRecordAddress width v.val (base+2))=0
  cache : ∀ v ∈ domain, I (vertexRecordAddress width v.val (base+4))=0
  excluded : ∀ v ∈ domain, I (vertexRecordAddress width v.val (base+5))=0
  highQueued : ∀ v ∈ domain, I (vertexRecordAddress width v.val (base+6))=0
  degree : ∀ v ∈ domain, I (vertexRecordAddress width v.val 0)=((g.neighbors v).length : ℤ)

structure FreshCallSetupRecords {n : ℕ} (g : InputGraph n) (I : ℤ → ℤ) (R : ℤ → ℝ)
    (width base : ℕ) (domain : Finset (Fin n)) (x r : Fin n → ℝ) : Prop extends
    FreshCallRecords g I R width base domain x r where
  exteriorQueued : ∀ v ∈ domain, I (vertexRecordAddress width v.val (base+3))=0

lemma FreshCallRecords.refresh_frame {n : ℕ} {g : InputGraph n} {I J : ℤ → ℤ} {R S : ℤ → ℝ}
    {width base : ℕ} {domain : Finset (Fin n)} {x r : Fin n → ℝ}
    (h : FreshCallRecords g I R width base domain x r) (hw : base+6 < width) (hb : 0 < base)
    (hR : S=R) (hI : ∀ v : Fin n, ∀ field < width, field ≠ base+3 →
      J (vertexRecordAddress width v.val field)=I (vertexRecordAddress width v.val field)) :
    FreshCallRecords g J S width base domain x r := by
  constructor
  · intro v hv; rw [hR]; exact h.reference v hv
  · intro v hv; rw [hR]; exact h.residual v hv
  · intro v hv; rw [hR]; exact h.highBoolean v hv
  · intro v hv; rw [hI v (base+2) (by omega) (by omega)]; exact h.active v hv
  · intro v hv; rw [hI v (base+4) (by omega) (by omega)]; exact h.cache v hv
  · intro v hv; rw [hI v (base+5) (by omega) (by omega)]; exact h.excluded v hv
  · intro v hv; rw [hI v (base+6) (by omega) (by omega)]; exact h.highQueued v hv
  · intro v hv; rw [hI v 0 (by omega) (by omega)]; exact h.degree v hv

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshListRecordsConstruction

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2000000 in
lemma fresh_list_records_construct {n : ℕ} (g : InputGraph n) (I : ℤ → ℤ) (R : ℤ → ℝ)
    (width parent : ℕ) (vertices : List (Fin n)) (domain : Finset (Fin n)) (x r : Fin n → ℝ)
    (hw : parent+22 < width) (hn : vertices.Nodup) (hSet : vertices.toFinset=domain)
    (hDegree : ∀ v ∈ domain, I (vertexRecordAddress width v.val 0)=((g.neighbors v).length : ℤ))
    (hX : ∀ v ∈ domain, R (vertexRecordAddress width v.val 0)=x v)
    (hR : ∀ v ∈ domain, R (vertexRecordAddress width v.val (parent+1))=r v) :
    FreshCallSetupRecords g (freshVertexListIntegerMemory I width parent vertices)
      (freshVertexListRealMemory R width parent vertices) width (parent+16) domain x r := by
  have hMem (v : Fin n) (hv : v ∈ domain) : v ∈ vertices := by
    rw [←hSet] at hv
    exact List.mem_toFinset.mp hv
  constructor
  · constructor
    · intro v hv
      exact (fresh_list_real_records R width parent vertices hw hn v (hMem v hv)).1.trans (hX v hv)
    · intro v hv
      exact (fresh_list_real_records R width parent vertices hw hn v (hMem v hv)).2.1.trans (hR v hv)
    · intro v hv
      exact (fresh_list_real_records R width parent vertices hw hn v (hMem v hv)).2.2
    · intro v hv
      exact fresh_list_integer_records I width parent vertices hw hn v (hMem v hv) 2 (by omega)
    · intro v hv
      exact fresh_list_integer_records I width parent vertices hw hn v (hMem v hv) 4 (by omega)
    · intro v hv
      exact fresh_list_integer_records I width parent vertices hw hn v (hMem v hv) 5 (by omega)
    · intro v hv
      exact fresh_list_integer_records I width parent vertices hw hn v (hMem v hv) 6 (by omega)
    · intro v hv
      rw [fresh_list_integer_lower I width parent vertices hw v 0 (by omega)]
      exact hDegree v hv
  · intro v hv
    exact fresh_list_integer_records I width parent vertices hw hn v (hMem v hv) 3 (by omega)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshListPositive

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma fresh_list_integer_positive {n : ℕ} (I : ℤ → ℤ) (width parent : ℕ) (vertices : List (Fin n))
    (z : ℤ) (hz : 0 ≤ z) : freshVertexListIntegerMemory I width parent vertices z=I z := by
  induction vertices generalizing I with
  | nil => rfl
  | cons v rest ih =>
    change freshVertexListIntegerMemory (clearLevelVertexFlagsMemory I width v.val (parent+16) [2,3,4,5,6]) width parent rest z=I z
    rw [ih,fresh_vertex_integer_positive I width v.val parent z hz]

lemma fresh_list_real_positive {n : ℕ} (R : ℤ → ℝ) (width parent : ℕ) (vertices : List (Fin n))
    (z : ℤ) (hz : 0 ≤ z) : freshVertexListRealMemory R width parent vertices z=R z := by
  induction vertices generalizing R with
  | nil => rfl
  | cons v rest ih =>
    change freshVertexListRealMemory (freshVertexRealMemory R width v.val parent) width parent rest z=R z
    rw [ih,fresh_vertex_real_positive R width v.val parent z hz]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshCallSetupExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 6500000 in
lemma fresh_call_setup_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (ell j length : ℕ) (N q : ℝ) (free head : ℤ)
    (vertices : List (Fin n)) (F : Finset ℤ) (domain : Finset (Fin n)) (x r : Fin n → ℝ)
    (hj : j ≤ ell) (hN : 1 ≤ N) (hFree : 128+32*((ell+2 : ℕ) : ℤ) ≤ free)
    (hDepth : st.scalar.integerMemory 2=((ell+2 : ℕ) : ℤ)) (hLength : st.scalar.integerMemory 5=(length : ℤ))
    (hLevel : st.scalar.core.ptrs 100=(j : ℤ)) (hf : st.scalar.core.ptrs 20=free)
    (hw : st.scalar.core.ptrs 50=((16*(ell+3) : ℕ) : ℤ)) (h1 : st.scalar.core.regs 31=1)
    (hNR : st.scalar.core.regs 12=N) (hqR : st.scalar.core.regs 13=q)
    (hHead : st.scalar.core.ptrs 113=head) (hList : VertexListRep st.scalar.integerMemory head vertices F)
    (hNodup : vertices.Nodup) (hSet : vertices.toFinset=domain)
    (hBelow : ∀ z ∈ F, z < free) (hAbove : ∀ z ∈ F, 128+32*((ell+2 : ℕ) : ℤ) ≤ z)
    (hDegree : ∀ v ∈ domain, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)=((g.neighbors v).length : ℤ))
    (hX : ∀ v ∈ domain, st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val 0)=x v)
    (hRhs : ∀ v ∈ domain, st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*j+1))=r v) :
    ∃ steps out, MachineEval m g ω freshCallSetupCode st steps out ∧
      steps ≤ (⌈N⌉₊+2)*(4*(ell-j)+22)+10*length+262+vertices.length*(40*(16*(ell+3))+112) ∧
      FreshHeaderMemory out.scalar.integerMemory out.scalar.core.mem j length (blockScale [] ell j N) N q free ∧
      FreshCallSetupRecords g out.scalar.integerMemory out.scalar.core.mem (16*(ell+3)) (16*(j+1)) domain x r ∧
      ExteriorQueueContext out (16*(ell+3)) (16*(j+1)) (16*(j+1)+3) length free (128+32*((ell+2 : ℕ) : ℤ)) q ∧
      VertexListRep out.scalar.integerMemory head vertices F ∧ out.scalar.core.ptrs 94=head ∧
      out.scalar.core.ptrs 20=free+2*(length : ℤ) ∧
      (∀ v : Fin n, ∀ field < 16*(j+1),
        out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)) ∧
      (∀ v : Fin n, ∀ field < 16*(j+1),
        out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field)) ∧
      (∀ v : Fin n, v ∉ domain → ∀ field < 16*(ell+3),
        out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)) ∧
      (∀ v : Fin n, v ∉ domain → ∀ field < 16*(ell+3),
        out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field)) ∧
      (∀ z, 0 ≤ z → z < free → OutsideLevelHeader j z → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ z, 0 ≤ z → OutsideLevelHeader j z → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let width := 16*(ell+3)
  let parent := 16*j
  have hWidth : parent+22 < width := by dsimp [parent,width]; omega
  have hBase : parent+16=16*(j+1) := by dsimp [parent]; omega
  obtain ⟨u,a,ea,hu,aHeader,aRaw,aFree,a0,a87,a89,a41,aLow,aFrame,aQ,aW,aO,aH⟩ :=
    fresh_header_exec m g ω st hh ell j length width N q free hj hN hFree hDepth hLength hLevel hf hw h1 hNR hqR
  have a113 := (ea.pointer_frame 113 (by decide)).trans hHead
  have aList : VertexListRep a.scalar.integerMemory head vertices F := by
    apply hList.frame
    intro z hz
    exact aFrame z (hBelow z hz) (outside_header_above (ell+2) j (by omega) z (hAbove z hz))
  let b := payUnit (pointerWrite a 94 head)
  have eb : MachineEval m g ω (coreCode (.pcopy 94 113)) a 1 b := by
    simpa only [b,coreCode,a113] using pcopy_eval m g ω a 94 113 aH
  have b94 : b.scalar.core.ptrs 94=head := by simp [b,payUnit,pcSet,pointerWrite]
  have b0 := (eb.pointer_frame 0 (by decide)).trans a0
  have b41 := (eb.pointer_frame 41 (by decide)).trans a41
  have b87 : b.scalar.core.ptrs 87=((parent+16 : ℕ) : ℤ) := by
    simpa only [hBase] using (eb.pointer_frame 87 (by decide)).trans a87
  obtain ⟨c,ec,cI,cR,cQ,cW,cO,cH⟩ := fresh_vertex_list_exec m g ω vertices head F width parent hWidth
    b aH b0 b41 b87 b94 aList
  have cHeader : FreshHeaderMemory c.scalar.integerMemory c.scalar.core.mem j length (blockScale [] ell j N) N q free := by
    apply aHeader.positive_frame
    · intro z hz
      rw [cI,fresh_list_integer_positive _ width parent vertices z hz]
      rfl
    · intro z hz
      rw [cR,fresh_list_real_positive _ width parent vertices z hz]
      rfl
  have bDegree : ∀ v ∈ domain, b.scalar.integerMemory (vertexRecordAddress width v.val 0)=((g.neighbors v).length : ℤ) := by
    intro v hv
    have hn := vertexRecordAddress_negative width v.val 0
    exact (aLow _ (by omega)).trans (hDegree v hv)
  have bX : ∀ v ∈ domain, b.scalar.core.mem (vertexRecordAddress width v.val 0)=x v := by
    intro v hv
    change a.scalar.core.mem _= _
    rw [aRaw,header_defaults_parameters_real_low _ j N q _ (by have hn := vertexRecordAddress_negative width v.val 0; omega)]
    exact hX v hv
  have bRhs : ∀ v ∈ domain, b.scalar.core.mem (vertexRecordAddress width v.val (parent+1))=r v := by
    intro v hv
    change a.scalar.core.mem _= _
    rw [aRaw,header_defaults_parameters_real_low _ j N q _ (by have hn := vertexRecordAddress_negative width v.val (parent+1); omega)]
    exact hRhs v hv
  have cRecords : FreshCallSetupRecords g c.scalar.integerMemory c.scalar.core.mem width (parent+16) domain x r := by
    rw [cI,cR]
    exact fresh_list_records_construct g b.scalar.integerMemory b.scalar.core.mem width parent vertices domain x r hWidth hNodup hSet bDegree bX bRhs
  have ePrefix := MachineEval.seq ea (MachineEval.seq eb ec)
  have c113 := (ePrefix.pointer_frame 113 (by decide)).trans hHead
  let d := payUnit (pointerWrite c 94 head)
  have ed : MachineEval m g ω (coreCode (.pcopy 94 113)) c 1 d := by
    simpa only [d,coreCode,c113] using pcopy_eval m g ω c 94 113 cH
  have d94 : d.scalar.core.ptrs 94=head := by simp [d,payUnit,pcSet,pointerWrite]
  have eBefore := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  have d100 := (eBefore.pointer_frame 100 (by decide)).trans hLevel
  have d50 := (eBefore.pointer_frame 50 (by decide)).trans hw
  have d31 := (eBefore.real_register_frame 31 (by decide)).trans h1
  have d0 := (ed.pointer_frame 0 (by decide)).trans ((ec.pointer_frame 0 (by decide)).trans b0)
  have dFree : d.scalar.core.ptrs 20=free+2*(length : ℤ) := by
    change c.scalar.core.ptrs 20= _
    rw [ec.pointer_frame 20 (by decide)]
    exact aFree
  have dLen : d.scalar.integerMemory 5=(length : ℤ) := by
    change c.scalar.integerMemory 5= _
    rw [cI,fresh_list_integer_positive _ width parent vertices 5 (by norm_num)]
    exact (aLow 5 (by norm_num)).trans hLength
  have dBase : d.scalar.integerMemory (levelHeaderAddress j 7)=free := by
    change c.scalar.integerMemory (levelHeaderAddress j 7)=free
    have h := cHeader.integers 7 (by simp [freshHeaderSlots])
    simpa [freshHeaderIntegerValue] using h
  obtain ⟨out,ee,eCtx,eI,eR,eFree,eW,eO,eH⟩ := exterior_frame_context_exec m g ω d cH j width length free
    (128+32*((ell+2 : ℕ) : ℤ)) q d100 d50 dLen dBase cHeader.scalars.2.1 d31 d0
    (by rw [dFree]; have := Int.natCast_nonneg length; omega)
  have finalI : out.scalar.integerMemory=c.scalar.integerMemory := eI
  have finalR : out.scalar.core.mem=c.scalar.core.mem := eR
  have outHeader : FreshHeaderMemory out.scalar.integerMemory out.scalar.core.mem j length (blockScale [] ell j N) N q free := by
    rw [finalI,finalR]
    exact cHeader
  have outRecords : FreshCallSetupRecords g out.scalar.integerMemory out.scalar.core.mem width (16*(j+1)) domain x r := by
    rw [finalI,finalR,←hBase]
    exact cRecords
  have cList : VertexListRep c.scalar.integerMemory head vertices F := by
    apply aList.frame
    intro z hz
    have hp : 0 ≤ z := by have := aList.positive_cells z hz; omega
    rw [cI,fresh_list_integer_positive _ width parent vertices z hp]
    rfl
  have ex := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed ee)))
  refine ⟨u+(1+((vertices.length*(40*width+112)+1)+(1+33))),out,ex,?_,outHeader,outRecords,eCtx,?_,?_,eFree.trans dFree,?_,?_,?_,?_,?_,?_,?_,?_,eO.trans (cO.trans aO),eH⟩
  · dsimp only [width]
    omega
  · rw [finalI]; exact cList
  · exact (ee.pointer_frame 94 (by decide)).trans d94
  · intro v field hf'
    rw [finalI,cI,fresh_list_integer_lower _ width parent vertices hWidth v field (by rw [hBase]; exact hf')]
    exact aLow _ (by have hn := vertexRecordAddress_negative width v.val field; omega)
  · intro v field hf'
    rw [finalR,cR,fresh_list_real_lower _ width parent vertices hWidth v field (by rw [hBase]; exact hf')]
    change a.scalar.core.mem _= _
    rw [aRaw,header_defaults_parameters_real_low _ j N q _ (by have hn := vertexRecordAddress_negative width v.val field; omega)]
  · intro v hv field hf'
    have hNot : v ∉ vertices := by
      intro h
      apply hv
      rw [←hSet]
      exact List.mem_toFinset.mpr h
    rw [finalI,cI,fresh_list_integer_other _ width parent vertices hWidth v hNot field hf']
    exact aLow _ (by have hn := vertexRecordAddress_negative width v.val field; omega)
  · intro v hv field hf'
    have hNot : v ∉ vertices := by
      intro h
      apply hv
      rw [←hSet]
      exact List.mem_toFinset.mpr h
    rw [finalR,cR,fresh_list_real_other _ width parent vertices hWidth v hNot field hf']
    change a.scalar.core.mem _= _
    rw [aRaw,header_defaults_parameters_real_low _ j N q _ (by have hn := vertexRecordAddress_negative width v.val field; omega)]
  · intro z hz hzF hzOut
    rw [finalI,cI,fresh_list_integer_positive _ width parent vertices z hz]
    exact aFrame z hzF hzOut
  · intro z hz hzOut
    rw [finalR,cR,fresh_list_real_positive _ width parent vertices z hz]
    change a.scalar.core.mem z= _
    rw [aRaw]
    exact header_parameters_defaults_outside st.scalar.core.mem j N q z hzOut
  · rw [ee.query_frame (by decide),ed.query_frame (by decide),cQ,eb.query_frame (by decide)]
    exact aQ
  · rw [eW]
    change c.work+1+33= _
    rw [cW]
    change b.work+(vertices.length*(40*width+112)+1 : ℕ)+1+33= _
    change a.work+1+(vertices.length*(40*width+112)+1 : ℕ)+1+33= _
    rw [aW]; push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorPopulateExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 5000000 in
lemma exterior_populate_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width levelBase flagOffset length N R : ℕ) (hflag : flagOffset < width) (hactive : levelBase+2 < width)
    (hneqActive : flagOffset ≠ levelBase+2) (hneqDegree : flagOffset ≠ 0)
    (base floor : ℤ) (hfloor : 2 ≤ floor) (q : ℝ) (domain : Finset (Fin n)) (valid : Finset ℕ)
    (vertices : List (Fin n)) (head : ℤ) (F : Finset ℤ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (obj : RankQueueObject st.scalar.integerMemory base length (st.scalar.core.ptrs 20) floor)
    (ctx : ExteriorQueueContext st width levelBase flagOffset length base floor q)
    (hdata : ExteriorQueueMemory st.scalar.integerMemory st.scalar.core.mem width levelBase flagOffset q domain valid obj.keys)
    (hDomain : ∀ v ∈ vertices, v ∈ domain)
    (hList : VertexListRep st.scalar.integerMemory head vertices F) (hHead : st.scalar.core.ptrs 94=head)
    (hBelow : ∀ z ∈ F, z < st.scalar.core.ptrs 20) (hSep : Disjoint F obj.cells)
    (hBudget : obj.mass+vertices.length ≤ N) (hcap : R < length) (hpow : N < 2^R) :
    ∃ steps out, ∃ next : RankQueueObject out.scalar.integerMemory base length (out.scalar.core.ptrs 20) floor,
      MachineEval m g ω exteriorPopulateCode st steps out ∧ steps ≤ vertices.length*(21*R+20*width+78)+1 ∧
      ExteriorQueueContext out width levelBase flagOffset length base floor q ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase flagOffset q domain valid next.keys ∧
      next.keys=eligibleInsertList valid obj.keys vertices ∧ next.mass ≤ obj.mass+vertices.length ∧
      st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 ∧
      (∀ z ∈ next.cells, z < st.scalar.core.ptrs 20 → z ∈ obj.cells) ∧
      (∀ other : Fin n, ∀ field < width, field ≠ flagOffset → out.scalar.integerMemory (vertexRecordAddress width other.val field)=st.scalar.integerMemory (vertexRecordAddress width other.val field)) ∧
      (∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 → z ∉ obj.cells → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction vertices generalizing st head F with
  | nil =>
    have h94 : st.scalar.core.ptrs 94=0 := hHead.trans hList.nil.1
    have ex : MachineEval m g ω exteriorPopulateCode st 1 (payUnit st) :=
      MachineEval.pointerDone hh (by rw [h94,ctx.zero])
    refine ⟨1,payUnit st,obj,ex,by simp,ctx.payUnit,hdata,rfl,by change obj.mass ≤ obj.mass; exact Nat.le_refl _,le_rfl,
      (fun z hz hlt => hz),(fun other field hf hn => rfl),(fun z hz hlt hnot => rfl),rfl,rfl,by simp [payUnit,pcSet],rfl,hh⟩
  | cons v vertices ih =>
    obtain ⟨nextHead,S,hPos,hKey,hChild,hNext,hTail,hF,hDisj⟩ := hList.cons_view
    have hSsub : S ⊆ F := by rw [hF]; exact Finset.subset_union_right
    obtain ⟨a,ea,a40,a94,a44,aI,aR,aQ,aW,aO,aH⟩ := push_output_read_exec m g ω (payUnit st) hh head nextHead v hHead hKey hNext
    have aFree : a.scalar.core.ptrs 20=st.scalar.core.ptrs 20 := ea.pointer_frame 20 (by decide)
    let aObj : RankQueueObject a.scalar.integerMemory base length (a.scalar.core.ptrs 20) floor :=
      obj.frame (fun z hz => congrFun aI z) (le_of_eq aFree.symm)
    have aCtx := exterior_context_after_reader ctx.payUnit ea
    have aData : ExteriorQueueMemory a.scalar.integerMemory a.scalar.core.mem width levelBase flagOffset q domain valid aObj.keys := by
      change ExteriorQueueMemory a.scalar.integerMemory a.scalar.core.mem width levelBase flagOffset q domain valid obj.keys
      rw [aI,aR]
      exact hdata
    have hm : aObj.mass ≤ N := by change obj.mass ≤ N; omega
    obtain ⟨u,b,bObj,eb,hu,bCtx,bData,bKeys,bMass,bFree,bFreeUp,bOwned,bFields,bFrame,bR,bQ,bW,bO,bH⟩ :=
      exterior_refresh_object_exec m g ω a aH width levelBase flagOffset length N R hflag hactive hneqActive hneqDegree
        base floor hfloor q domain valid aObj aCtx aData v (hDomain v (by simp)) a40 hm hcap hpow
    have bOld (z : ℤ) (hz : z ∈ bObj.cells) (hzOld : z < st.scalar.core.ptrs 20) : z ∈ obj.cells := by
      rcases Finset.mem_union.mp (bOwned hz) with hn|ho
      · have ht := (nodeCells_mem_iff (a.scalar.core.ptrs 20) z).mp hn
        rw [aFree] at ht
        omega
      · exact ho
    have bTail : VertexListRep b.scalar.integerMemory nextHead vertices S := by
      apply hTail.frame
      intro z hz
      have hFz := hSsub hz
      have hp : 0 ≤ z := by have := hTail.positive_cells z hz; omega
      have hb : z < a.scalar.core.ptrs 20 := by rw [aFree]; exact hBelow z hFz
      have hn : z ∉ aObj.cells := fun hq => Finset.disjoint_left.mp hSep hFz hq
      exact (bFrame z hp hb hn).trans (congrFun aI z)
    have bBelow : ∀ z ∈ S, z < b.scalar.core.ptrs 20 := by
      intro z hz
      have ht : z < a.scalar.core.ptrs 20 := by rw [aFree]; exact hBelow z (hSsub hz)
      exact ht.trans_le bFree
    have bSep : Disjoint S bObj.cells := by
      apply Finset.disjoint_left.mpr
      intro z hz hzQ
      exact Finset.disjoint_left.mp hSep (hSsub hz) (bOld z hzQ (hBelow z (hSsub hz)))
    have bBudget : bObj.mass+vertices.length ≤ N := by
      change bObj.mass ≤ obj.mass+1 at bMass
      simp only [List.length_cons] at hBudget
      omega
    have b94 : b.scalar.core.ptrs 94=nextHead := (eb.pointer_frame 94 (by decide)).trans a94
    obtain ⟨w,out,cObj,er,hw,cCtx,cData,cKeys,cMass,cFree,cOld,cFields,cFrame,cR,cQ,cW,cO,cH⟩ :=
      ih nextHead S (payUnit b) bH bObj bCtx.payUnit bData (fun u hu => hDomain u (by simp [hu])) bTail b94 bBelow bSep bBudget
    change cObj.keys=eligibleInsertList valid bObj.keys vertices at cKeys
    change cObj.mass ≤ bObj.mass+vertices.length at cMass
    change bObj.keys=(if v.val ∈ valid then insert v.val obj.keys else obj.keys) at bKeys
    have eBody := MachineEval.seq ea eb
    have ex : MachineEval m g ω exteriorPopulateCode st (1+(6+u)+1+w) out :=
      MachineEval.pointerNext hh (by rw [hHead,ctx.zero]; omega) eBody er
    refine ⟨1+(6+u)+1+w,out,cObj,ex,?_,cCtx,cData,?_,?_,?_,?_,?_,?_,
      cR.trans (bR.trans aR),cQ.trans (bQ.trans aQ),?_,cO.trans (bO.trans aO),cH⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [cKeys,bKeys]
      rfl
    · change bObj.mass ≤ obj.mass+1 at bMass
      simp only [List.length_cons]
      omega
    · have hb : st.scalar.core.ptrs 20 ≤ b.scalar.core.ptrs 20 := by rw [←aFree]; exact bFree
      exact hb.trans cFree
    · intro z hz hzOld
      have hzB : z < b.scalar.core.ptrs 20 := by
        have hzA : z < a.scalar.core.ptrs 20 := by rw [aFree]; exact hzOld
        exact hzA.trans_le bFree
      exact bOld z (cOld z hz hzB) hzOld
    · intro other field hf hn
      exact (cFields other field hf hn).trans ((bFields other field hf hn).trans (congrFun aI _))
    · intro z hz hzOld hNot
      have hzA : z < a.scalar.core.ptrs 20 := by rw [aFree]; exact hzOld
      have hzB : z < b.scalar.core.ptrs 20 := hzA.trans_le bFree
      have hNotB : z ∉ bObj.cells := fun h => hNot (bOld z h hzOld)
      exact (cFrame z hz hzB hNotB).trans ((bFrame z hz hzA hNot).trans (congrFun aI z))
    · rw [cW,payUnit_work,bW,aW,payUnit_work]
      push_cast
      ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EmptyQueueObject

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

@[simp] lemma slotKeySet_empty (length : ℕ) : slotKeySet (fun _ => none) length=∅ := by
  ext x
  simp [slotKeySet]
@[simp] lemma slotMass_empty (length : ℕ) : slotMass (fun _ => none) length=0 := by
  simp [slotMass]

def RankQueueObject.empty {I : ℤ → ℤ} {base free floor : ℤ} {length : ℕ}
    (rep : RankArrayRep I base length (fun _ => none) (fun _ => 0) (fun _ => ∅))
    (hBase : floor ≤ base) (hEnd : base+(length : ℤ) ≤ free) : RankQueueObject I base length free floor := {
  slots := fun _ => none
  roots := fun _ => 0
  feet := fun _ => ∅
  representation := rep
  unique := by simp
  below := by
    intro z hz
    have hm : z ∈ arrayCells base length := by simpa [queueCells] using hz
    obtain ⟨i,hi,rfl⟩ := (mem_arrayCells base z length).mp hm
    omega
  above := by
    intro z hz
    have hm : z ∈ arrayCells base length := by simpa [queueCells] using hz
    obtain ⟨i,hi,rfl⟩ := (mem_arrayCells base z length).mp hm
    have hi0 := Int.natCast_nonneg i
    omega
}

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshQueueSourceKeys

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma fresh_exterior_keys_source {n : ℕ} (g : InputGraph n) (I : ℤ → ℤ) (R : ℤ → ℝ)
    (width base : ℕ) (q : ℝ) (domain : Finset (Fin n)) (r : Fin n → ℝ)
    (hActive : ∀ v ∈ domain, I (vertexRecordAddress width v.val (base+2))=0)
    (hDegree : ∀ v ∈ domain, I (vertexRecordAddress width v.val 0)=((g.neighbors v).length : ℤ))
    (hResidual : ∀ v ∈ domain, R (vertexRecordAddress width v.val (base+1))=r v) :
    exteriorEligibleKeys I R width base q domain=
      (domain.filter (fun v => q*LocalPush.deg g.graph v < r v)).image Fin.val := by
  classical
  unfold exteriorEligibleKeys
  congr 1
  apply Finset.filter_congr
  intro v hv
  simp [hActive v hv,hDegree v hv,hResidual v hv,LocalPush.deg,input_degree]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshCallPopulation

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 5000000 in
lemma fresh_call_populate_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false)
    (ell j length capacity rank : ℕ) (N q : ℝ) (free head : ℤ)
    (vertices : List (Fin n)) (F : Finset ℤ) (domain : Finset (Fin n)) (x r : Fin n → ℝ)
    (hj : j ≤ ell) (hFree : 128+32*((ell+2 : ℕ) : ℤ) ≤ free)
    (hf : st.scalar.core.ptrs 20=free+2*(length : ℤ))
    (hHeader : FreshHeaderMemory st.scalar.integerMemory st.scalar.core.mem j length (blockScale [] ell j N) N q free)
    (hRecords : FreshCallSetupRecords g st.scalar.integerMemory st.scalar.core.mem
      (16*(ell+3)) (16*(j+1)) domain x r)
    (ctx : ExteriorQueueContext st (16*(ell+3)) (16*(j+1)) (16*(j+1)+3)
      length free (128+32*((ell+2 : ℕ) : ℤ)) q)
    (hList : VertexListRep st.scalar.integerMemory head vertices F) (hHead : st.scalar.core.ptrs 94=head)
    (hSet : vertices.toFinset=domain) (hBelow : ∀ z ∈ F, z < free)
    (hBudget : vertices.length ≤ capacity) (hcap : rank < length) (hpow : capacity < 2^rank) :
    ∃ steps out,
    ∃ exterior : RankQueueObject out.scalar.integerMemory free length (out.scalar.core.ptrs 20) free,
    ∃ high : RankQueueObject out.scalar.integerMemory (free+(length : ℤ)) length (out.scalar.core.ptrs 20) free,
      MachineEval m g ω exteriorPopulateCode st steps out ∧
      steps ≤ vertices.length*(21*rank+20*(16*(ell+3))+78)+1 ∧
      (∀ slot ∈ freshHeaderSlots, out.scalar.integerMemory (levelHeaderAddress j slot)=
        freshHeaderIntegerValue free length (blockScale [] ell j N) slot) ∧
      FreshHeaderScalars out.scalar.core.mem j N q ∧
      FreshCallRecords g out.scalar.integerMemory out.scalar.core.mem (16*(ell+3)) (16*(j+1)) domain x r ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem (16*(ell+3)) (16*(j+1))
        (16*(j+1)+3) q domain
        ((domain.filter (fun v => q*LocalPush.deg g.graph v < r v)).image Fin.val) exterior.keys ∧
      exterior.keys=(domain.filter (fun v => q*LocalPush.deg g.graph v < r v)).image Fin.val ∧
      exterior.mass ≤ vertices.length ∧ high.keys=∅ ∧ high.mass=0 ∧ Disjoint exterior.cells high.cells ∧
      VertexListRep out.scalar.integerMemory head vertices F ∧
      st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 ∧
      (∀ v : Fin n, ∀ field < 16*(ell+3), field ≠ 16*(j+1)+3 →
        out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)) ∧
      (∀ z, 0 ≤ z → z < free → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.core.ptrs 0=0 ∧ out.scalar.halted=false := by
  classical
  let width := 16*(ell+3)
  let base := 16*(j+1)
  have hFloor : 2 ≤ free := by omega
  let extObj : RankQueueObject st.scalar.integerMemory free length (st.scalar.core.ptrs 20) free :=
    RankQueueObject.empty hHeader.exterior (le_refl _) (by rw [hf]; omega)
  let highObj : RankQueueObject st.scalar.integerMemory (free+(length : ℤ)) length (st.scalar.core.ptrs 20) free :=
    RankQueueObject.empty hHeader.high (by omega) (by rw [hf]; omega)
  have extKeys : extObj.keys=∅ := by simp [extObj,RankQueueObject.keys,RankQueueObject.empty]
  have extMass : extObj.mass=0 := by simp [extObj,RankQueueObject.mass,RankQueueObject.empty]
  have highKeys : highObj.keys=∅ := by simp [highObj,RankQueueObject.keys,RankQueueObject.empty]
  have highMass : highObj.mass=0 := by simp [highObj,RankQueueObject.mass,RankQueueObject.empty]
  have hSep : Disjoint highObj.cells extObj.cells := by
    apply Finset.disjoint_left.mpr
    intro z hzH hzE
    have hmH : z ∈ arrayCells (free+(length : ℤ)) length := by
      simpa [highObj,RankQueueObject.cells,RankQueueObject.empty,queueCells] using hzH
    have hmE : z ∈ arrayCells free length := by
      simpa [extObj,RankQueueObject.cells,RankQueueObject.empty,queueCells] using hzE
    obtain ⟨i,hi,hei⟩ := (mem_arrayCells _ _ _).mp hmH
    obtain ⟨k,hk,hek⟩ := (mem_arrayCells _ _ _).mp hmE
    omega
  have hListSep : Disjoint F extObj.cells := by
    apply Finset.disjoint_left.mpr
    intro z hz hzE
    have := extObj.above z hzE
    have := hBelow z hz
    omega
  let valid := (domain.filter (fun v => q*LocalPush.deg g.graph v < r v)).image Fin.val
  have hValid : exteriorEligibleKeys st.scalar.integerMemory st.scalar.core.mem width base q domain=valid :=
    fresh_exterior_keys_source g _ _ width base q domain r hRecords.active hRecords.degree hRecords.residual
  have hData : ExteriorQueueMemory st.scalar.integerMemory st.scalar.core.mem width base (base+3) q domain valid extObj.keys := by
    rw [extKeys,←hValid]
    exact exterior_memory_fresh _ _ width base q domain hRecords.active hRecords.exteriorQueued
  have hValidList : valid ⊆ (vertices.map Fin.val).toFinset := by
    intro k hk
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨v,?_,rfl⟩
    apply List.mem_toFinset.mp
    rw [hSet]
    exact (Finset.mem_filter.mp hv).1
  obtain ⟨steps,out,ext,ex,hSteps,outCtx,outData,outKeys,outMass,outFree,outOld,outFields,outI,outR,outQ,outW,outO,outH⟩ :=
    exterior_populate_exec m g ω width base (base+3) length capacity rank
      (by dsimp [base,width]; omega) (by dsimp [base,width]; omega) (by omega) (by dsimp [base]; omega)
      free free hFloor q domain valid vertices head F st hh extObj
      (ctx.change_floor (by rw [hf]; omega)) hData
      (fun v hv => by rw [←hSet]; exact List.mem_toFinset.mpr hv)
      hList hHead (fun z hz => (hBelow z hz).trans_le (by rw [hf]; omega)) hListSep
      (by rw [extMass]; omega) hcap hpow
  let high := highObj.other_frame extObj.cells hFloor hSep outFree outI
  have hExtKeys : ext.keys=valid := by
    rw [outKeys]
    rw [extKeys]
    exact eligible_insert_list_complete valid vertices hValidList
  have hNewSep : Disjoint ext.cells high.cells := by
    change Disjoint ext.cells highObj.cells
    exact (queue_disjoint_after_growth highObj.below hSep outOld).symm
  have hLowI (z : ℤ) (hz : 0 ≤ z) (hlo : z < free) : out.scalar.integerMemory z=st.scalar.integerMemory z := by
    apply outI z hz
    · rw [hf]; omega
    · intro hm
      have := extObj.above z hm
      omega
  refine ⟨steps,out,ext,high,ex,hSteps,?_,?_,?_,outData,hExtKeys,?_,highKeys,highMass,hNewSep,?_,outFree,outFields,hLowI,outR,outQ,outW,outO,outCtx.zero,outH⟩
  · intro slot hs
    have hs32 : slot < 32 := by
      simp only [freshHeaderSlots,List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
    rw [hLowI _ (by have := levelHeaderAddress_positive j slot; omega)
      (by unfold levelHeaderAddress; omega)]
    exact hHeader.integers slot hs
  · rw [outR]; exact hHeader.scalars
  · exact hRecords.toFreshCallRecords.refresh_frame (by omega)
      (by omega) outR outFields
  · simpa only [extMass,zero_add] using outMass
  · exact vertex_list_queue_frame hList (fun z hz => (hBelow z hz).trans_le (by rw [hf]; omega)) hListSep outI

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshFrameVertexData

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


structure FreshFrameVertexData {n : ℕ} (I : ℤ → ℤ) (R : ℤ → ℝ) (width base : ℕ)
    (domain : Finset (Fin n)) (x r : Fin n → ℝ) : Prop where
  reference : ∀ v ∈ domain, R (vertexRecordAddress width v.val base)=x v
  residual : ∀ v ∈ domain, R (vertexRecordAddress width v.val (base+1))=r v
  highBoolean : ∀ v ∈ domain, R (vertexRecordAddress width v.val (base+4))=0
  active : ∀ v ∈ domain, I (vertexRecordAddress width v.val (base+2))=0
  cache : ∀ v ∈ domain, I (vertexRecordAddress width v.val (base+4))=0
  excluded : ∀ v ∈ domain, I (vertexRecordAddress width v.val (base+5))=0
  highQueued : ∀ v ∈ domain, I (vertexRecordAddress width v.val (base+6))=0

lemma FreshCallRecords.vertexData {n : ℕ} {g : InputGraph n} {I : ℤ → ℤ} {R : ℤ → ℝ}
    {width base : ℕ} {domain : Finset (Fin n)} {x r : Fin n → ℝ}
    (h : FreshCallRecords g I R width base domain x r) : FreshFrameVertexData I R width base domain x r :=
  ⟨h.reference,h.residual,h.highBoolean,h.active,h.cache,h.excluded,h.highQueued⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshCallFrameConstruction

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

/- Construct the source call representation after the stored domain has been
initialized and its exterior queue populated. The inputs are memory facts. -/
set_option maxHeartbeats 3500000 in
lemma fresh_call_frame_construct {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (j ell width length id : ℕ) (N q : ℝ) (domain : Finset (Fin n)) (x r : Fin n → ℝ)
    (machine : MachineState) (free floor : ℤ)
    (hFrame : logical.frames j=freshFrame g [] ell j id N q domain x r)
    (hDomain : parentDomain logical j=domain)
    (hHeaderI : ∀ slot ∈ freshHeaderSlots, machine.scalar.integerMemory (levelHeaderAddress j slot)=
      freshHeaderIntegerValue free length (blockScale [] ell j N) slot)
    (hHeaderR : FreshHeaderScalars machine.scalar.core.mem j N q)
    (hRecords : FreshFrameVertexData machine.scalar.integerMemory machine.scalar.core.mem width (16*(j+1)) domain x r)
    (exterior : RankQueueObject machine.scalar.integerMemory free length (machine.scalar.core.ptrs 20) floor)
    (high : RankQueueObject machine.scalar.integerMemory (free+(length : ℤ)) length (machine.scalar.core.ptrs 20) floor)
    (hExt : ExteriorQueueMemory machine.scalar.integerMemory machine.scalar.core.mem width
      (16*(j+1)) (16*(j+1)+3) q domain
      ((domain.filter (fun v => q*LocalPush.deg g.graph v < r v)).image Fin.val) exterior.keys)
    (hCover : (domain.filter (fun v => q*LocalPush.deg g.graph v < r v)).image Fin.val ⊆ exterior.keys)
    (hHigh : high.keys=∅) :
    ∃ frame : RecursiveFrameMemory g logical j width length machine floor,
      frame.activeFoot=∅ ∧ frame.cacheFoot=∅ ∧
      frame.exteriorObject.cells=exterior.cells ∧ frame.highObject.cells=high.cells ∧
      frame.exteriorObject.mass=exterior.mass ∧ frame.highObject.mass=high.mass ∧
      frame.exteriorObject.keys=exterior.keys ∧ frame.highObject.keys=high.keys := by
  have hHeadA : machine.scalar.integerMemory (levelHeaderAddress j 1)=0 := by
    have h := hHeaderI 1 (by simp [freshHeaderSlots])
    simpa [freshHeaderIntegerValue] using h
  have hHeadC : machine.scalar.integerMemory (levelHeaderAddress j 4)=0 := by
    have h := hHeaderI 4 (by simp [freshHeaderSlots])
    simpa [freshHeaderIntegerValue] using h
  have hInt (slot : ℕ) (hs : slot ∈ freshHeaderSlots) := hHeaderI slot hs
  let frame : RecursiveFrameMemory g logical j width length machine floor := {
    N := by rw [hFrame]; exact hHeaderR.1
    q := by rw [hFrame]; exact hHeaderR.2.1
    Q := by rw [hFrame]; exact hHeaderR.2.2.1
    W := by rw [hFrame]; exact hHeaderR.2.2.2.1
    theta := by rw [hFrame]; exact hHeaderR.2.2.2.2
    block := by rw [hFrame]; simpa [freshHeaderIntegerValue,freshFrame] using hInt 14 (by simp [freshHeaderSlots])
    pc := by rw [hFrame]; simpa [freshHeaderIntegerValue,freshFrame,emptyFrame,normalizePCNumber] using hInt 0 (by simp [freshHeaderSlots])
    openBudget := by rw [hFrame]; simpa [freshHeaderIntegerValue,freshFrame,emptyFrame] using hInt 9 (by simp [freshHeaderSlots])
    needFull := by rw [hFrame]; simpa [freshHeaderIntegerValue,freshFrame,emptyFrame] using hInt 10 (by simp [freshHeaderSlots])
    children := by rw [hFrame]; simpa [freshHeaderIntegerValue,freshFrame,emptyFrame] using hInt 11 (by simp [freshHeaderSlots])
    reference := by rw [hDomain,hFrame]; exact hRecords.reference
    residual := by rw [hDomain,hFrame]; exact hRecords.residual
    activeFlags := by
      rw [hDomain,hFrame]
      intro v hv
      simpa [freshFrame,emptyFrame] using hRecords.active v hv
    cacheFlags := by
      rw [hDomain,hFrame]
      intro v hv
      simpa [freshFrame,emptyFrame] using hRecords.cache v hv
    activeVertices := []
    activeFoot := ∅
    activeRep := by rw [hHeadA]; exact ForestRep.nil
    activeNodup := by simp
    activeSet := by simp [hFrame,freshFrame,emptyFrame]
    activeCount := by rw [hFrame]; simpa [freshHeaderIntegerValue,freshFrame,emptyFrame] using hInt 3 (by simp [freshHeaderSlots])
    activeVolume := by rw [hFrame]; simpa [freshHeaderIntegerValue,freshFrame,emptyFrame,volumeNat] using hInt 2 (by simp [freshHeaderSlots])
    activeBelow := by simp
    activeAbove := by simp
    cacheVertices := []
    cacheFoot := ∅
    cacheRep := by rw [hHeadC]; exact ForestRep.nil
    cacheNodup := by simp
    cacheSet := by simp [hFrame,freshFrame,emptyFrame]
    cacheCount := by rw [hFrame]; simpa [freshHeaderIntegerValue,freshFrame,emptyFrame] using hInt 5 (by simp [freshHeaderSlots])
    cacheVolume := by rw [hFrame]; simpa [freshHeaderIntegerValue,freshFrame,emptyFrame,volumeNat] using hInt 6 (by simp [freshHeaderSlots])
    cacheBelow := by simp
    cacheAbove := by simp
    exteriorBase := free
    highBase := free+(length : ℤ)
    exteriorPointer := by simpa [freshHeaderIntegerValue] using hInt 7 (by simp [freshHeaderSlots])
    highPointer := by simpa [freshHeaderIntegerValue] using hInt 8 (by simp [freshHeaderSlots])
    exteriorObject := exterior
    highObject := high
    exteriorData := by simpa [hFrame,hDomain,freshFrame,emptyFrame] using hExt
    exteriorCover := by simpa [hFrame,freshFrame,emptyFrame] using hCover
    highBoolean := by
      rw [hFrame,hDomain]
      exact high_boolean_fresh _ _ width _ 0 domain hRecords.active hRecords.highBoolean
    virtualExcluded := by rw [hDomain]; exact hRecords.excluded
    highFlags := by rw [hDomain,hHigh]; exact high_flags_fresh _ width _ domain hRecords.highQueued
    highDomain := by rw [hHigh]; exact Finset.empty_subset _
    highValid := by
      intro v hv
      have hv' : v ∈ domain := by simpa [hDomain] using hv
      simp [hFrame,freshFrame,emptyFrame,hRecords.active v hv']
    highCover := by simp [hFrame,freshFrame,emptyFrame]
  }
  exact ⟨frame,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshCallExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 6500000 in
lemma fresh_call_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (id : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false) (ell j length capacity rank : ℕ)
    (N q : ℝ) (free head : ℤ) (vertices : List (Fin n)) (F : Finset ℤ)
    (domain : Finset (Fin n)) (x r : Fin n → ℝ)
    (hFrame : logical.frames j=freshFrame g [] ell j id N q domain x r)
    (hDomain : parentDomain logical j=domain)
    (hj : j ≤ ell) (hN : 1 ≤ N) (hFree : 128+32*((ell+2 : ℕ) : ℤ) ≤ free)
    (hDepth : st.scalar.integerMemory 2=((ell+2 : ℕ) : ℤ)) (hLength : st.scalar.integerMemory 5=(length : ℤ))
    (hLevel : st.scalar.core.ptrs 100=(j : ℤ)) (hf : st.scalar.core.ptrs 20=free)
    (hw : st.scalar.core.ptrs 50=((16*(ell+3) : ℕ) : ℤ)) (h1 : st.scalar.core.regs 31=1)
    (hNR : st.scalar.core.regs 12=N) (hqR : st.scalar.core.regs 13=q)
    (hHead : st.scalar.core.ptrs 113=head) (hList : VertexListRep st.scalar.integerMemory head vertices F)
    (hNodup : vertices.Nodup) (hSet : vertices.toFinset=domain)
    (hBelow : ∀ z ∈ F, z < free) (hAbove : ∀ z ∈ F, 128+32*((ell+2 : ℕ) : ℤ) ≤ z)
    (hDegree : ∀ v ∈ domain, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)=((g.neighbors v).length : ℤ))
    (hX : ∀ v ∈ domain, st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val 0)=x v)
    (hRhs : ∀ v ∈ domain, st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*j+1))=r v)
    (hBudget : vertices.length ≤ capacity) (hcap : rank < length) (hpow : capacity < 2^rank) :
    ∃ steps out,
    ∃ frame : RecursiveFrameMemory g logical j (16*(ell+3)) length out (128+32*((ell+2 : ℕ) : ℤ)),
      MachineEval m g ω freshCallCode st steps out ∧
      steps ≤ (⌈N⌉₊+2)*(4*(ell-j)+22)+10*length+263+
        vertices.length*(21*rank+60*(16*(ell+3))+190) ∧
      frame.activeFoot=∅ ∧ frame.cacheFoot=∅ ∧
      frame.exteriorObject.mass ≤ vertices.length ∧ frame.highObject.mass=0 ∧
      frame.pieces.Pairwise Disjoint ∧ (∀ z ∈ frame.owned, free ≤ z) ∧
      VertexListRep out.scalar.integerMemory head vertices F ∧
      free ≤ out.scalar.core.ptrs 20 ∧
      (∀ v : Fin n, ∀ field < 16*(j+1),
        out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)) ∧
      (∀ v : Fin n, ∀ field < 16*(j+1),
        out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field)) ∧
      (∀ z, 0 ≤ z → z < free → OutsideLevelHeader j z → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ z, 0 ≤ z → OutsideLevelHeader j z → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧
      out.output=st.output ∧ out.scalar.core.ptrs 0=0 ∧ out.scalar.halted=false := by
  obtain ⟨u,a,ea,hu,aHeader,aRecords,aCtx,aList,a94,aFree,aLowerI,aLowerR,aOtherI,aOtherR,aPosI,aPosR,aQ,aW,aO,aH⟩ :=
    fresh_call_setup_exec m g ω st hh ell j length N q free head vertices F domain x r hj hN hFree
      hDepth hLength hLevel hf hw h1 hNR hqR hHead hList hNodup hSet hBelow hAbove hDegree hX hRhs
  obtain ⟨v,out,ext,high,eb,hv,bHeaderI,bHeaderR,bRecords,bData,bKeys,bMass,bHighKeys,bHighMass,bSep,bList,bFree,bFields,bPosI,bR,bQ,bW,bO,b0,bH⟩ :=
    fresh_call_populate_exec m g ω a aH ell j length capacity rank N q free head vertices F domain x r
      hj hFree aFree aHeader aRecords aCtx aList a94 hSet hBelow hBudget hcap hpow
  let ext' := ext.lower_floor hFree
  let high' := high.lower_floor hFree
  obtain ⟨frame,fActive,fCache,fExt,fHigh,fExtMass,fHighMass,fExtKeys,fHighKeys⟩ :=
    fresh_call_frame_construct g logical j ell (16*(ell+3)) length id N q domain x r out free
      (128+32*((ell+2 : ℕ) : ℤ)) hFrame hDomain bHeaderI bHeaderR bRecords.vertexData ext' high' bData
      (by change _ ⊆ ext.keys; rw [bKeys]) bHighKeys
  have hPieces : frame.pieces.Pairwise Disjoint := by
    simp only [RecursiveFrameMemory.pieces,fActive,fCache,fExt,fHigh]
    simpa [ext',high',RankQueueObject.cells,RankQueueObject.lower_floor] using bSep
  have hOwned : ∀ z ∈ frame.owned, free ≤ z := by
    intro z hz
    simp only [RecursiveFrameMemory.owned,fActive,fCache,Finset.empty_union,fExt,fHigh] at hz
    rcases Finset.mem_union.mp hz with he|hh'
    · exact ext.above z he
    · exact high.above z hh'
  refine ⟨u+v,out,frame,MachineEval.seq ea eb,?_,fActive,fCache,?_,?_,hPieces,hOwned,bList,?_,?_,?_,?_,?_,bQ.trans aQ,?_,bO.trans aO,b0,bH⟩
  · convert Nat.add_le_add hu hv using 1 <;> ring
  · rw [fExtMass]; exact bMass
  · rw [fHighMass]; exact bHighMass
  · have := Int.natCast_nonneg length
    rw [aFree] at bFree
    omega
  · intro w field hf'
    rw [bFields w field (by omega) (by omega)]
    exact aLowerI w field hf'
  · intro w field hf'
    rw [bR]
    exact aLowerR w field hf'
  · intro z hz hzF hzOut
    exact (bPosI z hz hzF).trans (aPosI z hz hzF hzOut)
  · intro z hz hzOut
    rw [bR]
    exact aPosR z hz hzOut
  · rw [bW,aW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshChildExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 6000000 in
lemma fresh_child_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical next : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell j length capacity rank : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hTop : logical.top=j) (hj : j < ell)
    (hStored : (logical.frames j).active ⊆ logical.stored)
    (hRegion : (logical.frames j).active ⊆ parentDomain logical j)
    (hBlock : 1 ≤ (logical.frames j).block)
    (hFrame : next.frames (j+1)=freshFrame g [] ell (j+1) logical.nextId
      (logical.frames j).block (logical.frames j).theta (logical.frames j).active logical.x (logical.frames j).residual)
    (hDomain : parentDomain next (j+1)=(logical.frames j).active)
    (hBudget : ((pm.frames j (by omega)).activeVertices).length ≤ capacity)
    (hcap : rank < length) (hpow : capacity < 2^rank) :
    ∃ steps out,
    ∃ child : RecursiveFrameMemory g next (j+1) (16*(ell+3)) length out (128+32*((ell+2 : ℕ) : ℤ)),
      MachineEval m g ω freshChildRawCode st steps out ∧
      steps ≤ ((logical.frames j).block+2)*(4*(ell-(j+1))+22)+10*length+323+
        ((pm.frames j (by omega)).activeVertices).length*(21*rank+60*(16*(ell+3))+190) ∧
      child.activeFoot=∅ ∧ child.cacheFoot=∅ ∧
      child.exteriorObject.mass ≤ ((pm.frames j (by omega)).activeVertices).length ∧ child.highObject.mass=0 ∧
      child.pieces.Pairwise Disjoint ∧ (∀ z ∈ child.owned, st.scalar.core.ptrs 20 ≤ z) ∧
      st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 ∧
      (∀ v : Fin n, ∀ field < 16*(j+2),
        out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)) ∧
      (∀ v : Fin n, ∀ field < 16*(j+2),
        out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field)) ∧
      (∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 → OutsideLevelHeader (j+1) z →
        out.scalar.integerMemory z=Function.update
          (Function.update st.scalar.integerMemory (levelHeaderAddress j 11)
            (st.scalar.integerMemory (levelHeaderAddress j 11)+1)) (levelHeaderAddress j 0) 5 z) ∧
      (∀ z, 0 ≤ z → OutsideLevelHeader (j+1) z → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧
      out.output=st.output ∧ out.scalar.core.ptrs 0=0 ∧ out.scalar.core.ptrs 100=((j+1 : ℕ) : ℤ) ∧ out.scalar.halted=false := by
  let parent := pm.frames j (by omega)
  let free := st.scalar.core.ptrs 20
  let head := st.scalar.integerMemory (levelHeaderAddress j 1)
  obtain ⟨a,ea,a100,a113,a12,a13,aI,aR,aQ,aW,aO,aH⟩ :=
    fresh_child_preparation_exec m g ω st hh j (by rw [pm.top,hTop]) pm.one
  have aFree : a.scalar.core.ptrs 20=free := ea.pointer_frame 20 (by decide)
  have aWidth := (ea.pointer_frame 50 (by decide)).trans pm.width
  have aOne := (ea.real_register_frame 31 (by decide)).trans pm.one
  have aINeg (z : ℤ) (hz : z < 128) : a.scalar.integerMemory z=st.scalar.integerMemory z := by
    rw [aI,Function.update_of_ne (by have := levelHeaderAddress_positive j 0; omega),
      Function.update_of_ne (by have := levelHeaderAddress_positive j 11; omega)]
  have aIAbove (z : ℤ) (hz : 128+32*((ell+2 : ℕ) : ℤ) ≤ z) : a.scalar.integerMemory z=st.scalar.integerMemory z := by
    rw [aI,Function.update_of_ne ((outside_header_above (ell+2) j (by omega) z hz) 0 (by decide)),
      Function.update_of_ne ((outside_header_above (ell+2) j (by omega) z hz) 11 (by decide))]
  have aList : VertexListRep a.scalar.integerMemory head parent.activeVertices parent.activeFoot :=
    parent.activeRep.frame (fun z hz => aIAbove z (parent.activeAbove z hz))
  have aN : a.scalar.core.regs 12=((logical.frames j).block : ℝ) := by
    rw [a12,parent.block]
    simp
  have aq : a.scalar.core.regs 13=(logical.frames j).theta := a13.trans parent.theta
  have aDegree : ∀ v ∈ (logical.frames j).active,
      a.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)=((g.neighbors v).length : ℤ) := by
    intro v hv
    rw [aINeg _ (by have := vertexRecordAddress_negative (16*(ell+3)) v.val 0; omega)]
    exact pm.graphCache.degree v (hStored hv)
  have aX : ∀ v ∈ (logical.frames j).active,
      a.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val 0)=logical.x v := by
    intro v hv
    rw [aR]
    exact pm.potential v
  have aRhs : ∀ v ∈ (logical.frames j).active,
      a.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+1))=(logical.frames j).residual v := by
    intro v hv
    rw [aR]
    exact parent.residual v (hRegion hv)
  obtain ⟨u,out,child,eb,hu,hActive,hCache,hMass,hHigh,hPieces,hOwned,hList,hFree,hLowerI,hLowerR,hPosI,hPosR,hQ,hW,hO,h0,hH⟩ :=
    fresh_call_exec m g ω next logical.nextId a aH ell (j+1) length capacity rank
      (logical.frames j).block (logical.frames j).theta free head parent.activeVertices parent.activeFoot
      (logical.frames j).active logical.x (logical.frames j).residual hFrame hDomain (by omega)
      (by exact_mod_cast hBlock) pm.allocator
      ((aINeg 2 (by norm_num)).trans pm.depthMemory) ((aINeg 5 (by norm_num)).trans pm.lengthMemory)
      a100 aFree aWidth aOne aN aq a113 aList parent.activeNodup parent.activeSet
      parent.activeBelow parent.activeAbove aDegree aX aRhs hBudget hcap hpow
  refine ⟨60+u,out,child,MachineEval.seq ea eb,?_,hActive,hCache,hMass,hHigh,hPieces,hOwned,hFree,?_,?_,?_,?_,hQ.trans aQ,?_,hO.trans aO,h0,(eb.pointer_frame 100 (by decide)).trans a100,hH⟩
  · dsimp only [parent] at hu
    simp only [Nat.ceil_natCast] at hu
    omega
  · intro v field hf'
    rw [hLowerI v field (by omega)]
    exact aINeg _ (by have := vertexRecordAddress_negative (16*(ell+3)) v.val field; omega)
  · intro v field hf'
    rw [hLowerR v field (by omega),aR]
  · intro z hz hzF hzOut
    rw [hPosI z hz hzF hzOut,aI]
  · intro z hz hzOut
    rw [hPosR z hz hzOut,aR]
  · rw [hW,aW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshChildOldFrames

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 5000000 in
lemma fresh_child_old_frames {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (st out : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top < ell)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hLowerI : ∀ v : Fin n, ∀ field < 16*(logical.top+2),
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field))
    (hLowerR : ∀ v : Fin n, ∀ field < 16*(logical.top+2),
      out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field))
    (hPosI : ∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 → OutsideLevelHeader (logical.top+1) z →
      out.scalar.integerMemory z=Function.update
        (Function.update st.scalar.integerMemory (levelHeaderAddress logical.top 11)
          (st.scalar.integerMemory (levelHeaderAddress logical.top 11)+1)) (levelHeaderAddress logical.top 0) 5 z)
    (hPosR : ∀ z, 0 ≤ z → OutsideLevelHeader (logical.top+1) z → out.scalar.core.mem z=st.scalar.core.mem z) :
    ∃ frames : ∀ i ≤ logical.top, RecursiveFrameMemory g (spawnChildState g ell logical) i
        (16*(ell+3)) length out (128+32*((ell+2 : ℕ) : ℤ)),
      ∀ i hi, (frames i hi).pieces=(pm.frames i hi).pieces ∧
        (frames i hi).owned=(pm.frames i hi).owned ∧
        (frames i hi).exteriorObject.mass=(pm.frames i hi).exteriorObject.mass ∧
        (frames i hi).highObject.mass=(pm.frames i hi).highObject.mass := by
  let next := spawnChildState g ell logical
  have hHeader (i : ℕ) (hi : i ≤ logical.top) (slot : ℕ) (hs : slot < 32) :
      out.scalar.integerMemory (levelHeaderAddress i slot)=Function.update
        (Function.update st.scalar.integerMemory (levelHeaderAddress logical.top 11)
          (st.scalar.integerMemory (levelHeaderAddress logical.top 11)+1)) (levelHeaderAddress logical.top 0) 5
          (levelHeaderAddress i slot) := by
    apply hPosI
    · have := levelHeaderAddress_positive i slot; omega
    · have := pm.allocator
      unfold levelHeaderAddress
      omega
    · exact outside_header_other (logical.top+1) i slot (by omega) hs
  have hOldHeader (i : ℕ) (hi : i ≤ logical.top) (slot : ℕ) (hs : slot < 32)
      (hslot : slot ≠ 0 ∧ slot ≠ 11) :
      out.scalar.integerMemory (levelHeaderAddress i slot)=st.scalar.integerMemory (levelHeaderAddress i slot) := by
    rw [hHeader i hi slot hs,Function.update_of_ne,Function.update_of_ne]
    · intro he
      exact hslot.2 (levelHeaderAddress_injective i logical.top slot 11 hs (by decide) he).2
    · intro he
      exact hslot.1 (levelHeaderAddress_injective i logical.top slot 0 hs (by decide) he).2
  have hFrame (i : ℕ) (hi : i ≤ logical.top) : next.frames i={logical.frames i with
      pc := (next.frames i).pc,openBudget := (next.frames i).openBudget,
      needFull := (next.frames i).needFull,childrenThisEpisode := (next.frames i).childrenThisEpisode} := by
    by_cases he : i=logical.top
    · subst i
      simp only [next,spawnChild_parent]
    · rw [show next.frames i=logical.frames i from spawnChild_other g ell logical i he (by omega)]
  have hControlPC (i : ℕ) (hi : i ≤ logical.top) :
      out.scalar.integerMemory (levelHeaderAddress i 0)=(normalizePCNumber (next.frames i).pc : ℤ) := by
    by_cases he : i=logical.top
    · subst i
      rw [hHeader _ hi 0 (by decide)]
      simp [next,spawnChild_parent,normalizePCNumber]
    · have h0 : levelHeaderAddress i 0 ≠ levelHeaderAddress logical.top 0 := by
        intro h; exact he (levelHeaderAddress_injective i logical.top 0 0 (by decide) (by decide) h).1
      have h11 : levelHeaderAddress i 0 ≠ levelHeaderAddress logical.top 11 := by
        intro h; exact he (levelHeaderAddress_injective i logical.top 0 11 (by decide) (by decide) h).1
      rw [hHeader i hi 0 (by decide),Function.update_of_ne h0,Function.update_of_ne h11]
      rw [show next.frames i=logical.frames i from spawnChild_other g ell logical i he (by omega)]
      exact (pm.frames i hi).pc
  have hControlBudget (i : ℕ) (hi : i ≤ logical.top) :
      out.scalar.integerMemory (levelHeaderAddress i 9)=if (next.frames i).openBudget then 1 else 0 := by
    rw [hOldHeader i hi 9 (by decide) (by decide)]
    by_cases he : i=logical.top
    · subst i; simpa only [next,spawnChild_parent] using (pm.frames _ hi).openBudget
    · rw [show next.frames i=logical.frames i from spawnChild_other g ell logical i he (by omega)]
      exact (pm.frames i hi).openBudget
  have hControlNeed (i : ℕ) (hi : i ≤ logical.top) :
      out.scalar.integerMemory (levelHeaderAddress i 10)=if (next.frames i).needFull then 1 else 0 := by
    rw [hOldHeader i hi 10 (by decide) (by decide)]
    by_cases he : i=logical.top
    · subst i; simpa only [next,spawnChild_parent] using (pm.frames _ hi).needFull
    · rw [show next.frames i=logical.frames i from spawnChild_other g ell logical i he (by omega)]
      exact (pm.frames i hi).needFull
  have hControlChildren (i : ℕ) (hi : i ≤ logical.top) :
      out.scalar.integerMemory (levelHeaderAddress i 11)=((next.frames i).childrenThisEpisode : ℤ) := by
    by_cases he : i=logical.top
    · subst i
      rw [hHeader _ hi 11 (by decide)]
      simp only [level_header_update_read,show ¬(11 : ℕ)=0 by decide,if_false,if_true,
        next,spawnChild_parent,Nat.cast_add,Nat.cast_one]
      rw [(pm.frames _ hi).children]
    · have h0 : levelHeaderAddress i 11 ≠ levelHeaderAddress logical.top 0 := by
        intro h; exact he (levelHeaderAddress_injective i logical.top 11 0 (by decide) (by decide) h).1
      have h11 : levelHeaderAddress i 11 ≠ levelHeaderAddress logical.top 11 := by
        intro h; exact he (levelHeaderAddress_injective i logical.top 11 11 (by decide) (by decide) h).1
      rw [hHeader i hi 11 (by decide),Function.update_of_ne h0,Function.update_of_ne h11]
      rw [show next.frames i=logical.frames i from spawnChild_other g ell logical i he (by omega)]
      exact (pm.frames i hi).children
  let frames (i : ℕ) (hi : i ≤ logical.top) := (pm.frames i hi).control_frame
    (next.frames i).pc (next.frames i).openBudget (next.frames i).needFull (next.frames i).childrenThisEpisode
    (hFrame i hi) (spawnChild_domain_old g ell logical i hi) hFree
    (fun slot hs hn => hOldHeader i hi slot hs (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
      exact ⟨hn.1,hn.2.2.2⟩))
    (fun slot hs => hPosR _ (by have := levelHeaderAddress_positive i slot; omega)
      (outside_header_other (logical.top+1) i slot (by omega) hs))
    (hControlPC i hi) (hControlBudget i hi) (hControlNeed i hi) (hControlChildren i hi)
    (fun v hv field hf => hLowerI v field (by omega))
    (fun v hv field hf => hLowerR v field (by omega))
    (fun z hz => by
      have hlo := (pm.frames i hi).owned_below z hz
      have hhi := (pm.frames i hi).owned_above z hz
      rw [hPosI z (by omega) hlo (outside_header_above (ell+2) (logical.top+1) (by omega) z hhi)]
      rw [Function.update_of_ne ((outside_header_above (ell+2) logical.top (by omega) z hhi) 0 (by decide)),
        Function.update_of_ne ((outside_header_above (ell+2) logical.top (by omega) z hhi) 11 (by decide))])
  refine ⟨frames,?_⟩
  intro i hi
  exact ⟨rfl,rfl,rfl,rfl⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshChildMemory

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 6500000 in
lemma fresh_child_memory {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (st out : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top < ell)
    (child : RecursiveFrameMemory g (spawnChildState g ell logical) (logical.top+1)
      (16*(ell+3)) length out (128+32*((ell+2 : ℕ) : ℤ)))
    (hPieces : child.pieces.Pairwise Disjoint)
    (hNewAbove : ∀ z ∈ child.owned, st.scalar.core.ptrs 20 ≤ z)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hLowerI : ∀ v : Fin n, ∀ field < 16*(logical.top+2),
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field))
    (hLowerR : ∀ v : Fin n, ∀ field < 16*(logical.top+2),
      out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field))
    (hPosI : ∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 → OutsideLevelHeader (logical.top+1) z →
      out.scalar.integerMemory z=Function.update
        (Function.update st.scalar.integerMemory (levelHeaderAddress logical.top 11)
          (st.scalar.integerMemory (levelHeaderAddress logical.top 11)+1)) (levelHeaderAddress logical.top 0) 5 z)
    (hPosR : ∀ z, 0 ≤ z → OutsideLevelHeader (logical.top+1) z → out.scalar.core.mem z=st.scalar.core.mem z)
    (hZero : out.scalar.core.ptrs 0=0) (hTop : out.scalar.core.ptrs 100=((logical.top+1 : ℕ) : ℤ))
    (hWidth : out.scalar.core.ptrs 50=((16*(ell+3) : ℕ) : ℤ))
    (hAlpha : out.scalar.core.regs 30=α) (hOne : out.scalar.core.regs 31=1)
    (hOutput : out.output=[]) :
    ∃ memory : RecursiveMachineMemory g s α ε ell length (spawnChildState g ell logical) out,
      memory.queueMass=pm.queueMass+child.queueMass := by
  let next := spawnChildState g ell logical
  obtain ⟨oldFrames,hOld⟩ := fresh_child_old_frames g logical s α ε ell length st out pm hDepth hFree hLowerI hLowerR hPosI hPosR
  let frames (i : ℕ) (hi : i ≤ next.top) : RecursiveFrameMemory g next i (16*(ell+3)) length out
      (128+32*((ell+2 : ℕ) : ℤ)) := if ho : i ≤ logical.top then oldFrames i ho else by
        have he : i=logical.top+1 := by change i ≤ logical.top+1 at hi; omega
        subst i
        exact child
  have allOld (i : ℕ) (hi : i ≤ logical.top) (hi' : i ≤ next.top) : frames i hi'=oldFrames i hi := by
    simp only [frames,dif_pos hi]
  have allChild : frames (logical.top+1) (by change logical.top+1 ≤ logical.top+1; omega)=child := by
    simp [frames]
  have ownedOld (i : ℕ) (hi : i ≤ logical.top) (hi' : i ≤ next.top) :
      (frames i hi').owned=(pm.frames i hi).owned := by
    rw [allOld i hi hi']
    exact (hOld i hi).2.1
  have hGlobalI (z : ℤ) (hz : 0 ≤ z) (hs : z < 128) : out.scalar.integerMemory z=st.scalar.integerMemory z := by
    have hF := pm.allocator
    rw [hPosI z hz (by omega) (outside_header_low (logical.top+1) z hs),
      Function.update_of_ne ((outside_header_low logical.top z hs) 0 (by decide)),
      Function.update_of_ne ((outside_header_low logical.top z hs) 11 (by decide))]
  have hRowI (z : ℤ) (hz : 128+32*((ell+2 : ℕ) : ℤ) ≤ z) (hf : z < st.scalar.core.ptrs 20) :
      out.scalar.integerMemory z=st.scalar.integerMemory z := by
    rw [hPosI z (by omega) hf (outside_header_above (ell+2) (logical.top+1) (by omega) z hz),
      Function.update_of_ne ((outside_header_above (ell+2) logical.top (by omega) z hz) 0 (by decide)),
      Function.update_of_ne ((outside_header_above (ell+2) logical.top (by omega) z hz) 11 (by decide))]
  have hCache : GraphCache g out.scalar.integerMemory (16*(ell+3)) logical.stored (out.scalar.core.ptrs 20) := by
    apply GraphCache.mono_free (hle:=hFree)
    apply pm.graphCache.frame g st.scalar.integerMemory out.scalar.integerMemory (16*(ell+3)) logical.stored (st.scalar.core.ptrs 20)
    · intro v field hf
      exact hLowerI v field (by omega)
    · intro v hv i hi
      apply hRowI
      · have := pm.rowAbove v hv
        have := Int.natCast_nonneg i
        omega
      · exact pm.graphCache.belowFree v hv i hi
  have hRowEq : cachedRowCells g out.scalar.integerMemory (16*(ell+3)) next.stored=
      cachedRowCells g st.scalar.integerMemory (16*(ell+3)) logical.stored := by
    change logical.stored.biUnion _=logical.stored.biUnion _
    apply Finset.biUnion_congr rfl
    intro v hv
    rw [hLowerI v 1 (by omega)]
  have hRowsBelow : ∀ z ∈ cachedRowCells g st.scalar.integerMemory (16*(ell+3)) logical.stored,
      z < st.scalar.core.ptrs 20 := by
    intro z hz
    obtain ⟨v,hv,hzv⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨i,hi,rfl⟩ := (mem_arrayCells _ _ _).mp hzv
    exact pm.graphCache.belowFree v hv i hi
  refine ⟨{
    zero := hZero
    top := hTop
    width := hWidth
    alphaRegister := hAlpha
    one := hOne
    alphaMemory := (hPosR 0 (by norm_num) (outside_header_low (logical.top+1) 0 (by norm_num))).trans pm.alphaMemory
    epsilonMemory := (hPosR 1 (by norm_num) (outside_header_low (logical.top+1) 1 (by norm_num))).trans pm.epsilonMemory
    depthMemory := (hGlobalI 2 (by norm_num) (by norm_num)).trans pm.depthMemory
    lengthMemory := (hGlobalI 5 (by norm_num) (by norm_num)).trans pm.lengthMemory
    seedMemory := (hGlobalI 0 (by norm_num) (by norm_num)).trans pm.seedMemory
    allocator := pm.allocator.trans hFree
    potential := fun v => (hLowerR v 0 (by omega)).trans (pm.potential v)
    seedMarker := fun v => (hLowerR v 2 (by omega)).trans (pm.seedMarker v)
    boundary := (hGlobalI 7 (by norm_num) (by norm_num)).trans pm.boundary
    graphCache := hCache
    rowAbove := ?_
    knownDegree := ?_
    unknownDegree := ?_
    frames := frames
    pieceSeparation := ?_
    frameSeparation := ?_
    cacheSeparation := ?_
    output := hOutput
  },?_⟩
  · intro v hv
    rw [hLowerI v 1 (by omega)]
    exact pm.rowAbove v hv
  · intro v hv
    rw [hLowerI v 0 (by omega)]
    exact pm.knownDegree v hv
  · intro v hv
    rw [hLowerI v 0 (by omega)]
    exact pm.unknownDegree v hv
  · intro i hi
    by_cases ho : i ≤ logical.top
    · rw [allOld i ho hi,(hOld i ho).1]
      exact pm.pieceSeparation i ho
    · have he : i=logical.top+1 := by change i ≤ logical.top+1 at hi; omega
      subst i
      rw [allChild]
      exact hPieces
  · intro i hi j hj hij
    by_cases hoi : i ≤ logical.top <;> by_cases hoj : j ≤ logical.top
    · rw [ownedOld i hoi hi,ownedOld j hoj hj]
      exact pm.frameSeparation i hoi j hoj hij
    · have hej : j=logical.top+1 := by change j ≤ logical.top+1 at hj; omega
      subst j
      rw [ownedOld i hoi hi,allChild]
      apply Finset.disjoint_left.mpr
      intro z hz hzChild
      have := (pm.frames i hoi).owned_below z hz
      have := hNewAbove z hzChild
      omega
    · have hei : i=logical.top+1 := by change i ≤ logical.top+1 at hi; omega
      subst i
      rw [allChild,ownedOld j hoj hj]
      apply Disjoint.symm
      apply Finset.disjoint_left.mpr
      intro z hz hzChild
      have := (pm.frames j hoj).owned_below z hz
      have := hNewAbove z hzChild
      omega
    · have hei : i=logical.top+1 := by change i ≤ logical.top+1 at hi; omega
      have hej : j=logical.top+1 := by change j ≤ logical.top+1 at hj; omega
      exact False.elim (hij (hei.trans hej.symm))
  · intro i hi
    rw [hRowEq]
    by_cases ho : i ≤ logical.top
    · rw [ownedOld i ho hi]
      exact pm.cacheSeparation i ho
    · have he : i=logical.top+1 := by change i ≤ logical.top+1 at hi; omega
      subst i
      rw [allChild]
      apply Finset.disjoint_left.mpr
      intro z hz hzRow
      have := hNewAbove z hz
      have := hRowsBelow z hzRow
      omega
  · change (∑ i ∈ Finset.range (logical.top+1+1), if hi : i ≤ logical.top+1 then
      (frames i hi).queueMass else 0)=pm.queueMass+child.queueMass
    rw [Finset.sum_range_succ]
    have hSum : (∑ i ∈ Finset.range (logical.top+1), if hi : i ≤ logical.top+1 then
        (frames i hi).queueMass else 0)=pm.queueMass := by
      unfold RecursiveMachineMemory.queueMass
      apply Finset.sum_congr rfl
      intro i hi
      have hlo : i ≤ logical.top := by have := Finset.mem_range.mp hi; omega
      rw [dif_pos (show i ≤ logical.top+1 by omega),dif_pos hlo]
      change (frames i (show i ≤ next.top by change i ≤ logical.top+1; omega)).queueMass=(pm.frames i hlo).queueMass
      rw [allOld i hlo]
      unfold RecursiveFrameMemory.queueMass
      rw [(hOld i hlo).2.2.1,(hOld i hlo).2.2.2]
    rw [hSum,dif_pos (le_refl (logical.top+1))]
    change pm.queueMass+(frames (logical.top+1) (show logical.top+1 ≤ next.top by change logical.top+1 ≤ logical.top+1; omega)).queueMass= _
    rw [allChild]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshChildSimulation

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 5000000 in
lemma fresh_child_simulation (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length capacity rank : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hDepth : logical.top < ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hRegion : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hBlock : 1 ≤ (logical.frames logical.top).block)
    (hBudget : ((pm.frames logical.top (le_refl _)).activeVertices).length ≤ capacity)
    (hcap : rank < length) (hpow : capacity < 2^rank) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (spawnChildState g ell logical) out,
      MachineEval m g ω freshChildCode st steps out ∧
      memory.queueMass ≤ pm.queueMass+((pm.frames logical.top (le_refl _)).activeVertices).length ∧
      steps ≤ ((logical.frames logical.top).block+2)*(4*(ell-(logical.top+1))+22)+10*length+324+
        ((pm.frames logical.top (le_refl _)).activeVertices).length*(21*rank+60*(16*(ell+3))+190) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  obtain ⟨steps,mid,child,ex,hSteps,hActive,hCache,hMass,hHigh,hPieces,hOwned,hFree,hLowerI,hLowerR,hPosI,hPosR,hQ,hW,hO,h0,hTop,hH⟩ :=
    fresh_child_exec m g ω logical (spawnChildState g ell logical) s α ε ell logical.top length capacity rank st hh pm rfl
      hDepth hStored hRegion hBlock (spawnChild_child g ell logical) (spawnChild_domain_child g ell logical)
      hBudget hcap hpow
  have hAlphaMem : mid.scalar.core.mem 0=α :=
    (hPosR 0 (by norm_num) (outside_header_low (logical.top+1) 0 (by norm_num))).trans pm.alphaMemory
  let out := payUnit (realWrite mid 30 α)
  have el : MachineEval m g ω (coreCode (.load 30 0)) mid 1 out := by
    simpa only [out,coreCode,h0,hAlphaMem] using load_eval m g ω mid 30 0 hH
  let child' := child.memory_frame (out:=out) le_rfl (by intros; rfl) (by intros; rfl)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
  obtain ⟨memory,hMemoryMass⟩ := fresh_child_memory g logical s α ε ell length st out pm hDepth child' hPieces hOwned hFree
    hLowerI hLowerR hPosI hPosR h0 hTop
    ((ex.pointer_frame 50 (by decide)).trans pm.width)
    (by simp [out,payUnit,pcSet,realWrite])
    ((ex.real_register_frame 31 (by decide)).trans pm.one) (hO.trans pm.output)
  refine ⟨steps+1,out,memory,MachineEval.seq ex el,?_,by omega,hQ,?_,hO,hH,(fun v => hLowerI v 7 (by omega))⟩
  · rw [hMemoryMass]
    change pm.queueMass+(child.exteriorObject.mass+child.highObject.mass) ≤ _
    rw [hHigh]
    omega
  · change mid.work+1= _
    rw [hW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution : ∀ (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length capacity rank : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hDepth : logical.top < ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hRegion : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hBlock : 1 ≤ (logical.frames logical.top).block)
    (hBudget : ((pm.frames logical.top (le_refl _)).activeVertices).length ≤ capacity)
    (hcap : rank < length) (hpow : capacity < 2^rank),
∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (spawnChildState g ell logical) out,
      MachineEval m g ω freshChildCode st steps out ∧
      memory.queueMass ≤ pm.queueMass+((pm.frames logical.top (le_refl _)).activeVertices).length ∧
      steps ≤ ((logical.frames logical.top).block+2)*(4*(ell-(logical.top+1))+22)+10*length+324+
        ((pm.frames logical.top (le_refl _)).activeVertices).length*(21*rank+60*(16*(ell+3))+190) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  exact @NearlyOptimalPPR.Computation.fresh_child_simulation
