-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.exterior_activation_apply_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:46:19.367351+00:00
-- url     : https://prove2.me/submissions/16a96404-75a8-4c62-a202-787116b279a7

import Batteries.Data.BinomialHeap
import Definitions.Def_NearlyOptimalPPR_Computation_compiler_buffers
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

lemma nodeCells_mem_iff (p a : ℤ) : a ∈ nodeCells p ↔ p ≤ a ∧ a ≤ p+2 := by
  simp only [nodeCells,Finset.mem_insert,Finset.mem_singleton]
  omega

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IntegerScaleCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma integerScaleCode_wellFormed : integerScaleCode.wellFormed := by
  simp [integerScaleCode,integerScaleLoopCode,integerScaleBodyCode,integerScaleBodyRoutine,
    PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,sequenceCode,coreCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.MemoryEffects

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def integerReadOnly : Instruction → Prop
  | .scalar (.integerStore _ _) => False
  | _ => True

lemma atomState_integer_readOnly (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (i : Instruction) (st : MachineState) (h : integerReadOnly i) :
    (atomState m g ω i st).scalar.integerMemory=st.scalar.integerMemory := by
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
    | core c => cases c <;> simp_all [integerReadOnly,atomState,machineStep,pcSet,hh,LocalPush.step,scalarProgram,
        LocalPush.coreProgram,SmaleNinth.RAMStep] <;> split_ifs <;> rfl
    | _ => simp_all [integerReadOnly,atomState,machineStep,pcSet,hh,LocalPush.step,scalarProgram]

lemma MachineEval.integer_memory_frame {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {code : MachineCode} {st out : MachineState} {u : ℕ} (e : MachineEval m g ω code st u out)
    (h : code.allAtoms integerReadOnly) : out.scalar.integerMemory=st.scalar.integerMemory := by
  apply e.frame (fun z => z.scalar.integerMemory) (by intros; rfl) (by intro; rfl)
  exact code.allAtoms_mono _ _ (fun i hi z => atomState_integer_readOnly m g ω i z hi) h

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


lemma levelHeaderAddressCode_wellFormed (slot : ℕ) : (levelHeaderAddressCode slot).wellFormed := by
  simp [levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

lemma levelHeaderIntegerLoadCode_wellFormed (slot : ℕ) : (levelHeaderIntegerLoadCode slot).wellFormed := by
  refine ⟨levelHeaderAddressCode_wellFormed slot,?_⟩
  simp [MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma levelHeaderIntegerStoreCode_wellFormed (slot : ℕ) : (levelHeaderIntegerStoreCode slot).wellFormed := by
  refine ⟨levelHeaderAddressCode_wellFormed slot,?_⟩
  simp [MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma levelHeaderRealLoadCode_wellFormed (slot : ℕ) : (levelHeaderRealLoadCode slot).wellFormed := by
  refine ⟨levelHeaderAddressCode_wellFormed slot,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma levelHeaderRealStoreCode_wellFormed (slot : ℕ) : (levelHeaderRealStoreCode slot).wellFormed := by
  refine ⟨levelHeaderAddressCode_wellFormed slot,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.LevelHeaderIntegerFrom

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderIntegerFromCode_wellFormed (slot source : ℕ) : (levelHeaderIntegerFromCode slot source).wellFormed := by
  refine ⟨?_,levelHeaderIntegerStoreCode_wellFormed slot⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
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

-- Proof module: Solutions.LevelContextPreparation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelContextCode_wellFormed : levelContextCode.wellFormed := by
  simp [levelContextCode,levelContextInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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


lemma vertexAddressCode_wellFormed : vertexAddressCode.wellFormed := by
  refine ⟨integerScaleCode_wellFormed,?_⟩
  simp [vertexAddressTailCode,sequenceCode,coreCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.VertexFlagClear

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma vertexFlagClearCode_wellFormed : vertexFlagClearCode.wellFormed := by
  simp [vertexFlagClearCode,vertexIntegerStoreCode,vertexAddressCode_wellFormed,
    coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveMachineFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

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

lemma node_alloc_frame (I : ℤ → ℤ) (p key z : ℤ) (hz : z ∉ nodeCells p) :
    nodeAllocMemory I p key z=I z := by
  have hz' : z ≠ p ∧ z ≠ p+1 ∧ z ≠ p+2 := by simpa [nodeCells] using hz
  simp [nodeAllocMemory,Function.update_of_ne hz'.1,Function.update_of_ne hz'.2.1,Function.update_of_ne hz'.2.2]

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexFlagSet

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexFlagSetCode_wellFormed : vertexFlagSetCode.wellFormed := by
  simp [vertexFlagSetCode,vertexIntegerStoreCode,vertexAddressCode_wellFormed,
    coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.LevelHeaderTo

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderIntegerToCode_wellFormed (slot target : ℕ) : (levelHeaderIntegerToCode slot target).wellFormed := by
  refine ⟨levelHeaderIntegerLoadCode_wellFormed slot,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelVertexFlagClear

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelVertexFlagClearCode_wellFormed (offset : ℕ) : (levelVertexFlagClearCode offset).wellFormed := by
  refine ⟨?_,vertexFlagClearCode_wellFormed⟩
  simp [levelVertexOffsetCode,levelVertexOffsetInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.OwnedFIFOFrames

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma VertexListRep.positive_cells {n : ℕ} {I : ℤ → ℤ} {head : ℤ} {vertices : List (Fin n)} {F : Finset ℤ}
    (h : VertexListRep I head vertices F) : ∀ z ∈ F, 2 ≤ z := ForestRep.positive_cells h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RealMemoryEffects

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def realMemoryReadOnly : Instruction → Prop
  | .solve _ | .scalar (.core (.store _ _)) => False
  | _ => True

instance realMemoryReadOnlyDecidable (i : Instruction) : Decidable (realMemoryReadOnly i) := by
  cases i with
  | solve r => exact isFalse id
  | emit a b => exact isTrue trivial
  | scalar s =>
    cases s with
    | core c => cases c <;> simp only [realMemoryReadOnly] <;> infer_instance
    | _ => exact isTrue trivial

lemma atomState_real_memory_readOnly (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (i : Instruction) (st : MachineState) (h : realMemoryReadOnly i) :
    (atomState m g ω i st).scalar.core.mem=st.scalar.core.mem := by
  by_cases hh : st.scalar.halted=true
  · simp [atomState,machineStep,pcSet,hh]
  have hh : st.scalar.halted=false := Bool.eq_false_iff.mpr hh
  cases i with
  | emit a b => simp [atomState,machineStep,pcSet,hh]
  | solve r => exact False.elim h
  | scalar i =>
    cases i with
    | core c => cases c <;> simp_all [realMemoryReadOnly,atomState,machineStep,pcSet,hh,LocalPush.step,scalarProgram,
        LocalPush.coreProgram,SmaleNinth.RAMStep] <;> split_ifs <;> rfl
    | _ => simp_all [realMemoryReadOnly,atomState,machineStep,pcSet,hh,LocalPush.step,scalarProgram]

lemma MachineEval.real_memory_frame {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {code : MachineCode} {st out : MachineState} {u : ℕ} (e : MachineEval m g ω code st u out)
    (h : code.allAtoms realMemoryReadOnly) : out.scalar.core.mem=st.scalar.core.mem := by
  apply e.frame (fun z => z.scalar.core.mem) (by intros; rfl) (by intro; rfl)
  exact code.allAtoms_mono _ _ (fun i hi z => atomState_real_memory_readOnly m g ω i z hi) h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.UnitWork

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

instance unitInstructionDecidable (i : Instruction) : Decidable (unitInstruction i) := by
  cases i with
  | solve r => exact isFalse id
  | emit a b => exact isTrue trivial
  | scalar i =>
    cases i with
    | core c => cases c <;> simp [unitInstruction,straightInstruction] <;> infer_instance
    | _ => simp [unitInstruction,straightInstruction] <;> infer_instance

lemma MachineEval.unit_work {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {code : MachineCode} {st out : MachineState} {steps : ℕ}
    (e : MachineEval m g ω code st steps out) (hForm : code.wellFormed)
    (hUnit : code.allAtoms unitInstruction) (hh : st.scalar.halted=false) : out.work=st.work+steps := by
  induction e with
  | skip st => simp
  | atom i st ready =>
    rw [pcSet_work,unitInstruction_work m g ω i hUnit st hh]
    simp
  | seq ea eb ia ib =>
    have ha := ia hForm.1 hUnit.1 hh
    have hb := ib hForm.2 hUnit.2 ((ea.halted hForm.1).trans hh)
    rw [hb,ha]
    push_cast
    ring
  | realNonpos h guard ea ih =>
    rw [ih hForm.1 hUnit.1 hh,payUnit_work]
    push_cast
    ring
  | realPos h guard eb ih =>
    rw [payUnit_work,ih hForm.2 hUnit.2 hh,payUnit_work]
    push_cast
    ring
  | pointerLe h guard ea ih =>
    rw [ih hForm.1 hUnit.1 hh,payUnit_work]
    push_cast
    ring
  | pointerGt h guard eb ih =>
    rw [payUnit_work,ih hForm.2 hUnit.2 hh,payUnit_work]
    push_cast
    ring
  | realDone h guard => simp only [payUnit_work,Nat.cast_one]
  | realNext h guard eb er ib ir =>
    have hb := ib hForm hUnit hh
    have hr := ir hForm hUnit ((eb.halted hForm).trans hh)
    rw [hr,payUnit_work,hb,payUnit_work]
    push_cast
    ring
  | pointerDone h guard => simp only [payUnit_work,Nat.cast_one]
  | pointerNext h guard eb er ib ir =>
    have hb := ib hForm hUnit hh
    have hr := ir hForm hUnit ((eb.halted hForm).trans hh)
    rw [hr,payUnit_work,hb,payUnit_work]
    push_cast
    ring

end
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

-- Proof module: Solutions.PayloadLevelLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 4500000 in
lemma payload_level_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    {Payload : Type} (body : MachineCode) (bound stop queryCost : ℕ)
    (data : MachineState → Payload) (update : ℕ → Payload → Payload)
    (Ctx : ℕ → MachineState → Prop) (hForm : body.wellFormed) (hUnit : body.allAtoms unitInstruction)
    (hDataUnit : ∀ st, data (payUnit st)=data st)
    (hCtxUnit : ∀ i st, Ctx i st → Ctx i (payUnit st))
    (hBody : ∀ i < stop, ∀ (st : MachineState), st.scalar.halted=false → Ctx i st →
      st.scalar.core.ptrs 109=(i : ℤ) → st.scalar.core.ptrs 111=(stop : ℤ) →
      ∃ u out, MachineEval m g ω body st u out ∧ u ≤ bound ∧
        out.scalar.core.ptrs 109=((i+1 : ℕ) : ℤ) ∧ out.scalar.core.ptrs 111=(stop : ℤ) ∧
        data out=update i (data st) ∧ Ctx (i+1) out ∧
        out.scalar.queries=st.scalar.queries+queryCost ∧ out.output=st.output)
    (remaining : ℕ) :
    ∀ (i : ℕ) (st : MachineState), st.scalar.halted=false → Ctx i st →
      i+remaining=stop → st.scalar.core.ptrs 109=(i : ℤ) → st.scalar.core.ptrs 111=(stop : ℤ) →
      ∃ steps out, MachineEval m g ω (.whilePointer 111 109 body) st steps out ∧
        steps ≤ remaining*(bound+2)+1 ∧ out.scalar.core.ptrs 109=(stop : ℤ) ∧
        out.scalar.core.ptrs 111=(stop : ℤ) ∧ data out=levelPayloadFold update i remaining (data st) ∧
        Ctx stop out ∧ out.scalar.queries=st.scalar.queries+remaining*queryCost ∧
        out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction remaining with
  | zero =>
    intro i st hh hCtx hCount hIndex hStop
    have he : i=stop := by omega
    have ex : MachineEval m g ω (.whilePointer 111 109 body) st 1 (payUnit st) :=
      MachineEval.pointerDone hh (by rw [hStop,hIndex,he])
    refine ⟨1,payUnit st,ex,by omega,?_,hStop,hDataUnit st,?_,?_,ex.unit_work hForm hUnit hh,rfl,hh⟩
    · change st.scalar.core.ptrs 109=(stop : ℤ)
      simpa only [he] using hIndex
    · simpa only [he] using hCtxUnit i st hCtx
    · change st.scalar.queries=st.scalar.queries+0*queryCost
      omega
  | succ remaining ih =>
    intro i st hh hCtx hCount hIndex hStop
    obtain ⟨u,b,eb,hu,bIndex,bStop,bData,bCtx,bQ,bO⟩ := hBody i (by omega) (payUnit st) hh
      (hCtxUnit i st hCtx) hIndex hStop
    have bH : b.scalar.halted=false := (eb.halted hForm).trans hh
    obtain ⟨w,out,er,hw,cIndex,cStop,cData,cCtx,cQ,cW,cO,cH⟩ := ih (i+1) (payUnit b) bH
      (hCtxUnit (i+1) b bCtx) (by omega) bIndex bStop
    have ex : MachineEval m g ω (.whilePointer 111 109 body) st (1+u+1+w) out :=
      MachineEval.pointerNext hh (by rw [hStop,hIndex]; omega) eb er
    refine ⟨1+u+1+w,out,ex,?_,cIndex,cStop,?_,cCtx,?_,ex.unit_work hForm hUnit hh,cO.trans bO,cH⟩
    · have hProduct : (remaining+1)*(bound+2)=remaining*(bound+2)+(bound+2) := by ring
      rw [hProduct]
      omega
    · change data out=levelPayloadFold update (i+1) remaining (update i (data st))
      rw [cData,hDataUnit b,bData,hDataUnit st]
    · change out.scalar.queries=st.scalar.queries+(remaining+1)*queryCost
      change out.scalar.queries=b.scalar.queries+remaining*queryCost at cQ
      change b.scalar.queries=st.scalar.queries+queryCost at bQ
      rw [cQ,bQ]
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PayloadFoldProperties

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma level_payload_integer_additive {Payload : Type} (update : ℕ → Payload → Payload)
    (increment : ℕ → ℤ) (limit : ℕ) (eval : Payload → ℤ)
    (hStep : ∀ i < limit, ∀ payload, eval (update i payload)=eval payload+increment i) (count : ℕ) :
    ∀ (start : ℕ) (payload : Payload), start+count ≤ limit →
      eval (levelPayloadFold update start count payload)=eval payload+∑ k ∈ Finset.range count, increment (start+k) := by
  induction count with
  | zero => intros; simp [levelPayloadFold]
  | succ count ih =>
    intro start payload hRange
    rw [levelPayloadFold,ih (start+1) (update start payload) (by omega),hStep start (by omega),Finset.sum_range_succ']
    have hSum : (∑ k ∈ Finset.range count, increment (start+1+k))=
        ∑ k ∈ Finset.range count, increment (start+(k+1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      omega
    rw [hSum]
    simp only [Nat.add_zero]
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MachinePendingFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

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


namespace PendingIntegerFrame

lemma payUnit {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (pm : MachinePendingKeys g s α ε ell length logical st) :
    PendingIntegerFrame pm pm.payUnit := ⟨le_rfl,by intros i hi z hz; exact fun _ => hz,by intros; rfl,by intros; rfl⟩

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

namespace PendingVisitedKeys

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

namespace MemoryBufferFrame

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

-- Proof module: Solutions.KeyListPrependMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section

lemma listPrependMemory_outside (I : ℤ → ℤ) (free : ℤ) (key : ℕ) (head z : ℤ)
    (hz : z ∉ nodeCells free) : listPrependMemory I free key head z=I z := by
  have hne : z ≠ free+2 := by intro he; subst z; exact hz (by simp [nodeCells])
  rw [listPrependMemory,Function.update_of_ne hne]
  exact node_alloc_frame _ _ _ _ hz

lemma listPrependMemory_below (I : ℤ → ℤ) (free : ℤ) (key : ℕ) (head z : ℤ)
    (hz : z < free) : listPrependMemory I free key head z=I z := by
  apply listPrependMemory_outside
  intro hm
  have he := (nodeCells_mem_iff free z).mp hm
  omega

lemma key_list_prepend_rep (I : ℤ → ℤ) (free : ℤ) (key : ℕ) (head : ℤ) (keys : List ℕ) (F : Finset ℤ)
    (hp : 2 ≤ free) (h : KeyListRep I head keys F) (hbelow : ∀ z ∈ F, z < free) :
    KeyListRep (listPrependMemory I free key head) free (key::keys) (nodeCells free ∪ F) := by
  have htail : KeyListRep (listPrependMemory I free key head) head keys F := by
    apply h.frame
    intro z hz
    exact listPrependMemory_below I free key head z (hbelow z hz)
  have hsep : Disjoint (nodeCells free) F := by
    apply Finset.disjoint_left.mpr
    intro z hz hf
    have hlo := (nodeCells_mem_iff free z).mp hz
    have hhi := hbelow z hf
    omega
  have hk : listPrependMemory I free key head free=(key : ℤ) := by
    simp [listPrependMemory,nodeAllocMemory,Function.update_of_ne (by omega : free ≠ free+2),
      Function.update_of_ne (by omega : free ≠ free+1)]
  have hc : listPrependMemory I free key head (free+1)=0 := by
    simp [listPrependMemory,nodeAllocMemory,Function.update_of_ne (by omega : free+1 ≠ free+2)]
  have hs : listPrependMemory I free key head (free+2)=head := by simp [listPrependMemory]
  simpa [KeyListRep,keyListForest] using
    ForestRep.node free key 0 head .nil (keyListForest keys) ∅ F hp hk hc hs ForestRep.nil htail (by simp) hsep (by simp)

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SupportListPrepend

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma supportListPrependCode_wellFormed : supportListPrependCode.wellFormed := by
  simp [supportListPrependCode,listLinkPrepRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,heapNodeAllocCode_wellFormed,coreCode,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SupportListPrependRaw

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 1800000 in
lemma support_list_prepend_raw_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (free head : ℤ) (key : ℕ) (keys : List ℕ) (F : Finset ℤ)
    (hp : 2 ≤ free) (hf : st.scalar.core.ptrs 20=free) (hk : st.scalar.core.ptrs 4=(key : ℤ))
    (hhead : st.scalar.core.ptrs 92=head) (h : KeyListRep st.scalar.integerMemory head keys F)
    (hbelow : ∀ z ∈ F, z < free) :
    ∃ out, MachineEval m g ω supportListPrependCode st 13 out ∧
      out.scalar.core.ptrs 92=free ∧ out.scalar.core.ptrs 20=free+3 ∧
      KeyListRep out.scalar.integerMemory (out.scalar.core.ptrs 92) (key::keys) (nodeCells free ∪ F) ∧
      (∀ z ∈ nodeCells free ∪ F, z < free+3) ∧
      (∀ z, z ∉ nodeCells free → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+13 ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      out.scalar.integerMemory=listPrependMemory st.scalar.integerMemory free key head ∧ out.scalar.core.ptrs 0=0 := by
  obtain ⟨alloc,ea,ha0,ha5,ha20,haI,haR,haW,haO⟩ := heap_node_alloc_exec m g ω st hh
  rw [hf] at ha5 ha20 haI
  rw [hk] at haI
  have haH : alloc.scalar.halted=false := (ea.halted heapNodeAllocCode_wellFormed).trans hh
  have ha92 : alloc.scalar.core.ptrs 92=head := (ea.pointer_frame 92 (by decide)).trans hhead
  obtain ⟨pre,eb,hPtr,hI,hR,hW,hO,hH⟩ := listLinkPrepRoutine.execute m g ω alloc haH
  have eb3 : MachineEval m g ω listLinkPrepRoutine.code alloc 3 pre := eb
  have pre7 : pre.scalar.core.ptrs 7=free+2 := by
    rw [hPtr]
    simp [listLinkPrepRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,ha5]
    ring
  have pre92 := (eb.pointer_frame 92 (by decide)).trans ha92
  have pre5 := (eb.pointer_frame 5 (by decide)).trans ha5
  have pre20 := (eb.pointer_frame 20 (by decide)).trans ha20
  let linked := payUnit (integerWrite pre (free+2) head)
  let out := payUnit (pointerWrite linked 92 free)
  have ec : MachineEval m g ω (.atom (.scalar (.integerStore 7 92))) pre 1 linked := by
    simpa only [linked,pre7,pre92] using integerStore_eval m g ω pre 7 92 hH
  have linkedH : linked.scalar.halted=false := hH
  have linked5 : linked.scalar.core.ptrs 5=free := pre5
  have ed : MachineEval m g ω (coreCode (.pcopy 92 5)) linked 1 out := by
    simpa only [out,coreCode,linked5] using pcopy_eval m g ω linked 92 5 linkedH
  have eRun : MachineEval m g ω supportListPrependCode st 13 out := MachineEval.seq ea (MachineEval.seq eb3 (MachineEval.seq ec ed))
  have houtI : out.scalar.integerMemory=listPrependMemory st.scalar.integerMemory free key head := by
    change Function.update pre.scalar.integerMemory (free+2) head= _
    rw [hI,haI]
    rfl
  have hout92 : out.scalar.core.ptrs 92=free := by simp [out,payUnit,pcSet,pointerWrite]
  refine ⟨out,eRun,hout92,pre20,?_,?_,?_,hR.trans haR,?_,?_,hO.trans haO,hH,houtI,
    ((MachineEval.seq eb3 (MachineEval.seq ec ed)).pointer_frame 0 (by decide)).trans ha0⟩
  · rw [houtI,hout92]
    exact key_list_prepend_rep _ _ _ _ _ _ hp h hbelow
  · intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · have hb := (nodeCells_mem_iff free z).mp hz; omega
    · have hb := hbelow z hz; omega
  · intro z hz
    rw [houtI]
    exact listPrependMemory_outside _ _ _ _ _ hz
  · exact eRun.query_frame (by
      simp [supportListPrependCode,heapNodeAllocCode,listLinkPrepRoutine,PointerRoutine.sequence,PointerRoutine.code,
        PointerOp.instruction,sequenceCode,MachineCode.allAtoms,coreCode,queryReadOnly])
  · change pre.work+1+1=st.work+13
    rw [hW,haW]
    change st.work+8+(3 : ℕ)+1+1=st.work+13
    ring
end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameListPrepend

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma frameListPrependCode_wellFormed (headSlot : ℕ) : (frameListPrependCode headSlot).wellFormed := by
  refine ⟨levelHeaderIntegerToCode_wellFormed headSlot 92,?_,supportListPrependCode_wellFormed,
    levelHeaderIntegerFromCode_wellFormed headSlot 92⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 3500000 in
lemma frame_list_prepend_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level headSlot : ℕ) (free : ℤ)
    (v : Fin n) (vertices : List (Fin n)) (F : Finset ℤ)
    (hfree : 2 ≤ free) (hf : st.scalar.core.ptrs 20=free) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hl : st.scalar.core.ptrs 100=(level : ℤ))
    (hRep : VertexListRep st.scalar.integerMemory (st.scalar.integerMemory (levelHeaderAddress level headSlot)) vertices F)
    (hBelow : ∀ z ∈ F, z < free) (hHeader : levelHeaderAddress level headSlot < free)
    (hSep : levelHeaderAddress level headSlot ∉ F) :
    ∃ out, MachineEval m g ω (frameListPrependCode headSlot) st 34 out ∧
      out.scalar.core.ptrs 20=free+3 ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.integerMemory=frameListPrependMemory st.scalar.integerMemory free v.val level headSlot ∧
      VertexListRep out.scalar.integerMemory (out.scalar.integerMemory (levelHeaderAddress level headSlot))
        (v::vertices) (nodeCells free ∪ F) ∧
      (∀ z ∈ nodeCells free ∪ F, z < free+3) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.regs=st.scalar.core.regs ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+34 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a92,aI,aR,aW,aO,aH⟩ := level_header_integer_to_exec m g ω st hh level headSlot 92 hl
  let b := payUnit (pointerWrite a 4 (v.val : ℤ))
  have eb : MachineEval m g ω (coreCode (.pcopy 4 40)) a 1 b := by
    have a40 := (ea.pointer_frame 40 (by
      simp [levelHeaderIntegerToCode,levelHeaderIntegerLoadCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
        linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets])).trans hv
    simpa only [b,coreCode,a40] using pcopy_eval m g ω a 4 40 aH
  have ePrefix := MachineEval.seq ea eb
  have b4 : b.scalar.core.ptrs 4=(v.val : ℤ) := by simp [b,payUnit,pcSet,pointerWrite]
  have bI : b.scalar.integerMemory=st.scalar.integerMemory := aI
  obtain ⟨c,ec,c92,c20,cRep,cBelow,cFrame,cR,cQ,cW,cO,cH,cI,c0⟩ := support_list_prepend_raw_exec m g ω b aH
    free (st.scalar.integerMemory (levelHeaderAddress level headSlot)) v.val (vertices.map Fin.val) F hfree
    ((ePrefix.pointer_frame 20 (by
      simp [levelHeaderIntegerToCode,levelHeaderIntegerLoadCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
        linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets])).trans hf) b4
    ((eb.pointer_frame 92 (by decide)).trans a92) (by rw [bI]; exact hRep) hBelow
  have eBefore := MachineEval.seq ea (MachineEval.seq eb ec)
  have c100 := (eBefore.pointer_frame 100 (by
    simp [frameListPrependCode,levelHeaderIntegerToCode,levelHeaderIntegerLoadCode,levelHeaderAddressCode,
      levelHeaderAddressInstructions,supportListPrependCode,heapNodeAllocCode,listLinkPrepRoutine,
      PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,linearCode,sequenceCode,coreCode,
      MachineCode.pointerTargets,pointerTargets])).trans hl
  obtain ⟨out,ed,dI,dR,dQ,dW,dO,dH⟩ := level_header_integer_from_exec m g ω c cH level headSlot 92 c100
  have ex : MachineEval m g ω (frameListPrependCode headSlot) st 34 out := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  have dHead : out.scalar.integerMemory (levelHeaderAddress level headSlot)=free := by rw [dI,c92]; simp
  have dRaw : out.scalar.integerMemory=frameListPrependMemory st.scalar.integerMemory free v.val level headSlot := by
    rw [dI,c92,cI,bI]
    rfl
  refine ⟨out,ex,(ed.pointer_frame 20 (by
    simp [levelHeaderIntegerFromCode,levelHeaderIntegerStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
      linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets])).trans c20,
    (ed.pointer_frame 0 (by
      simp [levelHeaderIntegerFromCode,levelHeaderIntegerStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
        linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets])).trans c0,dRaw,?_,cBelow,
    dR.trans (cR.trans aR),ex.register_frame (by
      simp [frameListPrependCode,levelHeaderIntegerToCode,levelHeaderIntegerFromCode,levelHeaderIntegerLoadCode,
        levelHeaderIntegerStoreCode,levelHeaderAddressCode_registerReadOnly,supportListPrependCode,heapNodeAllocCode,
        listLinkPrepRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,sequenceCode,
        coreCode,MachineCode.allAtoms,registerReadOnly]),ex.query_frame (by
      simp [frameListPrependCode,levelHeaderIntegerToCode,levelHeaderIntegerFromCode,levelHeaderIntegerLoadCode,
        levelHeaderIntegerStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,
        supportListPrependCode,heapNodeAllocCode,listLinkPrepRoutine,PointerRoutine.sequence,PointerRoutine.code,
        PointerOp.instruction,sequenceCode,coreCode,MachineCode.allAtoms,queryReadOnly]),
    ex.unit_work (frameListPrependCode_wellFormed headSlot) (by
      simp [frameListPrependCode,levelHeaderIntegerToCode,levelHeaderIntegerFromCode,levelHeaderIntegerLoadCode,
        levelHeaderIntegerStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,
        supportListPrependCode,heapNodeAllocCode,listLinkPrepRoutine,PointerRoutine.sequence,PointerRoutine.code,
        PointerOp.instruction,sequenceCode,coreCode,MachineCode.allAtoms,unitInstruction,straightInstruction]) hh,
    dO.trans (cO.trans aO),dH⟩
  rw [dHead]
  have cRep' : VertexListRep c.scalar.integerMemory free (v::vertices) (nodeCells free ∪ F) := by
    simpa only [VertexListRep,List.map_cons,c92] using cRep
  apply cRep'.frame
  intro z hz
  rw [dI]
  apply Function.update_of_ne
  intro he
  subst z
  rcases Finset.mem_union.mp hz with hz|hz
  · have := (nodeCells_mem_iff free (levelHeaderAddress level headSlot)).mp hz
    omega
  · exact hSep hz

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderIntegerAddFrom

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderIntegerAddFromCode_wellFormed (slot source : ℕ) :
    (levelHeaderIntegerAddFromCode slot source).wellFormed := by
  refine ⟨levelHeaderIntegerLoadCode_wellFormed slot,?_,levelHeaderIntegerStoreCode_wellFormed slot⟩
  simp [MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 1800000 in
lemma level_header_integer_add_from_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level slot source : ℕ) (hSource : 110 ≤ source)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω (levelHeaderIntegerAddFromCode slot source) st 19 out ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (levelHeaderAddress level slot)
        (st.scalar.integerMemory (levelHeaderAddress level slot)+st.scalar.core.ptrs source) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.regs=st.scalar.core.regs ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+19 ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a105,a40,a41,aI,aR,aW,aO,aH⟩ := level_header_integer_load_exec m g ω st hh level slot hl
  have aSource : a.scalar.core.ptrs source=st.scalar.core.ptrs source := ea.pointer_frame source (by
    simp [levelHeaderIntegerLoadCode,levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,
      MachineCode.pointerTargets,pointerTargets]
    omega)
  let b := payUnit (pointerWrite a 105 (a.scalar.core.ptrs 105+a.scalar.core.ptrs source))
  have eb : MachineEval m g ω (.atom (.scalar (.pointerAdd 105 105 source))) a 1 b := pointerAdd_eval m g ω a 105 105 source aH
  have b100 := ((MachineEval.seq ea eb).pointer_frame 100 (by
    simp [levelHeaderIntegerLoadCode,levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,
      MachineCode.pointerTargets,pointerTargets])).trans hl
  obtain ⟨out,ec,cI,c40,c41,cR,cW,cO,cH⟩ := level_header_integer_store_exec m g ω b aH level slot b100
  have ex : MachineEval m g ω (levelHeaderIntegerAddFromCode slot source) st 19 out := MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨out,ex,?_,cR.trans aR,ex.register_frame (by
    simp [levelHeaderIntegerAddFromCode,levelHeaderIntegerLoadCode,levelHeaderIntegerStoreCode,
      levelHeaderAddressCode_registerReadOnly,MachineCode.allAtoms,registerReadOnly]),
    ex.query_frame (by
      simp [levelHeaderIntegerAddFromCode,levelHeaderIntegerLoadCode,levelHeaderIntegerStoreCode,
        levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,MachineCode.allAtoms,queryReadOnly]),
    ?_,cO.trans aO,cH⟩
  · rw [cI]
    change Function.update a.scalar.integerMemory _ (a.scalar.core.ptrs 105+a.scalar.core.ptrs source)=_
    rw [aI,a105,aSource]
  · rw [cW]
    change a.work+1+9=_
    rw [aW]
    norm_num
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderArithmetic

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderIncrementCode_wellFormed (slot : ℕ) : (levelHeaderIncrementCode slot).wellFormed := by
  refine ⟨levelHeaderIntegerLoadCode_wellFormed slot,?_,levelHeaderIntegerStoreCode_wellFormed slot⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameListMetadata

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameListMetadataCode_wellFormed (cardSlot volumeSlot field : ℕ) :
    (frameListMetadataCode cardSlot volumeSlot field).wellFormed := by
  refine ⟨levelHeaderIncrementCode_wellFormed cardSlot,levelHeaderIntegerAddFromCode_wellFormed volumeSlot 120,
    ?_,vertexFlagSetCode_wellFormed⟩
  simp [frameFlagOffsetCode,frameFlagOffsetInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 4500000 in
lemma frame_list_metadata_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level cardSlot volumeSlot field width : ℕ)
    (hCard : cardSlot < 32) (hVol : volumeSlot < 32) (hDistinct : volumeSlot ≠ cardSlot)
    (v : Fin n) (hl : st.scalar.core.ptrs 100=(level : ℤ))
    (hBase : st.scalar.core.ptrs 87=((16*(level+1) : ℕ) : ℤ))
    (h0 : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) :
    ∃ out, MachineEval m g ω (frameListMetadataCode cardSlot volumeSlot field) st (4*width+49) out ∧
      out.scalar.integerMemory=frameListMetadataMemory st.scalar.integerMemory level cardSlot volumeSlot width v.val field
        (st.scalar.core.ptrs 120) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.regs=st.scalar.core.regs ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*width+49 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,aI,aR,aW,aO,aH⟩ := level_header_increment_exec m g ω st hh level cardSlot hl
  have a100 := (ea.pointer_frame 100 (by
    simp [levelHeaderIncrementCode,levelHeaderIntegerLoadCode,levelHeaderIntegerStoreCode,levelHeaderAddressCode,
      levelHeaderAddressInstructions,linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets])).trans hl
  obtain ⟨b,eb,bI,bR,bRegs,bQ,bW,bO,bH⟩ := level_header_integer_add_from_exec m g ω a aH level volumeSlot 120 (by omega) a100
  have a120 := ea.pointer_frame 120 (by
    simp [levelHeaderIncrementCode,levelHeaderIntegerLoadCode,levelHeaderIntegerStoreCode,levelHeaderAddressCode,
      levelHeaderAddressInstructions,linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets])
  have hAddr : levelHeaderAddress level volumeSlot ≠ levelHeaderAddress level cardSlot := by
    intro he
    exact hDistinct (levelHeaderAddress_injective level level volumeSlot cardSlot hVol hCard he).2
  have bRaw : b.scalar.integerMemory=Function.update (Function.update st.scalar.integerMemory
      (levelHeaderAddress level cardSlot) (st.scalar.integerMemory (levelHeaderAddress level cardSlot)+1))
      (levelHeaderAddress level volumeSlot) (st.scalar.integerMemory (levelHeaderAddress level volumeSlot)+st.scalar.core.ptrs 120) := by
    rw [bI,aI,a120,Function.update_of_ne hAddr]
  let c := linearRun m g ω (frameFlagOffsetInstructions field) b
  obtain ⟨ec,cW,cH⟩ := linear_execute m g ω (frameFlagOffsetInstructions field)
    (by simp [frameFlagOffsetInstructions,unitInstruction,straightInstruction]) b bH
  have ePrefix := MachineEval.seq ea (MachineEval.seq eb ec)
  have b87 := ((MachineEval.seq ea eb).pointer_frame 87 (by
    simp [levelHeaderIncrementCode,levelHeaderIntegerAddFromCode,levelHeaderIntegerLoadCode,levelHeaderIntegerStoreCode,
      levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,coreCode,
      MachineCode.pointerTargets,pointerTargets])).trans hBase
  have c88 : c.scalar.core.ptrs 88=((16*(level+1)+field : ℕ) : ℤ) := by
    simp [c,linearRun,frameFlagOffsetInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH,b87]
  have cI : c.scalar.integerMemory=b.scalar.integerMemory := by
    simp [c,linearRun,frameFlagOffsetInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH]
  have cR : c.scalar.core.mem=b.scalar.core.mem := by
    simp [c,linearRun,frameFlagOffsetInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH]
  obtain ⟨out,ed,dI,dR,dRegs,dQ,dW,dO,dH⟩ := vertex_flag_set_exec m g ω c cH width v.val (16*(level+1)+field)
    ((ePrefix.pointer_frame 0 (by
      simp [levelHeaderIncrementCode,levelHeaderIntegerAddFromCode,levelHeaderIntegerLoadCode,levelHeaderIntegerStoreCode,
        levelHeaderAddressCode,levelHeaderAddressInstructions,frameFlagOffsetCode,frameFlagOffsetInstructions,
        linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets])).trans h0)
    ((ePrefix.pointer_frame 40 (by
      simp [levelHeaderIncrementCode,levelHeaderIntegerAddFromCode,levelHeaderIntegerLoadCode,levelHeaderIntegerStoreCode,
        levelHeaderAddressCode,levelHeaderAddressInstructions,frameFlagOffsetCode,frameFlagOffsetInstructions,
        linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets])).trans hv)
    ((ePrefix.pointer_frame 41 (by
      simp [levelHeaderIncrementCode,levelHeaderIntegerAddFromCode,levelHeaderIntegerLoadCode,levelHeaderIntegerStoreCode,
        levelHeaderAddressCode,levelHeaderAddressInstructions,frameFlagOffsetCode,frameFlagOffsetInstructions,
        linearCode,sequenceCode,coreCode,MachineCode.pointerTargets,pointerTargets])).trans hw) c88
  have ex : MachineEval m g ω (frameListMetadataCode cardSlot volumeSlot field) st (4*width+49) out := by
    have er := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
    convert er using 1 <;> (first | rfl | change 4*width+49=19+(19+(2+(4*width+9))); omega)
  refine ⟨out,ex,?_,dR.trans (cR.trans (bR.trans aR)),ex.register_frame (by
    simp [frameListMetadataCode,levelHeaderIncrementCode,levelHeaderIntegerAddFromCode,levelHeaderIntegerLoadCode,
      levelHeaderIntegerStoreCode,levelHeaderAddressCode_registerReadOnly,frameFlagOffsetCode,frameFlagOffsetInstructions,
      linearCode,sequenceCode,coreCode,MachineCode.allAtoms,registerReadOnly,vertexFlagSetCode_registerReadOnly]),
    ex.query_frame (by
      simp [frameListMetadataCode,levelHeaderIncrementCode,levelHeaderIntegerAddFromCode,levelHeaderIntegerLoadCode,
        levelHeaderIntegerStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,frameFlagOffsetCode,
        frameFlagOffsetInstructions,linearCode,sequenceCode,coreCode,MachineCode.allAtoms,queryReadOnly,vertexFlagSetCode_queryReadOnly]),
    ?_,?_,dH⟩
  · rw [dI,cI,bRaw]
    rfl
  · rw [dW,cW,bW,aW]
    change st.work+19+19+(2 : ℕ)+(4*width+9 : ℕ)=_
    push_cast
    ring
  · have cO : c.output=b.output := by
      simp [c,linearRun,frameFlagOffsetInstructions,atomState,machineStep,pcSet,LocalPush.step,
        scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH]
    exact dO.trans (cO.trans (bO.trans aO))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameListMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma frame_list_prepend_below (I : ℤ → ℤ) (free : ℤ) (vertex level headSlot : ℕ) (z : ℤ)
    (hz : z < free) (hHead : z ≠ levelHeaderAddress level headSlot) :
    frameListPrependMemory I free vertex level headSlot z=I z := by
  rw [frameListPrependMemory,Function.update_of_ne hHead,listPrependMemory_below _ _ _ _ _ hz]

lemma frame_list_metadata_other (I : ℤ → ℤ) (level cardSlot volumeSlot width vertex field : ℕ) (degree z : ℤ)
    (hCard : z ≠ levelHeaderAddress level cardSlot) (hVol : z ≠ levelHeaderAddress level volumeSlot)
    (hFlag : z ≠ vertexRecordAddress width vertex (16*(level+1)+field)) :
    frameListMetadataMemory I level cardSlot volumeSlot width vertex field degree z=I z := by
  simp only [frameListMetadataMemory,Function.update_of_ne hFlag,Function.update_of_ne hVol,Function.update_of_ne hCard]

lemma level_header_below_end (level slot : ℕ) (hs : slot < 32) :
    levelHeaderAddress level slot < 128+32*((level+1 : ℕ) : ℤ) := by
  unfold levelHeaderAddress
  push_cast
  omega

lemma frame_list_metadata_on_positive (I : ℤ → ℤ) (level cardSlot volumeSlot width vertex field : ℕ)
    (degree z : ℤ) (hz : 0 ≤ z) (hCard : z ≠ levelHeaderAddress level cardSlot)
    (hVol : z ≠ levelHeaderAddress level volumeSlot) :
    frameListMetadataMemory I level cardSlot volumeSlot width vertex field degree z=I z := by
  apply frame_list_metadata_other I level cardSlot volumeSlot width vertex field degree z hCard hVol
  have := vertexRecordAddress_negative width vertex (16*(level+1)+field)
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameListInsert

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma frameListInsertCode_wellFormed (headSlot cardSlot volumeSlot field : ℕ) :
    (frameListInsertCode headSlot cardSlot volumeSlot field).wellFormed :=
  ⟨frameListPrependCode_wellFormed headSlot,frameListMetadataCode_wellFormed cardSlot volumeSlot field⟩

set_option maxHeartbeats 6000000 in
lemma frame_list_insert_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level headSlot cardSlot volumeSlot field width : ℕ)
    (hHead : headSlot < 32) (hCard : cardSlot < 32) (hVol : volumeSlot < 32)
    (hCardHead : cardSlot ≠ headSlot) (hVolHead : volumeSlot ≠ headSlot) (hVolCard : volumeSlot ≠ cardSlot)
    (free : ℤ) (v : Fin n) (vertices : List (Fin n)) (F : Finset ℤ)
    (hfree : 128+32*((level+1 : ℕ) : ℤ) ≤ free) (hf : st.scalar.core.ptrs 20=free)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) (hBase : st.scalar.core.ptrs 87=((16*(level+1) : ℕ) : ℤ))
    (hRep : VertexListRep st.scalar.integerMemory (st.scalar.integerMemory (levelHeaderAddress level headSlot)) vertices F)
    (hBelow : ∀ z ∈ F, z < free) (hAbove : ∀ z ∈ F, 128+32*((level+1 : ℕ) : ℤ) ≤ z) :
    ∃ out, MachineEval m g ω (frameListInsertCode headSlot cardSlot volumeSlot field) st (4*width+83) out ∧
      out.scalar.core.ptrs 20=free+3 ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.integerMemory=frameListInsertMemory st.scalar.integerMemory free v.val level headSlot cardSlot volumeSlot width field
        (st.scalar.core.ptrs 120) ∧
      VertexListRep out.scalar.integerMemory (out.scalar.integerMemory (levelHeaderAddress level headSlot))
        (v::vertices) (nodeCells free ∪ F) ∧
      (∀ z ∈ nodeCells free ∪ F, z < free+3) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.regs=st.scalar.core.regs ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*width+83 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  have hHeadBelow := level_header_below_end level headSlot hHead
  have hHeadSep : levelHeaderAddress level headSlot ∉ F := by
    intro hm
    have := hAbove _ hm
    omega
  obtain ⟨a,ea,a20,a0,aI,aRep,aBelow,aR,aRegs,aQ,aW,aO,aH⟩ := frame_list_prepend_exec m g ω st hh level headSlot free
    v vertices F (by have := Int.natCast_nonneg (level+1); omega) hf hv hl hRep hBelow (by omega) hHeadSep
  have a100 := (ea.pointer_frame 100 (by
    simp [frameListPrependCode,levelHeaderIntegerToCode,levelHeaderIntegerFromCode,levelHeaderIntegerLoadCode,
      levelHeaderIntegerStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,
      supportListPrependCode,heapNodeAllocCode,listLinkPrepRoutine,PointerRoutine.sequence,PointerRoutine.code,
      PointerOp.instruction,coreCode,MachineCode.pointerTargets,pointerTargets])).trans hl
  have a87 := (ea.pointer_frame 87 (by
    simp [frameListPrependCode,levelHeaderIntegerToCode,levelHeaderIntegerFromCode,levelHeaderIntegerLoadCode,
      levelHeaderIntegerStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,
      supportListPrependCode,heapNodeAllocCode,listLinkPrepRoutine,PointerRoutine.sequence,PointerRoutine.code,
      PointerOp.instruction,coreCode,MachineCode.pointerTargets,pointerTargets])).trans hBase
  have a40 := (ea.pointer_frame 40 (by
    simp [frameListPrependCode,levelHeaderIntegerToCode,levelHeaderIntegerFromCode,levelHeaderIntegerLoadCode,
      levelHeaderIntegerStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,
      supportListPrependCode,heapNodeAllocCode,listLinkPrepRoutine,PointerRoutine.sequence,PointerRoutine.code,
      PointerOp.instruction,coreCode,MachineCode.pointerTargets,pointerTargets])).trans hv
  have a41 := (ea.pointer_frame 41 (by
    simp [frameListPrependCode,levelHeaderIntegerToCode,levelHeaderIntegerFromCode,levelHeaderIntegerLoadCode,
      levelHeaderIntegerStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,
      supportListPrependCode,heapNodeAllocCode,listLinkPrepRoutine,PointerRoutine.sequence,PointerRoutine.code,
      PointerOp.instruction,coreCode,MachineCode.pointerTargets,pointerTargets])).trans hw
  have a120 := ea.pointer_frame 120 (by
    simp [frameListPrependCode,levelHeaderIntegerToCode,levelHeaderIntegerFromCode,levelHeaderIntegerLoadCode,
      levelHeaderIntegerStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,
      supportListPrependCode,heapNodeAllocCode,listLinkPrepRoutine,PointerRoutine.sequence,PointerRoutine.code,
      PointerOp.instruction,coreCode,MachineCode.pointerTargets,pointerTargets])
  obtain ⟨out,eb,bI,bR,bRegs,bQ,bW,bO,bH⟩ := frame_list_metadata_exec m g ω a aH level cardSlot volumeSlot field width
    hCard hVol hVolCard v a100 a87 a0 a40 a41
  have ex : MachineEval m g ω (frameListInsertCode headSlot cardSlot volumeSlot field) st (4*width+83) out := by
    have ee := MachineEval.seq ea eb
    convert ee using 1 <;> (first | rfl | omega)
  have hAddrCard : levelHeaderAddress level headSlot ≠ levelHeaderAddress level cardSlot := by
    intro he
    exact hCardHead (levelHeaderAddress_injective level level headSlot cardSlot hHead hCard he).2.symm
  have hAddrVol : levelHeaderAddress level headSlot ≠ levelHeaderAddress level volumeSlot := by
    intro he
    exact hVolHead (levelHeaderAddress_injective level level headSlot volumeSlot hHead hVol he).2.symm
  have bHead : out.scalar.integerMemory (levelHeaderAddress level headSlot)=a.scalar.integerMemory (levelHeaderAddress level headSlot) := by
    rw [bI]
    exact frame_list_metadata_on_positive _ level cardSlot volumeSlot width v.val field _ _
      (by have := levelHeaderAddress_positive level headSlot; omega) hAddrCard hAddrVol
  refine ⟨out,ex,(eb.pointer_frame 20 (by simp [frameListMetadataCode,levelHeaderIncrementCode,levelHeaderIntegerAddFromCode,
      levelHeaderIntegerLoadCode,levelHeaderIntegerStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
      frameFlagOffsetCode,frameFlagOffsetInstructions,linearCode,sequenceCode,coreCode,vertexFlagSetCode,
      vertexIntegerStoreCode,vertexAddressCode,vertexAddressTailCode,integerScaleCode,integerScaleLoopCode,
      integerScaleBodyCode,integerScaleBodyRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
      MachineCode.pointerTargets,pointerTargets])).trans a20,
    (eb.pointer_frame 0 (by simp [frameListMetadataCode,levelHeaderIncrementCode,levelHeaderIntegerAddFromCode,
      levelHeaderIntegerLoadCode,levelHeaderIntegerStoreCode,levelHeaderAddressCode,levelHeaderAddressInstructions,
      frameFlagOffsetCode,frameFlagOffsetInstructions,linearCode,sequenceCode,coreCode,vertexFlagSetCode,
      vertexIntegerStoreCode,vertexAddressCode,vertexAddressTailCode,integerScaleCode,integerScaleLoopCode,
      integerScaleBodyCode,integerScaleBodyRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
      MachineCode.pointerTargets,pointerTargets])).trans a0,?_,?_,aBelow,bR.trans aR,bRegs.trans aRegs,bQ.trans aQ,?_,bO.trans aO,bH⟩
  · rw [bI,aI,a120]
    rfl
  · rw [bHead]
    apply aRep.frame
    intro z hz
    rw [bI]
    have hLo : 128+32*((level+1 : ℕ) : ℤ) ≤ z := by
      rcases Finset.mem_union.mp hz with hz|hz
      · have := (nodeCells_mem_iff free z).mp hz
        omega
      · exact hAbove z hz
    apply frame_list_metadata_on_positive _ level cardSlot volumeSlot width v.val field _ z (by omega)
    · have := level_header_below_end level cardSlot hCard
      omega
    · have := level_header_below_end level volumeSlot hVol
      omega
  · rw [bW,aW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameListInsertHeaderFrame
set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
lemma frame_list_insert_header_other (I : ℤ → ℤ) (free : ℤ)
    (vertex level headSlot cardSlot volumeSlot width field slot : ℕ) (degree : ℤ)
    (hfree : 128+32*((level+1 : ℕ) : ℤ) ≤ free)
    (hh : headSlot < 32) (hc : cardSlot < 32) (hv : volumeSlot < 32) (hs : slot < 32)
    (hsh : slot ≠ headSlot) (hsc : slot ≠ cardSlot) (hsv : slot ≠ volumeSlot) :
    frameListInsertMemory I free vertex level headSlot cardSlot volumeSlot width field degree
      (levelHeaderAddress level slot)=I (levelHeaderAddress level slot) := by
  have hNe (k : ℕ) (hk : k < 32) (hne : slot ≠ k) : levelHeaderAddress level slot ≠ levelHeaderAddress level k := by
    intro he
    exact hne (levelHeaderAddress_injective level level slot k hs hk he).2
  rw [frameListInsertMemory,frame_list_metadata_on_positive _ level cardSlot volumeSlot width vertex field degree _
    (by have := levelHeaderAddress_positive level slot; omega) (hNe cardSlot hc hsc) (hNe volumeSlot hv hsv)]
  exact frame_list_prepend_below I free vertex level headSlot _
    (lt_of_lt_of_le (level_header_below_end level slot hs) hfree) (hNe headSlot hh hsh)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexRealAdd

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexRealAddCode_wellFormed : vertexRealAddCode.wellFormed := by
  refine ⟨vertexAddressCode_wellFormed,?_⟩
  simp [realAddAtPointerCode,linearCode,realAddAtPointerInstructions,RealOperation.instruction,
    sequenceCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma vertexRealAddCode_queryReadOnly : vertexRealAddCode.allAtoms queryReadOnly := by
  simp [vertexRealAddCode,vertexAddressCode_queryReadOnly,realAddAtPointerCode,linearCode,
    realAddAtPointerInstructions,RealOperation.instruction,sequenceCode,MachineCode.allAtoms,queryReadOnly]

set_option maxHeartbeats 1400000 in
lemma real_add_at_pointer_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω realAddAtPointerCode st 3 out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (st.scalar.core.ptrs 45)
        (st.scalar.core.mem (st.scalar.core.ptrs 45)+st.scalar.core.regs 10) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.work=st.work+3 ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω realAddAtPointerInstructions
    (by simp [realAddAtPointerInstructions,RealOperation.instruction,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,realAddAtPointerInstructions,RealOperation.instruction,atomState,machineStep,pcSet,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]

set_option maxHeartbeats 1000000 in
lemma vertex_real_add_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex offset : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hi : st.scalar.core.ptrs 44=(offset : ℤ)) :
    ∃ out, MachineEval m g ω vertexRealAddCode st (4*width+9) out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width vertex offset)
        (st.scalar.core.mem (vertexRecordAddress width vertex offset)+st.scalar.core.regs 10) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(4*width+9 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨mid,ea,haddr,hI,hR,hW,hO,hH⟩ := vertex_address_exec m g ω st hh width vertex offset hz hv hw hi
  have hRegs := ea.register_frame vertexAddressCode_registerReadOnly
  obtain ⟨out,eb,hoR,hoI,hoW,hoO,hoH⟩ := real_add_at_pointer_exec m g ω mid hH
  have eRun : MachineEval m g ω vertexRealAddCode st (4*width+9) out := by
    have ee := MachineEval.seq ea eb
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,?_,hoI.trans hI,eRun.query_frame vertexRealAddCode_queryReadOnly,?_,hoO.trans hO,hoH⟩
  · rw [hoR,haddr,hR,hRegs]
  · rw [hoW,hW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexRealAddFrom

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexRealAddFromCode_wellFormed (source : ℕ) : (vertexRealAddFromCode source).wellFormed := by
  refine ⟨?_,vertexRealAddCode_wellFormed⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 1600000 in
lemma vertex_real_add_from_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex offset source : ℕ)
    (h0 : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (ho : st.scalar.core.ptrs 44=(offset : ℤ))
    (hOne : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω (vertexRealAddFromCode source) st (4*width+10) out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width vertex offset)
        (st.scalar.core.mem (vertexRecordAddress width vertex offset)+st.scalar.core.regs source) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(4*width+10 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := payUnit (realWrite st 10 (st.scalar.core.regs source))
  have ea : MachineEval m g ω (coreCode (.mul 10 source 31)) st 1 a := by
    simpa only [a,coreCode,RealOperation.instruction,RealOperation.value,hOne,mul_one] using
      binary_eval m g ω st .mul 10 source 31 hh
  obtain ⟨out,eb,bR,bI,bQ,bW,bO,bH⟩ := vertex_real_add_exec m g ω a hh width vertex offset h0 hv hw ho
  have ex : MachineEval m g ω (vertexRealAddFromCode source) st (4*width+10) out := by
    convert MachineEval.seq ea eb using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,?_,bI,bQ,?_,bO,bH⟩
  · rw [bR]
    simp only [a,payUnit,pcSet,realWrite,Function.update_self]
  · rw [bW]
    change st.work+1+(4*width+9 : ℕ)= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderAddFrom

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderAddFromCode_wellFormed (slot source : ℕ) : (levelHeaderAddFromCode slot source).wellFormed := by
  refine ⟨levelHeaderRealLoadCode_wellFormed slot,?_,levelHeaderRealStoreCode_wellFormed slot⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 2000000 in
lemma level_header_add_from_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level slot source : ℕ) (hSource : source ≠ 10)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω (levelHeaderAddFromCode slot source) st 19 out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (levelHeaderAddress level slot)
        (st.scalar.core.mem (levelHeaderAddress level slot)+st.scalar.core.regs source) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+19 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a10,a40,a41,aI,aR,aW,aO,aH⟩ := level_header_real_load_exec m g ω st hh level slot hl
  have aSource : a.scalar.core.regs source=st.scalar.core.regs source := ea.real_register_frame source (by
    simp [levelHeaderRealLoadCode,levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,
      coreCode,MachineCode.registerTargets,registerTargets,hSource])
  let b := payUnit (realWrite a 10 (st.scalar.core.mem (levelHeaderAddress level slot)+st.scalar.core.regs source))
  have eb : MachineEval m g ω (coreCode (.add 10 10 source)) a 1 b := by
    simpa only [b,coreCode,RealOperation.instruction,RealOperation.value,a10,aSource] using binary_eval m g ω a .add 10 10 source aH
  have b100 := ((MachineEval.seq ea eb).pointer_frame 100 (by
    simp [levelHeaderRealLoadCode,levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,
      coreCode,MachineCode.pointerTargets,pointerTargets])).trans hl
  obtain ⟨out,ec,cR,c40,c41,cI,cW,cO,cH⟩ := level_header_real_store_exec m g ω b aH level slot b100
  have ex : MachineEval m g ω (levelHeaderAddFromCode slot source) st 19 out := MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨out,ex,?_,cI.trans aI,ex.query_frame (by
    simp [levelHeaderAddFromCode,levelHeaderRealLoadCode,levelHeaderRealStoreCode,levelHeaderAddressCode,
      levelHeaderAddressInstructions,linearCode,sequenceCode,coreCode,MachineCode.allAtoms,queryReadOnly]),?_,cO.trans aO,cH⟩
  · rw [cR]
    change Function.update a.scalar.core.mem _ (st.scalar.core.mem _+st.scalar.core.regs source)= _
    rw [aR]
  · rw [cW]
    change a.work+1+9= _
    rw [aW]
    norm_num
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredNeighborRead

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma storedNeighborReadCode_wellFormed : storedNeighborReadCode.wellFormed := by
  simp [storedNeighborReadCode,storedNeighborReadInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 1800000 in
lemma stored_neighbor_read_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (index width : ℕ) (base : ℤ) (v : Fin n)
    (hIndex : st.scalar.core.ptrs 109=(index : ℤ)) (hBase : st.scalar.core.ptrs 121=base)
    (hw : st.scalar.core.ptrs 50=(width : ℤ)) (hRecord : st.scalar.integerMemory (base+(index : ℤ))=(v.val : ℤ)) :
    ∃ out, MachineEval m g ω storedNeighborReadCode st 4 out ∧
      out.scalar.core.ptrs 122=(index : ℤ) ∧ out.scalar.core.ptrs 40=(v.val : ℤ) ∧ out.scalar.core.ptrs 41=(width : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+4 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω storedNeighborReadInstructions
    (by simp [storedNeighborReadInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,?_,ex.query_frame (by decide),hW,?_,hH⟩
  all_goals simp [linearRun,storedNeighborReadInstructions,atomState,machineStep,pcSet,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hIndex,hBase,hw,hRecord]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredActiveCountBody

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma storedActiveCountBodyCode_wellFormed : storedActiveCountBodyCode.wellFormed := by
  refine ⟨storedNeighborReadCode_wellFormed,?_,?_,?_⟩
  all_goals simp [vertexFieldReadCode,vertexIntegerLoadCode,vertexAddressCode_wellFormed,
    storedActiveDecisionRoutine,PointerRoutine.code,PointerOp.instruction,coreCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

def StoredActiveCountContext (I : ℤ → ℤ) (width : ℕ) (base : ℤ) (st : MachineState) : Prop :=
  st.scalar.integerMemory=I ∧ st.scalar.core.ptrs 0=0 ∧
    st.scalar.core.ptrs 50=(width : ℤ) ∧ st.scalar.core.ptrs 121=base

set_option maxHeartbeats 4500000 in
lemma stored_active_count_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (source : Fin n) (active : Finset (Fin n)) (I : ℤ → ℤ) (width : ℕ) (base : ℤ)
    (hRow : ∀ (i : ℕ) (hi : i < (g.neighbors source).length),
      I (base+(i : ℤ))=(((g.neighbors source)[i]'hi).val : ℤ))
    (hActive : ∀ v : Fin n, I (vertexRecordAddress width v.val 18)=(if v ∈ active then 1 else 0))
    (i : ℕ) (hi : i < (g.neighbors source).length) (st : MachineState) (hh : st.scalar.halted=false)
    (hCtx : StoredActiveCountContext I width base st)
    (hIndex : st.scalar.core.ptrs 109=(i : ℤ)) (hStop : st.scalar.core.ptrs 111=((g.neighbors source).length : ℤ)) :
    ∃ steps out, MachineEval m g ω storedActiveCountBodyCode st steps out ∧ steps ≤ 4*width+17 ∧
      out.scalar.core.ptrs 109=((i+1 : ℕ) : ℤ) ∧ out.scalar.core.ptrs 111=((g.neighbors source).length : ℤ) ∧
      out.scalar.core.ptrs 124=st.scalar.core.ptrs 124+(if (g.neighbors source)[i] ∈ active then 1 else 0) ∧
      StoredActiveCountContext I width base out ∧ out.scalar.queries=st.scalar.queries+0 ∧ out.output=st.output := by
  obtain ⟨a,ea,a122,a40,a41,aI,aR,aQ,aW,aO,aH⟩ := stored_neighbor_read_exec m g ω st hh i width base (g.neighbors source)[i]
    hIndex hCtx.2.2.2 hCtx.2.2.1 (by rw [hCtx.1]; exact hRow i hi)
  obtain ⟨b,eb,b60,bI,bR,bQ,bW,bO,bH⟩ := vertex_field_read_exec m g ω a aH width ((g.neighbors source)[i]).val 18 60
    ((ea.pointer_frame 0 (by decide)).trans hCtx.2.1) a40 a41
  have ePrefix := MachineEval.seq ea eb
  have b0 := (ePrefix.pointer_frame 0 (by decide)).trans hCtx.2.1
  have b60' : b.scalar.core.ptrs 60=(if (g.neighbors source)[i] ∈ active then 1 else 0) := by
    rw [b60,aI,hCtx.1]
    exact hActive _
  obtain ⟨c,ec,cPtrs,cI,cR,cW,cO,cH⟩ := storedActiveDecisionRoutine.execute m g ω b bH
  let u := (storedActiveDecisionRoutine.run b.scalar.integerMemory b.scalar.core.ptrs).1
  have hu : u ≤ 3 := by
    dsimp [u,storedActiveDecisionRoutine,PointerRoutine.run]
    by_cases hm : (g.neighbors source)[i] ∈ active <;> simp [b60',b0,hm]
  have c124 : c.scalar.core.ptrs 124=b.scalar.core.ptrs 124+(if (g.neighbors source)[i] ∈ active then 1 else 0) := by
    rw [cPtrs]
    by_cases hm : (g.neighbors source)[i] ∈ active <;>
      simp [storedActiveDecisionRoutine,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,b60',b0,hm]
  have eBefore := MachineEval.seq ea (MachineEval.seq eb ec)
  have cIndex := (eBefore.pointer_frame 109 (by decide)).trans hIndex
  let out := payUnit (pointerWrite c 109 ((i+1 : ℕ) : ℤ))
  have ed : MachineEval m g ω (coreCode (.pinc 109)) c 1 out := by
    simpa only [out,coreCode,cIndex,Nat.cast_add,Nat.cast_one] using pinc_eval m g ω c 109 cH
  have ex : MachineEval m g ω storedActiveCountBodyCode st (4+(4*width+9+(u+1))) out :=
    MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  refine ⟨4+(4*width+9+(u+1)),out,ex,by omega,by simp [out,payUnit,pcSet,pointerWrite],
    (ex.pointer_frame 111 (by decide)).trans hStop,?_,?_,?_,cO.trans (bO.trans aO)⟩
  · change c.scalar.core.ptrs 124=_
    rw [c124,ePrefix.pointer_frame 124 (by decide)]
  · exact ⟨cI.trans (bI.trans (aI.trans hCtx.1)),
      (ex.pointer_frame 0 (by decide)).trans hCtx.2.1,
      (ex.pointer_frame 50 (by decide)).trans hCtx.2.2.1,
      (ex.pointer_frame 121 (by decide)).trans hCtx.2.2.2⟩
  · rw [Nat.add_zero]
    exact ex.query_frame (by decide)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredNeighborMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma storedNeighborVertex_eq {n : ℕ} (g : InputGraph n) (source : Fin n) (i : ℕ)
    (hi : i < (g.neighbors source).length) : storedNeighborVertex g source i=(g.neighbors source)[i] := by
  simp [storedNeighborVertex,List.getElem?_eq_getElem hi]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredActiveCountMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma list_indicator_sum {α : Type} [DecidableEq α] (vertices : List α) (fallback : α) (set : Finset α) :
    (∑ i ∈ Finset.range vertices.length, if (vertices[i]?).getD fallback ∈ set then (1 : ℤ) else 0)=
      ((vertices.filter (fun v => v ∈ set)).length : ℤ) := by
  induction vertices with
  | nil => simp
  | cons v vertices ih =>
    change (∑ i ∈ Finset.range (vertices.length+1), if ((v::vertices)[i]?).getD fallback ∈ set then (1 : ℤ) else 0)=_
    rw [Finset.sum_range_succ']
    by_cases hv : v ∈ set <;> simp [hv,ih,add_comm]

def storedActiveCountUpdate {n : ℕ} (g : InputGraph n) (source : Fin n) (active : Finset (Fin n)) (i : ℕ) (count : ℤ) : ℤ :=
  count+(if storedNeighborVertex g source i ∈ active then 1 else 0)

lemma stored_active_count_fold {n : ℕ} (g : InputGraph n) (source : Fin n) (active : Finset (Fin n)) :
    levelPayloadFold (storedActiveCountUpdate g source active) 0 (g.neighbors source).length 0=
      (((g.neighbors source).filter (fun v => v ∈ active)).length : ℤ) := by
  have h := level_payload_integer_additive (storedActiveCountUpdate g source active)
    (fun i => if storedNeighborVertex g source i ∈ active then 1 else 0) (g.neighbors source).length id
    (by intros; rfl) (g.neighbors source).length 0 0 (by omega)
  simp only [id_eq,Nat.zero_add,zero_add] at h
  rw [h]
  exact list_indicator_sum (g.neighbors source) source active

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredActiveCountLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma storedActiveCountLoopCode_wellFormed : storedActiveCountLoopCode.wellFormed := by
  refine ⟨?_,storedActiveCountBodyCode_wellFormed,?_⟩
  all_goals simp [storedActiveCountInitCode,storedActiveCountInitInstructions,linearCode,sequenceCode,coreCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 6000000 in
lemma stored_active_count_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (source : Fin n) (active : Finset (Fin n)) (width : ℕ) (base : ℤ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (hWidth : st.scalar.core.ptrs 50=(width : ℤ))
    (hBase : st.scalar.core.ptrs 121=base) (hSelected : st.scalar.core.ptrs 116=(source.val : ℤ))
    (hDegree : st.scalar.core.ptrs 120=((g.neighbors source).length : ℤ))
    (hRow : ∀ (i : ℕ) (hi : i < (g.neighbors source).length),
      st.scalar.integerMemory (base+(i : ℤ))=(((g.neighbors source)[i]'hi).val : ℤ))
    (hActive : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress width v.val 18)=(if v ∈ active then 1 else 0)) :
    ∃ steps out, MachineEval m g ω storedActiveCountLoopCode st steps out ∧
      steps ≤ (g.neighbors source).length*(4*width+19)+5 ∧
      out.scalar.core.ptrs 124=(((g.neighbors source).filter (fun v => v ∈ active)).length : ℤ) ∧
      out.scalar.core.ptrs 40=(source.val : ℤ) ∧ out.scalar.integerMemory=st.scalar.integerMemory ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.regs=st.scalar.core.regs ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := linearRun m g ω storedActiveCountInitInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω storedActiveCountInitInstructions
    (by simp [storedActiveCountInitInstructions,unitInstruction,straightInstruction]) st hh
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,storedActiveCountInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,storedActiveCountInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have a124 : a.scalar.core.ptrs 124=0 := by
    simp [a,linearRun,storedActiveCountInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have a109 : a.scalar.core.ptrs 109=0 := by
    simp [a,linearRun,storedActiveCountInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have a111 : a.scalar.core.ptrs 111=((g.neighbors source).length : ℤ) := by
    simp [a,linearRun,storedActiveCountInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hDegree]
  have aCtx : StoredActiveCountContext st.scalar.integerMemory width base a :=
    ⟨aI,(ea.pointer_frame 0 (by decide)).trans h0,(ea.pointer_frame 50 (by decide)).trans hWidth,
      (ea.pointer_frame 121 (by decide)).trans hBase⟩
  obtain ⟨u,b,eb,hu,b109,b111,bCount,bCtx,bQ,bW,bO,bH⟩ := payload_level_loop_exec m g ω storedActiveCountBodyCode
    (4*width+17) (g.neighbors source).length 0 (fun z => z.scalar.core.ptrs 124)
    (storedActiveCountUpdate g source active) (fun _ z => StoredActiveCountContext st.scalar.integerMemory width base z)
    storedActiveCountBodyCode_wellFormed (by decide) (by intro z; rfl) (by intro i z h; exact h)
    (by
      intro i hi z hz hc hIndex hStop
      obtain ⟨k,out,ex,hk,o109,o111,o124,oCtx,oQ,oO⟩ :=
        stored_active_count_body_exec m g ω source active st.scalar.integerMemory width base hRow hActive i hi z hz hc hIndex hStop
      refine ⟨k,out,ex,hk,o109,o111,?_,oCtx,oQ,oO⟩
      simpa only [storedActiveCountUpdate,storedNeighborVertex_eq g source i hi] using o124)
    (g.neighbors source).length 0 a aH aCtx (by omega) a109 a111
  have eBefore := MachineEval.seq ea eb
  have b116 := (eBefore.pointer_frame 116 (by decide)).trans hSelected
  let out := payUnit (pointerWrite b 40 (source.val : ℤ))
  have ec : MachineEval m g ω (coreCode (.pcopy 40 116)) b 1 out := by
    simpa only [out,coreCode,b116] using pcopy_eval m g ω b 40 116 bH
  have ex : MachineEval m g ω storedActiveCountLoopCode st (3+(u+1)) out := MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨3+(u+1),out,ex,?_,?_,by simp [out,payUnit,pcSet,pointerWrite],bCtx.1,?_,?_,
    ex.query_frame (by decide),ex.unit_work storedActiveCountLoopCode_wellFormed (by decide) hh,bO.trans aO,bH⟩
  · have hBound : 4*width+17+2=4*width+19 := by omega
    rw [hBound] at hu
    omega
  · change b.scalar.core.ptrs 124=_
    rw [bCount,a124,stored_active_count_fold]
  · exact ex.real_memory_frame (by decide)
  · exact ex.register_frame (by
      simp [storedActiveCountLoopCode,storedActiveCountInitCode,storedActiveCountInitInstructions,
        storedActiveCountBodyCode,storedNeighborReadCode,storedNeighborReadInstructions,vertexFieldReadCode,
        vertexIntegerLoadCode,vertexAddressCode_registerReadOnly,storedActiveDecisionRoutine,PointerRoutine.code,
        PointerOp.instruction,linearCode,sequenceCode,coreCode,MachineCode.allAtoms,registerReadOnly])

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootBoundaryUpdate

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma rootBoundaryUpdateCode_wellFormed : rootBoundaryUpdateCode.wellFormed := by
  simp [rootBoundaryUpdateCode,rootBoundaryUpdatePrefixCode,rootBoundaryUpdateInstructions,rootBoundaryClipRoutine,
    PointerRoutine.code,PointerOp.instruction,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 2500000 in
lemma root_boundary_update_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (boundary degree count : ℕ)
    (h0 : st.scalar.core.ptrs 0=0) (hBoundary : st.scalar.integerMemory 7=(boundary : ℤ))
    (hDegree : st.scalar.core.ptrs 120=(degree : ℤ)) (hCount : st.scalar.core.ptrs 124=(count : ℤ)) :
    ∃ out, MachineEval m g ω rootBoundaryUpdateCode st 8 out ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory 7 ((boundary+degree-2*count : ℕ) : ℤ) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.regs=st.scalar.core.regs ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+8 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let delta : ℤ := (boundary : ℤ)+(degree : ℤ)-2*(count : ℤ)
  let a := linearRun m g ω rootBoundaryUpdateInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω rootBoundaryUpdateInstructions
    (by simp [rootBoundaryUpdateInstructions,unitInstruction,straightInstruction]) st hh
  have a125 : a.scalar.core.ptrs 125=delta := by
    simp [a,delta,linearRun,rootBoundaryUpdateInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hBoundary,hDegree,hCount]
    ring
  have a127 : a.scalar.core.ptrs 127=7 := by
    simp [a,linearRun,rootBoundaryUpdateInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have a0 : a.scalar.core.ptrs 0=0 := (ea.pointer_frame 0 (by decide)).trans h0
  obtain ⟨b,eb,bPtrs,bI,bR,bW,bO,bH⟩ := rootBoundaryClipRoutine.execute m g ω a aH
  have hSteps : (rootBoundaryClipRoutine.run a.scalar.integerMemory a.scalar.core.ptrs).1=2 := by
    simp [rootBoundaryClipRoutine,PointerRoutine.run]
    split_ifs <;> rfl
  have eb2 : MachineEval m g ω rootBoundaryClipRoutine.code a 2 b := by simpa only [hSteps] using eb
  have b125 : b.scalar.core.ptrs 125=((boundary+degree-2*count : ℕ) : ℤ) := by
    rw [bPtrs]
    by_cases hDelta : delta ≤ 0
    · simp [rootBoundaryClipRoutine,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,a125,a0,hDelta]
      dsimp [delta] at hDelta
      omega
    · simp [rootBoundaryClipRoutine,PointerRoutine.run,a125,a0,hDelta]
      dsimp [delta] at hDelta ⊢
      omega
  have b127 := (eb2.pointer_frame 127 (by decide)).trans a127
  let out := payUnit (integerWrite b 7 ((boundary+degree-2*count : ℕ) : ℤ))
  have ec : MachineEval m g ω (.atom (.scalar (.integerStore 127 125))) b 1 out := by
    simpa only [out,b127,b125] using integerStore_eval m g ω b 127 125 bH
  have ex : MachineEval m g ω rootBoundaryUpdateCode st 8 out := MachineEval.seq ea (MachineEval.seq eb2 ec)
  refine ⟨out,ex,?_,ex.real_memory_frame (by decide),ex.register_frame (by
    simp [rootBoundaryUpdateCode,rootBoundaryUpdatePrefixCode,rootBoundaryUpdateInstructions,rootBoundaryClipRoutine,
      PointerRoutine.code,PointerOp.instruction,linearCode,sequenceCode,MachineCode.allAtoms,registerReadOnly]),
    ex.query_frame (by decide),ex.unit_work rootBoundaryUpdateCode_wellFormed (by decide) hh,?_,bH⟩
  · change Function.update b.scalar.integerMemory 7 _=_
    rw [bI]
    have aI : a.scalar.integerMemory=st.scalar.integerMemory := ea.integer_memory_frame (by simp [linearCode,rootBoundaryUpdateInstructions,sequenceCode,MachineCode.allAtoms,integerReadOnly])
    rw [aI]
  · have aO : a.output=st.output := by
      simp [a,linearRun,rootBoundaryUpdateInstructions,atomState,machineStep,pcSet,LocalPush.step,
        scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
    exact bO.trans aO

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ActivationBoundary

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma activationBoundaryCode_wellFormed : activationBoundaryCode.wellFormed :=
  ⟨⟨storedActiveCountLoopCode_wellFormed,rootBoundaryUpdateCode_wellFormed⟩,trivial⟩

set_option maxHeartbeats 4500000 in
lemma activation_boundary_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (source : Fin n) (active : Finset (Fin n)) (level boundary width : ℕ) (base : ℤ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (hWidth : st.scalar.core.ptrs 50=(width : ℤ))
    (hBase : st.scalar.core.ptrs 121=base) (hSelected : st.scalar.core.ptrs 116=(source.val : ℤ))
    (hVertex : st.scalar.core.ptrs 40=(source.val : ℤ))
    (hDegree : st.scalar.core.ptrs 120=((g.neighbors source).length : ℤ))
    (hLevel : st.scalar.core.ptrs 112=(level : ℤ)) (hBoundary : st.scalar.integerMemory 7=(boundary : ℤ))
    (hRow : ∀ (i : ℕ) (hi : i < (g.neighbors source).length),
      st.scalar.integerMemory (base+(i : ℤ))=(((g.neighbors source)[i]'hi).val : ℤ))
    (hActive : level=0 → ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress width v.val 18)=(if v ∈ active then 1 else 0)) :
    ∃ steps out, MachineEval m g ω activationBoundaryCode st steps out ∧
      steps ≤ (g.neighbors source).length*(4*width+19)+14 ∧
      out.scalar.core.ptrs 40=(source.val : ℤ) ∧
      out.scalar.integerMemory=activationBoundaryMemory g source active boundary level st.scalar.integerMemory ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.regs=st.scalar.core.regs ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  by_cases hRoot : level=0
  · obtain ⟨u,a,ea,hu,a124,a40,aI,aR,aRegs,aQ,aW,aO,aH⟩ := stored_active_count_loop_exec m g ω source active width base
      (payUnit st) hh h0 hWidth hBase hSelected hDegree hRow (hActive hRoot)
    have a0 := (ea.pointer_frame 0 (by decide)).trans h0
    have a120 := (ea.pointer_frame 120 (by decide)).trans hDegree
    have aBoundary : a.scalar.integerMemory 7=(boundary : ℤ) := by rw [aI]; exact hBoundary
    obtain ⟨out,eb,bI,bR,bRegs,bQ,bW,bO,bH⟩ := root_boundary_update_exec m g ω a aH boundary (g.neighbors source).length
      ((g.neighbors source).filter (fun v => v ∈ active)).length a0 aBoundary a120 a124
    have eBody := MachineEval.seq ea eb
    have ex : MachineEval m g ω activationBoundaryCode st (1+(u+8)) out :=
      MachineEval.pointerLe hh (by rw [hLevel,h0,hRoot]; norm_num) eBody
    refine ⟨1+(u+8),out,ex,by omega,(eb.pointer_frame 40 (by decide)).trans a40,?_,bR.trans aR,bRegs.trans aRegs,
      ex.query_frame (by decide),ex.unit_work activationBoundaryCode_wellFormed (by decide) hh,bO.trans aO,bH⟩
    rw [bI,aI]
    simp only [activationBoundaryMemory,if_pos hRoot]
    rfl
  · have eSkip : MachineEval m g ω (.skip : MachineCode) (payUnit st) 0 (payUnit st) := MachineEval.skip _
    have ex : MachineEval m g ω activationBoundaryCode st 2 (payUnit (payUnit st)) :=
      MachineEval.pointerGt hh (by rw [hLevel,h0]; omega) eSkip
    refine ⟨2,payUnit (payUnit st),ex,by omega,hVertex,?_,rfl,rfl,rfl,
      ex.unit_work activationBoundaryCode_wellFormed (by decide) hh,rfl,hh⟩
    simp only [activationBoundaryMemory,if_neg hRoot]
    rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ActivationBudget

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma activationBudgetApplyCode_wellFormed : activationBudgetApplyCode.wellFormed := by
  refine ⟨?_,levelHeaderAddFromCode_wellFormed 4 48⟩
  simp [activationBudgetFactorCode,activationBudgetFactorInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma activationBudgetCode_wellFormed : activationBudgetCode.wellFormed :=
  ⟨levelHeaderIntegerLoadCode_wellFormed 9,trivial,activationBudgetApplyCode_wellFormed⟩

set_option maxHeartbeats 2200000 in
lemma activation_budget_apply_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level : ℕ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) :
    ∃ out, MachineEval m g ω activationBudgetApplyCode st 25 out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (levelHeaderAddress level 4)
        (st.scalar.core.mem (levelHeaderAddress level 4)+((level+3 : ℕ) : ℝ)*st.scalar.core.regs 43) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+25 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := linearRun m g ω activationBudgetFactorInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω activationBudgetFactorInstructions
    (by simp [activationBudgetFactorInstructions,unitInstruction,straightInstruction]) st hh
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,activationBudgetFactorInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aR : a.scalar.core.mem=st.scalar.core.mem := by
    simp [a,linearRun,activationBudgetFactorInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,activationBudgetFactorInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have a48 : a.scalar.core.regs 48=((level+3 : ℕ) : ℝ)*st.scalar.core.regs 43 := by
    simp [a,linearRun,activationBudgetFactorInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hl]
    exact Or.inl (by ring)
  obtain ⟨out,eb,bR,bI,bQ,bW,bO,bH⟩ := level_header_add_from_exec m g ω a aH level 4 48 (by decide)
    ((ea.pointer_frame 100 (by decide)).trans hl)
  have ex : MachineEval m g ω activationBudgetApplyCode st 25 out := MachineEval.seq ea eb
  refine ⟨out,ex,?_,bI.trans aI,ex.query_frame (by decide),
    ex.unit_work activationBudgetApplyCode_wellFormed (by decide) hh,bO.trans aO,bH⟩
  rw [bR,aR,a48]

set_option maxHeartbeats 2200000 in
lemma activation_budget_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level : ℕ) (opened : Bool)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) (h0 : st.scalar.core.ptrs 0=0)
    (hOpen : st.scalar.integerMemory (levelHeaderAddress level 9)=(if opened then 1 else 0)) :
    ∃ steps out, MachineEval m g ω activationBudgetCode st steps out ∧ steps ≤ 36 ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (levelHeaderAddress level 4)
        (st.scalar.core.mem (levelHeaderAddress level 4)+(if opened then ((level+3 : ℕ) : ℝ)*st.scalar.core.regs 43 else 0)) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a105,a40,a41,aI,aR,aW,aO,aH⟩ := level_header_integer_load_exec m g ω st hh level 9 hl
  have a0 := (ea.pointer_frame 0 (by decide)).trans h0
  have a100 := (ea.pointer_frame 100 (by decide)).trans hl
  rw [hOpen] at a105
  cases opened with
  | false =>
    have eSkip : MachineEval m g ω (.skip : MachineCode) (payUnit a) 0 (payUnit a) := MachineEval.skip _
    have eb : MachineEval m g ω (.branchPointer 105 0 .skip activationBudgetApplyCode) a 1 (payUnit a) :=
      MachineEval.pointerLe aH (by rw [a105,a0]; norm_num) eSkip
    have ex : MachineEval m g ω activationBudgetCode st 10 (payUnit a) := MachineEval.seq ea eb
    refine ⟨10,payUnit a,ex,by omega,?_,aI,ex.query_frame (by decide),
      ex.unit_work activationBudgetCode_wellFormed (by decide) hh,aO,aH⟩
    change a.scalar.core.mem=Function.update st.scalar.core.mem _ (_+0)
    rw [aR,add_zero,Function.update_eq_self]
  | true =>
    obtain ⟨b,eb,bR,bI,bQ,bW,bO,bH⟩ := activation_budget_apply_exec m g ω (payUnit a) aH level a100
    have eBranch : MachineEval m g ω (.branchPointer 105 0 .skip activationBudgetApplyCode) a (1+25+1) (payUnit b) :=
      MachineEval.pointerGt aH (by rw [a105,a0]; norm_num) eb
    have ex : MachineEval m g ω activationBudgetCode st 36 (payUnit b) := MachineEval.seq ea eBranch
    refine ⟨36,payUnit b,ex,by omega,?_,bI.trans aI,ex.query_frame (by decide),
      ex.unit_work activationBudgetCode_wellFormed (by decide) hh,bO.trans aO,bH⟩
    change b.scalar.core.mem=_
    rw [bR]
    change Function.update a.scalar.core.mem (levelHeaderAddress level 4) (a.scalar.core.mem (levelHeaderAddress level 4)+((level+3 : ℕ) : ℝ)*a.scalar.core.regs 43)=_
    rw [aR,ea.real_register_frame 43 (by decide)]
    rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ActivationScalars

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma activationScalarsCode_wellFormed : activationScalarsCode.wellFormed := by
  refine ⟨?_,vertexRealAddFromCode_wellFormed 43,activationBudgetCode_wellFormed⟩
  simp [activationResidualOffsetCode,activationResidualOffsetInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 3500000 in
lemma activation_scalars_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level width : ℕ) (v : Fin n) (opened : Bool)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) (hb : st.scalar.core.ptrs 87=((16*(level+1) : ℕ) : ℤ))
    (h0 : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hOne : st.scalar.core.regs 31=1)
    (hOpen : st.scalar.integerMemory (levelHeaderAddress level 9)=(if opened then 1 else 0)) :
    ∃ steps out, MachineEval m g ω activationScalarsCode st steps out ∧ steps ≤ 4*width+48 ∧
      out.scalar.core.mem=activationScalarsMemory st.scalar.core.mem width v.val level (st.scalar.core.regs 43) opened ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := linearRun m g ω activationResidualOffsetInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω activationResidualOffsetInstructions
    (by simp [activationResidualOffsetInstructions,unitInstruction,straightInstruction]) st hh
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,activationResidualOffsetInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aR : a.scalar.core.mem=st.scalar.core.mem := by
    simp [a,linearRun,activationResidualOffsetInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,activationResidualOffsetInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have a44 : a.scalar.core.ptrs 44=((16*(level+1)+1 : ℕ) : ℤ) := by
    simp [a,linearRun,activationResidualOffsetInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hb]
  obtain ⟨b,eb,bR,bI,bQ,bW,bO,bH⟩ := vertex_real_add_from_exec m g ω a aH width v.val (16*(level+1)+1) 43
    ((ea.pointer_frame 0 (by decide)).trans h0) ((ea.pointer_frame 40 (by decide)).trans hv)
    ((ea.pointer_frame 41 (by decide)).trans hw) a44 ((ea.real_register_frame 31 (by decide)).trans hOne)
  have ePrefix := MachineEval.seq ea eb
  have b100 := (ePrefix.pointer_frame 100 (by decide)).trans hl
  have b0 := (ePrefix.pointer_frame 0 (by decide)).trans h0
  have bOpen : b.scalar.integerMemory (levelHeaderAddress level 9)=(if opened then 1 else 0) := by rw [bI,aI]; exact hOpen
  obtain ⟨u,out,ec,hu,cR,cI,cQ,cW,cO,cH⟩ := activation_budget_exec m g ω b bH level opened b100 b0 bOpen
  have ex : MachineEval m g ω activationScalarsCode st (2+((4*width+10)+u)) out := MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨2+((4*width+10)+u),out,ex,by omega,?_,cI.trans (bI.trans aI),ex.query_frame (by decide),
    ex.unit_work activationScalarsCode_wellFormed (by decide) hh,cO.trans (bO.trans aO),cH⟩
  have hAddr : levelHeaderAddress level 4 ≠ vertexRecordAddress width v.val (16*(level+1)+1) := by
    have := levelHeaderAddress_positive level 4
    have := vertexRecordAddress_negative width v.val (16*(level+1)+1)
    omega
  rw [cR,bR,aR,ePrefix.real_register_frame 43 (by decide),ea.real_register_frame 43 (by decide),Function.update_of_ne hAddr]
  rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexRealCopy

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma vertexRealCopyCode_wellFormed : vertexRealCopyCode.wellFormed := by
  simp [vertexRealCopyCode,vertexRealLoadCode,vertexRealStoreCode,vertexAddressCode_wellFormed,
    coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

lemma vertexRealZeroCode_wellFormed : vertexRealZeroCode.wellFormed := by
  simp [vertexRealZeroCode,vertexRealStoreCode,vertexAddressCode_wellFormed,coreCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨0,by norm_num⟩

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

lemma levelVertexFlagsClearCode_wellFormed (offsets : List ℕ) : (levelVertexFlagsClearCode offsets).wellFormed := by
  induction offsets with
  | nil => trivial
  | cons k rest ih => exact ⟨levelVertexFlagClearCode_wellFormed k,ih⟩

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

-- Proof module: Solutions.FreshVertexCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma freshReferencePrepCode_wellFormed : freshReferencePrepCode.wellFormed := by
  simp [freshReferencePrepCode,freshReferencePrepInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma freshResidualPrepCode_wellFormed : freshResidualPrepCode.wellFormed := by
  simp [freshResidualPrepCode,freshResidualPrepInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma freshReferenceCode_wellFormed : freshReferenceCode.wellFormed := ⟨freshReferencePrepCode_wellFormed,vertexRealCopyCode_wellFormed⟩
lemma freshResidualCode_wellFormed : freshResidualCode.wellFormed := ⟨freshResidualPrepCode_wellFormed,vertexRealCopyCode_wellFormed⟩
lemma freshHighZeroCode_wellFormed : freshHighZeroCode.wellFormed := by
  refine ⟨?_,vertexRealZeroCode_wellFormed⟩
  simp [levelVertexOffsetCode,levelVertexOffsetInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma freshVertexCode_wellFormed : freshVertexCode.wellFormed :=
  ⟨freshReferenceCode_wellFormed,freshResidualCode_wellFormed,freshHighZeroCode_wellFormed,
    levelVertexFlagsClearCode_wellFormed _⟩

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


end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshVertexExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

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

-- Proof module: Solutions.ActivationChildAdmit

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma activationChildAdmitApplyCode_wellFormed : activationChildAdmitApplyCode.wellFormed := by
  refine ⟨?_,levelContextCode_wellFormed,freshVertexCode_wellFormed,?_,levelContextCode_wellFormed⟩
  all_goals simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma activationChildAdmitCode_wellFormed : activationChildAdmitCode.wellFormed :=
  ⟨trivial,activationChildAdmitApplyCode_wellFormed⟩

set_option maxHeartbeats 4000000 in
lemma activation_child_admit_apply_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level width : ℕ) (v : Fin n)
    (hWidth : 16*(level+1)+22 < width) (hl : st.scalar.core.ptrs 100=(level : ℤ))
    (hSelected : st.scalar.core.ptrs 112=(level : ℤ)) (h0 : st.scalar.core.ptrs 0=0)
    (hVertex : st.scalar.core.ptrs 40=(v.val : ℤ)) (hw : st.scalar.core.ptrs 50=(width : ℤ)) :
    ∃ out, MachineEval m g ω activationChildAdmitApplyCode st (40*width+122) out ∧
      out.scalar.core.ptrs 100=(level : ℤ) ∧ out.scalar.core.ptrs 87=((16*(level+1) : ℕ) : ℤ) ∧
      out.scalar.core.ptrs 41=(width : ℤ) ∧
      out.scalar.core.mem=freshVertexRealMemory st.scalar.core.mem width v.val (16*(level+1)) ∧
      out.scalar.integerMemory=clearLevelVertexFlagsMemory st.scalar.integerMemory width v.val (16*(level+1)+16) [2,3,4,5,6] ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(40*width+122 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  let a := payUnit (pointerWrite st 100 ((level+1 : ℕ) : ℤ))
  have ea : MachineEval m g ω (coreCode (.pinc 100)) st 1 a := by
    simpa only [a,coreCode,hl,Nat.cast_add,Nat.cast_one] using pinc_eval m g ω st 100 hh
  have a100 : a.scalar.core.ptrs 100=((level+1 : ℕ) : ℤ) := by simp [a,payUnit,pcSet,pointerWrite]
  obtain ⟨b,eb,b87,b89,b41,bI,bR,bQ,bW,bO,bH⟩ := level_context_exec m g ω a hh (level+1) width a100
    ((ea.pointer_frame 50 (by decide)).trans hw)
  have ePrefix := MachineEval.seq ea eb
  have b87' : b.scalar.core.ptrs 87=((16*(level+1)+16 : ℕ) : ℤ) := by rw [b87]; congr 1 <;> omega
  obtain ⟨c,ec,cR,cI,cQ,cW,cO,cH⟩ := fresh_vertex_exec m g ω b bH width v.val (16*(level+1)) hWidth
    ((ePrefix.pointer_frame 0 (by decide)).trans h0)
    ((ePrefix.pointer_frame 40 (by decide)).trans hVertex) b41 b87'
  have eBefore := MachineEval.seq ea (MachineEval.seq eb ec)
  have c112 := (eBefore.pointer_frame 112 (by decide)).trans hSelected
  let d := payUnit (pointerWrite c 100 (level : ℤ))
  have ed : MachineEval m g ω (coreCode (.pcopy 100 112)) c 1 d := by
    simpa only [d,coreCode,c112] using pcopy_eval m g ω c 100 112 cH
  have d100 : d.scalar.core.ptrs 100=(level : ℤ) := by simp [d,payUnit,pcSet,pointerWrite]
  obtain ⟨out,ee,e87,e89,e41,eI,eR,eQ,eW,eO,eH⟩ := level_context_exec m g ω d cH level width d100
    (((MachineEval.seq eBefore ed).pointer_frame 50 (by decide)).trans hw)
  have ex : MachineEval m g ω activationChildAdmitApplyCode st (40*width+122) out := by
    have er := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed ee)))
    convert er using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,(ee.pointer_frame 100 (by decide)).trans d100,e87,e41,?_,?_,ex.query_frame (by decide),
    ex.unit_work activationChildAdmitApplyCode_wellFormed (by decide) hh,eO.trans (cO.trans bO),eH⟩
  · rw [eR]
    change c.scalar.core.mem=_
    rw [cR,bR]
    rfl
  · rw [eI]
    change c.scalar.integerMemory=_
    rw [cI,bI]
    rfl

set_option maxHeartbeats 4000000 in
lemma activation_child_admit_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level top width : ℕ) (v : Fin n)
    (hWidth : level < top → 16*(level+1)+22 < width) (hl : st.scalar.core.ptrs 100=(level : ℤ))
    (hSelected : st.scalar.core.ptrs 112=(level : ℤ)) (hTop : st.scalar.core.ptrs 108=(top : ℤ))
    (h0 : st.scalar.core.ptrs 0=0) (hVertex : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 50=(width : ℤ)) (hBase : st.scalar.core.ptrs 87=((16*(level+1) : ℕ) : ℤ))
    (hw41 : st.scalar.core.ptrs 41=(width : ℤ)) :
    ∃ steps out, MachineEval m g ω activationChildAdmitCode st steps out ∧ steps ≤ 40*width+124 ∧
      out.scalar.core.ptrs 100=(level : ℤ) ∧ out.scalar.core.ptrs 87=((16*(level+1) : ℕ) : ℤ) ∧
      out.scalar.core.ptrs 41=(width : ℤ) ∧
      out.scalar.core.mem=(if level < top then freshVertexRealMemory st.scalar.core.mem width v.val (16*(level+1)) else st.scalar.core.mem) ∧
      out.scalar.integerMemory=(if level < top then
        clearLevelVertexFlagsMemory st.scalar.integerMemory width v.val (16*(level+1)+16) [2,3,4,5,6] else st.scalar.integerMemory) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  by_cases hChild : level < top
  · obtain ⟨a,ea,a100,a87,a41,aR,aI,aQ,aW,aO,aH⟩ := activation_child_admit_apply_exec m g ω (payUnit st) hh level width v
      (hWidth hChild) hl hSelected h0 hVertex hw
    have ex : MachineEval m g ω activationChildAdmitCode st (1+(40*width+122)+1) (payUnit a) :=
      MachineEval.pointerGt hh (by rw [hTop,hSelected]; omega) ea
    refine ⟨1+(40*width+122)+1,payUnit a,ex,by omega,a100,a87,a41,?_,?_,ex.query_frame (by decide),
      ex.unit_work activationChildAdmitCode_wellFormed (by decide) hh,aO,aH⟩
    · change a.scalar.core.mem=_
      rw [aR,if_pos hChild]
      rfl
    · change a.scalar.integerMemory=_
      rw [aI,if_pos hChild]
      rfl
  · have eSkip : MachineEval m g ω (.skip : MachineCode) (payUnit st) 0 (payUnit st) := MachineEval.skip _
    have ex : MachineEval m g ω activationChildAdmitCode st 1 (payUnit st) :=
      MachineEval.pointerLe hh (by rw [hTop,hSelected]; omega) eSkip
    refine ⟨1,payUnit st,ex,by omega,hl,hBase,hw41,?_,?_,rfl,?_,rfl,hh⟩
    · change st.scalar.core.mem=_
      rw [if_neg hChild]
    · change st.scalar.integerMemory=_
      rw [if_neg hChild]
    · simpa only [Nat.cast_one] using payUnit_work st

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorPushProgramCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma exteriorActivationPrepareCode_wellFormed : exteriorActivationPrepareCode.wellFormed := by
  refine ⟨?_,levelContextCode_wellFormed⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma exteriorActivationApplyCode_wellFormed : exteriorActivationApplyCode.wellFormed := by
  refine ⟨activationBoundaryCode_wellFormed,exteriorActivationPrepareCode_wellFormed,
    frameListInsertCode_wellFormed 1 3 2 2,activationScalarsCode_wellFormed,activationChildAdmitCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorActivationPrepare

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1800000 in
lemma exterior_activation_prepare_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level width : ℕ)
    (hLevel : st.scalar.core.ptrs 112=(level : ℤ)) (hWidth : st.scalar.core.ptrs 50=(width : ℤ)) :
    ∃ out, MachineEval m g ω exteriorActivationPrepareCode st 9 out ∧
      out.scalar.core.ptrs 100=(level : ℤ) ∧ out.scalar.core.ptrs 87=((16*(level+1) : ℕ) : ℤ) ∧
      out.scalar.core.ptrs 89=((16*(level+1) : ℕ) : ℤ) ∧ out.scalar.core.ptrs 41=(width : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.core.regs=st.scalar.core.regs ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+9 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := payUnit (pointerWrite st 100 (level : ℤ))
  have ea : MachineEval m g ω (coreCode (.pcopy 100 112)) st 1 a := by
    simpa only [a,coreCode,hLevel] using pcopy_eval m g ω st 100 112 hh
  have a100 : a.scalar.core.ptrs 100=(level : ℤ) := by simp [a,payUnit,pcSet,pointerWrite]
  obtain ⟨out,eb,b87,b89,b41,bI,bR,bQ,bW,bO,bH⟩ := level_context_exec m g ω a hh level width a100
    ((ea.pointer_frame 50 (by decide)).trans hWidth)
  have ex : MachineEval m g ω exteriorActivationPrepareCode st 9 out := MachineEval.seq ea eb
  refine ⟨out,ex,(eb.pointer_frame 100 (by decide)).trans a100,b87,b89,b41,bI,bR,ex.register_frame (by
    simp [exteriorActivationPrepareCode,levelContextCode,levelContextInstructions,linearCode,sequenceCode,coreCode,
      MachineCode.allAtoms,registerReadOnly]),ex.query_frame (by decide),
    ex.unit_work exteriorActivationPrepareCode_wellFormed (by decide) hh,bO,bH⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ActivationBoundaryMemory
set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
lemma activation_boundary_memory_other {n : ℕ} (g : InputGraph n) (source : Fin n) (active : Finset (Fin n))
    (boundary level : ℕ) (I : ℤ → ℤ) (z : ℤ) (hz : z ≠ 7) :
    activationBoundaryMemory g source active boundary level I z=I z := by
  unfold activationBoundaryMemory
  split_ifs <;> simp only [Function.update_of_ne hz]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorActivationExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 12000000 in
lemma exterior_activation_apply_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (source : Fin n) (rootActive : Finset (Fin n))
    (boundary level top width : ℕ) (free base : ℤ) (opened : Bool)
    (vertices : List (Fin n)) (F : Finset ℤ)
    (hWidth : level < top → 16*(level+1)+22 < width)
    (h0 : st.scalar.core.ptrs 0=0) (h50 : st.scalar.core.ptrs 50=(width : ℤ))
    (h108 : st.scalar.core.ptrs 108=(top : ℤ)) (h112 : st.scalar.core.ptrs 112=(level : ℤ))
    (h116 : st.scalar.core.ptrs 116=(source.val : ℤ)) (h40 : st.scalar.core.ptrs 40=(source.val : ℤ))
    (h120 : st.scalar.core.ptrs 120=((g.neighbors source).length : ℤ)) (h121 : st.scalar.core.ptrs 121=base)
    (h20 : st.scalar.core.ptrs 20=free) (hOne : st.scalar.core.regs 31=1)
    (hFree : 128+32*((level+1 : ℕ) : ℤ) ≤ free)
    (hBoundary : st.scalar.integerMemory 7=(boundary : ℤ))
    (hOpen : st.scalar.integerMemory (levelHeaderAddress level 9)=(if opened then 1 else 0))
    (hRep : VertexListRep st.scalar.integerMemory (st.scalar.integerMemory (levelHeaderAddress level 1)) vertices F)
    (hBelow : ∀ z ∈ F, z < free) (hAbove : ∀ z ∈ F, 128+32*((level+1 : ℕ) : ℤ) ≤ z)
    (hRow : ∀ (i : ℕ) (hi : i < (g.neighbors source).length), st.scalar.integerMemory (base+(i : ℤ))=(((g.neighbors source)[i]'hi).val : ℤ))
    (hRootActive : level=0 → ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress width v.val 18)=(if v ∈ rootActive then 1 else 0)) :
    ∃ steps out, MachineEval m g ω exteriorActivationApplyCode st steps out ∧
      steps ≤ (g.neighbors source).length*(4*width+19)+48*width+279 ∧
      out.scalar.core.ptrs 100=(top : ℤ) ∧ out.scalar.core.ptrs 20=free+3 ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.integerMemory=exteriorActivationIntegerMemory g source rootActive boundary level top width free st.scalar.integerMemory ∧
      out.scalar.core.mem=exteriorActivationRealMemory st.scalar.core.mem source.val level top width (st.scalar.core.regs 43) opened ∧
      VertexListRep out.scalar.integerMemory (out.scalar.integerMemory (levelHeaderAddress level 1)) (source::vertices) (nodeCells free ∪ F) ∧
      (∀ z ∈ nodeCells free ∪ F, z < free+3) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      out.scalar.core.ptrs 40=(source.val : ℤ) := by
  obtain ⟨u,a,ea,hu,a40,aI,aR,aRegs,aQ,aW,aO,aH⟩ := activation_boundary_exec m g ω source rootActive level boundary width base st hh
    h0 h50 h121 h116 h40 h120 h112 hBoundary hRow hRootActive
  have a112 := (ea.pointer_frame 112 (by decide)).trans h112
  have a50 := (ea.pointer_frame 50 (by decide)).trans h50
  obtain ⟨b,eb,b100,b87,b89,b41,bI,bR,bRegs,bQ,bW,bO,bH⟩ := exterior_activation_prepare_exec m g ω a aH level width a112 a50
  have ePrepare := MachineEval.seq ea eb
  have bRawI : b.scalar.integerMemory=activationBoundaryMemory g source rootActive boundary level st.scalar.integerMemory := bI.trans aI
  have bHeader (slot : ℕ) : b.scalar.integerMemory (levelHeaderAddress level slot)=st.scalar.integerMemory (levelHeaderAddress level slot) := by
    rw [bRawI]
    exact activation_boundary_memory_other g source rootActive boundary level _ _ (by have := levelHeaderAddress_positive level slot; omega)
  have bRep : VertexListRep b.scalar.integerMemory (b.scalar.integerMemory (levelHeaderAddress level 1)) vertices F := by
    rw [bHeader 1]
    apply hRep.frame
    intro z hz
    rw [bRawI]
    exact activation_boundary_memory_other g source rootActive boundary level _ z (by have := hAbove z hz; omega)
  have b20 := (ePrepare.pointer_frame 20 (by decide)).trans h20
  have b40 := (eb.pointer_frame 40 (by decide)).trans a40
  obtain ⟨c,ec,c20,c0,cI,cRep,cBelow,cR,cRegs,cQ,cW,cO,cH⟩ := frame_list_insert_exec m g ω b bH level 1 3 2 2 width
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) free source vertices F hFree b20 b40 b41 b100 b87 bRep hBelow hAbove
  have eList := MachineEval.seq ea (MachineEval.seq eb ec)
  have c100 := (ec.pointer_frame 100 (by decide)).trans b100
  have c87 := (ec.pointer_frame 87 (by decide)).trans b87
  have c40 := (ec.pointer_frame 40 (by decide)).trans b40
  have c41 := (ec.pointer_frame 41 (by decide)).trans b41
  have cOne := (eList.real_register_frame 31 (by decide)).trans hOne
  have c120 : c.scalar.core.ptrs 120=((g.neighbors source).length : ℤ) := (eList.pointer_frame 120 (by decide)).trans h120
  have cOpen : c.scalar.integerMemory (levelHeaderAddress level 9)=(if opened then 1 else 0) := by
    rw [cI,frame_list_insert_header_other _ free source.val level 1 3 2 width 2 9 _ hFree
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),bHeader 9]
    exact hOpen
  obtain ⟨w,d,ed,hw,dR,dI,dQ,dW,dO,dH⟩ := activation_scalars_exec m g ω c cH level width source opened c100 c87 c0 c40 c41 cOne cOpen
  have eScalars := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  obtain ⟨k,e,ee,hk,e100,e87,e41,eR,eI,eQ,eW,eO,eH⟩ := activation_child_admit_exec m g ω d dH level top width source hWidth
    ((ed.pointer_frame 100 (by decide)).trans c100)
    ((eScalars.pointer_frame 112 (by decide)).trans h112) ((eScalars.pointer_frame 108 (by decide)).trans h108)
    ((ed.pointer_frame 0 (by decide)).trans c0) ((ed.pointer_frame 40 (by decide)).trans c40)
    ((eScalars.pointer_frame 50 (by decide)).trans h50) ((ed.pointer_frame 87 (by decide)).trans c87)
    ((ed.pointer_frame 41 (by decide)).trans c41)
  have eBefore := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed ee)))
  have e108 := (eBefore.pointer_frame 108 (by decide)).trans h108
  let out := payUnit (pointerWrite e 100 (top : ℤ))
  have ef : MachineEval m g ω (coreCode (.pcopy 100 108)) e 1 out := by
    simpa only [out,coreCode,e108] using pcopy_eval m g ω e 100 108 eH
  have ex : MachineEval m g ω exteriorActivationApplyCode st (u+(9+((4*width+83)+(w+(k+1))))) out :=
    MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee ef))))
  have hInteger : out.scalar.integerMemory=exteriorActivationIntegerMemory g source rootActive boundary level top width free st.scalar.integerMemory := by
    change e.scalar.integerMemory=_
    rw [eI,dI,cI,bRawI,ePrepare.pointer_frame 120 (by decide),h120]
    rfl
  have hReal : out.scalar.core.mem=exteriorActivationRealMemory st.scalar.core.mem source.val level top width (st.scalar.core.regs 43) opened := by
    change e.scalar.core.mem=_
    rw [eR,dR,cR,bR,aR,eList.real_register_frame 43 (by decide)]
    rfl
  have ePositive : ∀ z, 0 ≤ z → e.scalar.integerMemory z=c.scalar.integerMemory z := by
    intro z hz
    rw [eI,dI]
    split_ifs
    · apply clear_level_flags_frame
      intro off hoff
      have := vertexRecordAddress_negative width source.val (16*(level+1)+16+off)
      omega
    · rfl
  have hList : VertexListRep out.scalar.integerMemory (out.scalar.integerMemory (levelHeaderAddress level 1))
      (source::vertices) (nodeCells free ∪ F) := by
    change VertexListRep e.scalar.integerMemory (e.scalar.integerMemory (levelHeaderAddress level 1)) _ _
    rw [ePositive _ (by have := levelHeaderAddress_positive level 1; omega)]
    apply cRep.frame
    intro z hz
    exact ePositive z (by have := cRep.positive_cells z hz; omega)
  refine ⟨_,out,ex,by omega,by simp [out,payUnit,pcSet,pointerWrite],?_,?_,hInteger,hReal,hList,cBelow,
    ex.query_frame (by decide),ex.unit_work exteriorActivationApplyCode_wellFormed (by decide) hh,
    eO.trans (dO.trans (cO.trans (bO.trans aO))),eH,?_⟩
  · exact ((MachineEval.seq ed (MachineEval.seq ee ef)).pointer_frame 20 (by decide)).trans c20
  · exact ((MachineEval.seq ed (MachineEval.seq ee ef)).pointer_frame 0 (by decide)).trans c0
  · exact ((MachineEval.seq ed (MachineEval.seq ee ef)).pointer_frame 40 (by decide)).trans c40

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution : ∀ (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (source : Fin n) (rootActive : Finset (Fin n))
    (boundary level top width : ℕ) (free base : ℤ) (opened : Bool)
    (vertices : List (Fin n)) (F : Finset ℤ)
    (hWidth : level < top → 16*(level+1)+22 < width)
    (h0 : st.scalar.core.ptrs 0=0) (h50 : st.scalar.core.ptrs 50=(width : ℤ))
    (h108 : st.scalar.core.ptrs 108=(top : ℤ)) (h112 : st.scalar.core.ptrs 112=(level : ℤ))
    (h116 : st.scalar.core.ptrs 116=(source.val : ℤ)) (h40 : st.scalar.core.ptrs 40=(source.val : ℤ))
    (h120 : st.scalar.core.ptrs 120=((g.neighbors source).length : ℤ)) (h121 : st.scalar.core.ptrs 121=base)
    (h20 : st.scalar.core.ptrs 20=free) (hOne : st.scalar.core.regs 31=1)
    (hFree : 128+32*((level+1 : ℕ) : ℤ) ≤ free)
    (hBoundary : st.scalar.integerMemory 7=(boundary : ℤ))
    (hOpen : st.scalar.integerMemory (levelHeaderAddress level 9)=(if opened then 1 else 0))
    (hRep : VertexListRep st.scalar.integerMemory (st.scalar.integerMemory (levelHeaderAddress level 1)) vertices F)
    (hBelow : ∀ z ∈ F, z < free) (hAbove : ∀ z ∈ F, 128+32*((level+1 : ℕ) : ℤ) ≤ z)
    (hRow : ∀ (i : ℕ) (hi : i < (g.neighbors source).length), st.scalar.integerMemory (base+(i : ℤ))=(((g.neighbors source)[i]'hi).val : ℤ))
    (hRootActive : level=0 → ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress width v.val 18)=(if v ∈ rootActive then 1 else 0)),
∃ steps out, MachineEval m g ω exteriorActivationApplyCode st steps out ∧
      steps ≤ (g.neighbors source).length*(4*width+19)+48*width+279 ∧
      out.scalar.core.ptrs 100=(top : ℤ) ∧ out.scalar.core.ptrs 20=free+3 ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.integerMemory=exteriorActivationIntegerMemory g source rootActive boundary level top width free st.scalar.integerMemory ∧
      out.scalar.core.mem=exteriorActivationRealMemory st.scalar.core.mem source.val level top width (st.scalar.core.regs 43) opened ∧
      VertexListRep out.scalar.integerMemory (out.scalar.integerMemory (levelHeaderAddress level 1)) (source::vertices) (nodeCells free ∪ F) ∧
      (∀ z ∈ nodeCells free ∪ F, z < free+3) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      out.scalar.core.ptrs 40=(source.val : ℤ) := by
  exact @NearlyOptimalPPR.Computation.exterior_activation_apply_exec
