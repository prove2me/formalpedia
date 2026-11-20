-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.queue_pair_refresh_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:46:16.987062+00:00
-- url     : https://prove2.me/submissions/97fae451-fc60-403d-88ba-f646b8317248

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

-- Proof module: Solutions.OwnedFIFOFrames

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

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

-- Proof module: Solutions.HighQueueContext

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1800000 in
lemma high_queue_context_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (levelBase : ℕ)
    (hbase : st.scalar.core.ptrs 89=(levelBase : ℤ)) :
    ∃ out, MachineEval m g ω highQueueContextCode st 9 out ∧
      out.scalar.core.ptrs 87=((levelBase+3 : ℕ) : ℤ) ∧
      out.scalar.core.ptrs 88=((levelBase+6 : ℕ) : ℤ) ∧ out.scalar.core.regs 20=0 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+9 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω highQueueContextInstructions
    (by simp [highQueueContextInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,?_,ex.query_frame (by decide),hW,?_,hH⟩
  all_goals simp [linearRun,highQueueContextInstructions,atomState,machineStep,pcSet,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hbase] <;> ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ActualHighKeys

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def actualHighKeys {n : ℕ} (R : ℤ → ℝ) (width levelBase : ℕ) (domain : Finset (Fin n)) : Finset ℕ :=
  (domain.filter (fun v => 0 < R (vertexRecordAddress width v.val (levelBase+4)))).image Fin.val

lemma mem_actual_high_keys {n : ℕ} (R : ℤ → ℝ) (width levelBase : ℕ) (domain : Finset (Fin n))
    (v : Fin n) (hv : v ∈ domain) :
    v.val ∈ actualHighKeys R width levelBase domain ↔ 0 < R (vertexRecordAddress width v.val (levelBase+4)) := by
  classical
  constructor
  · intro h
    obtain ⟨u,hu,he⟩ := Finset.mem_image.mp h
    have he' : u=v := Fin.ext he
    subst u
    exact (Finset.mem_filter.mp hu).2
  · intro h
    exact Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,h⟩,rfl⟩

lemma actual_high_as_exterior {n : ℕ} (I : ℤ → ℤ) (R : ℤ → ℝ) (width levelBase : ℕ)
    (domain : Finset (Fin n)) (queued : Finset ℕ)
    (hZero : ∀ v ∈ domain, I (vertexRecordAddress width v.val (levelBase+5))=0)
    (hDomain : queued ⊆ domain.image Fin.val) (hFlags : QueuedFlags I width (levelBase+6) domain queued) :
    ExteriorQueueMemory I R width (levelBase+3) (levelBase+6) 0 domain
      (actualHighKeys R width levelBase domain) queued := by
  refine ⟨hDomain,hFlags,?_,?_⟩
  · intro v hv
    change 0 ≤ I (vertexRecordAddress width v.val (levelBase+5))
    rw [hZero v hv]
  · intro v hv
    change v.val ∈ actualHighKeys R width levelBase domain ↔
      I (vertexRecordAddress width v.val (levelBase+5))=0 ∧
        (0 : ℝ)*(I (vertexRecordAddress width v.val 0) : ℝ) < R (vertexRecordAddress width v.val (levelBase+4))
    rw [hZero v hv,zero_mul]
    simp only [true_and]
    exact mem_actual_high_keys R width levelBase domain v hv

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

-- Proof module: Solutions.HighBooleanScalars

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1400000 in
lemma high_degree_product_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω highDegreeProductCode st 4 out ∧
      out.scalar.core.regs 22=3*st.scalar.core.regs 20*(st.scalar.core.ptrs 60 : ℝ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+4 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω highDegreeProductInstructions
    (by simp [highDegreeProductInstructions,RealOperation.instruction,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,highDegreeProductInstructions,RealOperation.instruction,atomState,machineStep,pcSet,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh] <;> ring

set_option maxHeartbeats 1400000 in
lemma high_residual_decision_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (product residual : ℝ)
    (hp : st.scalar.core.regs 22=product) (hr : st.scalar.core.regs 10=residual) :
    ∃ steps out, MachineEval m g ω highResidualDecisionCode st steps out ∧
      steps=(if product ≤ residual then 3 else 4) ∧
      out.scalar.core.regs 10=(if product ≤ residual then 1 else 0) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  classical
  let pre := payUnit (realWrite st 23 (product-residual))
  have ep : MachineEval m g ω (.atom (RealOperation.sub.instruction 23 22 10)) st 1 pre := by
    simpa only [pre,RealOperation.value,hp,hr] using binary_eval m g ω st .sub 23 22 10 hh
  have hp23 : pre.scalar.core.regs 23=product-residual := by simp [pre,payUnit,pcSet,realWrite]
  by_cases hle : product ≤ residual
  · let out := payUnit (realWrite (payUnit pre) 10 1)
    have ea : MachineEval m g ω (coreCode (.const 10 1)) (payUnit pre) 1 out := const_eval m g ω (payUnit pre) 10 1 hh
    have eb : MachineEval m g ω (.branchReal 23 (coreCode (.const 10 1)) (coreCode (.const 10 0))) pre 2 out :=
      MachineEval.realNonpos (st:=pre) (r:=23) hh (by rw [hp23]; linarith) ea
    refine ⟨3,out,MachineEval.seq ep eb,by simp [hle],?_,rfl,rfl,rfl,?_,rfl,hh⟩
    · simp [out,payUnit,pcSet,realWrite,hle]
    · simp [out,pre,payUnit,pcSet,realWrite]
      ring
  · let mid := payUnit (realWrite (payUnit pre) 10 0)
    have ea : MachineEval m g ω (coreCode (.const 10 0)) (payUnit pre) 1 mid := const_eval m g ω (payUnit pre) 10 0 hh
    have eb : MachineEval m g ω (.branchReal 23 (coreCode (.const 10 1)) (coreCode (.const 10 0))) pre 3 (payUnit mid) :=
      MachineEval.realPos (st:=pre) (r:=23) hh (by rw [hp23]; linarith) ea
    refine ⟨4,payUnit mid,MachineEval.seq ep eb,by simp [hle],?_,rfl,rfl,rfl,?_,rfl,hh⟩
    · simp [mid,payUnit,pcSet,realWrite,hle]
    · simp [mid,pre,payUnit,pcSet,realWrite]
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HighActiveExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2200000 in
lemma high_active_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex levelBase : ℕ) (theta : ℝ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hlevel : st.scalar.core.ptrs 87=(levelBase : ℤ))
    (htheta : st.scalar.core.regs 20=theta) :
    ∃ steps out, MachineEval m g ω highActiveCode st steps out ∧ steps ≤ 8*width+26 ∧
      out.scalar.core.regs 10=(if 3*theta*(st.scalar.integerMemory (vertexRecordAddress width vertex 0) : ℝ) ≤
        st.scalar.core.mem (vertexRecordAddress width vertex (levelBase+1)) then 1 else 0) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,ha60,haI,haR,haQ,haW,haO,haH⟩ := vertex_field_read_exec m g ω st hh width vertex 0 60 hz hv hw
  have ha20 := (ea.real_register_frame 20 (by decide)).trans htheta
  obtain ⟨b,eb,hb22,hbI,hbR,hbW,hbO,hbH⟩ := high_degree_product_exec m g ω a haH
  have hb22' : b.scalar.core.regs 22=3*theta*(st.scalar.integerMemory (vertexRecordAddress width vertex 0) : ℝ) := by rw [hb22,ha20,ha60]
  obtain ⟨c,ec,hp,hcI,hcR,hcW,hcO,hcH⟩ := exteriorResidualOffsetRoutine.execute m g ω b hbH
  have ec2 : MachineEval m g ω exteriorResidualOffsetRoutine.code b 2 c := ec
  have hb87 : b.scalar.core.ptrs 87=(levelBase : ℤ) :=
    (eb.pointer_frame 87 (by decide)).trans ((ea.pointer_frame 87 (by decide)).trans hlevel)
  have hc44 : c.scalar.core.ptrs 44=((levelBase+1 : ℕ) : ℤ) := by
    rw [hp]
    simp [exteriorResidualOffsetRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
      PointerOp.destination,PointerOp.result,hb87]
  have hc0 := (ec.pointer_frame 0 (by decide)).trans ((eb.pointer_frame 0 (by decide)).trans ((ea.pointer_frame 0 (by decide)).trans hz))
  have hc40 := (ec.pointer_frame 40 (by decide)).trans ((eb.pointer_frame 40 (by decide)).trans ((ea.pointer_frame 40 (by decide)).trans hv))
  have hc41 := (ec.pointer_frame 41 (by decide)).trans ((eb.pointer_frame 41 (by decide)).trans ((ea.pointer_frame 41 (by decide)).trans hw))
  obtain ⟨d,ed,hd10,hdI,hdR,hdW,hdO,hdH⟩ := vertex_real_load_exec m g ω c hcH width vertex (levelBase+1) hc0 hc40 hc41 hc44
  have hd22 : d.scalar.core.regs 22=3*theta*(st.scalar.integerMemory (vertexRecordAddress width vertex 0) : ℝ) :=
    (ed.real_register_frame 22 (by decide)).trans ((ec.real_register_frame 22 (by decide)).trans hb22')
  have hd10' : d.scalar.core.regs 10=st.scalar.core.mem (vertexRecordAddress width vertex (levelBase+1)) := by rw [hd10,hcR,hbR,haR]
  obtain ⟨u,out,ef,hu,ho10,hoI,hoR,hoQ,hoW,hoO,hoH⟩ := high_residual_decision_exec m g ω d hdH
    (3*theta*(st.scalar.integerMemory (vertexRecordAddress width vertex 0) : ℝ))
    (st.scalar.core.mem (vertexRecordAddress width vertex (levelBase+1))) hd22 hd10'
  have hu4 : u ≤ 4 := by rw [hu]; split_ifs <;> omega
  have eRun := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec2 (MachineEval.seq ed ef)))
  refine ⟨(4*width+9)+(4+(2+((4*width+7)+u))),out,eRun,by omega,ho10,
    hoI.trans (hdI.trans (hcI.trans (hbI.trans haI))),hoR.trans (hdR.trans (hcR.trans (hbR.trans haR))),
    eRun.query_frame (by decide),?_,hoO.trans (hdO.trans (hcO.trans (hbO.trans haO))),hoH⟩
  · rw [hoW,hdW,hcW,hbW,haW]
    change st.work+(4*width+9 : ℕ)+4+(2 : ℕ)+(4*width+7 : ℕ)+u= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HighBooleanValueExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2400000 in
lemma high_boolean_value_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex levelBase : ℕ) (theta : ℝ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hlevel : st.scalar.core.ptrs 87=(levelBase : ℤ))
    (htheta : st.scalar.core.regs 20=theta)
    (hactive : 0 ≤ st.scalar.integerMemory (vertexRecordAddress width vertex (levelBase+2))) :
    ∃ steps out, MachineEval m g ω highBooleanValueCode st steps out ∧ steps ≤ 12*width+38 ∧
      out.scalar.core.regs 10=(if st.scalar.integerMemory (vertexRecordAddress width vertex (levelBase+2))=0 then 0 else
        if 3*theta*(st.scalar.integerMemory (vertexRecordAddress width vertex 0) : ℝ) ≤
          st.scalar.core.mem (vertexRecordAddress width vertex (levelBase+1)) then 1 else 0) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
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
  have hb20 := (eb.real_register_frame 20 (by decide)).trans ((ea.real_register_frame 20 (by decide)).trans htheta)
  by_cases he : st.scalar.integerMemory (vertexRecordAddress width vertex (levelBase+2))=0
  · let out := payUnit (realWrite (payUnit b) 10 0)
    have ec : MachineEval m g ω (coreCode (.const 10 0)) (payUnit b) 1 out := const_eval m g ω (payUnit b) 10 0 hbH
    have ebranch : MachineEval m g ω (.branchPointer 51 0 (coreCode (.const 10 0)) highActiveCode) b 2 out :=
      MachineEval.pointerLe hbH (by rw [hb51',hb0,he]) ec
    have eRun := MachineEval.seq ea3 (MachineEval.seq eb ebranch)
    refine ⟨3+((4*width+7)+2),out,eRun,by omega,?_,hbI.trans haI,hbR.trans haR,
      eRun.query_frame (by decide),?_,hbO.trans haO,hbH⟩
    · simp [out,payUnit,pcSet,realWrite,he]
    · change b.work+1+1= _
      rw [hbW,haW]
      change st.work+(3 : ℕ)+(4*width+7 : ℕ)+1+1= _
      push_cast
      ring
  · obtain ⟨u,mid,ec,hu,hc10,hcI,hcR,hcQ,hcW,hcO,hcH⟩ := high_active_exec m g ω (payUnit b) hbH
      width vertex levelBase theta hb0 hb40 hb41 hb87 hb20
    have ebranch : MachineEval m g ω (.branchPointer 51 0 (coreCode (.const 10 0)) highActiveCode) b (1+u+1) (payUnit mid) :=
      MachineEval.pointerGt hbH (by rw [hb51',hb0]; omega) ec
    have eRun := MachineEval.seq ea3 (MachineEval.seq eb ebranch)
    refine ⟨3+((4*width+7)+(1+u+1)),payUnit mid,eRun,by omega,?_,hcI.trans (hbI.trans haI),hcR.trans (hbR.trans haR),
      eRun.query_frame (by decide),?_,hcO.trans (hbO.trans haO),hcH⟩
    · change mid.scalar.core.regs 10= _
      rw [if_neg he,hc10]
      change (if 3*theta*(b.scalar.integerMemory _ : ℝ) ≤ b.scalar.core.mem _ then (1 : ℝ) else 0)= _
      rw [hbI,haI,hbR,haR]
    · change mid.work+1= _
      rw [hcW,payUnit_work,hbW,haW]
      change st.work+(3 : ℕ)+(4*width+7 : ℕ)+1+u+1= _
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HighBooleanUpdateExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2000000 in
lemma high_boolean_update_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex levelBase : ℕ) (theta : ℝ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hlevel : st.scalar.core.ptrs 87=(levelBase : ℤ))
    (htheta : st.scalar.core.regs 20=theta)
    (hactive : 0 ≤ st.scalar.integerMemory (vertexRecordAddress width vertex (levelBase+2))) :
    ∃ steps out, MachineEval m g ω highBooleanUpdateCode st steps out ∧ steps ≤ 16*width+50 ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width vertex (levelBase+4))
        (if st.scalar.integerMemory (vertexRecordAddress width vertex (levelBase+2))=0 then 0 else
          if 3*theta*(st.scalar.integerMemory (vertexRecordAddress width vertex 0) : ℝ) ≤
            st.scalar.core.mem (vertexRecordAddress width vertex (levelBase+1)) then 1 else 0) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.regs 20=theta ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨u,pre,ep,hu,hp10,hpI,hpR,hpQ,hpW,hpO,hpH⟩ := high_boolean_value_exec m g ω st hh width vertex levelBase theta hz hv hw hlevel htheta hactive
  obtain ⟨mid,em,hp,hmI,hmR,hmW,hmO,hmH⟩ := highBooleanStoreOffsetRoutine.execute m g ω pre hpH
  have em5 : MachineEval m g ω highBooleanStoreOffsetRoutine.code pre 5 mid := em
  have hp87 := (ep.pointer_frame 87 (by decide)).trans hlevel
  have hm44 : mid.scalar.core.ptrs 44=((levelBase+4 : ℕ) : ℤ) := by
    rw [hp]
    simp [highBooleanStoreOffsetRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
      PointerOp.destination,PointerOp.result,hp87]
    ring
  have hm0 := (em.pointer_frame 0 (by decide)).trans ((ep.pointer_frame 0 (by decide)).trans hz)
  have hm40 := (em.pointer_frame 40 (by decide)).trans ((ep.pointer_frame 40 (by decide)).trans hv)
  have hm41 := (em.pointer_frame 41 (by decide)).trans ((ep.pointer_frame 41 (by decide)).trans hw)
  have hm10 := (em.real_register_frame 10 (by decide)).trans hp10
  obtain ⟨out,es,hoR,hoI,hoRegs,hoW,hoO,hoH⟩ := vertex_real_store_exec m g ω mid hmH width vertex (levelBase+4) hm0 hm40 hm41 hm44
  have eRun := MachineEval.seq ep (MachineEval.seq em5 es)
  refine ⟨u+(5+(4*width+7)),out,eRun,by omega,?_,hoI.trans (hmI.trans hpI),
    (eRun.real_register_frame 20 (by decide)).trans htheta,(eRun.pointer_frame 0 (by decide)).trans hz,
    eRun.query_frame (by decide),?_,hoO.trans (hmO.trans hpO),hoH⟩
  · rw [hoR,hmR,hpR,hm10]
  · rw [hoW,hmW,hpW]
    change st.work+u+(5 : ℕ)+(4*width+7 : ℕ)= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HighRefreshWeakObject

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 6000000 in
lemma high_refresh_weak_object_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width levelBase length N R : ℕ)
    (hw : levelBase+6 < width) (base floor : ℤ) (hFloor : 2 ≤ floor) (theta : ℝ)
    (domain : Finset (Fin n)) (obj : RankQueueObject st.scalar.integerMemory base length (st.scalar.core.ptrs 20) floor)
    (v : Fin n) (hv : v ∈ domain)
    (hZero : ∀ u ∈ domain, st.scalar.integerMemory (vertexRecordAddress width u.val (levelBase+5))=0)
    (hDomain : obj.keys ⊆ domain.image Fin.val)
    (hFlags : QueuedFlags st.scalar.integerMemory width (levelBase+6) domain obj.keys)
    (h0 : st.scalar.core.ptrs 0=0) (hBase : st.scalar.core.ptrs 13=base)
    (hLength : st.scalar.core.ptrs 25=(length : ℤ)) (hFree : floor ≤ st.scalar.core.ptrs 20)
    (hVertex : st.scalar.core.ptrs 40=(v.val : ℤ)) (hWidth : st.scalar.core.ptrs 50=(width : ℤ))
    (hLevel : st.scalar.core.ptrs 89=(levelBase : ℤ)) (hTheta : st.scalar.core.regs 20=theta)
    (hActive : 0 ≤ st.scalar.integerMemory (vertexRecordAddress width v.val (levelBase+2)))
    (hMass : obj.mass ≤ N) (hCap : R < length) (hPow : N < 2^R) :
    ∃ steps out, ∃ next : RankQueueObject out.scalar.integerMemory base length (out.scalar.core.ptrs 20) floor,
      MachineEval m g ω highQueueRefreshCode st steps out ∧ steps ≤ 21*R+36*width+131 ∧
      next.keys=(if st.scalar.integerMemory (vertexRecordAddress width v.val (levelBase+2)) ≠ 0 ∧
        3*theta*(st.scalar.integerMemory (vertexRecordAddress width v.val 0) : ℝ) ≤
          st.scalar.core.mem (vertexRecordAddress width v.val (levelBase+1)) then insert v.val obj.keys else obj.keys) ∧
      next.mass ≤ obj.mass+1 ∧ next.keys ⊆ domain.image Fin.val ∧
      QueuedFlags out.scalar.integerMemory width (levelBase+6) domain next.keys ∧
      st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 ∧ out.scalar.core.ptrs 20 ≤ st.scalar.core.ptrs 20+3 ∧
      next.cells ⊆ nodeCells (st.scalar.core.ptrs 20) ∪ obj.cells ∧
      (∀ other : Fin n, ∀ field < width, field ≠ levelBase+6 →
        out.scalar.integerMemory (vertexRecordAddress width other.val field)=st.scalar.integerMemory (vertexRecordAddress width other.val field)) ∧
      (∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 → z ∉ obj.cells → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width v.val (levelBase+4))
        (if st.scalar.integerMemory (vertexRecordAddress width v.val (levelBase+2))=0 then 0 else
          if 3*theta*(st.scalar.integerMemory (vertexRecordAddress width v.val 0) : ℝ) ≤
            st.scalar.core.mem (vertexRecordAddress width v.val (levelBase+1)) then 1 else 0) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧ out.scalar.core.ptrs 0=0 := by
  obtain ⟨a,ea,aPtrs,aI,aR,aW,aO,aH⟩ := highQueueRefreshInit.execute m g ω st hh
  have ea2 : MachineEval m g ω highQueueRefreshInit.code st 2 a := ea
  have a41 : a.scalar.core.ptrs 41=(width : ℤ) := by
    rw [aPtrs]
    simp [highQueueRefreshInit,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,hWidth]
  have a87 : a.scalar.core.ptrs 87=(levelBase : ℤ) := by
    rw [aPtrs]
    simp [highQueueRefreshInit,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,hLevel]
  obtain ⟨u,b,eb,hu,bR,bI,bTheta,b0,bQ,bW,bO,bH⟩ := high_boolean_update_exec m g ω a aH width v.val levelBase theta
    ((ea.pointer_frame 0 (by decide)).trans h0) ((ea.pointer_frame 40 (by decide)).trans hVertex)
    a41 a87 ((ea.real_register_frame 20 (by decide)).trans hTheta) (by rw [aI]; exact hActive)
  have b89 := (eb.pointer_frame 89 (by decide)).trans ((ea.pointer_frame 89 (by decide)).trans hLevel)
  obtain ⟨c,ec,c87,c88,cTheta,cI,cR,cQ,cW,cO,cH⟩ := high_queue_context_exec m g ω b bH levelBase b89
  have ePrefix := MachineEval.seq ea2 (MachineEval.seq eb ec)
  have cInteger : c.scalar.integerMemory=st.scalar.integerMemory := cI.trans (bI.trans aI)
  have cFree : c.scalar.core.ptrs 20=st.scalar.core.ptrs 20 := ePrefix.pointer_frame 20 (by decide)
  let cObj : RankQueueObject c.scalar.integerMemory base length (c.scalar.core.ptrs 20) floor :=
    obj.frame (fun z hz => congrFun cInteger z) (by rw [cFree])
  have cData : ExteriorQueueMemory c.scalar.integerMemory c.scalar.core.mem width (levelBase+3) (levelBase+6) 0 domain
      (actualHighKeys c.scalar.core.mem width levelBase domain) cObj.keys := by
    apply actual_high_as_exterior
    · rw [cInteger]
      exact hZero
    · exact hDomain
    · change QueuedFlags c.scalar.integerMemory width (levelBase+6) domain obj.keys
      rw [cInteger]
      exact hFlags
  have cCtx : ExteriorQueueContext c width (levelBase+3) (levelBase+6) length base floor 0 := {
    zero := (ePrefix.pointer_frame 0 (by decide)).trans h0
    basePointer := (ePrefix.pointer_frame 13 (by decide)).trans hBase
    lengthPointer := (ePrefix.pointer_frame 25 (by decide)).trans hLength
    widthPointer := (ePrefix.pointer_frame 50 (by decide)).trans hWidth
    levelPointer := c87
    flagPointer := c88
    threshold := cTheta
    floorBound := by rw [cFree]; exact hFree }
  obtain ⟨k,out,next,ed,hk,dCtx,dData,dKeys,dMass,dFree,dUpper,dCells,dFields,dPos,dR,dQ,dW,dO,dH⟩ :=
    exterior_refresh_object_exec m g ω c cH width (levelBase+3) (levelBase+6) length N R hw (by omega) (by omega) (by omega)
      base floor hFloor 0 domain (actualHighKeys c.scalar.core.mem width levelBase domain) cObj cCtx cData v hv
      ((ePrefix.pointer_frame 40 (by decide)).trans hVertex) hMass hCap hPow
  have hKeyV : v.val ∈ actualHighKeys c.scalar.core.mem width levelBase domain ↔
      st.scalar.integerMemory (vertexRecordAddress width v.val (levelBase+2)) ≠ 0 ∧
      3*theta*(st.scalar.integerMemory (vertexRecordAddress width v.val 0) : ℝ) ≤
        st.scalar.core.mem (vertexRecordAddress width v.val (levelBase+1)) := by
    rw [mem_actual_high_keys _ _ _ _ v hv,cR,bR,aI,aR,Function.update_self]
    by_cases ha : st.scalar.integerMemory (vertexRecordAddress width v.val (levelBase+2))=0 <;>
      by_cases hr : 3*theta*(st.scalar.integerMemory (vertexRecordAddress width v.val 0) : ℝ) ≤
        st.scalar.core.mem (vertexRecordAddress width v.val (levelBase+1)) <;> simp [ha,hr]
  have ex : MachineEval m g ω highQueueRefreshCode st (2+(u+(9+k))) out :=
    MachineEval.seq ea2 (MachineEval.seq eb (MachineEval.seq ec ed))
  refine ⟨2+(u+(9+k)),out,next,ex,by omega,?_,dMass,dData.queuedDomain,dData.flags,?_,?_,?_,
    (fun other field hf hn => (dFields other field hf hn).trans (congrFun cInteger _)),
    ?_,?_,ex.query_frame (by decide),?_,dO.trans (cO.trans (bO.trans aO)),dH,dCtx.zero⟩
  · rw [dKeys]
    simp only [hKeyV]
    rfl
  · rw [cFree] at dFree
    exact dFree
  · rw [cFree] at dUpper
    exact dUpper
  · change next.cells ⊆ nodeCells (c.scalar.core.ptrs 20) ∪ obj.cells at dCells
    rw [cFree] at dCells
    exact dCells
  · intro z hz hzf hn
    have hzf' : z < c.scalar.core.ptrs 20 := by rw [cFree]; exact hzf
    exact (dPos z hz hzf' hn).trans (congrFun cInteger z)
  · rw [dR,cR,bR,aI,aR]
  · rw [dW,cW,bW,aW]
    change st.work+(2 : ℕ)+u+(9 : ℕ)+k=_
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorQueueScopedFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma ExteriorQueueMemory.scoped_frame {n : ℕ} {I J : ℤ → ℤ} {R S : ℤ → ℝ}
    {width levelBase flagOffset : ℕ} {q : ℝ} {domain : Finset (Fin n)} {valid queued : Finset ℕ}
    (h : ExteriorQueueMemory I R width levelBase flagOffset q domain valid queued)
    (hFlag : ∀ v ∈ domain, J (vertexRecordAddress width v.val flagOffset)=I (vertexRecordAddress width v.val flagOffset))
    (hActive : ∀ v ∈ domain, J (vertexRecordAddress width v.val (levelBase+2))=I (vertexRecordAddress width v.val (levelBase+2)))
    (hDegree : ∀ v ∈ domain, J (vertexRecordAddress width v.val 0)=I (vertexRecordAddress width v.val 0))
    (hResidual : ∀ v ∈ domain, S (vertexRecordAddress width v.val (levelBase+1))=R (vertexRecordAddress width v.val (levelBase+1))) :
    ExteriorQueueMemory J S width levelBase flagOffset q domain valid queued := by
  refine ⟨h.queuedDomain,h.flags.frame hFlag,?_,?_⟩
  · intro v hv
    rw [hActive v hv]
    exact h.activeNonnegative v hv
  · intro v hv
    rw [hActive v hv,hDegree v hv,hResidual v hv]
    exact h.eligibility v hv

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueuePairRefreshCode

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 7000000 in
lemma queue_pair_refresh_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width levelBase length N R : ℕ)
    (hw : levelBase+6 < width) (extBase highBase floor : ℤ) (hFloor : 2 ≤ floor)
    (q theta : ℝ) (domain : Finset (Fin n)) (extValid highValid : Finset ℕ)
    (extObj : RankQueueObject st.scalar.integerMemory extBase length (st.scalar.core.ptrs 20) floor)
    (highObj : RankQueueObject st.scalar.integerMemory highBase length (st.scalar.core.ptrs 20) floor)
    (hSep : Disjoint highObj.cells extObj.cells)
    (ctx : ExteriorQueueContext st width levelBase (levelBase+3) length extBase floor q)
    (extData : ExteriorQueueMemory st.scalar.integerMemory st.scalar.core.mem width levelBase (levelBase+3) q domain extValid extObj.keys)
    (hZero : ∀ u ∈ domain, st.scalar.integerMemory (vertexRecordAddress width u.val (levelBase+5))=0)
    (hHighDomain : highObj.keys ⊆ domain.image Fin.val)
    (hHighFlags : QueuedFlags st.scalar.integerMemory width (levelBase+6) domain highObj.keys)
    (hHighValid : ∀ u ∈ domain, u.val ∈ highValid ↔
      st.scalar.integerMemory (vertexRecordAddress width u.val (levelBase+2)) ≠ 0 ∧
      3*theta*(st.scalar.integerMemory (vertexRecordAddress width u.val 0) : ℝ) ≤
        st.scalar.core.mem (vertexRecordAddress width u.val (levelBase+1)))
    (hHighBase : st.scalar.core.ptrs 128=highBase) (hLevel : st.scalar.core.ptrs 89=(levelBase : ℤ))
    (hOne : st.scalar.core.regs 31=1) (hTheta : st.scalar.core.regs 47=theta)
    (v : Fin n) (hv : v ∈ domain) (hVertex : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hExtMass : extObj.mass ≤ N) (hHighMass : highObj.mass ≤ N) (hCap : R < length) (hPow : N < 2^R) :
    ∃ steps out,
    ∃ newExt : RankQueueObject out.scalar.integerMemory extBase length (out.scalar.core.ptrs 20) floor,
    ∃ newHigh : RankQueueObject out.scalar.integerMemory highBase length (out.scalar.core.ptrs 20) floor,
      MachineEval m g ω queuePairRefreshCode st steps out ∧ steps ≤ 42*R+56*width+203 ∧
      newExt.keys=(if v.val ∈ extValid then insert v.val extObj.keys else extObj.keys) ∧
      newHigh.keys=(if v.val ∈ highValid then insert v.val highObj.keys else highObj.keys) ∧
      newExt.mass ≤ extObj.mass+1 ∧ newHigh.mass ≤ highObj.mass+1 ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase (levelBase+3) q domain extValid newExt.keys ∧
      newHigh.keys ⊆ domain.image Fin.val ∧ QueuedFlags out.scalar.integerMemory width (levelBase+6) domain newHigh.keys ∧
      Disjoint newHigh.cells newExt.cells ∧ st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 ∧
      out.scalar.core.ptrs 20 ≤ st.scalar.core.ptrs 20+6 ∧
      (∀ z ∈ newExt.cells ∪ newHigh.cells, z < st.scalar.core.ptrs 20 → z ∈ extObj.cells ∪ highObj.cells) ∧
      (∀ other : Fin n, ∀ field < width, field ≠ levelBase+3 → field ≠ levelBase+6 →
        out.scalar.integerMemory (vertexRecordAddress width other.val field)=st.scalar.integerMemory (vertexRecordAddress width other.val field)) ∧
      (∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 → z ∉ extObj.cells ∪ highObj.cells → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width v.val (levelBase+4))
        (if st.scalar.integerMemory (vertexRecordAddress width v.val (levelBase+2))=0 then 0 else
          if 3*theta*(st.scalar.integerMemory (vertexRecordAddress width v.val 0) : ℝ) ≤
            st.scalar.core.mem (vertexRecordAddress width v.val (levelBase+1)) then 1 else 0) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧
      out.scalar.halted=false ∧ out.scalar.core.ptrs 0=0 := by
  obtain ⟨u,a,aExt,ea,hu,aCtx,aData,aKeys,aMass,aFree,aUpper,aCells,aFields,aPos,aR,aQ,aW,aO,aH⟩ :=
    exterior_refresh_object_exec m g ω st hh width levelBase (levelBase+3) length N R (by omega) (by omega) (by omega) (by omega)
      extBase floor hFloor q domain extValid extObj ctx extData v hv hVertex hExtMass hCap hPow
  let aHigh : RankQueueObject a.scalar.integerMemory highBase length (a.scalar.core.ptrs 20) floor :=
    highObj.other_frame extObj.cells hFloor hSep aFree aPos
  have aOld (z : ℤ) (hz : z ∈ aExt.cells) (hlt : z < st.scalar.core.ptrs 20) : z ∈ extObj.cells := by
    rcases Finset.mem_union.mp (aCells hz) with hn|he
    · have := (nodeCells_mem_iff (st.scalar.core.ptrs 20) z).mp hn
      omega
    · exact he
  have aSep : Disjoint aExt.cells aHigh.cells :=
    (queue_disjoint_after_growth highObj.below hSep aOld).symm
  let b := linearRun m g ω queuePairHighPrepInstructions a
  obtain ⟨eb,bW,bH⟩ := linear_execute m g ω queuePairHighPrepInstructions
    (by simp [queuePairHighPrepInstructions,unitInstruction,straightInstruction]) a aH
  have bI : b.scalar.integerMemory=a.scalar.integerMemory := by
    simp [b,linearRun,queuePairHighPrepInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,aH]
  have bR : b.scalar.core.mem=a.scalar.core.mem := by
    simp [b,linearRun,queuePairHighPrepInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,aH]
  have bO : b.output=a.output := by
    simp [b,linearRun,queuePairHighPrepInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,aH]
  have bFree : b.scalar.core.ptrs 20=a.scalar.core.ptrs 20 := eb.pointer_frame 20 (by decide)
  let bHigh : RankQueueObject b.scalar.integerMemory highBase length (b.scalar.core.ptrs 20) floor :=
    aHigh.frame (fun z hz => congrFun bI z) (by rw [bFree])
  have ePrefix := MachineEval.seq ea eb
  have a128 : a.scalar.core.ptrs 128=highBase := (ea.pointer_frame 128 (by decide)).trans hHighBase
  have a47 : a.scalar.core.regs 47=theta := (ea.real_register_frame 47 (by decide)).trans hTheta
  have a31 : a.scalar.core.regs 31=1 := (ea.real_register_frame 31 (by decide)).trans hOne
  have b13 : b.scalar.core.ptrs 13=highBase := by
    simp [b,linearRun,queuePairHighPrepInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,aH,a128]
  have b20 : b.scalar.core.regs 20=theta := by
    simp [b,linearRun,queuePairHighPrepInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,aH,a47,a31]
  have bField (other : Fin n) (field : ℕ) (hf : field < width) (hn : field ≠ levelBase+3) :
      b.scalar.integerMemory (vertexRecordAddress width other.val field)=st.scalar.integerMemory (vertexRecordAddress width other.val field) := by
    rw [bI]
    exact aFields other field hf hn
  have bZero : ∀ w ∈ domain, b.scalar.integerMemory (vertexRecordAddress width w.val (levelBase+5))=0 := by
    intro w hw'
    rw [bField w (levelBase+5) (by omega) (by omega)]
    exact hZero w hw'
  have bFlags : QueuedFlags b.scalar.integerMemory width (levelBase+6) domain bHigh.keys :=
    hHighFlags.frame (fun w hw' => bField w (levelBase+6) hw (by omega))
  have bActive : 0 ≤ b.scalar.integerMemory (vertexRecordAddress width v.val (levelBase+2)) := by
    rw [bField v (levelBase+2) (by omega) (by omega)]
    exact extData.activeNonnegative v hv
  obtain ⟨k,out,cHigh,ec,hk,cKeys,cMass,cDomain,cFlags,cFree,cUpper,cCells,cFields,cPos,cR,cQ,cW,cO,cH,c0⟩ :=
    high_refresh_weak_object_exec m g ω b bH width levelBase length N R hw highBase floor hFloor theta domain bHigh v hv bZero
      hHighDomain bFlags ((eb.pointer_frame 0 (by decide)).trans aCtx.zero) b13
      ((eb.pointer_frame 25 (by decide)).trans aCtx.lengthPointer)
      (by rw [bFree]; exact aCtx.floorBound)
      ((ePrefix.pointer_frame 40 (by decide)).trans hVertex)
      ((ePrefix.pointer_frame 50 (by decide)).trans ctx.widthPointer)
      ((ePrefix.pointer_frame 89 (by decide)).trans hLevel) b20 bActive hHighMass hCap hPow
  let cExt : RankQueueObject out.scalar.integerMemory extBase length (out.scalar.core.ptrs 20) floor :=
    aExt.other_frame bHigh.cells hFloor aSep (by rw [←bFree]; exact cFree)
      (by intro z hz hzf hn; exact (cPos z hz (by rw [bFree]; exact hzf) hn).trans (congrFun bI z))
  have cOld (z : ℤ) (hz : z ∈ cHigh.cells) (hlt : z < b.scalar.core.ptrs 20) : z ∈ bHigh.cells := by
    rcases Finset.mem_union.mp (cCells hz) with hn|he
    · have := (nodeCells_mem_iff (b.scalar.core.ptrs 20) z).mp hn
      omega
    · exact he
  have cExtData : ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase (levelBase+3) q domain extValid cExt.keys := by
    apply aData.scoped_frame
    · intro w hw'; exact (cFields w (levelBase+3) (by omega) (by omega)).trans (congrFun bI _)
    · intro w hw'; exact (cFields w (levelBase+2) (by omega) (by omega)).trans (congrFun bI _)
    · intro w hw'; exact (cFields w 0 (by omega) (by omega)).trans (congrFun bI _)
    · intro w hw'
      rw [cR,vertex_memory_update_other_field _ width v.val w.val (levelBase+4) (levelBase+1) _ (by omega) (by omega) (by omega),bR]
  have ex : MachineEval m g ω queuePairRefreshCode st (u+(2+k)) out := MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨u+(2+k),out,cExt,cHigh,ex,by omega,aKeys,?_,aMass,cMass,cExtData,cDomain,cFlags,?_,?_,?_,?_,?_,?_,?_,
    ex.query_frame (by decide),?_,cO.trans (bO.trans aO),cH,c0⟩
  · rw [cKeys,bField v (levelBase+2) (by omega) (by omega),bField v 0 (by omega) (by omega),bR,aR]
    simp only [←hHighValid v hv]
    rfl
  · exact (queue_disjoint_after_growth aExt.below aSep (fun z hz hlt => cOld z hz (by rw [bFree]; exact hlt))).symm
  · exact aFree.trans (by rw [←bFree]; exact cFree)
  · rw [bFree] at cUpper
    omega
  · intro z hz hlt
    rcases Finset.mem_union.mp hz with he|hh'
    · exact Finset.mem_union_left _ (aOld z he hlt)
    · have hzA : z < b.scalar.core.ptrs 20 := by rw [bFree]; exact hlt.trans_le aFree
      exact Finset.mem_union_right _ (cOld z hh' hzA)
  · intro w field hf hExt hHigh
    exact (cFields w field hf hHigh).trans (bField w field hf hExt)
  · intro z hz hlt hn
    have hNotExt : z ∉ extObj.cells := fun h => hn (Finset.mem_union_left _ h)
    have hNotHigh : z ∉ bHigh.cells := fun h => hn (Finset.mem_union_right _ h)
    have hzB : z < b.scalar.core.ptrs 20 := by rw [bFree]; exact hlt.trans_le aFree
    exact (cPos z hz hzB hNotHigh).trans ((congrFun bI z).trans (aPos z hz hlt hNotExt))
  · rw [cR,bR,aR,bField v (levelBase+2) (by omega) (by omega),bField v 0 (by omega) (by omega)]
  · rw [cW,bW,aW]
    change st.work+u+(2 : ℕ)+k=_
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution : ∀ (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width levelBase length N R : ℕ)
    (hw : levelBase+6 < width) (extBase highBase floor : ℤ) (hFloor : 2 ≤ floor)
    (q theta : ℝ) (domain : Finset (Fin n)) (extValid highValid : Finset ℕ)
    (extObj : RankQueueObject st.scalar.integerMemory extBase length (st.scalar.core.ptrs 20) floor)
    (highObj : RankQueueObject st.scalar.integerMemory highBase length (st.scalar.core.ptrs 20) floor)
    (hSep : Disjoint highObj.cells extObj.cells)
    (ctx : ExteriorQueueContext st width levelBase (levelBase+3) length extBase floor q)
    (extData : ExteriorQueueMemory st.scalar.integerMemory st.scalar.core.mem width levelBase (levelBase+3) q domain extValid extObj.keys)
    (hZero : ∀ u ∈ domain, st.scalar.integerMemory (vertexRecordAddress width u.val (levelBase+5))=0)
    (hHighDomain : highObj.keys ⊆ domain.image Fin.val)
    (hHighFlags : QueuedFlags st.scalar.integerMemory width (levelBase+6) domain highObj.keys)
    (hHighValid : ∀ u ∈ domain, u.val ∈ highValid ↔
      st.scalar.integerMemory (vertexRecordAddress width u.val (levelBase+2)) ≠ 0 ∧
      3*theta*(st.scalar.integerMemory (vertexRecordAddress width u.val 0) : ℝ) ≤
        st.scalar.core.mem (vertexRecordAddress width u.val (levelBase+1)))
    (hHighBase : st.scalar.core.ptrs 128=highBase) (hLevel : st.scalar.core.ptrs 89=(levelBase : ℤ))
    (hOne : st.scalar.core.regs 31=1) (hTheta : st.scalar.core.regs 47=theta)
    (v : Fin n) (hv : v ∈ domain) (hVertex : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hExtMass : extObj.mass ≤ N) (hHighMass : highObj.mass ≤ N) (hCap : R < length) (hPow : N < 2^R),
∃ steps out,
    ∃ newExt : RankQueueObject out.scalar.integerMemory extBase length (out.scalar.core.ptrs 20) floor,
    ∃ newHigh : RankQueueObject out.scalar.integerMemory highBase length (out.scalar.core.ptrs 20) floor,
      MachineEval m g ω queuePairRefreshCode st steps out ∧ steps ≤ 42*R+56*width+203 ∧
      newExt.keys=(if v.val ∈ extValid then insert v.val extObj.keys else extObj.keys) ∧
      newHigh.keys=(if v.val ∈ highValid then insert v.val highObj.keys else highObj.keys) ∧
      newExt.mass ≤ extObj.mass+1 ∧ newHigh.mass ≤ highObj.mass+1 ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase (levelBase+3) q domain extValid newExt.keys ∧
      newHigh.keys ⊆ domain.image Fin.val ∧ QueuedFlags out.scalar.integerMemory width (levelBase+6) domain newHigh.keys ∧
      Disjoint newHigh.cells newExt.cells ∧ st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 ∧
      out.scalar.core.ptrs 20 ≤ st.scalar.core.ptrs 20+6 ∧
      (∀ z ∈ newExt.cells ∪ newHigh.cells, z < st.scalar.core.ptrs 20 → z ∈ extObj.cells ∪ highObj.cells) ∧
      (∀ other : Fin n, ∀ field < width, field ≠ levelBase+3 → field ≠ levelBase+6 →
        out.scalar.integerMemory (vertexRecordAddress width other.val field)=st.scalar.integerMemory (vertexRecordAddress width other.val field)) ∧
      (∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 → z ∉ extObj.cells ∪ highObj.cells → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width v.val (levelBase+4))
        (if st.scalar.integerMemory (vertexRecordAddress width v.val (levelBase+2))=0 then 0 else
          if 3*theta*(st.scalar.integerMemory (vertexRecordAddress width v.val 0) : ℝ) ≤
            st.scalar.core.mem (vertexRecordAddress width v.val (levelBase+1)) then 1 else 0) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧
      out.scalar.halted=false ∧ out.scalar.core.ptrs 0=0 := by
  exact @NearlyOptimalPPR.Computation.queue_pair_refresh_exec
