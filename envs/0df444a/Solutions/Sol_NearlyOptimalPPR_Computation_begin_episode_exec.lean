-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.begin_episode_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:29:11.392822+00:00
-- url     : https://prove2.me/submissions/24c658a3-51ef-47a1-9fdf-5e40ba202e9d

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

-- Proof module: Solutions.LevelHeaderRealFrom

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderRealFromCode_wellFormed (slot source : ℕ) : (levelHeaderRealFromCode slot source).wellFormed := by
  refine ⟨?_,levelHeaderRealStoreCode_wellFormed slot⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
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

lemma levelHeaderIntegerSetCode_wellFormed (slot : ℕ) (value : ℤ) :
    (levelHeaderIntegerSetCode slot value).wellFormed := by
  refine ⟨?_,levelHeaderIntegerStoreCode_wellFormed slot⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma levelHeaderRealZeroCode_wellFormed (slot : ℕ) : (levelHeaderRealZeroCode slot).wellFormed := by
  refine ⟨?_,levelHeaderRealStoreCode_wellFormed slot⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨0,by norm_num⟩

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
lemma levelHeaderIntegerSetsCode_wellFormed (assignments : List (ℕ × ℤ)) :
    (levelHeaderIntegerSetsCode assignments).wellFormed := by
  induction assignments with
  | nil => trivial
  | cons kv rest ih => exact ⟨levelHeaderIntegerSetCode_wellFormed kv.1 kv.2,ih⟩

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

lemma frameRankLoadCode_wellFormed : frameRankLoadCode.wellFormed := by
  simp [frameRankLoadCode,frameRankLoadInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.GraphCacheRead

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexFieldReadCode_wellFormed (field destination : ℕ) : (vertexFieldReadCode field destination).wellFormed := by
  simp [vertexFieldReadCode,vertexIntegerLoadCode,MachineCode.wellFormed,vertexAddressCode_wellFormed,
    coreCode,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorEligibility

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma exteriorEligibilityCode_wellFormed : exteriorEligibilityCode.wellFormed := by
  simp [exteriorEligibilityCode,exteriorInactiveCode,exteriorDegreeProductCode,linearCode,
    exteriorDegreeProductInstructions,exteriorActiveOffsetRoutine,exteriorResidualOffsetRoutine,
    PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,sequenceCode,vertexIntegerLoadCode,
    vertexRealLoadCode,vertexAddressCode_wellFormed,vertexFieldReadCode_wellFormed,
    MachineCode.wellFormed,RealOperation.instruction,coreCode,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨0,by norm_num⟩

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

def ofMemory {n : ℕ} {g : InputGraph n} {logical : RecursiveState n} {j width length : ℕ}
    {machine : MachineState} {floor : ℤ} (f : RecursiveFrameMemory g logical j width length machine floor) :
    FramePendingKeys g logical j width length machine floor := {
  N := f.N
  q := f.q
  Q := f.Q
  W := f.W
  theta := f.theta
  block := f.block
  pc := f.pc
  openBudget := f.openBudget
  needFull := f.needFull
  children := f.children
  reference := f.reference
  residual := f.residual
  activeFlags := f.activeFlags
  cacheFlags := f.cacheFlags
  activeVertices := f.activeVertices
  activeFoot := f.activeFoot
  activeRep := f.activeRep
  activeNodup := f.activeNodup
  activeSet := f.activeSet
  activeCount := f.activeCount
  activeVolume := f.activeVolume
  activeBelow := f.activeBelow
  activeAbove := f.activeAbove
  cacheVertices := f.cacheVertices
  cacheFoot := f.cacheFoot
  cacheRep := f.cacheRep
  cacheNodup := f.cacheNodup
  cacheSet := f.cacheSet
  cacheCount := f.cacheCount
  cacheVolume := f.cacheVolume
  cacheBelow := f.cacheBelow
  cacheAbove := f.cacheAbove
  exteriorBase := f.exteriorBase
  highBase := f.highBase
  exteriorPointer := f.exteriorPointer
  highPointer := f.highPointer
  exteriorObject := f.exteriorObject
  highObject := f.highObject
  exteriorData := f.exteriorData
  virtualExcluded := f.virtualExcluded
  highFlags := f.highFlags
  highDomain := f.highDomain
  highValid := f.highValid
}

def finish {n : ℕ} {g : InputGraph n} {logical : RecursiveState n} {j width length : ℕ}
    {machine : MachineState} {floor : ℤ} (f : FramePendingKeys g logical j width length machine floor)
    (hExt : (logical.frames j).exterior.image Fin.val ⊆ f.exteriorObject.keys)
    (hBool : HighBooleanRecords machine.scalar.integerMemory machine.scalar.core.mem width (16*(j+1))
      (logical.frames j).theta (parentDomain logical j))
    (hHigh : (logical.frames j).high.image Fin.val ⊆ f.highObject.keys) :
    RecursiveFrameMemory g logical j width length machine floor := {
  N := f.N
  q := f.q
  Q := f.Q
  W := f.W
  theta := f.theta
  block := f.block
  pc := f.pc
  openBudget := f.openBudget
  needFull := f.needFull
  children := f.children
  reference := f.reference
  residual := f.residual
  activeFlags := f.activeFlags
  cacheFlags := f.cacheFlags
  activeVertices := f.activeVertices
  activeFoot := f.activeFoot
  activeRep := f.activeRep
  activeNodup := f.activeNodup
  activeSet := f.activeSet
  activeCount := f.activeCount
  activeVolume := f.activeVolume
  activeBelow := f.activeBelow
  activeAbove := f.activeAbove
  cacheVertices := f.cacheVertices
  cacheFoot := f.cacheFoot
  cacheRep := f.cacheRep
  cacheNodup := f.cacheNodup
  cacheSet := f.cacheSet
  cacheCount := f.cacheCount
  cacheVolume := f.cacheVolume
  cacheBelow := f.cacheBelow
  cacheAbove := f.cacheAbove
  exteriorBase := f.exteriorBase
  highBase := f.highBase
  exteriorPointer := f.exteriorPointer
  highPointer := f.highPointer
  exteriorObject := f.exteriorObject
  highObject := f.highObject
  exteriorData := f.exteriorData
  exteriorCover := hExt
  highBoolean := hBool
  virtualExcluded := f.virtualExcluded
  highFlags := f.highFlags
  highDomain := f.highDomain
  highValid := f.highValid
  highCover := hHigh
}

end FramePendingKeys
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MemoryPredicateDecidable

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
instance integerReadOnlyDecidable (i : Instruction) : Decidable (integerReadOnly i) := by
  cases i with
  | scalar i => cases i <;> simp [integerReadOnly] <;> infer_instance
  | solve r => exact isTrue trivial
  | emit a b => exact isTrue trivial
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

-- Proof module: Solutions.HeapInsertExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma heapInsertCode_wellFormed : heapInsertCode.wellFormed := by
  refine ⟨heapNodeAllocCode_wellFormed,?_,heapCarryCode_wellFormed⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.FlaggedHeapInsert

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma flaggedHeapInsertCode_wellFormed : flaggedHeapInsertCode.wellFormed := by
  refine ⟨?_,heapInsertCode_wellFormed,?_,vertexFlagSetCode_wellFormed⟩
  all_goals simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

lemma queuedFlagReadCode_wellFormed : queuedFlagReadCode.wellFormed := by
  simp [queuedFlagReadCode,vertexIntegerLoadCode,vertexAddressCode_wellFormed,
    coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

lemma queuedInsertCode_wellFormed : queuedInsertCode.wellFormed :=
  ⟨queuedFlagReadCode_wellFormed,flaggedHeapInsertCode_wellFormed,trivial⟩

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

-- Proof module: Solutions.ExteriorQueueRefreshCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma exteriorQueueRefreshCode_wellFormed : exteriorQueueRefreshCode.wellFormed := by
  refine ⟨?_,exteriorEligibilityCode_wellFormed,trivial,queuedInsertCode_wellFormed⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

lemma levelHeaderIntegerToCode_wellFormed (slot target : ℕ) : (levelHeaderIntegerToCode slot target).wellFormed := by
  refine ⟨levelHeaderIntegerLoadCode_wellFormed slot,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma levelHeaderRealToCode_wellFormed (slot target : ℕ) : (levelHeaderRealToCode slot target).wellFormed := by
  refine ⟨levelHeaderRealLoadCode_wellFormed slot,?_⟩
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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameQueueContext

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameQueueContextCode_wellFormed (queueSlot scalarSlot : ℕ) : (frameQueueContextCode queueSlot scalarSlot).wellFormed :=
  ⟨levelContextCode_wellFormed,levelHeaderIntegerToCode_wellFormed queueSlot 13,
    frameRankLoadCode_wellFormed,levelHeaderRealToCode_wellFormed scalarSlot 20⟩
lemma exteriorFrameContextCode_wellFormed : exteriorFrameContextCode.wellFormed := by
  refine ⟨frameQueueContextCode_wellFormed 7 1,?_⟩
  simp [levelVertexOffsetCode,levelVertexOffsetInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
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

-- Proof module: Solutions.RecursiveFrameScopedTransport

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def RecursiveFrameMemory.scoped_frame {n : ℕ} {g : InputGraph n} {logical : RecursiveState n}
    {j width length : ℕ} {st out : MachineState} {floor : ℤ}
    (f : RecursiveFrameMemory g logical j width length st floor)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hHeaderI : ∀ slot < 32, out.scalar.integerMemory (levelHeaderAddress j slot)=st.scalar.integerMemory (levelHeaderAddress j slot))
    (hHeaderR : ∀ slot < 32, out.scalar.core.mem (levelHeaderAddress j slot)=st.scalar.core.mem (levelHeaderAddress j slot))
    (hFieldsI : ∀ v ∈ parentDomain logical j, ∀ field < 16*(j+1)+7, (field=0 ∨ 16*(j+1) ≤ field) →
      out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field))
    (hFieldsR : ∀ v ∈ parentDomain logical j, ∀ field < 16*(j+1)+7, (field=0 ∨ 16*(j+1) ≤ field) →
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
    exteriorCover := f.exteriorCover
    highBoolean := ?_
    virtualExcluded := fun v hv => (hFieldsI v hv _ (by omega) (by omega)).trans (f.virtualExcluded v hv)
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
      rw [hFieldsI v hv _ (by omega) (by omega)]
      exact f.exteriorData.flags v hv
    · intro v hv
      rw [hFieldsI v hv _ (by omega) (by omega)]
      exact f.exteriorData.activeNonnegative v hv
    · intro v hv
      rw [hFieldsI v hv _ (by omega) (by omega),hFieldsI v hv 0 (by omega) (by omega),hFieldsR v hv _ (by omega) (by omega)]
      exact f.exteriorData.eligibility v hv
  · intro v hv
    rw [hFieldsR v hv _ (by omega) (by omega),hFieldsI v hv _ (by omega) (by omega),hFieldsI v hv 0 (by omega) (by omega),hFieldsR v hv _ (by omega) (by omega)]
    exact f.highBoolean v hv
  · intro v hv
    rw [hFieldsI v hv _ (by omega) (by omega)]
    exact f.highFlags v hv
  · intro v hv
    rw [hFieldsI v hv _ (by omega) (by omega),hFieldsI v hv 0 (by omega) (by omega),hFieldsR v hv _ (by omega) (by omega)]
    exact f.highValid v hv

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

-- Proof module: Solutions.GraphCacheQueueFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma GraphCache.queue_frame {n : ℕ} (g : InputGraph n) {I J : ℤ → ℤ} {width : ℕ}
    {stored : Finset (Fin n)} {free nextFree : ℤ} (cache : GraphCache g I width stored free)
    (Q : Finset ℤ) (hSep : Disjoint (cachedRowCells g I width stored) Q) (hFree : free ≤ nextFree)
    (hMeta : ∀ v : Fin n, ∀ field < 3, J (vertexRecordAddress width v.val field)=I (vertexRecordAddress width v.val field))
    (hFrame : ∀ z, 0 ≤ z → z < free → z ∉ Q → J z=I z) :
    GraphCache g J width stored nextFree := by
  apply GraphCache.mono_free (next:=nextFree) (hle:=hFree)
  apply cache.frame g I J width stored free hMeta
  intro v hv i hi
  have hCell : I (vertexRecordAddress width v.val 1)+(i : ℤ) ∈ cachedRowCells g I width stored := by
    apply Finset.mem_biUnion.mpr
    refine ⟨v,hv,?_⟩
    exact (mem_arrayCells _ _ _).mpr ⟨i,hi,rfl⟩
  have hp := cache.basePositive v hv
  have hi0 := Int.natCast_nonneg i
  exact hFrame _ (by omega) (cache.belowFree v hv i hi)
    (fun hq => Finset.disjoint_left.mp hSep hCell hq)

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

-- Proof module: Solutions.CompilerBeginEpisodeSource

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_begin_top {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n) :
    (compilerBeginEpisode m g logical).top=logical.top := rfl

lemma compiler_begin_active {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n) (j : ℕ) :
    ((compilerBeginEpisode m g logical).frames j).active=(logical.frames j).active := by
  classical
  by_cases hj : j=logical.top <;> simp [compilerBeginEpisode,changeFrame,debit,hj]

lemma compiler_begin_domain {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n) (j : ℕ) :
    parentDomain (compilerBeginEpisode m g logical) j=parentDomain logical j := by
  unfold parentDomain
  split_ifs
  · rfl
  · exact compiler_begin_active m g logical (j-1)

lemma compiler_begin_selected {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n) :
    let f := logical.frames logical.top
    let Q := max (∑ v ∈ f.active, f.residual v) (f.q*(f.block : ℝ))
    let theta := Q/(f.block : ℝ)
    (compilerBeginEpisode m g logical).frames logical.top={f with Q := Q,W := 0,theta := theta,openBudget := true,childrenThisEpisode := 0,cache := ∅,high := f.active.filter (fun v => 3*theta*LocalPush.deg g.graph v ≤ f.residual v),pc := if f.needFull then .fullSolve else .normalize} := by
  simp only [compilerBeginEpisode,changeFrame,debit,Function.update_self]

lemma compiler_begin_other {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n) (j : ℕ) (hj : j ≠ logical.top) :
    (compilerBeginEpisode m g logical).frames j=logical.frames j := by
  simp only [compilerBeginEpisode,changeFrame,debit,Function.update_of_ne hj]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheRowExtension

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma cached_row_cells_congr {n : ℕ} (g : InputGraph n) (stored : Finset (Fin n)) (width : ℕ) (I J : ℤ → ℤ)
    (h : ∀ u ∈ stored, J (vertexRecordAddress width u.val 1)=I (vertexRecordAddress width u.val 1)) :
    cachedRowCells g J width stored=cachedRowCells g I width stored := by
  unfold cachedRowCells
  apply Finset.biUnion_congr rfl
  intro u hu
  rw [h u hu]

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

def ofMemory {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {machine : MachineState}
    (f : RecursiveMachineMemory g s α ε ell length logical machine) :
    MachinePendingKeys g s α ε ell length logical machine := {
  zero := f.zero
  top := f.top
  width := f.width
  alphaRegister := f.alphaRegister
  one := f.one
  alphaMemory := f.alphaMemory
  epsilonMemory := f.epsilonMemory
  depthMemory := f.depthMemory
  lengthMemory := f.lengthMemory
  seedMemory := f.seedMemory
  allocator := f.allocator
  potential := f.potential
  seedMarker := f.seedMarker
  boundary := f.boundary
  graphCache := f.graphCache
  rowAbove := f.rowAbove
  knownDegree := f.knownDegree
  unknownDegree := f.unknownDegree
  frames := fun j hj => FramePendingKeys.ofMemory (f.frames j hj)
  pieceSeparation := f.pieceSeparation
  frameSeparation := f.frameSeparation
  cacheSeparation := f.cacheSeparation
  output := f.output
}

def finish {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {machine : MachineState}
    (f : MachinePendingKeys g s α ε ell length logical machine)
    (hExt : ∀ j, ∀ hj : j ≤ logical.top, (logical.frames j).exterior.image Fin.val ⊆ (f.frames j hj).exteriorObject.keys)
    (hBool : ∀ j ≤ logical.top, HighBooleanRecords machine.scalar.integerMemory machine.scalar.core.mem (16*(ell+3)) (16*(j+1))
      (logical.frames j).theta (parentDomain logical j))
    (hHigh : ∀ j, ∀ hj : j ≤ logical.top, (logical.frames j).high.image Fin.val ⊆ (f.frames j hj).highObject.keys) :
    RecursiveMachineMemory g s α ε ell length logical machine := {
  zero := f.zero
  top := f.top
  width := f.width
  alphaRegister := f.alphaRegister
  one := f.one
  alphaMemory := f.alphaMemory
  epsilonMemory := f.epsilonMemory
  depthMemory := f.depthMemory
  lengthMemory := f.lengthMemory
  seedMemory := f.seedMemory
  allocator := f.allocator
  potential := f.potential
  seedMarker := f.seedMarker
  boundary := f.boundary
  graphCache := f.graphCache
  rowAbove := f.rowAbove
  knownDegree := f.knownDegree
  unknownDegree := f.unknownDegree
  frames := fun j hj => (f.frames j hj).finish (hExt j hj) (hBool j hj) (hHigh j hj)
  pieceSeparation := f.pieceSeparation
  frameSeparation := f.frameSeparation
  cacheSeparation := f.cacheSeparation
  output := f.output
}

end MachinePendingKeys
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

lemma vertex_memory_update_other_vertex {β : Type} (M : ℤ → β) (width vertex other offset field : ℕ)
    (value : β) (ho : offset < width) (hf : field < width) (hne : other ≠ vertex) :
    Function.update M (vertexRecordAddress width vertex offset) value (vertexRecordAddress width other field)=
      M (vertexRecordAddress width other field) := by
  have hn : vertexRecordAddress width other field ≠ vertexRecordAddress width vertex offset := by
    intro he
    exact hne (vertexRecordAddress_injective width other vertex field offset hf ho he).1
  simp only [Function.update_of_ne hn]

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingNumericFrames

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma MachinePendingKeys.degree_frame {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st out : MachineState}
    (old : MachinePendingKeys g s α ε ell length logical st)
    (next : MachinePendingKeys g s α ε ell length logical out) (v : Fin n) :
    out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)=
      st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0) := by
  classical
  by_cases hv : v ∈ recursiveDegreeDomain g s logical
  · exact (next.knownDegree v hv).trans (old.knownDegree v hv).symm
  · exact (next.unknownDegree v hv).trans (old.unknownDegree v hv).symm

lemma MachinePendingKeys.active_frame {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st out : MachineState}
    (old : MachinePendingKeys g s α ε ell length logical st)
    (next : MachinePendingKeys g s α ε ell length logical out) (j : ℕ) (hj : j ≤ logical.top)
    (v : Fin n) (hv : v ∈ parentDomain logical j) :
    out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+2))=
      st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+2)) :=
  ((next.frames j hj).activeFlags v hv).trans ((old.frames j hj).activeFlags v hv).symm

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ScalarLevelLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelRealMemoryFold (update : ℕ → (ℤ → ℝ) → (ℤ → ℝ)) : ℕ → ℕ → (ℤ → ℝ) → (ℤ → ℝ)
  | _,0,R => R
  | i,k+1,R => levelRealMemoryFold update (i+1) k (update i R)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelMemoryProperties

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma level_memory_frame (update : ℕ → (ℤ → ℝ) → (ℤ → ℝ)) (limit : ℕ) (z : ℤ)
    (hStep : ∀ i < limit, ∀ R, update i R z=R z) (count : ℕ) :
    ∀ (start : ℕ) (R : ℤ → ℝ), start+count ≤ limit →
      levelRealMemoryFold update start count R z=R z := by
  induction count with
  | zero => intros; rfl
  | succ count ih =>
    intro start R hRange
    rw [levelRealMemoryFold,ih (start+1) (update start R) (by omega),hStep start (by omega)]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PayloadLevelLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelPayloadFold {Payload : Type} (update : ℕ → Payload → Payload) : ℕ → ℕ → Payload → Payload
  | _,0,payload => payload
  | i,k+1,payload => levelPayloadFold update (i+1) k (update i payload)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PayloadFoldProperties

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma level_payload_overwrite {Payload Value : Type} (update : ℕ → Payload → Payload)
    (hit : ℕ → Prop) [DecidablePred hit] (limit : ℕ) (eval : Payload → Value) (value : Value)
    (hStep : ∀ i < limit, ∀ payload, eval (update i payload)=if hit i then value else eval payload) (count : ℕ) :
    ∀ (start : ℕ) (payload : Payload), start+count ≤ limit →
      eval (levelPayloadFold update start count payload)=
        @ite Value (∃ j, start ≤ j ∧ j < start+count ∧ hit j) (Classical.propDecidable _) value (eval payload) := by
  classical
  induction count with
  | zero =>
    intro start payload hRange
    simp only [levelPayloadFold,Nat.add_zero]
    rw [if_neg (by rintro ⟨j,hj,hj',hh⟩; omega)]
  | succ count ih =>
    intro start payload hRange
    rw [levelPayloadFold,ih (start+1) (update start payload) (by omega),hStep start (by omega)]
    have hSplit : (∃ j, start ≤ j ∧ j < start+(count+1) ∧ hit j) ↔
        hit start ∨ ∃ j, start+1 ≤ j ∧ j < start+1+count ∧ hit j := by
      constructor
      · rintro ⟨j,hj,hj',hh⟩
        by_cases he : j=start
        · exact Or.inl (he ▸ hh)
        · exact Or.inr ⟨j,by omega,by omega,hh⟩
      · rintro (hh|⟨j,hj,hj',hh⟩)
        · exact ⟨start,by omega,by omega,hh⟩
        · exact ⟨j,by omega,by omega,hh⟩
    rw [hSplit]
    by_cases ht : ∃ j, start+1 ≤ j ∧ j < start+1+count ∧ hit j
    · rw [if_pos ht,if_pos (Or.inr ht)]
    · rw [if_neg ht]
      by_cases hs : hit start
      · rw [if_pos hs,if_pos (Or.inl hs)]
      · rw [if_neg hs,if_neg (fun h => h.elim hs ht)]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingBooleanMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def sourceHighBooleanValue {n : ℕ} (logical : RecursiveState n) (j : ℕ) (v : Fin n) (degree : ℤ) : ℝ :=
  if v ∈ (logical.frames j).active then
    if 3*(logical.frames j).theta*(degree : ℝ) ≤ (logical.frames j).residual v then 1 else 0
  else 0

def pendingBooleanMemoryUpdate {n : ℕ} (logical : RecursiveState n) (width : ℕ) (v : Fin n) (degree : ℤ)
    (j : ℕ) (R : ℤ → ℝ) : ℤ → ℝ :=
  if v ∈ parentDomain logical j then
    Function.update R (vertexRecordAddress width v.val (16*(j+1)+4)) (sourceHighBooleanValue logical j v degree)
  else R

lemma MachinePendingKeys.high_boolean_value {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st : MachineState}
    (pm : MachinePendingKeys g s α ε ell length logical st) (j : ℕ) (hj : j ≤ logical.top)
    (v : Fin n) (hv : v ∈ parentDomain logical j) (degree : ℤ)
    (hDegree : st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)=degree) :
    (if st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+2))=0 then (0 : ℝ) else
      if 3*(logical.frames j).theta*(st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0) : ℝ) ≤
        st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+1)) then 1 else 0)=
      sourceHighBooleanValue logical j v degree := by
  rw [(pm.frames j hj).activeFlags v hv,(pm.frames j hj).residual v hv,hDegree]
  by_cases ha : v ∈ (logical.frames j).active <;> simp [ha,sourceHighBooleanValue]

lemma MachinePendingKeys.boolean_memory_update_eq {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st : MachineState}
    (pm : MachinePendingKeys g s α ε ell length logical st) (j : ℕ) (hj : j ≤ logical.top)
    (v : Fin n) (degree : ℤ) (hDegree : st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)=degree) :
    (if v ∈ parentDomain logical j then
      Function.update st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+4))
        (if st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+2))=0 then 0 else
          if 3*(logical.frames j).theta*(st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0) : ℝ) ≤
            st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+1)) then 1 else 0)
      else st.scalar.core.mem)=pendingBooleanMemoryUpdate logical (16*(ell+3)) v degree j st.scalar.core.mem := by
  unfold pendingBooleanMemoryUpdate
  by_cases hv : v ∈ parentDomain logical j
  · rw [if_pos hv,if_pos hv,pm.high_boolean_value j hj v hv degree hDegree]
  · rw [if_neg hv,if_neg hv]

lemma level_real_payload_eq (update : ℕ → (ℤ → ℝ) → (ℤ → ℝ)) (count : ℕ) :
    ∀ start R, levelRealMemoryFold update start count R=levelPayloadFold update start count R := by
  induction count with
  | zero => intros; rfl
  | succ count ih =>
    intro start R
    exact ih (start+1) (update start R)

lemma pending_boolean_fold_other_vertex {n : ℕ} (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (v w : Fin n) (hne : w ≠ v) (degree : ℤ) (field : ℕ)
    (hf : field < 16*(ell+3)) (R : ℤ → ℝ) :
    levelRealMemoryFold (pendingBooleanMemoryUpdate logical (16*(ell+3)) v degree) 0 (logical.top+1) R
      (vertexRecordAddress (16*(ell+3)) w.val field)=R (vertexRecordAddress (16*(ell+3)) w.val field) := by
  apply level_memory_frame (limit:=logical.top+1)
  · intro i hi R'
    unfold pendingBooleanMemoryUpdate
    split_ifs
    · exact vertex_memory_update_other_vertex R' (16*(ell+3)) v.val w.val (16*(i+1)+4) field _
        (by omega) hf (fun h => hne (Fin.ext h))
    · rfl
  · omega

lemma pending_boolean_fold_at {n : ℕ} (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (v : Fin n) (degree : ℤ) (j : ℕ) (hj : j ≤ logical.top) (R : ℤ → ℝ) :
    levelRealMemoryFold (pendingBooleanMemoryUpdate logical (16*(ell+3)) v degree) 0 (logical.top+1) R
      (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+4))=
      (if v ∈ parentDomain logical j then sourceHighBooleanValue logical j v degree else
        R (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+4))) := by
  classical
  rw [level_real_payload_eq]
  have h := level_payload_overwrite (pendingBooleanMemoryUpdate logical (16*(ell+3)) v degree)
    (fun i => i=j ∧ v ∈ parentDomain logical j) (logical.top+1)
    (fun R' => R' (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+4)))
    (sourceHighBooleanValue logical j v degree)
    (by
      intro i hi R'
      by_cases he : i=j
      · subst i
        unfold pendingBooleanMemoryUpdate
        by_cases hv : v ∈ parentDomain logical j <;> simp [hv]
      · have hn : vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+4) ≠
          vertexRecordAddress (16*(ell+3)) v.val (16*(i+1)+4) := by
          intro h
          have := (vertexRecordAddress_injective (16*(ell+3)) v.val v.val (16*(j+1)+4) (16*(i+1)+4)
            (by omega) (by omega) h).2
          omega
        unfold pendingBooleanMemoryUpdate
        split_ifs <;> (first | rfl | simp_all [Function.update_of_ne hn]))
    (logical.top+1) 0 R (by omega)
  have hExist : (∃ i, 0 ≤ i ∧ i < 0+(logical.top+1) ∧ i=j ∧ v ∈ parentDomain logical j) ↔
      v ∈ parentDomain logical j := by
    constructor
    · rintro ⟨i,hi0,hi,hij,hv⟩
      exact hv
    · intro hv
      exact ⟨j,Nat.zero_le _,by omega,rfl,hv⟩
  simpa only [hExist] using h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingBooleanRestoration

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma MachinePendingKeys.boolean_refresh_complete {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st out : MachineState}
    (old : MachinePendingKeys g s α ε ell length logical st)
    (next : MachinePendingKeys g s α ε ell length logical out) (hDepth : logical.top ≤ ell)
    (visited : Finset (Fin n)) (v : Fin n)
    (hOld : ∀ j ≤ logical.top, HighBooleanRecords st.scalar.integerMemory st.scalar.core.mem (16*(ell+3)) (16*(j+1))
      (logical.frames j).theta (parentDomain logical j ∩ visited))
    (hR : out.scalar.core.mem=levelRealMemoryFold
      (pendingBooleanMemoryUpdate logical (16*(ell+3)) v (st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)))
      0 (logical.top+1) st.scalar.core.mem) :
    ∀ j ≤ logical.top, HighBooleanRecords out.scalar.integerMemory out.scalar.core.mem (16*(ell+3)) (16*(j+1))
      (logical.frames j).theta (parentDomain logical j ∩ insert v visited) := by
  intro j hj u hu
  have huD := (Finset.mem_inter.mp hu).1
  by_cases huv : u=v
  · subst u
    calc
      out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+4))=
          sourceHighBooleanValue logical j v (st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)) := by
        rw [hR,pending_boolean_fold_at logical ell hDepth v _ j hj,if_pos huD]
      _ = _ := (next.high_boolean_value j hj v huD _ (old.degree_frame next v)).symm
  · have hVisited : u ∈ visited := (Finset.mem_insert.mp (Finset.mem_inter.mp hu).2).resolve_left huv
    have hBit : out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+4))=
        st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+4)) := by
      rw [hR]
      exact pending_boolean_fold_other_vertex logical ell hDepth v u huv _ _ (by omega) _
    rw [hBit,old.active_frame next j hj u huD,old.degree_frame next u,
      ((next.frames j hj).residual u huD).trans ((old.frames j hj).residual u huD).symm]
    exact hOld j hj u (Finset.mem_inter.mpr ⟨huD,hVisited⟩)

end
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

lemma pending_queueMass_exchange {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (st out : MachineState)
    (old : MachinePendingKeys g s α ε ell length logical st)
    (next : MachinePendingKeys g s α ε ell length logical out)
    (i : ℕ) (hi : i ≤ logical.top) (before after : ℕ)
    (hSame : ∀ j hj, j ≠ i → (next.frames j hj).queueMass=(old.frames j hj).queueMass)
    (hChange : (next.frames i hi).queueMass+before=(old.frames i hi).queueMass+after) :
    next.queueMass+before=old.queueMass+after := by
  have hPoint (j : ℕ) (hj : j ≤ logical.top) :
      (if h : j ≤ logical.top then (next.frames j h).queueMass else 0)+(if j=i then before else 0)=
      (if h : j ≤ logical.top then (old.frames j h).queueMass else 0)+(if j=i then after else 0) := by
    rw [dif_pos hj,dif_pos hj]
    by_cases he : j=i
    · subst j; simpa using hChange
    · simp only [if_neg he,add_zero]
      exact hSame j hj he
  have hSum := Finset.sum_congr (s₁:=Finset.range (logical.top+1)) (s₂:=Finset.range (logical.top+1)) rfl
    (fun j hj => hPoint j (by have := Finset.mem_range.mp hj; omega))
  have hBefore : (∑ j ∈ Finset.range (logical.top+1), if j=i then before else 0)=before := by
    simp [Finset.mem_range,show i < logical.top+1 by omega]
  have hAfter : (∑ j ∈ Finset.range (logical.top+1), if j=i then after else 0)=after := by
    simp [Finset.mem_range,show i < logical.top+1 by omega]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,hBefore,hAfter] at hSum
  exact hSum

lemma MachinePendingKeys.frame_mass_le_total {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {machine : MachineState}
    (memory : MachinePendingKeys g s α ε ell length logical machine) (i : ℕ) (hi : i ≤ logical.top) :
    (memory.frames i hi).queueMass ≤ memory.queueMass := by
  have hMem : i ∈ Finset.range (logical.top+1) := Finset.mem_range.mpr (by omega)
  have hSum := Finset.single_le_sum (f:=fun j => if hj : j ≤ logical.top then (memory.frames j hj).queueMass else 0)
    (fun j hj => Nat.zero_le _) hMem
  change Nat.le _ _ at hSum
  change Nat.le _ _
  simpa only [MachinePendingKeys.queueMass,dif_pos hi] using hSum

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

-- Proof module: Solutions.FramePendingOwnership

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma FramePendingKeys.owned_above {n : ℕ} {g : InputGraph n} {logical : RecursiveState n}
    {j width length : ℕ} {machine : MachineState} {floor : ℤ}
    (f : FramePendingKeys g logical j width length machine floor) : ∀ z ∈ f.owned, floor ≤ z := by
  intro z hz
  rcases Finset.mem_union.mp hz with habc|hd
  · rcases Finset.mem_union.mp habc with hab|hc
    · rcases Finset.mem_union.mp hab with ha|hb
      · exact f.activeAbove z ha
      · exact f.cacheAbove z hb
    · exact f.exteriorObject.above z hc
  · exact f.highObject.above z hd

lemma FramePendingKeys.owned_below {n : ℕ} {g : InputGraph n} {logical : RecursiveState n}
    {j width length : ℕ} {machine : MachineState} {floor : ℤ}
    (f : FramePendingKeys g logical j width length machine floor) : ∀ z ∈ f.owned, z < machine.scalar.core.ptrs 20 := by
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

lemma after_vertex {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState} {visited : Finset (Fin n)}
    {old : MachinePendingKeys g s α ε ell length logical st}
    {next : MachinePendingKeys g s α ε ell length logical out}
    (inv : PendingVisitedKeys old visited) (hDepth : logical.top ≤ ell) (v : Fin n)
    (hExt : ∀ j, ∀ hj : j ≤ logical.top, (next.frames j hj).exteriorObject.keys=
      if v ∈ (logical.frames j).exterior then insert v.val (old.frames j hj).exteriorObject.keys else (old.frames j hj).exteriorObject.keys)
    (hHigh : ∀ j, ∀ hj : j ≤ logical.top, (next.frames j hj).highObject.keys=
      if v ∈ (logical.frames j).high then insert v.val (old.frames j hj).highObject.keys else (old.frames j hj).highObject.keys)
    (hR : out.scalar.core.mem=levelRealMemoryFold
      (pendingBooleanMemoryUpdate logical (16*(ell+3)) v (st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)))
      0 (logical.top+1) st.scalar.core.mem) : PendingVisitedKeys next (insert v visited) := by
  classical
  refine ⟨old.boolean_refresh_complete next hDepth visited v inv.boolean hR,?_,?_⟩
  · intro j hj u hu hKey
    rw [hExt j hj]
    rcases Finset.mem_insert.mp hu with he|hu
    · subst u
      rw [if_pos hKey]
      exact Finset.mem_insert_self _ _
    · split_ifs
      · exact Finset.mem_insert_of_mem (inv.exterior j hj u hu hKey)
      · exact inv.exterior j hj u hu hKey
  · intro j hj u hu hKey
    rw [hHigh j hj]
    rcases Finset.mem_insert.mp hu with he|hu
    · subst u
      rw [if_pos hKey]
      exact Finset.mem_insert_self _ _
    · split_ifs
      · exact Finset.mem_insert_of_mem (inv.high j hj u hu hKey)
      · exact inv.high j hj u hu hKey

def finish {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} {visited : Finset (Fin n)}
    {pm : MachinePendingKeys g s α ε ell length logical st} (inv : PendingVisitedKeys pm visited)
    (hAll : visited=Finset.univ) : RecursiveMachineMemory g s α ε ell length logical st := by
  refine pm.finish ?_ ?_ ?_
  · intro j hj k hk
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
    exact inv.exterior j hj v (by rw [hAll]; simp) hv
  · intro j hj v hv
    exact inv.boolean j hj v (Finset.mem_inter.mpr ⟨hv,by rw [hAll]; simp⟩)
  · intro j hj k hk
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
    exact inv.high j hj v (by rw [hAll]; simp) hv

lemma finish_frame {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} {visited : Finset (Fin n)}
    {pm : MachinePendingKeys g s α ε ell length logical st} (inv : PendingVisitedKeys pm visited)
    (hAll : visited=Finset.univ) : PendingIntegerFrame pm (MachinePendingKeys.ofMemory (inv.finish hAll)) := by
  refine ⟨le_rfl,?_,by intros; rfl,by intros; rfl⟩
  intros i hi z hz hBelow
  exact hz

lemma finish_mass {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} {visited : Finset (Fin n)}
    {pm : MachinePendingKeys g s α ε ell length logical st} (inv : PendingVisitedKeys pm visited)
    (hAll : visited=Finset.univ) : (inv.finish hAll).queueMass=pm.queueMass := rfl

end PendingVisitedKeys
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HighQueueContext

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma highQueueContextCode_wellFormed : highQueueContextCode.wellFormed := by
  simp [highQueueContextCode,linearCode,highQueueContextInstructions,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨0,by norm_num⟩

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

-- Proof module: Solutions.FramePendingQueueTransport

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def FramePendingKeys.queues_frame {n : ℕ} {g : InputGraph n} {logical : RecursiveState n}
    {j width length : ℕ} {st out : MachineState} {floor : ℤ}
    (f : FramePendingKeys g logical j width length st floor)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hHeaderI : ∀ slot < 32, out.scalar.integerMemory (levelHeaderAddress j slot)=st.scalar.integerMemory (levelHeaderAddress j slot))
    (hHeaderR : ∀ slot < 32, out.scalar.core.mem (levelHeaderAddress j slot)=st.scalar.core.mem (levelHeaderAddress j slot))
    (hFieldsI : ∀ v ∈ parentDomain logical j, ∀ field < 16*(j+1)+7, (field=0 ∨ 16*(j+1) ≤ field) →
      field ≠ 16*(j+1)+3 → field ≠ 16*(j+1)+6 →
      out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field))
    (hFieldsR : ∀ v ∈ parentDomain logical j, ∀ field < 16*(j+1)+7, (field=0 ∨ 16*(j+1) ≤ field) →
      field ≠ 16*(j+1)+4 →
      out.scalar.core.mem (vertexRecordAddress width v.val field)=st.scalar.core.mem (vertexRecordAddress width v.val field))
    (hOwned : ∀ z ∈ f.activeFoot ∪ f.cacheFoot, out.scalar.integerMemory z=st.scalar.integerMemory z)
    (newExt : RankQueueObject out.scalar.integerMemory f.exteriorBase length (out.scalar.core.ptrs 20) floor)
    (newHigh : RankQueueObject out.scalar.integerMemory f.highBase length (out.scalar.core.ptrs 20) floor)
    (hData : ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width (16*(j+1)) (16*(j+1)+3)
      (logical.frames j).q (parentDomain logical j) ((logical.frames j).exterior.image Fin.val) newExt.keys)
    (hHighFlags : QueuedFlags out.scalar.integerMemory width (16*(j+1)+6) (parentDomain logical j) newHigh.keys)
    (hHighDomain : newHigh.keys ⊆ (parentDomain logical j).image Fin.val) :
    FramePendingKeys g logical j width length out floor := by
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
    reference := fun v hv => (hFieldsR v hv _ (by omega) (by omega) (by omega)).trans (f.reference v hv)
    residual := fun v hv => (hFieldsR v hv _ (by omega) (by omega) (by omega)).trans (f.residual v hv)
    activeFlags := fun v hv => (hFieldsI v hv _ (by omega) (by omega) (by omega) (by omega)).trans (f.activeFlags v hv)
    cacheFlags := fun v hv => (hFieldsI v hv _ (by omega) (by omega) (by omega) (by omega)).trans (f.cacheFlags v hv)
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
    exteriorObject := newExt
    highObject := newHigh
    exteriorData := hData
    virtualExcluded := fun v hv => (hFieldsI v hv _ (by omega) (by omega) (by omega) (by omega)).trans (f.virtualExcluded v hv)
    highFlags := hHighFlags
    highDomain := hHighDomain
    highValid := ?_
  }
  · rw [hHeaderI 1 (by decide)]
    apply f.activeRep.frame
    intro z hz
    exact hOwned z (Finset.mem_union_left _ hz)
  · rw [hHeaderI 4 (by decide)]
    apply f.cacheRep.frame
    intro z hz
    exact hOwned z (Finset.mem_union_right _ hz)
  · intro v hv
    rw [hFieldsI v hv _ (by omega) (by omega) (by omega) (by omega),
      hFieldsI v hv 0 (by omega) (by omega) (by omega) (by omega),
      hFieldsR v hv _ (by omega) (by omega) (by omega)]
    exact f.highValid v hv

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueuePairSeparation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma queue_pair_separate (A C E H : Finset ℤ) (hp : [A,C,E,H].Pairwise Disjoint) :
    Disjoint (A ∪ C) (E ∪ H) := by
  have hAE : Disjoint A E := hp.rel_get_of_lt (a:=⟨0,by norm_num⟩) (b:=⟨2,by norm_num⟩) (by change (0 : ℕ)<2; omega)
  have hAH : Disjoint A H := hp.rel_get_of_lt (a:=⟨0,by norm_num⟩) (b:=⟨3,by norm_num⟩) (by change (0 : ℕ)<3; omega)
  have hCE : Disjoint C E := hp.rel_get_of_lt (a:=⟨1,by norm_num⟩) (b:=⟨2,by norm_num⟩) (by change (1 : ℕ)<2; omega)
  have hCH : Disjoint C H := hp.rel_get_of_lt (a:=⟨1,by norm_num⟩) (b:=⟨3,by norm_num⟩) (by change (1 : ℕ)<3; omega)
  exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨hAE,hAH⟩,Finset.disjoint_union_right.mpr ⟨hCE,hCH⟩⟩

lemma replace_queue_pair_pieces (A C E H E' H' : Finset ℤ) (free : ℤ)
    (hp : [A,C,E,H].Pairwise Disjoint) (hBelow : ∀ z ∈ A ∪ C, z < free)
    (hOld : ∀ z ∈ E' ∪ H', z < free → z ∈ E ∪ H) (hNew : Disjoint E' H') :
    [A,C,E',H'].Pairwise Disjoint := by
  have hAC : Disjoint A C := hp.rel_get_of_lt (a:=⟨0,by norm_num⟩) (b:=⟨1,by norm_num⟩) (by change (0 : ℕ)<1; omega)
  have hSep := queue_pair_separate A C E H hp
  have hA : Disjoint A (E ∪ H) := Finset.disjoint_union_left.mp hSep |>.1
  have hC : Disjoint C (E ∪ H) := Finset.disjoint_union_left.mp hSep |>.2
  have hAE := queue_disjoint_after_growth (fun z hz => hBelow z (Finset.mem_union_left _ hz)) hA
    (fun z hz hlt => hOld z (Finset.mem_union_left _ hz) hlt)
  have hAH := queue_disjoint_after_growth (fun z hz => hBelow z (Finset.mem_union_left _ hz)) hA
    (fun z hz hlt => hOld z (Finset.mem_union_right _ hz) hlt)
  have hCE := queue_disjoint_after_growth (fun z hz => hBelow z (Finset.mem_union_right _ hz)) hC
    (fun z hz hlt => hOld z (Finset.mem_union_left _ hz) hlt)
  have hCH := queue_disjoint_after_growth (fun z hz => hBelow z (Finset.mem_union_right _ hz)) hC
    (fun z hz hlt => hOld z (Finset.mem_union_right _ hz) hlt)
  simpa [List.pairwise_cons] using (show (Disjoint A C ∧ Disjoint A E' ∧ Disjoint A H') ∧
    (Disjoint C E' ∧ Disjoint C H') ∧ Disjoint E' H' from ⟨⟨hAC,hAE,hAH⟩,⟨hCE,hCH⟩,hNew⟩)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingQueuePairReplacement

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 9000000 in
lemma replace_pending_queue_pair_frame {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length j : ℕ) (st out : MachineState)
    (pm : MachinePendingKeys g s α ε ell length logical st)
    (hj : j ≤ logical.top) (hDepth : logical.top ≤ ell)
    (nextExt : RankQueueObject out.scalar.integerMemory (pm.frames j hj).exteriorBase length
      (out.scalar.core.ptrs 20) (128+32*((ell+2 : ℕ) : ℤ)))
    (nextHigh : RankQueueObject out.scalar.integerMemory (pm.frames j hj).highBase length
      (out.scalar.core.ptrs 20) (128+32*((ell+2 : ℕ) : ℤ)))
    (hData : ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem (16*(ell+3)) (16*(j+1)) (16*(j+1)+3)
      (logical.frames j).q (parentDomain logical j) ((logical.frames j).exterior.image Fin.val) nextExt.keys)
    (hHighDomain : nextHigh.keys ⊆ (parentDomain logical j).image Fin.val)
    (hHighFlags : QueuedFlags out.scalar.integerMemory (16*(ell+3)) (16*(j+1)+6) (parentDomain logical j) nextHigh.keys)
    (hPair : Disjoint nextExt.cells nextHigh.cells)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hOld : ∀ z ∈ nextExt.cells ∪ nextHigh.cells, z < st.scalar.core.ptrs 20 →
      z ∈ (pm.frames j hj).exteriorObject.cells ∪ (pm.frames j hj).highObject.cells)
    (hFields : ∀ v : Fin n, ∀ field < 16*(ell+3), field ≠ 16*(j+1)+3 → field ≠ 16*(j+1)+6 →
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field))
    (hPos : ∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 →
      z ∉ (pm.frames j hj).exteriorObject.cells ∪ (pm.frames j hj).highObject.cells →
      out.scalar.integerMemory z=st.scalar.integerMemory z)
    (hRPos : ∀ z, 0 ≤ z → out.scalar.core.mem z=st.scalar.core.mem z)
    (hRFields : ∀ v : Fin n, ∀ field < 16*(ell+3), field ≠ 16*(j+1)+4 →
      out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field))
    (hZero : out.scalar.core.ptrs 0=0) (hTop : out.scalar.core.ptrs 100=(logical.top : ℤ))
    (hWidth : out.scalar.core.ptrs 50=((16*(ell+3) : ℕ) : ℤ))
    (hAlpha : out.scalar.core.regs 30=α) (hOne : out.scalar.core.regs 31=1) (hOutput : out.output=[]) :
    ∃ memory : MachinePendingKeys g s α ε ell length logical out,
      memory.queueMass+(pm.frames j hj).queueMass=pm.queueMass+(nextExt.mass+nextHigh.mass) ∧
      (memory.frames j hj).exteriorObject.keys=nextExt.keys ∧ (memory.frames j hj).highObject.keys=nextHigh.keys ∧
      (∀ i, ∀ hi : i ≤ logical.top, i ≠ j →
        (memory.frames i hi).exteriorObject.keys=(pm.frames i hi).exteriorObject.keys ∧
        (memory.frames i hi).highObject.keys=(pm.frames i hi).highObject.keys) ∧ PendingIntegerFrame pm memory := by
  let f := pm.frames j hj
  let floor := 128+32*((ell+2 : ℕ) : ℤ)
  let oldQ := f.exteriorObject.cells ∪ f.highObject.cells
  have oldAbove (z : ℤ) (hz : z ∈ oldQ) : floor ≤ z := by
    rcases Finset.mem_union.mp hz with he|hh
    · exact f.exteriorObject.above z he
    · exact f.highObject.above z hh
  have oldOwned (z : ℤ) (hz : z ∈ oldQ) : z ∈ f.owned := by
    rcases Finset.mem_union.mp hz with he|hh
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ he)
    · exact Finset.mem_union_right _ hh
  have hHeader (i : ℕ) (hi : i ≤ logical.top) (slot : ℕ) (hs : slot < 32) :
      out.scalar.integerMemory (levelHeaderAddress i slot)=st.scalar.integerMemory (levelHeaderAddress i slot) := by
    apply hPos
    · have := levelHeaderAddress_positive i slot; omega
    · have := pm.allocator
      unfold levelHeaderAddress
      omega
    · intro hz
      have hlo := oldAbove _ hz
      dsimp only [floor] at hlo
      unfold levelHeaderAddress at hlo
      omega
  have hHeaderR (i slot : ℕ) : out.scalar.core.mem (levelHeaderAddress i slot)=st.scalar.core.mem (levelHeaderAddress i slot) :=
    hRPos _ (by have := levelHeaderAddress_positive i slot; omega)
  have hListBelow : ∀ z ∈ f.activeFoot ∪ f.cacheFoot, z < st.scalar.core.ptrs 20 := by
    intro z hz
    exact (Finset.mem_union.mp hz).elim (f.activeBelow z) (f.cacheBelow z)
  have hListAbove : ∀ z ∈ f.activeFoot ∪ f.cacheFoot, floor ≤ z := by
    intro z hz
    exact (Finset.mem_union.mp hz).elim (f.activeAbove z) (f.cacheAbove z)
  have hOwnList : ∀ z ∈ f.activeFoot ∪ f.cacheFoot, out.scalar.integerMemory z=st.scalar.integerMemory z := by
    intro z hz
    apply hPos z (by have := hListAbove z hz; dsimp only [floor] at this; omega) (hListBelow z hz)
    exact fun hq => Finset.disjoint_left.mp
      (queue_pair_separate f.activeFoot f.cacheFoot f.exteriorObject.cells f.highObject.cells (pm.pieceSeparation j hj)) hz hq
  let current := f.queues_frame hFree (hHeader j hj) (by intros; exact hHeaderR j _)
    (fun v hv field hf hn ha hb => hFields v field (by omega) ha hb)
    (fun v hv field hf hn ha => hRFields v field (by omega) ha) hOwnList nextExt nextHigh hData hHighFlags hHighDomain
  have hCurrentPieces : current.pieces.Pairwise Disjoint :=
    replace_queue_pair_pieces f.activeFoot f.cacheFoot f.exteriorObject.cells f.highObject.cells nextExt.cells nextHigh.cells
      (st.scalar.core.ptrs 20) (pm.pieceSeparation j hj) hListBelow hOld hPair
  have hCurrentOld : ∀ z ∈ current.owned, z < st.scalar.core.ptrs 20 → z ∈ f.owned := by
    intro z hz hzOld
    change z ∈ f.activeFoot ∪ f.cacheFoot ∪ nextExt.cells ∪ nextHigh.cells at hz
    rcases Finset.mem_union.mp hz with hacq|hh
    · rcases Finset.mem_union.mp hacq with hac|he
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hac)
      · exact oldOwned z (hOld z (Finset.mem_union_left _ he) hzOld)
    · exact oldOwned z (hOld z (Finset.mem_union_right _ hh) hzOld)
  have hOtherOwned (i : ℕ) (hi : i ≤ logical.top) (hne : i ≠ j) :
      ∀ z ∈ (pm.frames i hi).owned, out.scalar.integerMemory z=st.scalar.integerMemory z := by
    intro z hz
    apply hPos z (by have := (pm.frames i hi).owned_above z hz; omega) ((pm.frames i hi).owned_below z hz)
    intro hzQ
    exact Finset.disjoint_left.mp (pm.frameSeparation i hi j hj hne) hz (oldOwned z hzQ)
  let other (i : ℕ) (hi : i ≤ logical.top) (hne : i ≠ j) := (pm.frames i hi).scoped_frame hFree
    (hHeader i hi) (by intros; exact hHeaderR i _)
    (fun v hv field hf hneeded => hFields v field (by omega) (by omega) (by omega))
    (fun v hv field hf hneeded => hRFields v field (by omega) (by omega)) (hOtherOwned i hi hne)
  let frames (i : ℕ) (hi : i ≤ logical.top) : FramePendingKeys g logical i (16*(ell+3)) length out floor :=
    if he : i=j then by subst i; exact current else other i hi he
  have allCurrent : frames j hj=current := by simp [frames]
  have allOther (i : ℕ) (hi : i ≤ logical.top) (hne : i ≠ j) : frames i hi=other i hi hne := by
    simp only [frames,dif_neg hne]
  have ownedOther (i : ℕ) (hi : i ≤ logical.top) (hne : i ≠ j) : (frames i hi).owned=(pm.frames i hi).owned := by
    rw [allOther i hi hne]
    rfl
  have hGlobalI (z : ℤ) (hz : 0 ≤ z) (hs : z < 128) : out.scalar.integerMemory z=st.scalar.integerMemory z := by
    apply hPos z hz (by have := pm.allocator; omega)
    intro hm
    have := oldAbove z hm
    dsimp only [floor] at this
    omega
  have hCacheSep : Disjoint (cachedRowCells g st.scalar.integerMemory (16*(ell+3)) logical.stored) oldQ := by
    apply Finset.disjoint_left.mpr
    intro z hz hzQ
    exact Finset.disjoint_left.mp (pm.cacheSeparation j hj) (oldOwned z hzQ) hz
  have hCache : GraphCache g out.scalar.integerMemory (16*(ell+3)) logical.stored (out.scalar.core.ptrs 20) :=
    pm.graphCache.queue_frame g oldQ hCacheSep hFree (fun v field hf => hFields v field (by omega) (by omega) (by omega)) hPos
  have hRows : cachedRowCells g out.scalar.integerMemory (16*(ell+3)) logical.stored=
      cachedRowCells g st.scalar.integerMemory (16*(ell+3)) logical.stored := by
    unfold cachedRowCells
    apply Finset.biUnion_congr rfl
    intro v hv
    rw [hFields v 1 (by omega) (by omega) (by omega)]
  have hRowsBelow : ∀ z ∈ cachedRowCells g st.scalar.integerMemory (16*(ell+3)) logical.stored, z < st.scalar.core.ptrs 20 := by
    intro z hz
    obtain ⟨v,hv,hzv⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨i,hi,rfl⟩ := (mem_arrayCells _ _ _).mp hzv
    exact pm.graphCache.belowFree v hv i hi
  let memory : MachinePendingKeys g s α ε ell length logical out := {
    zero := hZero
    top := hTop
    width := hWidth
    alphaRegister := hAlpha
    one := hOne
    alphaMemory := (hRPos 0 (by norm_num)).trans pm.alphaMemory
    epsilonMemory := (hRPos 1 (by norm_num)).trans pm.epsilonMemory
    depthMemory := (hGlobalI 2 (by norm_num) (by norm_num)).trans pm.depthMemory
    lengthMemory := (hGlobalI 5 (by norm_num) (by norm_num)).trans pm.lengthMemory
    seedMemory := (hGlobalI 0 (by norm_num) (by norm_num)).trans pm.seedMemory
    allocator := pm.allocator.trans hFree
    potential := fun v => (hRFields v 0 (by omega) (by omega)).trans (pm.potential v)
    seedMarker := fun v => (hRFields v 2 (by omega) (by omega)).trans (pm.seedMarker v)
    boundary := (hGlobalI 7 (by norm_num) (by norm_num)).trans pm.boundary
    graphCache := hCache
    rowAbove := by intro v hv; rw [hFields v 1 (by omega) (by omega) (by omega)]; exact pm.rowAbove v hv
    knownDegree := by intro v hv; rw [hFields v 0 (by omega) (by omega) (by omega)]; exact pm.knownDegree v hv
    unknownDegree := by intro v hv; rw [hFields v 0 (by omega) (by omega) (by omega)]; exact pm.unknownDegree v hv
    frames := frames
    pieceSeparation := by
      intro i hi
      by_cases he : i=j
      · subst i; rw [allCurrent]; exact hCurrentPieces
      · rw [allOther i hi he]; exact pm.pieceSeparation i hi
    frameSeparation := by
      intro i hi k hk hik
      by_cases hei : i=j <;> by_cases hek : k=j
      · exact False.elim (hik (hei.trans hek.symm))
      · subst i
        rw [allCurrent,ownedOther k hk hek]
        apply Finset.disjoint_right.mpr
        intro z hz hzCurrent
        exact Finset.disjoint_left.mp (pm.frameSeparation j hj k hk (Ne.symm hek))
          (hCurrentOld z hzCurrent ((pm.frames k hk).owned_below z hz)) hz
      · subst k
        rw [ownedOther i hi hei,allCurrent]
        exact queue_disjoint_after_growth (pm.frames i hi).owned_below (pm.frameSeparation i hi j hj hei) hCurrentOld
      · rw [ownedOther i hi hei,ownedOther k hk hek]
        exact pm.frameSeparation i hi k hk hik
    cacheSeparation := by
      intro i hi
      rw [hRows]
      by_cases he : i=j
      · subst i
        rw [allCurrent]
        apply Finset.disjoint_right.mpr
        intro z hz hzCurrent
        exact Finset.disjoint_left.mp (pm.cacheSeparation j hj) (hCurrentOld z hzCurrent (hRowsBelow z hz)) hz
      · rw [ownedOther i hi he]; exact pm.cacheSeparation i hi
    output := hOutput
  }
  refine ⟨memory,?_,?_,?_,?_,?_⟩
  · apply pending_queueMass_exchange g logical s α ε ell length st out pm memory j hj f.queueMass (nextExt.mass+nextHigh.mass)
    · intro i hi he
      change (frames i hi).queueMass=(pm.frames i hi).queueMass
      rw [allOther i hi he]
      rfl
    · change (frames j hj).queueMass+f.queueMass=f.queueMass+(nextExt.mass+nextHigh.mass)
      rw [allCurrent]
      change (nextExt.mass+nextHigh.mass)+f.queueMass=f.queueMass+(nextExt.mass+nextHigh.mass)
      omega
  · change (frames j hj).exteriorObject.keys=nextExt.keys
    rw [allCurrent]
    rfl
  · change (frames j hj).highObject.keys=nextHigh.keys
    rw [allCurrent]
    rfl
  · intro i hi he
    change (frames i hi).exteriorObject.keys=_ ∧ (frames i hi).highObject.keys=_
    rw [allOther i hi he]
    exact ⟨rfl,rfl⟩

  · refine ⟨hFree,?_,?_,fun v => hFields v 7 (by omega) (by omega) (by omega)⟩
    · intro i hi z hz hBelow
      change z ∈ (frames i hi).owned at hz
      by_cases he : i=j
      · subst i
        rw [allCurrent] at hz
        exact hCurrentOld z hz hBelow
      · rw [ownedOther i hi he] at hz
        exact hz
    · intro z hz hBelow hOutside
      apply hPos z hz hBelow
      intro hQ
      exact hOutside j hj (oldOwned z hQ)

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

-- Proof module: Solutions.GraphNeighborDegree

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_graph_neighbor_degree {n : ℕ} (g : InputGraph n) (v : Fin n) :
    (g.neighbors v).length=g.graph.degree v := by
  have he : (g.neighbors v).toFinset=g.graph.neighborFinset v := by
    ext u
    simp [g.correct]
  rw [←List.toFinset_card_of_nodup (g.nodup v),he,SimpleGraph.card_neighborFinset_eq_degree]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexListCopyBody

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexListCopyBodyCode_wellFormed : vertexListCopyBodyCode.wellFormed := by
  simp [vertexListCopyBodyCode,linearCode,vertexListCopyInstructions,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma vertexListCopyBodyCode_queryReadOnly : vertexListCopyBodyCode.allAtoms queryReadOnly := by
  simp [vertexListCopyBodyCode,linearCode,vertexListCopyInstructions,sequenceCode,MachineCode.allAtoms,queryReadOnly]

set_option maxHeartbeats 2000000 in
lemma vertex_list_copy_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (head free next : ℤ) (v : Fin n)
    (hhead : st.scalar.core.ptrs 94=head) (hfree : st.scalar.core.ptrs 20=free)
    (hkey : st.scalar.integerMemory head=(v.val : ℤ)) (hnext : st.scalar.integerMemory (head+2)=next)
    (hbelow : head+2 < free) :
    ∃ out, MachineEval m g ω vertexListCopyBodyCode st 8 out ∧
      out.scalar.core.ptrs 94=next ∧ out.scalar.core.ptrs 20=free+1 ∧
      out.scalar.core.ptrs 75=st.scalar.core.ptrs 75+1 ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory free (v.val : ℤ) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+8 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let out := linearRun m g ω vertexListCopyInstructions st
  obtain ⟨e,hw,hH⟩ := linear_execute m g ω vertexListCopyInstructions
    (by simp [vertexListCopyInstructions,unitInstruction,straightInstruction]) st hh
  have hne : head+2 ≠ free := by omega
  refine ⟨out,e,?_,?_,?_,?_,?_,e.query_frame vertexListCopyBodyCode_queryReadOnly,hw,?_,hH⟩
  all_goals
    simp [out,linearRun,vertexListCopyInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hhead,hfree,hkey,Int.add_assoc,
      Function.update_of_ne hne,hnext]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexListCopyLoop

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 2300000 in
lemma vertex_list_copy_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (vertices : List (Fin n)) (head free count : ℤ) (F : Finset ℤ)
    (st : MachineState) (hh : st.scalar.halted=false) (hz : st.scalar.core.ptrs 0=0)
    (hhp : st.scalar.core.ptrs 94=head) (hf : st.scalar.core.ptrs 20=free) (hc : st.scalar.core.ptrs 75=count)
    (h : VertexListRep st.scalar.integerMemory head vertices F) (hbelow : ∀ z ∈ F, z < free) :
    ∃ out, MachineEval m g ω vertexListCopyLoopCode st (10*vertices.length+1) out ∧
      out.scalar.core.ptrs 94=0 ∧ out.scalar.core.ptrs 20=free+(vertices.length : ℤ) ∧
      out.scalar.core.ptrs 75=count+(vertices.length : ℤ) ∧
      AdjacencyStored out.scalar.integerMemory free vertices vertices.length ∧
      (∀ z, z < free → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(10*vertices.length+1 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction vertices generalizing st head free count F with
  | nil =>
    have hhead : head=0 := h.nil.1
    have hd : st.scalar.core.ptrs 94=0 := hhp.trans hhead
    refine ⟨payUnit st,?_,hd,by simpa using hf,by simpa using hc,?_,(by intros; rfl),rfl,rfl,by simp,rfl,hh⟩
    · exact MachineEval.pointerDone (r:=94) (s:=0) (body:=vertexListCopyBodyCode) hh (by rw [hd,hz])
    · intro i hi; simp at hi
  | cons v vertices ih =>
    obtain ⟨next,S,hpos,hkey,hchild,hnext,hTail,hF,hsep⟩ := h.cons_view
    have hNodeBelow : head+2 < free := hbelow _ (by rw [hF]; simp [nodeCells])
    obtain ⟨mid,eb,hm94,hm20,hm75,hmI,hmR,hmQ,hmW,hmO,hmH⟩ :=
      vertex_list_copy_body_exec m g ω (payUnit st) hh head free next v hhp hf hkey hnext hNodeBelow
    have hSsub : S ⊆ F := by rw [hF]; exact Finset.subset_union_right
    have hmTail : VertexListRep mid.scalar.integerMemory next vertices S := by
      apply hTail.frame
      intro z hz'
      rw [hmI]
      have hb := hbelow z (hSsub hz')
      change Function.update st.scalar.integerMemory free (v.val : ℤ) z=st.scalar.integerMemory z
      simp only [Function.update_of_ne (by omega : z ≠ free)]
    have hmBelow : ∀ z ∈ S, z < free+1 := by
      intro z hz'
      have hb := hbelow z (hSsub hz')
      omega
    have hm0 := (eb.pointer_frame 0 (by decide)).trans hz
    have hmCount : mid.scalar.core.ptrs 75=count+1 := by simpa only [payUnit,pcSet,hc] using hm75
    obtain ⟨out,er,ho94,ho20,ho75,hoStored,hoFrame,hoR,hoQ,hoW,hoO,hoH⟩ :=
      ih next (free+1) (count+1) S (payUnit mid) hmH hm0 hm94 hm20 hmCount hmTail hmBelow
    refine ⟨out,?_,ho94,?_,?_,?_,?_,hoR.trans hmR,hoQ.trans hmQ,?_,hoO.trans hmO,hoH⟩
    · have eRun := MachineEval.pointerNext (r:=94) (s:=0) hh (by rw [hhp,hz]; omega) eb er
      convert eRun using 1 <;> (first | rfl | simp [List.length_cons]; omega)
    · rw [ho20]
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      ring
    · rw [ho75]
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      ring
    · intro j hj hj'
      cases j with
      | zero =>
        simp only [Nat.cast_zero,add_zero,List.getElem_cons_zero]
        change out.scalar.integerMemory free=(v.val : ℤ)
        have hAt : out.scalar.integerMemory free=mid.scalar.integerMemory free := hoFrame free (by omega)
        rw [hAt,hmI]
        simp
      | succ j =>
        have hji : j < vertices.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hj'
        have hs := hoStored j hji hji
        change out.scalar.integerMemory (free+((j+1 : ℕ) : ℤ))=(vertices[j].val : ℤ)
        have haddr : free+((j+1 : ℕ) : ℤ)=free+1+(j : ℤ) := by push_cast; ring
        rw [haddr]
        exact hs
    · intro z hz'
      have hmFrame : mid.scalar.integerMemory z=st.scalar.integerMemory z := by
        rw [hmI]
        change Function.update st.scalar.integerMemory free (v.val : ℤ) z=st.scalar.integerMemory z
        simp only [Function.update_of_ne (by omega : z ≠ free)]
      exact (hoFrame z (by omega)).trans hmFrame
    · rw [hoW,payUnit_work,hmW,payUnit_work]
      simp only [List.length_cons]
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexEnumerationCreation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexEnumerationCode_wellFormed : vertexEnumerationCode.wellFormed := by
  refine ⟨?_,vertexListCopyBodyCode_wellFormed,?_⟩
  · simp [vertexEnumerationInit,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
      MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  · simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma vertexEnumerationCode_queryReadOnly : vertexEnumerationCode.allAtoms queryReadOnly := by
  simp [vertexEnumerationCode,vertexEnumerationInit,PointerRoutine.sequence,PointerRoutine.code,
    PointerOp.instruction,vertexListCopyLoopCode,MachineCode.allAtoms,
    vertexListCopyBodyCode_queryReadOnly,coreCode,queryReadOnly]

set_option maxHeartbeats 1800000 in
lemma vertex_enumeration_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (vertices : List (Fin n)) (head free : ℤ) (F : Finset ℤ)
    (st : MachineState) (hh : st.scalar.halted=false) (hz : st.scalar.core.ptrs 0=0)
    (hhp : st.scalar.core.ptrs 90=head) (hf : st.scalar.core.ptrs 20=free)
    (h : VertexListRep st.scalar.integerMemory head vertices F) (hbelow : ∀ z ∈ F, z < free) :
    ∃ out, MachineEval m g ω vertexEnumerationCode st (10*vertices.length+5) out ∧
      out.scalar.core.ptrs 80=free ∧ out.scalar.core.ptrs 77=(vertices.length : ℤ) ∧
      out.scalar.core.ptrs 20=free+(vertices.length : ℤ) ∧
      EnumerationStored out.scalar.integerMemory free (vertexEnumeration vertices) ∧
      (∀ z, z < free → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(10*vertices.length+5 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,ei,hp,hI,hR,hW,hO,hH⟩ := vertexEnumerationInit.execute m g ω st hh
  have ei3 : MachineEval m g ω vertexEnumerationInit.code st 3 pre := ei
  have h0 := (ei.pointer_frame 0 (by decide)).trans hz
  have h20 := (ei.pointer_frame 20 (by decide)).trans hf
  have h80 : pre.scalar.core.ptrs 80=free := by
    rw [hp]; simp [vertexEnumerationInit,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
      PointerOp.destination,PointerOp.result,hf]
  have h94 : pre.scalar.core.ptrs 94=head := by
    rw [hp]; simp [vertexEnumerationInit,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
      PointerOp.destination,PointerOp.result,hhp]
  have h75 : pre.scalar.core.ptrs 75=0 := by
    rw [hp]; simp [vertexEnumerationInit,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
      PointerOp.destination,PointerOp.result]
  have hpList : VertexListRep pre.scalar.integerMemory head vertices F := by rw [hI]; exact h
  obtain ⟨mid,el,hm94,hm20,hm75,hmStored,hmFrame,hmR,hmQ,hmW,hmO,hmH⟩ :=
    vertex_list_copy_loop_exec m g ω vertices head free 0 F pre hH h0 h94 h20 h75 hpList hbelow
  let out := payUnit (pointerWrite mid 77 (mid.scalar.core.ptrs 75))
  have ef := pcopy_eval m g ω mid 77 75 hmH
  have eRun : MachineEval m g ω vertexEnumerationCode st (10*vertices.length+5) out := by
    have ee := MachineEval.seq ei3 (MachineEval.seq el ef)
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,?_,?_,?_,?_,?_,hmR.trans hR,?_,?_,hmO.trans hO,hmH⟩
  · exact (ef.pointer_frame 80 (by decide)).trans ((el.pointer_frame 80 (by decide)).trans h80)
  · change mid.scalar.core.ptrs 75=(vertices.length : ℤ)
    simpa only [zero_add] using hm75
  · exact hm20
  · intro j
    exact hmStored j.val j.isLt j.isLt
  · intro z hz'
    exact (hmFrame z hz').trans (congrFun hI z)
  · exact eRun.query_frame vertexEnumerationCode_queryReadOnly
  · change mid.work+1=st.work+(10*vertices.length+5 : ℕ)
    rw [hmW,hW]
    change st.work+(3 : ℕ)+(10*vertices.length+1 : ℕ)+1= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexEnumerationDomain

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertex_enumeration_domain {n : ℕ} (vertices : List (Fin n)) :
    Finset.univ.image (vertexEnumeration vertices)=vertices.toFinset := by
  classical
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and,List.mem_toFinset]
  exact List.mem_iff_get.symm

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingEnumerationBuffer

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

structure PendingEnumerationBuffer {n k : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {machine : MachineState}
    (memory : MachinePendingKeys g s α ε ell length logical machine)
    (base : ℤ) (e : Fin k → Fin n) : Prop where
  nonnegative : 0 ≤ base
  below : ∀ i : Fin k, base+(i.val : ℤ) < machine.scalar.core.ptrs 20
  foreign : ∀ i : Fin k, ∀ j, ∀ hj : j ≤ logical.top, base+(i.val : ℤ) ∉ (memory.frames j hj).owned
  stored : EnumerationStored machine.scalar.integerMemory base e

lemma PendingEnumerationBuffer.frame {n k : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState}
    {old : MachinePendingKeys g s α ε ell length logical st} {next : MachinePendingKeys g s α ε ell length logical out}
    {base : ℤ} {e : Fin k → Fin n} (buffer : PendingEnumerationBuffer old base e)
    (fr : PendingIntegerFrame old next) : PendingEnumerationBuffer next base e := by
  refine ⟨buffer.nonnegative,fun i => (buffer.below i).trans_le fr.free,?_,?_⟩
  · intro i j hj hOwned
    exact buffer.foreign i j hj (fr.oldOwned j hj _ hOwned (buffer.below i))
  · intro i
    rw [fr.integerFrame _ (by have := buffer.nonnegative; have := Int.natCast_nonneg i.val; omega)
      (buffer.below i) (buffer.foreign i)]
    exact buffer.stored i

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingArrayRefreshRead

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pendingArrayRefreshReadCode_wellFormed : pendingArrayRefreshReadCode.wellFormed := by
  simp [pendingArrayRefreshReadCode,pendingArrayRefreshReadInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma pending_array_refresh_read_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (base : ℤ) (index : ℕ) (v : Fin n) (st : MachineState) (hh : st.scalar.halted=false)
    (h140 : st.scalar.core.ptrs 140=base) (h143 : st.scalar.core.ptrs 143=(index : ℤ))
    (hEnum : st.scalar.integerMemory (base+(index : ℤ))=(v.val : ℤ)) :
    ∃ out, MachineEval m g ω pendingArrayRefreshReadCode st 2 out ∧ out.scalar.core.ptrs 40=(v.val : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+2 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω pendingArrayRefreshReadInstructions
    (by simp [pendingArrayRefreshReadInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,pendingArrayRefreshReadInstructions,atomState,machineStep,pcSet,hh,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,h140,h143,hEnum]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueuePairFrameContext

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma queuePairFrameContextCode_wellFormed : queuePairFrameContextCode.wellFormed := by
  refine ⟨levelHeaderIntegerToCode_wellFormed 8 128,levelHeaderRealToCode_wellFormed 5 47,
    exteriorFrameContextCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 3500000 in
lemma queue_pair_frame_context_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level width length : ℕ) (extBase highBase floor : ℤ) (q theta : ℝ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) (hw : st.scalar.core.ptrs 50=(width : ℤ))
    (hLen : st.scalar.integerMemory 5=(length : ℤ))
    (hExtBase : st.scalar.integerMemory (levelHeaderAddress level 7)=extBase)
    (hHighBase : st.scalar.integerMemory (levelHeaderAddress level 8)=highBase)
    (hQ : st.scalar.core.mem (levelHeaderAddress level 1)=q)
    (hTheta : st.scalar.core.mem (levelHeaderAddress level 5)=theta)
    (hOne : st.scalar.core.regs 31=1) (h0 : st.scalar.core.ptrs 0=0) (hFree : floor ≤ st.scalar.core.ptrs 20) :
    ∃ out, MachineEval m g ω queuePairFrameContextCode st 54 out ∧
      ExteriorQueueContext out width (16*(level+1)) (16*(level+1)+3) length extBase floor q ∧
      out.scalar.core.ptrs 128=highBase ∧ out.scalar.core.ptrs 89=((16*(level+1) : ℕ) : ℤ) ∧
      out.scalar.core.regs 47=theta ∧ out.scalar.core.regs 31=1 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.core.ptrs 20=st.scalar.core.ptrs 20 ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+54 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a128,aI,aR,aW,aO,aH⟩ := level_header_integer_to_exec m g ω st hh level 8 128 hl
  rw [hHighBase] at a128
  obtain ⟨b,eb,b47,bI,bR,bW,bO,bH⟩ := level_header_real_to_exec m g ω a aH level 5 47
    ((ea.pointer_frame 100 (by decide)).trans hl) ((ea.real_register_frame 31 (by decide)).trans hOne)
  have b47' : b.scalar.core.regs 47=theta := by rw [b47,aR]; exact hTheta
  have ePrefix := MachineEval.seq ea eb
  have bLen : b.scalar.integerMemory 5=(length : ℤ) := by rw [bI,aI]; exact hLen
  have bExt : b.scalar.integerMemory (levelHeaderAddress level 7)=extBase := by rw [bI,aI]; exact hExtBase
  have bQ : b.scalar.core.mem (levelHeaderAddress level 1)=q := by rw [bR,aR]; exact hQ
  have bFree : b.scalar.core.ptrs 20=st.scalar.core.ptrs 20 := ePrefix.pointer_frame 20 (by decide)
  obtain ⟨c,ec,cCtx,cI,cR,cFree,cW,cO,cH⟩ := exterior_frame_context_exec m g ω b bH level width length extBase floor q
    ((ePrefix.pointer_frame 100 (by decide)).trans hl) ((ePrefix.pointer_frame 50 (by decide)).trans hw)
    bLen bExt bQ ((ePrefix.real_register_frame 31 (by decide)).trans hOne)
    ((ePrefix.pointer_frame 0 (by decide)).trans h0) (by rw [bFree]; exact hFree)
  let out := payUnit (pointerWrite c 89 ((16*(level+1) : ℕ) : ℤ))
  have ed : MachineEval m g ω (coreCode (.pcopy 89 87)) c 1 out := by
    simpa only [out,coreCode,cCtx.levelPointer] using pcopy_eval m g ω c 89 87 cH
  have eSuffix := MachineEval.seq ec ed
  have ex : MachineEval m g ω queuePairFrameContextCode st 54 out := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  refine ⟨out,ex,?_,?_,by simp [out,payUnit,pcSet,pointerWrite],?_,?_,cI.trans (bI.trans aI),cR.trans (bR.trans aR),
    cFree.trans bFree,ex.query_frame (by decide),ex.unit_work queuePairFrameContextCode_wellFormed (by decide) hh,
    cO.trans (bO.trans aO),cH⟩
  · exact ⟨cCtx.zero,cCtx.basePointer,cCtx.lengthPointer,cCtx.widthPointer,cCtx.levelPointer,cCtx.flagPointer,cCtx.threshold,cCtx.floorBound⟩
  · exact ((MachineEval.seq eb eSuffix).pointer_frame 128 (by decide)).trans a128
  · exact (eSuffix.real_register_frame 47 (by decide)).trans b47'
  · exact (ex.real_register_frame 31 (by decide)).trans hOne

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HighBooleanCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma highDegreeProductCode_wellFormed : highDegreeProductCode.wellFormed := by
  simp [highDegreeProductCode,linearCode,highDegreeProductInstructions,RealOperation.instruction,
    sequenceCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨3,by norm_num⟩

lemma highResidualDecisionCode_wellFormed : highResidualDecisionCode.wellFormed := by
  simp [highResidualDecisionCode,RealOperation.instruction,coreCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  constructor
  · exact ⟨1,by norm_num⟩
  · exact ⟨0,by norm_num⟩

lemma highActiveCode_wellFormed : highActiveCode.wellFormed := by
  refine ⟨vertexFieldReadCode_wellFormed 0 60,highDegreeProductCode_wellFormed,?_,?_,highResidualDecisionCode_wellFormed⟩
  · simp [exteriorResidualOffsetRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
      MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  · simp [vertexRealLoadCode,vertexAddressCode_wellFormed,coreCode,MachineCode.wellFormed,
      straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma highBooleanValueCode_wellFormed : highBooleanValueCode.wellFormed := by
  refine ⟨?_,?_,?_,highActiveCode_wellFormed⟩
  · simp [exteriorActiveOffsetRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
      MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  · simp [vertexIntegerLoadCode,vertexAddressCode_wellFormed,MachineCode.wellFormed,straightInstruction,
      admissible,scalarProgram,LocalPush.Admissible]
  · simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
    exact ⟨0,by norm_num⟩

lemma highBooleanUpdateCode_wellFormed : highBooleanUpdateCode.wellFormed := by
  refine ⟨highBooleanValueCode_wellFormed,?_,?_⟩
  · simp [highBooleanStoreOffsetRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
      MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  · simp [vertexRealStoreCode,vertexAddressCode_wellFormed,coreCode,MachineCode.wellFormed,straightInstruction,
      admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.HighQueueRefreshExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma highQueueRefreshCode_wellFormed : highQueueRefreshCode.wellFormed := by
  refine ⟨?_,highBooleanUpdateCode_wellFormed,highQueueContextCode_wellFormed,exteriorQueueRefreshCode_wellFormed⟩
  simp [highQueueRefreshInit,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end SparseQueue
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

lemma queuePairRefreshCode_wellFormed : queuePairRefreshCode.wellFormed := by
  refine ⟨exteriorQueueRefreshCode_wellFormed,?_,highQueueRefreshCode_wellFormed⟩
  simp [queuePairHighPrepCode,queuePairHighPrepInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.PendingLevelRefresh

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma pendingLevelRefreshCode_wellFormed : pendingLevelRefreshCode.wellFormed := by
  refine ⟨?_,queuePairFrameContextCode_wellFormed,queuePairRefreshCode_wellFormed,?_⟩
  all_goals simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 9000000 in
lemma pending_level_refresh_foreign_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length N R : ℕ) (logical : RecursiveState n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : MachinePendingKeys g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (j : ℕ) (hj : j ≤ logical.top) (v : Fin n) (hv : v ∈ parentDomain logical j)
    (hIndex : st.scalar.core.ptrs 109=(j : ℤ)) (hTop : st.scalar.core.ptrs 108=(logical.top : ℤ))
    (hVertex : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hMass : pm.queueMass ≤ N) (hCap : R < length) (hPow : N < 2^R) :
    ∃ steps out, ∃ memory : MachinePendingKeys g s α ε ell length logical out,
      MachineEval m g ω pendingLevelRefreshCode st steps out ∧
      steps ≤ 42*R+56*(16*(ell+3))+259 ∧ memory.queueMass ≤ pm.queueMass+2 ∧
      (memory.frames j hj).exteriorObject.keys=(if v ∈ (logical.frames j).exterior then
        insert v.val (pm.frames j hj).exteriorObject.keys else (pm.frames j hj).exteriorObject.keys) ∧
      (memory.frames j hj).highObject.keys=(if v ∈ (logical.frames j).high then
        insert v.val (pm.frames j hj).highObject.keys else (pm.frames j hj).highObject.keys) ∧
      (∀ i, ∀ hi : i ≤ logical.top, i ≠ j →
        (memory.frames i hi).exteriorObject.keys=(pm.frames i hi).exteriorObject.keys ∧
        (memory.frames i hi).highObject.keys=(pm.frames i hi).highObject.keys) ∧
      out.scalar.core.ptrs 89=((16*(j+1) : ℕ) : ℤ) ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+4))
        (if st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+2))=0 then 0 else
          if 3*(logical.frames j).theta*(st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0) : ℝ) ≤
            st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+1)) then 1 else 0) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧ PendingIntegerFrame pm memory := by
  classical
  let width := 16*(ell+3)
  let floor := 128+32*((ell+2 : ℕ) : ℤ)
  let f := pm.frames j hj
  let a := payUnit (pointerWrite st 100 (j : ℤ))
  have ea : MachineEval m g ω (coreCode (.pcopy 100 109)) st 1 a := by
    simpa only [a,coreCode,hIndex] using pcopy_eval m g ω st 100 109 hh
  have a100 : a.scalar.core.ptrs 100=(j : ℤ) := by simp [a,payUnit,pcSet,pointerWrite]
  obtain ⟨b,eb,bCtx,b128,b89,b47,b31,bI,bR,bFree,bQ,bW,bO,bH⟩ := queue_pair_frame_context_exec m g ω a hh j width length
    f.exteriorBase f.highBase floor (logical.frames j).q (logical.frames j).theta a100
    ((ea.pointer_frame 50 (by decide)).trans pm.width) pm.lengthMemory f.exteriorPointer f.highPointer f.q f.theta pm.one pm.zero pm.allocator
  have ePrefix := MachineEval.seq ea eb
  have prefixFree : b.scalar.core.ptrs 20=st.scalar.core.ptrs 20 := ePrefix.pointer_frame 20 (by decide)
  let bExt : RankQueueObject b.scalar.integerMemory f.exteriorBase length (b.scalar.core.ptrs 20) floor :=
    f.exteriorObject.frame (fun z hz => congrFun bI z) (le_of_eq prefixFree.symm)
  let bHigh : RankQueueObject b.scalar.integerMemory f.highBase length (b.scalar.core.ptrs 20) floor :=
    f.highObject.frame (fun z hz => congrFun bI z) (le_of_eq prefixFree.symm)
  have bSep : Disjoint bHigh.cells bExt.cells := by
    have he := (pm.pieceSeparation j hj).rel_get_of_lt
      (a:=⟨2,by simp [FramePendingKeys.pieces]⟩) (b:=⟨3,by simp [FramePendingKeys.pieces]⟩) (by change (2 : ℕ)<3; omega)
    exact he.symm
  have bData : ExteriorQueueMemory b.scalar.integerMemory b.scalar.core.mem width (16*(j+1)) (16*(j+1)+3)
      (logical.frames j).q (parentDomain logical j) ((logical.frames j).exterior.image Fin.val) bExt.keys := by
    change ExteriorQueueMemory b.scalar.integerMemory b.scalar.core.mem width (16*(j+1)) (16*(j+1)+3)
      (logical.frames j).q (parentDomain logical j) ((logical.frames j).exterior.image Fin.val) f.exteriorObject.keys
    rw [bI,bR]
    exact f.exteriorData
  have bZero : ∀ u ∈ parentDomain logical j, b.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+5))=0 := by
    rw [bI]
    exact f.virtualExcluded
  have bFlags : QueuedFlags b.scalar.integerMemory width (16*(j+1)+6) (parentDomain logical j) bHigh.keys := by
    change QueuedFlags b.scalar.integerMemory width (16*(j+1)+6) (parentDomain logical j) f.highObject.keys
    rw [bI]
    exact f.highFlags
  have bValid : ∀ u ∈ parentDomain logical j, u.val ∈ (logical.frames j).high.image Fin.val ↔
      b.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+2)) ≠ 0 ∧
      3*(logical.frames j).theta*(b.scalar.integerMemory (vertexRecordAddress width u.val 0) : ℝ) ≤
        b.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+1)) := by
    rw [bI,bR]
    exact f.highValid
  have bExtMass : bExt.mass ≤ N := (Nat.le_add_right _ _).trans ((pm.frame_mass_le_total j hj).trans hMass)
  have bHighMass : bHigh.mass ≤ N := (Nat.le_add_left _ _).trans ((pm.frame_mass_le_total j hj).trans hMass)
  obtain ⟨u,c,cExt,cHigh,ec,hu,cExtKeys,cHighKeys,cExtMass,cHighMass,cData,cDomain,cFlags,cSep,cFree,cUpper,cOld,cFields,cPos,cR,cQ,cW,cO,cH,c0⟩ :=
    queue_pair_refresh_exec m g ω b bH width (16*(j+1)) length N R (by dsimp [width]; omega)
      f.exteriorBase f.highBase floor (by dsimp [floor]; omega) (logical.frames j).q (logical.frames j).theta
      (parentDomain logical j) ((logical.frames j).exterior.image Fin.val) ((logical.frames j).high.image Fin.val)
      bExt bHigh bSep bCtx bData bZero f.highDomain bFlags bValid b128 b89 b31 b47 v hv
      ((ePrefix.pointer_frame 40 (by decide)).trans hVertex) bExtMass bHighMass hCap hPow
  have eBefore := MachineEval.seq ea (MachineEval.seq eb ec)
  have c108 := (eBefore.pointer_frame 108 (by decide)).trans hTop
  let out := payUnit (pointerWrite c 100 (logical.top : ℤ))
  have ed : MachineEval m g ω (coreCode (.pcopy 100 108)) c 1 out := by
    simpa only [out,coreCode,c108] using pcopy_eval m g ω c 100 108 cH
  have ex : MachineEval m g ω pendingLevelRefreshCode st (1+(54+(u+1))) out := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  have hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 := by
    change st.scalar.core.ptrs 20 ≤ c.scalar.core.ptrs 20
    change b.scalar.core.ptrs 20=a.scalar.core.ptrs 20 at bFree
    change b.scalar.core.ptrs 20=st.scalar.core.ptrs 20 at bFree
    rw [←bFree]
    exact cFree
  have hFields : ∀ w : Fin n, ∀ field < width, field ≠ 16*(j+1)+3 → field ≠ 16*(j+1)+6 →
      out.scalar.integerMemory (vertexRecordAddress width w.val field)=st.scalar.integerMemory (vertexRecordAddress width w.val field) := by
    intro w field hf h3 h6
    change c.scalar.integerMemory _=_
    rw [cFields w field hf h3 h6,bI]
    rfl
  have hReal : out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)+4))
      (if st.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+2))=0 then 0 else
        if 3*(logical.frames j).theta*(st.scalar.integerMemory (vertexRecordAddress width v.val 0) : ℝ) ≤
          st.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)+1)) then 1 else 0) := by
    change c.scalar.core.mem=_
    rw [cR,bI,bR]
    rfl
  obtain ⟨memory,hMassEq,hExtKeys,hHighKeys,hOthers,hIntegerFrame⟩ := replace_pending_queue_pair_frame g logical s α ε ell length j st out pm hj hDepth
    cExt cHigh cData cDomain cFlags cSep.symm hFree
    (by
      intro z hz hlt
      have hz' : z < b.scalar.core.ptrs 20 := by rw [bFree]; exact hlt
      exact cOld z hz hz') hFields
    (by
      intro z hz hlt hn
      have hz' : z < b.scalar.core.ptrs 20 := by rw [bFree]; exact hlt
      exact (cPos z hz hz' hn).trans (congrFun bI z))
    (by
      intro z hz
      rw [hReal,Function.update_of_ne (by have := vertexRecordAddress_negative width v.val (16*(j+1)+4); omega)])
    (by
      intro w field hf hn
      rw [hReal,vertex_memory_update_other_field _ width v.val w.val (16*(j+1)+4) field _ (by dsimp [width]; omega) hf hn])
    c0 (by simp [out,payUnit,pcSet,pointerWrite])
    ((ex.pointer_frame 50 (by decide)).trans pm.width)
    ((ex.real_register_frame 30 (by decide)).trans pm.alphaRegister)
    ((ex.real_register_frame 31 (by decide)).trans pm.one) (by change c.output=[]; exact cO.trans (bO.trans pm.output))
  refine ⟨1+(54+(u+1)),out,memory,ex,by dsimp [width] at hu ⊢; omega,?_,?_,?_,hOthers,
    (ed.pointer_frame 89 (by decide)).trans ((ec.pointer_frame 89 (by decide)).trans b89),hReal,ex.query_frame (by decide),
    ex.unit_work pendingLevelRefreshCode_wellFormed (by decide) hh,cO.trans bO,cH,hIntegerFrame⟩
  · change cExt.mass ≤ f.exteriorObject.mass+1 at cExtMass
    change cHigh.mass ≤ f.highObject.mass+1 at cHighMass
    change memory.queueMass+(f.exteriorObject.mass+f.highObject.mass)=pm.queueMass+(cExt.mass+cHigh.mass) at hMassEq
    omega
  · have hMem : v.val ∈ (logical.frames j).exterior.image Fin.val ↔ v ∈ (logical.frames j).exterior := by
      constructor
      · intro h
        obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
        exact (Fin.ext he : w=v) ▸ hw
      · intro h
        exact Finset.mem_image.mpr ⟨v,h,rfl⟩
    rw [hExtKeys]
    change cExt.keys=(if v ∈ (logical.frames j).exterior then insert v.val f.exteriorObject.keys else f.exteriorObject.keys)
    rw [cExtKeys]
    by_cases he : v ∈ (logical.frames j).exterior
    · rw [if_pos (hMem.mpr he),if_pos he]
      rfl
    · rw [if_neg (fun h => he (hMem.mp h)),if_neg he]
      rfl
  · have hMem : v.val ∈ (logical.frames j).high.image Fin.val ↔ v ∈ (logical.frames j).high := by
      constructor
      · intro h
        obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
        exact (Fin.ext he : w=v) ▸ hw
      · intro h
        exact Finset.mem_image.mpr ⟨v,h,rfl⟩
    rw [hHighKeys]
    change cHigh.keys=(if v ∈ (logical.frames j).high then insert v.val f.highObject.keys else f.highObject.keys)
    rw [cHighKeys]
    by_cases he : v ∈ (logical.frames j).high
    · rw [if_pos (hMem.mpr he),if_pos he]
      rfl
    · rw [if_neg (fun h => he (hMem.mp h)),if_neg he]
      rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingLevelGuard

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pendingLevelGuardCode_wellFormed : pendingLevelGuardCode.wellFormed := ⟨trivial,pendingLevelRefreshCode_wellFormed⟩

set_option maxHeartbeats 6000000 in
lemma pending_level_guard_foreign_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length N R : ℕ) (logical : RecursiveState n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : MachinePendingKeys g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (j : ℕ) (hj : j ≤ logical.top) (v : Fin n)
    (hExtDomain : (logical.frames j).exterior ⊆ parentDomain logical j)
    (hHighDomain : (logical.frames j).high ⊆ parentDomain logical j)
    (hIndex : st.scalar.core.ptrs 109=(j : ℤ)) (hTop : st.scalar.core.ptrs 108=(logical.top : ℤ))
    (hVertex : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hFlag : st.scalar.core.ptrs 118=(if v ∈ parentDomain logical j then 1 else 0))
    (hMass : pm.queueMass ≤ N) (hCap : R < length) (hPow : N < 2^R) :
    ∃ steps out, ∃ memory : MachinePendingKeys g s α ε ell length logical out,
      MachineEval m g ω pendingLevelGuardCode st steps out ∧
      steps ≤ 42*R+56*(16*(ell+3))+261 ∧ memory.queueMass ≤ pm.queueMass+2 ∧
      (memory.frames j hj).exteriorObject.keys=(if v ∈ (logical.frames j).exterior then
        insert v.val (pm.frames j hj).exteriorObject.keys else (pm.frames j hj).exteriorObject.keys) ∧
      (memory.frames j hj).highObject.keys=(if v ∈ (logical.frames j).high then
        insert v.val (pm.frames j hj).highObject.keys else (pm.frames j hj).highObject.keys) ∧
      (∀ i, ∀ hi : i ≤ logical.top, i ≠ j →
        (memory.frames i hi).exteriorObject.keys=(pm.frames i hi).exteriorObject.keys ∧
        (memory.frames i hi).highObject.keys=(pm.frames i hi).highObject.keys) ∧
      out.scalar.core.mem=(if v ∈ parentDomain logical j then
        Function.update st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+4))
          (if st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+2))=0 then 0 else
            if 3*(logical.frames j).theta*(st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0) : ℝ) ≤
              st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+1)) then 1 else 0)
        else st.scalar.core.mem) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧ PendingIntegerFrame pm memory := by
  by_cases hDomain : v ∈ parentDomain logical j
  · obtain ⟨u,b,bMemory,eb,hu,bMass,bExt,bHigh,bOthers,b89,bR,bQ,bW,bO,bH,bFrame⟩ :=
      pending_level_refresh_foreign_exec m g ω s α ε ell length N R logical (payUnit st) hh pm.payUnit hDepth j hj v hDomain
        hIndex hTop hVertex hMass hCap hPow
    have ex : MachineEval m g ω pendingLevelGuardCode st (1+u+1) (payUnit b) :=
      MachineEval.pointerGt hh (by rw [hFlag,if_pos hDomain,pm.zero]; norm_num) eb
    refine ⟨1+u+1,payUnit b,bMemory.payUnit,ex,by omega,bMass,bExt,bHigh,bOthers,?_,
      ex.query_frame (by decide),ex.unit_work pendingLevelGuardCode_wellFormed (by decide) hh,bO,bH,((PendingIntegerFrame.payUnit pm).trans bFrame).trans (PendingIntegerFrame.payUnit bMemory)⟩
    change b.scalar.core.mem=_
    rw [if_pos hDomain]
    exact bR
  · have eSkip : MachineEval m g ω (.skip : MachineCode) (payUnit st) 0 (payUnit st) := MachineEval.skip _
    have ex : MachineEval m g ω pendingLevelGuardCode st 1 (payUnit st) :=
      MachineEval.pointerLe hh (by rw [hFlag,if_neg hDomain,pm.zero]) eSkip
    refine ⟨1,payUnit st,pm.payUnit,ex,by omega,by change pm.queueMass ≤ pm.queueMass+2; omega,?_,?_,?_,?_,rfl,
      ex.unit_work pendingLevelGuardCode_wellFormed (by decide) hh,rfl,hh,PendingIntegerFrame.payUnit pm⟩
    · have he : v ∉ (logical.frames j).exterior := fun h => hDomain (hExtDomain h)
      rw [if_neg he]
      rfl
    · have he : v ∉ (logical.frames j).high := fun h => hDomain (hHighDomain h)
      rw [if_neg he]
      rfl
    · intro i hi he
      exact ⟨rfl,rfl⟩
    · change st.scalar.core.mem=_
      rw [if_neg hDomain]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DomainAdvance

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma domainAdvanceCode_wellFormed : domainAdvanceCode.wellFormed := by
  refine ⟨trivial,?_,queuedFlagReadCode_wellFormed,?_⟩
  all_goals simp [levelVertexOffsetCode,levelVertexOffsetInstructions,linearCode,sequenceCode,coreCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 3000000 in
lemma domain_advance_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width base : ℕ) (v : Fin n)
    (domain active : Finset (Fin n)) (hSubset : active ⊆ domain)
    (h0 : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hb : st.scalar.core.ptrs 87=(base : ℤ))
    (hFlag : st.scalar.core.ptrs 118=if v ∈ domain then 1 else 0)
    (hRecord : v ∈ domain → st.scalar.integerMemory (vertexRecordAddress width v.val (base+2))=(if v ∈ active then 1 else 0)) :
    ∃ steps out, MachineEval m g ω domainAdvanceCode st steps out ∧ steps ≤ 4*width+13 ∧
      out.scalar.core.ptrs 118=(if v ∈ active then 1 else 0) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.core.regs=st.scalar.core.regs ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  classical
  by_cases hDomain : v ∈ domain
  · obtain ⟨a,ea,a88,aI,aR,aW,aO,aH⟩ := level_vertex_offset_exec m g ω (payUnit st) hh base 2 hb
    obtain ⟨b,eb,b51,bI,bR,bG,bQ,bW,bO,bH⟩ := queued_flag_read_exec m g ω a aH width v.val (base+2)
      ((ea.pointer_frame 0 (by decide)).trans h0) ((ea.pointer_frame 40 (by decide)).trans hv)
      ((ea.pointer_frame 41 (by decide)).trans hw) a88
    have b51' : b.scalar.core.ptrs 51=(if v ∈ active then 1 else 0) := by rw [b51,aI]; exact hRecord hDomain
    let c := payUnit (pointerWrite b 118 (if v ∈ active then 1 else 0))
    have ec : MachineEval m g ω (coreCode (.pcopy 118 51)) b 1 c := by
      simpa only [c,coreCode,b51'] using pcopy_eval m g ω b 118 51 bH
    have eBody : MachineEval m g ω domainAdvanceBodyCode (payUnit st) (2+(4*width+8+1)) c :=
      MachineEval.seq ea (MachineEval.seq eb ec)
    have ex : MachineEval m g ω domainAdvanceCode st (1+(2+(4*width+8+1))+1) (payUnit c) :=
      MachineEval.pointerGt hh (by rw [hFlag,if_pos hDomain,h0]; norm_num) eBody
    refine ⟨1+(2+(4*width+8+1))+1,payUnit c,ex,by omega,?_,bI.trans aI,bR.trans aR,?_,
      ex.query_frame (by decide),ex.unit_work domainAdvanceCode_wellFormed (by decide) hh,bO.trans aO,bH⟩
    · simp [c,payUnit,pcSet,pointerWrite]
    · exact bG.trans (ea.register_frame (by
        simp [levelVertexOffsetCode,levelVertexOffsetInstructions,linearCode,sequenceCode,coreCode,MachineCode.allAtoms,registerReadOnly]))
  · have hActive : v ∉ active := fun h => hDomain (hSubset h)
    have ex : MachineEval m g ω domainAdvanceCode st 1 (payUnit st) :=
      MachineEval.pointerLe hh (by rw [hFlag,if_neg hDomain,h0]) (MachineEval.skip (payUnit st))
    refine ⟨1,payUnit st,ex,by omega,?_,rfl,rfl,rfl,rfl,ex.unit_work domainAdvanceCode_wellFormed (by decide) hh,rfl,hh⟩
    change st.scalar.core.ptrs 118= _
    rw [hFlag,if_neg hDomain,if_neg hActive]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingDomainAdvance

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pendingDomainAdvanceCode_wellFormed : pendingDomainAdvanceCode.wellFormed := by
  refine ⟨?_,domainAdvanceCode_wellFormed⟩
  simp [pendingDomainAdvanceInitCode,pendingDomainAdvanceInitInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 4000000 in
lemma pending_domain_advance_foreign_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (logical : RecursiveState n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : MachinePendingKeys g s α ε ell length logical st) (j : ℕ) (hj : j ≤ logical.top)
    (v : Fin n) (hSubset : (logical.frames j).active ⊆ parentDomain logical j)
    (hIndex : st.scalar.core.ptrs 109=(j : ℤ)) (hVertex : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hFlag : st.scalar.core.ptrs 118=(if v ∈ parentDomain logical j then 1 else 0)) :
    ∃ steps out, ∃ memory : MachinePendingKeys g s α ε ell length logical out,
      MachineEval m g ω pendingDomainAdvanceCode st steps out ∧ steps ≤ 4*(16*(ell+3))+20 ∧
      out.scalar.core.ptrs 118=(if v ∈ parentDomain logical (j+1) then 1 else 0) ∧
      memory.queueMass=pm.queueMass ∧
      (∀ i, ∀ hi : i ≤ logical.top, (memory.frames i hi).exteriorObject.keys=(pm.frames i hi).exteriorObject.keys ∧
        (memory.frames i hi).highObject.keys=(pm.frames i hi).highObject.keys) ∧ out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧ PendingIntegerFrame pm memory := by
  let width := 16*(ell+3)
  let a := linearRun m g ω pendingDomainAdvanceInitInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω pendingDomainAdvanceInitInstructions
    (by simp [pendingDomainAdvanceInitInstructions,unitInstruction,straightInstruction]) st hh
  have a87 : a.scalar.core.ptrs 87=((16*(j+1) : ℕ) : ℤ) := by
    simp [a,linearRun,pendingDomainAdvanceInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hIndex]
    omega
  have a41 : a.scalar.core.ptrs 41=(width : ℤ) := by
    simp [a,linearRun,pendingDomainAdvanceInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,pm.width,width]
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,pendingDomainAdvanceInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aR : a.scalar.core.mem=st.scalar.core.mem := by
    simp [a,linearRun,pendingDomainAdvanceInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,pendingDomainAdvanceInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  obtain ⟨u,out,eb,hu,b118,bI,bR,bG,bQ,bW,bO,bH⟩ := domain_advance_exec m g ω a aH width (16*(j+1)) v
    (parentDomain logical j) (logical.frames j).active hSubset
    ((ea.pointer_frame 0 (by decide)).trans pm.zero) ((ea.pointer_frame 40 (by decide)).trans hVertex) a41 a87
    ((ea.pointer_frame 118 (by decide)).trans hFlag) (by intro hv; rw [aI]; exact (pm.frames j hj).activeFlags v hv)
  have ex : MachineEval m g ω pendingDomainAdvanceCode st (7+u) out := MachineEval.seq ea eb
  have outI := bI.trans aI
  have outR := bR.trans aR
  have hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ex.pointer_frame _ (by decide)
  have hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ex.real_register_frame _ (by decide)
  let memory := pm.frame outI outR hP hG (bO.trans aO)
  refine ⟨7+u,out,memory,ex,by dsimp [width] at hu ⊢; omega,?_,(by rfl),(by intro i hi; exact ⟨rfl,rfl⟩),outI,outR,
    ex.query_frame (by decide),ex.unit_work pendingDomainAdvanceCode_wellFormed (by decide) hh,bO.trans aO,bH,PendingIntegerFrame.frame pm outI outR hP hG (bO.trans aO)⟩
  simpa [parentDomain] using b118

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingVertexLevelBody

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pendingVertexLevelBodyCode_wellFormed : pendingVertexLevelBodyCode.wellFormed := by
  refine ⟨pendingLevelGuardCode_wellFormed,pendingDomainAdvanceCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 6000000 in
lemma pending_vertex_level_body_foreign_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length N R : ℕ) (logical : RecursiveState n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : MachinePendingKeys g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (j : ℕ) (hj : j ≤ logical.top) (v : Fin n)
    (hActiveDomain : (logical.frames j).active ⊆ parentDomain logical j)
    (hExtDomain : (logical.frames j).exterior ⊆ parentDomain logical j)
    (hHighDomain : (logical.frames j).high ⊆ parentDomain logical j)
    (hIndex : st.scalar.core.ptrs 109=(j : ℤ)) (hStop : st.scalar.core.ptrs 111=((logical.top+1 : ℕ) : ℤ))
    (hTop : st.scalar.core.ptrs 108=(logical.top : ℤ)) (hVertex : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hFlag : st.scalar.core.ptrs 118=(if v ∈ parentDomain logical j then 1 else 0))
    (hMass : pm.queueMass ≤ N) (hCap : R < length) (hPow : N < 2^R) :
    ∃ steps out, ∃ memory : MachinePendingKeys g s α ε ell length logical out,
      MachineEval m g ω pendingVertexLevelBodyCode st steps out ∧
      steps ≤ 42*R+60*(16*(ell+3))+282 ∧ memory.queueMass ≤ pm.queueMass+2 ∧
      out.scalar.core.ptrs 109=((j+1 : ℕ) : ℤ) ∧ out.scalar.core.ptrs 111=((logical.top+1 : ℕ) : ℤ) ∧
      out.scalar.core.ptrs 118=(if v ∈ parentDomain logical (j+1) then 1 else 0) ∧
      (memory.frames j hj).exteriorObject.keys=(if v ∈ (logical.frames j).exterior then
        insert v.val (pm.frames j hj).exteriorObject.keys else (pm.frames j hj).exteriorObject.keys) ∧
      (memory.frames j hj).highObject.keys=(if v ∈ (logical.frames j).high then
        insert v.val (pm.frames j hj).highObject.keys else (pm.frames j hj).highObject.keys) ∧
      (∀ i, ∀ hi : i ≤ logical.top, i ≠ j →
        (memory.frames i hi).exteriorObject.keys=(pm.frames i hi).exteriorObject.keys ∧
        (memory.frames i hi).highObject.keys=(pm.frames i hi).highObject.keys) ∧
      out.scalar.core.mem=(if v ∈ parentDomain logical j then
        Function.update st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+4))
          (if st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+2))=0 then 0 else
            if 3*(logical.frames j).theta*(st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0) : ℝ) ≤
              st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+1)) then 1 else 0)
        else st.scalar.core.mem) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧ PendingIntegerFrame pm memory := by
  obtain ⟨u,b,bMem,eb,hu,bMass,bExt,bHigh,bOthers,bR,bQ,bW,bO,bH,bFrame⟩ := pending_level_guard_foreign_exec m g ω s α ε ell length N R
    logical st hh pm hDepth j hj v hExtDomain hHighDomain hIndex hTop hVertex hFlag hMass hCap hPow
  obtain ⟨w,a,aMem,ea,hw,a118,aMass,aKeys,aI,aR,aQ,aW,aO,aH,aFrame⟩ := pending_domain_advance_foreign_exec m g ω s α ε ell length logical
    b bH bMem j hj v hActiveDomain ((eb.pointer_frame 109 (by decide)).trans hIndex)
    ((eb.pointer_frame 40 (by decide)).trans hVertex) ((eb.pointer_frame 118 (by decide)).trans hFlag)
  have ePrefix := MachineEval.seq eb ea
  have a109 := (ePrefix.pointer_frame 109 (by decide)).trans hIndex
  let out := payUnit (pointerWrite a 109 ((j+1 : ℕ) : ℤ))
  have ec : MachineEval m g ω (coreCode (.pinc 109)) a 1 out := by
    simpa only [out,coreCode,a109,Nat.cast_add,Nat.cast_one] using pinc_eval m g ω a 109 aH
  let memory := (aMem.pointerWrite 109 ((j+1 : ℕ) : ℤ) (by decide)).payUnit
  have ex : MachineEval m g ω pendingVertexLevelBodyCode st (u+(w+1)) out := MachineEval.seq eb (MachineEval.seq ea ec)
  refine ⟨u+(w+1),out,memory,ex,by omega,?_,by simp [out,payUnit,pcSet,pointerWrite],
    (ex.pointer_frame 111 (by decide)).trans hStop,(ec.pointer_frame 118 (by decide)).trans a118,?_,?_,?_,?_,
    ex.query_frame (by decide),ex.unit_work pendingVertexLevelBodyCode_wellFormed (by decide) hh,aO.trans bO,aH,?_⟩
  · change aMem.queueMass ≤ pm.queueMass+2
    rw [aMass]
    exact bMass
  · change (aMem.frames j hj).exteriorObject.keys=_
    rw [(aKeys j hj).1,bExt]
  · change (aMem.frames j hj).highObject.keys=_
    rw [(aKeys j hj).2,bHigh]
  · intro i hi he
    change (aMem.frames i hi).exteriorObject.keys=_ ∧ (aMem.frames i hi).highObject.keys=_
    rw [(aKeys i hi).1,(aKeys i hi).2]
    exact bOthers i hi he
  · change a.scalar.core.mem=_
    rw [aR,bR]

  · exact (((bFrame.trans aFrame).trans (PendingIntegerFrame.pointerWrite aMem 109 ((j+1 : ℕ) : ℤ) (by decide))).trans
      (PendingIntegerFrame.payUnit (aMem.pointerWrite 109 ((j+1 : ℕ) : ℤ) (by decide))))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndexedKeyRefresh

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma indexed_key_refresh_step (start i : ℕ) (refresh : Finset ℕ → Finset ℕ)
    (old middle final : Finset ℕ) (hMiddle : middle=if i=start then refresh old else old)
    (hFinal : final=if start+1 ≤ i then refresh middle else middle) :
    final=if start ≤ i then refresh old else old := by
  by_cases he : i=start
  · subst i
    rw [if_pos rfl] at hMiddle
    rw [if_neg (by omega)] at hFinal
    rw [if_pos (le_refl _),hFinal,hMiddle]
  · rw [if_neg he] at hMiddle
    by_cases hi : start ≤ i
    · rw [if_pos (by omega),hMiddle] at hFinal
      rw [if_pos hi]
      exact hFinal
    · rw [if_neg (by omega),hMiddle] at hFinal
      rw [if_neg hi]
      exact hFinal

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingVertexLevelLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pendingVertexLevelLoopCode_wellFormed : pendingVertexLevelLoopCode.wellFormed := pendingVertexLevelBodyCode_wellFormed

set_option maxHeartbeats 12000000 in
lemma pending_vertex_level_loop_foreign_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length N R : ℕ) (logical : RecursiveState n) (v : Fin n) (degree : ℤ)
    (hDepth : logical.top ≤ ell) (hCap : R < length) (hPow : N < 2^R)
    (hActiveDomain : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hExtDomain : ∀ i ≤ logical.top, (logical.frames i).exterior ⊆ parentDomain logical i)
    (hHighDomain : ∀ i ≤ logical.top, (logical.frames i).high ⊆ parentDomain logical i) (remaining : ℕ) :
    ∀ (index : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
      (pm : MachinePendingKeys g s α ε ell length logical st),
      index+remaining=logical.top+1 → st.scalar.core.ptrs 109=(index : ℤ) →
      st.scalar.core.ptrs 111=((logical.top+1 : ℕ) : ℤ) → st.scalar.core.ptrs 108=(logical.top : ℤ) →
      st.scalar.core.ptrs 40=(v.val : ℤ) → st.scalar.core.ptrs 118=(if v ∈ parentDomain logical index then 1 else 0) →
      st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)=degree →
      pm.queueMass+2*remaining ≤ N →
      ∃ steps out, ∃ memory : MachinePendingKeys g s α ε ell length logical out,
        MachineEval m g ω pendingVertexLevelLoopCode st steps out ∧
        steps ≤ remaining*(42*R+60*(16*(ell+3))+284)+1 ∧ memory.queueMass ≤ pm.queueMass+2*remaining ∧
        out.scalar.core.ptrs 109=((logical.top+1 : ℕ) : ℤ) ∧ out.scalar.core.ptrs 111=((logical.top+1 : ℕ) : ℤ) ∧
        out.scalar.core.ptrs 118=(if v ∈ parentDomain logical (logical.top+1) then 1 else 0) ∧
        (∀ i, ∀ hi : i ≤ logical.top,
          (memory.frames i hi).exteriorObject.keys=(if index ≤ i then
            (if v ∈ (logical.frames i).exterior then insert v.val (pm.frames i hi).exteriorObject.keys else (pm.frames i hi).exteriorObject.keys)
            else (pm.frames i hi).exteriorObject.keys)) ∧
        (∀ i, ∀ hi : i ≤ logical.top,
          (memory.frames i hi).highObject.keys=(if index ≤ i then
            (if v ∈ (logical.frames i).high then insert v.val (pm.frames i hi).highObject.keys else (pm.frames i hi).highObject.keys)
            else (pm.frames i hi).highObject.keys)) ∧
        out.scalar.core.mem=levelRealMemoryFold (pendingBooleanMemoryUpdate logical (16*(ell+3)) v degree) index remaining st.scalar.core.mem ∧
        out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧ PendingIntegerFrame pm memory := by
  let B := 42*R+60*(16*(ell+3))+282
  induction remaining with
  | zero =>
    intro index st hh pm hCount hIndex hStop hTop hVertex hFlag hDegree hBudget
    have he : index=logical.top+1 := by omega
    have ex : MachineEval m g ω pendingVertexLevelLoopCode st 1 (payUnit st) :=
      MachineEval.pointerDone hh (by rw [hStop,hIndex,he])
    refine ⟨1,payUnit st,pm.payUnit,ex,by omega,by change pm.queueMass ≤ pm.queueMass+0; omega,?_,hStop,?_,?_,?_,rfl,rfl,
      ex.unit_work pendingVertexLevelLoopCode_wellFormed (by decide) hh,rfl,hh,PendingIntegerFrame.payUnit pm⟩
    · change st.scalar.core.ptrs 109=((logical.top+1 : ℕ) : ℤ)
      simpa only [he] using hIndex
    · change st.scalar.core.ptrs 118=_
      simpa only [he] using hFlag
    · intro i hi
      rw [if_neg (by omega)]
      rfl
    · intro i hi
      rw [if_neg (by omega)]
      rfl
  | succ remaining ih =>
    intro index st hh pm hCount hIndex hStop hTop hVertex hFlag hDegree hBudget
    have hIndexLe : index ≤ logical.top := by omega
    obtain ⟨u,b,bMem,eb,hu,bMass,b109,b111,b118,bExt,bHigh,bOthers,bR,bQ,bW,bO,bH,bFrame⟩ :=
      pending_vertex_level_body_foreign_exec m g ω s α ε ell length N R logical (payUnit st) hh pm.payUnit hDepth index hIndexLe v
        (hActiveDomain index hIndexLe) (hExtDomain index hIndexLe) (hHighDomain index hIndexLe)
        hIndex hStop hTop hVertex hFlag (by change pm.queueMass ≤ N; omega) hCap hPow
    have bTop := (eb.pointer_frame 108 (by decide)).trans hTop
    have bVertex := (eb.pointer_frame 40 (by decide)).trans hVertex
    have bDegree : b.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)=degree :=
      (pm.degree_frame bMem v).trans hDegree
    have bBudget : bMem.queueMass+2*remaining ≤ N := by
      change bMem.queueMass ≤ pm.queueMass+2 at bMass
      omega
    obtain ⟨w,out,next,er,hw,cMass,c109,c111,c118,cExt,cHigh,cR,cQ,cW,cO,cH,cFrame⟩ :=
      ih (index+1) (payUnit b) bH bMem.payUnit (by omega) b109 b111 bTop bVertex b118 bDegree bBudget
    have ex : MachineEval m g ω pendingVertexLevelLoopCode st (1+u+1+w) out :=
      MachineEval.pointerNext hh (by rw [hStop,hIndex]; omega) eb er
    have bR' : b.scalar.core.mem=pendingBooleanMemoryUpdate logical (16*(ell+3)) v degree index st.scalar.core.mem :=
      bR.trans (pm.boolean_memory_update_eq index hIndexLe v degree hDegree)
    refine ⟨1+u+1+w,out,next,ex,?_,?_,c109,c111,c118,?_,?_,?_,ex.query_frame (by decide),
      ex.unit_work pendingVertexLevelLoopCode_wellFormed (by decide) hh,cO.trans bO,cH,(((PendingIntegerFrame.payUnit pm).trans bFrame).trans (PendingIntegerFrame.payUnit bMem)).trans cFrame⟩
    · have hProduct : (remaining+1)*(B+2)=remaining*(B+2)+(B+2) := by ring
      change u ≤ B at hu
      change w ≤ remaining*(B+2)+1 at hw
      change 1+u+1+w ≤ (remaining+1)*(B+2)+1
      rw [hProduct]
      omega
    · change bMem.queueMass ≤ pm.queueMass+2 at bMass
      change next.queueMass ≤ bMem.queueMass+2*remaining at cMass
      omega
    · intro i hi
      have hMiddle : (bMem.frames i hi).exteriorObject.keys=(if i=index then
          (if v ∈ (logical.frames i).exterior then insert v.val (pm.frames i hi).exteriorObject.keys else (pm.frames i hi).exteriorObject.keys)
          else (pm.frames i hi).exteriorObject.keys) := by
        by_cases he : i=index
        · subst i
          rw [if_pos rfl]
          exact bExt
        · rw [if_neg he]
          exact (bOthers i hi he).1
      have hFinal : (next.frames i hi).exteriorObject.keys=(if index+1 ≤ i then
          (if v ∈ (logical.frames i).exterior then insert v.val (bMem.frames i hi).exteriorObject.keys else (bMem.frames i hi).exteriorObject.keys)
          else (bMem.frames i hi).exteriorObject.keys) := cExt i hi
      exact indexed_key_refresh_step index i (fun Q => if v ∈ (logical.frames i).exterior then insert v.val Q else Q)
        (pm.frames i hi).exteriorObject.keys (bMem.frames i hi).exteriorObject.keys (next.frames i hi).exteriorObject.keys hMiddle hFinal
    · intro i hi
      have hMiddle : (bMem.frames i hi).highObject.keys=(if i=index then
          (if v ∈ (logical.frames i).high then insert v.val (pm.frames i hi).highObject.keys else (pm.frames i hi).highObject.keys)
          else (pm.frames i hi).highObject.keys) := by
        by_cases he : i=index
        · subst i
          rw [if_pos rfl]
          exact bHigh
        · rw [if_neg he]
          exact (bOthers i hi he).2
      have hFinal : (next.frames i hi).highObject.keys=(if index+1 ≤ i then
          (if v ∈ (logical.frames i).high then insert v.val (bMem.frames i hi).highObject.keys else (bMem.frames i hi).highObject.keys)
          else (bMem.frames i hi).highObject.keys) := cHigh i hi
      exact indexed_key_refresh_step index i (fun Q => if v ∈ (logical.frames i).high then insert v.val Q else Q)
        (pm.frames i hi).highObject.keys (bMem.frames i hi).highObject.keys (next.frames i hi).highObject.keys hMiddle hFinal
    · change out.scalar.core.mem=levelRealMemoryFold (pendingBooleanMemoryUpdate logical (16*(ell+3)) v degree)
        (index+1) remaining (pendingBooleanMemoryUpdate logical (16*(ell+3)) v degree index st.scalar.core.mem)
      change out.scalar.core.mem=levelRealMemoryFold (pendingBooleanMemoryUpdate logical (16*(ell+3)) v degree)
        (index+1) remaining b.scalar.core.mem at cR
      rw [cR,bR']

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingVertexRefresh

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pendingVertexRefreshCode_wellFormed : pendingVertexRefreshCode.wellFormed := by
  refine ⟨?_,pendingVertexLevelLoopCode_wellFormed⟩
  simp [pendingVertexRefreshInitCode,pendingVertexRefreshInitInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 7000000 in
lemma pending_vertex_refresh_foreign_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length N R : ℕ) (logical : RecursiveState n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : MachinePendingKeys g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hActiveDomain : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hExtDomain : ∀ i ≤ logical.top, (logical.frames i).exterior ⊆ parentDomain logical i)
    (hHighDomain : ∀ i ≤ logical.top, (logical.frames i).high ⊆ parentDomain logical i)
    (v : Fin n) (hVertex : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hMass : pm.queueMass+2*(logical.top+1) ≤ N) (hCap : R < length) (hPow : N < 2^R) :
    ∃ steps out, ∃ memory : MachinePendingKeys g s α ε ell length logical out,
      MachineEval m g ω pendingVertexRefreshCode st steps out ∧
      steps ≤ (logical.top+1)*(42*R+60*(16*(ell+3))+284)+6 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1) ∧
      (∀ i, ∀ hi : i ≤ logical.top,
        (memory.frames i hi).exteriorObject.keys=(if v ∈ (logical.frames i).exterior then
          insert v.val (pm.frames i hi).exteriorObject.keys else (pm.frames i hi).exteriorObject.keys)) ∧
      (∀ i, ∀ hi : i ≤ logical.top,
        (memory.frames i hi).highObject.keys=(if v ∈ (logical.frames i).high then
          insert v.val (pm.frames i hi).highObject.keys else (pm.frames i hi).highObject.keys)) ∧
      out.scalar.core.mem=levelRealMemoryFold
        (pendingBooleanMemoryUpdate logical (16*(ell+3)) v (st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)))
        0 (logical.top+1) st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧ PendingIntegerFrame pm memory := by
  let a := linearRun m g ω pendingVertexRefreshInitInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω pendingVertexRefreshInitInstructions
    (by simp [pendingVertexRefreshInitInstructions,unitInstruction,straightInstruction]) st hh
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,pendingVertexRefreshInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aR : a.scalar.core.mem=st.scalar.core.mem := by
    simp [a,linearRun,pendingVertexRefreshInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,pendingVertexRefreshInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aP : ∀ r ∈ ([0,20,50,100] : List ℕ), a.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ea.pointer_frame _ (by decide)
  have aG : ∀ r ∈ ([30,31] : List ℕ), a.scalar.core.regs r=st.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ea.real_register_frame _ (by decide)
  let aMem := pm.frame aI aR aP aG aO
  have a109 : a.scalar.core.ptrs 109=0 := by
    simp [a,linearRun,pendingVertexRefreshInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have a108 : a.scalar.core.ptrs 108=(logical.top : ℤ) := by
    simp [a,linearRun,pendingVertexRefreshInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,pm.top]
  have a111 : a.scalar.core.ptrs 111=((logical.top+1 : ℕ) : ℤ) := by
    simp [a,linearRun,pendingVertexRefreshInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,pm.top]
  have a118 : a.scalar.core.ptrs 118=(if v ∈ parentDomain logical 0 then 1 else 0) := by
    simp [a,linearRun,pendingVertexRefreshInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,parentDomain]
  obtain ⟨u,out,memory,eb,hu,bMass,b109,b111,b118,bExt,bHigh,bR,bQ,bW,bO,bH,bFrame⟩ := pending_vertex_level_loop_foreign_exec m g ω
    s α ε ell length N R logical v (st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)) hDepth hCap hPow
    hActiveDomain hExtDomain hHighDomain (logical.top+1) 0 a aH aMem (by omega) a109 a111 a108
    ((ea.pointer_frame 40 (by decide)).trans hVertex) a118 (by rw [aI]) hMass
  have ex : MachineEval m g ω pendingVertexRefreshCode st (5+u) out := MachineEval.seq ea eb
  refine ⟨5+u,out,memory,ex,by omega,bMass,?_,?_,?_,ex.query_frame (by decide),
    ex.unit_work pendingVertexRefreshCode_wellFormed (by decide) hh,bO.trans aO,bH,(PendingIntegerFrame.frame pm aI aR aP aG aO).trans bFrame⟩
  · intro i hi
    have hKeys : (aMem.frames i hi).exteriorObject.keys=(pm.frames i hi).exteriorObject.keys := rfl
    simpa only [if_pos (Nat.zero_le i),hKeys] using bExt i hi
  · intro i hi
    have hKeys : (aMem.frames i hi).highObject.keys=(pm.frames i hi).highObject.keys := rfl
    simpa only [if_pos (Nat.zero_le i),hKeys] using bHigh i hi
  · rw [bR,aR]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingArrayRefreshBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pendingArrayRefreshBodyCode_wellFormed : pendingArrayRefreshBodyCode.wellFormed := by
  refine ⟨pendingArrayRefreshReadCode_wellFormed,pendingVertexRefreshCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 12000000 in
lemma pending_array_refresh_body_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ)
    (e : Fin k → Fin n) (base : ℤ) (index : ℕ) (hi : index < k) (visited : Finset (Fin n))
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : MachinePendingKeys g s α ε ell length logical st)
    (buffer : PendingEnumerationBuffer pm base e) (inv : PendingVisitedKeys pm visited)
    (hDepth : logical.top ≤ ell)
    (hActiveDomain : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (hExtDomain : ∀ j ≤ logical.top, (logical.frames j).exterior ⊆ parentDomain logical j)
    (hHighDomain : ∀ j ≤ logical.top, (logical.frames j).high ⊆ parentDomain logical j)
    (h140 : st.scalar.core.ptrs 140=base) (h143 : st.scalar.core.ptrs 143=(index : ℤ))
    (hMass : pm.queueMass+2*(logical.top+1) ≤ N) (hCap : rank < length) (hPow : N < 2^rank) :
    ∃ steps out, ∃ memory : MachinePendingKeys g s α ε ell length logical out,
      MachineEval m g ω pendingArrayRefreshBodyCode st steps out ∧
      steps ≤ (logical.top+1)*(42*rank+60*(16*(ell+3))+284)+9 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1) ∧
      out.scalar.core.ptrs 143=((index+1 : ℕ) : ℤ) ∧
      PendingEnumerationBuffer memory base e ∧ PendingVisitedKeys memory (insert (e ⟨index,hi⟩) visited) ∧
      PendingIntegerFrame pm memory ∧ out.work=st.work+steps ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let i : Fin k := ⟨index,hi⟩
  obtain ⟨a,ea,a40,aI,aR,aW,aO,aH⟩ := pending_array_refresh_read_exec m g ω base index (e i) st hh h140 h143 (buffer.stored i)
  have aP : ∀ r ∈ ([0,20,50,100] : List ℕ), a.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ea.pointer_frame _ (by decide)
  have aG : ∀ r ∈ ([30,31] : List ℕ), a.scalar.core.regs r=st.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ea.real_register_frame _ (by decide)
  let am := pm.frame aI aR aP aG aO
  have aFrame : PendingIntegerFrame pm am := PendingIntegerFrame.frame pm aI aR aP aG aO
  have aInv : PendingVisitedKeys am visited := inv.frame aI aR aP aG aO
  obtain ⟨u,b,bm,eb,hu,bMass,bExt,bHigh,bR,bQuery,bW,bO,bH,bFrame⟩ :=
    pending_vertex_refresh_foreign_exec m g ω s α ε ell length N rank logical a aH am hDepth
      hActiveDomain hExtDomain hHighDomain (e i) a40 hMass hCap hPow
  have bInv := aInv.after_vertex hDepth (e i) bExt bHigh bR
  have b143 := (eb.pointer_frame 143 (by decide)).trans ((ea.pointer_frame 143 (by decide)).trans h143)
  let pointer := bm.pointerWrite 143 ((index+1 : ℕ) : ℤ) (by simp)
  let memory := pointer.payUnit
  let out := payUnit (pointerWrite b 143 ((index+1 : ℕ) : ℤ))
  have ec : MachineEval m g ω (coreCode (.pinc 143)) b 1 out := by
    simpa only [coreCode,b143,Nat.cast_add,Nat.cast_one,out] using pinc_eval m g ω b 143 bH
  have tailFrame : PendingIntegerFrame bm memory :=
    (PendingIntegerFrame.pointerWrite bm 143 ((index+1 : ℕ) : ℤ) (by simp)).trans (PendingIntegerFrame.payUnit pointer)
  have totalFrame := (aFrame.trans bFrame).trans tailFrame
  have ex : MachineEval m g ω pendingArrayRefreshBodyCode st (2+(u+1)) out := MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨_,out,memory,ex,by omega,bMass,?_,buffer.frame totalFrame,?_,totalFrame,
    ex.unit_work pendingArrayRefreshBodyCode_wellFormed (by decide) hh,
    (ec.query_frame (by decide)).trans (bQuery.trans (ea.query_frame (by decide))),bO.trans aO,bH⟩
  · simp [out,payUnit,pcSet,pointerWrite]
  · exact (bInv.pointerWrite 143 ((index+1 : ℕ) : ℤ) (by simp)).payUnit

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingArrayRefreshLoop

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 16000000 in
lemma pending_array_refresh_loop_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ)
    (e : Fin k → Fin n) (base : ℤ) (remaining : ℕ)
    (hDepth : logical.top ≤ ell)
    (hActiveDomain : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (hExtDomain : ∀ j ≤ logical.top, (logical.frames j).exterior ⊆ parentDomain logical j)
    (hHighDomain : ∀ j ≤ logical.top, (logical.frames j).high ⊆ parentDomain logical j)
    (hCap : rank < length) (hPow : N < 2^rank) :
    ∀ (index : ℕ) (hCount : index+remaining=k) (visited : Finset (Fin n))
      (st : MachineState) (hh : st.scalar.halted=false)
      (pm : MachinePendingKeys g s α ε ell length logical st),
      PendingEnumerationBuffer pm base e → PendingVisitedKeys pm visited →
      (∀ v ∉ Finset.univ.image e, v ∈ visited) →
      (∀ i : Fin k, i.val < index → e i ∈ visited) →
      st.scalar.core.ptrs 140=base → st.scalar.core.ptrs 142=(k : ℤ) → st.scalar.core.ptrs 143=(index : ℤ) →
      pm.queueMass+2*(logical.top+1)*remaining ≤ N →
      ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
        MachineEval m g ω pendingArrayRefreshLoopCode st steps out ∧
        steps ≤ remaining*((logical.top+1)*(42*rank+60*(16*(ell+3))+284)+11)+1 ∧
        memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*remaining ∧
        PendingIntegerFrame pm (MachinePendingKeys.ofMemory memory) ∧
        out.work=st.work+steps ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  classical
  let B := (logical.top+1)*(42*rank+60*(16*(ell+3))+284)+11
  let Q := 2*(logical.top+1)
  induction remaining with
  | zero =>
    intro index hCount visited st hh pm buffer inv hOutside hPast h140 h142 h143 hMass
    have hi : index=k := by omega
    have hAll : visited=Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro v
      by_cases hv : v ∈ Finset.univ.image e
      · obtain ⟨i,hiMem,rfl⟩ := Finset.mem_image.mp hv
        exact hPast i (by rw [hi]; exact i.isLt)
      · exact hOutside v hv
    let memory := inv.payUnit.finish hAll
    have ex : MachineEval m g ω pendingArrayRefreshLoopCode st 1 (payUnit st) :=
      MachineEval.pointerDone hh (by rw [h142,h143,hi])
    refine ⟨1,payUnit st,memory,ex,by omega,?_,?_,
      ex.unit_work pendingArrayRefreshBodyCode_wellFormed (by decide) hh,rfl,rfl,hh⟩
    · change memory.queueMass ≤ pm.queueMass+0
      rw [inv.payUnit.finish_mass hAll]
      change pm.queueMass ≤ pm.queueMass
      exact le_rfl
    · exact (PendingIntegerFrame.payUnit pm).trans (inv.payUnit.finish_frame hAll)
  | succ remaining ih =>
    intro index hCount visited st hh pm buffer inv hOutside hPast h140 h142 h143 hMass
    have hi : index < k := by omega
    have hBudget : pm.queueMass+Q*remaining+Q ≤ N := by
      change pm.queueMass+Q*(remaining+1) ≤ N at hMass
      rw [Nat.mul_succ] at hMass
      omega
    have hOneBudget : pm.payUnit.queueMass+2*(logical.top+1) ≤ N := by change pm.queueMass+Q ≤ N; omega
    obtain ⟨u,mid,midMemory,eb,hu,hMidMass,hm143,hmBuffer,hmInv,hmFrame,hmW,hmQuery,hmO,hmH⟩ :=
      pending_array_refresh_body_exec m g ω logical s α ε ell length N rank e base index hi visited (payUnit st) hh pm.payUnit
        (buffer.frame (PendingIntegerFrame.payUnit pm)) inv.payUnit hDepth hActiveDomain hExtDomain hHighDomain h140 h143 hOneBudget hCap hPow
    have hm140 := (eb.pointer_frame 140 (by decide)).trans h140
    have hm142 := (eb.pointer_frame 142 (by decide)).trans h142
    have hOutsideNew : ∀ v ∉ Finset.univ.image e, v ∈ insert (e ⟨index,hi⟩) visited := by
      intro v hv
      exact Finset.mem_insert_of_mem (hOutside v hv)
    have hPastNew : ∀ i : Fin k, i.val < index+1 → e i ∈ insert (e ⟨index,hi⟩) visited := by
      intro i hlt
      by_cases he : i.val=index
      · have he' : i=⟨index,hi⟩ := Fin.ext he
        rw [he']
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hPast i (by omega))
    have hMassRec : midMemory.payUnit.queueMass+2*(logical.top+1)*remaining ≤ N := by
      change midMemory.queueMass+Q*remaining ≤ N
      change midMemory.queueMass ≤ pm.queueMass+Q at hMidMass
      omega
    obtain ⟨v,out,memory,er,hv,hMassOut,hFrameOut,hW,hQuery,hO,hH⟩ := ih (index+1) (by omega)
      (insert (e ⟨index,hi⟩) visited) (payUnit mid) hmH midMemory.payUnit
      (hmBuffer.frame (PendingIntegerFrame.payUnit midMemory)) hmInv.payUnit hOutsideNew hPastNew hm140 hm142 hm143 hMassRec
    have ex : MachineEval m g ω pendingArrayRefreshLoopCode st (1+u+1+v) out :=
      MachineEval.pointerNext hh (by rw [h142,h143]; omega) eb er
    refine ⟨_,out,memory,ex,?_,?_,
      (((PendingIntegerFrame.payUnit pm).trans hmFrame).trans (PendingIntegerFrame.payUnit midMemory)).trans hFrameOut,
      ex.unit_work pendingArrayRefreshBodyCode_wellFormed (by decide) hh,hQuery.trans hmQuery,hO.trans hmO,hH⟩
    · change 1+u+1+v ≤ (remaining+1)*B+1
      change v ≤ remaining*B+1 at hv
      have hBody : u+2 ≤ B := by dsimp only [B]; omega
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · change memory.queueMass ≤ pm.queueMass+Q*(remaining+1)
      change memory.queueMass ≤ midMemory.queueMass+Q*remaining at hMassOut
      change midMemory.queueMass ≤ pm.queueMass+Q at hMidMass
      rw [Nat.mul_succ]
      omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingArrayRefreshExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pendingArrayRefreshCode_wellFormed : pendingArrayRefreshCode.wellFormed := by
  refine ⟨?_,pendingArrayRefreshBodyCode_wellFormed⟩
  simp [pendingArrayRefreshInitRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 12000000 in
lemma pending_array_refresh_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ)
    (e : Fin k → Fin n) (base : ℤ) (visited : Finset (Fin n))
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : MachinePendingKeys g s α ε ell length logical st)
    (buffer : PendingEnumerationBuffer pm base e) (inv : PendingVisitedKeys pm visited)
    (hDepth : logical.top ≤ ell)
    (hActiveDomain : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (hExtDomain : ∀ j ≤ logical.top, (logical.frames j).exterior ⊆ parentDomain logical j)
    (hHighDomain : ∀ j ≤ logical.top, (logical.frames j).high ⊆ parentDomain logical j)
    (hOutside : ∀ v ∉ Finset.univ.image e, v ∈ visited)
    (h80 : st.scalar.core.ptrs 80=base) (h77 : st.scalar.core.ptrs 77=(k : ℤ))
    (hMass : pm.queueMass+2*(logical.top+1)*k ≤ N) (hCap : rank < length) (hPow : N < 2^rank) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω pendingArrayRefreshCode st steps out ∧
      steps ≤ k*((logical.top+1)*(42*rank+60*(16*(ell+3))+284)+11)+4 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*k ∧
      PendingIntegerFrame pm (MachinePendingKeys.ofMemory memory) ∧
      out.work=st.work+steps ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,ep,hP,hI,hR,hW,hO,hH⟩ := pendingArrayRefreshInitRoutine.execute m g ω st hh
  have ep3 : MachineEval m g ω pendingArrayRefreshInitRoutine.code st 3 pre := ep
  have h140 : pre.scalar.core.ptrs 140=base := by
    rw [hP]; simp [pendingArrayRefreshInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,h80]
  have h142 : pre.scalar.core.ptrs 142=(k : ℤ) := by
    rw [hP]; simp [pendingArrayRefreshInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,h77]
  have h143 : pre.scalar.core.ptrs 143=0 := by
    rw [hP]; simp [pendingArrayRefreshInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result]
  have hPtrs : ∀ r ∈ ([0,20,50,100] : List ℕ), pre.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ep.pointer_frame _ (by decide)
  have hRegs : ∀ r ∈ ([30,31] : List ℕ), pre.scalar.core.regs r=st.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ep.real_register_frame _ (by decide)
  let preMemory := pm.frame hI hR hPtrs hRegs hO
  have preFrame : PendingIntegerFrame pm preMemory := PendingIntegerFrame.frame pm hI hR hPtrs hRegs hO
  obtain ⟨u,out,memory,eb,hu,hMassOut,hFrameOut,hWork,hQuery,hOutput,hHalt⟩ := pending_array_refresh_loop_exec m g ω logical s α ε ell length N rank e base k
    hDepth hActiveDomain hExtDomain hHighDomain hCap hPow 0 (by omega) visited pre hH preMemory
      (buffer.frame preFrame) (inv.frame hI hR hPtrs hRegs hO) hOutside (by intros; omega) h140 h142 h143 hMass
  have ex : MachineEval m g ω pendingArrayRefreshCode st (3+u) out := MachineEval.seq ep3 eb
  exact ⟨_,out,memory,ex,by omega,hMassOut,preFrame.trans hFrameOut,
    ex.unit_work pendingArrayRefreshCode_wellFormed (by decide) hh,hQuery.trans (ep.query_frame (by decide)),hOutput.trans hO,hHalt⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushOutputRead

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pushOutputReadCode_wellFormed : pushOutputReadCode.wellFormed := by
  simp [pushOutputReadCode,pushOutputReadInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.RecursiveMachineSolveFrame

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section


def RecursiveMachineMemory.solve_frame {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hI : ∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 → out.scalar.integerMemory z=st.scalar.integerMemory z)
    (hV : ∀ v : Fin n, ∀ field < 16*(ell+3), field ≠ 7 → field ≠ 8 →
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field))
    (hR : ∀ z, z < st.scalar.core.ptrs 20 → out.scalar.core.mem z=st.scalar.core.mem z)
    (hP : ∀ r ∈ ([0,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : RecursiveMachineMemory g s α ε ell length logical out := by
  have hFloor := pm.allocator
  have hBase : 0 ≤ st.scalar.core.ptrs 20 := by omega
  have hHead : ∀ j ≤ logical.top, ∀ slot < 32,
      0 ≤ levelHeaderAddress j slot ∧ levelHeaderAddress j slot < st.scalar.core.ptrs 20 := by
    intro j hj slot hs
    unfold levelHeaderAddress
    have hjE : j ≤ ell := hj.trans hDepth
    omega
  have hNeg : ∀ v : Fin n, ∀ field, vertexRecordAddress (16*(ell+3)) v.val field < st.scalar.core.ptrs 20 :=
    fun v field => (vertexRecordAddress_negative _ _ _).trans_le hBase
  let frames := fun j hj => (pm.frames j hj).scoped_frame hFree
    (fun slot hs => hI _ (hHead j hj slot hs).1 (hHead j hj slot hs).2)
    (fun slot hs => hR _ (hHead j hj slot hs).2)
    (by
      intro v hv field hf hScope
      have hjE : j ≤ ell := hj.trans hDepth
      apply hV v field (by omega) <;> omega)
    (fun v hv field hf hScope => hR _ (hNeg v field))
    (fun z hz => hI z (by have := (pm.frames j hj).owned_above z hz; omega) ((pm.frames j hj).owned_below z hz))
  have hCache : GraphCache g out.scalar.integerMemory (16*(ell+3)) logical.stored (st.scalar.core.ptrs 20) := by
    apply pm.graphCache.frame g _ _ _ _ _
    · intro v field hf
      exact hV v field (by omega) (by omega) (by omega)
    · intro v hv i hi
      apply hI
      · have := pm.graphCache.basePositive v hv
        have := Int.natCast_nonneg i
        omega
      · exact pm.graphCache.belowFree v hv i hi
  refine {
    zero := (hP 0 (by simp)).trans pm.zero
    top := (hP 100 (by simp)).trans pm.top
    width := (hP 50 (by simp)).trans pm.width
    alphaRegister := (hG 30 (by simp)).trans pm.alphaRegister
    one := (hG 31 (by simp)).trans pm.one
    alphaMemory := (hR 0 (by omega)).trans pm.alphaMemory
    epsilonMemory := (hR 1 (by omega)).trans pm.epsilonMemory
    depthMemory := (hI 2 (by omega) (by omega)).trans pm.depthMemory
    lengthMemory := (hI 5 (by omega) (by omega)).trans pm.lengthMemory
    seedMemory := (hI 0 (by omega) (by omega)).trans pm.seedMemory
    allocator := hFloor.trans hFree
    potential := fun v => (hR _ (hNeg v 0)).trans (pm.potential v)
    seedMarker := fun v => (hR _ (hNeg v 2)).trans (pm.seedMarker v)
    boundary := (hI 7 (by omega) (by omega)).trans pm.boundary
    graphCache := hCache.mono_free hFree
    rowAbove := fun v hv => by rw [hV v 1 (by omega) (by omega) (by omega)]; exact pm.rowAbove v hv
    knownDegree := fun v hv => (hV v 0 (by omega) (by omega) (by omega)).trans (pm.knownDegree v hv)
    unknownDegree := fun v hv => (hV v 0 (by omega) (by omega) (by omega)).trans (pm.unknownDegree v hv)
    frames := frames
    pieceSeparation := pm.pieceSeparation
    frameSeparation := pm.frameSeparation
    cacheSeparation := ?_
    output := hO.trans pm.output
  }
  intro j hj
  change Disjoint (pm.frames j hj).owned (cachedRowCells g out.scalar.integerMemory (16*(ell+3)) logical.stored)
  rw [cached_row_cells_congr g logical.stored (16*(ell+3)) st.scalar.integerMemory out.scalar.integerMemory
    (fun v hv => hV v 1 (by omega) (by omega) (by omega))]
  exact pm.cacheSeparation j hj

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexEnumerationMemory

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 4000000 in
lemma vertex_enumeration_memory_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (vertices : List (Fin n)) (head : ℤ) (F : Finset ℤ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hhp : st.scalar.core.ptrs 90=head)
    (h : VertexListRep st.scalar.integerMemory head vertices F)
    (hbelow : ∀ z ∈ F, z < st.scalar.core.ptrs 20) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω vertexEnumerationCode st (10*vertices.length+5) out ∧
      out.scalar.core.ptrs 80=st.scalar.core.ptrs 20 ∧ out.scalar.core.ptrs 77=(vertices.length : ℤ) ∧
      out.scalar.core.ptrs 20=st.scalar.core.ptrs 20+(vertices.length : ℤ) ∧
      EnumerationStored out.scalar.integerMemory (st.scalar.core.ptrs 20) (vertexEnumeration vertices) ∧
      (∀ i : Fin vertices.length, st.scalar.core.ptrs 20+(i.val : ℤ) < out.scalar.core.ptrs 20) ∧
      (∀ i : Fin vertices.length, ∀ j, ∀ hj : j ≤ logical.top,
        st.scalar.core.ptrs 20+(i.val : ℤ) ∉ (memory.frames j hj).owned) ∧
      memory.queueMass=pm.queueMass ∧
      (∀ z, z < st.scalar.core.ptrs 20 → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+(10*vertices.length+5 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨out,ex,h80,h77,h20,hEnum,hI,hR,hQ,hWork,hOutput,hHalt⟩ :=
    vertex_enumeration_exec m g ω vertices head (st.scalar.core.ptrs 20) F st hh pm.zero hhp rfl h hbelow
  have hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 := by rw [h20]; omega
  have hBase : 0 ≤ st.scalar.core.ptrs 20 := by have := pm.allocator; omega
  let memory := pm.solve_frame hDepth hFree
    (fun z hz hlt => hI z hlt)
    (fun v field hf hf7 hf8 => hI _ ((vertexRecordAddress_negative _ _ _).trans_le hBase))
    (fun z hz => congrFun hR z)
    (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> exact ex.pointer_frame _ (by decide))
    (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> exact ex.real_register_frame _ (by decide)) hOutput
  refine ⟨out,memory,ex,h80,h77,h20,hEnum,?_,?_,rfl,hI,hR,hWork,hOutput,hHalt⟩
  · intro i
    rw [h20]
    have := i.isLt
    omega
  · intro i j hj hz
    have hOld : st.scalar.core.ptrs 20+(i.val : ℤ) ∈ (pm.frames j hj).owned := hz
    have hLt := (pm.frames j hj).owned_below _ hOld
    have := Int.natCast_nonneg i.val
    omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameResidualSumPrelude

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameResidualSumPreludeCode_wellFormed : frameResidualSumPreludeCode.wellFormed := by
  refine ⟨levelHeaderIntegerToCode_wellFormed 1 94,?_,?_⟩ <;>
    simp [frameResidualSumPointerRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
      coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨0,by norm_num⟩

set_option maxHeartbeats 4000000 in
lemma frame_residual_sum_prelude_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (level width : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (h100 : st.scalar.core.ptrs 100=(level : ℤ)) (h50 : st.scalar.core.ptrs 50=(width : ℤ)) :
    ∃ out, MachineEval m g ω frameResidualSumPreludeCode st 19 out ∧
      out.scalar.core.ptrs 94=st.scalar.integerMemory (levelHeaderAddress level 1) ∧
      out.scalar.core.ptrs 83=((16*(level+1)+1 : ℕ) : ℤ) ∧ out.scalar.core.ptrs 41=(width : ℤ) ∧
      out.scalar.core.regs 70=0 ∧ out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+19 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a94,aI,aR,aW,aO,aH⟩ := level_header_integer_to_exec m g ω st hh level 1 94 h100
  have a100 := (ea.pointer_frame 100 (by decide)).trans h100
  have a50 := (ea.pointer_frame 50 (by decide)).trans h50
  obtain ⟨b,eb,bP,bI,bR,bW,bO,bH⟩ := frameResidualSumPointerRoutine.execute m g ω a aH
  have eb8 : MachineEval m g ω frameResidualSumPointerRoutine.code a 8 b := eb
  have b83 : b.scalar.core.ptrs 83=((16*(level+1)+1 : ℕ) : ℤ) := by
    rw [bP]
    simp [frameResidualSumPointerRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,a100]
    ring
  have b41 : b.scalar.core.ptrs 41=(width : ℤ) := by
    rw [bP]
    simp [frameResidualSumPointerRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,a50]
  let out := payUnit (realWrite b 70 0)
  have ec : MachineEval m g ω (coreCode (.const 70 0)) b 1 out := const_eval m g ω b 70 0 bH
  have ex : MachineEval m g ω frameResidualSumPreludeCode st 19 out := MachineEval.seq ea (MachineEval.seq eb8 ec)
  refine ⟨out,ex,?_,b83,b41,?_,bI.trans aI,bR.trans aR,?_,bO.trans aO,bH⟩
  · exact (ec.pointer_frame 94 (by decide)).trans ((eb.pointer_frame 94 (by decide)).trans a94)
  · simp [out,payUnit,pcSet,realWrite]
  · change b.work+1= _
    rw [bW,aW]
    change st.work+10+8+1= _
    norm_num; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexResidualSumBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexResidualSumBodyCode_wellFormed : vertexResidualSumBodyCode.wellFormed := by
  refine ⟨pushOutputReadCode_wellFormed,?_,?_,?_⟩ <;>
    simp [coreCode,vertexRealLoadCode,vertexAddressCode_wellFormed,MachineCode.wellFormed,
      straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 5000000 in
lemma vertex_residual_sum_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width offset : ℕ) (head next : ℤ) (v : Fin n) (r : ℝ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (h41 : st.scalar.core.ptrs 41=(width : ℤ))
    (h83 : st.scalar.core.ptrs 83=(offset : ℤ)) (h94 : st.scalar.core.ptrs 94=head)
    (hKey : st.scalar.integerMemory head=(v.val : ℤ)) (hNext : st.scalar.integerMemory (head+2)=next)
    (hValue : st.scalar.core.mem (vertexRecordAddress width v.val offset)=r) :
    ∃ out, MachineEval m g ω vertexResidualSumBodyCode st (4*width+15) out ∧
      out.scalar.core.ptrs 94=next ∧ out.scalar.core.regs 70=st.scalar.core.regs 70+r ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*width+15 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a40,a94,a44,aI,aR,aQ,aW,aO,aH⟩ := push_output_read_exec m g ω st hh head next v h94 hKey hNext
  have a83 := (ea.pointer_frame 83 (by decide)).trans h83
  let b := payUnit (pointerWrite a 44 (offset : ℤ))
  have eb : MachineEval m g ω (coreCode (.pcopy 44 83)) a 1 b := by
    simpa only [coreCode,a83,b] using pcopy_eval m g ω a 44 83 aH
  have b44 : b.scalar.core.ptrs 44=(offset : ℤ) := by simp [b,payUnit,pcSet,pointerWrite]
  have b0 := (eb.pointer_frame 0 (by decide)).trans ((ea.pointer_frame 0 (by decide)).trans h0)
  have b40 := (eb.pointer_frame 40 (by decide)).trans a40
  have b41 := (eb.pointer_frame 41 (by decide)).trans ((ea.pointer_frame 41 (by decide)).trans h41)
  obtain ⟨c,ec,c10,cI,cR,cW,cO,cH⟩ := vertex_real_load_exec m g ω b aH width v.val offset b0 b40 b41 b44
  have cValue : c.scalar.core.regs 10=r := by rw [c10]; change a.scalar.core.mem _=r; rw [aR]; exact hValue
  have c70 : c.scalar.core.regs 70=st.scalar.core.regs 70 :=
    (ec.real_register_frame 70 (by decide)).trans ((eb.real_register_frame 70 (by decide)).trans (ea.real_register_frame 70 (by decide)))
  let out := payUnit (realWrite c 70 (st.scalar.core.regs 70+r))
  have ed : MachineEval m g ω (coreCode (.add 70 70 10)) c 1 out := by
    simpa only [coreCode,RealOperation.instruction,RealOperation.value,cValue,c70,out] using binary_eval m g ω c .add 70 70 10 cH
  have ex : MachineEval m g ω vertexResidualSumBodyCode st (4*width+15) out := by
    have ee := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
    convert ee using 1 <;> (first | rfl | ring)
  refine ⟨out,ex,?_,?_,cI.trans aI,cR.trans aR,ex.query_frame (by decide),?_,cO.trans aO,cH⟩
  · exact (ed.pointer_frame 94 (by decide)).trans ((ec.pointer_frame 94 (by decide)).trans ((eb.pointer_frame 94 (by decide)).trans a94))
  · simp [out,payUnit,pcSet,realWrite]
  · change c.work+1= _
    rw [cW]
    change a.work+1+(4*width+7 : ℕ)+1= _
    rw [aW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexResidualSumLoop

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 6500000 in
lemma vertex_residual_sum_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width offset : ℕ) (vertices : List (Fin n)) (head : ℤ) (F : Finset ℤ) (r : Fin n → ℝ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (h41 : st.scalar.core.ptrs 41=(width : ℤ))
    (h83 : st.scalar.core.ptrs 83=(offset : ℤ)) (h94 : st.scalar.core.ptrs 94=head)
    (hList : VertexListRep st.scalar.integerMemory head vertices F)
    (hValues : ∀ v ∈ vertices, st.scalar.core.mem (vertexRecordAddress width v.val offset)=r v) :
    ∃ out, MachineEval m g ω vertexResidualSumLoopCode st ((4*width+17)*vertices.length+1) out ∧
      out.scalar.core.regs 70=st.scalar.core.regs 70+(vertices.map r).sum ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+((4*width+17)*vertices.length+1 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  induction vertices generalizing st head F with
  | nil =>
    have hHead : st.scalar.core.ptrs 94=0 := h94.trans hList.nil.1
    refine ⟨payUnit st,MachineEval.pointerDone hh (by rw [hHead,h0]),?_,rfl,rfl,rfl,by simp,rfl,hh⟩
    simp [payUnit,pcSet]
  | cons v vertices ih =>
    obtain ⟨next,S,hPos,hKey,hChild,hNext,hTail,hF,hSep⟩ := hList.cons_view
    obtain ⟨mid,eb,hm94,hm70,hmI,hmR,hmQ,hmW,hmO,hmH⟩ := vertex_residual_sum_body_exec m g ω width offset head next v (r v)
      (payUnit st) hh h0 h41 h83 h94 hKey hNext (hValues v (by simp))
    have hm0 := (eb.pointer_frame 0 (by decide)).trans h0
    have hm41 := (eb.pointer_frame 41 (by decide)).trans h41
    have hm83 := (eb.pointer_frame 83 (by decide)).trans h83
    have hmList : VertexListRep mid.scalar.integerMemory next vertices S := by rw [hmI]; exact hTail
    have hmValues : ∀ u ∈ vertices, mid.scalar.core.mem (vertexRecordAddress width u.val offset)=r u := by
      intro u hu
      rw [hmR]
      exact hValues u (by simp [hu])
    obtain ⟨out,er,ho70,hoI,hoR,hoQ,hoW,hoO,hoH⟩ := ih next S (payUnit mid) hmH hm0 hm41 hm83 hm94 hmList hmValues
    have ex : MachineEval m g ω vertexResidualSumLoopCode st ((4*width+17)*(v::vertices).length+1) out := by
      have ee := MachineEval.pointerNext (r:=94) (s:=0) hh (by rw [h94,h0]; omega) eb er
      convert ee using 1 <;> (first | rfl | simp only [List.length_cons]; ring)
    refine ⟨out,ex,?_,hoI.trans hmI,hoR.trans hmR,hoQ.trans hmQ,?_,hoO.trans hmO,hoH⟩
    · rw [ho70]
      change mid.scalar.core.regs 70+_= _
      rw [hm70]
      simp only [payUnit_regs,List.map_cons,List.sum_cons]
      ring
    · rw [hoW,payUnit_work,hmW,payUnit_work]
      simp only [List.length_cons]
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameResidualSumExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameResidualSumCode_wellFormed : frameResidualSumCode.wellFormed :=
  ⟨frameResidualSumPreludeCode_wellFormed,vertexResidualSumBodyCode_wellFormed⟩

set_option maxHeartbeats 7000000 in
lemma frame_residual_sum_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hSubset : (logical.frames logical.top).active ⊆ parentDomain logical logical.top) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω frameResidualSumCode st
        ((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+20) out ∧
      out.scalar.core.regs 70=∑ v ∈ (logical.frames logical.top).active, (logical.frames logical.top).residual v ∧
      memory.queueMass=pm.queueMass ∧
      out.work=st.work+((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+20 : ℕ) ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let f := pm.frames logical.top le_rfl
  obtain ⟨pre,ep,h94,h83,h41,h70,hI,hR,hW,hO,hH⟩ := frame_residual_sum_prelude_exec m g ω logical.top (16*(ell+3)) st hh pm.top pm.width
  have h0 := (ep.pointer_frame 0 (by decide)).trans pm.zero
  have hList : VertexListRep pre.scalar.integerMemory (st.scalar.integerMemory (levelHeaderAddress logical.top 1)) f.activeVertices f.activeFoot := by
    rw [hI]
    exact f.activeRep
  have hValues : ∀ v ∈ f.activeVertices,
      pre.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+1))=(logical.frames logical.top).residual v := by
    intro v hv
    rw [hR]
    apply f.residual
    apply hSubset
    rw [←f.activeSet]
    exact List.mem_toFinset.mpr hv
  obtain ⟨out,el,ho70,hoI,hoR,hoQ,hoW,hoO,hoH⟩ := vertex_residual_sum_loop_exec m g ω (16*(ell+3)) (16*(logical.top+1)+1)
    f.activeVertices (st.scalar.integerMemory (levelHeaderAddress logical.top 1)) f.activeFoot (logical.frames logical.top).residual
    pre hH h0 h41 h83 h94 hList hValues
  have hLength : f.activeVertices.length=(logical.frames logical.top).active.card := by
    rw [←f.activeSet,List.toFinset_card_of_nodup f.activeNodup]
  have hSum : (f.activeVertices.map (logical.frames logical.top).residual).sum=
      ∑ v ∈ (logical.frames logical.top).active, (logical.frames logical.top).residual v := by
    rw [←f.activeSet]
    exact (List.sum_toFinset _ f.activeNodup).symm
  have ex : MachineEval m g ω frameResidualSumCode st
      ((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+20) out := by
    have ee := MachineEval.seq ep el
    rw [hLength] at ee
    convert ee using 1 <;> (first | rfl | omega)
  have hFinalI : out.scalar.integerMemory=st.scalar.integerMemory := hoI.trans hI
  have hFinalR : out.scalar.core.mem=st.scalar.core.mem := hoR.trans hR
  have hFinalO : out.output=st.output := hoO.trans hO
  let memory := pm.frame hFinalI hFinalR
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> exact ex.pointer_frame _ (by decide))
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl <;> exact ex.real_register_frame _ (by decide)) hFinalO
  refine ⟨out,memory,ex,?_,rfl,?_,ex.query_frame (by decide),hFinalO,hoH⟩
  · rw [ho70,h70,hSum,zero_add]
  · rw [hoW,hW,hLength]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeMaximumExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma episodeMaximumCode_wellFormed : episodeMaximumCode.wellFormed := by
  simp [episodeMaximumCode,coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 5000000 in
lemma episode_maximum_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (mu qb : ℝ) (st : MachineState) (hh : st.scalar.halted=false)
    (h70 : st.scalar.core.regs 70=mu) (h73 : st.scalar.core.regs 73=qb) (h31 : st.scalar.core.regs 31=1) :
    ∃ steps out, MachineEval m g ω episodeMaximumCode st steps out ∧ steps ≤ 4 ∧
      out.scalar.core.regs 75=max mu qb ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let mid := payUnit (realWrite st 74 (mu-qb))
  have ea : MachineEval m g ω (coreCode (.sub 74 70 73)) st 1 mid := by
    simpa only [coreCode,RealOperation.instruction,RealOperation.value,h70,h73,mid] using binary_eval m g ω st .sub 74 70 73 hh
  have hm74 : mid.scalar.core.regs 74=mu-qb := by simp [mid,payUnit,pcSet,realWrite]
  have hm31 := (ea.real_register_frame 31 (by decide)).trans h31
  have hm70 := (ea.real_register_frame 70 (by decide)).trans h70
  have hm73 := (ea.real_register_frame 73 (by decide)).trans h73
  by_cases hLe : mu ≤ qb
  · let out := payUnit (realWrite (payUnit mid) 75 qb)
    have eb : MachineEval m g ω (coreCode (.mul 75 73 31)) (payUnit mid) 1 out := by
      simpa only [coreCode,RealOperation.instruction,RealOperation.value,payUnit_regs,hm73,hm31,mul_one,out] using
        binary_eval m g ω (payUnit mid) .mul 75 73 31 hh
    have ex : MachineEval m g ω episodeMaximumCode st 3 out :=
      MachineEval.seq ea (MachineEval.realNonpos hh (by rw [hm74]; linarith) eb)
    refine ⟨3,out,ex,by omega,?_,rfl,rfl,ex.unit_work episodeMaximumCode_wellFormed (by decide) hh,rfl,hh⟩
    simp [out,payUnit,pcSet,realWrite,max_eq_right hLe]
  · let b := payUnit (realWrite (payUnit mid) 75 mu)
    let out := payUnit b
    have eb : MachineEval m g ω (coreCode (.mul 75 70 31)) (payUnit mid) 1 b := by
      simpa only [coreCode,RealOperation.instruction,RealOperation.value,payUnit_regs,hm70,hm31,mul_one,b] using
        binary_eval m g ω (payUnit mid) .mul 75 70 31 hh
    have ex : MachineEval m g ω episodeMaximumCode st 4 out :=
      MachineEval.seq ea (MachineEval.realPos hh (by rw [hm74]; linarith) eb)
    refine ⟨4,out,ex,le_rfl,?_,rfl,rfl,ex.unit_work episodeMaximumCode_wellFormed (by decide) hh,rfl,hh⟩
    simp [out,b,payUnit,pcSet,realWrite,max_eq_left (le_of_not_ge hLe)]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeBudgetScalarExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma episodeBudgetProductCode_wellFormed : episodeBudgetProductCode.wellFormed := by
  simp [episodeBudgetProductCode,episodeBudgetProductInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma episodeBudgetScalarCode_wellFormed : episodeBudgetScalarCode.wellFormed := by
  refine ⟨levelHeaderRealToCode_wellFormed 1 71,levelHeaderIntegerToCode_wellFormed 14 180,
    episodeBudgetProductCode_wellFormed,episodeMaximumCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 3000000 in
lemma episode_budget_product_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (q : ℝ) (block : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (h71 : st.scalar.core.regs 71=q) (h180 : st.scalar.core.ptrs 180=(block : ℤ)) :
    ∃ out, MachineEval m g ω episodeBudgetProductCode st 2 out ∧ out.scalar.core.regs 72=(block : ℝ) ∧
      out.scalar.core.regs 73=q*(block : ℝ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+2 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω episodeBudgetProductInstructions
    (by simp [episodeBudgetProductInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,episodeBudgetProductInstructions,atomState,machineStep,pcSet,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,h71,h180]

set_option maxHeartbeats 7500000 in
lemma episode_budget_scalar_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (level block : ℕ) (q mu : ℝ) (st : MachineState) (hh : st.scalar.halted=false)
    (h100 : st.scalar.core.ptrs 100=(level : ℤ)) (h31 : st.scalar.core.regs 31=1)
    (hQ : st.scalar.core.mem (levelHeaderAddress level 1)=q)
    (hBlock : st.scalar.integerMemory (levelHeaderAddress level 14)=(block : ℤ))
    (hMu : st.scalar.core.regs 70=mu) :
    ∃ steps out, MachineEval m g ω episodeBudgetScalarCode st steps out ∧ steps ≤ 27 ∧
      out.scalar.core.regs 75=max mu (q*(block : ℝ)) ∧
      out.scalar.core.regs 76=max mu (q*(block : ℝ))/(block : ℝ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a71,aI,aR,aW,aO,aH⟩ := level_header_real_to_exec m g ω st hh level 1 71 h100 h31
  have a100 := (ea.pointer_frame 100 (by decide)).trans h100
  have a71' := a71.trans hQ
  obtain ⟨b,eb,b180,bI,bR,bW,bO,bH⟩ := level_header_integer_to_exec m g ω a aH level 14 180 a100
  have b180' : b.scalar.core.ptrs 180=(block : ℤ) := by rw [b180,aI]; exact hBlock
  have b71 := (eb.real_register_frame 71 (by decide)).trans a71'
  obtain ⟨c,ec,c72,c73,cI,cR,cW,cO,cH⟩ := episode_budget_product_exec m g ω q block b bH b71 b180'
  have c70 := (ec.real_register_frame 70 (by decide)).trans ((eb.real_register_frame 70 (by decide)).trans ((ea.real_register_frame 70 (by decide)).trans hMu))
  have c31 := (ec.real_register_frame 31 (by decide)).trans ((eb.real_register_frame 31 (by decide)).trans ((ea.real_register_frame 31 (by decide)).trans h31))
  obtain ⟨u,d,ed,hu,d75,dI,dR,dW,dO,dH⟩ := episode_maximum_exec m g ω mu (q*(block : ℝ)) c cH c70 c73 c31
  have d72 := (ed.real_register_frame 72 (by decide)).trans c72
  let out := payUnit (realWrite d 76 (max mu (q*(block : ℝ))/(block : ℝ)))
  have ee : MachineEval m g ω (coreCode (.div 76 75 72)) d 1 out := by
    simpa only [coreCode,RealOperation.instruction,RealOperation.value,d75,d72,out] using binary_eval m g ω d .div 76 75 72 dH
  have ex : MachineEval m g ω episodeBudgetScalarCode st (10+(10+(2+(u+1)))) out :=
    MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed ee)))
  refine ⟨_,out,ex,by omega,?_,?_,dI.trans (cI.trans (bI.trans aI)),dR.trans (cR.trans (bR.trans aR)),
    ex.unit_work episodeBudgetScalarCode_wellFormed (by decide) hh,dO.trans (cO.trans (bO.trans aO)),dH⟩
  · exact (ee.real_register_frame 75 (by decide)).trans d75
  · simp [out,payUnit,pcSet,realWrite]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameEpisodeParametersExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameEpisodeParametersCode_wellFormed : frameEpisodeParametersCode.wellFormed :=
  ⟨frameResidualSumCode_wellFormed,episodeBudgetScalarCode_wellFormed⟩

set_option maxHeartbeats 9000000 in
lemma frame_episode_parameters_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hSubset : (logical.frames logical.top).active ⊆ parentDomain logical logical.top) :
    let mu := ∑ v ∈ (logical.frames logical.top).active, (logical.frames logical.top).residual v
    let Q := max mu ((logical.frames logical.top).q*((logical.frames logical.top).block : ℝ))
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω frameEpisodeParametersCode st steps out ∧
      steps ≤ (4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+47 ∧
      out.scalar.core.regs 75=Q ∧ out.scalar.core.regs 76=Q/((logical.frames logical.top).block : ℝ) ∧
      memory.queueMass=pm.queueMass ∧ out.work=st.work+steps ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  dsimp only
  obtain ⟨pre,preMemory,ep,hMu,hMass,hWork,hQuery,hOutput,hHalt⟩ := frame_residual_sum_exec m g ω logical s α ε ell length st hh pm hSubset
  let f := preMemory.frames logical.top le_rfl
  obtain ⟨u,out,eb,hu,hQ,hTheta,hI,hR,hW,hO,hH⟩ := episode_budget_scalar_exec m g ω logical.top (logical.frames logical.top).block
    (logical.frames logical.top).q (∑ v ∈ (logical.frames logical.top).active, (logical.frames logical.top).residual v)
    pre hHalt preMemory.top preMemory.one f.q f.block hMu
  have hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=pre.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact eb.pointer_frame _ (by decide)
  have hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=pre.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact eb.real_register_frame _ (by decide)
  let memory := preMemory.frame hI hR hP hG hO
  have ex := MachineEval.seq ep eb
  refine ⟨_,out,memory,ex,by omega,hQ,hTheta,hMass,
    ex.unit_work frameEpisodeParametersCode_wellFormed (by decide) hh,
    (eb.query_frame (by decide)).trans hQuery,hO.trans hOutput,hH⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameCacheClearPrelude

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameCacheClearPreludeCode_wellFormed : frameCacheClearPreludeCode.wellFormed := by
  refine ⟨levelHeaderIntegerToCode_wellFormed 1 94,?_⟩
  simp [frameCacheClearPointerRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 4000000 in
lemma frame_cache_clear_prelude_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (level width : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (h100 : st.scalar.core.ptrs 100=(level : ℤ)) (h50 : st.scalar.core.ptrs 50=(width : ℤ)) :
    ∃ out, MachineEval m g ω frameCacheClearPreludeCode st 19 out ∧
      out.scalar.core.ptrs 94=st.scalar.integerMemory (levelHeaderAddress level 1) ∧
      out.scalar.core.ptrs 182=((16*(level+1)+4 : ℕ) : ℤ) ∧ out.scalar.core.ptrs 41=(width : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+19 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a94,aI,aR,aW,aO,aH⟩ := level_header_integer_to_exec m g ω st hh level 1 94 h100
  have a100 := (ea.pointer_frame 100 (by decide)).trans h100
  have a50 := (ea.pointer_frame 50 (by decide)).trans h50
  obtain ⟨out,eb,hP,hI,hR,hW,hO,hH⟩ := frameCacheClearPointerRoutine.execute m g ω a aH
  have eb9 : MachineEval m g ω frameCacheClearPointerRoutine.code a 9 out := eb
  have ex : MachineEval m g ω frameCacheClearPreludeCode st 19 out := MachineEval.seq ea eb9
  refine ⟨out,ex,?_,?_,?_,hI.trans aI,hR.trans aR,?_,hO.trans aO,hH⟩
  · exact (eb.pointer_frame 94 (by decide)).trans a94
  · rw [hP]
    simp [frameCacheClearPointerRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,a100]
    ring
  · rw [hP]
    simp [frameCacheClearPointerRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,a50]
  · rw [hW,aW]
    change st.work+10+9= _
    norm_num; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ClearVertexFieldRecords

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def clearVertexFieldRecords {n : ℕ} (width offset : ℕ) (vertices : List (Fin n)) (I : ℤ → ℤ) : ℤ → ℤ :=
  fun z => if z ∈ vertices.map (fun v => vertexRecordAddress width v.val offset) then 0 else I z

lemma clear_vertex_field_records_nil {n : ℕ} (width offset : ℕ) (I : ℤ → ℤ) :
    clearVertexFieldRecords (n:=n) width offset [] I=I := by
  funext z
  simp [clearVertexFieldRecords]

lemma clear_vertex_field_records_cons {n : ℕ} (width offset : ℕ) (v : Fin n) (vertices : List (Fin n)) (I : ℤ → ℤ) :
    clearVertexFieldRecords width offset (v::vertices) I=
      clearVertexFieldRecords width offset vertices (Function.update I (vertexRecordAddress width v.val offset) 0) := by
  funext z
  by_cases hz : z=vertexRecordAddress width v.val offset <;>
    by_cases hm : z ∈ vertices.map (fun u => vertexRecordAddress width u.val offset) <;>
    simp [clearVertexFieldRecords,hz,hm]

lemma clear_vertex_field_records_positive {n : ℕ} (width offset : ℕ) (vertices : List (Fin n)) (I : ℤ → ℤ)
    (z : ℤ) (hz : 0 ≤ z) : clearVertexFieldRecords width offset vertices I z=I z := by
  have hn : z ∉ vertices.map (fun v => vertexRecordAddress width v.val offset) := by
    rintro hm
    obtain ⟨v,hv,he⟩ := List.mem_map.mp hm
    have hNeg := vertexRecordAddress_negative width v.val offset
    omega
  simp only [clearVertexFieldRecords,if_neg hn]

lemma clear_vertex_field_records_at {n : ℕ} (width offset : ℕ) (vertices : List (Fin n)) (I : ℤ → ℤ)
    (v : Fin n) (hv : v ∈ vertices) : clearVertexFieldRecords width offset vertices I (vertexRecordAddress width v.val offset)=0 := by
  apply if_pos
  exact List.mem_map.mpr ⟨v,hv,rfl⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ClearVertexFieldBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma clearVertexFieldBodyCode_wellFormed : clearVertexFieldBodyCode.wellFormed := by
  refine ⟨pushOutputReadCode_wellFormed,?_,?_⟩ <;>
    simp [clearVertexFieldPrepRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
      vertexIntegerStoreCode,vertexAddressCode_wellFormed,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 5000000 in
lemma clear_vertex_field_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width offset : ℕ) (head next : ℤ) (v : Fin n) (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (h41 : st.scalar.core.ptrs 41=(width : ℤ))
    (h182 : st.scalar.core.ptrs 182=(offset : ℤ)) (h94 : st.scalar.core.ptrs 94=head)
    (hKey : st.scalar.integerMemory head=(v.val : ℤ)) (hNext : st.scalar.integerMemory (head+2)=next) :
    ∃ out, MachineEval m g ω clearVertexFieldBodyCode st (4*width+15) out ∧ out.scalar.core.ptrs 94=next ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (vertexRecordAddress width v.val offset) 0 ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(4*width+15 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a40,a94,a44,aI,aR,aQ,aW,aO,aH⟩ := push_output_read_exec m g ω st hh head next v h94 hKey hNext
  have a0 := (ea.pointer_frame 0 (by decide)).trans h0
  have a41 := (ea.pointer_frame 41 (by decide)).trans h41
  have a182 := (ea.pointer_frame 182 (by decide)).trans h182
  obtain ⟨b,eb,bP,bI,bR,bW,bO,bH⟩ := clearVertexFieldPrepRoutine.execute m g ω a aH
  have eb2 : MachineEval m g ω clearVertexFieldPrepRoutine.code a 2 b := eb
  have b44 : b.scalar.core.ptrs 44=(offset : ℤ) := by
    rw [bP]; simp [clearVertexFieldPrepRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,a182]
  have b51 : b.scalar.core.ptrs 51=0 := by
    rw [bP]; simp [clearVertexFieldPrepRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,a0]
  have b0 := (eb.pointer_frame 0 (by decide)).trans a0
  have b40 := (eb.pointer_frame 40 (by decide)).trans a40
  have b41 := (eb.pointer_frame 41 (by decide)).trans a41
  obtain ⟨out,ec,cI,cR,cW,cO,cH⟩ := vertex_integer_store_exec m g ω b bH width v.val offset b0 b40 b41 b44
  have ex : MachineEval m g ω clearVertexFieldBodyCode st (4*width+15) out := by
    have ee := MachineEval.seq ea (MachineEval.seq eb2 ec)
    convert ee using 1 <;> (first | rfl | ring)
  refine ⟨out,ex,?_,?_,cR.trans (bR.trans aR),ex.query_frame (by decide),
    ex.unit_work clearVertexFieldBodyCode_wellFormed (by decide) hh,cO.trans (bO.trans aO),cH⟩
  · exact (ec.pointer_frame 94 (by decide)).trans ((eb.pointer_frame 94 (by decide)).trans a94)
  · rw [cI,b51,bI,aI]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ClearVertexFieldLoop

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 6500000 in
lemma clear_vertex_field_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width offset : ℕ) (vertices : List (Fin n)) (head : ℤ) (F : Finset ℤ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (h41 : st.scalar.core.ptrs 41=(width : ℤ))
    (h182 : st.scalar.core.ptrs 182=(offset : ℤ)) (h94 : st.scalar.core.ptrs 94=head)
    (hList : VertexListRep st.scalar.integerMemory head vertices F) :
    ∃ out, MachineEval m g ω clearVertexFieldLoopCode st ((4*width+17)*vertices.length+1) out ∧
      out.scalar.integerMemory=clearVertexFieldRecords width offset vertices st.scalar.integerMemory ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+((4*width+17)*vertices.length+1 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction vertices generalizing st head F with
  | nil =>
    have hHead : st.scalar.core.ptrs 94=0 := h94.trans hList.nil.1
    refine ⟨payUnit st,MachineEval.pointerDone hh (by rw [hHead,h0]),?_,rfl,rfl,by simp,rfl,hh⟩
    symm
    exact clear_vertex_field_records_nil width offset _
  | cons v vertices ih =>
    obtain ⟨next,S,hPos,hKey,hChild,hNext,hTail,hF,hSep⟩ := hList.cons_view
    obtain ⟨mid,eb,hm94,hmI,hmR,hmQ,hmW,hmO,hmH⟩ := clear_vertex_field_body_exec m g ω width offset head next v
      (payUnit st) hh h0 h41 h182 h94 hKey hNext
    have hm0 := (eb.pointer_frame 0 (by decide)).trans h0
    have hm41 := (eb.pointer_frame 41 (by decide)).trans h41
    have hm182 := (eb.pointer_frame 182 (by decide)).trans h182
    have hmList : VertexListRep mid.scalar.integerMemory next vertices S := by
      apply hTail.frame
      intro z hz
      rw [hmI]
      apply Function.update_of_ne
      have hPositive : 0 ≤ z := by have := ForestRep.positive_cells hTail z hz; omega
      have hNegative := vertexRecordAddress_negative width v.val offset
      omega
    obtain ⟨out,er,hoI,hoR,hoQ,hoW,hoO,hoH⟩ := ih next S (payUnit mid) hmH hm0 hm41 hm182 hm94 hmList
    have ex : MachineEval m g ω clearVertexFieldLoopCode st ((4*width+17)*(v::vertices).length+1) out := by
      have ee := MachineEval.pointerNext (r:=94) (s:=0) hh (by rw [h94,h0]; omega) eb er
      convert ee using 1 <;> (first | rfl | simp only [List.length_cons]; ring)
    refine ⟨out,ex,?_,hoR.trans hmR,hoQ.trans hmQ,?_,hoO.trans hmO,hoH⟩
    · rw [hoI]
      change clearVertexFieldRecords width offset vertices mid.scalar.integerMemory= _
      rw [hmI,clear_vertex_field_records_cons]
      rfl
    · rw [hoW,payUnit_work,hmW,payUnit_work]
      simp only [List.length_cons]
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ClearVertexFieldPointwise

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma clear_vertex_field_records_samefield {n : ℕ} (width offset : ℕ) (vertices : List (Fin n)) (I : ℤ → ℤ)
    (ho : offset < width) (v : Fin n) :
    clearVertexFieldRecords width offset vertices I (vertexRecordAddress width v.val offset)=
      if v ∈ vertices then 0 else I (vertexRecordAddress width v.val offset) := by
  classical
  by_cases hv : v ∈ vertices
  · rw [clear_vertex_field_records_at width offset vertices I v hv,if_pos hv]
  · rw [if_neg hv]
    apply if_neg
    intro hm
    obtain ⟨u,hu,he⟩ := List.mem_map.mp hm
    have hVal := (vertexRecordAddress_injective width v.val u.val offset offset ho ho he.symm).1
    have hEq : u=v := Fin.ext hVal.symm
    subst u
    exact hv hu

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameCacheClearExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameCacheClearCode_wellFormed : frameCacheClearCode.wellFormed :=
  ⟨frameCacheClearPreludeCode_wellFormed,clearVertexFieldBodyCode_wellFormed⟩

set_option maxHeartbeats 7000000 in
lemma frame_cache_clear_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hCacheSubset : (logical.frames logical.top).cache ⊆ (logical.frames logical.top).active) :
    let vertices := (pm.frames logical.top le_rfl).activeVertices
    ∃ out, MachineEval m g ω frameCacheClearCode st
      ((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+20) out ∧
      out.scalar.integerMemory=clearVertexFieldRecords (16*(ell+3)) (16*(logical.top+1)+4) vertices st.scalar.integerMemory ∧
      (∀ v ∈ parentDomain logical logical.top, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+20 : ℕ) ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  dsimp only
  let f := pm.frames logical.top le_rfl
  obtain ⟨pre,ep,h94,h182,h41,hI,hR,hW,hO,hH⟩ := frame_cache_clear_prelude_exec m g ω logical.top (16*(ell+3)) st hh pm.top pm.width
  have h0 := (ep.pointer_frame 0 (by decide)).trans pm.zero
  have hList : VertexListRep pre.scalar.integerMemory (st.scalar.integerMemory (levelHeaderAddress logical.top 1)) f.activeVertices f.activeFoot := by
    rw [hI]
    exact f.activeRep
  obtain ⟨out,el,hoI,hoR,hoQ,hoW,hoO,hoH⟩ := clear_vertex_field_loop_exec m g ω (16*(ell+3)) (16*(logical.top+1)+4)
    f.activeVertices (st.scalar.integerMemory (levelHeaderAddress logical.top 1)) f.activeFoot pre hH h0 h41 h182 h94 hList
  have hLength : f.activeVertices.length=(logical.frames logical.top).active.card := by
    rw [←f.activeSet,List.toFinset_card_of_nodup f.activeNodup]
  have ex : MachineEval m g ω frameCacheClearCode st
      ((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+20) out := by
    have ee := MachineEval.seq ep el
    rw [hLength] at ee
    convert ee using 1 <;> (first | rfl | omega)
  have hFinalI : out.scalar.integerMemory=clearVertexFieldRecords (16*(ell+3)) (16*(logical.top+1)+4) f.activeVertices st.scalar.integerMemory := by rw [hoI,hI]
  refine ⟨out,ex,hFinalI,?_,hoR.trans hR,?_,hoQ.trans (ep.query_frame (by decide)),hoO.trans hO,hoH⟩
  · intro v hv
    rw [hFinalI,clear_vertex_field_records_samefield _ _ _ _ (by omega)]
    by_cases ha : v ∈ (logical.frames logical.top).active
    · have hm : v ∈ f.activeVertices := by apply List.mem_toFinset.mp; rw [f.activeSet]; exact ha
      rw [if_pos hm]
    · have hm : v ∉ f.activeVertices := by intro hm; apply ha; rw [←f.activeSet]; exact List.mem_toFinset.mpr hm
      have hc : v ∉ (logical.frames logical.top).cache := by intro hc; exact ha (hCacheSubset hc)
      rw [if_neg hm,f.cacheFlags v hv,if_neg hc]
  · rw [hoW,hW,hLength]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ClearVertexFieldSet

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def clearVertexFieldSetRecords {n : ℕ} (width offset : ℕ) (T : Finset (Fin n)) (I : ℤ → ℤ) : ℤ → ℤ :=
  fun z => if z ∈ T.image (fun v => vertexRecordAddress width v.val offset) then 0 else I z

lemma clear_vertex_field_list_set {n : ℕ} (width offset : ℕ) (vertices : List (Fin n)) (I : ℤ → ℤ) :
    clearVertexFieldRecords width offset vertices I=clearVertexFieldSetRecords width offset vertices.toFinset I := by
  funext z
  have hMem : z ∈ vertices.map (fun v => vertexRecordAddress width v.val offset) ↔
      z ∈ vertices.toFinset.image (fun v => vertexRecordAddress width v.val offset) := by
    simp only [List.mem_map,Finset.mem_image,List.mem_toFinset]
  simp only [clearVertexFieldRecords,clearVertexFieldSetRecords,hMem]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodePCExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma episodePCCode_wellFormed : episodePCCode.wellFormed :=
  ⟨levelHeaderIntegerToCode_wellFormed 10 181,levelHeaderIntegerSetCode_wellFormed _ _,levelHeaderIntegerSetCode_wellFormed _ _⟩

set_option maxHeartbeats 6500000 in
lemma episode_pc_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (level : ℕ) (needFull : Bool) (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (hLevel : st.scalar.core.ptrs 100=(level : ℤ))
    (hNeed : st.scalar.integerMemory (levelHeaderAddress level 10)=if needFull then 1 else 0) :
    ∃ steps out, MachineEval m g ω episodePCCode st steps out ∧ steps ≤ 22 ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (levelHeaderAddress level 0)
        (normalizePCNumber (if needFull then .fullSolve else .normalize) : ℤ) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a181,aI,aR,aW,aO,aH⟩ := level_header_integer_to_exec m g ω st hh level 10 181 hLevel
  have a0 := (ea.pointer_frame 0 (by decide)).trans h0
  have a100 := (ea.pointer_frame 100 (by decide)).trans hLevel
  have aNeed := a181.trans hNeed
  cases hBool : needFull with
  | false =>
    have aClosed : a.scalar.core.ptrs 181=0 := by simpa only [hBool,Bool.false_eq_true,if_false] using aNeed
    obtain ⟨out,eb,hI,hR,hW,hO,hH⟩ := level_header_integer_set_exec m g ω (payUnit a) aH level 0 (normalizePCNumber .normalize : ℤ) a100
    have ex : MachineEval m g ω episodePCCode st 21 out :=
      MachineEval.seq ea (MachineEval.pointerLe aH (by rw [aClosed,a0]) eb)
    refine ⟨21,out,ex,by omega,?_,hR.trans aR,ex.unit_work episodePCCode_wellFormed (by decide) hh,hO.trans aO,hH⟩
    change out.scalar.integerMemory=Function.update st.scalar.integerMemory _ (normalizePCNumber .normalize : ℤ)
    change out.scalar.integerMemory=Function.update a.scalar.integerMemory _ _ at hI
    rw [aI] at hI
    exact hI
  | true =>
    have aOpened : a.scalar.core.ptrs 181=1 := by simpa only [hBool,if_true] using aNeed
    obtain ⟨b,eb,hI,hR,hW,hO,hH⟩ := level_header_integer_set_exec m g ω (payUnit a) aH level 0 (normalizePCNumber .fullSolve : ℤ) a100
    let out := payUnit b
    have ex : MachineEval m g ω episodePCCode st 22 out :=
      MachineEval.seq ea (MachineEval.pointerGt aH (by rw [aOpened,a0]; omega) eb)
    refine ⟨22,out,ex,le_rfl,?_,hR.trans aR,ex.unit_work episodePCCode_wellFormed (by decide) hh,hO.trans aO,hH⟩
    change b.scalar.integerMemory=Function.update st.scalar.integerMemory _ (normalizePCNumber .fullSolve : ℤ)
    change b.scalar.integerMemory=Function.update a.scalar.integerMemory _ _ at hI
    rw [aI] at hI
    exact hI

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeHeaderExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def episodeHeaderIntegerMemory (I : ℤ → ℤ) (level : ℕ) (needFull : Bool) : ℤ → ℤ :=
  Function.update (levelHeaderIntegerSetsMemory I level episodeIntegerAssignments) (levelHeaderAddress level 0)
    (normalizePCNumber (if needFull then .fullSolve else .normalize) : ℤ)
def episodeHeaderRealMemory (R : ℤ → ℝ) (level : ℕ) (Q theta : ℝ) : ℤ → ℝ :=
  Function.update (Function.update (Function.update R (levelHeaderAddress level 3) Q) (levelHeaderAddress level 4) 0)
    (levelHeaderAddress level 5) theta

lemma episodeHeaderCode_wellFormed : episodeHeaderCode.wellFormed :=
  ⟨levelHeaderRealFromCode_wellFormed 3 75,levelHeaderRealZeroCode_wellFormed 4,
    levelHeaderRealFromCode_wellFormed 5 76,levelHeaderIntegerSetsCode_wellFormed _,episodePCCode_wellFormed⟩

set_option maxHeartbeats 10000000 in
lemma episode_header_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (level : ℕ) (needFull : Bool) (Q theta : ℝ) (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (hLevel : st.scalar.core.ptrs 100=(level : ℤ))
    (h31 : st.scalar.core.regs 31=1) (h75 : st.scalar.core.regs 75=Q) (h76 : st.scalar.core.regs 76=theta)
    (hNeed : st.scalar.integerMemory (levelHeaderAddress level 10)=if needFull then 1 else 0) :
    ∃ steps out, MachineEval m g ω episodeHeaderCode st steps out ∧ steps ≤ 102 ∧
      out.scalar.integerMemory=episodeHeaderIntegerMemory st.scalar.integerMemory level needFull ∧
      out.scalar.core.mem=episodeHeaderRealMemory st.scalar.core.mem level Q theta ∧
      out.work=st.work+steps ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,aR,aI,aQuery,aW,aO,aH⟩ := level_header_real_from_exec m g ω st hh level 3 75 hLevel h31
  have a100 := (ea.pointer_frame 100 (by decide)).trans hLevel
  obtain ⟨b,eb,bR,bI,bW,bO,bH⟩ := level_header_real_zero_exec m g ω a aH level 4 a100
  have b100 := (eb.pointer_frame 100 (by decide)).trans a100
  have b31 := (eb.real_register_frame 31 (by decide)).trans ((ea.real_register_frame 31 (by decide)).trans h31)
  have b76 := (eb.real_register_frame 76 (by decide)).trans ((ea.real_register_frame 76 (by decide)).trans h76)
  obtain ⟨c,ec,cR,cI,cQuery,cW,cO,cH⟩ := level_header_real_from_exec m g ω b bH level 5 76 b100 b31
  have c100 := (ec.pointer_frame 100 (by decide)).trans b100
  obtain ⟨d,ed,dI,dR,dQuery,dW,dO,dH⟩ := level_header_integer_sets_exec m g ω episodeIntegerAssignments c cH level c100
  have d100 := (ed.pointer_frame 100 (by decide)).trans c100
  have d0 := (ed.pointer_frame 0 (by decide)).trans ((ec.pointer_frame 0 (by decide)).trans ((eb.pointer_frame 0 (by decide)).trans ((ea.pointer_frame 0 (by decide)).trans h0)))
  have dNeed : d.scalar.integerMemory (levelHeaderAddress level 10)=if needFull then 1 else 0 := by
    rw [dI,cI,bI,aI]
    simpa [levelHeaderIntegerSetsMemory,episodeIntegerAssignments] using hNeed
  obtain ⟨u,out,ee,hu,hI,hR,hWork,hOutput,hHalt⟩ := episode_pc_exec m g ω level needFull d dH d0 d100 dNeed
  have ex : MachineEval m g ω episodeHeaderCode st (10+(10+(10+(50+u)))) out := by
    have ee' : MachineEval m g ω (levelHeaderIntegerSetsCode episodeIntegerAssignments) c 50 d := ed
    exact MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ee' ee)))
  refine ⟨_,out,ex,by omega,?_,?_,ex.unit_work episodeHeaderCode_wellFormed (by decide) hh,
    ex.query_frame (by decide),hOutput.trans (dO.trans (cO.trans (bO.trans aO))),hHalt⟩
  · rw [hI,dI,cI,bI,aI]
    rfl
  · rw [hR,dR,cR,b76,bR,aR,h75]
    rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeHeaderMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma episode_header_integer_below (I : ℤ → ℤ) (level : ℕ) (need : Bool) (z : ℤ) (hz : z < 128) :
    episodeHeaderIntegerMemory I level need z=I z := by
  have hNe : ∀ slot, z ≠ levelHeaderAddress level slot := by
    intro slot he
    have := levelHeaderAddress_positive level slot
    omega
  simp [episodeHeaderIntegerMemory,episodeIntegerAssignments,levelHeaderIntegerSetsMemory,
    Function.update_of_ne (hNe 0),Function.update_of_ne (hNe 4),Function.update_of_ne (hNe 5),
    Function.update_of_ne (hNe 6),Function.update_of_ne (hNe 9),Function.update_of_ne (hNe 11)]

lemma episode_header_real_below (R : ℤ → ℝ) (level : ℕ) (Q theta : ℝ) (z : ℤ) (hz : z < 128) :
    episodeHeaderRealMemory R level Q theta z=R z := by
  have hNe : ∀ slot, z ≠ levelHeaderAddress level slot := by
    intro slot he
    have := levelHeaderAddress_positive level slot
    omega
  simp [episodeHeaderRealMemory,Function.update_of_ne (hNe 3),Function.update_of_ne (hNe 4),Function.update_of_ne (hNe 5)]

lemma episode_header_integer_same (I : ℤ → ℤ) (level slot : ℕ) (need : Bool)
    (hOther : slot ∉ ([0,4,5,6,9,11] : List ℕ)) :
    episodeHeaderIntegerMemory I level need (levelHeaderAddress level slot)=I (levelHeaderAddress level slot) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hOther
  simp only [episodeHeaderIntegerMemory,episodeIntegerAssignments,levelHeaderIntegerSetsMemory,
    List.foldl_cons,List.foldl_nil,level_header_update_read]
  split_ifs <;> (first | rfl | omega)

lemma episode_header_real_same (R : ℤ → ℝ) (level slot : ℕ) (Q theta : ℝ)
    (hOther : slot ∉ ([3,4,5] : List ℕ)) :
    episodeHeaderRealMemory R level Q theta (levelHeaderAddress level slot)=R (levelHeaderAddress level slot) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hOther
  simp only [episodeHeaderRealMemory,level_header_update_read]
  split_ifs <;> (first | rfl | omega)

lemma episode_header_integer_other_level (I : ℤ → ℤ) (level other slot : ℕ) (need : Bool)
    (hNe : other ≠ level) (hSlot : slot < 32) :
    episodeHeaderIntegerMemory I level need (levelHeaderAddress other slot)=I (levelHeaderAddress other slot) := by
  have hAddress : ∀ field < 32, levelHeaderAddress other slot ≠ levelHeaderAddress level field := by
    intro field hf he
    exact hNe (levelHeaderAddress_injective other level slot field hSlot hf he).1
  simp [episodeHeaderIntegerMemory,episodeIntegerAssignments,levelHeaderIntegerSetsMemory,
    Function.update_of_ne (hAddress 0 (by decide)),Function.update_of_ne (hAddress 4 (by decide)),
    Function.update_of_ne (hAddress 5 (by decide)),Function.update_of_ne (hAddress 6 (by decide)),
    Function.update_of_ne (hAddress 9 (by decide)),Function.update_of_ne (hAddress 11 (by decide))]

lemma episode_header_real_other_level (R : ℤ → ℝ) (level other slot : ℕ) (Q theta : ℝ)
    (hNe : other ≠ level) (hSlot : slot < 32) :
    episodeHeaderRealMemory R level Q theta (levelHeaderAddress other slot)=R (levelHeaderAddress other slot) := by
  have hAddress : ∀ field < 32, levelHeaderAddress other slot ≠ levelHeaderAddress level field := by
    intro field hf he
    exact hNe (levelHeaderAddress_injective other level slot field hSlot hf he).1
  simp [episodeHeaderRealMemory,Function.update_of_ne (hAddress 3 (by decide)),
    Function.update_of_ne (hAddress 4 (by decide)),Function.update_of_ne (hAddress 5 (by decide))]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeRawExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma episodeRawCode_wellFormed : episodeRawCode.wellFormed :=
  ⟨frameEpisodeParametersCode_wellFormed,frameCacheClearCode_wellFormed,episodeHeaderCode_wellFormed⟩

set_option maxHeartbeats 14000000 in
lemma episode_raw_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hSubset : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hCacheSubset : (logical.frames logical.top).cache ⊆ (logical.frames logical.top).active) :
    let f := logical.frames logical.top
    let mu := ∑ v ∈ f.active, f.residual v
    let Q := max mu (f.q*(f.block : ℝ))
    let theta := Q/(f.block : ℝ)
    ∃ steps out, MachineEval m g ω episodeRawCode st steps out ∧
      steps ≤ 2*(4*(16*(ell+3))+17)*f.active.card+169 ∧
      out.scalar.integerMemory=episodeHeaderIntegerMemory
        (clearVertexFieldSetRecords (16*(ell+3)) (16*(logical.top+1)+4) f.active st.scalar.integerMemory) logical.top f.needFull ∧
      out.scalar.core.mem=episodeHeaderRealMemory st.scalar.core.mem logical.top Q theta ∧
      (∀ v ∈ parentDomain logical logical.top, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0) ∧
      out.work=st.work+steps ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  dsimp only
  obtain ⟨aSteps,a,ma,ea,ha,a75,a76,aMass,aW,aQuery,aO,aH⟩ := frame_episode_parameters_exec m g ω logical s α ε ell length st hh pm hSubset
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := ea.integer_memory_frame (by decide)
  have aR : a.scalar.core.mem=st.scalar.core.mem := ea.real_memory_frame (by decide)
  obtain ⟨b,eb,bI,bCache,bR,bW,bQuery,bO,bH⟩ := frame_cache_clear_exec m g ω logical s α ε ell length a aH ma hDepth hCacheSubset
  have b0 := (eb.pointer_frame 0 (by decide)).trans ma.zero
  have b100 := (eb.pointer_frame 100 (by decide)).trans ma.top
  have b31 := (eb.real_register_frame 31 (by decide)).trans ma.one
  have b75 := (eb.real_register_frame 75 (by decide)).trans a75
  have b76 := (eb.real_register_frame 76 (by decide)).trans a76
  have bNeed : b.scalar.integerMemory (levelHeaderAddress logical.top 10)=if (logical.frames logical.top).needFull then 1 else 0 := by
    rw [bI,clear_vertex_field_records_positive _ _ _ _ _ (by have := levelHeaderAddress_positive logical.top 10; omega)]
    exact (ma.frames logical.top le_rfl).needFull
  obtain ⟨u,out,ec,hu,hI,hR,hW,hQuery,hO,hH⟩ := episode_header_exec m g ω logical.top (logical.frames logical.top).needFull
    _ _ b bH b0 b100 b31 b75 b76 bNeed
  have hSet : clearVertexFieldRecords (16*(ell+3)) (16*(logical.top+1)+4) (ma.frames logical.top le_rfl).activeVertices a.scalar.integerMemory=
      clearVertexFieldSetRecords (16*(ell+3)) (16*(logical.top+1)+4) (logical.frames logical.top).active st.scalar.integerMemory := by
    rw [clear_vertex_field_list_set,(ma.frames logical.top le_rfl).activeSet,aI]
  have ex := MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨_,out,ex,by nlinarith,?_,?_,?_,ex.unit_work episodeRawCode_wellFormed (by decide) hh,
    hQuery.trans (bQuery.trans aQuery),hO.trans (bO.trans aO),hH⟩
  · rw [hI,bI,hSet]
  · rw [hR,bR,aR]
  · intro v hv
    rw [hI,episode_header_integer_below _ _ _ _ (by have := vertexRecordAddress_negative (16*(ell+3)) v.val (16*(logical.top+1)+4); omega)]
    exact bCache v hv

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeHeaderHeapFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma episode_header_integer_outside (I : ℤ → ℤ) (level : ℕ) (need : Bool) (z : ℤ)
    (hNe : ∀ slot < 32, z ≠ levelHeaderAddress level slot) :
    episodeHeaderIntegerMemory I level need z=I z := by
  simp [episodeHeaderIntegerMemory,episodeIntegerAssignments,levelHeaderIntegerSetsMemory,
    Function.update_of_ne (hNe 0 (by decide)),Function.update_of_ne (hNe 4 (by decide)),
    Function.update_of_ne (hNe 5 (by decide)),Function.update_of_ne (hNe 6 (by decide)),
    Function.update_of_ne (hNe 9 (by decide)),Function.update_of_ne (hNe 11 (by decide))]

lemma episode_header_integer_above (I : ℤ → ℤ) (level : ℕ) (need : Bool) (z : ℤ)
    (hz : levelHeaderAddress level 31 < z) : episodeHeaderIntegerMemory I level need z=I z := by
  apply episode_header_integer_outside
  intro slot hs he
  unfold levelHeaderAddress at hz he
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ClearVertexFieldSetFacts

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma clear_vertex_field_set_positive {n : ℕ} (width offset : ℕ) (T : Finset (Fin n)) (I : ℤ → ℤ)
    (z : ℤ) (hz : 0 ≤ z) : clearVertexFieldSetRecords width offset T I z=I z := by
  apply if_neg
  intro hm
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hm
  have hNeg := vertexRecordAddress_negative width v.val offset
  omega

lemma clear_vertex_field_set_other_field {n : ℕ} (width offset field : ℕ) (T : Finset (Fin n)) (I : ℤ → ℤ)
    (ho : offset < width) (hf : field < width) (hne : field ≠ offset) (v : Fin n) :
    clearVertexFieldSetRecords width offset T I (vertexRecordAddress width v.val field)=I (vertexRecordAddress width v.val field) := by
  apply if_neg
  intro hm
  obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hm
  exact hne (vertexRecordAddress_injective width v.val u.val field offset hf ho he.symm).2

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeRawMemoryFacts

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def episodeRawIntegerMemory {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell : ℕ) : ℤ → ℤ :=
  episodeHeaderIntegerMemory (clearVertexFieldSetRecords (16*(ell+3)) (16*(logical.top+1)+4)
    (logical.frames logical.top).active I) logical.top (logical.frames logical.top).needFull

def episodeRawRealMemory {n : ℕ} (R : ℤ → ℝ) (logical : RecursiveState n) : ℤ → ℝ :=
  let f := logical.frames logical.top
  let Q := max (∑ v ∈ f.active, f.residual v) (f.q*(f.block : ℝ))
  episodeHeaderRealMemory R logical.top Q (Q/(f.block : ℝ))

lemma episode_raw_integer_global {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell : ℕ)
    (z : ℤ) (hz : 0 ≤ z) (h128 : z < 128) : episodeRawIntegerMemory I logical ell z=I z := by
  rw [episodeRawIntegerMemory,episode_header_integer_below _ _ _ _ h128,clear_vertex_field_set_positive _ _ _ _ _ hz]

lemma episode_raw_integer_field {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (v : Fin n) (field : ℕ) (hf : field < 16*(ell+3))
    (hNe : field ≠ 16*(logical.top+1)+4) :
    episodeRawIntegerMemory I logical ell (vertexRecordAddress (16*(ell+3)) v.val field)=I (vertexRecordAddress (16*(ell+3)) v.val field) := by
  rw [episodeRawIntegerMemory,episode_header_integer_below _ _ _ _ (by have := vertexRecordAddress_negative (16*(ell+3)) v.val field; omega)]
  exact clear_vertex_field_set_other_field _ _ _ _ _ (by omega) hf hNe v

lemma episode_raw_real_field {n : ℕ} (R : ℤ → ℝ) (logical : RecursiveState n) (width vertex field : ℕ) :
    episodeRawRealMemory R logical (vertexRecordAddress width vertex field)=R (vertexRecordAddress width vertex field) := by
  apply episode_header_real_below
  have := vertexRecordAddress_negative width vertex field
  omega

lemma episode_raw_integer_header_same {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell slot : ℕ)
    (hOther : slot ∉ ([0,4,5,6,9,11] : List ℕ)) :
    episodeRawIntegerMemory I logical ell (levelHeaderAddress logical.top slot)=I (levelHeaderAddress logical.top slot) := by
  rw [episodeRawIntegerMemory,episode_header_integer_same _ _ _ _ hOther]
  apply clear_vertex_field_set_positive
  have := levelHeaderAddress_positive logical.top slot
  omega

lemma episode_raw_integer_header_other {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell j slot : ℕ)
    (hOther : j ≠ logical.top) (hSlot : slot < 32) :
    episodeRawIntegerMemory I logical ell (levelHeaderAddress j slot)=I (levelHeaderAddress j slot) := by
  rw [episodeRawIntegerMemory,episode_header_integer_other_level _ _ _ _ _ hOther hSlot]
  apply clear_vertex_field_set_positive
  have := levelHeaderAddress_positive j slot
  omega

lemma episode_raw_real_header_other {n : ℕ} (R : ℤ → ℝ) (logical : RecursiveState n) (j slot : ℕ)
    (hOther : j ≠ logical.top) (hSlot : slot < 32) :
    episodeRawRealMemory R logical (levelHeaderAddress j slot)=R (levelHeaderAddress j slot) := by
  exact episode_header_real_other_level _ _ _ _ _ _ hOther hSlot

lemma episode_raw_integer_above {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (z : ℤ) (hz : 128+32*((ell+2 : ℕ) : ℤ) ≤ z) :
    episodeRawIntegerMemory I logical ell z=I z := by
  have hAbove : levelHeaderAddress logical.top 31 < z := by unfold levelHeaderAddress; omega
  rw [episodeRawIntegerMemory,episode_header_integer_above _ _ _ _ hAbove]
  apply clear_vertex_field_set_positive
  omega

lemma episode_raw_cache_words {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell : ℕ) :
    episodeRawIntegerMemory I logical ell (levelHeaderAddress logical.top 4)=0 ∧
    episodeRawIntegerMemory I logical ell (levelHeaderAddress logical.top 5)=0 ∧
    episodeRawIntegerMemory I logical ell (levelHeaderAddress logical.top 6)=0 ∧
    episodeRawIntegerMemory I logical ell (levelHeaderAddress logical.top 9)=1 ∧
    episodeRawIntegerMemory I logical ell (levelHeaderAddress logical.top 11)=0 := by
  simp [episodeRawIntegerMemory,episodeHeaderIntegerMemory,episodeIntegerAssignments,levelHeaderIntegerSetsMemory]

lemma episode_raw_pc {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell : ℕ) :
    episodeRawIntegerMemory I logical ell (levelHeaderAddress logical.top 0)=
      (normalizePCNumber (if (logical.frames logical.top).needFull then .fullSolve else .normalize) : ℤ) := by
  simp [episodeRawIntegerMemory,episodeHeaderIntegerMemory]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FramePendingEpisodeTransport

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def RecursiveFrameMemory.reset_cache_pending {n : ℕ} {g : InputGraph n} {logical next : RecursiveState n}
    {j width length : ℕ} {st out : MachineState} {floor : ℤ}
    (f : RecursiveFrameMemory g logical j width length st floor) (Q W theta : ℝ) (pc : NormalizePC) (budget : Bool) (children : ℕ)
    (hFrame : next.frames j={logical.frames j with Q := Q,W := W,theta := theta,openBudget := budget,childrenThisEpisode := children,cache := ∅,high := (logical.frames j).active.filter (fun v => 3*theta*LocalPush.deg g.graph v ≤ (logical.frames j).residual v),pc := pc})
    (hDomain : parentDomain next j=parentDomain logical j)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hHeaderI : ∀ slot < 32, slot ∉ ([0,4,5,6,9,11] : List ℕ) → out.scalar.integerMemory (levelHeaderAddress j slot)=st.scalar.integerMemory (levelHeaderAddress j slot))
    (hHeaderR : ∀ slot < 32, slot ∉ ([3,4,5] : List ℕ) → out.scalar.core.mem (levelHeaderAddress j slot)=st.scalar.core.mem (levelHeaderAddress j slot))
    (hPC : out.scalar.integerMemory (levelHeaderAddress j 0)=(normalizePCNumber pc : ℤ))
    (hQ : out.scalar.core.mem (levelHeaderAddress j 3)=Q)
    (hW : out.scalar.core.mem (levelHeaderAddress j 4)=W)
    (hTheta : out.scalar.core.mem (levelHeaderAddress j 5)=theta)
    (hOpen : out.scalar.integerMemory (levelHeaderAddress j 9)=if budget then 1 else 0)
    (hChildren : out.scalar.integerMemory (levelHeaderAddress j 11)=(children : ℤ))
    (hCacheHead : out.scalar.integerMemory (levelHeaderAddress j 4)=0)
    (hCacheCount : out.scalar.integerMemory (levelHeaderAddress j 5)=0)
    (hCacheVolume : out.scalar.integerMemory (levelHeaderAddress j 6)=0)
    (hFieldsI : ∀ v ∈ parentDomain logical j, ∀ field,
      field=0 ∨ field=16*(j+1)+2 ∨ field=16*(j+1)+3 ∨ field=16*(j+1)+5 ∨ field=16*(j+1)+6 →
      out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field))
    (hFieldsR : ∀ v ∈ parentDomain logical j, ∀ field, out.scalar.core.mem (vertexRecordAddress width v.val field)=st.scalar.core.mem (vertexRecordAddress width v.val field))
    (hCacheFlags : ∀ v ∈ parentDomain logical j, out.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+4))=0)
    (hDegree : ∀ v ∈ (logical.frames j).active, st.scalar.integerMemory (vertexRecordAddress width v.val 0)=((g.neighbors v).length : ℤ))
    (hOwned : ∀ z ∈ f.owned, out.scalar.integerMemory z=st.scalar.integerMemory z) :
    FramePendingKeys g next j width length out floor := by
  classical
  let ext := f.exteriorObject.frame (fun z hz => hOwned z (Finset.mem_union_left _ (Finset.mem_union_right _ hz))) hFree
  let high := f.highObject.frame (fun z hz => hOwned z (Finset.mem_union_right _ hz)) hFree
  refine {
    N := by simpa only [hFrame] using (hHeaderR 0 (by decide) (by simp)).trans f.N
    q := by simpa only [hFrame] using (hHeaderR 1 (by decide) (by simp)).trans f.q
    Q := by simpa only [hFrame] using hQ
    W := by simpa only [hFrame] using hW
    theta := by simpa only [hFrame] using hTheta
    block := by simpa only [hFrame] using (hHeaderI 14 (by decide) (by simp)).trans f.block
    pc := by simpa only [hFrame] using hPC
    openBudget := by simpa only [hFrame,if_true] using hOpen
    needFull := by simpa only [hFrame] using (hHeaderI 10 (by decide) (by simp)).trans f.needFull
    children := by simpa only [hFrame,Nat.cast_zero] using hChildren
    reference := by rw [hDomain,hFrame]; exact fun v hv => (hFieldsR v hv _).trans (f.reference v hv)
    residual := by rw [hDomain,hFrame]; exact fun v hv => (hFieldsR v hv _).trans (f.residual v hv)
    activeFlags := by rw [hDomain,hFrame]; exact fun v hv => (hFieldsI v hv _ (by omega)).trans (f.activeFlags v hv)
    cacheFlags := ?_
    activeVertices := f.activeVertices
    activeFoot := f.activeFoot
    activeRep := ?_
    activeNodup := f.activeNodup
    activeSet := by simpa only [hFrame] using f.activeSet
    activeCount := by simpa only [hFrame] using (hHeaderI 3 (by decide) (by simp)).trans f.activeCount
    activeVolume := by simpa only [hFrame] using (hHeaderI 2 (by decide) (by simp)).trans f.activeVolume
    activeBelow := fun z hz => (f.activeBelow z hz).trans_le hFree
    activeAbove := f.activeAbove
    cacheVertices := []
    cacheFoot := ∅
    cacheRep := ?_
    cacheNodup := List.nodup_nil
    cacheSet := by simp [hFrame]
    cacheCount := by simpa [hFrame] using hCacheCount
    cacheVolume := by simpa [hFrame,volumeNat] using hCacheVolume
    cacheBelow := by simp
    cacheAbove := by simp
    exteriorBase := f.exteriorBase
    highBase := f.highBase
    exteriorPointer := (hHeaderI 7 (by decide) (by simp)).trans f.exteriorPointer
    highPointer := (hHeaderI 8 (by decide) (by simp)).trans f.highPointer
    exteriorObject := ext
    highObject := high
    exteriorData := ?_
    virtualExcluded := ?_
    highFlags := ?_
    highDomain := by rw [hDomain]; exact f.highDomain
    highValid := ?_
  }
  · intro v hv
    rw [hDomain] at hv
    simpa [hFrame] using hCacheFlags v hv
  · rw [hHeaderI 1 (by decide) (by simp)]
    apply f.activeRep.frame
    intro z hz
    exact hOwned z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hz)))
  · rw [hCacheHead]
    exact ForestRep.nil
  · rw [hDomain,hFrame]
    refine ⟨f.exteriorData.queuedDomain,?_,?_,?_⟩
    · intro v hv
      rw [hFieldsI v hv _ (by omega)]
      exact f.exteriorData.flags v hv
    · intro v hv
      rw [hFieldsI v hv _ (by omega)]
      exact f.exteriorData.activeNonnegative v hv
    · intro v hv
      rw [hFieldsI v hv _ (by omega),hFieldsI v hv 0 (by omega),hFieldsR v hv _]
      exact f.exteriorData.eligibility v hv
  · intro v hv
    rw [hDomain] at hv
    rw [hFieldsI v hv _ (by omega)]
    exact f.virtualExcluded v hv
  · intro v hv
    rw [hDomain] at hv
    rw [hFieldsI v hv _ (by omega)]
    exact f.highFlags v hv
  · intro v hv
    rw [hDomain] at hv
    rw [hFrame,hFieldsI v hv _ (by omega),hFieldsI v hv 0 (by omega),hFieldsR v hv _,f.activeFlags v hv,f.residual v hv]
    simp only [Finset.mem_image,Fin.val_inj,exists_eq_right,Finset.mem_filter]
    by_cases ha : v ∈ (logical.frames j).active
    · rw [hDegree v ha]
      simp [ha,LocalPush.deg,compiler_graph_neighbor_degree]
    · simp [ha]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeSelectedPendingMemory

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 10000000 in
def episode_selected_pending_memory {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState} (m : SolveModel)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hI : out.scalar.integerMemory=episodeRawIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=episodeRawRealMemory st.scalar.core.mem logical)
    (hCache : ∀ v ∈ parentDomain logical logical.top,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0) :
    FramePendingKeys g (compilerBeginEpisode m g logical) logical.top (16*(ell+3)) length out
      (128+32*((ell+2 : ℕ) : ℤ)) := by
  let f := pm.frames logical.top le_rfl
  let Q := max (∑ v ∈ (logical.frames logical.top).active, (logical.frames logical.top).residual v)
    ((logical.frames logical.top).q*((logical.frames logical.top).block : ℝ))
  let theta := Q/((logical.frames logical.top).block : ℝ)
  have hWords := episode_raw_cache_words st.scalar.integerMemory logical ell
  refine f.reset_cache_pending (next := compilerBeginEpisode m g logical) Q 0 theta
    (if (logical.frames logical.top).needFull then .fullSolve else .normalize) true 0
    (compiler_begin_selected m g logical) (compiler_begin_domain m g logical logical.top) hFree
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hCache ?_ ?_
  · intro slot hs hOther
    rw [hI]
    exact episode_raw_integer_header_same _ _ _ _ hOther
  · intro slot hs hOther
    rw [hR]
    exact episode_header_real_same _ _ _ _ _ hOther
  · rw [hI]
    exact episode_raw_pc _ _ _
  · rw [hR]
    simp [episodeRawRealMemory,episodeHeaderRealMemory,Q]
  · rw [hR]
    simp [episodeRawRealMemory,episodeHeaderRealMemory]
  · rw [hR]
    simp [episodeRawRealMemory,episodeHeaderRealMemory,Q,theta]
  · rw [hI]
    exact hWords.2.2.2.1
  · rw [hI]
    exact hWords.2.2.2.2
  · rw [hI]
    exact hWords.1
  · rw [hI]
    exact hWords.2.1
  · rw [hI]
    exact hWords.2.2.1
  · intro v hv field hField
    rw [hI]
    exact episode_raw_integer_field _ _ _ hDepth v field (by omega) (by omega)
  · intro v hv field
    rw [hR]
    exact episode_raw_real_field _ _ _ _ _
  · intro v hv
    apply pm.knownDegree
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hStored hv))
  · intro z hz
    rw [hI]
    exact episode_raw_integer_above _ _ _ hDepth z (f.owned_above z hz)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeOtherFrameMemory

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 8000000 in
def episode_other_frame_memory {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState} (m : SolveModel)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hI : out.scalar.integerMemory=episodeRawIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=episodeRawRealMemory st.scalar.core.mem logical)
    (j : ℕ) (hj : j ≤ logical.top) (hOther : j ≠ logical.top) :
    RecursiveFrameMemory g (compilerBeginEpisode m g logical) j (16*(ell+3)) length out
      (128+32*((ell+2 : ℕ) : ℤ)) := by
  let f := pm.frames j hj
  let logicalFrame := f.logical_frame (compiler_begin_other m g logical j hOther) (compiler_begin_domain m g logical j)
  refine logicalFrame.scoped_frame hFree ?_ ?_ ?_ ?_ ?_
  · intro slot hs
    rw [hI]
    exact episode_raw_integer_header_other _ _ _ _ _ hOther hs
  · intro slot hs
    rw [hR]
    exact episode_raw_real_header_other _ _ _ _ hOther hs
  · intro v hv field hf hScope
    rw [hI]
    exact episode_raw_integer_field _ _ _ hDepth v field (by omega) (by omega)
  · intro v hv field hf hScope
    rw [hR]
    exact episode_raw_real_field _ _ _ _ _
  · intro z hz
    have hOld : z ∈ f.owned := hz
    rw [hI]
    exact episode_raw_integer_above _ _ _ hDepth z (f.owned_above z hOld)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodePendingMachineMemory

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 16000000 in
def episode_pending_machine_memory {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState} (m : SolveModel)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hI : out.scalar.integerMemory=episodeRawIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=episodeRawRealMemory st.scalar.core.mem logical)
    (hCache : ∀ v ∈ parentDomain logical logical.top,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : MachinePendingKeys g s α ε ell length (compilerBeginEpisode m g logical) out := by
  classical
  have hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 := le_of_eq (hP 20 (by simp)).symm
  let selected := episode_selected_pending_memory m pm hDepth hStored hFree hI hR hCache
  let next := compilerBeginEpisode m g logical
  let frames : ∀ j ≤ next.top, FramePendingKeys g next j (16*(ell+3)) length out (128+32*((ell+2 : ℕ) : ℤ)) :=
    fun j hj => if hEq : j=logical.top then by subst j; exact selected
      else FramePendingKeys.ofMemory (episode_other_frame_memory m pm hDepth hFree hI hR j hj hEq)
  have hOwned : ∀ j, ∀ hj : j ≤ next.top, (frames j hj).owned ⊆ (pm.frames j hj).owned := by
    intro j hj
    dsimp only [frames]
    by_cases hEq : j=logical.top
    · subst j
      rw [dif_pos rfl]
      change (pm.frames logical.top le_rfl).activeFoot ∪ ∅ ∪ (pm.frames logical.top le_rfl).exteriorObject.cells ∪
        (pm.frames logical.top le_rfl).highObject.cells ⊆ (pm.frames logical.top le_rfl).owned
      intro z hz
      simp only [RecursiveFrameMemory.owned,Finset.mem_union,Finset.notMem_empty,or_false] at hz ⊢
      tauto
    · rw [dif_neg hEq]
      exact Finset.Subset.rfl
  have hFields : ∀ v : Fin n, ∀ field < 3,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field) := by
    intro v field hf
    rw [hI]
    exact episode_raw_integer_field _ _ _ hDepth v field (by omega) (by omega)
  have hGraph : GraphCache g out.scalar.integerMemory (16*(ell+3)) logical.stored (out.scalar.core.ptrs 20) := by
    apply (pm.graphCache.frame g _ _ _ _ _ hFields ?_).mono_free hFree
    intro v hv i hi
    rw [hI]
    apply episode_raw_integer_above _ _ _ hDepth
    have hBase := pm.rowAbove v hv
    have hi0 := Int.natCast_nonneg i
    omega
  have hGlobal : ∀ z, 0 ≤ z → z < 128 → out.scalar.integerMemory z=st.scalar.integerMemory z := by
    intro z hz h128
    rw [hI]
    exact episode_raw_integer_global _ _ _ z hz h128
  have hVertexR : ∀ v : Fin n, ∀ field,
      out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field) := by
    intro v field
    rw [hR]
    exact episode_raw_real_field _ _ _ _ _
  have hRealGlobal : ∀ z, z < 128 → out.scalar.core.mem z=st.scalar.core.mem z := by
    intro z hz
    rw [hR]
    exact episode_header_real_below _ _ _ _ _ hz
  refine {
    zero := (hP 0 (by simp)).trans pm.zero
    top := (hP 100 (by simp)).trans pm.top
    width := (hP 50 (by simp)).trans pm.width
    alphaRegister := (hG 30 (by simp)).trans pm.alphaRegister
    one := (hG 31 (by simp)).trans pm.one
    alphaMemory := (hRealGlobal 0 (by omega)).trans pm.alphaMemory
    epsilonMemory := (hRealGlobal 1 (by omega)).trans pm.epsilonMemory
    depthMemory := (hGlobal 2 (by omega) (by omega)).trans pm.depthMemory
    lengthMemory := (hGlobal 5 (by omega) (by omega)).trans pm.lengthMemory
    seedMemory := (hGlobal 0 (by omega) (by omega)).trans pm.seedMemory
    allocator := by rw [hP 20 (by simp)]; exact pm.allocator
    potential := fun v => (hVertexR v 0).trans (pm.potential v)
    seedMarker := fun v => (hVertexR v 2).trans (pm.seedMarker v)
    boundary := (hGlobal 7 (by omega) (by omega)).trans pm.boundary
    graphCache := hGraph
    rowAbove := fun v hv => by rw [hFields v 1 (by decide)]; exact pm.rowAbove v hv
    knownDegree := fun v hv => (hFields v 0 (by decide)).trans (pm.knownDegree v hv)
    unknownDegree := fun v hv => (hFields v 0 (by decide)).trans (pm.unknownDegree v hv)
    frames := frames
    pieceSeparation := ?_
    frameSeparation := fun i hi j hj hij => (pm.frameSeparation i hi j hj hij).mono (hOwned i hi) (hOwned j hj)
    cacheSeparation := ?_
    output := hO.trans pm.output
  }
  · intro j hj
    dsimp only [frames]
    by_cases hEq : j=logical.top
    · subst j
      rw [dif_pos rfl]
      have hOld := pm.pieceSeparation logical.top le_rfl
      change ([(pm.frames logical.top le_rfl).activeFoot,∅,(pm.frames logical.top le_rfl).exteriorObject.cells,
        (pm.frames logical.top le_rfl).highObject.cells] : List (Finset ℤ)).Pairwise Disjoint
      change ([(pm.frames logical.top le_rfl).activeFoot,(pm.frames logical.top le_rfl).cacheFoot,
        (pm.frames logical.top le_rfl).exteriorObject.cells,(pm.frames logical.top le_rfl).highObject.cells] : List (Finset ℤ)).Pairwise Disjoint at hOld
      simp [List.pairwise_cons] at hOld ⊢
      tauto
    · rw [dif_neg hEq]
      exact pm.pieceSeparation j hj
  · intro j hj
    change Disjoint (frames j hj).owned (cachedRowCells g out.scalar.integerMemory (16*(ell+3)) logical.stored)
    rw [cached_row_cells_congr g logical.stored (16*(ell+3)) st.scalar.integerMemory out.scalar.integerMemory (fun v hv => hFields v 1 (by decide))]
    exact (pm.cacheSeparation j hj).mono_left (hOwned j hj)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodePendingMachineProperties

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma episode_pending_machine_owned {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState} (m : SolveModel)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hI : out.scalar.integerMemory=episodeRawIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=episodeRawRealMemory st.scalar.core.mem logical)
    (hCache : ∀ v ∈ parentDomain logical logical.top,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) (j : ℕ) (hj : j ≤ logical.top) :
    ((episode_pending_machine_memory m pm hDepth hStored hI hR hCache hP hG hO).frames j hj).owned ⊆ (pm.frames j hj).owned := by
  classical
  dsimp only [episode_pending_machine_memory]
  by_cases hEq : j=logical.top
  · subst j
    rw [dif_pos rfl]
    change (pm.frames logical.top le_rfl).activeFoot ∪ ∅ ∪ (pm.frames logical.top le_rfl).exteriorObject.cells ∪
      (pm.frames logical.top le_rfl).highObject.cells ⊆ (pm.frames logical.top le_rfl).owned
    intro z hz
    simp only [RecursiveFrameMemory.owned,Finset.mem_union,Finset.notMem_empty,or_false] at hz ⊢
    tauto
  · rw [dif_neg hEq]
    exact Finset.Subset.rfl

lemma episode_pending_machine_frame_mass {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState} (m : SolveModel)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hI : out.scalar.integerMemory=episodeRawIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=episodeRawRealMemory st.scalar.core.mem logical)
    (hCache : ∀ v ∈ parentDomain logical logical.top,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) (j : ℕ) (hj : j ≤ logical.top) :
    ((episode_pending_machine_memory m pm hDepth hStored hI hR hCache hP hG hO).frames j hj).queueMass=(pm.frames j hj).queueMass := by
  classical
  dsimp only [episode_pending_machine_memory]
  by_cases hEq : j=logical.top
  · subst j
    rw [dif_pos rfl]
    rfl
  · rw [dif_neg hEq]
    rfl

lemma episode_pending_machine_exterior_keys {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState} (m : SolveModel)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hI : out.scalar.integerMemory=episodeRawIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=episodeRawRealMemory st.scalar.core.mem logical)
    (hCache : ∀ v ∈ parentDomain logical logical.top,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) (j : ℕ) (hj : j ≤ logical.top) :
    ((episode_pending_machine_memory m pm hDepth hStored hI hR hCache hP hG hO).frames j hj).exteriorObject.keys=(pm.frames j hj).exteriorObject.keys := by
  classical
  dsimp only [episode_pending_machine_memory]
  by_cases hEq : j=logical.top
  · subst j
    rw [dif_pos rfl]
    rfl
  · rw [dif_neg hEq]
    rfl

lemma episode_pending_machine_high_keys {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState} (m : SolveModel)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hI : out.scalar.integerMemory=episodeRawIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=episodeRawRealMemory st.scalar.core.mem logical)
    (hCache : ∀ v ∈ parentDomain logical logical.top,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) (j : ℕ) (hj : j ≤ logical.top) :
    ((episode_pending_machine_memory m pm hDepth hStored hI hR hCache hP hG hO).frames j hj).highObject.keys=(pm.frames j hj).highObject.keys := by
  classical
  dsimp only [episode_pending_machine_memory]
  by_cases hEq : j=logical.top
  · subst j
    rw [dif_pos rfl]
    rfl
  · rw [dif_neg hEq]
    rfl

lemma episode_pending_machine_mass {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState} (m : SolveModel)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hI : out.scalar.integerMemory=episodeRawIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=episodeRawRealMemory st.scalar.core.mem logical)
    (hCache : ∀ v ∈ parentDomain logical logical.top,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : (episode_pending_machine_memory m pm hDepth hStored hI hR hCache hP hG hO).queueMass=pm.queueMass := by
  unfold MachinePendingKeys.queueMass RecursiveMachineMemory.queueMass
  change (∑ j ∈ Finset.range (logical.top+1), if hj : j ≤ logical.top then
    ((episode_pending_machine_memory m pm hDepth hStored hI hR hCache hP hG hO).frames j hj).queueMass else 0)= _
  apply Finset.sum_congr rfl
  intro j hj
  have hLive : j ≤ logical.top := by have := Finset.mem_range.mp hj; omega
  simp only [dif_pos hLive]
  exact episode_pending_machine_frame_mass m pm hDepth hStored hI hR hCache hP hG hO j hLive

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodePendingExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 16000000 in
lemma episode_pending_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hSubset : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hCacheSubset : (logical.frames logical.top).cache ⊆ (logical.frames logical.top).active) :
    ∃ steps out, ∃ pending : MachinePendingKeys g s α ε ell length (compilerBeginEpisode m g logical) out,
      MachineEval m g ω episodeRawCode st steps out ∧
      steps ≤ 2*(4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+169 ∧
      pending.queueMass=pm.queueMass ∧
      (∀ j, ∀ hj : j ≤ logical.top, (pending.frames j hj).owned ⊆ (pm.frames j hj).owned) ∧
      (∀ j, ∀ hj : j ≤ logical.top, (pending.frames j hj).exteriorObject.keys=(pm.frames j hj).exteriorObject.keys) ∧
      (∀ j, ∀ hj : j ≤ logical.top, (pending.frames j hj).highObject.keys=(pm.frames j hj).highObject.keys) ∧
      out.scalar.integerMemory=episodeRawIntegerMemory st.scalar.integerMemory logical ell ∧
      out.scalar.core.mem=episodeRawRealMemory st.scalar.core.mem logical ∧
      out.work=st.work+steps ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨steps,out,ex,hSteps,hI,hR,hCache,hW,hQuery,hO,hH⟩ := episode_raw_exec m g ω logical s α ε ell length st hh pm hDepth hSubset hCacheSubset
  have hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ex.pointer_frame _ (by decide)
  have hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ex.real_register_frame _ (by decide)
  let pending := episode_pending_machine_memory m pm hDepth hStored hI hR hCache hP hG hO
  exact ⟨steps,out,pending,ex,hSteps,episode_pending_machine_mass m pm hDepth hStored hI hR hCache hP hG hO,
    episode_pending_machine_owned m pm hDepth hStored hI hR hCache hP hG hO,
    episode_pending_machine_exterior_keys m pm hDepth hStored hI hR hCache hP hG hO,
    episode_pending_machine_high_keys m pm hDepth hStored hI hR hCache hP hG hO,hI,hR,hW,hQuery,hO,hH⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeInitialVisited

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 10000000 in
lemma episode_initial_visited {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState} (m : SolveModel)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (next : MachinePendingKeys g s α ε ell length (compilerBeginEpisode m g logical) out)
    (hDepth : logical.top ≤ ell) (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hI : out.scalar.integerMemory=episodeRawIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=episodeRawRealMemory st.scalar.core.mem logical)
    (hExtKeys : ∀ j, ∀ hj : j ≤ logical.top, (next.frames j hj).exteriorObject.keys=(pm.frames j hj).exteriorObject.keys)
    (hHighKeys : ∀ j, ∀ hj : j ≤ logical.top, (next.frames j hj).highObject.keys=(pm.frames j hj).highObject.keys) :
    PendingVisitedKeys next (Finset.univ \ (logical.frames logical.top).active) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro j hj v hv
    have hvD := (Finset.mem_inter.mp hv).1
    have hInactive := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).2).2
    by_cases hEq : j=logical.top
    · subst j
      have hvOld : v ∈ parentDomain logical logical.top := by simpa only [compiler_begin_domain] using hvD
      have hActiveOld : st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+2))=0 := by
        rw [(pm.frames logical.top le_rfl).activeFlags v hvOld,if_neg hInactive]
      have hActiveNew : out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+2))=0 := by
        rw [hI,episode_raw_integer_field _ _ _ hDepth v _ (by omega) (by omega),hActiveOld]
      have hBit : st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0 := by
        simpa [hActiveOld] using (pm.frames logical.top le_rfl).highBoolean v hvOld
      simp only [hActiveNew,if_true]
      rw [hR,episode_raw_real_field]
      exact hBit
    · exact (episode_other_frame_memory m pm hDepth hFree hI hR j hj hEq).highBoolean v hvD
  · intro j hj v hv hKey
    have hSame : ((compilerBeginEpisode m g logical).frames j).exterior=(logical.frames j).exterior := by
      by_cases hEq : j=logical.top
      · subst j
        rw [compiler_begin_selected]
      · rw [compiler_begin_other m g logical j hEq]
    rw [hSame] at hKey
    rw [hExtKeys j hj]
    exact (pm.frames j hj).exteriorCover (Finset.mem_image.mpr ⟨v,hKey,rfl⟩)
  · intro j hj v hv hKey
    by_cases hEq : j=logical.top
    · subst j
      have hInactive := (Finset.mem_sdiff.mp hv).2
      rw [compiler_begin_selected] at hKey
      exact False.elim (hInactive (Finset.mem_filter.mp hKey).1)
    · rw [compiler_begin_other m g logical j hEq] at hKey
      rw [hHighKeys j hj]
      exact (pm.frames j hj).highCover (Finset.mem_image.mpr ⟨v,hKey,rfl⟩)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EnumeratedEpisodePendingExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma enumeratedEpisodePendingCode_wellFormed : enumeratedEpisodePendingCode.wellFormed :=
  ⟨levelHeaderIntegerToCode_wellFormed 1 90,vertexEnumerationCode_wellFormed,episodeRawCode_wellFormed⟩

set_option maxHeartbeats 18000000 in
lemma enumerated_episode_pending_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hSubset : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hCacheSubset : (logical.frames logical.top).cache ⊆ (logical.frames logical.top).active) :
    let vertices := (pm.frames logical.top le_rfl).activeVertices
    ∃ steps out, ∃ pending : MachinePendingKeys g s α ε ell length (compilerBeginEpisode m g logical) out,
      ∃ base : ℤ, MachineEval m g ω enumeratedEpisodePendingCode st steps out ∧
      steps ≤ (2*(4*(16*(ell+3))+17)+10)*(logical.frames logical.top).active.card+184 ∧
      pending.queueMass=pm.queueMass ∧
      PendingEnumerationBuffer pending base (vertexEnumeration vertices) ∧
      PendingVisitedKeys pending (Finset.univ \ (logical.frames logical.top).active) ∧
      out.scalar.core.ptrs 80=base ∧ out.scalar.core.ptrs 77=(vertices.length : ℤ) ∧
      out.work=st.work+steps ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ z : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) z.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) z.val 7)) := by
  dsimp only
  let f := pm.frames logical.top le_rfl
  obtain ⟨a,ea,a90,aI,aR,aW,aO,aH⟩ := level_header_integer_to_exec m g ω st hh logical.top 1 90 pm.top
  have aP : ∀ r ∈ ([0,20,50,100] : List ℕ), a.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ea.pointer_frame _ (by decide)
  have aG : ∀ r ∈ ([30,31] : List ℕ), a.scalar.core.regs r=st.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ea.real_register_frame _ (by decide)
  let am := pm.frame aI aR aP aG aO
  have hList : VertexListRep a.scalar.integerMemory (st.scalar.integerMemory (levelHeaderAddress logical.top 1)) f.activeVertices f.activeFoot := by
    rw [aI]
    exact f.activeRep
  have hBelow : ∀ z ∈ f.activeFoot, z < a.scalar.core.ptrs 20 := by
    intro z hz
    rw [aP 20 (by simp)]
    exact f.activeBelow z hz
  obtain ⟨b,bm,eb,b80,b77,b20,bEnum,bBelow,bForeign,bMass,bI,bR,bW,bO,bH⟩ := vertex_enumeration_memory_exec m g ω logical s α ε ell length
    f.activeVertices (st.scalar.integerMemory (levelHeaderAddress logical.top 1)) f.activeFoot a aH am hDepth a90 hList hBelow
  obtain ⟨u,out,pending,ec,hu,hMass,hOwned,hExt,hHigh,hI,hR,hWork,hQuery,hOutput,hHalt⟩ :=
    episode_pending_exec m g ω logical s α ε ell length b bH bm hDepth hStored hSubset hCacheSubset
  have hFree : b.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 := le_of_eq (ec.pointer_frame 20 (by decide)).symm
  have hBase : 128+32*((ell+2 : ℕ) : ℤ) ≤ a.scalar.core.ptrs 20 := am.allocator
  have buffer : PendingEnumerationBuffer pending (a.scalar.core.ptrs 20) (vertexEnumeration f.activeVertices) := by
    refine ⟨by omega,?_,?_,?_⟩
    · intro i
      exact (bBelow i).trans_le hFree
    · intro i j hj hz
      exact bForeign i j hj (hOwned j hj hz)
    · intro i
      rw [hI,episode_raw_integer_above _ _ _ hDepth _ (by have := Int.natCast_nonneg i.val; omega)]
      exact bEnum i
  have inv := episode_initial_visited m bm pending hDepth hFree hI hR hExt hHigh
  have hLength : f.activeVertices.length=(logical.frames logical.top).active.card := by
    rw [←f.activeSet,List.toFinset_card_of_nodup f.activeNodup]
  have ex : MachineEval m g ω enumeratedEpisodePendingCode st (10+((10*f.activeVertices.length+5)+u)) out :=
    MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨_,out,pending,a.scalar.core.ptrs 20,ex,?_,?_,buffer,inv,?_,?_,
    ex.unit_work enumeratedEpisodePendingCode_wellFormed (by decide) hh,
    hQuery.trans (eb.query_frame (by decide) |>.trans (ea.query_frame (by decide))),hOutput.trans (bO.trans aO),hHalt,?_⟩
  · rw [hLength]
    nlinarith
  · rw [hMass,bMass]
    rfl
  · exact (ec.pointer_frame 80 (by decide)).trans b80
  · exact (ec.pointer_frame 77 (by decide)).trans b77
  · intro z
    rw [hI,episode_raw_integer_field _ _ _ hDepth z 7 (by omega) (by omega)]
    exact (bI _ (by
      have hNeg := vertexRecordAddress_negative (16*(ell+3)) z.val 7
      have hAlloc := am.allocator
      omega)).trans (congrFun aI _)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerBeginEpisodeRegion

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_begin_region {n : ℕ} (m : SolveModel) (g : InputGraph n)
    (logical : RecursiveState n) (hRegion : RegionInvariant logical) :
    RegionInvariant (compilerBeginEpisode m g logical) := by
  classical
  intro j hj
  change j ≤ logical.top at hj
  have h := hRegion j hj
  rw [compiler_begin_domain]
  by_cases hEq : j=logical.top
  · subst j
    rw [compiler_begin_selected]
    exact ⟨h.1,h.2.1,Finset.filter_subset _ _,Finset.empty_subset _⟩
  · rw [compiler_begin_other m g logical j hEq]
    exact h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BeginEpisodeExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 18000000 in
lemma begin_episode_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hDepth : logical.top ≤ ell) (hRegion : RegionInvariant logical)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hMass : pm.queueMass+2*(logical.top+1)*(logical.frames logical.top).active.card ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length
      (compilerBeginEpisode m g logical) out,
      MachineEval m g ω beginEpisodeCode st steps out ∧
      steps ≤ ((2*(4*(16*(ell+3))+17)+10)+
        ((logical.top+1)*(42*rank+60*(16*(ell+3))+284)+11))*
        (logical.frames logical.top).active.card+188 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*(logical.frames logical.top).active.card ∧
      out.work=st.work+steps ∧ out.scalar.queries=st.scalar.queries ∧
      out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ z : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) z.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) z.val 7)) := by
  classical
  let f := pm.frames logical.top le_rfl
  let vertices := f.activeVertices
  let e := vertexEnumeration vertices
  have hLength : vertices.length=(logical.frames logical.top).active.card := by
    rw [←f.activeSet,List.toFinset_card_of_nodup f.activeNodup]
  have hEnum : Finset.univ.image e=(logical.frames logical.top).active :=
    (vertex_enumeration_domain vertices).trans f.activeSet
  obtain ⟨a,mid,pending,base,ea,ha,hm,buffer,inv,h80,h77,haW,haQ,haO,haH,haIndex⟩ :=
    enumerated_episode_pending_exec m g ω logical s α ε ell length st hh pm hDepth hStored
      (hRegion logical.top le_rfl).1 (hRegion logical.top le_rfl).2.2.2
  have region := compiler_begin_region m g logical hRegion
  have activeDomain : ∀ j ≤ (compilerBeginEpisode m g logical).top,
      ((compilerBeginEpisode m g logical).frames j).active ⊆
        parentDomain (compilerBeginEpisode m g logical) j := fun j hj => (region j hj).1
  have extDomain : ∀ j ≤ (compilerBeginEpisode m g logical).top,
      ((compilerBeginEpisode m g logical).frames j).exterior ⊆
        parentDomain (compilerBeginEpisode m g logical) j := by
    intro j hj v hv
    exact Finset.mem_sdiff.mp ((region j hj).2.1 hv) |>.1
  have highDomain : ∀ j ≤ (compilerBeginEpisode m g logical).top,
      ((compilerBeginEpisode m g logical).frames j).high ⊆
        parentDomain (compilerBeginEpisode m g logical) j := by
    intro j hj v hv
    exact (region j hj).1 ((region j hj).2.2.1 hv)
  have outside : ∀ v ∉ Finset.univ.image e,
      v ∈ Finset.univ \ (logical.frames logical.top).active := by
    intro v hv
    rw [hEnum] at hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩
  have hMass' : pending.queueMass+2*((compilerBeginEpisode m g logical).top+1)*vertices.length ≤ N := by
    rw [hm,compiler_begin_top,hLength]
    exact hMass
  obtain ⟨b,out,memory,eb,hb,hMassOut,hFrame,hbW,hbQ,hbO,hbH⟩ :=
    pending_array_refresh_exec m g ω (compilerBeginEpisode m g logical) s α ε ell length N rank
      e base (Finset.univ \ (logical.frames logical.top).active) mid haH pending buffer inv
      hDepth activeDomain extDomain highDomain outside h80 h77 hMass' hCap hPow
  have ex : MachineEval m g ω beginEpisodeCode st (a+b) out := MachineEval.seq ea eb
  refine ⟨_,out,memory,ex,?_,?_,?_,hbQ.trans haQ,hbO.trans haO,hbH,fun z => (hFrame.indexFrame z).trans (haIndex z)⟩
  · rw [compiler_begin_top,hLength] at hb
    nlinarith
  · simpa only [hm,compiler_begin_top,hLength] using hMassOut
  · rw [hbW,haW]
    simp only [Nat.cast_add,add_assoc]

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution : ∀ (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hDepth : logical.top ≤ ell) (hRegion : RegionInvariant logical)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hMass : pm.queueMass+2*(logical.top+1)*(logical.frames logical.top).active.card ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank),
∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length
      (compilerBeginEpisode m g logical) out,
      MachineEval m g ω beginEpisodeCode st steps out ∧
      steps ≤ ((2*(4*(16*(ell+3))+17)+10)+
        ((logical.top+1)*(42*rank+60*(16*(ell+3))+284)+11))*
        (logical.frames logical.top).active.card+188 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*(logical.frames logical.top).active.card ∧
      out.work=st.work+steps ∧ out.scalar.queries=st.scalar.queries ∧
      out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ z : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) z.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) z.val 7)) := by
  exact @NearlyOptimalPPR.Computation.begin_episode_exec
