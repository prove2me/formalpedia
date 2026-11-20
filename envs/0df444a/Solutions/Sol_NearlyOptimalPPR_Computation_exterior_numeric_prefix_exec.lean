-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.exterior_numeric_prefix_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:46:18.728171+00:00
-- url     : https://prove2.me/submissions/d1a4df7a-b611-41f1-b50c-f17550c58040

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

lemma vertexFieldWriteCode_queryReadOnly (field source : ℕ) :
    (vertexFieldWriteCode field source).allAtoms queryReadOnly := by
  simp [vertexFieldWriteCode,fieldWritePrepRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    vertexIntegerStoreCode,MachineCode.allAtoms,queryReadOnly,vertexAddressCode_queryReadOnly]

lemma vertexFieldWriteCode_wellFormed (field source : ℕ) : (vertexFieldWriteCode field source).wellFormed := by
  simp [vertexFieldWriteCode,fieldWritePrepRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    vertexIntegerStoreCode,MachineCode.wellFormed,vertexAddressCode_wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 1000000 in
lemma vertex_field_write_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex field source : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) :
    ∃ out, MachineEval m g ω (vertexFieldWriteCode field source) st (4*width+9) out ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (vertexRecordAddress width vertex field) (st.scalar.core.ptrs source) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(4*width+9 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,ep,hp,hI,hR,hW,hO,hH⟩ := (fieldWritePrepRoutine field source).execute m g ω st hh
  have ep2 : MachineEval m g ω (fieldWritePrepRoutine field source).code st 2 pre := ep
  have h0 : pre.scalar.core.ptrs 0=0 := (ep.pointer_frame 0 (by simp [fieldWritePrepRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,MachineCode.pointerTargets,pointerTargets])).trans hz
  have h40 : pre.scalar.core.ptrs 40=(vertex : ℤ) := (ep.pointer_frame 40 (by simp [fieldWritePrepRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,MachineCode.pointerTargets,pointerTargets])).trans hv
  have h41 : pre.scalar.core.ptrs 41=(width : ℤ) := (ep.pointer_frame 41 (by simp [fieldWritePrepRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,MachineCode.pointerTargets,pointerTargets])).trans hw
  have h44 : pre.scalar.core.ptrs 44=(field : ℤ) := by
    rw [hp]; simp [fieldWritePrepRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result]
  have h51 : pre.scalar.core.ptrs 51=st.scalar.core.ptrs source := by
    rw [hp]; simp [fieldWritePrepRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result]
  obtain ⟨out,es,hoI,hoR,hoW,hoO,hoH⟩ := vertex_integer_store_exec m g ω pre hH width vertex field h0 h40 h41 h44
  have e : MachineEval m g ω (vertexFieldWriteCode field source) st (4*width+9) out := by
    have ee := MachineEval.seq ep2 es
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,e,?_,hoR.trans hR,e.query_frame (vertexFieldWriteCode_queryReadOnly field source),?_,hoO.trans hO,hoH⟩
  · rw [hoI,hI,h51]
  · rw [hoW,hW]
    change st.work+(2 : ℕ)+(4*width+7 : ℕ)= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AdjacencyMetadata

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def adjacencyMetadataWords (I : ℤ → ℤ) (width vertex : ℕ) (degree base : ℤ) : ℤ → ℤ :=
  Function.update (Function.update (Function.update I (vertexRecordAddress width vertex 0) degree)
    (vertexRecordAddress width vertex 1) base) (vertexRecordAddress width vertex 2) 1

lemma adjacencyMetadataCode_wellFormed : adjacencyMetadataCode.wellFormed := by
  refine ⟨vertexFieldWriteCode_wellFormed 0 60,vertexFieldWriteCode_wellFormed 1 61,?_,vertexFieldWriteCode_wellFormed 2 51⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 1200000 in
lemma adjacency_metadata_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) :
    ∃ out, MachineEval m g ω adjacencyMetadataCode st (12*width+28) out ∧
      out.scalar.integerMemory=adjacencyMetadataWords st.scalar.integerMemory width vertex
        (st.scalar.core.ptrs 60) (st.scalar.core.ptrs 61) ∧
      out.scalar.core.ptrs 60=st.scalar.core.ptrs 60 ∧ out.scalar.core.ptrs 61=st.scalar.core.ptrs 61 ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(12*width+28 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨A,ea,hAI,hAR,hAQ,hAW,hAO,hAH⟩ := vertex_field_write_exec m g ω st hh width vertex 0 60 hz hv hw
  have a0 := (ea.pointer_frame 0 (by decide)).trans hz
  have a40 := (ea.pointer_frame 40 (by decide)).trans hv
  have a41 := (ea.pointer_frame 41 (by decide)).trans hw
  have a61 := ea.pointer_frame 61 (by decide)
  obtain ⟨B,eb,hBI,hBR,hBQ,hBW,hBO,hBH⟩ := vertex_field_write_exec m g ω A hAH width vertex 1 61 a0 a40 a41
  rw [a61] at hBI
  let C := payUnit (pointerWrite B 51 1)
  have ec : MachineEval m g ω (coreCode (.pset 51 1)) B 1 C := pset_eval m g ω B 51 1 hBH
  have cH : C.scalar.halted=false := hBH
  have c0 := (ec.pointer_frame 0 (by decide)).trans ((eb.pointer_frame 0 (by decide)).trans a0)
  have c40 := (ec.pointer_frame 40 (by decide)).trans ((eb.pointer_frame 40 (by decide)).trans a40)
  have c41 := (ec.pointer_frame 41 (by decide)).trans ((eb.pointer_frame 41 (by decide)).trans a41)
  have c51 : C.scalar.core.ptrs 51=1 := by simp [C,payUnit,pcSet,pointerWrite]
  obtain ⟨out,ed,hDI,hDR,hDQ,hDW,hDO,hDH⟩ := vertex_field_write_exec m g ω C cH width vertex 2 51 c0 c40 c41
  have e : MachineEval m g ω adjacencyMetadataCode st (12*width+28) out := by
    have ee := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,e,?_,e.pointer_frame 60 (by decide),e.pointer_frame 61 (by decide),
    hDR.trans (hBR.trans hAR),?_,?_,hDO.trans (hBO.trans hAO),hDH⟩
  · rw [hDI,c51]
    change Function.update B.scalar.integerMemory (vertexRecordAddress width vertex 2) 1= _
    rw [hBI,hAI]
    rfl
  · exact e.query_frame (by
      simp [adjacencyMetadataCode,MachineCode.allAtoms,vertexFieldWriteCode_queryReadOnly,coreCode,queryReadOnly])
  · rw [hDW]
    change B.work+1+(4*width+9 : ℕ)= _
    rw [hBW,hAW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.GraphQueryExecution

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma nodeOf_vertex {n : ℕ} (v : Fin n) : LocalPush.nodeOf n (v.val : ℤ)=some v := by
  simp [LocalPush.nodeOf,v.isLt]

lemma degree_answer_vertex {n : ℕ} (g : InputGraph n) (v : Fin n) :
    LocalPush.degAnswer g.neighbors (v.val : ℤ)=((g.neighbors v).length : ℤ) := by
  simp [LocalPush.degAnswer,nodeOf_vertex]

lemma neighbor_answer_vertex {n : ℕ} (g : InputGraph n) (v : Fin n) (i : ℕ)
    (hi : i < (g.neighbors v).length) :
    LocalPush.nbrAnswer g.neighbors (v.val : ℤ) (i : ℤ)=((g.neighbors v)[i].val : ℤ) := by
  simp [LocalPush.nbrAnswer,nodeOf_vertex,List.getElem?_eq_getElem hi]

lemma degree_query_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (d a : ℕ) :
    ∃ out, MachineEval m g ω (.atom (.scalar (.deg d a))) st 1 out ∧
      out.scalar.core.ptrs d=LocalPush.degAnswer g.neighbors (st.scalar.core.ptrs a) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries+1 ∧ out.work=st.work+1 ∧ out.output=st.output ∧
      out.scalar.halted=false := by
  let out := pcSet (atomState m g ω (.scalar (.deg d a)) st) 0
  have hu : unitInstruction (.scalar (.deg d a)) := trivial
  refine ⟨out,MachineEval.atom _ st (unitInstruction_advances m g ω _ hu st hh),?_,?_,?_,?_,?_,?_,?_⟩
  all_goals simp [out,atomState,machineStep,pcSet,LocalPush.step,scalarProgram,hh]

lemma neighbor_query_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (d a b : ℕ) :
    ∃ out, MachineEval m g ω (.atom (.scalar (.nbr d a b))) st 1 out ∧
      out.scalar.core.ptrs d=LocalPush.nbrAnswer g.neighbors (st.scalar.core.ptrs a) (st.scalar.core.ptrs b) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries+1 ∧ out.work=st.work+1 ∧ out.output=st.output ∧
      out.scalar.halted=false := by
  let out := pcSet (atomState m g ω (.scalar (.nbr d a b)) st) 0
  have hu : unitInstruction (.scalar (.nbr d a b)) := trivial
  refine ⟨out,MachineEval.atom _ st (unitInstruction_advances m g ω _ hu st hh),?_,?_,?_,?_,?_,?_,?_⟩
  all_goals simp [out,atomState,machineStep,pcSet,LocalPush.step,scalarProgram,hh]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AdjacencyFetchCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma adjacencyFetchBodyCode_wellFormed : adjacencyFetchBodyCode.wellFormed := by
  simp [adjacencyFetchBodyCode,sequenceCode,coreCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 1000000 in
lemma adjacency_fetch_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (v : Fin n) (base : ℤ) (i : ℕ)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) (hb : st.scalar.core.ptrs 61=base)
    (hi : st.scalar.core.ptrs 62=(i : ℤ)) (hil : i < (g.neighbors v).length) :
    ∃ out, MachineEval m g ω adjacencyFetchBodyCode st 4 out ∧
      out.scalar.core.ptrs 62=(i+1 : ℕ) ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (base+(i : ℤ)) ((g.neighbors v)[i].val : ℤ) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries+1 ∧
      out.work=st.work+4 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨q,eq,hq63,hqI,hqR,hqQueries,hqW,hqO,hqH⟩ := neighbor_query_exec m g ω st hh 63 40 62
  rw [hv,hi,neighbor_answer_vertex g v i hil] at hq63
  have hq61 : q.scalar.core.ptrs 61=base := (eq.pointer_frame 61 (by decide)).trans hb
  have hq62 : q.scalar.core.ptrs 62=(i : ℤ) := (eq.pointer_frame 62 (by decide)).trans hi
  let A := payUnit (pointerWrite q 64 (base+(i : ℤ)))
  let B := payUnit (integerWrite A (base+(i : ℤ)) ((g.neighbors v)[i].val : ℤ))
  let out := payUnit (pointerWrite B 62 (i+1 : ℕ))
  have ea : MachineEval m g ω (.atom (.scalar (.pointerAdd 64 61 62))) q 1 A := by
    simpa only [A,hq61,hq62] using pointerAdd_eval m g ω q 64 61 62 hqH
  have ah : A.scalar.halted=false := hqH
  have eb : MachineEval m g ω (.atom (.scalar (.integerStore 64 63))) A 1 B := by
    have h64 : A.scalar.core.ptrs 64=base+(i : ℤ) := by simp [A,payUnit,pcSet,pointerWrite]
    have h63 : A.scalar.core.ptrs 63=((g.neighbors v)[i].val : ℤ) := by simpa [A,payUnit,pcSet,pointerWrite] using hq63
    simpa only [B,h64,h63] using integerStore_eval m g ω A 64 63 ah
  have bh : B.scalar.halted=false := ah
  have eo : MachineEval m g ω (coreCode (.pinc 62)) B 1 out := by
    have h62 : B.scalar.core.ptrs 62=(i : ℤ) := by simpa [B,A,payUnit,pcSet,integerWrite,pointerWrite] using hq62
    simpa only [out,coreCode,h62,Nat.cast_add,Nat.cast_one] using pinc_eval m g ω B 62 bh
  refine ⟨out,MachineEval.seq eq (MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq eo (MachineEval.skip out)))),
    ?_,?_,hqR,hqQueries,?_,hqO,hqH⟩
  · simp [out,payUnit,pcSet,pointerWrite]
  · change Function.update q.scalar.integerMemory _ _= _
    rw [hqI]
  · change q.work+1+1+1=st.work+4
    rw [hqW]
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AdjacencyFetchLoop

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma adjacencyStored_advance {n : ℕ} (I : ℤ → ℤ) (base : ℤ) (neighbors : List (Fin n))
    (i : ℕ) (hi : i < neighbors.length) (h : AdjacencyStored I base neighbors i) :
    AdjacencyStored (Function.update I (base+(i : ℤ)) (neighbors[i].val : ℤ)) base neighbors (i+1) := by
  intro j hj hj'
  by_cases he : j=i
  · subst j; simp
  · rw [Function.update_of_ne (by omega : base+(j : ℤ) ≠ base+(i : ℤ))]
    exact h j (by omega) hj'

set_option maxHeartbeats 1500000 in
lemma adjacency_fetch_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (v : Fin n) (base : ℤ) (remaining i : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) (hb : st.scalar.core.ptrs 61=base)
    (hd : st.scalar.core.ptrs 60=((g.neighbors v).length : ℤ)) (hi : st.scalar.core.ptrs 62=(i : ℤ))
    (hlen : i+remaining=(g.neighbors v).length)
    (hstored : AdjacencyStored st.scalar.integerMemory base (g.neighbors v) i) :
    ∃ out, MachineEval m g ω adjacencyFetchLoopCode st (6*remaining+1) out ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧ out.scalar.core.ptrs 61=base ∧
      out.scalar.core.ptrs 60=((g.neighbors v).length : ℤ) ∧ out.scalar.core.ptrs 62=((g.neighbors v).length : ℤ) ∧
      AdjacencyStored out.scalar.integerMemory base (g.neighbors v) (g.neighbors v).length ∧
      (∀ z, z ∉ arrayCells base (g.neighbors v).length → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries+remaining ∧
      out.work=st.work+(6*remaining+1 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction remaining generalizing st i with
  | zero =>
    have he : i=(g.neighbors v).length := by omega
    refine ⟨payUnit st,?_,hv,hb,hd,by simpa [he] using hi,by simpa only [he,payUnit,pcSet] using hstored,
      (by intros; rfl),rfl,by simp [payUnit,pcSet],by simp,rfl,hh⟩
    exact MachineEval.pointerDone (r:=60) (s:=62) (body:=adjacencyFetchBodyCode) hh (by rw [hd,hi,he])
  | succ remaining ih =>
    have hil : i < (g.neighbors v).length := by omega
    obtain ⟨mid,eb,hmid62,hmidI,hmidR,hmidQ,hmidW,hmidO,hmidH⟩ :=
      adjacency_fetch_body_exec m g ω (payUnit st) hh v base i hv hb hi hil
    have hm40 : mid.scalar.core.ptrs 40=(v.val : ℤ) := (eb.pointer_frame 40 (by decide)).trans hv
    have hm61 : mid.scalar.core.ptrs 61=base := (eb.pointer_frame 61 (by decide)).trans hb
    have hm60 : mid.scalar.core.ptrs 60=((g.neighbors v).length : ℤ) := (eb.pointer_frame 60 (by decide)).trans hd
    have hmidStored : AdjacencyStored mid.scalar.integerMemory base (g.neighbors v) (i+1) := by
      rw [hmidI]
      exact adjacencyStored_advance _ _ _ i hil hstored
    obtain ⟨out,er,ho40,ho61,ho60,ho62,hoStored,hoFrame,hoR,hoQ,hoW,hoO,hoH⟩ :=
      ih (i+1) (payUnit mid) hmidH hm40 hm61 hm60 hmid62 (by omega) hmidStored
    refine ⟨out,?_,ho40,ho61,ho60,ho62,hoStored,?_,hoR.trans hmidR,?_,?_,hoO.trans hmidO,hoH⟩
    · have e := MachineEval.pointerNext (r:=60) (s:=62) hh (by rw [hd,hi]; omega) eb er
      convert e using 1 <;> (first | rfl | omega)
    · intro z hz
      have he : z ≠ base+(i : ℤ) := by
        intro he
        apply hz
        exact (mem_arrayCells _ _ _).mpr ⟨i,hil,he⟩
      have hmidFrame : mid.scalar.integerMemory z=st.scalar.integerMemory z := by
        rw [hmidI,Function.update_of_ne he]
        rfl
      exact (hoFrame z hz).trans hmidFrame
    · change out.scalar.queries=st.scalar.queries+(remaining+1)
      change out.scalar.queries=mid.scalar.queries+remaining at hoQ
      change mid.scalar.queries=st.scalar.queries+1 at hmidQ
      rw [hoQ,hmidQ]
      omega
    · rw [hoW,payUnit_work,hmidW,payUnit_work]
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AdjacencyStorage

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma adjacencyStorageCode_wellFormed : adjacencyStorageCode.wellFormed := by
  simp [adjacencyStorageCode,adjacencyReserveRoutine,PointerRoutine.sequence,PointerRoutine.code,
    PointerOp.instruction,adjacencyFetchLoopCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible,adjacencyFetchBodyCode_wellFormed]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AdjacencyMetadataSemantics

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma vertexRecordAddress_offset_injective (width vertex i j : ℕ)
    (h : vertexRecordAddress width vertex i=vertexRecordAddress width vertex j) : i=j := by
  unfold vertexRecordAddress at h
  omega

lemma adjacencyMetadataWords_self (I : ℤ → ℤ) (width vertex : ℕ) (degree base : ℤ) :
    adjacencyMetadataWords I width vertex degree base (vertexRecordAddress width vertex 0)=degree ∧
    adjacencyMetadataWords I width vertex degree base (vertexRecordAddress width vertex 1)=base ∧
    adjacencyMetadataWords I width vertex degree base (vertexRecordAddress width vertex 2)=1 := by
  have h01 : vertexRecordAddress width vertex 0 ≠ vertexRecordAddress width vertex 1 := by
    intro he; have h := vertexRecordAddress_offset_injective _ _ _ _ he; omega
  have h02 : vertexRecordAddress width vertex 0 ≠ vertexRecordAddress width vertex 2 := by
    intro he; have h := vertexRecordAddress_offset_injective _ _ _ _ he; omega
  have h12 : vertexRecordAddress width vertex 1 ≠ vertexRecordAddress width vertex 2 := by
    intro he; have h := vertexRecordAddress_offset_injective _ _ _ _ he; omega
  simp [adjacencyMetadataWords,Function.update_of_ne h01,Function.update_of_ne h02,Function.update_of_ne h12]

lemma adjacencyMetadataWords_other (I : ℤ → ℤ) (width vertex other field : ℕ)
    (hw : 3 ≤ width) (hf : field < width) (ho : other ≠ vertex) (degree base : ℤ) :
    adjacencyMetadataWords I width vertex degree base (vertexRecordAddress width other field)=
      I (vertexRecordAddress width other field) := by
  have hn (i : ℕ) (hi : i < 3) : vertexRecordAddress width other field ≠ vertexRecordAddress width vertex i := by
    intro he
    exact ho (vertexRecordAddress_injective width other vertex field i hf (by omega) he).1
  simp [adjacencyMetadataWords,Function.update_of_ne (hn 0 (by omega)),
    Function.update_of_ne (hn 1 (by omega)),Function.update_of_ne (hn 2 (by omega))]

lemma adjacencyMetadataWords_nonnegative (I : ℤ → ℤ) (width vertex : ℕ) (degree base z : ℤ) (hz : 0 ≤ z) :
    adjacencyMetadataWords I width vertex degree base z=I z := by
  have hn (i : ℕ) : z ≠ vertexRecordAddress width vertex i := by
    have h := vertexRecordAddress_negative width vertex i
    omega
  simp [adjacencyMetadataWords,Function.update_of_ne (hn 0),Function.update_of_ne (hn 1),Function.update_of_ne (hn 2)]

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

-- Proof module: Solutions.GraphCacheRead

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexFieldReadCode_wellFormed (field destination : ℕ) : (vertexFieldReadCode field destination).wellFormed := by
  simp [vertexFieldReadCode,vertexIntegerLoadCode,MachineCode.wellFormed,vertexAddressCode_wellFormed,
    coreCode,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma cacheReadCode_wellFormed : cacheReadCode.wellFormed :=
  ⟨vertexFieldReadCode_wellFormed 0 60,vertexFieldReadCode_wellFormed 1 61⟩

set_option maxHeartbeats 1000000 in
lemma cache_read_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) :
    ∃ out, MachineEval m g ω cacheReadCode st (8*width+18) out ∧
      out.scalar.core.ptrs 60=st.scalar.integerMemory (vertexRecordAddress width vertex 0) ∧
      out.scalar.core.ptrs 61=st.scalar.integerMemory (vertexRecordAddress width vertex 1) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(8*width+18 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨mid,ea,hm60,hmI,hmR,hmQ,hmW,hmO,hmH⟩ := vertex_field_read_exec m g ω st hh width vertex 0 60 hz hv hw
  have hm0 := (ea.pointer_frame 0 (by decide)).trans hz
  have hm40 := (ea.pointer_frame 40 (by decide)).trans hv
  have hm41 := (ea.pointer_frame 41 (by decide)).trans hw
  obtain ⟨out,eb,ho61,hoI,hoR,hoQ,hoW,hoO,hoH⟩ := vertex_field_read_exec m g ω mid hmH width vertex 1 61 hm0 hm40 hm41
  have e : MachineEval m g ω cacheReadCode st (8*width+18) out := by
    have ee := MachineEval.seq ea eb
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,e,(eb.pointer_frame 60 (by decide)).trans hm60,?_,hoI.trans hmI,hoR.trans hmR,
    hoQ.trans hmQ,?_,hoO.trans hmO,hoH⟩
  · rw [ho61,hmI]
  · rw [hoW,hmW]
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

-- Proof module: Solutions.LevelHeaderTo

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderRealToCode_wellFormed (slot target : ℕ) : (levelHeaderRealToCode slot target).wellFormed := by
  refine ⟨levelHeaderRealLoadCode_wellFormed slot,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.GraphCacheInsert

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma arrayCells_lower_bound (base : ℤ) (length : ℕ) (z : ℤ) (hz : z ∈ arrayCells base length) : base ≤ z := by
  obtain ⟨i,hi,rfl⟩ := (mem_arrayCells _ _ _).mp hz
  omega

set_option maxHeartbeats 1800000 in
lemma GraphCache.insert_stored {n : ℕ} (g : InputGraph n) (I J : ℤ → ℤ) (width : ℕ)
    (stored : Finset (Fin n)) (free : ℤ) (v : Fin n)
    (h : GraphCache g I width stored free)
    (hnew : AdjacencyStored J free (g.neighbors v) (g.neighbors v).length)
    (hframe : ∀ z, z ∉ arrayCells free (g.neighbors v).length → J z=I z) :
    GraphCache g (adjacencyMetadataWords J width v.val ((g.neighbors v).length : ℤ) free)
      width (insert v stored) (free+((g.neighbors v).length : ℤ)) := by
  have hwidth := h.widthBound
  have self := adjacencyMetadataWords_self J width v.val ((g.neighbors v).length : ℤ) free
  have negFrame (z : ℤ) (hz : z<0) : J z=I z := by
    apply hframe
    intro hm
    have hb := arrayCells_lower_bound free (g.neighbors v).length z hm
    have hf := h.freeBound
    omega
  have otherFrame (u : Fin n) (hu : u ≠ v) (field : ℕ) (hfield : field < 3) :
      adjacencyMetadataWords J width v.val ((g.neighbors v).length : ℤ) free (vertexRecordAddress width u.val field)=I (vertexRecordAddress width u.val field) := by
    rw [adjacencyMetadataWords_other J width v.val u.val field h.widthBound (by omega)
      (by intro he; exact hu (Fin.ext he))]
    exact negFrame _ (vertexRecordAddress_negative _ _ _)
  have oldArrayFrame (u : Fin n) (hu : u ∈ stored) (i : ℕ) (hi : i < (g.neighbors u).length) :
      adjacencyMetadataWords J width v.val ((g.neighbors v).length : ℤ) free (I (vertexRecordAddress width u.val 1)+(i : ℤ))=
        I (I (vertexRecordAddress width u.val 1)+(i : ℤ)) := by
    have hbase := h.basePositive u hu
    rw [adjacencyMetadataWords_nonnegative J width v.val ((g.neighbors v).length : ℤ) free _ (by omega)]
    apply hframe
    intro hm
    have hlo := arrayCells_lower_bound free (g.neighbors v).length _ hm
    have hhi := h.belowFree u hu i hi
    omega
  refine ⟨h.widthBound,by have hb := h.freeBound; omega,?_,?_,?_,?_,?_⟩
  · intro u
    by_cases hu : u=v
    · subst u
      rw [self.2.2]
      simp
    · rw [otherFrame u hu 2 (by omega),h.flag u]
      simp [hu]
  · intro u hu
    rcases Finset.mem_insert.mp hu with he|hu
    · subst u
      exact self.1
    · by_cases he : u=v
      · subst u; exact self.1
      · rw [otherFrame u he 0 (by omega)]
        exact h.degree u hu
  · intro u hu
    by_cases he : u=v
    · subst u; rw [self.2.1]; exact h.freeBound
    · rw [otherFrame u he 1 (by omega)]
      exact h.basePositive u (Finset.mem_of_mem_insert_of_ne hu he)
  · intro u hu
    by_cases he : u=v
    · subst u
      rw [self.2.1]
      intro i hi hi'
      rw [adjacencyMetadataWords_nonnegative J width v.val ((g.neighbors v).length : ℤ) free _ (by have hb := h.freeBound; omega)]
      exact hnew i hi hi'
    · have hu' := Finset.mem_of_mem_insert_of_ne hu he
      rw [otherFrame u he 1 (by omega)]
      intro i hi hi'
      rw [oldArrayFrame u hu' i hi']
      exact h.adjacency u hu' i hi hi'
  · intro u hu i hi
    by_cases he : u=v
    · subst u
      rw [self.2.1]
      omega
    · rw [otherFrame u he 1 (by omega)]
      have hb := h.belowFree u (Finset.mem_of_mem_insert_of_ne hu he) i hi
      omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.GraphCacheFresh

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma cacheFreshCode_wellFormed : cacheFreshCode.wellFormed :=
  ⟨adjacencyStorageCode_wellFormed,adjacencyMetadataCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.GraphCacheCheck

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma cacheCheckCode_wellFormed : cacheCheckCode.wellFormed := by
  simp [cacheCheckCode,cacheCheckPrepRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    vertexIntegerLoadCode,MachineCode.wellFormed,vertexAddressCode_wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

lemma cacheCheckCode_queryReadOnly : cacheCheckCode.allAtoms queryReadOnly := by
  simp [cacheCheckCode,cacheCheckPrepRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    vertexIntegerLoadCode,MachineCode.allAtoms,queryReadOnly,vertexAddressCode_queryReadOnly]

set_option maxHeartbeats 1000000 in
lemma cache_check_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 50=(width : ℤ)) :
    ∃ out, MachineEval m g ω cacheCheckCode st (4*width+9) out ∧
      out.scalar.core.ptrs 51=st.scalar.integerMemory (vertexRecordAddress width vertex 2) ∧
      out.scalar.core.ptrs 41=(width : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*width+9 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,ep,hp,hI,hR,hW,hO,hH⟩ := cacheCheckPrepRoutine.execute m g ω st hh
  have ep2 : MachineEval m g ω cacheCheckPrepRoutine.code st 2 pre := ep
  have h0 := (ep.pointer_frame 0 (by decide)).trans hz
  have h40 := (ep.pointer_frame 40 (by decide)).trans hv
  have h41 : pre.scalar.core.ptrs 41=(width : ℤ) := by
    rw [hp]; simp [cacheCheckPrepRoutine,PointerRoutine.sequence,PointerRoutine.run,
      PointerOp.update,PointerOp.destination,PointerOp.result,hw]
  have h44 : pre.scalar.core.ptrs 44=2 := by
    rw [hp]; simp [cacheCheckPrepRoutine,PointerRoutine.sequence,PointerRoutine.run,
      PointerOp.update,PointerOp.destination,PointerOp.result]
  obtain ⟨out,el,ho51,hoI,hoR,hoW,hoO,hoH⟩ := vertex_integer_load_exec m g ω pre hH width vertex 2 h0 h40 h41 h44
  have e : MachineEval m g ω cacheCheckCode st (4*width+9) out := by
    have ee := MachineEval.seq ep2 el
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,e,?_,(el.pointer_frame 41 (by decide)).trans h41,hoI.trans hI,hoR.trans hR,
    e.query_frame cacheCheckCode_queryReadOnly,?_,hoO.trans hO,hoH⟩
  · rw [ho51,hI]
  · rw [hoW,hW]
    change st.work+(2 : ℕ)+(4*width+7 : ℕ)= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.GraphCacheExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma cacheRowCode_wellFormed : cacheRowCode.wellFormed :=
  ⟨cacheCheckCode_wellFormed,cacheFreshCode_wellFormed,cacheReadCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AdjacencyStorageOwned

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 1500000 in
lemma adjacency_storage_owned_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (v : Fin n) (free : ℤ)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) (hf : st.scalar.core.ptrs 20=free)
    :
    ∃ out, MachineEval m g ω adjacencyStorageCode st (6*(g.neighbors v).length+5) out ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧ out.scalar.core.ptrs 61=free ∧
      out.scalar.core.ptrs 60=((g.neighbors v).length : ℤ) ∧
      out.scalar.core.ptrs 20=free+((g.neighbors v).length : ℤ) ∧
      AdjacencyStored out.scalar.integerMemory free (g.neighbors v) (g.neighbors v).length ∧
      (∀ z, z ∉ arrayCells free (g.neighbors v).length → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries+(g.neighbors v).length+1 ∧
      out.work=st.work+(6*(g.neighbors v).length+5 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨deg,ed,hd60,hdI,hdR,hdQueries,hdW,hdO,hdH⟩ := degree_query_exec m g ω st hh 60 40
  rw [hv,degree_answer_vertex] at hd60
  have hd40 : deg.scalar.core.ptrs 40=(v.val : ℤ) := (ed.pointer_frame 40 (by decide)).trans hv
  have hd20 : deg.scalar.core.ptrs 20=free := (ed.pointer_frame 20 (by decide)).trans hf
  obtain ⟨pre,ep,hp,hpI,hpR,hpW,hpO,hpH⟩ := adjacencyReserveRoutine.execute m g ω deg hdH
  have ep3 : MachineEval m g ω adjacencyReserveRoutine.code deg 3 pre := ep
  have pre40 : pre.scalar.core.ptrs 40=(v.val : ℤ) := (ep.pointer_frame 40 (by decide)).trans hd40
  have pre60 : pre.scalar.core.ptrs 60=((g.neighbors v).length : ℤ) := (ep.pointer_frame 60 (by decide)).trans hd60
  have pre61 : pre.scalar.core.ptrs 61=free := by
    rw [hp]; simp [adjacencyReserveRoutine,PointerRoutine.sequence,PointerRoutine.run,
      PointerOp.update,PointerOp.destination,PointerOp.result,hd20]
  have pre20 : pre.scalar.core.ptrs 20=free+((g.neighbors v).length : ℤ) := by
    rw [hp]; simp [adjacencyReserveRoutine,PointerRoutine.sequence,PointerRoutine.run,
      PointerOp.update,PointerOp.destination,PointerOp.result,hd20,hd60]
  have pre62 : pre.scalar.core.ptrs 62=0 := by
    rw [hp]; simp [adjacencyReserveRoutine,PointerRoutine.sequence,PointerRoutine.run,
      PointerOp.update,PointerOp.destination,PointerOp.result]
  obtain ⟨out,el,ho40,ho61,ho60,ho62,hoStored,hoFrame,hoR,hoQ,hoW,hoO,hoH⟩ :=
    adjacency_fetch_loop_exec m g ω v free (g.neighbors v).length 0 pre hpH pre40 pre61 pre60 pre62
      (by omega) (by intro i hi; omega)
  have hFrame : ∀ z, z ∉ arrayCells free (g.neighbors v).length → out.scalar.integerMemory z=st.scalar.integerMemory z := by
    intro z hz
    exact (hoFrame z hz).trans (congrFun (hpI.trans hdI) z)
  refine ⟨out,?_,ho40,ho61,ho60,(el.pointer_frame 20 (by decide)).trans pre20,
    hoStored,hFrame,hoR.trans (hpR.trans hdR),?_,?_,hoO.trans (hpO.trans hdO),hoH⟩
  · have e := MachineEval.seq ed (MachineEval.seq ep3 el)
    convert e using 1 <;> (first | rfl | omega)
  · rw [hoQ]
    have hpQueries : pre.scalar.queries=deg.scalar.queries := by
      apply ep.frame (fun z => z.scalar.queries) (by intros; rfl) (by intro; rfl)
      simp [adjacencyReserveRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
        MachineCode.allAtoms,atomState,machineStep,pcSet,LocalPush.step,scalarProgram,
        LocalPush.coreProgram,SmaleNinth.RAMStep]
      refine ⟨?_,?_,?_⟩
      all_goals intro z; split_ifs <;> rfl
    rw [hpQueries,hdQueries]
    omega
  · rw [hoW,hpW,hdW]
    change st.work+1+(3 : ℕ)+(6*(g.neighbors v).length+1 : ℕ)= _
    push_cast
    ring


end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.GraphCacheFreshOwned

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 1500000 in
lemma cache_fresh_owned_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width : ℕ) (v : Fin n)
    (stored : Finset (Fin n)) (free : ℤ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hf : st.scalar.core.ptrs 20=free)
    (hcache : GraphCache g st.scalar.integerMemory width stored free)
    :
    ∃ out, MachineEval m g ω cacheFreshCode st (6*(g.neighbors v).length+12*width+33) out ∧
      out.scalar.core.ptrs 60=((g.neighbors v).length : ℤ) ∧ out.scalar.core.ptrs 61=free ∧
      out.scalar.core.ptrs 20=free+((g.neighbors v).length : ℤ) ∧
      GraphCache g out.scalar.integerMemory width (insert v stored) (free+((g.neighbors v).length : ℤ)) ∧
      out.scalar.integerMemory (vertexRecordAddress width v.val 1)=free ∧
      (∀ z, z ∉ cacheWriteCells width v.val free (g.neighbors v).length → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries+(g.neighbors v).length+1 ∧
      out.work=st.work+(6*(g.neighbors v).length+12*width+33 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨mid,ea,hm40,hm61,hm60,hm20,hmStored,hmFrame,hmR,hmQ,hmW,hmO,hmH⟩ :=
    adjacency_storage_owned_exec m g ω st hh v free hv hf
  have hm0 := (ea.pointer_frame 0 (by decide)).trans hz
  have hm41 := (ea.pointer_frame 41 (by decide)).trans hw
  obtain ⟨out,eb,hoI,ho60,ho61,hoR,hoQ,hoW,hoO,hoH⟩ := adjacency_metadata_exec m g ω mid hmH width v.val hm0 hm40 hm41
  rw [hm60,hm61] at hoI
  have hoCache : GraphCache g out.scalar.integerMemory width (insert v stored) (free+((g.neighbors v).length : ℤ)) := by
    rw [hoI]
    exact GraphCache.insert_stored g st.scalar.integerMemory mid.scalar.integerMemory width stored free v hcache hmStored hmFrame
  refine ⟨out,?_,ho60.trans hm60,ho61.trans hm61,(eb.pointer_frame 20 (by decide)).trans hm20,
    hoCache,?_,?_,hoR.trans hmR,hoQ.trans hmQ,?_,hoO.trans hmO,hoH⟩
  · have e := MachineEval.seq ea eb
    convert e using 1 <;> (first | rfl | omega)
  · rw [hoI]
    exact (adjacencyMetadataWords_self _ _ _ _ _).2.1
  · intro z hz'
    have hs : z ∉ arrayCells free (g.neighbors v).length := by
      intro he; exact hz' (Finset.mem_union_left _ he)
    have hn0 : z ≠ vertexRecordAddress width v.val 0 := by intro he; subst z; exact hz' (by simp [cacheWriteCells])
    have hn1 : z ≠ vertexRecordAddress width v.val 1 := by intro he; subst z; exact hz' (by simp [cacheWriteCells])
    have hn2 : z ≠ vertexRecordAddress width v.val 2 := by intro he; subst z; exact hz' (by simp [cacheWriteCells])
    rw [hoI]
    simp only [adjacencyMetadataWords,Function.update_of_ne hn0,Function.update_of_ne hn1,Function.update_of_ne hn2]
    exact hmFrame z hs
  · rw [hoW,hmW]
    push_cast
    ring


end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheWriteFrames

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma cache_write_cells_negative_field (width vertex other field : ℕ) (free : ℤ) (degree : ℕ)
    (hFree : 0 ≤ free) (hWidth : 3 ≤ width) (hf : field < width) (hField : 3 ≤ field) :
    vertexRecordAddress width other field ∉ cacheWriteCells width vertex free degree := by
  intro h
  rcases Finset.mem_union.mp h with hArray|hMeta
  · obtain ⟨i,hi,he⟩ := (mem_arrayCells free (vertexRecordAddress width other field) degree).mp hArray
    have hn := vertexRecordAddress_negative width other field
    have hi0 := Int.natCast_nonneg i
    omega
  · have hNe (k : ℕ) (hk : k < 3) : vertexRecordAddress width other field ≠ vertexRecordAddress width vertex k := by
      intro he
      have hEq := (vertexRecordAddress_injective width other vertex field k hf (by omega) he).2
      omega
    simpa only [Finset.mem_insert,Finset.mem_singleton,hNe 0 (by omega),hNe 1 (by omega),hNe 2 (by omega),or_self] using hMeta

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ScalarLevelLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 4500000 in
lemma scalar_level_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (body : MachineCode) (bound top : ℕ) (update : ℕ → (ℤ → ℝ) → (ℤ → ℝ))
    (Ctx : ℕ → MachineState → Prop) (hForm : body.wellFormed)
    (hUnit : body.allAtoms unitInstruction) (hQuery : body.allAtoms queryReadOnly)
    (hCtxUnit : ∀ i st, Ctx i st → Ctx i (payUnit st))
    (hBody : ∀ i ≤ top, ∀ (st : MachineState), st.scalar.halted=false → Ctx i st →
      st.scalar.core.ptrs 109=(i : ℤ) → st.scalar.core.ptrs 111=((top+1 : ℕ) : ℤ) →
      ∃ u out, MachineEval m g ω body st u out ∧ u ≤ bound ∧
        out.scalar.core.ptrs 109=((i+1 : ℕ) : ℤ) ∧ out.scalar.core.ptrs 111=((top+1 : ℕ) : ℤ) ∧
        out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=update i st.scalar.core.mem ∧
        Ctx (i+1) out ∧ out.output=st.output)
    (remaining : ℕ) :
    ∀ (i : ℕ) (st : MachineState), st.scalar.halted=false → Ctx i st →
      i+remaining=top+1 → st.scalar.core.ptrs 109=(i : ℤ) → st.scalar.core.ptrs 111=((top+1 : ℕ) : ℤ) →
      ∃ steps out, MachineEval m g ω (.whilePointer 111 109 body) st steps out ∧
        steps ≤ remaining*(bound+2)+1 ∧ out.scalar.core.ptrs 109=((top+1 : ℕ) : ℤ) ∧
        out.scalar.core.ptrs 111=((top+1 : ℕ) : ℤ) ∧ out.scalar.integerMemory=st.scalar.integerMemory ∧
        out.scalar.core.mem=levelRealMemoryFold update i remaining st.scalar.core.mem ∧ Ctx (top+1) out ∧
        out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction remaining with
  | zero =>
    intro i st hh hCtx hCount hIndex hStop
    have he : i=top+1 := by omega
    have ex : MachineEval m g ω (.whilePointer 111 109 body) st 1 (payUnit st) :=
      MachineEval.pointerDone hh (by rw [hStop,hIndex,he])
    refine ⟨1,payUnit st,ex,by omega,?_,hStop,rfl,rfl,?_,rfl,ex.unit_work hForm hUnit hh,rfl,hh⟩
    · change st.scalar.core.ptrs 109=((top+1 : ℕ) : ℤ)
      simpa only [he] using hIndex
    · simpa only [he] using hCtxUnit i st hCtx
  | succ remaining ih =>
    intro i st hh hCtx hCount hIndex hStop
    obtain ⟨u,b,eb,hu,bIndex,bStop,bI,bR,bCtx,bO⟩ := hBody i (by omega) (payUnit st) hh
      (hCtxUnit i st hCtx) hIndex hStop
    have bH : b.scalar.halted=false := (eb.halted hForm).trans hh
    obtain ⟨w,out,er,hw,cIndex,cStop,cI,cR,cCtx,cQ,cW,cO,cH⟩ := ih (i+1) (payUnit b) bH
      (hCtxUnit (i+1) b bCtx) (by omega) bIndex bStop
    have ex : MachineEval m g ω (.whilePointer 111 109 body) st (1+u+1+w) out :=
      MachineEval.pointerNext hh (by rw [hStop,hIndex]; omega) eb er
    refine ⟨1+u+1+w,out,ex,?_,cIndex,cStop,cI.trans bI,?_,cCtx,ex.query_frame hQuery,
      ex.unit_work hForm hUnit hh,cO.trans bO,cH⟩
    · have hProduct : (remaining+1)*(bound+2)=remaining*(bound+2)+(bound+2) := by ring
      rw [hProduct]
      omega
    · change out.scalar.core.mem=levelRealMemoryFold update (i+1) remaining (update i st.scalar.core.mem)
      change out.scalar.core.mem=levelRealMemoryFold update (i+1) remaining b.scalar.core.mem at cR
      rw [cR,bR]
      rfl

end
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

lemma level_payload_invariant {Payload : Type} (update : ℕ → Payload → Payload) (limit : ℕ)
    (P : Payload → Prop) (hStep : ∀ i < limit, ∀ payload, P payload → P (update i payload)) (count : ℕ) :
    ∀ (start : ℕ) (payload : Payload), start+count ≤ limit → P payload →
      P (levelPayloadFold update start count payload) := by
  induction count with
  | zero => intros; assumption
  | succ count ih =>
    intro start payload hRange hp
    exact ih (start+1) (update start payload) (by omega) (hStep start (by omega) payload hp)

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

-- Proof module: Solutions.VertexRealReadTo

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexRealReadToCode_wellFormed (target : ℕ) : (vertexRealReadToCode target).wellFormed := by
  simp [vertexRealReadToCode,vertexRealLoadCode,vertexAddressCode_wellFormed,coreCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 1500000 in
lemma vertex_real_read_to_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex offset target : ℕ)
    (h0 : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hOffset : st.scalar.core.ptrs 44=(offset : ℤ))
    (hOne : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω (vertexRealReadToCode target) st (4*width+8) out ∧
      out.scalar.core.regs target=st.scalar.core.mem (vertexRecordAddress width vertex offset) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*width+8 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a10,aI,aR,aW,aO,aH⟩ := vertex_real_load_exec m g ω st hh width vertex offset h0 hv hw hOffset
  have a31 := (ea.real_register_frame 31 (by decide)).trans hOne
  let out := payUnit (realWrite a target (st.scalar.core.mem (vertexRecordAddress width vertex offset)))
  have eb : MachineEval m g ω (coreCode (.mul target 10 31)) a 1 out := by
    simpa only [out,coreCode,RealOperation.instruction,RealOperation.value,a10,a31,mul_one] using
      binary_eval m g ω a .mul target 10 31 aH
  have ex : MachineEval m g ω (vertexRealReadToCode target) st (4*width+8) out := by
    convert MachineEval.seq ea eb using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,by simp [out,payUnit,pcSet,realWrite],aI,aR,ex.query_frame (by
    simp [vertexRealReadToCode,vertexRealLoadCode,vertexAddressCode_queryReadOnly,coreCode,MachineCode.allAtoms,queryReadOnly]),?_,aO,aH⟩
  change a.work+1= _
  rw [aW]
  push_cast
  ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorScalarPrefix

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma exteriorScalarPrefixCode_wellFormed : exteriorScalarPrefixCode.wellFormed := by
  refine ⟨?_,levelContextCode_wellFormed,levelHeaderRealToCode_wellFormed 1 20⟩
  simp [exteriorScalarPrefixInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 3000000 in
lemma exterior_scalar_prefix_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width t : ℕ)
    (ht : st.scalar.core.ptrs 112=(t : ℤ)) (hw : st.scalar.core.ptrs 50=(width : ℤ))
    (hOne : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω exteriorScalarPrefixCode st 21 out ∧
      out.scalar.core.ptrs 100=(t : ℤ) ∧ out.scalar.core.ptrs 108=st.scalar.core.ptrs 100 ∧
      out.scalar.core.ptrs 116=st.scalar.core.ptrs 40 ∧ out.scalar.core.ptrs 41=(width : ℤ) ∧
      out.scalar.core.ptrs 87=((16*(t+1) : ℕ) : ℤ) ∧ out.scalar.core.regs 20=st.scalar.core.mem (levelHeaderAddress t 1) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+21 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := linearRun m g ω exteriorScalarPrefixInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω exteriorScalarPrefixInstructions
    (by simp [exteriorScalarPrefixInstructions,unitInstruction,straightInstruction]) st hh
  have a100 : a.scalar.core.ptrs 100=(t : ℤ) := by
    simp [a,linearRun,exteriorScalarPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh,ht]
  have a108 : a.scalar.core.ptrs 108=st.scalar.core.ptrs 100 := by
    simp [a,linearRun,exteriorScalarPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have a116 : a.scalar.core.ptrs 116=st.scalar.core.ptrs 40 := by
    simp [a,linearRun,exteriorScalarPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,exteriorScalarPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have aR : a.scalar.core.mem=st.scalar.core.mem := by
    simp [a,linearRun,exteriorScalarPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,exteriorScalarPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  obtain ⟨b,eb,b87,b89,b41,bI,bR,bQ,bW,bO,bH⟩ := level_context_exec m g ω a aH t width a100
    ((ea.pointer_frame 50 (by decide)).trans hw)
  have b100 := (eb.pointer_frame 100 (by decide)).trans a100
  have b31 := ((MachineEval.seq ea eb).real_register_frame 31 (by decide)).trans hOne
  obtain ⟨out,ec,c20,cI,cR,cW,cO,cH⟩ := level_header_real_to_exec m g ω b bH t 1 20 b100 b31
  have ex : MachineEval m g ω exteriorScalarPrefixCode st 21 out := MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨out,ex,(ec.pointer_frame 100 (by decide)).trans b100,
    ((MachineEval.seq eb ec).pointer_frame 108 (by decide)).trans a108,
    ((MachineEval.seq eb ec).pointer_frame 116 (by decide)).trans a116,
    (ec.pointer_frame 41 (by decide)).trans b41,(ec.pointer_frame 87 (by decide)).trans b87,?_,
    cI.trans (bI.trans aI),cR.trans (bR.trans aR),ex.query_frame (by decide),
    ex.unit_work exteriorScalarPrefixCode_wellFormed (by decide) hh,cO.trans (bO.trans aO),cH⟩
  rw [c20,bR,aR]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorInputsCode

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma exteriorRootReferenceCode_wellFormed : exteriorRootReferenceCode.wellFormed := by
  simp [exteriorRootReferenceCode,coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨0,by norm_num⟩
lemma exteriorResidualOffsetCode_wellFormed : exteriorResidualOffsetCode.wellFormed := by
  simp [exteriorResidualOffsetCode,exteriorResidualOffsetInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma exteriorInputsTailCode_wellFormed : exteriorInputsTailCode.wellFormed := by
  simp [exteriorInputsTailCode,coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma exteriorInputsCode_wellFormed : exteriorInputsCode.wellFormed := by
  refine ⟨?_,vertexRealReadToCode_wellFormed 4,?_,vertexRealReadToCode_wellFormed 5,
    exteriorRootReferenceCode_wellFormed,exteriorResidualOffsetCode_wellFormed,?_,exteriorInputsTailCode_wellFormed⟩
  all_goals simp [vertexRealLoadCode,vertexAddressCode_wellFormed,coreCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 1600000 in
lemma exterior_root_reference_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (t : ℕ) (h0 : st.scalar.core.ptrs 0=0)
    (ht : st.scalar.core.ptrs 112=(t : ℤ)) :
    ∃ out, MachineEval m g ω exteriorRootReferenceCode st 2 out ∧
      out.scalar.core.regs 5=(if t=0 then 0 else st.scalar.core.regs 5) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+2 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  by_cases he : t=0
  · let out := payUnit (realWrite (payUnit st) 5 0)
    have el : MachineEval m g ω (coreCode (.const 5 0)) (payUnit st) 1 out := const_eval m g ω (payUnit st) 5 0 hh
    have ex : MachineEval m g ω exteriorRootReferenceCode st 2 out :=
      MachineEval.pointerLe hh (by rw [ht,h0,he]; norm_num) el
    refine ⟨out,ex,by simp [out,payUnit,pcSet,realWrite,he],rfl,rfl,rfl,?_,rfl,hh⟩
    change st.work+1+1= _
    norm_num
    ring
  · have ex : MachineEval m g ω exteriorRootReferenceCode st 2 (payUnit (payUnit st)) :=
      MachineEval.pointerGt hh (by rw [ht,h0]; omega) (MachineEval.skip (payUnit st))
    refine ⟨payUnit (payUnit st),ex,by simp only [if_neg he]; rfl,rfl,rfl,rfl,?_,rfl,hh⟩
    change st.work+1+1= _
    norm_num
    ring

set_option maxHeartbeats 1400000 in
lemma exterior_residual_offset_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base : ℕ) (hb : st.scalar.core.ptrs 87=(base : ℤ)) :
    ∃ out, MachineEval m g ω exteriorResidualOffsetCode st 2 out ∧
      out.scalar.core.ptrs 44=((base+1 : ℕ) : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+2 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω exteriorResidualOffsetInstructions
    (by simp [exteriorResidualOffsetInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,ex.query_frame (by decide),hW,?_,hH⟩
  all_goals simp [linearRun,exteriorResidualOffsetInstructions,atomState,machineStep,pcSet,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hb]

set_option maxHeartbeats 1800000 in
lemma exterior_inputs_tail_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (v : Fin n) (x reference : ℝ)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) (hx : st.scalar.core.regs 4=x) (hr : st.scalar.core.regs 5=reference) :
    ∃ out, MachineEval m g ω exteriorInputsTailCode st 3 out ∧
      out.scalar.core.regs 11=((g.neighbors v).length : ℝ) ∧ out.scalar.core.regs 12=x-reference ∧
      out.scalar.core.ptrs 60=((g.neighbors v).length : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries+1 ∧ out.work=st.work+3 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a60,aI,aR,aQ,aW,aO,aH⟩ := degree_query_exec m g ω st hh 60 40
  rw [hv,degree_answer_vertex] at a60
  let b := payUnit (realWrite a 11 ((g.neighbors v).length : ℝ))
  have eb : MachineEval m g ω (.atom (.scalar (.pointerReal 11 60))) a 1 b := by
    simpa only [b,a60,Int.cast_natCast] using pointerReal_eval m g ω a 11 60 aH
  have b4 := ((MachineEval.seq ea eb).real_register_frame 4 (by decide)).trans hx
  have b5 := ((MachineEval.seq ea eb).real_register_frame 5 (by decide)).trans hr
  let out := payUnit (realWrite b 12 (x-reference))
  have ec : MachineEval m g ω (coreCode (.sub 12 4 5)) b 1 out := by
    simpa only [out,coreCode,RealOperation.instruction,RealOperation.value,b4,b5] using binary_eval m g ω b .sub 12 4 5 aH
  refine ⟨out,MachineEval.seq ea (MachineEval.seq eb ec),?_,by simp [out,payUnit,pcSet,realWrite],?_,aI,aR,aQ,?_,aO,aH⟩
  · simp [out,b,payUnit,pcSet,realWrite]
  · exact ((MachineEval.seq eb ec).pointer_frame 60 (by decide)).trans a60
  · change a.work+1+1= _
    rw [aW]
    norm_num
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorInputsExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 5500000 in
lemma exterior_inputs_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width t : ℕ) (v : Fin n)
    (h0 : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hb : st.scalar.core.ptrs 87=((16*(t+1) : ℕ) : ℤ))
    (ht : st.scalar.core.ptrs 112=(t : ℤ)) (hOne : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω exteriorInputsCode st (12*width+32) out ∧
      out.scalar.core.regs 10=st.scalar.core.mem (vertexRecordAddress width v.val (16*(t+1)+1)) ∧
      out.scalar.core.regs 11=((g.neighbors v).length : ℝ) ∧
      out.scalar.core.regs 12=(if t=0 then st.scalar.core.mem (vertexRecordAddress width v.val 0) else
        st.scalar.core.mem (vertexRecordAddress width v.val 0)-st.scalar.core.mem (vertexRecordAddress width v.val (16*(t+1)))) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries+1 ∧ out.work=st.work+(12*width+32 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  let base := 16*(t+1)
  let a := payUnit (pointerWrite st 44 0)
  have ea : MachineEval m g ω (coreCode (.pset 44 0)) st 1 a := pset_eval m g ω st 44 0 hh
  have a44 : a.scalar.core.ptrs 44=0 := by simp [a,payUnit,pcSet,pointerWrite]
  obtain ⟨b,eb,b4,bI,bR,bQ,bW,bO,bH⟩ := vertex_real_read_to_exec m g ω a hh width v.val 0 4
    ((ea.pointer_frame 0 (by decide)).trans h0) ((ea.pointer_frame 40 (by decide)).trans hv)
    ((ea.pointer_frame 41 (by decide)).trans hw) a44 ((ea.real_register_frame 31 (by decide)).trans hOne)
  have b87 := ((MachineEval.seq ea eb).pointer_frame 87 (by decide)).trans hb
  let c := payUnit (pointerWrite b 44 (base : ℤ))
  have ec : MachineEval m g ω (coreCode (.pcopy 44 87)) b 1 c := by
    simpa only [c,coreCode,b87] using pcopy_eval m g ω b 44 87 bH
  have c44 : c.scalar.core.ptrs 44=(base : ℤ) := by simp [c,payUnit,pcSet,pointerWrite]
  have eBefore := MachineEval.seq ea (MachineEval.seq eb ec)
  obtain ⟨d,ed,d5,dI,dR,dQ,dW,dO,dH⟩ := vertex_real_read_to_exec m g ω c bH width v.val base 5
    ((eBefore.pointer_frame 0 (by decide)).trans h0) ((eBefore.pointer_frame 40 (by decide)).trans hv)
    ((eBefore.pointer_frame 41 (by decide)).trans hw) c44 ((eBefore.real_register_frame 31 (by decide)).trans hOne)
  have eBeforeRoot := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  obtain ⟨e,ee,e5,eI,eR,eQ,eW,eO,eH⟩ := exterior_root_reference_exec m g ω d dH t
    ((eBeforeRoot.pointer_frame 0 (by decide)).trans h0) ((eBeforeRoot.pointer_frame 112 (by decide)).trans ht)
  have eBeforeOffset := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed ee)))
  obtain ⟨f,ef,f44,fI,fR,fQ,fW,fO,fH⟩ := exterior_residual_offset_exec m g ω e eH base
    ((eBeforeOffset.pointer_frame 87 (by decide)).trans hb)
  have eBeforeResidual := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee ef))))
  obtain ⟨r,er,r10,rI,rR,rW,rO,rH⟩ := vertex_real_load_exec m g ω f fH width v.val (base+1)
    ((eBeforeResidual.pointer_frame 0 (by decide)).trans h0) ((eBeforeResidual.pointer_frame 40 (by decide)).trans hv)
    ((eBeforeResidual.pointer_frame 41 (by decide)).trans hw) f44
  have eBeforeTail := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee (MachineEval.seq ef er)))))
  have r4 : r.scalar.core.regs 4=st.scalar.core.mem (vertexRecordAddress width v.val 0) := by
    exact ((MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee (MachineEval.seq ef er)))).real_register_frame 4 (by decide)).trans b4
  have r5 : r.scalar.core.regs 5=(if t=0 then 0 else st.scalar.core.mem (vertexRecordAddress width v.val base)) := by
    rw [(MachineEval.seq ef er).real_register_frame 5 (by decide),e5,d5]
    change (if t=0 then 0 else b.scalar.core.mem _)= _
    rw [bR]
    rfl
  obtain ⟨out,es,s11,s12,s60,sI,sR,sQ,sW,sO,sH⟩ := exterior_inputs_tail_exec m g ω r rH v
    (st.scalar.core.mem (vertexRecordAddress width v.val 0))
    (if t=0 then 0 else st.scalar.core.mem (vertexRecordAddress width v.val base))
    ((eBeforeTail.pointer_frame 40 (by decide)).trans hv) r4 r5
  have ex : MachineEval m g ω exteriorInputsCode st (12*width+32) out := by
    have ee' := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed
      (MachineEval.seq ee (MachineEval.seq ef (MachineEval.seq er es))))))
    convert ee' using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,?_,s11,?_,sI.trans (rI.trans (fI.trans (eI.trans (dI.trans bI)))),
    sR.trans (rR.trans (fR.trans (eR.trans (dR.trans bR)))),?_,ex.unit_work exteriorInputsCode_wellFormed (by decide) hh,
    sO.trans (rO.trans (fO.trans (eO.trans (dO.trans bO)))),sH⟩
  · rw [es.real_register_frame 10 (by decide),r10,fR,eR,dR]
    change b.scalar.core.mem _= _
    rw [bR]
    rfl
  · rw [s12]
    by_cases he : t=0 <;> simp [he,base]
  · rw [sQ,(er.query_frame (by decide)),fQ,eQ,dQ,(ec.query_frame (by decide)),bQ,(ea.query_frame (by decide))]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorAmountCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma exteriorAmountPrefixCode_wellFormed : exteriorAmountPrefixCode.wellFormed := by
  simp [exteriorAmountPrefixCode,exteriorAmountPrefixInstructions,linearCode,sequenceCode,RealOperation.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨⟨5,by norm_num⟩,⟨3/8,by norm_num⟩⟩
lemma exteriorAmountChoiceCode_wellFormed (sourceReg : ℕ) (activated : ℤ) : (exteriorAmountChoiceCode sourceReg activated).wellFormed := by
  simp [exteriorAmountChoiceCode,coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma exteriorAmountDecisionCode_wellFormed : exteriorAmountDecisionCode.wellFormed :=
  ⟨exteriorAmountChoiceCode_wellFormed 19 1,exteriorAmountChoiceCode_wellFormed 17 0⟩
lemma exteriorAmountTailCode_wellFormed : exteriorAmountTailCode.wellFormed := by
  simp [exteriorAmountTailCode,exteriorAmountTailInstructions,linearCode,sequenceCode,RealOperation.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨1/2,by norm_num⟩
lemma exteriorAmountCode_wellFormed : exteriorAmountCode.wellFormed :=
  ⟨exteriorAmountPrefixCode_wellFormed,exteriorAmountDecisionCode_wellFormed,exteriorAmountTailCode_wellFormed⟩

set_option maxHeartbeats 1800000 in
lemma exterior_amount_prefix_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (r d y q : ℝ)
    (hr : st.scalar.core.regs 10=r) (hd : st.scalar.core.regs 11=d)
    (hy : st.scalar.core.regs 12=y) (hq : st.scalar.core.regs 20=q) :
    ∃ out, MachineEval m g ω exteriorAmountPrefixCode st 7 out ∧
      out.scalar.core.regs 17=r/(5*d) ∧ out.scalar.core.regs 18=3*q/8 ∧
      out.scalar.core.regs 19=3*q/8-y ∧ out.scalar.core.regs 22=(3*q/8-y)-r/(5*d) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+7 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω exteriorAmountPrefixInstructions
    (by simp [exteriorAmountPrefixInstructions,RealOperation.instruction,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,?_,?_,ex.query_frame (by decide),hW,?_,hH⟩
  all_goals simp [linearRun,exteriorAmountPrefixInstructions,RealOperation.instruction,atomState,machineStep,pcSet,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hr,hd,hy,hq] <;> ring

set_option maxHeartbeats 1800000 in
lemma exterior_amount_tail_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (d h q α : ℝ)
    (hd : st.scalar.core.regs 11=d) (hhval : st.scalar.core.regs 40=h)
    (hq : st.scalar.core.regs 20=q) (ha : st.scalar.core.regs 30=α) (hOne : st.scalar.core.regs 31=1)
    (hCap : st.scalar.core.regs 18=3*q/8) :
    ∃ out, MachineEval m g ω exteriorAmountTailCode st 9 out ∧
      out.scalar.core.regs 40=h ∧ out.scalar.core.regs 41=(1-α)*h ∧ out.scalar.core.regs 42=d*h ∧
      out.scalar.core.regs 43=q*d/2 ∧ out.scalar.core.regs 44=3*q/8 ∧ out.scalar.core.regs 45=q ∧
      out.scalar.core.regs 46=(1-α)*d*h ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+9 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω exteriorAmountTailInstructions
    (by simp [exteriorAmountTailInstructions,RealOperation.instruction,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,?_,?_,?_,?_,?_,ex.query_frame (by decide),hW,?_,hH⟩
  all_goals simp [linearRun,exteriorAmountTailInstructions,RealOperation.instruction,atomState,machineStep,pcSet,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hd,hhval,hq,ha,hOne,hCap] <;> ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorAmountExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1800000 in
lemma exterior_amount_choice_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (sourceReg : ℕ) (activated : ℤ)
    (hOne : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω (exteriorAmountChoiceCode sourceReg activated) st 2 out ∧
      out.scalar.core.regs 40=st.scalar.core.regs sourceReg ∧ out.scalar.core.ptrs 114=activated ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+2 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := payUnit (realWrite st 40 (st.scalar.core.regs sourceReg))
  have ea : MachineEval m g ω (coreCode (.mul 40 sourceReg 31)) st 1 a := by
    simpa only [a,coreCode,RealOperation.instruction,RealOperation.value,hOne,mul_one] using binary_eval m g ω st .mul 40 sourceReg 31 hh
  let out := payUnit (pointerWrite a 114 activated)
  have eb : MachineEval m g ω (coreCode (.pset 114 activated)) a 1 out := pset_eval m g ω a 114 activated hh
  refine ⟨out,MachineEval.seq ea eb,?_,?_,rfl,rfl,rfl,?_,rfl,hh⟩
  · simp [out,a,payUnit,pcSet,pointerWrite,realWrite]
  · simp [out,payUnit,pcSet,pointerWrite]
  · change st.work+1+1= _
    norm_num
    ring

set_option maxHeartbeats 2500000 in
lemma exterior_amount_decision_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (a b cap y : ℝ) (hb : b=cap-y)
    (h17 : st.scalar.core.regs 17=a) (h19 : st.scalar.core.regs 19=b)
    (h22 : st.scalar.core.regs 22=b-a) (hOne : st.scalar.core.regs 31=1) :
    ∃ steps out, MachineEval m g ω exteriorAmountDecisionCode st steps out ∧ steps ≤ 4 ∧
      out.scalar.core.regs 40=min a b ∧ out.scalar.core.ptrs 114=(if y+min a b=cap then 1 else 0) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  by_cases hba : b ≤ a
  · obtain ⟨out,ex,h40,h114,hI,hR,hQ,hW,hO,hH⟩ := exterior_amount_choice_exec m g ω (payUnit st) hh 19 1 hOne
    have hMin : min a b=b := min_eq_right hba
    have hActive : y+min a b=cap := by rw [hMin,hb]; ring
    have eBranch : MachineEval m g ω exteriorAmountDecisionCode st 3 out :=
      MachineEval.realNonpos hh (by rw [h22]; linarith) ex
    refine ⟨3,out,eBranch,by omega,?_,?_,hI,hR,hQ,?_,hO,hH⟩
    · rw [hMin]; exact h40.trans h19
    · rw [if_pos hActive]; exact h114
    · rw [hW,payUnit_work]; norm_num; ring
  · obtain ⟨mid,ex,h40,h114,hI,hR,hQ,hW,hO,hH⟩ := exterior_amount_choice_exec m g ω (payUnit st) hh 17 0 hOne
    have hMin : min a b=a := min_eq_left (le_of_lt (lt_of_not_ge hba))
    have hActive : y+min a b ≠ cap := by rw [hMin]; linarith
    have eBranch : MachineEval m g ω exteriorAmountDecisionCode st 4 (payUnit mid) :=
      MachineEval.realPos hh (by rw [h22]; linarith) ex
    refine ⟨4,payUnit mid,eBranch,by omega,?_,?_,hI,hR,hQ,?_,hO,hH⟩
    · rw [hMin]; exact h40.trans h17
    · rw [if_neg hActive]; exact h114
    · change mid.work+1= _
      rw [hW,payUnit_work]; norm_num; ring

set_option maxHeartbeats 4000000 in
lemma exterior_amount_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (r d y q α : ℝ)
    (hr : st.scalar.core.regs 10=r) (hd : st.scalar.core.regs 11=d) (hy : st.scalar.core.regs 12=y)
    (hq : st.scalar.core.regs 20=q) (ha : st.scalar.core.regs 30=α) (hOne : st.scalar.core.regs 31=1) :
    let h := min (r/(5*d)) (3*q/8-y)
    ∃ steps out, MachineEval m g ω exteriorAmountCode st steps out ∧ steps ≤ 20 ∧
      out.scalar.core.regs 40=h ∧ out.scalar.core.regs 41=(1-α)*h ∧ out.scalar.core.regs 42=d*h ∧
      out.scalar.core.regs 43=q*d/2 ∧ out.scalar.core.regs 44=3*q/8 ∧ out.scalar.core.regs 45=q ∧
      out.scalar.core.regs 46=(1-α)*d*h ∧ out.scalar.core.ptrs 114=(if y+h=3*q/8 then 1 else 0) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  intro h
  obtain ⟨a,ea,a17,a18,a19,a22,aI,aR,aQ,aW,aO,aH⟩ := exterior_amount_prefix_exec m g ω st hh r d y q hr hd hy hq
  obtain ⟨u,b,eb,hu,b40,b114,bI,bR,bQ,bW,bO,bH⟩ := exterior_amount_decision_exec m g ω a aH
    (r/(5*d)) (3*q/8-y) (3*q/8) y rfl a17 a19 a22 ((ea.real_register_frame 31 (by decide)).trans hOne)
  have eBefore := MachineEval.seq ea eb
  have b11 := (eBefore.real_register_frame 11 (by decide)).trans hd
  have b20 := (eBefore.real_register_frame 20 (by decide)).trans hq
  have b30 := (eBefore.real_register_frame 30 (by decide)).trans ha
  have b31 := (eBefore.real_register_frame 31 (by decide)).trans hOne
  have b18 := (eb.real_register_frame 18 (by decide)).trans a18
  obtain ⟨out,ec,c40,c41,c42,c43,c44,c45,c46,cI,cR,cQ,cW,cO,cH⟩ :=
    exterior_amount_tail_exec m g ω b bH d h q α b11 b40 b20 b30 b31 b18
  refine ⟨7+(u+9),out,MachineEval.seq ea (MachineEval.seq eb ec),by omega,c40,c41,c42,c43,c44,c45,c46,?_,
    cI.trans (bI.trans aI),cR.trans (bR.trans aR),cQ.trans (bQ.trans aQ),?_,cO.trans (bO.trans aO),cH⟩
  · exact (ec.pointer_frame 114 (by decide)).trans b114
  · rw [cW,bW,aW]
    push_cast
    ring

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

-- Proof module: Solutions.ExteriorScalarExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma exteriorScalarCode_wellFormed : exteriorScalarCode.wellFormed :=
  ⟨exteriorScalarPrefixCode_wellFormed,exteriorInputsCode_wellFormed,exteriorAmountCode_wellFormed⟩

set_option maxHeartbeats 5500000 in
lemma exterior_scalar_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length t : ℕ) (v : Fin n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (ht : t ≤ logical.top)
    (hvDomain : v ∈ parentDomain logical t)
    (hSelected : st.scalar.core.ptrs 112=(t : ℤ)) (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) :
    let d := LocalPush.deg g.graph v
    let q := (logical.frames t).q
    let h := min ((logical.frames t).residual v/(5*d)) (3*q/8-relative logical t v)
    ∃ steps out, MachineEval m g ω exteriorScalarCode st steps out ∧ steps ≤ 12*(16*(ell+3))+73 ∧
      out.scalar.core.regs 40=h ∧ out.scalar.core.regs 41=(1-α)*h ∧ out.scalar.core.regs 42=d*h ∧
      out.scalar.core.regs 43=q*d/2 ∧ out.scalar.core.regs 44=3*q/8 ∧ out.scalar.core.regs 45=q ∧
      out.scalar.core.regs 46=(1-α)*d*h ∧ out.scalar.core.ptrs 114=(if relative logical t v+h=3*q/8 then 1 else 0) ∧
      out.scalar.core.ptrs 108=(logical.top : ℤ) ∧ out.scalar.core.ptrs 116=(v.val : ℤ) ∧
      out.scalar.core.ptrs 100=(t : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries+1 ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  intro d q h
  let width := 16*(ell+3)
  let f := pm.frames t ht
  obtain ⟨a,ea,a100,a108,a116,a41,a87,a20,aI,aR,aQ,aW,aO,aH⟩ :=
    exterior_scalar_prefix_exec m g ω st hh width t hSelected pm.width pm.one
  obtain ⟨b,eb,b10,b11,b12,bI,bR,bQ,bW,bO,bH⟩ := exterior_inputs_exec m g ω a aH width t v
    ((ea.pointer_frame 0 (by decide)).trans pm.zero) ((ea.pointer_frame 40 (by decide)).trans hv)
    a41 a87 ((ea.pointer_frame 112 (by decide)).trans hSelected) ((ea.real_register_frame 31 (by decide)).trans pm.one)
  have bResidual : b.scalar.core.regs 10=(logical.frames t).residual v := by
    rw [b10,aR]
    exact f.residual v hvDomain
  have bDegree : b.scalar.core.regs 11=d := by
    simpa only [d,LocalPush.deg,input_degree] using b11
  have bRelative : b.scalar.core.regs 12=relative logical t v := by
    rw [b12,aR]
    by_cases he : t=0
    · simp only [relative,if_pos he]
      exact pm.potential v
    · simp only [relative,if_neg he]
      rw [pm.potential v,f.reference v hvDomain]
  have bq : b.scalar.core.regs 20=q := ((eb.real_register_frame 20 (by decide)).trans a20).trans f.q
  have eBefore := MachineEval.seq ea eb
  obtain ⟨u,out,ec,hu,c40,c41,c42,c43,c44,c45,c46,c114,cI,cR,cQ,cW,cO,cH⟩ := exterior_amount_exec m g ω b bH
    ((logical.frames t).residual v) d (relative logical t v) q α bResidual bDegree bRelative bq
      ((eBefore.real_register_frame 30 (by decide)).trans pm.alphaRegister)
      ((eBefore.real_register_frame 31 (by decide)).trans pm.one)
  have ex : MachineEval m g ω exteriorScalarCode st (21+((12*width+32)+u)) out := MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨21+((12*width+32)+u),out,ex,?_,c40,c41,c42,c43,c44,c45,c46,c114,
    ((MachineEval.seq eb ec).pointer_frame 108 (by decide)).trans (a108.trans pm.top),
    ((MachineEval.seq eb ec).pointer_frame 116 (by decide)).trans (a116.trans hv),
    ((MachineEval.seq eb ec).pointer_frame 100 (by decide)).trans a100,
    cI.trans (bI.trans aI),cR.trans (bR.trans aR),?_,ex.unit_work exteriorScalarCode_wellFormed (by decide) hh,
    cO.trans (bO.trans aO),cH⟩
  · dsimp only [width]
    omega
  · rw [cQ,bQ,aQ]

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

-- Proof module: Solutions.ExteriorSelfUpdate

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma exteriorSelfCoefficientCode_wellFormed (coefficient : ℤ) : (exteriorSelfCoefficientCode coefficient).wellFormed := by
  simp [exteriorSelfCoefficientCode,exteriorSelfCoefficientInstructions,linearCode,sequenceCode,RealOperation.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨(coefficient : ℚ),by simp⟩
lemma exteriorSelfChoiceCode_wellFormed : exteriorSelfChoiceCode.wellFormed :=
  ⟨exteriorSelfCoefficientCode_wellFormed (-5),exteriorSelfCoefficientCode_wellFormed (-1)⟩
lemma exteriorSelfCode_wellFormed : exteriorSelfCode.wellFormed :=
  ⟨⟨exteriorSelfChoiceCode_wellFormed,exteriorResidualOffsetCode_wellFormed,vertexRealAddFromCode_wellFormed 48⟩,trivial⟩

set_option maxHeartbeats 1500000 in
lemma exterior_self_coefficient_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (coefficient : ℤ) (z : ℝ) (hz : st.scalar.core.regs 42=z) :
    ∃ out, MachineEval m g ω (exteriorSelfCoefficientCode coefficient) st 2 out ∧
      out.scalar.core.regs 48=(coefficient : ℝ)*z ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+2 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω (exteriorSelfCoefficientInstructions coefficient)
    (by simp [exteriorSelfCoefficientInstructions,RealOperation.instruction,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,ex.query_frame (by
    simp [exteriorSelfCoefficientCode,exteriorSelfCoefficientInstructions,linearCode,sequenceCode,RealOperation.instruction,MachineCode.allAtoms,queryReadOnly]),hW,?_,hH⟩
  all_goals simp [linearRun,exteriorSelfCoefficientInstructions,RealOperation.instruction,atomState,machineStep,pcSet,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hz]

set_option maxHeartbeats 2200000 in
lemma exterior_self_choice_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (i t : ℕ) (z : ℝ) (hi : i ≤ t)
    (h100 : st.scalar.core.ptrs 100=(i : ℤ)) (h112 : st.scalar.core.ptrs 112=(t : ℤ)) (hz : st.scalar.core.regs 42=z) :
    ∃ steps out, MachineEval m g ω exteriorSelfChoiceCode st steps out ∧ steps ≤ 4 ∧
      out.scalar.core.regs 48=(if i < t then -z else -5*z) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  by_cases he : i=t
  · obtain ⟨out,ex,h48,hI,hR,hQ,hW,hO,hH⟩ := exterior_self_coefficient_exec m g ω (payUnit st) hh (-5) z hz
    have eBranch : MachineEval m g ω exteriorSelfChoiceCode st 3 out :=
      MachineEval.pointerLe hh (by rw [h100,h112]; omega) ex
    refine ⟨3,out,eBranch,by omega,?_,hI,hR,hQ,eBranch.unit_work exteriorSelfChoiceCode_wellFormed (by decide) hh,hO,hH⟩
    simpa [he] using h48
  · obtain ⟨mid,ex,h48,hI,hR,hQ,hW,hO,hH⟩ := exterior_self_coefficient_exec m g ω (payUnit st) hh (-1) z hz
    have eBranch : MachineEval m g ω exteriorSelfChoiceCode st 4 (payUnit mid) :=
      MachineEval.pointerGt hh (by rw [h100,h112]; omega) ex
    refine ⟨4,payUnit mid,eBranch,by omega,?_,hI,hR,hQ,eBranch.unit_work exteriorSelfChoiceCode_wellFormed (by decide) hh,hO,hH⟩
    change mid.scalar.core.regs 48= _
    simpa only [if_pos (show i < t by omega),Int.cast_neg,Int.cast_one,neg_one_mul] using h48

set_option maxHeartbeats 4000000 in
lemma exterior_self_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width i t : ℕ) (v : Fin n) (z : ℝ)
    (h0 : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hb : st.scalar.core.ptrs 87=((16*(i+1) : ℕ) : ℤ))
    (h100 : st.scalar.core.ptrs 100=(i : ℤ)) (h112 : st.scalar.core.ptrs 112=(t : ℤ))
    (hz : st.scalar.core.regs 42=z) (hOne : st.scalar.core.regs 31=1) :
    ∃ steps out, MachineEval m g ω exteriorSelfCode st steps out ∧ steps ≤ 4*width+17 ∧
      out.scalar.core.mem=(if i ≤ t then Function.update st.scalar.core.mem
        (vertexRecordAddress width v.val (16*(i+1)+1))
        (st.scalar.core.mem (vertexRecordAddress width v.val (16*(i+1)+1))+(if i < t then -z else -5*z)) else st.scalar.core.mem) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  by_cases hi : i ≤ t
  · obtain ⟨u,a,ea,hu,a48,aI,aR,aQ,aW,aO,aH⟩ := exterior_self_choice_exec m g ω (payUnit st) hh i t z hi h100 h112 hz
    have a87 := (ea.pointer_frame 87 (by decide)).trans hb
    obtain ⟨b,eb,b44,bI,bR,bQ,bW,bO,bH⟩ := exterior_residual_offset_exec m g ω a aH (16*(i+1)) a87
    have eBefore := MachineEval.seq ea eb
    obtain ⟨out,ec,cR,cI,cQ,cW,cO,cH⟩ := vertex_real_add_from_exec m g ω b bH width v.val (16*(i+1)+1) 48
      ((eBefore.pointer_frame 0 (by decide)).trans h0) ((eBefore.pointer_frame 40 (by decide)).trans hv)
      ((eBefore.pointer_frame 41 (by decide)).trans hw) b44 ((eBefore.real_register_frame 31 (by decide)).trans hOne)
    have eBody := MachineEval.seq ea (MachineEval.seq eb ec)
    have ex : MachineEval m g ω exteriorSelfCode st (1+(u+(2+(4*width+10)))) out :=
      MachineEval.pointerLe hh (by rw [h100,h112]; exact_mod_cast hi) eBody
    refine ⟨1+(u+(2+(4*width+10))),out,ex,by omega,?_,cI.trans (bI.trans aI),cQ.trans (bQ.trans aQ),
      ex.unit_work exteriorSelfCode_wellFormed (by decide) hh,cO.trans (bO.trans aO),cH⟩
    rw [if_pos hi,cR,(eb.real_register_frame 48 (by decide)),a48,bR,aR]
    rfl
  · have ex : MachineEval m g ω exteriorSelfCode st 2 (payUnit (payUnit st)) :=
      MachineEval.pointerGt hh (by rw [h100,h112]; omega) (MachineEval.skip (payUnit st))
    refine ⟨2,payUnit (payUnit st),ex,by omega,?_,rfl,rfl,ex.unit_work exteriorSelfCode_wellFormed (by decide) hh,rfl,hh⟩
    rw [if_neg hi]
    rfl

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

-- Proof module: Solutions.ExteriorBudgetUpdate

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma exteriorBudgetCode_wellFormed : exteriorBudgetCode.wellFormed :=
  ⟨⟨levelHeaderIntegerLoadCode_wellFormed 9,trivial,levelHeaderAddFromCode_wellFormed 4 46⟩,trivial⟩

set_option maxHeartbeats 3500000 in
lemma exterior_budget_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (i t : ℕ) (flow : ℝ)
    (h0 : st.scalar.core.ptrs 0=0) (h100 : st.scalar.core.ptrs 100=(i : ℤ))
    (h112 : st.scalar.core.ptrs 112=(t : ℤ)) (hFlow : st.scalar.core.regs 46=flow) :
    ∃ steps out, MachineEval m g ω exteriorBudgetCode st steps out ∧ steps ≤ 31 ∧
      out.scalar.core.mem=(if t ≤ i ∧ 0 < st.scalar.integerMemory (levelHeaderAddress i 9) then
        Function.update st.scalar.core.mem (levelHeaderAddress i 4) (st.scalar.core.mem (levelHeaderAddress i 4)+flow)
        else st.scalar.core.mem) ∧ out.scalar.integerMemory=st.scalar.integerMemory ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  by_cases ht : t ≤ i
  · obtain ⟨a,ea,a105,a40,a41,aI,aR,aW,aO,aH⟩ := level_header_integer_load_exec m g ω (payUnit st) hh i 9 h100
    have a0 := (ea.pointer_frame 0 (by decide)).trans h0
    by_cases hopen : 0 < st.scalar.integerMemory (levelHeaderAddress i 9)
    · have a100 := (ea.pointer_frame 100 (by decide)).trans h100
      obtain ⟨b,eb,bR,bI,bQ,bW,bO,bH⟩ := level_header_add_from_exec m g ω (payUnit a) aH i 4 46 (by decide) a100
      have eOpen : MachineEval m g ω (.branchPointer 105 0 .skip (levelHeaderAddFromCode 4 46)) a 21 (payUnit b) :=
        MachineEval.pointerGt aH (by change ¬a.scalar.core.ptrs 105 ≤ a.scalar.core.ptrs 0; rw [a105,a0]; exact not_le.mpr hopen) eb
      have ex : MachineEval m g ω exteriorBudgetCode st 31 (payUnit b) :=
        MachineEval.pointerLe hh (by rw [h100,h112]; exact_mod_cast ht) (MachineEval.seq ea eOpen)
      refine ⟨31,payUnit b,ex,by omega,?_,bI.trans aI,ex.query_frame (by decide),
        ex.unit_work exteriorBudgetCode_wellFormed (by decide) hh,bO.trans aO,bH⟩
      have aFlow : a.scalar.core.regs 46=flow := (ea.real_register_frame 46 (by decide)).trans hFlow
      change b.scalar.core.mem= _
      rw [if_pos ⟨ht,hopen⟩,bR]
      change Function.update a.scalar.core.mem _ (a.scalar.core.mem _+a.scalar.core.regs 46)= _
      rw [aFlow,aR]
      rfl
    · have eOpen : MachineEval m g ω (.branchPointer 105 0 .skip (levelHeaderAddFromCode 4 46)) a 1 (payUnit a) :=
        MachineEval.pointerLe aH (by change a.scalar.core.ptrs 105 ≤ a.scalar.core.ptrs 0; rw [a105,a0]; exact le_of_not_gt hopen) (MachineEval.skip (payUnit a))
      have ex : MachineEval m g ω exteriorBudgetCode st 11 (payUnit a) :=
        MachineEval.pointerLe hh (by rw [h100,h112]; exact_mod_cast ht) (MachineEval.seq ea eOpen)
      refine ⟨11,payUnit a,ex,by omega,?_,aI,ex.query_frame (by decide),
        ex.unit_work exteriorBudgetCode_wellFormed (by decide) hh,aO,aH⟩
      rw [if_neg (by simp [hopen] : ¬(t ≤ i ∧ 0 < st.scalar.integerMemory (levelHeaderAddress i 9)))]
      exact aR
  · have ex : MachineEval m g ω exteriorBudgetCode st 2 (payUnit (payUnit st)) :=
      MachineEval.pointerGt hh (by rw [h100,h112]; omega) (MachineEval.skip (payUnit st))
    refine ⟨2,payUnit (payUnit st),ex,by omega,?_,rfl,rfl,
      ex.unit_work exteriorBudgetCode_wellFormed (by decide) hh,rfl,hh⟩
    rw [if_neg (by simp [ht] : ¬(t ≤ i ∧ 0 < st.scalar.integerMemory (levelHeaderAddress i 9)))]
    rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorSelfBudget

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma exteriorSelfBudgetCode_wellFormed : exteriorSelfBudgetCode.wellFormed :=
  ⟨exteriorSelfCode_wellFormed,exteriorBudgetCode_wellFormed⟩

set_option maxHeartbeats 4000000 in
lemma exterior_self_budget_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width i t : ℕ) (v : Fin n) (z flow : ℝ)
    (h0 : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hb : st.scalar.core.ptrs 87=((16*(i+1) : ℕ) : ℤ))
    (h100 : st.scalar.core.ptrs 100=(i : ℤ)) (h112 : st.scalar.core.ptrs 112=(t : ℤ))
    (hz : st.scalar.core.regs 42=z) (hFlow : st.scalar.core.regs 46=flow) (hOne : st.scalar.core.regs 31=1) :
    ∃ steps out, MachineEval m g ω exteriorSelfBudgetCode st steps out ∧ steps ≤ 4*width+48 ∧
      out.scalar.core.mem=exteriorSelfBudgetMemoryUpdate st.scalar.integerMemory width v.val t z flow i st.scalar.core.mem ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨u,a,ea,hu,aR,aI,aQ,aW,aO,aH⟩ := exterior_self_exec m g ω st hh width i t v z h0 hv hw hb h100 h112 hz hOne
  obtain ⟨w,out,eb,hwSteps,bR,bI,bQ,bW,bO,bH⟩ := exterior_budget_exec m g ω a aH i t flow
    ((ea.pointer_frame 0 (by decide)).trans h0) ((ea.pointer_frame 100 (by decide)).trans h100)
    ((ea.pointer_frame 112 (by decide)).trans h112) ((ea.real_register_frame 46 (by decide)).trans hFlow)
  have ex : MachineEval m g ω exteriorSelfBudgetCode st (u+w) out := MachineEval.seq ea eb
  refine ⟨u+w,out,ex,by omega,?_,bI.trans aI,bQ.trans aQ,
    ex.unit_work exteriorSelfBudgetCode_wellFormed (by decide) hh,bO.trans aO,bH⟩
  rw [bR,aI,aR]
  rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorSelfBudgetLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma exteriorSelfBudgetBodyCode_wellFormed : exteriorSelfBudgetBodyCode.wellFormed := by
  refine ⟨?_,levelContextCode_wellFormed,exteriorSelfBudgetCode_wellFormed,?_⟩
  all_goals simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma exteriorSelfBudgetLoopCode_wellFormed : exteriorSelfBudgetLoopCode.wellFormed := by
  refine ⟨?_,exteriorSelfBudgetBodyCode_wellFormed,?_⟩
  all_goals simp [exteriorSelfBudgetInitCode,exteriorSelfBudgetInitInstructions,linearCode,sequenceCode,coreCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

def ExteriorSelfBudgetContext (width top t vertex : ℕ) (z flow : ℝ) (I : ℤ → ℤ) (st : MachineState) : Prop :=
  st.scalar.core.ptrs 0=0 ∧ st.scalar.core.ptrs 50=(width : ℤ) ∧ st.scalar.core.ptrs 108=(top : ℤ) ∧
  st.scalar.core.ptrs 40=(vertex : ℤ) ∧ st.scalar.core.ptrs 112=(t : ℤ) ∧ st.scalar.core.regs 31=1 ∧
  st.scalar.core.regs 42=z ∧ st.scalar.core.regs 46=flow ∧ st.scalar.integerMemory=I

set_option maxHeartbeats 4000000 in
lemma exterior_self_budget_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width top t : ℕ) (v : Fin n) (z flow : ℝ) (I : ℤ → ℤ)
    (i : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (hCtx : ExteriorSelfBudgetContext width top t v.val z flow I st)
    (hIndex : st.scalar.core.ptrs 109=(i : ℤ)) (hStop : st.scalar.core.ptrs 111=((top+1 : ℕ) : ℤ)) :
    ∃ steps out, MachineEval m g ω exteriorSelfBudgetBodyCode st steps out ∧ steps ≤ 4*width+58 ∧
      out.scalar.core.ptrs 109=((i+1 : ℕ) : ℤ) ∧ out.scalar.core.ptrs 111=((top+1 : ℕ) : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧
      out.scalar.core.mem=exteriorSelfBudgetMemoryUpdate I width v.val t z flow i st.scalar.core.mem ∧
      ExteriorSelfBudgetContext width top t v.val z flow I out ∧ out.output=st.output := by
  rcases hCtx with ⟨h0,hWidth,hTop,hVertex,hSelected,hOne,hz,hFlow,hInteger⟩
  let a := payUnit (pointerWrite st 100 (i : ℤ))
  have ea : MachineEval m g ω (coreCode (.pcopy 100 109)) st 1 a := by
    simpa only [a,coreCode,hIndex] using pcopy_eval m g ω st 100 109 hh
  have a100 : a.scalar.core.ptrs 100=(i : ℤ) := by simp [a,payUnit,pcSet,pointerWrite]
  obtain ⟨b,eb,b87,b89,b41,bI,bR,bQ,bW,bO,bH⟩ := level_context_exec m g ω a hh i width a100
    ((ea.pointer_frame 50 (by decide)).trans hWidth)
  have ePrefix := MachineEval.seq ea eb
  obtain ⟨u,c,ec,hu,cR,cI,cQ,cW,cO,cH⟩ := exterior_self_budget_exec m g ω b bH width i t v z flow
    ((ePrefix.pointer_frame 0 (by decide)).trans h0) ((ePrefix.pointer_frame 40 (by decide)).trans hVertex)
    b41 b87 ((eb.pointer_frame 100 (by decide)).trans a100)
    ((ePrefix.pointer_frame 112 (by decide)).trans hSelected) ((ePrefix.real_register_frame 42 (by decide)).trans hz)
    ((ePrefix.real_register_frame 46 (by decide)).trans hFlow) ((ePrefix.real_register_frame 31 (by decide)).trans hOne)
  have eBefore := MachineEval.seq ea (MachineEval.seq eb ec)
  have cIndex := (eBefore.pointer_frame 109 (by decide)).trans hIndex
  let out := payUnit (pointerWrite c 109 ((i+1 : ℕ) : ℤ))
  have ed : MachineEval m g ω (coreCode (.pinc 109)) c 1 out := by
    simpa only [out,coreCode,cIndex,Nat.cast_add,Nat.cast_one] using pinc_eval m g ω c 109 cH
  have ex : MachineEval m g ω exteriorSelfBudgetBodyCode st (1+(8+(u+1))) out :=
    MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  have hOutI : out.scalar.integerMemory=st.scalar.integerMemory := cI.trans bI
  refine ⟨1+(8+(u+1)),out,ex,by omega,by simp [out,payUnit,pcSet,pointerWrite],
    (ex.pointer_frame 111 (by decide)).trans hStop,hOutI,?_,?_,cO.trans bO⟩
  · change c.scalar.core.mem= _
    rw [cR,bI,bR]
    change exteriorSelfBudgetMemoryUpdate st.scalar.integerMemory width v.val t z flow i st.scalar.core.mem= _
    rw [hInteger]
  · exact ⟨(ex.pointer_frame 0 (by decide)).trans h0,(ex.pointer_frame 50 (by decide)).trans hWidth,
      (ex.pointer_frame 108 (by decide)).trans hTop,(ex.pointer_frame 40 (by decide)).trans hVertex,
      (ex.pointer_frame 112 (by decide)).trans hSelected,(ex.real_register_frame 31 (by decide)).trans hOne,
      (ex.real_register_frame 42 (by decide)).trans hz,(ex.real_register_frame 46 (by decide)).trans hFlow,hOutI.trans hInteger⟩

set_option maxHeartbeats 6000000 in
lemma exterior_self_budget_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width top t : ℕ) (v : Fin n) (z flow : ℝ) (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (hWidth : st.scalar.core.ptrs 50=(width : ℤ))
    (hTop : st.scalar.core.ptrs 108=(top : ℤ)) (hVertex : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hSelected : st.scalar.core.ptrs 112=(t : ℤ)) (hOne : st.scalar.core.regs 31=1)
    (hz : st.scalar.core.regs 42=z) (hFlow : st.scalar.core.regs 46=flow) :
    ∃ steps out, MachineEval m g ω exteriorSelfBudgetLoopCode st steps out ∧
      steps ≤ (top+1)*(4*width+60)+5 ∧ out.scalar.core.ptrs 100=(top : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧
      out.scalar.core.mem=levelRealMemoryFold (exteriorSelfBudgetMemoryUpdate st.scalar.integerMemory width v.val t z flow) 0 (top+1) st.scalar.core.mem ∧
      ExteriorSelfBudgetContext width top t v.val z flow st.scalar.integerMemory out ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := linearRun m g ω exteriorSelfBudgetInitInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω exteriorSelfBudgetInitInstructions
    (by simp [exteriorSelfBudgetInitInstructions,unitInstruction,straightInstruction]) st hh
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,exteriorSelfBudgetInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have aR : a.scalar.core.mem=st.scalar.core.mem := by
    simp [a,linearRun,exteriorSelfBudgetInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,exteriorSelfBudgetInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have a109 : a.scalar.core.ptrs 109=0 := by
    simp [a,linearRun,exteriorSelfBudgetInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have a111 : a.scalar.core.ptrs 111=((top+1 : ℕ) : ℤ) := by
    simp [a,linearRun,exteriorSelfBudgetInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh,hTop]
  have aCtx : ExteriorSelfBudgetContext width top t v.val z flow st.scalar.integerMemory a :=
    ⟨(ea.pointer_frame 0 (by decide)).trans h0,(ea.pointer_frame 50 (by decide)).trans hWidth,
      (ea.pointer_frame 108 (by decide)).trans hTop,(ea.pointer_frame 40 (by decide)).trans hVertex,
      (ea.pointer_frame 112 (by decide)).trans hSelected,(ea.real_register_frame 31 (by decide)).trans hOne,
      (ea.real_register_frame 42 (by decide)).trans hz,(ea.real_register_frame 46 (by decide)).trans hFlow,aI⟩
  obtain ⟨u,b,eb,hu,b109,b111,bI,bR,bCtx,bQ,bW,bO,bH⟩ :=
    scalar_level_loop_exec m g ω exteriorSelfBudgetBodyCode (4*width+58) top
      (exteriorSelfBudgetMemoryUpdate st.scalar.integerMemory width v.val t z flow)
      (fun _ => ExteriorSelfBudgetContext width top t v.val z flow st.scalar.integerMemory)
      exteriorSelfBudgetBodyCode_wellFormed (by decide) (by decide) (by intros i q h; exact h)
      (by intro i hi q hq hCtx hIndex hStop; exact exterior_self_budget_body_exec m g ω width top t v z flow st.scalar.integerMemory i q hq hCtx hIndex hStop)
      (top+1) 0 a aH aCtx (by omega) a109 a111
  let out := payUnit (pointerWrite b 100 (top : ℤ))
  have el : MachineEval m g ω (coreCode (.pcopy 100 108)) b 1 out := by
    have b108 := bCtx.2.2.1
    simpa only [out,coreCode,b108] using pcopy_eval m g ω b 100 108 bH
  have ex : MachineEval m g ω exteriorSelfBudgetLoopCode st (3+(u+1)) out := MachineEval.seq ea (MachineEval.seq eb el)
  refine ⟨3+(u+1),out,ex,?_,by simp [out,payUnit,pcSet,pointerWrite],bI.trans aI,?_,bCtx,
    ex.query_frame (by decide),ex.unit_work exteriorSelfBudgetLoopCode_wellFormed (by decide) hh,bO.trans aO,bH⟩
  · have hBase : 4*width+58+2=4*width+60 := by omega
    rw [hBase] at hu
    omega
  · change b.scalar.core.mem= _
    rw [bR,aR]

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

-- Proof module: Solutions.DegreeRecordStore

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma degreeRecordStoreCode_wellFormed : degreeRecordStoreCode.wellFormed := by
  refine ⟨?_,vertexFieldWriteCode_wellFormed 0 60⟩
  simp [MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 1400000 in
lemma degree_record_store_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width : ℕ) (v : Fin n)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) :
    ∃ out, MachineEval m g ω degreeRecordStoreCode st (4*width+10) out ∧
      out.scalar.core.ptrs 60=((g.neighbors v).length : ℤ) ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (vertexRecordAddress width v.val 0) ((g.neighbors v).length : ℤ) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.regs=st.scalar.core.regs ∧
      out.scalar.queries=st.scalar.queries+1 ∧ out.work=st.work+(4*width+10 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,ep,hp60,hpI,hpR,hpQ,hpW,hpO,hpH⟩ := degree_query_exec m g ω st hh 60 40
  rw [hv,degree_answer_vertex] at hp60
  have hp0 := (ep.pointer_frame 0 (by decide)).trans hz
  have hp40 := (ep.pointer_frame 40 (by decide)).trans hv
  have hp41 := (ep.pointer_frame 41 (by decide)).trans hw
  obtain ⟨out,es,hoI,hoR,hoQ,hoW,hoO,hoH⟩ := vertex_field_write_exec m g ω pre hpH width v.val 0 60 hp0 hp40 hp41
  have eRun : MachineEval m g ω degreeRecordStoreCode st (4*width+10) out := by
    have ee := MachineEval.seq ep es
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,(es.pointer_frame 60 (by decide)).trans hp60,?_,hoR.trans hpR,?_,hoQ.trans hpQ,?_,hoO.trans hpO,hoH⟩
  · rw [hoI,hpI,hp60]
  · exact eRun.register_frame (by
      simp [degreeRecordStoreCode,vertexFieldWriteCode,fieldWritePrepRoutine,PointerRoutine.sequence,
        PointerRoutine.code,PointerOp.instruction,vertexIntegerStoreCode,MachineCode.allAtoms,
        vertexAddressCode_registerReadOnly,coreCode,registerReadOnly])
  · rw [hoW,hpW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DomainResidualUpdate

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma domainResidualAddCode_wellFormed : domainResidualAddCode.wellFormed :=
  ⟨trivial,exteriorResidualOffsetCode_wellFormed,vertexRealAddFromCode_wellFormed 41⟩
lemma domainResidualStepCode_wellFormed : domainResidualStepCode.wellFormed :=
  ⟨domainResidualAddCode_wellFormed,domainAdvanceCode_wellFormed⟩

set_option maxHeartbeats 3000000 in
lemma domain_residual_add_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width base : ℕ) (v : Fin n)
    (domain : Finset (Fin n)) (delta : ℝ)
    (h0 : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hb : st.scalar.core.ptrs 87=(base : ℤ))
    (hFlag : st.scalar.core.ptrs 118=if v ∈ domain then 1 else 0)
    (hDelta : st.scalar.core.regs 41=delta) (hOne : st.scalar.core.regs 31=1) :
    ∃ steps out, MachineEval m g ω domainResidualAddCode st steps out ∧ steps ≤ 4*width+14 ∧
      out.scalar.core.mem=(if v ∈ domain then Function.update st.scalar.core.mem (vertexRecordAddress width v.val (base+1))
        (st.scalar.core.mem (vertexRecordAddress width v.val (base+1))+delta) else st.scalar.core.mem) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  classical
  by_cases hDomain : v ∈ domain
  · obtain ⟨a,ea,a44,aI,aR,aQ,aW,aO,aH⟩ := exterior_residual_offset_exec m g ω (payUnit st) hh base hb
    obtain ⟨b,eb,bR,bI,bQ,bW,bO,bH⟩ := vertex_real_add_from_exec m g ω a aH width v.val (base+1) 41
      ((ea.pointer_frame 0 (by decide)).trans h0) ((ea.pointer_frame 40 (by decide)).trans hv)
      ((ea.pointer_frame 41 (by decide)).trans hw) a44 ((ea.real_register_frame 31 (by decide)).trans hOne)
    have ex : MachineEval m g ω domainResidualAddCode st (1+(2+(4*width+10))+1) (payUnit b) :=
      MachineEval.pointerGt hh (by rw [hFlag,if_pos hDomain,h0]; norm_num) (MachineEval.seq ea eb)
    refine ⟨1+(2+(4*width+10))+1,payUnit b,ex,by omega,?_,bI.trans aI,ex.query_frame (by decide),
      ex.unit_work domainResidualAddCode_wellFormed (by decide) hh,bO.trans aO,bH⟩
    have aDelta : a.scalar.core.regs 41=delta := (ea.real_register_frame 41 (by decide)).trans hDelta
    change b.scalar.core.mem= _
    rw [if_pos hDomain,bR,aDelta,aR]
    rfl
  · have ex : MachineEval m g ω domainResidualAddCode st 1 (payUnit st) :=
      MachineEval.pointerLe hh (by rw [hFlag,if_neg hDomain,h0]) (MachineEval.skip (payUnit st))
    refine ⟨1,payUnit st,ex,by omega,?_,rfl,rfl,ex.unit_work domainResidualAddCode_wellFormed (by decide) hh,rfl,hh⟩
    rw [if_neg hDomain]
    rfl

set_option maxHeartbeats 3500000 in
lemma domain_residual_step_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width base : ℕ) (v : Fin n)
    (domain active : Finset (Fin n)) (delta : ℝ) (hSubset : active ⊆ domain)
    (h0 : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hb : st.scalar.core.ptrs 87=(base : ℤ))
    (hFlag : st.scalar.core.ptrs 118=if v ∈ domain then 1 else 0)
    (hRecord : v ∈ domain → st.scalar.integerMemory (vertexRecordAddress width v.val (base+2))=(if v ∈ active then 1 else 0))
    (hDelta : st.scalar.core.regs 41=delta) (hOne : st.scalar.core.regs 31=1) :
    ∃ steps out, MachineEval m g ω domainResidualStepCode st steps out ∧ steps ≤ 8*width+27 ∧
      out.scalar.core.ptrs 118=(if v ∈ active then 1 else 0) ∧
      out.scalar.core.mem=(if v ∈ domain then Function.update st.scalar.core.mem (vertexRecordAddress width v.val (base+1))
        (st.scalar.core.mem (vertexRecordAddress width v.val (base+1))+delta) else st.scalar.core.mem) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨u,a,ea,hu,aR,aI,aQ,aW,aO,aH⟩ := domain_residual_add_exec m g ω st hh width base v domain delta h0 hv hw hb hFlag hDelta hOne
  obtain ⟨w,out,eb,hwSteps,b118,bI,bR,bG,bQ,bW,bO,bH⟩ := domain_advance_exec m g ω a aH width base v domain active hSubset
    ((ea.pointer_frame 0 (by decide)).trans h0) ((ea.pointer_frame 40 (by decide)).trans hv)
    ((ea.pointer_frame 41 (by decide)).trans hw) ((ea.pointer_frame 87 (by decide)).trans hb)
    ((ea.pointer_frame 118 (by decide)).trans hFlag) (by intro h; rw [aI]; exact hRecord h)
  have ex := MachineEval.seq ea eb
  refine ⟨u+w,out,ex,by omega,b118,bR.trans aR,bI.trans aI,bQ.trans aQ,
    ex.unit_work domainResidualStepCode_wellFormed (by decide) hh,bO.trans aO,bH⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DomainResidualBody

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma domainResidualBodyCode_wellFormed : domainResidualBodyCode.wellFormed := by
  refine ⟨?_,levelContextCode_wellFormed,domainResidualStepCode_wellFormed,?_⟩
  all_goals simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

def DomainResidualContext {n : ℕ} (logical : RecursiveState n) (width : ℕ) (v : Fin n)
    (delta : ℝ) (I : ℤ → ℤ) (i : ℕ) (st : MachineState) : Prop :=
  st.scalar.core.ptrs 0=0 ∧ st.scalar.core.ptrs 50=(width : ℤ) ∧
  st.scalar.core.ptrs 108=(logical.top : ℤ) ∧ st.scalar.core.ptrs 40=(v.val : ℤ) ∧
  st.scalar.core.regs 31=1 ∧ st.scalar.core.regs 41=delta ∧ st.scalar.integerMemory=I ∧
  st.scalar.core.ptrs 118=(if v ∈ parentDomain logical i then 1 else 0)

set_option maxHeartbeats 4500000 in
lemma domain_residual_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (width : ℕ) (v : Fin n) (delta : ℝ) (I : ℤ → ℤ)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hRecords : ∀ i ≤ logical.top, v ∈ parentDomain logical i →
      I (vertexRecordAddress width v.val (16*(i+1)+2))=(if v ∈ (logical.frames i).active then 1 else 0))
    (i : ℕ) (hi : i ≤ logical.top) (st : MachineState) (hh : st.scalar.halted=false)
    (hCtx : DomainResidualContext logical width v delta I i st)
    (hIndex : st.scalar.core.ptrs 109=(i : ℤ)) (hStop : st.scalar.core.ptrs 111=((logical.top+1 : ℕ) : ℤ)) :
    ∃ steps out, MachineEval m g ω domainResidualBodyCode st steps out ∧ steps ≤ 8*width+37 ∧
      out.scalar.core.ptrs 109=((i+1 : ℕ) : ℤ) ∧ out.scalar.core.ptrs 111=((logical.top+1 : ℕ) : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=domainResidualMemoryUpdate logical width v delta i st.scalar.core.mem ∧
      DomainResidualContext logical width v delta I (i+1) out ∧ out.output=st.output := by
  rcases hCtx with ⟨h0,hWidth,hTop,hVertex,hOne,hDelta,hInteger,hBit⟩
  let a := payUnit (pointerWrite st 100 (i : ℤ))
  have ea : MachineEval m g ω (coreCode (.pcopy 100 109)) st 1 a := by
    simpa only [a,coreCode,hIndex] using pcopy_eval m g ω st 100 109 hh
  have a100 : a.scalar.core.ptrs 100=(i : ℤ) := by simp [a,payUnit,pcSet,pointerWrite]
  obtain ⟨b,eb,b87,b89,b41,bI,bR,bQ,bW,bO,bH⟩ := level_context_exec m g ω a hh i width a100
    ((ea.pointer_frame 50 (by decide)).trans hWidth)
  have ePrefix := MachineEval.seq ea eb
  obtain ⟨u,c,ec,hu,c118,cR,cI,cQ,cW,cO,cH⟩ := domain_residual_step_exec m g ω b bH width (16*(i+1)) v
    (parentDomain logical i) (logical.frames i).active delta (hSubset i hi)
    ((ePrefix.pointer_frame 0 (by decide)).trans h0) ((ePrefix.pointer_frame 40 (by decide)).trans hVertex)
    b41 b87 ((ePrefix.pointer_frame 118 (by decide)).trans hBit)
    (by intro hv'; rw [bI]; change st.scalar.integerMemory _= _; rw [hInteger]; exact hRecords i hi hv')
    ((ePrefix.real_register_frame 41 (by decide)).trans hDelta)
    ((ePrefix.real_register_frame 31 (by decide)).trans hOne)
  have eBefore := MachineEval.seq ea (MachineEval.seq eb ec)
  have cIndex := (eBefore.pointer_frame 109 (by decide)).trans hIndex
  let out := payUnit (pointerWrite c 109 ((i+1 : ℕ) : ℤ))
  have ed : MachineEval m g ω (coreCode (.pinc 109)) c 1 out := by
    simpa only [out,coreCode,cIndex,Nat.cast_add,Nat.cast_one] using pinc_eval m g ω c 109 cH
  have ex : MachineEval m g ω domainResidualBodyCode st (1+(8+(u+1))) out :=
    MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  have hOutI : out.scalar.integerMemory=st.scalar.integerMemory := cI.trans bI
  refine ⟨1+(8+(u+1)),out,ex,by omega,by simp [out,payUnit,pcSet,pointerWrite],
    (ex.pointer_frame 111 (by decide)).trans hStop,hOutI,?_,?_,cO.trans bO⟩
  · change c.scalar.core.mem= _
    rw [cR,bR]
    rfl
  · refine ⟨(ex.pointer_frame 0 (by decide)).trans h0,(ex.pointer_frame 50 (by decide)).trans hWidth,
      (ex.pointer_frame 108 (by decide)).trans hTop,(ex.pointer_frame 40 (by decide)).trans hVertex,
      (ex.real_register_frame 31 (by decide)).trans hOne,(ex.real_register_frame 41 (by decide)).trans hDelta,
      hOutI.trans hInteger,?_⟩
    have hDomain : parentDomain logical (i+1)=(logical.frames i).active := by simp [parentDomain]
    rw [hDomain]
    exact (ed.pointer_frame 118 (by decide)).trans c118

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DomainResidualLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma domainResidualLoopCode_wellFormed : domainResidualLoopCode.wellFormed := by
  refine ⟨?_,domainResidualBodyCode_wellFormed,?_⟩
  all_goals simp [domainResidualInitCode,domainResidualInitInstructions,linearCode,sequenceCode,coreCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 6000000 in
lemma domain_residual_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (width : ℕ) (v : Fin n) (delta : ℝ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hRecords : ∀ i ≤ logical.top, v ∈ parentDomain logical i →
      st.scalar.integerMemory (vertexRecordAddress width v.val (16*(i+1)+2))=(if v ∈ (logical.frames i).active then 1 else 0))
    (h0 : st.scalar.core.ptrs 0=0) (hWidth : st.scalar.core.ptrs 50=(width : ℤ))
    (hTop : st.scalar.core.ptrs 108=(logical.top : ℤ)) (hVertex : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hOne : st.scalar.core.regs 31=1) (hDelta : st.scalar.core.regs 41=delta) :
    ∃ steps out, MachineEval m g ω domainResidualLoopCode st steps out ∧
      steps ≤ (logical.top+1)*(8*width+39)+6 ∧
      out.scalar.core.ptrs 100=(logical.top : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧
      out.scalar.core.mem=levelRealMemoryFold (domainResidualMemoryUpdate logical width v delta) 0
        (logical.top+1) st.scalar.core.mem ∧
      DomainResidualContext logical width v delta st.scalar.integerMemory (logical.top+1) out ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := linearRun m g ω domainResidualInitInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω domainResidualInitInstructions
    (by simp [domainResidualInitInstructions,unitInstruction,straightInstruction]) st hh
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,domainResidualInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have aR : a.scalar.core.mem=st.scalar.core.mem := by
    simp [a,linearRun,domainResidualInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,domainResidualInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have a109 : a.scalar.core.ptrs 109=0 := by
    simp [a,linearRun,domainResidualInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have a111 : a.scalar.core.ptrs 111=((logical.top+1 : ℕ) : ℤ) := by
    simp [a,linearRun,domainResidualInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh,hTop]
  have a118 : a.scalar.core.ptrs 118=1 := by
    simp [a,linearRun,domainResidualInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have aCtx : DomainResidualContext logical width v delta st.scalar.integerMemory 0 a := by
    refine ⟨(ea.pointer_frame 0 (by decide)).trans h0,(ea.pointer_frame 50 (by decide)).trans hWidth,
      (ea.pointer_frame 108 (by decide)).trans hTop,(ea.pointer_frame 40 (by decide)).trans hVertex,
      (ea.real_register_frame 31 (by decide)).trans hOne,(ea.real_register_frame 41 (by decide)).trans hDelta,aI,?_⟩
    simpa [parentDomain] using a118
  obtain ⟨u,b,eb,hu,b109,b111,bI,bR,bCtx,bQ,bW,bO,bH⟩ :=
    scalar_level_loop_exec m g ω domainResidualBodyCode (8*width+37) logical.top
      (domainResidualMemoryUpdate logical width v delta)
      (DomainResidualContext logical width v delta st.scalar.integerMemory)
      domainResidualBodyCode_wellFormed (by decide) (by decide) (by intros i z h; exact h)
      (domain_residual_body_exec m g ω logical width v delta st.scalar.integerMemory hSubset hRecords)
      (logical.top+1) 0 a aH aCtx (by omega) a109 a111
  let out := payUnit (pointerWrite b 100 (logical.top : ℤ))
  have el : MachineEval m g ω (coreCode (.pcopy 100 108)) b 1 out := by
    have b108 := bCtx.2.2.1
    simpa only [out,coreCode,b108] using pcopy_eval m g ω b 100 108 bH
  have ex : MachineEval m g ω domainResidualLoopCode st (4+(u+1)) out := MachineEval.seq ea (MachineEval.seq eb el)
  refine ⟨4+(u+1),out,ex,?_,by simp [out,payUnit,pcSet,pointerWrite],bI.trans aI,?_,bCtx,
    ex.query_frame (by decide),ex.unit_work domainResidualLoopCode_wellFormed (by decide) hh,bO.trans aO,bH⟩
  · have hBase : 8*width+37+2=8*width+39 := by omega
    rw [hBase] at hu
    omega
  · change b.scalar.core.mem= _
    rw [bR,aR]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredNeighborBody

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma storedNeighborBodyCode_wellFormed : storedNeighborBodyCode.wellFormed := by
  refine ⟨storedNeighborReadCode_wellFormed,degreeRecordStoreCode_wellFormed,domainResidualLoopCode_wellFormed,?_⟩
  simp [storedNeighborTailCode,storedNeighborTailInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

structure StoredNeighborContext {n : ℕ} (g : InputGraph n) (source : Fin n)
    (logical : RecursiveState n) (ell : ℕ) (delta : ℝ) (base : ℤ) (st : MachineState) : Prop where
  zero : st.scalar.core.ptrs 0=0
  width : st.scalar.core.ptrs 50=((16*(ell+3) : ℕ) : ℤ)
  top : st.scalar.core.ptrs 108=(logical.top : ℤ)
  selected : st.scalar.core.ptrs 116=(source.val : ℤ)
  degree : st.scalar.core.ptrs 120=((g.neighbors source).length : ℤ)
  basePtr : st.scalar.core.ptrs 121=base
  one : st.scalar.core.regs 31=1
  deltaReg : st.scalar.core.regs 41=delta
  row : ∀ i < (g.neighbors source).length,
    st.scalar.integerMemory (base+(i : ℤ))=((storedNeighborVertex g source i).val : ℤ)
  active : ∀ i ≤ logical.top, ∀ v ∈ parentDomain logical i,
    st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(i+1)+2))=
      (if v ∈ (logical.frames i).active then 1 else 0)

set_option maxHeartbeats 6000000 in
lemma stored_neighbor_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (source : Fin n) (logical : RecursiveState n) (ell : ℕ) (delta : ℝ) (base : ℤ)
    (hBase : 128 ≤ base) (hDepth : logical.top ≤ ell)
    (hSubset : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (i : ℕ) (hi : i < (g.neighbors source).length) (st : MachineState) (hh : st.scalar.halted=false)
    (hCtx : StoredNeighborContext g source logical ell delta base st)
    (hIndex : st.scalar.core.ptrs 109=(i : ℤ))
    (hStop : st.scalar.core.ptrs 111=((g.neighbors source).length : ℤ)) :
    ∃ steps out, MachineEval m g ω storedNeighborBodyCode st steps out ∧
      steps ≤ (logical.top+1)*(8*(16*(ell+3))+39)+4*(16*(ell+3))+23 ∧
      out.scalar.core.ptrs 109=((i+1 : ℕ) : ℤ) ∧
      out.scalar.core.ptrs 111=((g.neighbors source).length : ℤ) ∧
      (out.scalar.integerMemory,out.scalar.core.mem)=storedNeighborMemoryUpdate g source logical ell delta i
        (st.scalar.integerMemory,st.scalar.core.mem) ∧
      StoredNeighborContext g source logical ell delta base out ∧
      out.scalar.queries=st.scalar.queries+1 ∧ out.output=st.output := by
  let width := 16*(ell+3)
  let v := storedNeighborVertex g source i
  obtain ⟨a,ea,a122,a40,a41,aI,aR,aQ,aW,aO,aH⟩ := stored_neighbor_read_exec m g ω st hh i width base v
    hIndex hCtx.basePtr hCtx.width (hCtx.row i hi)
  obtain ⟨b,eb,b60,bI,bR,bRegs,bQ,bW,bO,bH⟩ := degree_record_store_exec m g ω a aH width v
    ((ea.pointer_frame 0 (by decide)).trans hCtx.zero) a40 a41
  have ePrefix := MachineEval.seq ea eb
  have bRecords : ∀ j ≤ logical.top, v ∈ parentDomain logical j →
      b.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+2))=
        (if v ∈ (logical.frames j).active then 1 else 0) := by
    intro j hj hv
    rw [bI,vertex_integer_update_other_field _ width v.val v.val 0 (16*(j+1)+2) _
      (by dsimp [width]; omega) (by dsimp [width]; omega) (by omega),aI]
    exact hCtx.active j hj v hv
  obtain ⟨u,c,ec,hu,c100,cI,cR,cCtx,cQ,cW,cO,cH⟩ := domain_residual_loop_exec m g ω logical width v delta b bH
    hSubset bRecords ((ePrefix.pointer_frame 0 (by decide)).trans hCtx.zero)
    ((ePrefix.pointer_frame 50 (by decide)).trans hCtx.width)
    ((ePrefix.pointer_frame 108 (by decide)).trans hCtx.top)
    ((eb.pointer_frame 40 (by decide)).trans a40)
    ((ePrefix.real_register_frame 31 (by decide)).trans hCtx.one)
    ((ePrefix.real_register_frame 41 (by decide)).trans hCtx.deltaReg)
  have eBefore := MachineEval.seq ea (MachineEval.seq eb ec)
  have c122 := (MachineEval.seq eb ec).pointer_frame 122 (by decide)
  have c120 := (eBefore.pointer_frame 120 (by decide)).trans hCtx.degree
  obtain ⟨ed,dW,dH⟩ := linear_execute m g ω storedNeighborTailInstructions
    (by simp [storedNeighborTailInstructions,unitInstruction,straightInstruction]) c cH
  let out := linearRun m g ω storedNeighborTailInstructions c
  have d109 : out.scalar.core.ptrs 109=((i+1 : ℕ) : ℤ) := by
    simp [out,linearRun,storedNeighborTailInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,cH,c122,a122]
  have d111 : out.scalar.core.ptrs 111=((g.neighbors source).length : ℤ) := by
    simp [out,linearRun,storedNeighborTailInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,cH,c120]
  have dI : out.scalar.integerMemory=Function.update st.scalar.integerMemory
      (vertexRecordAddress width v.val 0) ((g.neighbors v).length : ℤ) := by
    have frame : out.scalar.integerMemory=c.scalar.integerMemory := by
      simp [out,linearRun,storedNeighborTailInstructions,atomState,machineStep,pcSet,LocalPush.step,
        scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,cH]
    rw [frame,cI,bI,aI]
  have dR : out.scalar.core.mem=levelRealMemoryFold (domainResidualMemoryUpdate logical width v delta) 0
      (logical.top+1) st.scalar.core.mem := by
    have frame : out.scalar.core.mem=c.scalar.core.mem := by
      simp [out,linearRun,storedNeighborTailInstructions,atomState,machineStep,pcSet,LocalPush.step,
        scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,cH]
    rw [frame,cR,bR,aR]
  have ex : MachineEval m g ω storedNeighborBodyCode st (4+(4*width+10+(u+3))) out := by
    have er := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
    convert er using 1 <;> rfl
  refine ⟨4+(4*width+10+(u+3)),out,ex,by dsimp [width] at hu ⊢; omega,d109,d111,?_,?_,?_,?_⟩
  · exact Prod.ext dI dR
  · refine ⟨(ex.pointer_frame 0 (by decide)).trans hCtx.zero,
      (ex.pointer_frame 50 (by decide)).trans hCtx.width,
      (ex.pointer_frame 108 (by decide)).trans hCtx.top,
      (ex.pointer_frame 116 (by decide)).trans hCtx.selected,
      (ex.pointer_frame 120 (by decide)).trans hCtx.degree,
      (ex.pointer_frame 121 (by decide)).trans hCtx.basePtr,
      (ex.real_register_frame 31 (by decide)).trans hCtx.one,
      (ex.real_register_frame 41 (by decide)).trans hCtx.deltaReg,?_,?_⟩
    · intro k hk
      rw [dI]
      have hAddr : base+(k : ℤ) ≠ vertexRecordAddress width v.val 0 := by
        have := vertexRecordAddress_negative width v.val 0
        have := Int.natCast_nonneg k
        omega
      rw [Function.update_of_ne hAddr]
      exact hCtx.row k hk
    · intro j hj w hw
      rw [dI,vertex_integer_update_other_field _ width v.val w.val 0 (16*(j+1)+2) _
        (by dsimp [width]; omega) (by dsimp [width]; omega) (by omega)]
      exact hCtx.active j hj w hw
  · have dQ : out.scalar.queries=c.scalar.queries := ed.query_frame (by decide)
    rw [dQ,cQ,bQ,aQ]
  · have dO : out.output=c.output := by
      simp [out,linearRun,storedNeighborTailInstructions,atomState,machineStep,pcSet,LocalPush.step,
        scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,cH]
    exact dO.trans (cO.trans (bO.trans aO))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredNeighborLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma storedNeighborLoopCode_wellFormed : storedNeighborLoopCode.wellFormed := by
  refine ⟨?_,storedNeighborBodyCode_wellFormed,?_⟩
  all_goals simp [storedNeighborInitCode,storedNeighborInitInstructions,storedNeighborRestoreCode,
    storedNeighborRestoreInstructions,linearCode,sequenceCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 7000000 in
lemma stored_neighbor_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (source : Fin n) (logical : RecursiveState n) (ell : ℕ) (delta : ℝ) (base : ℤ)
    (hBase : 128 ≤ base) (hDepth : logical.top ≤ ell)
    (hSubset : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (hWidth : st.scalar.core.ptrs 50=((16*(ell+3) : ℕ) : ℤ))
    (hTop : st.scalar.core.ptrs 108=(logical.top : ℤ))
    (hSelected : st.scalar.core.ptrs 116=(source.val : ℤ))
    (hDegree : st.scalar.core.ptrs 60=((g.neighbors source).length : ℤ))
    (hBasePtr : st.scalar.core.ptrs 61=base)
    (hOne : st.scalar.core.regs 31=1) (hDelta : st.scalar.core.regs 41=delta)
    (hRow : ∀ i < (g.neighbors source).length,
      st.scalar.integerMemory (base+(i : ℤ))=((storedNeighborVertex g source i).val : ℤ))
    (hRecords : ∀ i ≤ logical.top, ∀ v ∈ parentDomain logical i,
      st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(i+1)+2))=
        (if v ∈ (logical.frames i).active then 1 else 0)) :
    ∃ steps out, MachineEval m g ω storedNeighborLoopCode st steps out ∧
      steps ≤ (g.neighbors source).length*((logical.top+1)*(8*(16*(ell+3))+39)+4*(16*(ell+3))+25)+7 ∧
      out.scalar.core.ptrs 40=(source.val : ℤ) ∧ out.scalar.core.ptrs 100=(logical.top : ℤ) ∧
      (out.scalar.integerMemory,out.scalar.core.mem)=
        levelPayloadFold (storedNeighborMemoryUpdate g source logical ell delta) 0
          (g.neighbors source).length (st.scalar.integerMemory,st.scalar.core.mem) ∧
      StoredNeighborContext g source logical ell delta base out ∧
      out.scalar.queries=st.scalar.queries+(g.neighbors source).length ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := linearRun m g ω storedNeighborInitInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω storedNeighborInitInstructions
    (by simp [storedNeighborInitInstructions,unitInstruction,straightInstruction]) st hh
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,storedNeighborInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aR : a.scalar.core.mem=st.scalar.core.mem := by
    simp [a,linearRun,storedNeighborInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,storedNeighborInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have a109 : a.scalar.core.ptrs 109=0 := by
    simp [a,linearRun,storedNeighborInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have a111 : a.scalar.core.ptrs 111=((g.neighbors source).length : ℤ) := by
    simp [a,linearRun,storedNeighborInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hDegree]
  have aCtx : StoredNeighborContext g source logical ell delta base a := by
    refine ⟨(ea.pointer_frame 0 (by decide)).trans h0,(ea.pointer_frame 50 (by decide)).trans hWidth,
      (ea.pointer_frame 108 (by decide)).trans hTop,(ea.pointer_frame 116 (by decide)).trans hSelected,
      ?_,?_,(ea.real_register_frame 31 (by decide)).trans hOne,
      (ea.real_register_frame 41 (by decide)).trans hDelta,?_,?_⟩
    · simp [a,linearRun,storedNeighborInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
        scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hDegree]
    · simp [a,linearRun,storedNeighborInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
        scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hBasePtr]
    · simpa only [aI] using hRow
    · simpa only [aI] using hRecords
  obtain ⟨u,b,eb,hu,b109,b111,bData,bCtx,bQ,bW,bO,bH⟩ := payload_level_loop_exec m g ω storedNeighborBodyCode
    ((logical.top+1)*(8*(16*(ell+3))+39)+4*(16*(ell+3))+23) (g.neighbors source).length 1
    (fun z => (z.scalar.integerMemory,z.scalar.core.mem)) (storedNeighborMemoryUpdate g source logical ell delta)
    (fun _ z => StoredNeighborContext g source logical ell delta base z)
    storedNeighborBodyCode_wellFormed (by decide) (by intro z; rfl) (by intro i z h; exact ⟨h.zero,h.width,h.top,h.selected,h.degree,h.basePtr,h.one,h.deltaReg,h.row,h.active⟩)
    (stored_neighbor_body_exec m g ω source logical ell delta base hBase hDepth hSubset)
    (g.neighbors source).length 0 a aH aCtx (by omega) a109 a111
  let out := linearRun m g ω storedNeighborRestoreInstructions b
  obtain ⟨ec,cW,cH⟩ := linear_execute m g ω storedNeighborRestoreInstructions
    (by simp [storedNeighborRestoreInstructions,unitInstruction,straightInstruction]) b bH
  have cI : out.scalar.integerMemory=b.scalar.integerMemory := by
    simp [out,linearRun,storedNeighborRestoreInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH]
  have cR : out.scalar.core.mem=b.scalar.core.mem := by
    simp [out,linearRun,storedNeighborRestoreInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH]
  have ex : MachineEval m g ω storedNeighborLoopCode st (4+(u+2)) out := MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨4+(u+2),out,ex,?_,?_,?_,?_,?_,?_,ex.unit_work storedNeighborLoopCode_wellFormed (by decide) hh,?_,cH⟩
  · have hBound : (logical.top+1)*(8*(16*(ell+3))+39)+4*(16*(ell+3))+23+2=
        (logical.top+1)*(8*(16*(ell+3))+39)+4*(16*(ell+3))+25 := by omega
    rw [hBound] at hu
    omega
  · simp [out,linearRun,storedNeighborRestoreInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH,bCtx.selected]
  · simp [out,linearRun,storedNeighborRestoreInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH,bCtx.top]
  · rw [cI,cR,bData,aI,aR]
  · refine ⟨(ec.pointer_frame 0 (by decide)).trans bCtx.zero,
      (ec.pointer_frame 50 (by decide)).trans bCtx.width,
      (ec.pointer_frame 108 (by decide)).trans bCtx.top,
      (ec.pointer_frame 116 (by decide)).trans bCtx.selected,
      (ec.pointer_frame 120 (by decide)).trans bCtx.degree,
      (ec.pointer_frame 121 (by decide)).trans bCtx.basePtr,
      (ec.real_register_frame 31 (by decide)).trans bCtx.one,
      (ec.real_register_frame 41 (by decide)).trans bCtx.deltaReg,?_,?_⟩
    · simpa only [cI] using bCtx.row
    · simpa only [cI] using bCtx.active
  · rw [ec.query_frame (by decide),bQ,ea.query_frame (by decide),Nat.mul_one]
  · have cO : out.output=b.output := by
      simp [out,linearRun,storedNeighborRestoreInstructions,atomState,machineStep,pcSet,LocalPush.step,
        scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH]
    exact cO.trans (bO.trans aO)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.GraphCacheDegreeUpdate

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma GraphCache.degree_update {n : ℕ} (g : InputGraph n) (I : ℤ → ℤ) (width : ℕ)
    (stored : Finset (Fin n)) (free : ℤ) (cache : GraphCache g I width stored free) (v : Fin n) :
    GraphCache g (Function.update I (vertexRecordAddress width v.val 0) ((g.neighbors v).length : ℤ)) width stored free := by
  let J := Function.update I (vertexRecordAddress width v.val 0) ((g.neighbors v).length : ℤ)
  have hField (u : Fin n) (field : ℕ) (hf : field < width) (hn : field ≠ 0) :
      J (vertexRecordAddress width u.val field)=I (vertexRecordAddress width u.val field) :=
    vertex_integer_update_other_field I width v.val u.val 0 field _ (by have := cache.widthBound; omega) hf hn
  refine ⟨cache.widthBound,cache.freeBound,?_,?_,?_,?_,?_⟩
  · intro u
    change J (vertexRecordAddress width u.val 2)=_
    rw [hField u 2 (by have := cache.widthBound; omega) (by decide)]
    exact cache.flag u
  · intro u hu
    by_cases he : u=v
    · subst u
      exact Function.update_self _ _ _
    · have hAddr : vertexRecordAddress width u.val 0 ≠ vertexRecordAddress width v.val 0 := by
        intro h
        exact he (Fin.ext (vertexRecordAddress_injective width u.val v.val 0 0
          (by have := cache.widthBound; omega) (by have := cache.widthBound; omega) h).1)
      change J (vertexRecordAddress width u.val 0)= _
      rw [show J (vertexRecordAddress width u.val 0)=I (vertexRecordAddress width u.val 0) from Function.update_of_ne hAddr _ _]
      exact cache.degree u hu
  · intro u hu
    change 128 ≤ J (vertexRecordAddress width u.val 1)
    rw [hField u 1 (by have := cache.widthBound; omega) (by decide)]
    exact cache.basePositive u hu
  · intro u hu i hi hi'
    change J (J (vertexRecordAddress width u.val 1)+(i : ℤ))=_
    rw [hField u 1 (by have := cache.widthBound; omega) (by decide)]
    have hAddr : I (vertexRecordAddress width u.val 1)+(i : ℤ) ≠ vertexRecordAddress width v.val 0 := by
      have hp := cache.basePositive u hu
      have hn := vertexRecordAddress_negative width v.val 0
      have hi0 := Int.natCast_nonneg i
      omega
    change Function.update I _ _ _ = _
    rw [Function.update_of_ne hAddr]
    exact cache.adjacency u hu i hi hi'
  · intro u hu i hi
    change J (vertexRecordAddress width u.val 1)+(i : ℤ)<free
    rw [hField u 1 (by have := cache.widthBound; omega) (by decide)]
    exact cache.belowFree u hu i hi

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredNeighborMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma storedNeighborVertex_eq {n : ℕ} (g : InputGraph n) (source : Fin n) (i : ℕ)
    (hi : i < (g.neighbors source).length) : storedNeighborVertex g source i=(g.neighbors source)[i] := by
  simp [storedNeighborVertex,List.getElem?_eq_getElem hi]

lemma stored_neighbor_fold_graph_cache {n : ℕ} (g : InputGraph n) (source : Fin n)
    (logical : RecursiveState n) (ell : ℕ) (delta : ℝ) (stored : Finset (Fin n)) (free : ℤ)
    (payload : (ℤ → ℤ) × (ℤ → ℝ)) (cache : GraphCache g payload.1 (16*(ell+3)) stored free) :
    GraphCache g (levelPayloadFold (storedNeighborMemoryUpdate g source logical ell delta) 0
      (g.neighbors source).length payload).1 (16*(ell+3)) stored free := by
  apply level_payload_invariant (storedNeighborMemoryUpdate g source logical ell delta) (limit:=(g.neighbors source).length)
    (P:=fun p => GraphCache g p.1 (16*(ell+3)) stored free)
  · intro i hi p hp
    exact GraphCache.degree_update g p.1 (16*(ell+3)) stored free hp (storedNeighborVertex g source i)
  · omega
  · exact cache

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorPushProgramCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma exteriorPotentialAddCode_wellFormed : exteriorPotentialAddCode.wellFormed := by
  refine ⟨?_,vertexRealAddFromCode_wellFormed 40⟩
  simp [exteriorPotentialPrepCode,exteriorPotentialPrepInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma exteriorNumericPrefixCode_wellFormed : exteriorNumericPrefixCode.wellFormed :=
  ⟨exteriorScalarCode_wellFormed,cacheRowCode_wellFormed,exteriorPotentialAddCode_wellFormed,
    exteriorSelfBudgetLoopCode_wellFormed,storedNeighborLoopCode_wellFormed⟩
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorPotentialAdd

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2200000 in
lemma exterior_potential_add_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width : ℕ) (v : Fin n)
    (h0 : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 50=(width : ℤ)) (hOne : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω exteriorPotentialAddCode st (4*width+12) out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width v.val 0)
        (st.scalar.core.mem (vertexRecordAddress width v.val 0)+st.scalar.core.regs 40) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(4*width+12 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := linearRun m g ω exteriorPotentialPrepInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω exteriorPotentialPrepInstructions
    (by simp [exteriorPotentialPrepInstructions,unitInstruction,straightInstruction]) st hh
  have a41 : a.scalar.core.ptrs 41=(width : ℤ) := by
    simp [a,linearRun,exteriorPotentialPrepInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hw]
  have a44 : a.scalar.core.ptrs 44=0 := by
    simp [a,linearRun,exteriorPotentialPrepInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,exteriorPotentialPrepInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aR : a.scalar.core.mem=st.scalar.core.mem := by
    simp [a,linearRun,exteriorPotentialPrepInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,exteriorPotentialPrepInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  obtain ⟨out,eb,bR,bI,bQ,bW,bO,bH⟩ := vertex_real_add_from_exec m g ω a aH width v.val 0 40
    ((ea.pointer_frame 0 (by decide)).trans h0) ((ea.pointer_frame 40 (by decide)).trans hv) a41 a44
    ((ea.real_register_frame 31 (by decide)).trans hOne)
  have ex : MachineEval m g ω exteriorPotentialAddCode st (4*width+12) out := by
    have er := MachineEval.seq ea eb
    convert er using 1 <;> (first | rfl | change 4*width+12=2+(4*width+10); omega)
  refine ⟨out,ex,?_,bI.trans aI,ex.query_frame (by decide),
    ex.unit_work exteriorPotentialAddCode_wellFormed (by decide) hh,bO.trans aO,bH⟩
  rw [bR,aR,ea.real_register_frame 40 (by decide)]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.GraphCacheOwnedBase
set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section
set_option maxHeartbeats 2500000 in
lemma cache_row_owned_base_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width : ℕ) (v : Fin n)
    (stored : Finset (Fin n)) (free : ℤ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 50=(width : ℤ)) (hf : st.scalar.core.ptrs 20=free)
    (hcache : GraphCache g st.scalar.integerMemory width stored free)
    :
    let endFree := if v ∈ stored then free else free+((g.neighbors v).length : ℤ)
    ∃ steps out, MachineEval m g ω cacheRowCode st steps out ∧ steps ≤ 20*width+6*(g.neighbors v).length+64 ∧
      out.scalar.core.ptrs 60=((g.neighbors v).length : ℤ) ∧
      out.scalar.core.ptrs 61=out.scalar.integerMemory (vertexRecordAddress width v.val 1) ∧
      out.scalar.core.ptrs 20=endFree ∧
      GraphCache g out.scalar.integerMemory width (insert v stored) endFree ∧
      (∀ z, z ∉ cacheWriteCells width v.val free (g.neighbors v).length → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries+(if v ∈ stored then 0 else (g.neighbors v).length+1) ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      out.scalar.integerMemory (vertexRecordAddress width v.val 1)=
        (if v ∈ stored then st.scalar.integerMemory (vertexRecordAddress width v.val 1) else free) := by
  dsimp only
  obtain ⟨mid,ec,hflag,h41,hI,hR,hQ,hW,hO,hH⟩ := cache_check_exec m g ω st hh width v.val hz hv hw
  have h0 := (ec.pointer_frame 0 (by decide)).trans hz
  have h40 := (ec.pointer_frame 40 (by decide)).trans hv
  have h20 := (ec.pointer_frame 20 (by decide)).trans hf
  have hmidCache : GraphCache g mid.scalar.integerMemory width stored free := by rw [hI]; exact hcache
  by_cases hs : v ∈ stored
  · simp only [if_pos hs,add_zero,Finset.insert_eq_of_mem hs]
    rw [hcache.flag v,if_pos hs] at hflag
    obtain ⟨read,er,hr60,hr61,hrI,hrR,hrQ,hrW,hrO,hrH⟩ := cache_read_exec m g ω (payUnit mid) hH width v.val h0 h40 h41
    have eb : MachineEval m g ω (.branchPointer 51 0 cacheFreshCode cacheReadCode) mid (1+(8*width+18)+1) (payUnit read) :=
      MachineEval.pointerGt (r:=51) (s:=0) (a:=cacheFreshCode) hH (by rw [hflag,h0]; norm_num) er
    have e := MachineEval.seq ec eb
    have hrI' : read.scalar.integerMemory=st.scalar.integerMemory := hrI.trans hI
    refine ⟨_,payUnit read,e,by omega,?_,?_,?_,?_,?_,hrR.trans hR,?_,?_,hrO.trans hO,hrH,?_⟩
    · change read.scalar.core.ptrs 60=((g.neighbors v).length : ℤ)
      rw [hr60]
      change mid.scalar.integerMemory (vertexRecordAddress width v.val 0)= _
      rw [hI]
      exact hcache.degree v hs
    · change read.scalar.core.ptrs 61=read.scalar.integerMemory (vertexRecordAddress width v.val 1)
      rw [hr61,hrI]
    · exact (er.pointer_frame 20 (by decide)).trans h20
    · change GraphCache g read.scalar.integerMemory width stored free
      rw [hrI']; exact hcache
    · intro z hz'; exact congrFun hrI' z
    · change read.scalar.queries=st.scalar.queries
      exact hrQ.trans hQ
    · rw [payUnit_work,hrW,payUnit_work,hW]
      push_cast
      ring
    · change read.scalar.integerMemory (vertexRecordAddress width v.val 1)=st.scalar.integerMemory (vertexRecordAddress width v.val 1)
      rw [hrI']
  · simp only [if_neg hs]
    rw [hcache.flag v,if_neg hs] at hflag
    obtain ⟨out,ef,hf60,hf61,hf20,hfCache,hfBase,hfFrame,hfR,hfQ,hfW,hfO,hfH⟩ :=
      cache_fresh_owned_exec m g ω (payUnit mid) hH width v stored free h0 h40 h41 h20 hmidCache
    have eb : MachineEval m g ω (.branchPointer 51 0 cacheFreshCode cacheReadCode) mid
        (1+(6*(g.neighbors v).length+12*width+33)) out :=
      MachineEval.pointerLe (r:=51) (s:=0) (b:=cacheReadCode) hH (by rw [hflag,h0]) ef
    have e := MachineEval.seq ec eb
    refine ⟨_,out,e,by omega,hf60,hf61.trans hfBase.symm,hf20,hfCache,?_,hfR.trans hR,?_,?_,hfO.trans hO,hfH,hfBase⟩
    · intro z hz'
      exact (hfFrame z hz').trans (congrFun hI z)
    · change out.scalar.queries=st.scalar.queries+((g.neighbors v).length+1)
      rw [hfQ]
      change mid.scalar.queries+(g.neighbors v).length+1= _
      rw [hQ]
      omega
    · rw [hfW,payUnit_work,hW]
      push_cast
      ring
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorNumericPrefixExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 15000000 in
lemma exterior_numeric_prefix_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length t : ℕ) (v : Fin n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (ht : t ≤ logical.top) (hvDomain : v ∈ parentDomain logical t)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hSelected : st.scalar.core.ptrs 112=(t : ℤ)) (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) :
    let width := 16*(ell+3)
    let d := LocalPush.deg g.graph v
    let q := (logical.frames t).q
    let h := min ((logical.frames t).residual v/(5*d)) (3*q/8-relative logical t v)
    let endFree := if v ∈ logical.stored then st.scalar.core.ptrs 20 else st.scalar.core.ptrs 20+((g.neighbors v).length : ℤ)
    ∃ steps out, ∃ J : ℤ → ℤ, MachineEval m g ω exteriorNumericPrefixCode st steps out ∧
      steps ≤ 36*width+161+(logical.top+1)*(4*width+60)+
        (g.neighbors v).length*((logical.top+1)*(8*width+39)+4*width+31) ∧
      GraphCache g J width (insert v logical.stored) endFree ∧
      (∀ z, z ∉ cacheWriteCells width v.val (st.scalar.core.ptrs 20) (g.neighbors v).length → J z=st.scalar.integerMemory z) ∧
      (out.scalar.integerMemory,out.scalar.core.mem)=
        levelPayloadFold (storedNeighborMemoryUpdate g v logical ell ((1-α)*h)) 0 (g.neighbors v).length
          (J,levelRealMemoryFold (exteriorSelfBudgetMemoryUpdate J width v.val t (d*h) ((1-α)*d*h)) 0 (logical.top+1)
            (Function.update st.scalar.core.mem (vertexRecordAddress width v.val 0) (st.scalar.core.mem (vertexRecordAddress width v.val 0)+h))) ∧
      GraphCache g out.scalar.integerMemory width (insert v logical.stored) endFree ∧
      out.scalar.core.ptrs 20=endFree ∧ out.scalar.core.ptrs 40=(v.val : ℤ) ∧ out.scalar.core.ptrs 100=(logical.top : ℤ) ∧
      out.scalar.core.ptrs 120=((g.neighbors v).length : ℤ) ∧ out.scalar.core.ptrs 121=J (vertexRecordAddress width v.val 1) ∧
      out.scalar.core.ptrs 108=(logical.top : ℤ) ∧ out.scalar.core.ptrs 112=(t : ℤ) ∧ out.scalar.core.ptrs 116=(v.val : ℤ) ∧
      out.scalar.core.ptrs 114=(if relative logical t v+h=3*q/8 then 1 else 0) ∧
      out.scalar.core.regs 40=h ∧ out.scalar.core.regs 41=(1-α)*h ∧ out.scalar.core.regs 42=d*h ∧
      out.scalar.core.regs 43=q*d/2 ∧ out.scalar.core.regs 46=(1-α)*d*h ∧
      out.scalar.queries=st.scalar.queries+1+(if v ∈ logical.stored then 0 else (g.neighbors v).length+1)+(g.neighbors v).length ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      J (vertexRecordAddress width v.val 1)=(if v ∈ logical.stored then st.scalar.integerMemory (vertexRecordAddress width v.val 1) else st.scalar.core.ptrs 20) := by
  intro width d q h endFree
  obtain ⟨u,a,ea,hu,a40R,a41R,a42R,a43R,a44R,a45R,a46R,a114,a108,a116,a100,aI,aR,aQ,aW,aO,aH⟩ :=
    exterior_scalar_exec m g ω logical s α ε ell length t v st hh pm ht hvDomain hSelected hv
  have aCache : GraphCache g a.scalar.integerMemory width logical.stored (st.scalar.core.ptrs 20) := by rw [aI]; exact pm.graphCache
  obtain ⟨k,b,eb,hk,b60,b61,b20,bCache,bFrame,bR,bQ,bW,bO,bH,bBase⟩ := cache_row_owned_base_exec m g ω a aH width v logical.stored
    (st.scalar.core.ptrs 20) ((ea.pointer_frame 0 (by decide)).trans pm.zero)
    ((ea.pointer_frame 40 (by decide)).trans hv) ((ea.pointer_frame 50 (by decide)).trans pm.width)
    (ea.pointer_frame 20 (by decide)) aCache
  have eCache := MachineEval.seq ea eb
  obtain ⟨c,ec,cR,cI,cQ,cW,cO,cH⟩ := exterior_potential_add_exec m g ω b bH width v
    ((eCache.pointer_frame 0 (by decide)).trans pm.zero) ((eCache.pointer_frame 40 (by decide)).trans hv)
    ((eCache.pointer_frame 50 (by decide)).trans pm.width) ((eCache.real_register_frame 31 (by decide)).trans pm.one)
  have ePotential := MachineEval.seq ea (MachineEval.seq eb ec)
  have cR' : c.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width v.val 0)
      (st.scalar.core.mem (vertexRecordAddress width v.val 0)+h) := by
    rw [cR,bR,aR,eb.real_register_frame 40 (by decide),a40R]
  obtain ⟨r,ds,ed,hr,d100,dI,dR,dCtx,dQ,dW,dO,dH⟩ := exterior_self_budget_loop_exec m g ω width logical.top t v (d*h) ((1-α)*d*h)
    c cH ((ePotential.pointer_frame 0 (by decide)).trans pm.zero) ((ePotential.pointer_frame 50 (by decide)).trans pm.width)
    (((MachineEval.seq eb ec).pointer_frame 108 (by decide)).trans a108)
    ((ePotential.pointer_frame 40 (by decide)).trans hv) ((ePotential.pointer_frame 112 (by decide)).trans hSelected)
    ((ePotential.real_register_frame 31 (by decide)).trans pm.one)
    (((MachineEval.seq eb ec).real_register_frame 42 (by decide)).trans a42R)
    (((MachineEval.seq eb ec).real_register_frame 46 (by decide)).trans a46R)
  have eSelf := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  have dI' : ds.scalar.integerMemory=b.scalar.integerMemory := dI.trans cI
  have dRecords : ∀ i ≤ logical.top, ∀ w ∈ parentDomain logical i,
      ds.scalar.integerMemory (vertexRecordAddress width w.val (16*(i+1)+2))=(if w ∈ (logical.frames i).active then 1 else 0) := by
    intro i hi w hw
    rw [dI',bFrame _ (cache_write_cells_negative_field width v.val w.val (16*(i+1)+2) _ _
      (by have := pm.allocator; omega) (by dsimp [width]; omega) (by dsimp [width]; omega) (by omega)),aI]
    exact (pm.frames i hi).activeFlags w hw
  have dCache : GraphCache g ds.scalar.integerMemory width (insert v logical.stored) endFree := by
    rw [dI']
    exact bCache
  have dBase : 128 ≤ b.scalar.integerMemory (vertexRecordAddress width v.val 1) := bCache.basePositive v (by simp)
  obtain ⟨z,out,ee,hz,e40,e100,eData,eCtx,eQ,eW,eO,eH⟩ := stored_neighbor_loop_exec m g ω v logical ell ((1-α)*h)
    (b.scalar.integerMemory (vertexRecordAddress width v.val 1)) dBase hDepth hSubset ds dH
    ((eSelf.pointer_frame 0 (by decide)).trans pm.zero) ((eSelf.pointer_frame 50 (by decide)).trans pm.width)
    (((MachineEval.seq eb (MachineEval.seq ec ed)).pointer_frame 108 (by decide)).trans a108)
    (((MachineEval.seq eb (MachineEval.seq ec ed)).pointer_frame 116 (by decide)).trans a116)
    (((MachineEval.seq ec ed).pointer_frame 60 (by decide)).trans b60)
    (((MachineEval.seq ec ed).pointer_frame 61 (by decide)).trans b61)
    ((eSelf.real_register_frame 31 (by decide)).trans pm.one)
    (((MachineEval.seq eb (MachineEval.seq ec ed)).real_register_frame 41 (by decide)).trans a41R)
    (by
      intro i hi
      rw [dI']
      simpa only [storedNeighborVertex_eq g v i hi] using bCache.adjacency v (by simp) i hi hi) dRecords
  have ex : MachineEval m g ω exteriorNumericPrefixCode st (u+(k+((4*width+12)+(r+z)))) out :=
    MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed ee)))
  have eData' : (out.scalar.integerMemory,out.scalar.core.mem)=
      levelPayloadFold (storedNeighborMemoryUpdate g v logical ell ((1-α)*h)) 0 (g.neighbors v).length
        (b.scalar.integerMemory,levelRealMemoryFold (exteriorSelfBudgetMemoryUpdate b.scalar.integerMemory width v.val t (d*h) ((1-α)*d*h))
          0 (logical.top+1) (Function.update st.scalar.core.mem (vertexRecordAddress width v.val 0)
            (st.scalar.core.mem (vertexRecordAddress width v.val 0)+h))) := by
    rw [eData,dI',dR,cI,cR']
  have outCache : GraphCache g out.scalar.integerMemory width (insert v logical.stored) endFree := by
    have hc := stored_neighbor_fold_graph_cache g v logical ell ((1-α)*h) (insert v logical.stored) endFree
      (b.scalar.integerMemory,ds.scalar.core.mem) bCache
    have hi := congrArg Prod.fst eData
    change out.scalar.integerMemory=_ at hi
    rw [dI'] at hi
    rw [←hi] at hc
    exact hc
  have afterScalar := MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed ee))
  refine ⟨_,out,b.scalar.integerMemory,ex,?_,bCache,?_,eData',outCache,?_,e40,e100,eCtx.degree,eCtx.basePtr,
    (afterScalar.pointer_frame 108 (by decide)).trans a108,(ex.pointer_frame 112 (by decide)).trans hSelected,
    (afterScalar.pointer_frame 116 (by decide)).trans a116,(afterScalar.pointer_frame 114 (by decide)).trans a114,
    (afterScalar.real_register_frame 40 (by decide)).trans a40R,(afterScalar.real_register_frame 41 (by decide)).trans a41R,
    (afterScalar.real_register_frame 42 (by decide)).trans a42R,(afterScalar.real_register_frame 43 (by decide)).trans a43R,
    (afterScalar.real_register_frame 46 (by decide)).trans a46R,?_,ex.unit_work exteriorNumericPrefixCode_wellFormed (by decide) hh,
    eO.trans (dO.trans (cO.trans (bO.trans aO))),eH,?_⟩
  · have hRing : 6*(g.neighbors v).length+(g.neighbors v).length*((logical.top+1)*(8*width+39)+4*width+25)=
        (g.neighbors v).length*((logical.top+1)*(8*width+39)+4*width+31) := by ring
    rw [←hRing]
    change u ≤ 12*width+73 at hu
    change k ≤ 20*width+6*(g.neighbors v).length+64 at hk
    change r ≤ (logical.top+1)*(4*width+60)+5 at hr
    change z ≤ (g.neighbors v).length*((logical.top+1)*(8*width+39)+4*width+25)+7 at hz
    omega
  · intro p hp
    exact (bFrame p hp).trans (congrFun aI p)
  · exact ((MachineEval.seq ec (MachineEval.seq ed ee)).pointer_frame 20 (by decide)).trans b20
  · rw [eQ,dQ,cQ,bQ,aQ]
  · simpa only [aI] using bBase

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution : ∀ (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length t : ℕ) (v : Fin n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (ht : t ≤ logical.top) (hvDomain : v ∈ parentDomain logical t)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hSelected : st.scalar.core.ptrs 112=(t : ℤ)) (hv : st.scalar.core.ptrs 40=(v.val : ℤ)),
let width := 16*(ell+3)
    let d := LocalPush.deg g.graph v
    let q := (logical.frames t).q
    let h := min ((logical.frames t).residual v/(5*d)) (3*q/8-relative logical t v)
    let endFree := if v ∈ logical.stored then st.scalar.core.ptrs 20 else st.scalar.core.ptrs 20+((g.neighbors v).length : ℤ)
    ∃ steps out, ∃ J : ℤ → ℤ, MachineEval m g ω exteriorNumericPrefixCode st steps out ∧
      steps ≤ 36*width+161+(logical.top+1)*(4*width+60)+
        (g.neighbors v).length*((logical.top+1)*(8*width+39)+4*width+31) ∧
      GraphCache g J width (insert v logical.stored) endFree ∧
      (∀ z, z ∉ cacheWriteCells width v.val (st.scalar.core.ptrs 20) (g.neighbors v).length → J z=st.scalar.integerMemory z) ∧
      (out.scalar.integerMemory,out.scalar.core.mem)=
        levelPayloadFold (storedNeighborMemoryUpdate g v logical ell ((1-α)*h)) 0 (g.neighbors v).length
          (J,levelRealMemoryFold (exteriorSelfBudgetMemoryUpdate J width v.val t (d*h) ((1-α)*d*h)) 0 (logical.top+1)
            (Function.update st.scalar.core.mem (vertexRecordAddress width v.val 0) (st.scalar.core.mem (vertexRecordAddress width v.val 0)+h))) ∧
      GraphCache g out.scalar.integerMemory width (insert v logical.stored) endFree ∧
      out.scalar.core.ptrs 20=endFree ∧ out.scalar.core.ptrs 40=(v.val : ℤ) ∧ out.scalar.core.ptrs 100=(logical.top : ℤ) ∧
      out.scalar.core.ptrs 120=((g.neighbors v).length : ℤ) ∧ out.scalar.core.ptrs 121=J (vertexRecordAddress width v.val 1) ∧
      out.scalar.core.ptrs 108=(logical.top : ℤ) ∧ out.scalar.core.ptrs 112=(t : ℤ) ∧ out.scalar.core.ptrs 116=(v.val : ℤ) ∧
      out.scalar.core.ptrs 114=(if relative logical t v+h=3*q/8 then 1 else 0) ∧
      out.scalar.core.regs 40=h ∧ out.scalar.core.regs 41=(1-α)*h ∧ out.scalar.core.regs 42=d*h ∧
      out.scalar.core.regs 43=q*d/2 ∧ out.scalar.core.regs 46=(1-α)*d*h ∧
      out.scalar.queries=st.scalar.queries+1+(if v ∈ logical.stored then 0 else (g.neighbors v).length+1)+(g.neighbors v).length ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      J (vertexRecordAddress width v.val 1)=(if v ∈ logical.stored then st.scalar.integerMemory (vertexRecordAddress width v.val 1) else st.scalar.core.ptrs 20) := by
  exact @NearlyOptimalPPR.Computation.exterior_numeric_prefix_exec
