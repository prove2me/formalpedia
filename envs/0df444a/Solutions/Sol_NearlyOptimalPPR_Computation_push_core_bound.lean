-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.push_core_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:31:13.63717+00:00
-- url     : https://prove2.me/submissions/7185dd86-92fe-4c55-a5c7-615399b513ac

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

lemma nodeCells_mem_iff (p a : ℤ) : a ∈ nodeCells p ↔ p ≤ a ∧ a ≤ p+2 := by
  simp only [nodeCells,Finset.mem_insert,Finset.mem_singleton]
  omega

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

lemma vertexFieldWriteCode_queryReadOnly (field source : ℕ) :
    (vertexFieldWriteCode field source).allAtoms queryReadOnly := by
  simp [vertexFieldWriteCode,fieldWritePrepRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    vertexIntegerStoreCode,MachineCode.allAtoms,queryReadOnly,vertexAddressCode_queryReadOnly]

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

-- Proof module: Solutions.ExteriorEligibility

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

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

end
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

lemma KeyListRep.zero_iff {I : ℤ → ℤ} {head : ℤ} {keys : List ℕ} {F : Finset ℤ}
    (h : KeyListRep I head keys F) : head=0 ↔ keys=[] := by
  cases keys with
  | nil => simp [h.nil.1]
  | cons a keys =>
    obtain ⟨next,S,hpos,_⟩ := h.cons_view
    constructor
    · intro he; omega
    · intro he; cases he

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

-- Proof module: Solutions.FIFORepresentation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section


inductive FIFORep (I : ℤ → ℤ) : ℤ → ℤ → List ℕ → Finset ℤ → Prop where
  | nil : FIFORep I 0 0 [] ∅
  | one (p : ℤ) (key : ℕ) (hp : 2 ≤ p) (hk : I p=(key : ℤ)) (hc : I (p+1)=0) (hn : I (p+2)=0) :
      FIFORep I p p [key] (nodeCells p)
  | cons (p next tail : ℤ) (key first : ℕ) (keys : List ℕ) (S : Finset ℤ)
      (hp : 2 ≤ p) (hk : I p=(key : ℤ)) (hc : I (p+1)=0) (hn : I (p+2)=next)
      (rest : FIFORep I next tail (first::keys) S) (sep : Disjoint (nodeCells p) S) :
      FIFORep I p tail (key::first::keys) (nodeCells p ∪ S)

lemma FIFORep.to_list {I : ℤ → ℤ} {head tail : ℤ} {keys : List ℕ} {F : Finset ℤ}
    (h : FIFORep I head tail keys F) : KeyListRep I head keys F := by
  induction h with
  | nil => exact ForestRep.nil
  | one p key hp hk hc hn =>
    simpa [KeyListRep,keyListForest] using ForestRep.node p key 0 0 .nil .nil ∅ ∅ hp hk hc hn
      ForestRep.nil ForestRep.nil (by simp) (by simp) (by simp)
  | cons p next tail key first keys S hp hk hc hn rest sep ih =>
    simpa [KeyListRep,keyListForest] using ForestRep.node p key 0 next .nil (keyListForest (first::keys)) ∅ S
      hp hk hc hn ForestRep.nil ih (by simp) sep (by simp)

lemma FIFORep.frame {I J : ℤ → ℤ} {head tail : ℤ} {keys : List ℕ} {F : Finset ℤ}
    (h : FIFORep I head tail keys F) (he : ∀ z ∈ F, J z=I z) : FIFORep J head tail keys F := by
  induction h with
  | nil => exact FIFORep.nil
  | one p key hp hk hc hn =>
    apply FIFORep.one p key hp
    · rw [he p (by simp [nodeCells])]; exact hk
    · rw [he (p+1) (by simp [nodeCells])]; exact hc
    · rw [he (p+2) (by simp [nodeCells])]; exact hn
  | cons p next tail key first keys S hp hk hc hn rest sep ih =>
    apply FIFORep.cons p next tail key first keys S hp
    · rw [he p (by simp [nodeCells])]; exact hk
    · rw [he (p+1) (by simp [nodeCells])]; exact hc
    · rw [he (p+2) (by simp [nodeCells])]; exact hn
    · exact ih (fun z hz => he z (Finset.mem_union_right _ hz))
    · exact sep

lemma FIFORep.tail_cells {I : ℤ → ℤ} {head tail : ℤ} {keys : List ℕ} {F : Finset ℤ}
    (h : FIFORep I head tail keys F) (hn : keys ≠ []) : nodeCells tail ⊆ F := by
  induction h with
  | nil => exact False.elim (hn rfl)
  | one => exact Finset.Subset.refl _
  | cons p next tail key first keys S hp hk hc hnext rest sep ih =>
    exact (ih (by simp)).trans Finset.subset_union_right

lemma FIFORep.nil_view {I : ℤ → ℤ} {head tail : ℤ} {F : Finset ℤ} (h : FIFORep I head tail [] F) :
    head=0 ∧ tail=0 ∧ F=∅ := by cases h; exact ⟨rfl,rfl,rfl⟩

lemma FIFORep.head_positive {I : ℤ → ℤ} {head tail : ℤ} {a : ℕ} {keys : List ℕ} {F : Finset ℤ}
    (h : FIFORep I head tail (a::keys) F) : 2 ≤ head := by cases h <;> assumption

lemma FIFORep.pop_view {I : ℤ → ℤ} {head tail : ℤ} {a : ℕ} {keys : List ℕ} {F : Finset ℤ}
    (h : FIFORep I head tail (a::keys) F) :
    ∃ next tail' S, I head=(a : ℤ) ∧ I (head+2)=next ∧ FIFORep I next tail' keys S ∧
      tail'=(if keys=[] then 0 else tail) ∧ S ⊆ F := by
  cases h with
  | one p key hp hk hc hn => exact ⟨0,0,∅,hk,hn,FIFORep.nil,by simp,by simp⟩
  | cons p next tail key first keys S hp hk hc hn rest sep =>
    exact ⟨next,tail,S,hk,hn,rest,by simp,Finset.subset_union_right⟩

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FIFOAppendMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def fifoAppendMemory (I : ℤ → ℤ) (free head tail : ℤ) (key : ℕ) : ℤ → ℤ :=
  if head=0 then nodeAllocMemory I free key else Function.update (nodeAllocMemory I free key) (tail+2) free

lemma fifo_node_rep (I : ℤ → ℤ) (free : ℤ) (key : ℕ) (hf : 2 ≤ free) :
    FIFORep (nodeAllocMemory I free key) free free [key] (nodeCells free) := by
  apply FIFORep.one free key hf
  · simp [nodeAllocMemory,Function.update_of_ne (by omega : free ≠ free+2),Function.update_of_ne (by omega : free ≠ free+1)]
  · simp [nodeAllocMemory,Function.update_of_ne (by omega : free+1 ≠ free+2)]
  · simp [nodeAllocMemory]

lemma node_alloc_below (I : ℤ → ℤ) (free : ℤ) (key : ℕ) (z : ℤ) (hz : z < free) :
    nodeAllocMemory I free key z=I z := by
  apply node_alloc_frame
  intro hm
  have hb := (nodeCells_mem_iff free z).mp hm
  omega

set_option maxHeartbeats 2400000 in
lemma fifo_append_rep (I : ℤ → ℤ) (free : ℤ) (key : ℕ) (hf : 2 ≤ free)
    (head tail : ℤ) (keys : List ℕ) (F : Finset ℤ) (h : FIFORep I head tail keys F)
    (hbelow : ∀ z ∈ F, z < free) :
    FIFORep (fifoAppendMemory I free head tail key) (if head=0 then free else head) free (keys++[key]) (F ∪ nodeCells free) := by
  induction h with
  | nil => simpa [fifoAppendMemory] using fifo_node_rep I free key hf
  | one p old hp hk hc hn =>
    have hp0 : p ≠ 0 := by omega
    let M := fifoAppendMemory I free p p key
    have hpBelow : p+2 < free := hbelow _ (by simp [nodeCells])
    have hNew : FIFORep M free free [key] (nodeCells free) := by
      apply (fifo_node_rep I free key hf).frame
      intro z hz
      have hb := (nodeCells_mem_iff free z).mp hz
      simp only [M,fifoAppendMemory,if_neg hp0,Function.update_of_ne (by omega : z ≠ p+2)]
    have hKey : M p=(old : ℤ) := by
      simp only [M,fifoAppendMemory,if_neg hp0,Function.update_of_ne (by omega : p ≠ p+2)]
      rw [node_alloc_below I free key p (by omega)]
      exact hk
    have hChild : M (p+1)=0 := by
      simp only [M,fifoAppendMemory,if_neg hp0,Function.update_of_ne (by omega : p+1 ≠ p+2)]
      rw [node_alloc_below I free key (p+1) (by omega)]
      exact hc
    have hNext : M (p+2)=free := by simp [M,fifoAppendMemory,hp0]
    have hSep : Disjoint (nodeCells p) (nodeCells free) := by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      have ho := hbelow z hz
      have hn' := (nodeCells_mem_iff free z).mp hz'
      omega
    have hr := FIFORep.cons p free free old key [] (nodeCells free) hp hKey hChild hNext hNew hSep
    simpa only [if_neg hp0,List.singleton_append] using hr
  | cons p next tail old first keys S hp hk hc hn rest sep ih =>
    have hp0 : p ≠ 0 := by omega
    have hn0 : next ≠ 0 := by have hn' := rest.head_positive; omega
    let M := fifoAppendMemory I free p tail key
    have hTailCell : tail+2 ∈ S := rest.tail_cells (by simp) (by simp [nodeCells])
    have hPrefix (z : ℤ) (hz : z ∈ nodeCells p) : M z=I z := by
      have hzBelow := hbelow z (Finset.mem_union_left _ hz)
      have hzNe : z ≠ tail+2 := by
        intro he
        rw [he] at hz
        exact Finset.disjoint_left.mp sep hz hTailCell
      simp only [M,fifoAppendMemory,if_neg hp0,Function.update_of_ne hzNe]
      exact node_alloc_below I free key z hzBelow
    have hRest : FIFORep M next free ((first::keys)++[key]) (S ∪ nodeCells free) := by
      have hh := ih (fun z hz => hbelow z (Finset.mem_union_right _ hz))
      simpa only [M,fifoAppendMemory,if_neg hp0,if_neg hn0] using hh
    have hNewSep : Disjoint (nodeCells p) (nodeCells free) := by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      have ho := hbelow z (Finset.mem_union_left _ hz)
      have hn' := (nodeCells_mem_iff free z).mp hz'
      omega
    have hSep : Disjoint (nodeCells p) (S ∪ nodeCells free) := Finset.disjoint_union_right.mpr ⟨sep,hNewSep⟩
    have hKey := (hPrefix p (by simp [nodeCells])).trans hk
    have hChild := (hPrefix (p+1) (by simp [nodeCells])).trans hc
    have hNext := (hPrefix (p+2) (by simp [nodeCells])).trans hn
    have hr := FIFORep.cons p next free old first (keys++[key]) (S ∪ nodeCells free) hp hKey hChild hNext hRest hSep
    simpa only [if_neg hp0,List.cons_append,Finset.union_assoc] using hr

lemma fifoAppendMemory_outside (I : ℤ → ℤ) (free head tail z : ℤ) (key : ℕ)
    (hz : z ∉ nodeCells free) (ht : z ≠ tail+2) : fifoAppendMemory I free head tail key z=I z := by
  unfold fifoAppendMemory
  split_ifs
  · exact node_alloc_frame _ _ _ _ hz
  · rw [Function.update_of_ne ht]
    exact node_alloc_frame _ _ _ _ hz

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FIFOTailLink

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 1400000 in
lemma fifo_tail_link_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (tail fresh : ℤ)
    (ht : st.scalar.core.ptrs 91=tail) (hf : st.scalar.core.ptrs 5=fresh) :
    ∃ out, MachineEval m g ω fifoTailLinkCode st 4 out ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (tail+2) fresh ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+4 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω fifoTailLinkInstructions
    (by simp [fifoTailLinkInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,fifoTailLinkInstructions,atomState,machineStep,pcSet,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,ht,hf,Int.add_assoc]

set_option maxHeartbeats 1200000 in
lemma fifo_append_branch_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (head tail fresh : ℤ)
    (hz : st.scalar.core.ptrs 0=0) (hhead : st.scalar.core.ptrs 90=head)
    (ht : st.scalar.core.ptrs 91=tail) (hf : st.scalar.core.ptrs 5=fresh) (hclass : head=0 ∨ 2 ≤ head) :
    ∃ steps out, MachineEval m g ω fifoAppendBranchCode st steps out ∧ steps ≤ 6 ∧
      out.scalar.core.ptrs 90=(if head=0 then fresh else head) ∧
      out.scalar.integerMemory=(if head=0 then st.scalar.integerMemory else Function.update st.scalar.integerMemory (tail+2) fresh) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  by_cases he : head=0
  · let out := payUnit (pointerWrite (payUnit st) 90 fresh)
    have ec : MachineEval m g ω (coreCode (.pcopy 90 5)) (payUnit st) 1 out := by
      simpa only [out,coreCode,payUnit_ptrs,hf] using pcopy_eval m g ω (payUnit st) 90 5 hh
    have ex : MachineEval m g ω fifoAppendBranchCode st 2 out := MachineEval.pointerLe hh (by rw [hhead,hz,he]) ec
    refine ⟨2,out,ex,by omega,?_,by simp only [if_pos he]; rfl,rfl,?_,rfl,hh⟩
    · simp [out,payUnit,pcSet,pointerWrite,he]
    · simp [out,payUnit,pcSet,pointerWrite]
      ring
  · have hp : 2 ≤ head := hclass.resolve_left he
    obtain ⟨mid,em,hmI,hmR,hmW,hmO,hmH⟩ := fifo_tail_link_exec m g ω (payUnit st) hh tail fresh ht hf
    have ex : MachineEval m g ω fifoAppendBranchCode st 6 (payUnit mid) := MachineEval.pointerGt hh (by rw [hhead,hz]; omega) em
    refine ⟨6,payUnit mid,ex,by omega,?_,by simpa only [payUnit,pcSet,if_neg he] using hmI,hmR,?_,hmO,hmH⟩
    · simpa only [payUnit_ptrs,if_neg he] using (em.pointer_frame 90 (by decide)).trans hhead
    · change mid.work+1= _
      rw [hmW,payUnit_work]
      norm_num
      ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FIFOAppendExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma fifoAppendMemory_owned_frame (I : ℤ → ℤ) (free head tail z : ℤ) (key : ℕ) (keys : List ℕ) (F : Finset ℤ)
    (h : FIFORep I head tail keys F) (hz : z ∉ F ∪ nodeCells free) : fifoAppendMemory I free head tail key z=I z := by
  have hn : z ∉ nodeCells free := fun hm => hz (Finset.mem_union_right _ hm)
  by_cases he : head=0
  · simpa only [fifoAppendMemory,if_pos he] using node_alloc_frame I free key z hn
  · have hkeys : keys ≠ [] := fun hk => he (h.to_list.zero_iff.mpr hk)
    apply fifoAppendMemory_outside I free head tail z key hn
    intro heq
    have ht := h.tail_cells hkeys (by simp [nodeCells] : tail+2 ∈ nodeCells tail)
    apply hz
    apply Finset.mem_union_left
    simpa only [heq] using ht

set_option maxHeartbeats 2200000 in
lemma fifo_append_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (free head tail : ℤ) (key : ℕ) (keys : List ℕ) (F : Finset ℤ)
    (hfree : 2 ≤ free) (hf : st.scalar.core.ptrs 20=free) (hk : st.scalar.core.ptrs 4=(key : ℤ))
    (hhead : st.scalar.core.ptrs 90=head) (htail : st.scalar.core.ptrs 91=tail)
    (h : FIFORep st.scalar.integerMemory head tail keys F) (hbelow : ∀ z ∈ F, z < free) :
    ∃ steps out, MachineEval m g ω fifoAppendCode st steps out ∧ steps ≤ 15 ∧
      out.scalar.core.ptrs 90=(if head=0 then free else head) ∧ out.scalar.core.ptrs 91=free ∧
      out.scalar.core.ptrs 20=free+3 ∧ out.scalar.core.ptrs 0=0 ∧
      FIFORep out.scalar.integerMemory (out.scalar.core.ptrs 90) free (keys++[key]) (F ∪ nodeCells free) ∧
      out.scalar.integerMemory=fifoAppendMemory st.scalar.integerMemory free head tail key ∧
      (∀ z ∈ F ∪ nodeCells free, z < free+3) ∧
      (∀ z, z ∉ F ∪ nodeCells free → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,ep,hp0,hp5,hp20,hpI,hpR,hpW,hpO⟩ := heap_node_alloc_exec m g ω st hh
  rw [hf] at hp5 hp20 hpI
  rw [hk] at hpI
  have hpH := (ep.halted heapNodeAllocCode_wellFormed).trans hh
  have hp90 := (ep.pointer_frame 90 (by decide)).trans hhead
  have hp91 := (ep.pointer_frame 91 (by decide)).trans htail
  have hclass : head=0 ∨ 2 ≤ head := by
    cases keys with
    | nil => exact Or.inl h.nil_view.1
    | cons a keys => exact Or.inr h.head_positive
  obtain ⟨u,mid,eb,hu,hm90,hmI,hmR,hmW,hmO,hmH⟩ := fifo_append_branch_exec m g ω pre hpH head tail free hp0 hp90 hp91 hp5 hclass
  have hm5 := (eb.pointer_frame 5 (by decide)).trans hp5
  let out := payUnit (pointerWrite mid 91 free)
  have ef : MachineEval m g ω (coreCode (.pcopy 91 5)) mid 1 out := by
    simpa only [out,coreCode,hm5] using pcopy_eval m g ω mid 91 5 hmH
  have eRun := MachineEval.seq ep (MachineEval.seq eb ef)
  have hoI : out.scalar.integerMemory=fifoAppendMemory st.scalar.integerMemory free head tail key := by
    change mid.scalar.integerMemory= _
    rw [hmI,hpI]
    rfl
  have ho90 := (ef.pointer_frame 90 (by decide)).trans hm90
  have hoRep : FIFORep out.scalar.integerMemory (out.scalar.core.ptrs 90) free (keys++[key]) (F ∪ nodeCells free) := by
    rw [hoI,ho90]
    exact fifo_append_rep _ free key hfree head tail keys F h hbelow
  refine ⟨8+(u+1),out,eRun,by omega,ho90,by simp [out,payUnit,pcSet,pointerWrite],
    (ef.pointer_frame 20 (by decide)).trans ((eb.pointer_frame 20 (by decide)).trans hp20),
    (ef.pointer_frame 0 (by decide)).trans ((eb.pointer_frame 0 (by decide)).trans hp0),hoRep,hoI,?_,?_,
    hmR.trans hpR,eRun.query_frame (by decide),?_,hmO.trans hpO,hmH⟩
  · intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · have hb := hbelow z hz
      omega
    · have hb := (nodeCells_mem_iff free z).mp hz
      omega
  · intro z hz
    rw [hoI]
    exact fifoAppendMemory_owned_frame _ _ _ _ _ _ keys F h hz
  · change mid.work+1= _
    rw [hmW,hpW]
    push_cast
    ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FIFOPopExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 1400000 in
lemma fifo_pop_head_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (head next : ℤ) (key : ℕ)
    (hhead : st.scalar.core.ptrs 90=head) (hk : st.scalar.integerMemory head=(key : ℤ))
    (hn : st.scalar.integerMemory (head+2)=next) :
    ∃ out, MachineEval m g ω fifoPopHeadCode st 5 out ∧
      out.scalar.core.ptrs 40=(key : ℤ) ∧ out.scalar.core.ptrs 90=next ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+5 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω fifoPopHeadInstructions
    (by simp [fifoPopHeadInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,fifoPopHeadInstructions,atomState,machineStep,pcSet,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hhead,hk,hn,Int.add_assoc]

set_option maxHeartbeats 2000000 in
lemma fifo_pop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (head tail : ℤ) (key : ℕ) (keys : List ℕ) (F : Finset ℤ)
    (hz : st.scalar.core.ptrs 0=0) (hhead : st.scalar.core.ptrs 90=head) (htail : st.scalar.core.ptrs 91=tail)
    (h : FIFORep st.scalar.integerMemory head tail (key::keys) F) :
    ∃ out S, MachineEval m g ω fifoPopCode st 7 out ∧ out.scalar.core.ptrs 40=(key : ℤ) ∧
      FIFORep out.scalar.integerMemory (out.scalar.core.ptrs 90) (out.scalar.core.ptrs 91) keys S ∧ S ⊆ F ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.core.ptrs 0=0 ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+7 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨next,tail',S,hk,hn,hRest,hTail,hSub⟩ := h.pop_view
  obtain ⟨pre,ep,hp40,hp90,hpI,hpR,hpW,hpO,hpH⟩ := fifo_pop_head_exec m g ω st hh head next key hhead hk hn
  have hp0 := (ep.pointer_frame 0 (by decide)).trans hz
  have hp91 := (ep.pointer_frame 91 (by decide)).trans htail
  by_cases he : keys=[]
  · have hnext : next=0 := by rw [he] at hRest; exact hRest.nil_view.1
    have htail' : tail'=0 := by rw [he] at hRest; exact hRest.nil_view.2.1
    let out := payUnit (pointerWrite (payUnit pre) 91 0)
    have ec : MachineEval m g ω (coreCode (.pset 91 0)) (payUnit pre) 1 out := pset_eval m g ω (payUnit pre) 91 0 hpH
    have eb : MachineEval m g ω (.branchPointer 90 0 (coreCode (.pset 91 0)) .skip) pre 2 out :=
      MachineEval.pointerLe hpH (by rw [hp90,hnext,hp0]) ec
    have eRun := MachineEval.seq ep eb
    have hRep : FIFORep out.scalar.integerMemory (out.scalar.core.ptrs 90) (out.scalar.core.ptrs 91) keys S := by
      change FIFORep pre.scalar.integerMemory (pre.scalar.core.ptrs 90) 0 keys S
      rw [hpI,hp90,←htail']
      exact hRest
    refine ⟨out,S,eRun,?_,hRep,hSub,hpI,hpR,?_,eRun.query_frame (by decide),?_,hpO,hpH⟩
    · exact (eb.pointer_frame 40 (by decide)).trans hp40
    · exact (eb.pointer_frame 0 (by decide)).trans hp0
    · change pre.work+1+1= _
      rw [hpW]
      norm_num
      ring
  · have hnextPos : 2 ≤ next := by
      cases keys with
      | nil => exact False.elim (he rfl)
      | cons a keys => exact hRest.head_positive
    have eb : MachineEval m g ω (.branchPointer 90 0 (coreCode (.pset 91 0)) .skip) pre 2 (payUnit (payUnit pre)) :=
      MachineEval.pointerGt hpH (by rw [hp90,hp0]; omega) (MachineEval.skip (payUnit pre))
    have eRun := MachineEval.seq ep eb
    have hRep : FIFORep (payUnit (payUnit pre)).scalar.integerMemory ((payUnit (payUnit pre)).scalar.core.ptrs 90)
        ((payUnit (payUnit pre)).scalar.core.ptrs 91) keys S := by
      change FIFORep pre.scalar.integerMemory (pre.scalar.core.ptrs 90) (pre.scalar.core.ptrs 91) keys S
      rw [hpI,hp90,hp91]
      simpa only [hTail,if_neg he] using hRest
    refine ⟨payUnit (payUnit pre),S,eRun,hp40,hRep,hSub,hpI,hpR,hp0,eRun.query_frame (by decide),?_,hpO,hpH⟩
    change pre.work+1+1= _
    rw [hpW]
    norm_num
    ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexFIFOExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def VertexFIFORep {n : ℕ} (I : ℤ → ℤ) (head tail : ℤ) (vertices : List (Fin n)) (F : Finset ℤ) : Prop :=
  FIFORep I head tail (vertices.map Fin.val) F

lemma VertexFIFORep.frame {n : ℕ} {I J : ℤ → ℤ} {head tail : ℤ} {vertices : List (Fin n)} {F : Finset ℤ}
    (h : VertexFIFORep I head tail vertices F) (he : ∀ z ∈ F, J z=I z) : VertexFIFORep J head tail vertices F := FIFORep.frame h he

lemma VertexFIFORep.positive_cells {n : ℕ} {I : ℤ → ℤ} {head tail : ℤ} {vertices : List (Fin n)} {F : Finset ℤ}
    (h : VertexFIFORep I head tail vertices F) : ∀ z ∈ F, 2 ≤ z := ForestRep.positive_cells h.to_list

lemma VertexFIFORep.zero_iff {n : ℕ} {I : ℤ → ℤ} {head tail : ℤ} {vertices : List (Fin n)} {F : Finset ℤ}
    (h : VertexFIFORep I head tail vertices F) : head=0 ↔ vertices=[] := by
  simpa only [List.map_eq_nil_iff] using h.to_list.zero_iff

set_option maxHeartbeats 1000000 in
lemma vertex_fifo_append_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (free head tail : ℤ) (v : Fin n) (vertices : List (Fin n)) (F : Finset ℤ)
    (hfree : 2 ≤ free) (hf : st.scalar.core.ptrs 20=free) (hk : st.scalar.core.ptrs 4=(v.val : ℤ))
    (hhead : st.scalar.core.ptrs 90=head) (htail : st.scalar.core.ptrs 91=tail)
    (h : VertexFIFORep st.scalar.integerMemory head tail vertices F) (hbelow : ∀ z ∈ F, z < free) :
    ∃ steps out, MachineEval m g ω fifoAppendCode st steps out ∧ steps ≤ 15 ∧
      out.scalar.core.ptrs 90=(if head=0 then free else head) ∧ out.scalar.core.ptrs 91=free ∧
      out.scalar.core.ptrs 20=free+3 ∧ out.scalar.core.ptrs 0=0 ∧
      VertexFIFORep out.scalar.integerMemory (out.scalar.core.ptrs 90) free (vertices++[v]) (F ∪ nodeCells free) ∧
      (∀ z ∈ F ∪ nodeCells free, z < free+3) ∧
      (∀ z, z ∉ F ∪ nodeCells free → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨steps,out,ex,hs,h90,h91,h20,h0,hRep,hI,hBelow,hFrame,hR,hQ,hW,hO,hH⟩ :=
    fifo_append_exec m g ω st hh free head tail v.val (vertices.map Fin.val) F hfree hf hk hhead htail h hbelow
  refine ⟨steps,out,ex,hs,h90,h91,h20,h0,?_,hBelow,hFrame,hR,hQ,hW,hO,hH⟩
  simpa only [VertexFIFORep,List.map_append,List.map_singleton] using hRep

set_option maxHeartbeats 1000000 in
lemma vertex_fifo_pop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (head tail : ℤ) (v : Fin n) (vertices : List (Fin n)) (F : Finset ℤ)
    (hz : st.scalar.core.ptrs 0=0) (hhead : st.scalar.core.ptrs 90=head) (htail : st.scalar.core.ptrs 91=tail)
    (h : VertexFIFORep st.scalar.integerMemory head tail (v::vertices) F) :
    ∃ out S, MachineEval m g ω fifoPopCode st 7 out ∧ out.scalar.core.ptrs 40=(v.val : ℤ) ∧
      VertexFIFORep out.scalar.integerMemory (out.scalar.core.ptrs 90) (out.scalar.core.ptrs 91) vertices S ∧ S ⊆ F ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.core.ptrs 0=0 ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+7 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  exact fifo_pop_exec m g ω st hh head tail v.val (vertices.map Fin.val) F hz hhead htail h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OwnedFIFOFrames

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma VertexFIFORep.negative_write {n : ℕ} {I : ℤ → ℤ} {head tail : ℤ} {vertices : List (Fin n)} {F : Finset ℤ}
    (h : VertexFIFORep I head tail vertices F) (address value : ℤ) (ha : address < 0) :
    VertexFIFORep (Function.update I address value) head tail vertices F := by
  apply h.frame
  intro z hz
  have hp := h.positive_cells z hz
  simp only [Function.update_of_ne (by omega : z ≠ address)]

lemma VertexListRep.positive_cells {n : ℕ} {I : ℤ → ℤ} {head : ℤ} {vertices : List (Fin n)} {F : Finset ℤ}
    (h : VertexListRep I head vertices F) : ∀ z ∈ F, 2 ≤ z := ForestRep.positive_cells h

lemma VertexListRep.negative_write {n : ℕ} {I : ℤ → ℤ} {head : ℤ} {vertices : List (Fin n)} {F : Finset ℤ}
    (h : VertexListRep I head vertices F) (address value : ℤ) (ha : address < 0) :
    VertexListRep (Function.update I address value) head vertices F := by
  apply h.frame
  intro z hz
  have hp := h.positive_cells z hz
  simp only [Function.update_of_ne (by omega : z ≠ address)]

lemma owned_nodes_disjoint_fresh (F : Finset ℤ) (free : ℤ) (hf : ∀ z ∈ F, z < free) :
    Disjoint F (nodeCells free) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  have hb := hf z hz
  have hn := (nodeCells_mem_iff free z).mp hz'
  omega

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

lemma refl {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (pm : MachinePendingKeys g s α ε ell length logical st) :
    PendingIntegerFrame pm pm := ⟨le_rfl,by intros i hi z hz; exact fun _ => hz,by intros; rfl,by intros; rfl⟩

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

-- Proof module: Solutions.KeyListPrependMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section

def listPrependMemory (I : ℤ → ℤ) (free : ℤ) (key : ℕ) (head : ℤ) : ℤ → ℤ :=
  Function.update (nodeAllocMemory I free key) (free+2) head

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

set_option maxHeartbeats 1800000 in
lemma support_list_prepend_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
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
      out.work=st.work+13 ∧ out.output=st.output ∧ out.scalar.halted=false := by
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
  refine ⟨out,eRun,hout92,pre20,?_,?_,?_,hR.trans haR,?_,?_,hO.trans haO,hH⟩
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

-- Proof module: Solutions.MachineEvalDeterminism

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma MachineEval.deterministic {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {code : MachineCode} {st out out' : MachineState} {u v : ℕ}
    (ex : MachineEval m g ω code st u out) (ey : MachineEval m g ω code st v out') :
    u=v ∧ out=out' := by
  induction ex generalizing v out' with
  | skip st => cases ey; exact ⟨rfl,rfl⟩
  | atom i st h => cases ey; exact ⟨rfl,rfl⟩
  | seq ea eb iha ihb =>
    cases ey with
    | seq ea' eb' =>
      obtain ⟨rfl,rfl⟩ := iha ea'
      obtain ⟨rfl,rfl⟩ := ihb eb'
      exact ⟨rfl,rfl⟩
  | realNonpos hh hg ea ih =>
    cases ey with
    | realNonpos hh' hg' ea' => obtain ⟨rfl,rfl⟩ := ih ea'; exact ⟨rfl,rfl⟩
    | realPos hh' hg' eb' => exact False.elim (hg' hg)
  | realPos hh hg eb ih =>
    cases ey with
    | realNonpos hh' hg' ea' => exact False.elim (hg hg')
    | realPos hh' hg' eb' => obtain ⟨rfl,rfl⟩ := ih eb'; exact ⟨rfl,rfl⟩
  | pointerLe hh hg ea ih =>
    cases ey with
    | pointerLe hh' hg' ea' => obtain ⟨rfl,rfl⟩ := ih ea'; exact ⟨rfl,rfl⟩
    | pointerGt hh' hg' eb' => exact False.elim (hg' hg)
  | pointerGt hh hg eb ih =>
    cases ey with
    | pointerLe hh' hg' ea' => exact False.elim (hg hg')
    | pointerGt hh' hg' eb' => obtain ⟨rfl,rfl⟩ := ih eb'; exact ⟨rfl,rfl⟩
  | realDone hh hg =>
    cases ey with
    | realDone hh' hg' => exact ⟨rfl,rfl⟩
    | realNext hh' hg' eb' er' => exact False.elim (hg' hg)
  | realNext hh hg eb er ihb ihr =>
    cases ey with
    | realDone hh' hg' => exact False.elim (hg hg')
    | realNext hh' hg' eb' er' =>
      obtain ⟨rfl,rfl⟩ := ihb eb'
      obtain ⟨rfl,rfl⟩ := ihr er'
      exact ⟨rfl,rfl⟩
  | pointerDone hh hg =>
    cases ey with
    | pointerDone hh' hg' => exact ⟨rfl,rfl⟩
    | pointerNext hh' hg' eb' er' => exact False.elim (hg' hg)
  | pointerNext hh hg eb er ihb ihr =>
    cases ey with
    | pointerDone hh' hg' => exact False.elim (hg hg')
    | pointerNext hh' hg' eb' er' =>
      obtain ⟨rfl,rfl⟩ := ihb eb'
      obtain ⟨rfl,rfl⟩ := ihr er'
      exact ⟨rfl,rfl⟩

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

lemma push_residual_update (g : InputGraph n) (s v : Fin n) (α : ℝ)
    (z r : Fin n → ℝ) (hr : r = residual g.graph α s z)
    (hd : 0 < g.graph.degree v) :
    residual g.graph α s (Function.update z v (z v + r v / LocalPush.deg g.graph v)) =
      fun u => (if u = v then 0 else r u) +
        if u ∈ g.neighbors v then (1 - α) * (r v / LocalPush.deg g.graph v) else 0 := by
  classical
  let h := r v / LocalPush.deg g.graph v
  have hz : Function.update z v (z v + h) = z + Pi.single v h := by
    ext u
    by_cases hu : u = v <;> simp [hu, Pi.single_apply]
  change residual g.graph α s (Function.update z v (z v + h)) = _
  rw [hz]
  ext u
  have hru := congrFun hr u
  simp only [residual, Pi.sub_apply] at hru ⊢
  rw [Matrix.mulVec_add, Matrix.mulVec_single]
  change LocalPush.e s u - ((LocalPush.Lα g.graph α *ᵥ z) u +
      LocalPush.Lα g.graph α u v * h) = _
  have hd0 : LocalPush.deg g.graph v ≠ 0 := by
    unfold LocalPush.deg
    exact_mod_cast hd.ne'
  have hmuv : LocalPush.Lα g.graph α u v =
      (if u = v then LocalPush.deg g.graph v else 0) -
        (1-α) * (if g.graph.Adj u v then 1 else 0) := by
    by_cases hu : u = v <;> simp [LocalPush.Lα, LocalPush.degM, LocalPush.adjM,
      SimpleGraph.adjMatrix_apply, Matrix.diagonal_apply, hu]
  rw [hmuv]
  simp only [g.correct]
  by_cases hu : u = v
  · subst u
    simp only [ite_true, SimpleGraph.irrefl, ite_false, mul_zero, sub_zero, add_zero]
    dsimp [h]
    field_simp
    linarith [hru]
  · by_cases ha : g.graph.Adj v u
    · have ha' := ha.symm
      simp only [hu, ite_false, ha, ha', ite_true, mul_one, zero_sub]
      dsimp [h]
      linarith [hru]
    · have ha' : ¬ g.graph.Adj u v := fun h => ha h.symm
      simp only [hu, ite_false, ha, ha', mul_zero, sub_zero, zero_mul, add_zero]
      exact hru.symm

structure PushInvariant (g : InputGraph n) (s : Fin n) (α ε : ℝ) (st : PushState n) : Prop where
  z_nonneg : ∀ v, 0 ≤ st.z v
  r_nonneg : ∀ v, 0 ≤ st.r v
  residual_eq : st.r = residual g.graph α s st.z
  queue_nodup : st.queue.Nodup
  queued_eq : st.queued = st.queue.toFinset
  queue_positive : ∀ v ∈ st.queue, 0 < g.graph.degree v
  high_queued : ∀ v, ε * LocalPush.deg g.graph v < st.r v → v ∈ st.queue
  support_z : ∀ v ∉ st.support, st.z v = 0
  done_queue : st.done = true → st.queue = []
  done_output : st.done = true →
    st.output = sparseOn st.support (potentialOutput g.graph α st.z)

lemma push_init_invariant (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hε : 0 < ε) (hs : 0 < g.graph.degree s) :
    PushInvariant g s α ε (pushInit s) := by
  classical
  constructor
  · simp [pushInit]
  · intro v
    simp only [pushInit, LocalPush.e, Pi.single_apply]
    split <;> norm_num
  · simp [pushInit, residual, show (fun _ : Fin n => (0 : ℝ)) = 0 from rfl]
  · simp [pushInit]
  · simp [pushInit]
  · simpa [pushInit] using hs
  · intro v hv
    by_cases h : v = s
    · simpa [pushInit] using h
    · have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
      simp [pushInit, LocalPush.e, Pi.single_apply, h] at hv
      exact (not_lt_of_ge (mul_nonneg hε.le hd) hv).elim
  · simp [pushInit]
  · simp [pushInit]
  · simp [pushInit]

lemma push_step_invariant (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε) (st : PushState n)
    (hi : PushInvariant g s α ε st) :
    PushInvariant g s α ε (pushStep g α ε st) := by
  classical
  by_cases hd : st.done = true
  · simpa [pushStep, hd] using hi
  cases hq : st.queue with
  | nil =>
    simp only [pushStep, hd, Bool.false_eq_true, ↓reduceIte, hq]
    exact ⟨hi.z_nonneg, hi.r_nonneg, hi.residual_eq, by simp,
      by simpa [hq] using hi.queued_eq, by simp,
      by simpa [hq] using hi.high_queued, hi.support_z, by simp, by simp⟩
  | cons v rest =>
    have hn : v ∉ rest ∧ rest.Nodup := by simpa [hq] using hi.queue_nodup
    have hvpos : 0 < g.graph.degree v := hi.queue_positive v (by simp [hq])
    have hQ : st.queued.erase v = rest.toFinset := by
      simp [hi.queued_eq, hq, hn.1]
    by_cases ha : ε * LocalPush.deg g.graph v < st.r v
    · let r' : Fin n → ℝ := fun u => (if u = v then 0 else st.r u) +
        if u ∈ g.neighbors v then (1 - α) * (st.r v / LocalPush.deg g.graph v) else 0
      let added := (g.neighbors v).filter fun u =>
        u ∉ st.queued.erase v ∧ ε * LocalPush.deg g.graph u < r' u
      have hrpos : ∀ u, 0 ≤ r' u := by
        intro u
        have hr := hi.r_nonneg u
        have hrv := hi.r_nonneg v
        have hnon : 0 ≤ 1 - α := sub_nonneg.mpr hα.2.le
        have hdg : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
        dsimp [r']
        split <;> split <;> positivity
      have hrself : r' v = 0 := by simp [r', g.correct]
      have hadded : ∀ u, u ∈ added ↔
          u ∈ g.neighbors v ∧ u ∉ rest ∧ ε * LocalPush.deg g.graph u < r' u := by
        intro u
        simp [added, hQ, and_assoc]
      have hhq : ∀ u, ε * LocalPush.deg g.graph u < r' u → u ∈ rest ++ added := by
        intro u hu
        by_cases hur : u ∈ rest
        · simp [hur]
        · apply List.mem_append.mpr
          right
          apply (hadded u).mpr
          refine ⟨?_, hur, hu⟩
          by_contra hun
          by_cases huv : u = v
          · subst u
            rw [hrself] at hu
            have hdg : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
            exact (not_lt_of_ge (mul_nonneg hε.le hdg) hu)
          · have hrold : r' u = st.r u := by simp [r', huv, hun]
            have hold := hi.high_queued u (by rwa [hrold] at hu)
            simpa [hq, huv, hur] using hold
      simp only [pushStep, hd, Bool.false_eq_true, ↓reduceIte, hq, ha]
      change PushInvariant g s α ε
        ⟨Function.update st.z v (st.z v + st.r v / LocalPush.deg g.graph v),
          r', rest ++ added, st.queued.erase v ∪ added.toFinset,
          insert v st.support, _, [], false⟩
      constructor
      · intro u
        by_cases hu : u = v
        · subst u
          simp only [Function.update_self]
          exact add_nonneg (hi.z_nonneg v) (div_nonneg (hi.r_nonneg v) (by unfold LocalPush.deg; positivity))
        · simpa [hu] using hi.z_nonneg u
      · exact hrpos
      · exact (push_residual_update g s v α st.z st.r hi.residual_eq hvpos).symm
      · apply List.nodup_append.mpr
        refine ⟨hn.2, (g.nodup v).filter _, ?_⟩
        intro u hu w hw he
        subst w
        exact ((hadded u).mp hw).2.1 hu
      · simp [hQ]
      · intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hi.queue_positive u (by simp [hq, hu])
        · exact ((g.correct v u).mp ((hadded u).mp hu).1).degree_pos_right
      · exact hhq
      · intro u hu
        have hu' : u ≠ v ∧ u ∉ st.support := by simpa using hu
        simpa [hu'.1] using hi.support_z u hu'.2
      · simp
      · simp
    · simp only [pushStep, hd, Bool.false_eq_true, ↓reduceIte, hq, ha]
      constructor
      · exact hi.z_nonneg
      · exact hi.r_nonneg
      · exact hi.residual_eq
      · exact hn.2
      · exact hQ
      · intro u hu
        exact hi.queue_positive u (by simp [hq, hu])
      · intro u hu
        have hold := hi.high_queued u hu
        have huv : u ≠ v := by intro he; subst u; exact ha hu
        simpa [hq, huv] using hold
      · exact hi.support_z
      · simp
      · simp

lemma push_run_invariant (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε) (hs : 0 < g.graph.degree s) (t : ℕ) :
    PushInvariant g s α ε (pushRun g s α ε t) := by
  induction t with
  | zero => simpa [pushRun] using push_init_invariant g s α ε hε hs
  | succ t ih =>
    simpa only [pushRun, Function.iterate_succ_apply'] using
      push_step_invariant g s α ε hα hε (pushRun g s α ε t) ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexRealAdd

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

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

-- Proof module: Solutions.DegreeRecordStore

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

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

-- Proof module: Solutions.PushOutputScalar

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1400000 in
lemma push_output_scalar_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (v : Fin n) (α z : ℝ) (d : ℕ)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) (hd : st.scalar.core.ptrs 60=(d : ℤ))
    (ha : st.scalar.core.regs 30=α) (hz : st.scalar.core.regs 10=z) :
    ∃ out, MachineEval m g ω pushOutputScalarCode st 4 out ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+4 ∧
      out.output=st.output++[((v.val : ℤ),α*(d : ℝ)*z)] ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω pushOutputScalarInstructions
    (by simp [pushOutputScalarInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,ex.query_frame (by decide),hW,?_,hH⟩
  all_goals simp [linearRun,pushOutputScalarInstructions,atomState,machineStep,pcSet,hh,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hv,hd,ha,hz,mul_assoc,mul_left_comm,mul_comm]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushOutputDenotation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma output_vertex_list {n : ℕ} (vertices : List (Fin n)) (hn : vertices.Nodup) (x : Fin n → ℝ) (v : Fin n) :
    outputVector (vertices.map (fun u => ((u.val : ℤ),x u))) v=if v ∈ vertices then x v else 0 := by
  classical
  simp only [outputVector,List.map_map,Function.comp_apply]
  have he : ∀ u : Fin n, ((u.val : ℤ)=(v.val : ℤ)) ↔ u=v := by intro u; simp only [Int.natCast_inj,Fin.val_inj]
  rw [← List.sum_toFinset _ hn]
  by_cases hv : v ∈ vertices <;> simp [hv,Fin.val_inj]

lemma push_output_list_potential {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : PushState n)
    (vertices : List (Fin n)) (hn : vertices.Nodup) (hs : vertices.toFinset=logical.support)
    (hz : ∀ v ∉ logical.support, logical.z v=0) :
    outputVector (vertices.map (fun v => ((v.val : ℤ),α*((g.neighbors v).length : ℝ)*logical.z v)))=
      potentialOutput g.graph α logical.z := by
  funext v
  rw [output_vertex_list vertices hn]
  by_cases hv : v ∈ vertices
  · simp [hv,potentialOutput,LocalPush.deg,input_degree,mul_assoc]
  · have hnv : v ∉ logical.support := by rw [←hs]; simpa using hv
    simp [hv,potentialOutput,hz v hnv]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexFIFOFlags

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def VertexFIFOFlags {n : ℕ} (I : ℤ → ℤ) (width offset : ℕ) (vertices : List (Fin n)) : Prop :=
  ∀ v : Fin n, I (vertexRecordAddress width v.val offset)=if v ∈ vertices then 1 else 0

lemma VertexFIFOFlags.frame {n : ℕ} {I J : ℤ → ℤ} {width offset : ℕ} {vertices : List (Fin n)}
    (h : VertexFIFOFlags I width offset vertices)
    (he : ∀ v : Fin n, J (vertexRecordAddress width v.val offset)=I (vertexRecordAddress width v.val offset)) :
    VertexFIFOFlags J width offset vertices := fun v => (he v).trans (h v)

lemma VertexFIFOFlags.append {n : ℕ} {I : ℤ → ℤ} {width offset : ℕ} {vertices : List (Fin n)}
    (h : VertexFIFOFlags I width offset vertices) (hoff : offset < width) (v : Fin n) :
    VertexFIFOFlags (Function.update I (vertexRecordAddress width v.val offset) 1) width offset (vertices++[v]) := by
  intro u
  by_cases he : u=v
  · subst u
    simp
  · have hval : u.val ≠ v.val := by intro h; exact he (Fin.ext h)
    rw [vertex_integer_update_other_vertex I width v.val u.val offset offset 1 hoff hoff hval,h u]
    simp [he]

lemma VertexFIFOFlags.pop {n : ℕ} {I : ℤ → ℤ} {width offset : ℕ} {v : Fin n} {vertices : List (Fin n)}
    (h : VertexFIFOFlags I width offset (v::vertices)) (hoff : offset < width) (hn : (v::vertices).Nodup) :
    VertexFIFOFlags (Function.update I (vertexRecordAddress width v.val offset) 0) width offset vertices := by
  intro u
  by_cases he : u=v
  · subst u
    have hv := (List.nodup_cons.mp hn).1
    simp [hv]
  · have hval : u.val ≠ v.val := by intro h; exact he (Fin.ext h)
    rw [vertex_integer_update_other_vertex I width v.val u.val offset offset 0 hoff hoff hval,h u]
    simpa only [List.mem_cons,he,false_or]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushMachineMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section


structure PushMachineMemory {n : ℕ} (g : InputGraph n) (α ε : ℝ) (logical : PushState n) (st : MachineState) where
  zeroPointer : st.scalar.core.ptrs 0=0
  widthPointer : st.scalar.core.ptrs 41=16
  globalWidth : st.scalar.core.ptrs 50=16
  freeBound : 128 ≤ st.scalar.core.ptrs 20
  alphaRegister : st.scalar.core.regs 30=α
  oneRegister : st.scalar.core.regs 31=1
  epsilonRegister : st.scalar.core.regs 20=ε
  potential : ∀ v : Fin n, st.scalar.core.mem (vertexRecordAddress 16 v.val 0)=logical.z v
  residual : ∀ v : Fin n, st.scalar.core.mem (vertexRecordAddress 16 v.val 1)=logical.r v
  excluded : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress 16 v.val 2)=0
  queueFlags : VertexFIFOFlags st.scalar.integerMemory 16 3 logical.queue
  supportDegree : ∀ v ∈ logical.support, st.scalar.integerMemory (vertexRecordAddress 16 v.val 0)=((g.neighbors v).length : ℤ)
  queueCells : Finset ℤ
  queue : VertexFIFORep st.scalar.integerMemory (st.scalar.core.ptrs 90) (st.scalar.core.ptrs 91) logical.queue queueCells
  supportVertices : List (Fin n)
  supportCells : Finset ℤ
  support : VertexListRep st.scalar.integerMemory (st.scalar.core.ptrs 92) supportVertices supportCells
  supportNodup : supportVertices.Nodup
  supportSet : supportVertices.toFinset=logical.support
  supportFlags : VertexFIFOFlags st.scalar.integerMemory 16 4 supportVertices
  separate : Disjoint queueCells supportCells
  queueBelow : ∀ z ∈ queueCells, z < st.scalar.core.ptrs 20
  supportBelow : ∀ z ∈ supportCells, z < st.scalar.core.ptrs 20

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexFIFOEnqueue

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 2400000 in
lemma vertex_fifo_enqueue_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width : ℕ) (hw3 : 3 < width)
    (free head tail : ℤ) (v : Fin n) (vertices : List (Fin n)) (F : Finset ℤ)
    (hfree : 2 ≤ free) (hf : st.scalar.core.ptrs 20=free) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hhead : st.scalar.core.ptrs 90=head) (htail : st.scalar.core.ptrs 91=tail)
    (h : VertexFIFORep st.scalar.integerMemory head tail vertices F) (hbelow : ∀ z ∈ F, z < free)
    (hFlags : VertexFIFOFlags st.scalar.integerMemory width 3 vertices) :
    ∃ steps out, MachineEval m g ω vertexFIFOEnqueueCode st steps out ∧ steps ≤ 4*width+26 ∧
      out.scalar.core.ptrs 90=(if head=0 then free else head) ∧ out.scalar.core.ptrs 91=free ∧
      out.scalar.core.ptrs 20=free+3 ∧ out.scalar.core.ptrs 0=0 ∧
      VertexFIFORep out.scalar.integerMemory (out.scalar.core.ptrs 90) (out.scalar.core.ptrs 91) (vertices++[v]) (F ∪ nodeCells free) ∧
      VertexFIFOFlags out.scalar.integerMemory width 3 (vertices++[v]) ∧
      (∀ z ∈ F ∪ nodeCells free, z < free+3) ∧
      (∀ other : Fin n, ∀ field < width, field ≠ 3 → out.scalar.integerMemory (vertexRecordAddress width other.val field)=st.scalar.integerMemory (vertexRecordAddress width other.val field)) ∧
      (∀ z, 0 ≤ z → z < free → z ∉ F → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let pre := payUnit (pointerWrite st 4 (v.val : ℤ))
  have ep : MachineEval m g ω (coreCode (.pcopy 4 40)) st 1 pre := by
    simpa only [pre,coreCode,hv] using pcopy_eval m g ω st 4 40 hh
  have hp4 : pre.scalar.core.ptrs 4=(v.val : ℤ) := by simp [pre,payUnit,pcSet,pointerWrite]
  have hp20 := (ep.pointer_frame 20 (by decide)).trans hf
  have hp90 := (ep.pointer_frame 90 (by decide)).trans hhead
  have hp91 := (ep.pointer_frame 91 (by decide)).trans htail
  obtain ⟨u,mid,ea,hu,hm90,hm91,hm20,hm0,hmRep,hmBelow,hmFrame,hmR,hmQ,hmW,hmO,hmH⟩ :=
    vertex_fifo_append_exec m g ω pre hh free head tail v vertices F hfree hp20 hp4 hp90 hp91 h hbelow
  have hmNeg : ∀ z, z < 0 → mid.scalar.integerMemory z=st.scalar.integerMemory z := by
    intro z hz
    apply hmFrame
    intro hmem
    rcases Finset.mem_union.mp hmem with hmem|hmem
    · have hp := h.positive_cells z hmem
      omega
    · have hp := (nodeCells_mem_iff free z).mp hmem
      omega
  have hmFlags : VertexFIFOFlags mid.scalar.integerMemory width 3 vertices :=
    hFlags.frame (fun other => hmNeg _ (vertexRecordAddress_negative _ _ _))
  let a := payUnit (pointerWrite mid 88 3)
  have eo : MachineEval m g ω (coreCode (.pset 88 3)) mid 1 a := pset_eval m g ω mid 88 3 hmH
  have a0 := (eo.pointer_frame 0 (by decide)).trans hm0
  have a40 := (eo.pointer_frame 40 (by decide)).trans ((ea.pointer_frame 40 (by decide)).trans ((ep.pointer_frame 40 (by decide)).trans hv))
  have a41 := (eo.pointer_frame 41 (by decide)).trans ((ea.pointer_frame 41 (by decide)).trans ((ep.pointer_frame 41 (by decide)).trans hw))
  have a88 : a.scalar.core.ptrs 88=(3 : ℤ) := by simp [a,payUnit,pcSet,pointerWrite]
  obtain ⟨out,es,hoI,hoR,hoRegs,hoQ,hoW,hoO,hoH⟩ := vertex_flag_set_exec m g ω a hmH width v.val 3 a0 a40 a41 a88
  have ho90 := (es.pointer_frame 90 (by decide)).trans (eo.pointer_frame 90 (by decide))
  have ho91 : out.scalar.core.ptrs 91=free := (es.pointer_frame 91 (by decide)).trans ((eo.pointer_frame 91 (by decide)).trans hm91)
  have hoRep : VertexFIFORep out.scalar.integerMemory (out.scalar.core.ptrs 90) (out.scalar.core.ptrs 91) (vertices++[v]) (F ∪ nodeCells free) := by
    rw [ho90,ho91]
    apply hmRep.frame
    intro z hz
    rw [hoI]
    change Function.update mid.scalar.integerMemory (vertexRecordAddress width v.val 3) 1 z=mid.scalar.integerMemory z
    have hp := hmRep.positive_cells z hz
    have hn := vertexRecordAddress_negative width v.val 3
    simp only [Function.update_of_ne (by omega : z ≠ vertexRecordAddress width v.val 3)]
  have hoFlags : VertexFIFOFlags out.scalar.integerMemory width 3 (vertices++[v]) := by
    rw [hoI]
    exact hmFlags.append hw3 v
  have eRun := MachineEval.seq ep (MachineEval.seq ea (MachineEval.seq eo es))
  refine ⟨1+(u+(1+(4*width+9))),out,eRun,by omega,ho90.trans hm90,ho91,
    (es.pointer_frame 20 (by decide)).trans ((eo.pointer_frame 20 (by decide)).trans hm20),
    (es.pointer_frame 0 (by decide)).trans a0,hoRep,hoFlags,hmBelow,?_,?_,hoR.trans hmR,eRun.query_frame (by decide),?_,hoO.trans hmO,hoH⟩
  · intro other field hfield hne
    rw [hoI]
    change Function.update mid.scalar.integerMemory (vertexRecordAddress width v.val 3) 1 (vertexRecordAddress width other.val field)=st.scalar.integerMemory _
    rw [vertex_integer_update_other_field _ _ _ _ _ _ _ hw3 hfield hne]
    exact hmNeg _ (vertexRecordAddress_negative _ _ _)
  · intro z hz hzF hn
    rw [hoI]
    change Function.update mid.scalar.integerMemory (vertexRecordAddress width v.val 3) 1 z=st.scalar.integerMemory z
    have haNeg := vertexRecordAddress_negative width v.val 3
    rw [Function.update_of_ne (by omega : z ≠ vertexRecordAddress width v.val 3)]
    apply hmFrame
    intro hm
    rcases Finset.mem_union.mp hm with hm|hm
    · exact hn hm
    · have hp := (nodeCells_mem_iff free z).mp hm
      omega
  · rw [hoW]
    change mid.work+1+(4*width+9 : ℕ)= _
    rw [hmW]
    change st.work+1+u+1+(4*width+9 : ℕ)= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushInitPrefixExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2400000 in
lemma push_init_prefix_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (s : Fin n) (α ε : ℝ)
    (hseed : st.scalar.integerMemory 0=(s.val : ℤ)) (ha : st.scalar.core.mem 0=α) (he : st.scalar.core.mem 1=ε) :
    ∃ out, MachineEval m g ω pushInitPrefixCode st 14 out ∧
      out.scalar.core.ptrs 0=0 ∧ out.scalar.core.ptrs 41=16 ∧ out.scalar.core.ptrs 50=16 ∧
      out.scalar.core.ptrs 20=128 ∧ out.scalar.core.ptrs 90=0 ∧ out.scalar.core.ptrs 91=0 ∧ out.scalar.core.ptrs 92=0 ∧
      out.scalar.core.ptrs 40=(s.val : ℤ) ∧ out.scalar.core.ptrs 44=1 ∧
      out.scalar.core.regs 30=α ∧ out.scalar.core.regs 20=ε ∧ out.scalar.core.regs 31=1 ∧ out.scalar.core.regs 10=1 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+14 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω pushInitInstructions
    (by simp [pushInitInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,ex.query_frame (by decide),hW,?_,hH⟩
  all_goals simp [linearRun,pushInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hseed,ha,he]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushInitExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma seed_residual_memory {n : ℕ} (R : ℤ → ℝ) (s v : Fin n)
    (hzero : ∀ z, z < 0 → R z=0) :
    Function.update R (vertexRecordAddress 16 s.val 1) 1 (vertexRecordAddress 16 v.val 1)=LocalPush.e s v := by
  by_cases he : v=s
  · subst v
    simp [LocalPush.e,Pi.single_apply]
  · have hne : vertexRecordAddress 16 v.val 1 ≠ vertexRecordAddress 16 s.val 1 := by
      intro hx
      exact he (Fin.ext (vertexRecordAddress_injective 16 v.val s.val 1 1 (by decide) (by decide) hx).1)
    rw [Function.update_of_ne hne,hzero _ (vertexRecordAddress_negative _ _ _)]
    simp [LocalPush.e,Pi.single_apply,he]

lemma seed_potential_zero {n : ℕ} (R : ℤ → ℝ) (s v : Fin n)
    (hzero : ∀ z, z < 0 → R z=0) :
    Function.update R (vertexRecordAddress 16 s.val 1) 1 (vertexRecordAddress 16 v.val 0)=0 := by
  have hne : vertexRecordAddress 16 v.val 0 ≠ vertexRecordAddress 16 s.val 1 := by
    intro hx
    have ho := (vertexRecordAddress_injective 16 v.val s.val 0 1 (by decide) (by decide) hx).2
    omega
  rw [Function.update_of_ne hne]
  exact hzero _ (vertexRecordAddress_negative _ _ _)

set_option maxHeartbeats 3000000 in
lemma push_init_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (s : Fin n) (α ε : ℝ)
    (hseed : st.scalar.integerMemory 0=(s.val : ℤ)) (ha : st.scalar.core.mem 0=α) (he : st.scalar.core.mem 1=ε)
    (hIz : ∀ z, z < 0 → st.scalar.integerMemory z=0) (hRz : ∀ z, z < 0 → st.scalar.core.mem z=0) :
    ∃ steps out, MachineEval m g ω pushInitCode st steps out ∧ steps ≤ 175 ∧
      Nonempty (PushMachineMemory g α ε (pushInit s) out) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,ep,hp0,hp41,hp50,hp20,hp90,hp91,hp92,hp40,hp44,hp30,hpε,hp31,hp10,hpI,hpR,hpQ,hpW,hpO,hpH⟩ :=
    push_init_prefix_exec m g ω st hh s α ε hseed ha he
  obtain ⟨mid,em,hmR,hmI,hmRegs,hmW,hmO,hmH⟩ := vertex_real_store_exec m g ω pre hpH 16 s.val 1 hp0 hp40 hp41 hp44
  have hmI' : mid.scalar.integerMemory=st.scalar.integerMemory := hmI.trans hpI
  have hm20 := (em.pointer_frame 20 (by decide)).trans hp20
  have hm40 := (em.pointer_frame 40 (by decide)).trans hp40
  have hm41 := (em.pointer_frame 41 (by decide)).trans hp41
  have hm90 := (em.pointer_frame 90 (by decide)).trans hp90
  have hm91 := (em.pointer_frame 91 (by decide)).trans hp91
  have hm92 := (em.pointer_frame 92 (by decide)).trans hp92
  have hmQueue : VertexFIFORep mid.scalar.integerMemory 0 0 ([] : List (Fin n)) ∅ := FIFORep.nil
  have hmFlags : VertexFIFOFlags mid.scalar.integerMemory 16 3 ([] : List (Fin n)) := by
    intro v
    rw [hmI']
    simpa only [List.not_mem_nil,if_false] using hIz _ (vertexRecordAddress_negative _ _ _)
  obtain ⟨u,out,eq,hu,h90,h91,h20,h0,hQueue,hFlags,hBelow,hFields,hPos,hR,hQ,hW,hO,hH⟩ :=
    vertex_fifo_enqueue_exec m g ω mid hmH 16 (by decide) 128 0 0 s [] ∅ (by norm_num)
      hm20 hm40 hm41 hm90 hm91 hmQueue (by simp) hmFlags
  have hRtotal : out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress 16 s.val 1) 1 := by
    rw [hR,hmR,hpR,hp10]
  have out41 := (eq.pointer_frame 41 (by decide)).trans hm41
  have out50 := (eq.pointer_frame 50 (by decide)).trans ((em.pointer_frame 50 (by decide)).trans hp50)
  have out92 := (eq.pointer_frame 92 (by decide)).trans hm92
  have out30 := (eq.real_register_frame 30 (by decide)).trans ((em.real_register_frame 30 (by decide)).trans hp30)
  have outε := (eq.real_register_frame 20 (by decide)).trans ((em.real_register_frame 20 (by decide)).trans hpε)
  have out31 := (eq.real_register_frame 31 (by decide)).trans ((em.real_register_frame 31 (by decide)).trans hp31)
  have hExcluded : ∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress 16 v.val 2)=0 := by
    intro v
    rw [hFields v 2 (by decide) (by decide),hmI']
    exact hIz _ (vertexRecordAddress_negative _ _ _)
  have hSupportFlags : VertexFIFOFlags out.scalar.integerMemory 16 4 ([] : List (Fin n)) := by
    intro v
    rw [hFields v 4 (by decide) (by decide),hmI']
    simpa only [List.not_mem_nil,if_false] using hIz _ (vertexRecordAddress_negative _ _ _)
  have hSupport : VertexListRep out.scalar.integerMemory (out.scalar.core.ptrs 92) ([] : List (Fin n)) ∅ := by
    rw [out92]
    exact ForestRep.nil
  have hMem : PushMachineMemory g α ε (pushInit s) out := {
    zeroPointer := h0
    widthPointer := out41
    globalWidth := out50
    freeBound := by rw [h20]; norm_num
    alphaRegister := out30
    oneRegister := out31
    epsilonRegister := outε
    potential := by
      intro v
      change out.scalar.core.mem _=0
      rw [hRtotal]
      exact seed_potential_zero _ s v hRz
    residual := by
      intro v
      change out.scalar.core.mem _=LocalPush.e s v
      rw [hRtotal]
      exact seed_residual_memory _ s v hRz
    excluded := hExcluded
    queueFlags := hFlags
    supportDegree := by intro v hv; simp [pushInit] at hv
    queueCells := ∅ ∪ nodeCells 128
    queue := hQueue
    supportVertices := []
    supportCells := ∅
    support := hSupport
    supportNodup := by simp
    supportSet := by simp [pushInit]
    supportFlags := hSupportFlags
    separate := by simp
    queueBelow := by
      intro z hz
      rw [h20]
      exact hBelow z hz
    supportBelow := by intro z hz; simp at hz
  }
  have eRun := MachineEval.seq ep (MachineEval.seq em eq)
  refine ⟨14+((4*16+7)+u),out,eRun,by omega,⟨hMem⟩,eRun.query_frame (by decide),?_,hO.trans (hmO.trans hpO),hH⟩
  · rw [hW,hmW,hpW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexFIFODequeue

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 1800000 in
lemma vertex_fifo_dequeue_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width : ℕ) (hw3 : 3 < width)
    (head tail : ℤ) (v : Fin n) (vertices : List (Fin n)) (F : Finset ℤ)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hhead : st.scalar.core.ptrs 90=head) (htail : st.scalar.core.ptrs 91=tail)
    (h : VertexFIFORep st.scalar.integerMemory head tail (v::vertices) F)
    (hFlags : VertexFIFOFlags st.scalar.integerMemory width 3 (v::vertices)) (hn : (v::vertices).Nodup) :
    ∃ out S, MachineEval m g ω vertexFIFODequeueCode st (4*width+17) out ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧
      VertexFIFORep out.scalar.integerMemory (out.scalar.core.ptrs 90) (out.scalar.core.ptrs 91) vertices S ∧ S ⊆ F ∧
      VertexFIFOFlags out.scalar.integerMemory width 3 vertices ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (vertexRecordAddress width v.val 3) 0 ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*width+17 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,S,ep,hp40,hpRep,hSub,hpI,hpR,hp0,hpQ,hpW,hpO,hpH⟩ := vertex_fifo_pop_exec m g ω st hh head tail v vertices F hz hhead htail h
  let mid := payUnit (pointerWrite pre 88 3)
  have eo : MachineEval m g ω (coreCode (.pset 88 3)) pre 1 mid := pset_eval m g ω pre 88 3 hpH
  have hm0 := (eo.pointer_frame 0 (by decide)).trans hp0
  have hm40 := (eo.pointer_frame 40 (by decide)).trans hp40
  have hm41 := (eo.pointer_frame 41 (by decide)).trans ((ep.pointer_frame 41 (by decide)).trans hw)
  have hm88 : mid.scalar.core.ptrs 88=(3 : ℤ) := by simp [mid,payUnit,pcSet,pointerWrite]
  obtain ⟨out,es,hoI,hoR,hoRegs,hoQ,hoW,hoO,hoH⟩ := vertex_flag_clear_exec m g ω mid hpH width v.val 3 hm0 hm40 hm41 hm88
  have hI : out.scalar.integerMemory=Function.update st.scalar.integerMemory (vertexRecordAddress width v.val 3) 0 := by
    rw [hoI]
    change Function.update pre.scalar.integerMemory _ _= _
    rw [hpI]
  have ho90 := (es.pointer_frame 90 (by decide)).trans (eo.pointer_frame 90 (by decide))
  have ho91 := (es.pointer_frame 91 (by decide)).trans (eo.pointer_frame 91 (by decide))
  have hoRep : VertexFIFORep out.scalar.integerMemory (out.scalar.core.ptrs 90) (out.scalar.core.ptrs 91) vertices S := by
    rw [ho90,ho91]
    apply hpRep.frame
    intro z hz'
    rw [hoI]
    change Function.update pre.scalar.integerMemory (vertexRecordAddress width v.val 3) 0 z=pre.scalar.integerMemory z
    have hp := hpRep.positive_cells z hz'
    have hn' := vertexRecordAddress_negative width v.val 3
    simp only [Function.update_of_ne (by omega : z ≠ vertexRecordAddress width v.val 3)]
  have hoFlags : VertexFIFOFlags out.scalar.integerMemory width 3 vertices := by rw [hI]; exact hFlags.pop hw3 hn
  have eRun : MachineEval m g ω vertexFIFODequeueCode st (4*width+17) out := by
    have ee := MachineEval.seq ep (MachineEval.seq eo es)
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,S,eRun,(es.pointer_frame 40 (by decide)).trans hm40,hoRep,hSub,hoFlags,hI,hoR.trans hpR,
    (es.pointer_frame 0 (by decide)).trans hm0,eRun.query_frame (by decide),?_,hoO.trans hpO,hoH⟩
  · rw [hoW]
    change pre.work+1+(4*width+9 : ℕ)= _
    rw [hpW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushDequeueMemory

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def pushDequeued {n : ℕ} (logical : PushState n) (v : Fin n) (vertices : List (Fin n)) : PushState n :=
  { logical with queue := vertices, queued := logical.queued.erase v }

set_option maxHeartbeats 2200000 in
lemma push_dequeue_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε : ℝ) (logical : PushState n) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : PushMachineMemory g α ε logical st) (v : Fin n) (vertices : List (Fin n))
    (hq : logical.queue=v::vertices) (hn : logical.queue.Nodup) :
    ∃ out, MachineEval m g ω vertexFIFODequeueCode st 81 out ∧ out.scalar.core.ptrs 40=(v.val : ℤ) ∧
      Nonempty (PushMachineMemory g α ε (pushDequeued logical v vertices) out) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+81 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  have hQueue : VertexFIFORep st.scalar.integerMemory (st.scalar.core.ptrs 90) (st.scalar.core.ptrs 91) (v::vertices) pm.queueCells := by rw [←hq]; exact pm.queue
  have hFlags : VertexFIFOFlags st.scalar.integerMemory 16 3 (v::vertices) := by rw [←hq]; exact pm.queueFlags
  obtain ⟨out,S,ex,h40,hRep,hSub,hF,hI,hR,h0,hQ,hW,hO,hH⟩ := vertex_fifo_dequeue_exec m g ω st hh 16 (by decide)
    (st.scalar.core.ptrs 90) (st.scalar.core.ptrs 91) v vertices pm.queueCells pm.zeroPointer pm.widthPointer rfl rfl hQueue hFlags (by rw [←hq]; exact hn)
  have hp20 : out.scalar.core.ptrs 20=st.scalar.core.ptrs 20 := ex.pointer_frame 20 (by decide)
  have hField (u : Fin n) (field : ℕ) (hf : field < 16) (hne : field ≠ 3) :
      out.scalar.integerMemory (vertexRecordAddress 16 u.val field)=st.scalar.integerMemory (vertexRecordAddress 16 u.val field) := by
    rw [hI]
    exact vertex_integer_update_other_field _ _ _ _ _ _ _ (by decide) hf hne
  have hSupport : VertexListRep out.scalar.integerMemory (out.scalar.core.ptrs 92) pm.supportVertices pm.supportCells := by
    rw [hI,ex.pointer_frame 92 (by decide)]
    exact pm.support.negative_write _ _ (vertexRecordAddress_negative _ _ _)
  have outMem : PushMachineMemory g α ε (pushDequeued logical v vertices) out := {
    zeroPointer := h0
    widthPointer := (ex.pointer_frame 41 (by decide)).trans pm.widthPointer
    globalWidth := (ex.pointer_frame 50 (by decide)).trans pm.globalWidth
    freeBound := by rw [hp20]; exact pm.freeBound
    alphaRegister := (ex.real_register_frame 30 (by decide)).trans pm.alphaRegister
    oneRegister := (ex.real_register_frame 31 (by decide)).trans pm.oneRegister
    epsilonRegister := (ex.real_register_frame 20 (by decide)).trans pm.epsilonRegister
    potential := by intro u; rw [hR]; exact pm.potential u
    residual := by intro u; rw [hR]; exact pm.residual u
    excluded := fun u => (hField u 2 (by decide) (by decide)).trans (pm.excluded u)
    queueFlags := hF
    supportDegree := fun u hu => (hField u 0 (by decide) (by decide)).trans (pm.supportDegree u hu)
    queueCells := S
    queue := hRep
    supportVertices := pm.supportVertices
    supportCells := pm.supportCells
    support := hSupport
    supportNodup := pm.supportNodup
    supportSet := pm.supportSet
    supportFlags := pm.supportFlags.frame (fun u => hField u 4 (by decide) (by decide))
    separate := pm.separate.mono_left hSub
    queueBelow := by intro z hz; rw [hp20]; exact pm.queueBelow z (hSub hz)
    supportBelow := by intro z hz; rw [hp20]; exact pm.supportBelow z hz
  }
  exact ⟨out,ex,h40,⟨outMem⟩,hQ,hW,hO,hH⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushDegreeMemory

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 1800000 in
lemma push_degree_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε : ℝ) (logical : PushState n) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : PushMachineMemory g α ε logical st) (v : Fin n) (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) :
    ∃ out, MachineEval m g ω degreeRecordStoreCode st 74 out ∧
      out.scalar.core.ptrs 60=((g.neighbors v).length : ℤ) ∧
      out.scalar.integerMemory (vertexRecordAddress 16 v.val 0)=((g.neighbors v).length : ℤ) ∧
      Nonempty (PushMachineMemory g α ε logical out) ∧
      out.scalar.queries=st.scalar.queries+1 ∧ out.work=st.work+74 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨out,ex,h60,hI,hR,hRegs,hQ,hW,hO,hH⟩ := degree_record_store_exec m g ω st hh 16 v pm.zeroPointer hv pm.widthPointer
  have hp20 := ex.pointer_frame 20 (by decide)
  have hField (u : Fin n) (field : ℕ) (hf : field < 16) (hne : field ≠ 0) :
      out.scalar.integerMemory (vertexRecordAddress 16 u.val field)=st.scalar.integerMemory (vertexRecordAddress 16 u.val field) := by
    rw [hI]
    exact vertex_integer_update_other_field _ _ _ _ _ _ _ (by decide) hf hne
  have hQueue : VertexFIFORep out.scalar.integerMemory (out.scalar.core.ptrs 90) (out.scalar.core.ptrs 91) logical.queue pm.queueCells := by
    rw [hI,ex.pointer_frame 90 (by decide),ex.pointer_frame 91 (by decide)]
    exact pm.queue.negative_write _ _ (vertexRecordAddress_negative _ _ _)
  have hSupport : VertexListRep out.scalar.integerMemory (out.scalar.core.ptrs 92) pm.supportVertices pm.supportCells := by
    rw [hI,ex.pointer_frame 92 (by decide)]
    exact pm.support.negative_write _ _ (vertexRecordAddress_negative _ _ _)
  have hSupportDegree : ∀ u ∈ logical.support, out.scalar.integerMemory (vertexRecordAddress 16 u.val 0)=((g.neighbors u).length : ℤ) := by
    intro u hu
    rw [hI]
    by_cases he : u=v
    · subst u; simp
    · have hn : vertexRecordAddress 16 u.val 0 ≠ vertexRecordAddress 16 v.val 0 := by
        intro hx
        exact he (Fin.ext (vertexRecordAddress_injective 16 u.val v.val 0 0 (by decide) (by decide) hx).1)
      rw [Function.update_of_ne hn]
      exact pm.supportDegree u hu
  have outMem : PushMachineMemory g α ε logical out := {
    zeroPointer := (ex.pointer_frame 0 (by decide)).trans pm.zeroPointer
    widthPointer := (ex.pointer_frame 41 (by decide)).trans pm.widthPointer
    globalWidth := (ex.pointer_frame 50 (by decide)).trans pm.globalWidth
    freeBound := by rw [hp20]; exact pm.freeBound
    alphaRegister := (congrFun hRegs 30).trans pm.alphaRegister
    oneRegister := (congrFun hRegs 31).trans pm.oneRegister
    epsilonRegister := (congrFun hRegs 20).trans pm.epsilonRegister
    potential := by intro u; rw [hR]; exact pm.potential u
    residual := by intro u; rw [hR]; exact pm.residual u
    excluded := fun u => (hField u 2 (by decide) (by decide)).trans (pm.excluded u)
    queueFlags := pm.queueFlags.frame (fun u => hField u 3 (by decide) (by decide))
    supportDegree := hSupportDegree
    queueCells := pm.queueCells
    queue := hQueue
    supportVertices := pm.supportVertices
    supportCells := pm.supportCells
    support := hSupport
    supportNodup := pm.supportNodup
    supportSet := pm.supportSet
    supportFlags := pm.supportFlags.frame (fun u => hField u 4 (by decide) (by decide))
    separate := pm.separate
    queueBelow := by intro z hz; rw [hp20]; exact pm.queueBelow z hz
    supportBelow := by intro z hz; rw [hp20]; exact pm.supportBelow z hz
  }
  refine ⟨out,ex,h60,?_,⟨outMem⟩,hQ,hW,hO,hH⟩
  rw [hI]
  simp

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushMemoryFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def PushMachineMemory.frame {n : ℕ} {g : InputGraph n} {α ε : ℝ} {logical : PushState n}
    {st out : MachineState} (pm : PushMachineMemory g α ε logical st)
    (hI : out.scalar.integerMemory=st.scalar.integerMemory)
    (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hP : ∀ i ∈ ([0,20,41,50,90,91,92] : List ℕ), out.scalar.core.ptrs i=st.scalar.core.ptrs i)
    (hG : ∀ i ∈ ([20,30,31] : List ℕ), out.scalar.core.regs i=st.scalar.core.regs i) :
    PushMachineMemory g α ε logical out := {
  zeroPointer := (hP 0 (by simp)).trans pm.zeroPointer
  widthPointer := (hP 41 (by simp)).trans pm.widthPointer
  globalWidth := (hP 50 (by simp)).trans pm.globalWidth
  freeBound := by rw [hP 20 (by simp)]; exact pm.freeBound
  alphaRegister := (hG 30 (by simp)).trans pm.alphaRegister
  oneRegister := (hG 31 (by simp)).trans pm.oneRegister
  epsilonRegister := (hG 20 (by simp)).trans pm.epsilonRegister
  potential := by rw [hR]; exact pm.potential
  residual := by rw [hR]; exact pm.residual
  excluded := by rw [hI]; exact pm.excluded
  queueFlags := by rw [hI]; exact pm.queueFlags
  supportDegree := by rw [hI]; exact pm.supportDegree
  queueCells := pm.queueCells
  queue := by rw [hI,hP 90 (by simp),hP 91 (by simp)]; exact pm.queue
  supportVertices := pm.supportVertices
  supportCells := pm.supportCells
  support := by rw [hI,hP 92 (by simp)]; exact pm.support
  supportNodup := pm.supportNodup
  supportSet := pm.supportSet
  supportFlags := by rw [hI]; exact pm.supportFlags
  separate := pm.separate
  queueBelow := by rw [hP 20 (by simp)]; exact pm.queueBelow
  supportBelow := by rw [hP 20 (by simp)]; exact pm.supportBelow
}

def PushMachineMemory.payUnit {n : ℕ} {g : InputGraph n} {α ε : ℝ} {logical : PushState n}
    {st : MachineState} (pm : PushMachineMemory g α ε logical st) :
    PushMachineMemory g α ε logical (NearlyOptimalPPR.Computation.payUnit st) :=
  pm.frame rfl rfl (by intros; rfl) (by intros; rfl)

def PushMachineMemory.pointerWrite {n : ℕ} {g : InputGraph n} {α ε : ℝ} {logical : PushState n}
    {st : MachineState} (pm : PushMachineMemory g α ε logical st) (r : ℕ) (value : ℤ)
    (hr : r ∉ ([0,20,41,50,90,91,92] : List ℕ)) :
    PushMachineMemory g α ε logical (NearlyOptimalPPR.Computation.pointerWrite st r value) :=
  pm.frame rfl rfl (by
    intro j hj
    change Function.update st.scalar.core.ptrs r value j=st.scalar.core.ptrs j
    apply Function.update_of_ne
    intro he
    subst j
    exact hr hj) (by intros; rfl)

def PushMachineMemory.agree {n : ℕ} {g : InputGraph n} {α ε : ℝ} {a b : PushState n}
    {st : MachineState} (pm : PushMachineMemory g α ε a st)
    (hz : b.z=a.z) (hr : b.r=a.r) (hq : b.queue=a.queue) (hs : b.support=a.support) :
    PushMachineMemory g α ε b st := {
  pm with
  potential := by rw [hz]; exact pm.potential
  residual := by rw [hr]; exact pm.residual
  queueFlags := by rw [hq]; exact pm.queueFlags
  supportDegree := by rw [hs]; exact pm.supportDegree
  queue := by rw [hq]; exact pm.queue
  supportSet := by rw [hs]; exact pm.supportSet
}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushEligibilityExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1000000 in
lemma push_eligibility_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width : ℕ) (v : Fin n) (ε residual : ℝ) (degree : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (he : st.scalar.core.regs 20=ε)
    (hr : st.scalar.core.mem (vertexRecordAddress width v.val 1)=residual)
    (hd : st.scalar.integerMemory (vertexRecordAddress width v.val 0)=(degree : ℤ)) :
    ∃ out, MachineEval m g ω pushEligibilityCode st (8*width+22) out ∧
      out.scalar.core.regs 23=residual-ε*(degree : ℝ) ∧ (0 < out.scalar.core.regs 23 ↔ ε*(degree : ℝ) < residual) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(8*width+22 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let pre := payUnit (pointerWrite st 87 0)
  have ep : MachineEval m g ω (coreCode (.pset 87 0)) st 1 pre := pset_eval m g ω st 87 0 hh
  have hp0 := (ep.pointer_frame 0 (by decide)).trans hz
  have hp40 := (ep.pointer_frame 40 (by decide)).trans hv
  have hp41 := (ep.pointer_frame 41 (by decide)).trans hw
  have hp20 := (ep.real_register_frame 20 (by decide)).trans he
  have hp87 : pre.scalar.core.ptrs 87=0 := by simp [pre,payUnit,pcSet,pointerWrite]
  obtain ⟨out,ee,h23,hI,hR,hQ,hW,hO,hH⟩ := exterior_inactive_exec m g ω pre hh width v.val 0 ε hp0 hp40 hp41 hp87 hp20
  have ho23 : out.scalar.core.regs 23=residual-ε*(degree : ℝ) := by
    change out.scalar.core.regs 23=st.scalar.core.mem (vertexRecordAddress width v.val 1)-ε*(st.scalar.integerMemory (vertexRecordAddress width v.val 0) : ℝ) at h23
    simpa only [hr,hd,Int.cast_natCast] using h23
  have eRun : MachineEval m g ω pushEligibilityCode st (8*width+22) out := by
    have e := MachineEval.seq ep ee
    convert e using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,ho23,by rw [ho23]; exact sub_pos,hI,hR,hQ,?_,hO,hH⟩
  rw [hW]
  change st.work+1+(8*width+21 : ℕ)= _
  push_cast
  ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushEligibilityMemory

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1600000 in
lemma push_eligibility_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε : ℝ) (logical : PushState n) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : PushMachineMemory g α ε logical st) (v : Fin n)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hd : st.scalar.integerMemory (vertexRecordAddress 16 v.val 0)=((g.neighbors v).length : ℤ)) :
    ∃ out, MachineEval m g ω pushEligibilityCode st 150 out ∧
      (0 < out.scalar.core.regs 23 ↔ ε*((g.neighbors v).length : ℝ) < logical.r v) ∧
      Nonempty (PushMachineMemory g α ε logical out) ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+150 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨out,ex,h23,hTest,hI,hR,hQ,hW,hO,hH⟩ := push_eligibility_exec m g ω st hh 16 v ε (logical.r v) (g.neighbors v).length
    pm.zeroPointer hv pm.widthPointer pm.epsilonRegister (pm.residual v) hd
  have hP : ∀ i ∈ ([0,20,41,50,90,91,92] : List ℕ), out.scalar.core.ptrs i=st.scalar.core.ptrs i := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ex.pointer_frame _ (by decide)
  have hG : ∀ i ∈ ([20,30,31] : List ℕ), out.scalar.core.regs i=st.scalar.core.regs i := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl <;> exact ex.real_register_frame _ (by decide)
  exact ⟨out,ex,hTest,⟨pm.frame hI hR hP hG⟩,(ex.pointer_frame 40 (by decide)).trans hv,hQ,hW,hO,hH⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushEligibilityDegree

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1400000 in
lemma exterior_inactive_degree (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st out : MachineState) (u : ℕ) (hh : st.scalar.halted=false) (width vertex : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (ex : MachineEval m g ω exteriorInactiveCode st u out) :
    out.scalar.core.ptrs 60=st.scalar.integerMemory (vertexRecordAddress width vertex 0) := by
  cases ex with
  | seq ea eb =>
    obtain ⟨a,er,h60,hI,hR,hQ,hW,hO,hH⟩ := vertex_field_read_exec m g ω st hh width vertex 0 60 hz hv hw
    obtain ⟨_,he⟩ := ea.deterministic er
    subst a
    exact (eb.pointer_frame 60 (by decide)).trans h60

lemma push_eligibility_degree (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st out : MachineState) (u : ℕ) (hh : st.scalar.halted=false) (width vertex : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (ex : MachineEval m g ω pushEligibilityCode st u out) :
    out.scalar.core.ptrs 60=st.scalar.integerMemory (vertexRecordAddress width vertex 0) := by
  cases ex with
  | seq ea eb =>
    have h0 := (ea.pointer_frame 0 (by decide)).trans hz
    have h40 := (ea.pointer_frame 40 (by decide)).trans hv
    have h41 := (ea.pointer_frame 41 (by decide)).trans hw
    have hI := ea.integer_memory_frame (by simp [coreCode,MachineCode.allAtoms,integerReadOnly])
    have h60 := exterior_inactive_degree m g ω _ out _ ((ea.halted (by simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible])).trans hh) width vertex h0 h40 h41 eb
    exact h60.trans (congrFun hI _)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushScalarCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1600000 in
lemma push_value_calc_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (degree : ℕ) (residual α : ℝ)
    (hd : st.scalar.core.ptrs 60=(degree : ℤ)) (hr : st.scalar.core.regs 10=residual)
    (ha : st.scalar.core.regs 30=α) (h1 : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω pushValueCalcCode st 6 out ∧
      out.scalar.core.regs 12=residual/(degree : ℝ) ∧
      out.scalar.core.regs 13=(1-α)*(residual/(degree : ℝ)) ∧
      out.scalar.core.regs 10=residual/(degree : ℝ) ∧ out.scalar.core.ptrs 44=0 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+6 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω pushValueCalcInstructions
    (by simp [pushValueCalcInstructions,RealOperation.instruction,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,?_,?_,ex.query_frame (by decide),hW,?_,hH⟩
  all_goals simp [linearRun,pushValueCalcInstructions,RealOperation.instruction,atomState,machineStep,pcSet,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hd,hr,ha,h1]

set_option maxHeartbeats 1000000 in
lemma push_residual_reset_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω pushResidualResetCode st 2 out ∧ out.scalar.core.regs 10=0 ∧
      out.scalar.core.ptrs 44=1 ∧ out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+2 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω pushResidualResetInstructions
    (by simp [pushResidualResetInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,pushResidualResetInstructions,atomState,machineStep,pcSet,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushScalarUpdateExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2600000 in
lemma push_scalar_update_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width : ℕ) (v : Fin n) (degree : ℕ) (α residual potential : ℝ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hd : st.scalar.core.ptrs 60=(degree : ℤ))
    (ha : st.scalar.core.regs 30=α) (h1 : st.scalar.core.regs 31=1)
    (hr : st.scalar.core.mem (vertexRecordAddress width v.val 1)=residual)
    (hp : st.scalar.core.mem (vertexRecordAddress width v.val 0)=potential) :
    ∃ out, MachineEval m g ω pushScalarUpdateCode st (12*width+32) out ∧
      out.scalar.core.mem=Function.update
        (Function.update st.scalar.core.mem (vertexRecordAddress width v.val 0) (potential+residual/(degree : ℝ)))
        (vertexRecordAddress width v.val 1) 0 ∧
      out.scalar.core.regs 12=residual/(degree : ℝ) ∧ out.scalar.core.regs 13=(1-α)*(residual/(degree : ℝ)) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧ out.scalar.core.ptrs 41=(width : ℤ) ∧ out.scalar.core.ptrs 60=(degree : ℤ) ∧
      out.scalar.core.regs 20=st.scalar.core.regs 20 ∧ out.scalar.core.regs 30=α ∧ out.scalar.core.regs 31=1 ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(12*width+32 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := payUnit (pointerWrite st 44 1)
  have ea : MachineEval m g ω (coreCode (.pset 44 1)) st 1 a := pset_eval m g ω st 44 1 hh
  have a0 := (ea.pointer_frame 0 (by decide)).trans hz
  have a40 := (ea.pointer_frame 40 (by decide)).trans hv
  have a41 := (ea.pointer_frame 41 (by decide)).trans hw
  have a44 : a.scalar.core.ptrs 44=(1 : ℤ) := by simp [a,payUnit,pcSet,pointerWrite]
  obtain ⟨b,eb,hb10,hbI,hbR,hbW,hbO,hbH⟩ := vertex_real_load_exec m g ω a hh width v.val 1 a0 a40 a41 a44
  have b10 : b.scalar.core.regs 10=residual := by rw [hb10]; exact hr
  have b60 := (eb.pointer_frame 60 (by decide)).trans ((ea.pointer_frame 60 (by decide)).trans hd)
  have b30 := (eb.real_register_frame 30 (by decide)).trans ((ea.real_register_frame 30 (by decide)).trans ha)
  have b31 := (eb.real_register_frame 31 (by decide)).trans ((ea.real_register_frame 31 (by decide)).trans h1)
  obtain ⟨c,ec,hc12,hc13,hc10,hc44,hcI,hcR,hcQ,hcW,hcO,hcH⟩ := push_value_calc_exec m g ω b hbH degree residual α b60 b10 b30 b31
  have ePrefix := MachineEval.seq ea (MachineEval.seq eb ec)
  have c0 := (ePrefix.pointer_frame 0 (by decide)).trans hz
  have c40 := (ePrefix.pointer_frame 40 (by decide)).trans hv
  have c41 := (ePrefix.pointer_frame 41 (by decide)).trans hw
  have cR : c.scalar.core.mem=st.scalar.core.mem := hcR.trans hbR
  obtain ⟨d,ed,hdR,hdI,hdQ,hdW,hdO,hdH⟩ := vertex_real_add_exec m g ω c hcH width v.val 0 c0 c40 c41 hc44
  have dR : d.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width v.val 0)
      (potential+residual/(degree : ℝ)) := by rw [hdR,cR,hc10,hp]
  obtain ⟨e,ee,he10,he44,heI,heR,heW,heO,heH⟩ := push_residual_reset_exec m g ω d hdH
  have e0 := (ee.pointer_frame 0 (by decide)).trans ((ed.pointer_frame 0 (by decide)).trans c0)
  have e40 := (ee.pointer_frame 40 (by decide)).trans ((ed.pointer_frame 40 (by decide)).trans c40)
  have e41 := (ee.pointer_frame 41 (by decide)).trans ((ed.pointer_frame 41 (by decide)).trans c41)
  obtain ⟨out,ef,hoR,hoI,hoRegs,hoW,hoO,hoH⟩ := vertex_real_store_exec m g ω e heH width v.val 1 e0 e40 e41 he44
  have eRun : MachineEval m g ω pushScalarUpdateCode st (12*width+32) out := by
    have ex := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee ef))))
    convert ex using 1 <;> (first | rfl | omega)
  have h12 : out.scalar.core.regs 12=residual/(degree : ℝ) :=
    (ef.real_register_frame 12 (by decide)).trans ((ee.real_register_frame 12 (by decide)).trans ((ed.real_register_frame 12 (by decide)).trans hc12))
  have h13 : out.scalar.core.regs 13=(1-α)*(residual/(degree : ℝ)) :=
    (ef.real_register_frame 13 (by decide)).trans ((ee.real_register_frame 13 (by decide)).trans ((ed.real_register_frame 13 (by decide)).trans hc13))
  refine ⟨out,eRun,?_,h12,h13,hoI.trans (heI.trans (hdI.trans (hcI.trans hbI))),
    (eRun.pointer_frame 0 (by decide)).trans hz,(eRun.pointer_frame 40 (by decide)).trans hv,
    (eRun.pointer_frame 41 (by decide)).trans hw,(eRun.pointer_frame 60 (by decide)).trans hd,
    eRun.real_register_frame 20 (by decide),(eRun.real_register_frame 30 (by decide)).trans ha,
    (eRun.real_register_frame 31 (by decide)).trans h1,eRun.query_frame (by decide),?_,hoO.trans (heO.trans (hdO.trans (hcO.trans hbO))),hoH⟩
  · rw [hoR,heR,dR,he10]
  · rw [hoW,heW,hdW,hcW,hbW]
    change st.work+1+(4*width+7 : ℕ)+(6 : ℕ)+(4*width+9 : ℕ)+(2 : ℕ)+(4*width+7 : ℕ)= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexRealTables

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def VertexRealTable {n : ℕ} (R : ℤ → ℝ) (width offset : ℕ) (values : Fin n → ℝ) : Prop :=
  ∀ v : Fin n, R (vertexRecordAddress width v.val offset)=values v

lemma VertexRealTable.update {n : ℕ} {R : ℤ → ℝ} {width offset : ℕ} {values : Fin n → ℝ}
    (h : VertexRealTable R width offset values) (hoff : offset < width) (v : Fin n) (value : ℝ) :
    VertexRealTable (Function.update R (vertexRecordAddress width v.val offset) value)
      width offset (Function.update values v value) := by
  intro u
  by_cases he : u=v
  · subst u
    simp
  · have hne : vertexRecordAddress width u.val offset ≠ vertexRecordAddress width v.val offset := by
      intro hx
      exact he (Fin.ext (vertexRecordAddress_injective width u.val v.val offset offset hoff hoff hx).1)
    simp only [Function.update_of_ne hne,Function.update_of_ne he]
    exact h u

lemma VertexRealTable.other_field {n : ℕ} {R : ℤ → ℝ} {width offset : ℕ} {values : Fin n → ℝ}
    (h : VertexRealTable R width offset values) (hoff : offset < width) (v : Fin n) (field : ℕ)
    (hf : field < width) (hne : offset ≠ field) (value : ℝ) :
    VertexRealTable (Function.update R (vertexRecordAddress width v.val field) value) width offset values := by
  intro u
  have hn : vertexRecordAddress width u.val offset ≠ vertexRecordAddress width v.val field := by
    intro hx
    exact hne (vertexRecordAddress_injective width u.val v.val offset field hoff hf hx).2
  simp only [Function.update_of_ne hn]
  exact h u

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushScalarMemory

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushScalarUpdated {n : ℕ} (logical : PushState n) (v : Fin n) (degree : ℕ) : PushState n :=
  { logical with
    z := Function.update logical.z v (logical.z v+logical.r v/(degree : ℝ))
    r := Function.update logical.r v 0 }

set_option maxHeartbeats 2200000 in
lemma push_scalar_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε : ℝ) (logical : PushState n) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : PushMachineMemory g α ε logical st) (v : Fin n) (degree : ℕ)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) (hd : st.scalar.core.ptrs 60=(degree : ℤ)) :
    ∃ out, MachineEval m g ω pushScalarUpdateCode st 224 out ∧
      Nonempty (PushMachineMemory g α ε (pushScalarUpdated logical v degree) out) ∧
      out.scalar.core.regs 12=logical.r v/(degree : ℝ) ∧
      out.scalar.core.regs 13=(1-α)*(logical.r v/(degree : ℝ)) ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧ out.scalar.integerMemory=st.scalar.integerMemory ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+224 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨out,ex,hR,h12,h13,hI,h0,h40,h41,h60,h20,h30,h31,hQ,hW,hO,hH⟩ :=
    push_scalar_update_exec m g ω st hh 16 v degree α (logical.r v) (logical.z v)
      pm.zeroPointer hv pm.widthPointer hd pm.alphaRegister pm.oneRegister (pm.residual v) (pm.potential v)
  have hz : VertexRealTable st.scalar.core.mem 16 0 logical.z := pm.potential
  have hr : VertexRealTable st.scalar.core.mem 16 1 logical.r := pm.residual
  have hz' := (hz.update (by decide) v (logical.z v+logical.r v/(degree : ℝ))).other_field (by decide) v 1 (by decide) (by decide) 0
  have hr' := (hr.other_field (by decide) v 0 (by decide) (by decide) (logical.z v+logical.r v/(degree : ℝ))).update (by decide) v 0
  have hp20 := ex.pointer_frame 20 (by decide)
  have outMem : PushMachineMemory g α ε (pushScalarUpdated logical v degree) out := {
    zeroPointer := h0
    widthPointer := h41
    globalWidth := (ex.pointer_frame 50 (by decide)).trans pm.globalWidth
    freeBound := by rw [hp20]; exact pm.freeBound
    alphaRegister := h30
    oneRegister := h31
    epsilonRegister := h20.trans pm.epsilonRegister
    potential := by rw [hR]; exact hz'
    residual := by rw [hR]; exact hr'
    excluded := by rw [hI]; exact pm.excluded
    queueFlags := by rw [hI]; exact pm.queueFlags
    supportDegree := by rw [hI]; exact pm.supportDegree
    queueCells := pm.queueCells
    queue := by rw [hI,ex.pointer_frame 90 (by decide),ex.pointer_frame 91 (by decide)]; exact pm.queue
    supportVertices := pm.supportVertices
    supportCells := pm.supportCells
    support := by rw [hI,ex.pointer_frame 92 (by decide)]; exact pm.support
    supportNodup := pm.supportNodup
    supportSet := pm.supportSet
    supportFlags := by rw [hI]; exact pm.supportFlags
    separate := pm.separate
    queueBelow := by rw [hp20]; exact pm.queueBelow
    supportBelow := by rw [hp20]; exact pm.supportBelow
  }
  exact ⟨out,ex,⟨outMem⟩,h12,h13,h40,hI,hQ,hW,hO,hH⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SupportInsertCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma support_list_prepend_zero {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {st out : MachineState} {u : ℕ} (hh : st.scalar.halted=false)
    (e : MachineEval m g ω supportListPrependCode st u out) : out.scalar.core.ptrs 0=0 := by
  change MachineEval m g ω (.seq heapNodeAllocCode _) st u out at e
  cases e with
  | seq eAlloc eTail =>
    obtain ⟨alloc,ee,ha0,ha5,ha20,haI,haR,haW,haO⟩ := heap_node_alloc_exec m g ω st hh
    have hEq := (eAlloc.deterministic ee).2
    rw [hEq] at eTail
    exact (eTail.pointer_frame 0 (by decide)).trans ha0

set_option maxHeartbeats 2200000 in
lemma support_insert_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width : ℕ) (hw4 : 4 < width)
    (free head : ℤ) (v : Fin n) (vertices : List (Fin n)) (F : Finset ℤ)
    (hfree : 2 ≤ free) (hf : st.scalar.core.ptrs 20=free) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hhead : st.scalar.core.ptrs 92=head)
    (h : VertexListRep st.scalar.integerMemory head vertices F) (hbelow : ∀ z ∈ F, z < free)
    (hFlags : VertexFIFOFlags st.scalar.integerMemory width 4 vertices) :
    ∃ out, MachineEval m g ω supportInsertCode st (4*width+24) out ∧
      out.scalar.core.ptrs 92=free ∧ out.scalar.core.ptrs 20=free+3 ∧ out.scalar.core.ptrs 0=0 ∧
      VertexListRep out.scalar.integerMemory (out.scalar.core.ptrs 92) (v::vertices) (nodeCells free ∪ F) ∧
      VertexFIFOFlags out.scalar.integerMemory width 4 (v::vertices) ∧
      (∀ z ∈ nodeCells free ∪ F, z < free+3) ∧
      (∀ other : Fin n, ∀ field < width, field ≠ 4 → out.scalar.integerMemory (vertexRecordAddress width other.val field)=st.scalar.integerMemory (vertexRecordAddress width other.val field)) ∧
      (∀ z, 0 ≤ z → z < free → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(4*width+24 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let pre := payUnit (pointerWrite st 4 (v.val : ℤ))
  have ep : MachineEval m g ω (coreCode (.pcopy 4 40)) st 1 pre := by
    simpa only [pre,coreCode,hv] using pcopy_eval m g ω st 4 40 hh
  have hp4 : pre.scalar.core.ptrs 4=(v.val : ℤ) := by simp [pre,payUnit,pcSet,pointerWrite]
  have hp20 := (ep.pointer_frame 20 (by decide)).trans hf
  have hp92 := (ep.pointer_frame 92 (by decide)).trans hhead
  obtain ⟨mid,ea,hm92,hm20,hmRep,hmBelow,hmFrame,hmR,hmQ,hmW,hmO,hmH⟩ :=
    support_list_prepend_exec m g ω pre hh free head v.val (vertices.map Fin.val) F hfree hp20 hp4 hp92 h hbelow
  have hmNeg : ∀ z, z < 0 → mid.scalar.integerMemory z=st.scalar.integerMemory z := by
    intro z hz
    apply hmFrame
    intro hmem
    have hb := (nodeCells_mem_iff free z).mp hmem
    omega
  have hmFlags : VertexFIFOFlags mid.scalar.integerMemory width 4 vertices := hFlags.frame (fun u => hmNeg _ (vertexRecordAddress_negative _ _ _))
  have hm0 : mid.scalar.core.ptrs 0=0 := support_list_prepend_zero (st:=pre) hh ea
  let a := payUnit (pointerWrite mid 88 4)
  have eo : MachineEval m g ω (coreCode (.pset 88 4)) mid 1 a := pset_eval m g ω mid 88 4 hmH
  have a0 := (eo.pointer_frame 0 (by decide)).trans hm0
  have a40 := (eo.pointer_frame 40 (by decide)).trans ((ea.pointer_frame 40 (by decide)).trans ((ep.pointer_frame 40 (by decide)).trans hv))
  have a41 := (eo.pointer_frame 41 (by decide)).trans ((ea.pointer_frame 41 (by decide)).trans ((ep.pointer_frame 41 (by decide)).trans hw))
  have a88 : a.scalar.core.ptrs 88=(4 : ℤ) := by simp [a,payUnit,pcSet,pointerWrite]
  obtain ⟨out,es,hoI,hoR,hoRegs,hoQ,hoW,hoO,hoH⟩ := vertex_flag_set_exec m g ω a hmH width v.val 4 a0 a40 a41 a88
  have ho92 := (es.pointer_frame 92 (by decide)).trans ((eo.pointer_frame 92 (by decide)).trans hm92)
  have hoRep : VertexListRep out.scalar.integerMemory (out.scalar.core.ptrs 92) (v::vertices) (nodeCells free ∪ F) := by
    rw [ho92]
    have hmRep' : VertexListRep mid.scalar.integerMemory free (v::vertices) (nodeCells free ∪ F) := by
      simpa only [VertexListRep,List.map_cons,hm92] using hmRep
    apply VertexListRep.frame hmRep'
    intro z hz
    rw [hoI]
    change Function.update mid.scalar.integerMemory (vertexRecordAddress width v.val 4) 1 z=mid.scalar.integerMemory z
    have hpos := ForestRep.positive_cells hmRep z hz
    have hneg := vertexRecordAddress_negative width v.val 4
    simp only [Function.update_of_ne (by omega : z ≠ vertexRecordAddress width v.val 4)]
  have hoFlags : VertexFIFOFlags out.scalar.integerMemory width 4 (v::vertices) := by
    rw [hoI]
    have hAppend := hmFlags.append hw4 v
    intro u
    simpa [a,payUnit,pcSet,pointerWrite,or_comm] using hAppend u
  have eRun : MachineEval m g ω supportInsertCode st (4*width+24) out := by
    have ee := MachineEval.seq ep (MachineEval.seq ea (MachineEval.seq eo es))
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,ho92,(es.pointer_frame 20 (by decide)).trans ((eo.pointer_frame 20 (by decide)).trans hm20),
    (es.pointer_frame 0 (by decide)).trans a0,hoRep,hoFlags,hmBelow,?_,?_,hoR.trans hmR,eRun.query_frame (by decide),?_,hoO.trans hmO,hoH⟩
  · intro other field hfield hne
    rw [hoI]
    change Function.update mid.scalar.integerMemory (vertexRecordAddress width v.val 4) 1 (vertexRecordAddress width other.val field)=st.scalar.integerMemory _
    rw [vertex_integer_update_other_field _ _ _ _ _ _ _ hw4 hfield hne]
    exact hmNeg _ (vertexRecordAddress_negative _ _ _)
  · intro z hz hzF
    rw [hoI]
    change Function.update mid.scalar.integerMemory (vertexRecordAddress width v.val 4) 1 z=st.scalar.integerMemory z
    have hneg := vertexRecordAddress_negative width v.val 4
    rw [Function.update_of_ne (by omega : z ≠ vertexRecordAddress width v.val 4)]
    apply hmFrame
    intro hm
    have hb := (nodeCells_mem_iff free z).mp hm
    omega
  · rw [hoW]
    change mid.work+1+(4*width+9 : ℕ)= _
    rw [hmW]
    change st.work+1+(13 : ℕ)+1+(4*width+9 : ℕ)= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SupportEnsureExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 2800000 in
lemma support_ensure_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width : ℕ) (hw4 : 4 < width)
    (free head : ℤ) (v : Fin n) (vertices : List (Fin n)) (F : Finset ℤ)
    (hfree : 2 ≤ free) (hf : st.scalar.core.ptrs 20=free) (hz : st.scalar.core.ptrs 0=0)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hhead : st.scalar.core.ptrs 92=head) (h : VertexListRep st.scalar.integerMemory head vertices F)
    (hbelow : ∀ z ∈ F, z < free) (hn : vertices.Nodup)
    (hFlags : VertexFIFOFlags st.scalar.integerMemory width 4 vertices) :
    ∃ steps out F', MachineEval m g ω supportEnsureCode st steps out ∧ steps ≤ 8*width+34 ∧
      VertexListRep out.scalar.integerMemory (out.scalar.core.ptrs 92) (if v ∈ vertices then vertices else v::vertices) F' ∧
      VertexFIFOFlags out.scalar.integerMemory width 4 (if v ∈ vertices then vertices else v::vertices) ∧
      (if v ∈ vertices then vertices else v::vertices).Nodup ∧
      (if v ∈ vertices then vertices else v::vertices).toFinset=insert v vertices.toFinset ∧
      out.scalar.core.ptrs 20=free+(if v ∈ vertices then 0 else 3) ∧ out.scalar.core.ptrs 0=0 ∧
      (∀ z ∈ F', z < out.scalar.core.ptrs 20) ∧ F' ⊆ nodeCells free ∪ F ∧
      (∀ other : Fin n, ∀ field < width, field ≠ 4 → out.scalar.integerMemory (vertexRecordAddress width other.val field)=st.scalar.integerMemory (vertexRecordAddress width other.val field)) ∧
      (∀ z, 0 ≤ z → z < free → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let pre := payUnit (pointerWrite st 88 4)
  have ep : MachineEval m g ω (coreCode (.pset 88 4)) st 1 pre := pset_eval m g ω st 88 4 hh
  have hp0 := (ep.pointer_frame 0 (by decide)).trans hz
  have hp40 := (ep.pointer_frame 40 (by decide)).trans hv
  have hp41 := (ep.pointer_frame 41 (by decide)).trans hw
  have hp88 : pre.scalar.core.ptrs 88=(4 : ℤ) := by simp [pre,payUnit,pcSet,pointerWrite]
  obtain ⟨b,eb,hb51,hbI,hbR,hbRegs,hbQ,hbW,hbO,hbH⟩ := queued_flag_read_exec m g ω pre hh width v.val 4 hp0 hp40 hp41 hp88
  have bI : b.scalar.integerMemory=st.scalar.integerMemory := hbI
  have bR : b.scalar.core.mem=st.scalar.core.mem := hbR
  have b51 : b.scalar.core.ptrs 51=if v ∈ vertices then 1 else 0 := hb51.trans (hFlags v)
  have b0 := (eb.pointer_frame 0 (by decide)).trans hp0
  have b20 := (eb.pointer_frame 20 (by decide)).trans ((ep.pointer_frame 20 (by decide)).trans hf)
  have b40 := (eb.pointer_frame 40 (by decide)).trans hp40
  have b41 := (eb.pointer_frame 41 (by decide)).trans hp41
  have b92 := (eb.pointer_frame 92 (by decide)).trans ((ep.pointer_frame 92 (by decide)).trans hhead)
  have bRep : VertexListRep b.scalar.integerMemory head vertices F := by rw [bI]; exact h
  have bFlags : VertexFIFOFlags b.scalar.integerMemory width 4 vertices := by rw [bI]; exact hFlags
  by_cases hmem : v ∈ vertices
  · have ec : MachineEval m g ω (.branchPointer 51 0 supportInsertCode .skip) b 2 (payUnit (payUnit b)) :=
      MachineEval.pointerGt hbH (by rw [b51,if_pos hmem,b0]; norm_num) (MachineEval.skip (payUnit b))
    have eRun := MachineEval.seq ep (MachineEval.seq eb ec)
    have hoRep : VertexListRep (payUnit (payUnit b)).scalar.integerMemory ((payUnit (payUnit b)).scalar.core.ptrs 92)
        (if v ∈ vertices then vertices else v::vertices) F := by
      change VertexListRep b.scalar.integerMemory (b.scalar.core.ptrs 92) _ F
      rw [b92,if_pos hmem]
      exact bRep
    refine ⟨1+((4*width+8)+2),payUnit (payUnit b),F,eRun,by omega,hoRep,
      by simpa only [payUnit,pcSet,if_pos hmem] using bFlags,by simpa only [if_pos hmem] using hn,?_,?_,b0,?_,Finset.subset_union_right,
      (fun other field hfield hne => congrFun bI _),(fun z hz' hzF => congrFun bI z),bR,eRun.query_frame (by decide),?_,hbO,hbH⟩
    · simp [hmem]
    · simpa only [payUnit_ptrs,if_pos hmem,add_zero] using b20
    · intro z hz'
      change z < b.scalar.core.ptrs 20
      rw [b20]
      exact hbelow z hz'
    · change b.work+1+1= _
      rw [hbW]
      change st.work+1+(4*width+8 : ℕ)+1+1= _
      push_cast
      ring
  · obtain ⟨out,ec,h92,h20,h0,hRep,hFlagOut,hBelow,hFields,hPos,hR,hQ,hW,hO,hH⟩ :=
      support_insert_exec m g ω (payUnit b) hbH width hw4 free head v vertices F hfree b20 b40 b41 b92 bRep hbelow bFlags
    have ed : MachineEval m g ω (.branchPointer 51 0 supportInsertCode .skip) b (1+(4*width+24)) out :=
      MachineEval.pointerLe hbH (by rw [b51,if_neg hmem,b0]) ec
    have eRun := MachineEval.seq ep (MachineEval.seq eb ed)
    refine ⟨1+((4*width+8)+(1+(4*width+24))),out,nodeCells free ∪ F,eRun,by omega,
      by simpa only [if_neg hmem] using hRep,by simpa only [if_neg hmem] using hFlagOut,?_,by simp [hmem],
      by simpa only [if_neg hmem] using h20,h0,?_,Finset.Subset.refl _,
      (fun other field hfield hne => (hFields other field hfield hne).trans (congrFun bI _)),
      (fun z hz' hzF => (hPos z hz' hzF).trans (congrFun bI z)),hR.trans bR,eRun.query_frame (by decide),?_,hO.trans hbO,hH⟩
    · simpa only [if_neg hmem] using (List.nodup_cons.mpr ⟨hmem,hn⟩)
    · intro z hz'
      rw [h20]
      exact hBelow z hz'
    · rw [hW,payUnit_work,hbW]
      change st.work+1+(4*width+8 : ℕ)+1+(4*width+24 : ℕ)= _
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushSupportMemory

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def pushSupportUpdated {n : ℕ} (logical : PushState n) (v : Fin n) : PushState n :=
  { logical with support := insert v logical.support }

set_option maxHeartbeats 2400000 in
lemma push_support_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε : ℝ) (logical : PushState n) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : PushMachineMemory g α ε logical st) (v : Fin n)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hd : st.scalar.integerMemory (vertexRecordAddress 16 v.val 0)=((g.neighbors v).length : ℤ)) :
    ∃ steps out, MachineEval m g ω supportEnsureCode st steps out ∧ steps ≤ 162 ∧
      Nonempty (PushMachineMemory g α ε (pushSupportUpdated logical v) out) ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨steps,out,F,ex,hSteps,hRep,hFlags,hNodup,hSet,hFree,h0,hBelow,hSub,hField,hPos,hR,hQ,hW,hO,hH⟩ :=
    support_ensure_exec m g ω st hh 16 (by decide) (st.scalar.core.ptrs 20) (st.scalar.core.ptrs 92)
      v pm.supportVertices pm.supportCells (by have := pm.freeBound; omega) rfl pm.zeroPointer hv pm.widthPointer rfl
      pm.support pm.supportBelow pm.supportNodup pm.supportFlags
  have hQueue : VertexFIFORep out.scalar.integerMemory (out.scalar.core.ptrs 90) (out.scalar.core.ptrs 91) logical.queue pm.queueCells := by
    rw [ex.pointer_frame 90 (by decide),ex.pointer_frame 91 (by decide)]
    apply pm.queue.frame
    intro z hz
    exact hPos z (by have := pm.queue.positive_cells z hz; omega) (pm.queueBelow z hz)
  have hDisj : Disjoint pm.queueCells F := by
    apply Finset.disjoint_left.mpr
    intro z hz hzF
    rcases Finset.mem_union.mp (hSub hzF) with hn|hs
    · exact Finset.disjoint_left.mp (owned_nodes_disjoint_fresh _ _ pm.queueBelow) hz hn
    · exact Finset.disjoint_left.mp pm.separate hz hs
  have outMem : PushMachineMemory g α ε (pushSupportUpdated logical v) out := {
    zeroPointer := h0
    widthPointer := (ex.pointer_frame 41 (by decide)).trans pm.widthPointer
    globalWidth := (ex.pointer_frame 50 (by decide)).trans pm.globalWidth
    freeBound := by rw [hFree]; split_ifs <;> have := pm.freeBound <;> omega
    alphaRegister := (ex.real_register_frame 30 (by decide)).trans pm.alphaRegister
    oneRegister := (ex.real_register_frame 31 (by decide)).trans pm.oneRegister
    epsilonRegister := (ex.real_register_frame 20 (by decide)).trans pm.epsilonRegister
    potential := by intro u; rw [hR]; exact pm.potential u
    residual := by intro u; rw [hR]; exact pm.residual u
    excluded := fun u => (hField u 2 (by decide) (by decide)).trans (pm.excluded u)
    queueFlags := pm.queueFlags.frame (fun u => hField u 3 (by decide) (by decide))
    supportDegree := by
      intro u hu
      have hu' : u ∈ insert v logical.support := hu
      rcases Finset.mem_insert.mp hu' with he|hu
      · subst u; exact (hField v 0 (by decide) (by decide)).trans hd
      · exact (hField u 0 (by decide) (by decide)).trans (pm.supportDegree u hu)
    queueCells := pm.queueCells
    queue := hQueue
    supportVertices := if v ∈ pm.supportVertices then pm.supportVertices else v::pm.supportVertices
    supportCells := F
    support := hRep
    supportNodup := hNodup
    supportSet := by rw [hSet,pm.supportSet]; rfl
    supportFlags := hFlags
    separate := hDisj
    queueBelow := by
      intro z hz
      have hb := pm.queueBelow z hz
      rw [hFree]; split_ifs <;> omega
    supportBelow := hBelow
  }
  exact ⟨steps,out,ex,hSteps,⟨outMem⟩,(ex.pointer_frame 40 (by decide)).trans hv,hQ,hW,hO,hH⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushNeighborsPreparation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1200000 in
lemma push_neighbors_prepare_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε : ℝ) (logical : PushState n) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : PushMachineMemory g α ε logical st) (v : Fin n)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) (hd : st.scalar.core.ptrs 60=((g.neighbors v).length : ℤ)) :
    ∃ out, MachineEval m g ω pushNeighborsPrepareCode st 3 out ∧
      out.scalar.core.ptrs 63=(v.val : ℤ) ∧ out.scalar.core.ptrs 67=((g.neighbors v).length : ℤ) ∧
      out.scalar.core.ptrs 62=0 ∧ Nonempty (PushMachineMemory g α ε logical out) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+3 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω pushNeighborsPrepareInstructions
    (by simp [pushNeighborsPrepareInstructions,unitInstruction,straightInstruction]) st hh
  have hI : (linearRun m g ω pushNeighborsPrepareInstructions st).scalar.integerMemory=st.scalar.integerMemory := by
    simp [linearRun,pushNeighborsPrepareInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep]
  have hR : (linearRun m g ω pushNeighborsPrepareInstructions st).scalar.core.mem=st.scalar.core.mem := by
    simp [linearRun,pushNeighborsPrepareInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep]
  have hP : ∀ i ∈ ([0,20,41,50,90,91,92] : List ℕ),
      (linearRun m g ω pushNeighborsPrepareInstructions st).scalar.core.ptrs i=st.scalar.core.ptrs i := by
    intro i hi
    apply ex.pointer_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hG : ∀ i ∈ ([20,30,31] : List ℕ),
      (linearRun m g ω pushNeighborsPrepareInstructions st).scalar.core.regs i=st.scalar.core.regs i := by
    intro i hi
    apply ex.real_register_frame
    simp [pushNeighborsPrepareCode,linearCode,pushNeighborsPrepareInstructions,sequenceCode,
      MachineCode.registerTargets,registerTargets]
  refine ⟨_,ex,?_,?_,?_,⟨pm.frame hI hR hP hG⟩,ex.query_frame (by decide),hW,?_,hH⟩
  all_goals simp [linearRun,pushNeighborsPrepareInstructions,atomState,machineStep,pcSet,hh,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hv,hd]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushResidualCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma push_residual_prepare_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (δ : ℝ)
    (hd : st.scalar.core.regs 13=δ) (h1 : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω pushResidualPrepareCode st 2 out ∧
      out.scalar.core.ptrs 44=1 ∧ out.scalar.core.regs 10=δ ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+2 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω pushResidualPrepareInstructions
    (by simp [pushResidualPrepareInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,pushResidualPrepareInstructions,atomState,machineStep,pcSet,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hd,h1]

set_option maxHeartbeats 1400000 in
lemma push_residual_add_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width : ℕ) (v : Fin n) (δ : ℝ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hd : st.scalar.core.regs 13=δ) (h1 : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω pushResidualAddCode st (4*width+11) out ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width v.val 1)
        (st.scalar.core.mem (vertexRecordAddress width v.val 1)+δ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(4*width+11 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a44,a10,aI,aR,aW,aO,aH⟩ := push_residual_prepare_exec m g ω st hh δ hd h1
  have a0 := (ea.pointer_frame 0 (by decide)).trans hz
  have a40 := (ea.pointer_frame 40 (by decide)).trans hv
  have a41 := (ea.pointer_frame 41 (by decide)).trans hw
  obtain ⟨out,eb,bR,bI,bQ,bW,bO,bH⟩ := vertex_real_add_exec m g ω a aH width v.val 1 a0 a40 a41 a44
  have ex : MachineEval m g ω pushResidualAddCode st (4*width+11) out := by
    have e := MachineEval.seq ea eb
    convert e using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,?_,bI.trans aI,?_,?_,bO.trans aO,bH⟩
  · rw [bR,aR,a10]
  · rw [bQ]; exact ea.query_frame (by decide)
  · rw [bW,aW]; push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushResidualMemory

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushResidualUpdated {n : ℕ} (logical : PushState n) (v : Fin n) (δ : ℝ) : PushState n :=
  { logical with r := Function.update logical.r v (logical.r v+δ) }

set_option maxHeartbeats 1600000 in
lemma push_residual_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε δ : ℝ) (logical : PushState n) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : PushMachineMemory g α ε logical st) (v : Fin n)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) (hd : st.scalar.core.regs 13=δ) :
    ∃ out, MachineEval m g ω pushResidualAddCode st 75 out ∧
      Nonempty (PushMachineMemory g α ε (pushResidualUpdated logical v δ) out) ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧ out.scalar.integerMemory=st.scalar.integerMemory ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+75 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨out,ex,hR,hI,hQ,hW,hO,hH⟩ := push_residual_add_exec m g ω st hh 16 v δ pm.zeroPointer hv pm.widthPointer hd pm.oneRegister
  have hz : VertexRealTable st.scalar.core.mem 16 0 logical.z := pm.potential
  have hr : VertexRealTable st.scalar.core.mem 16 1 logical.r := pm.residual
  have hp20 := ex.pointer_frame 20 (by decide)
  have outMem : PushMachineMemory g α ε (pushResidualUpdated logical v δ) out := {
    zeroPointer := (ex.pointer_frame 0 (by decide)).trans pm.zeroPointer
    widthPointer := (ex.pointer_frame 41 (by decide)).trans pm.widthPointer
    globalWidth := (ex.pointer_frame 50 (by decide)).trans pm.globalWidth
    freeBound := by rw [hp20]; exact pm.freeBound
    alphaRegister := (ex.real_register_frame 30 (by decide)).trans pm.alphaRegister
    oneRegister := (ex.real_register_frame 31 (by decide)).trans pm.oneRegister
    epsilonRegister := (ex.real_register_frame 20 (by decide)).trans pm.epsilonRegister
    potential := by rw [hR]; exact hz.other_field (by decide) v 1 (by decide) (by decide) (st.scalar.core.mem (vertexRecordAddress 16 v.val 1)+δ)
    residual := by rw [hR,pm.residual v]; exact hr.update (by decide) v (logical.r v+δ)
    excluded := by rw [hI]; exact pm.excluded
    queueFlags := by rw [hI]; exact pm.queueFlags
    supportDegree := by rw [hI]; exact pm.supportDegree
    queueCells := pm.queueCells
    queue := by rw [hI,ex.pointer_frame 90 (by decide),ex.pointer_frame 91 (by decide)]; exact pm.queue
    supportVertices := pm.supportVertices
    supportCells := pm.supportCells
    support := by rw [hI,ex.pointer_frame 92 (by decide)]; exact pm.support
    supportNodup := pm.supportNodup
    supportSet := pm.supportSet
    supportFlags := by rw [hI]; exact pm.supportFlags
    separate := pm.separate
    queueBelow := by rw [hp20]; exact pm.queueBelow
    supportBelow := by rw [hp20]; exact pm.supportBelow
  }
  exact ⟨out,ex,⟨outMem⟩,(ex.pointer_frame 40 (by decide)).trans hv,hI,hQ,hW,hO,hH⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FIFOEnsureExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 2600000 in
lemma fifo_ensure_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width : ℕ) (hw3 : 3 < width)
    (free head tail : ℤ) (v : Fin n) (vertices : List (Fin n)) (F : Finset ℤ)
    (hfree : 2 ≤ free) (hf : st.scalar.core.ptrs 20=free) (hz : st.scalar.core.ptrs 0=0)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hhead : st.scalar.core.ptrs 90=head) (htail : st.scalar.core.ptrs 91=tail)
    (h : VertexFIFORep st.scalar.integerMemory head tail vertices F) (hbelow : ∀ z ∈ F, z < free)
    (hFlags : VertexFIFOFlags st.scalar.integerMemory width 3 vertices) :
    ∃ steps out F', MachineEval m g ω fifoEnsureCode st steps out ∧ steps ≤ 8*width+36 ∧
      VertexFIFORep out.scalar.integerMemory (out.scalar.core.ptrs 90) (out.scalar.core.ptrs 91)
        (if v ∈ vertices then vertices else vertices++[v]) F' ∧
      VertexFIFOFlags out.scalar.integerMemory width 3 (if v ∈ vertices then vertices else vertices++[v]) ∧
      out.scalar.core.ptrs 20=free+(if v ∈ vertices then 0 else 3) ∧ out.scalar.core.ptrs 0=0 ∧
      (∀ z ∈ F', z < out.scalar.core.ptrs 20) ∧ F' ⊆ F ∪ nodeCells free ∧
      (∀ other : Fin n, ∀ field < width, field ≠ 3 → out.scalar.integerMemory (vertexRecordAddress width other.val field)=st.scalar.integerMemory (vertexRecordAddress width other.val field)) ∧
      (∀ z, 0 ≤ z → z < free → z ∉ F → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let pre := payUnit (pointerWrite st 88 3)
  have ep : MachineEval m g ω (coreCode (.pset 88 3)) st 1 pre := pset_eval m g ω st 88 3 hh
  have hp0 := (ep.pointer_frame 0 (by decide)).trans hz
  have hp40 := (ep.pointer_frame 40 (by decide)).trans hv
  have hp41 := (ep.pointer_frame 41 (by decide)).trans hw
  have hp88 : pre.scalar.core.ptrs 88=(3 : ℤ) := by simp [pre,payUnit,pcSet,pointerWrite]
  obtain ⟨b,eb,hb51,hbI,hbR,hbRegs,hbQ,hbW,hbO,hbH⟩ := queued_flag_read_exec m g ω pre hh width v.val 3 hp0 hp40 hp41 hp88
  have bI : b.scalar.integerMemory=st.scalar.integerMemory := hbI
  have bR : b.scalar.core.mem=st.scalar.core.mem := hbR
  have b51 : b.scalar.core.ptrs 51=if v ∈ vertices then 1 else 0 := hb51.trans (hFlags v)
  have b0 := (eb.pointer_frame 0 (by decide)).trans hp0
  have b20 := (eb.pointer_frame 20 (by decide)).trans ((ep.pointer_frame 20 (by decide)).trans hf)
  have b40 := (eb.pointer_frame 40 (by decide)).trans hp40
  have b41 := (eb.pointer_frame 41 (by decide)).trans hp41
  have b90 := (eb.pointer_frame 90 (by decide)).trans ((ep.pointer_frame 90 (by decide)).trans hhead)
  have b91 := (eb.pointer_frame 91 (by decide)).trans ((ep.pointer_frame 91 (by decide)).trans htail)
  have bRep : VertexFIFORep b.scalar.integerMemory head tail vertices F := by rw [bI]; exact h
  have bFlags : VertexFIFOFlags b.scalar.integerMemory width 3 vertices := by rw [bI]; exact hFlags
  by_cases hmem : v ∈ vertices
  · have ec : MachineEval m g ω (.branchPointer 51 0 vertexFIFOEnqueueCode .skip) b 2 (payUnit (payUnit b)) :=
      MachineEval.pointerGt hbH (by rw [b51,if_pos hmem,b0]; norm_num) (MachineEval.skip (payUnit b))
    have eRun := MachineEval.seq ep (MachineEval.seq eb ec)
    have hoRep : VertexFIFORep (payUnit (payUnit b)).scalar.integerMemory ((payUnit (payUnit b)).scalar.core.ptrs 90)
        ((payUnit (payUnit b)).scalar.core.ptrs 91) (if v ∈ vertices then vertices else vertices++[v]) F := by
      change VertexFIFORep b.scalar.integerMemory (b.scalar.core.ptrs 90) (b.scalar.core.ptrs 91) _ F
      rw [b90,b91,if_pos hmem]
      exact bRep
    refine ⟨1+((4*width+8)+2),payUnit (payUnit b),F,eRun,by omega,hoRep,by simpa only [payUnit,pcSet,if_pos hmem] using bFlags,?_,b0,?_,Finset.subset_union_left,
      (fun other field hfield hne => congrFun bI _),(fun z hz' hzF hn => congrFun bI z),bR,eRun.query_frame (by decide),?_,hbO,hbH⟩
    · simpa only [payUnit_ptrs,if_pos hmem,add_zero] using b20
    · intro z hz'
      change z < b.scalar.core.ptrs 20
      rw [b20]
      exact hbelow z hz'
    · change b.work+1+1= _
      rw [hbW]
      change st.work+1+(4*width+8 : ℕ)+1+1= _
      push_cast
      ring
  · obtain ⟨u,out,ec,hu,h90,h91,h20,h0,hRep,hFlagOut,hBelow,hFields,hPos,hR,hQ,hW,hO,hH⟩ :=
      vertex_fifo_enqueue_exec m g ω (payUnit b) hbH width hw3 free head tail v vertices F hfree b20 b40 b41 b90 b91 bRep hbelow bFlags
    have ed : MachineEval m g ω (.branchPointer 51 0 vertexFIFOEnqueueCode .skip) b (1+u) out :=
      MachineEval.pointerLe hbH (by rw [b51,if_neg hmem,b0]) ec
    have eRun := MachineEval.seq ep (MachineEval.seq eb ed)
    refine ⟨1+((4*width+8)+(1+u)),out,F ∪ nodeCells free,eRun,by omega,by simpa only [if_neg hmem] using hRep,
      by simpa only [if_neg hmem] using hFlagOut,by simpa only [if_neg hmem] using h20,h0,?_,Finset.Subset.refl _,
      (fun other field hfield hne => (hFields other field hfield hne).trans (congrFun bI _)),
      (fun z hz' hzF hn => (hPos z hz' hzF hn).trans (congrFun bI z)),hR.trans bR,eRun.query_frame (by decide),?_,hO.trans hbO,hH⟩
    · intro z hz'
      rw [h20]
      exact hBelow z hz'
    · rw [hW,payUnit_work,hbW]
      change st.work+1+(4*width+8 : ℕ)+1+u= _
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushQueueMemory

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def pushQueueUpdated {n : ℕ} (logical : PushState n) (v : Fin n) : PushState n :=
  { logical with
    queue := if v ∈ logical.queue then logical.queue else logical.queue++[v]
    queued := insert v logical.queued }

set_option maxHeartbeats 2400000 in
lemma push_queue_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε : ℝ) (logical : PushState n) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : PushMachineMemory g α ε logical st) (v : Fin n)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) :
    ∃ steps out, MachineEval m g ω fifoEnsureCode st steps out ∧ steps ≤ 164 ∧
      Nonempty (PushMachineMemory g α ε (pushQueueUpdated logical v) out) ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨steps,out,F,ex,hSteps,hRep,hFlags,hFree,h0,hBelow,hSub,hField,hPos,hR,hQ,hW,hO,hH⟩ :=
    fifo_ensure_exec m g ω st hh 16 (by decide) (st.scalar.core.ptrs 20) (st.scalar.core.ptrs 90) (st.scalar.core.ptrs 91)
      v logical.queue pm.queueCells (by have := pm.freeBound; omega) rfl pm.zeroPointer hv pm.widthPointer rfl rfl
      pm.queue pm.queueBelow pm.queueFlags
  have hSupport : VertexListRep out.scalar.integerMemory (out.scalar.core.ptrs 92) pm.supportVertices pm.supportCells := by
    rw [ex.pointer_frame 92 (by decide)]
    apply pm.support.frame
    intro z hz
    exact hPos z (by have := pm.support.positive_cells z hz; omega) (pm.supportBelow z hz)
      (fun hq => Finset.disjoint_left.mp pm.separate hq hz)
  have hDisj : Disjoint F pm.supportCells := by
    apply Finset.disjoint_left.mpr
    intro z hzF hz
    rcases Finset.mem_union.mp (hSub hzF) with hq|hn
    · exact Finset.disjoint_left.mp pm.separate hq hz
    · exact Finset.disjoint_left.mp (owned_nodes_disjoint_fresh _ _ pm.supportBelow) hz hn
  have outMem : PushMachineMemory g α ε (pushQueueUpdated logical v) out := {
    zeroPointer := h0
    widthPointer := (ex.pointer_frame 41 (by decide)).trans pm.widthPointer
    globalWidth := (ex.pointer_frame 50 (by decide)).trans pm.globalWidth
    freeBound := by rw [hFree]; split_ifs <;> have := pm.freeBound <;> omega
    alphaRegister := (ex.real_register_frame 30 (by decide)).trans pm.alphaRegister
    oneRegister := (ex.real_register_frame 31 (by decide)).trans pm.oneRegister
    epsilonRegister := (ex.real_register_frame 20 (by decide)).trans pm.epsilonRegister
    potential := by intro u; rw [hR]; exact pm.potential u
    residual := by intro u; rw [hR]; exact pm.residual u
    excluded := fun u => (hField u 2 (by decide) (by decide)).trans (pm.excluded u)
    queueFlags := hFlags
    supportDegree := fun u hu => (hField u 0 (by decide) (by decide)).trans (pm.supportDegree u hu)
    queueCells := F
    queue := hRep
    supportVertices := pm.supportVertices
    supportCells := pm.supportCells
    support := hSupport
    supportNodup := pm.supportNodup
    supportSet := pm.supportSet
    supportFlags := pm.supportFlags.frame (fun u => hField u 4 (by decide) (by decide))
    separate := hDisj
    queueBelow := hBelow
    supportBelow := by
      intro z hz
      have hb := pm.supportBelow z hz
      rw [hFree]; split_ifs <;> omega
  }
  exact ⟨steps,out,ex,hSteps,⟨outMem⟩,(ex.pointer_frame 40 (by decide)).trans hv,hQ,hW,hO,hH⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushRefreshCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushRefreshed {n : ℕ} (g : InputGraph n) (ε : ℝ) (logical : PushState n) (v : Fin n) : PushState n :=
  if ε*((g.neighbors v).length : ℝ) < logical.r v then pushQueueUpdated logical v else logical

set_option maxHeartbeats 2000000 in
lemma push_refresh_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε : ℝ) (logical : PushState n) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : PushMachineMemory g α ε logical st) (v : Fin n)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hd : st.scalar.integerMemory (vertexRecordAddress 16 v.val 0)=((g.neighbors v).length : ℤ)) :
    ∃ steps out, MachineEval m g ω pushRefreshCode st steps out ∧ steps ≤ 316 ∧
      Nonempty (PushMachineMemory g α ε (pushRefreshed g ε logical v) out) ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,hTest,⟨pma⟩,a40,aQ,aW,aO,aH⟩ := push_eligibility_memory m g ω α ε logical st hh pm v hv hd
  by_cases ht : ε*((g.neighbors v).length : ℝ) < logical.r v
  · obtain ⟨steps,out,eb,hSteps,⟨pmb⟩,b40,bQ,bW,bO,bH⟩ := push_queue_memory m g ω α ε logical
      (payUnit a) aH pma.payUnit v a40
    have ec := MachineEval.realPos (a:=.skip) aH (not_le.mpr (hTest.mpr ht)) eb
    have ex := MachineEval.seq ea ec
    refine ⟨150+(1+steps+1),payUnit out,ex,by omega,?_,b40,bQ.trans aQ,?_,bO.trans aO,bH⟩
    · simpa only [pushRefreshed,if_pos ht] using (Nonempty.intro pmb.payUnit)
    · change out.work+1= _
      rw [bW,payUnit_work,aW]; push_cast; ring
  · have hn : a.scalar.core.regs 23 ≤ 0 := le_of_not_gt (fun h => ht (hTest.mp h))
    have eb : MachineEval m g ω (.branchReal 23 .skip fifoEnsureCode) a 1 (payUnit a) :=
      MachineEval.realNonpos aH hn (MachineEval.skip (payUnit a))
    have ex := MachineEval.seq ea eb
    refine ⟨151,payUnit a,ex,by omega,?_,a40,aQ,?_,aO,aH⟩
    · simpa only [pushRefreshed,if_neg ht] using (Nonempty.intro pma.payUnit)
    · change a.work+1= _
      rw [aW]; norm_num; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushNeighborUpdate

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushNeighborUpdated {n : ℕ} (g : InputGraph n) (ε δ : ℝ) (logical : PushState n) (v : Fin n) : PushState n :=
  pushRefreshed g ε (pushResidualUpdated logical v δ) v

set_option maxHeartbeats 2400000 in
lemma push_neighbor_update_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε δ : ℝ) (logical : PushState n) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : PushMachineMemory g α ε logical st) (v : Fin n)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) (hd : st.scalar.core.regs 13=δ) :
    ∃ steps out, MachineEval m g ω pushNeighborUpdateCode st steps out ∧ steps ≤ 465 ∧
      Nonempty (PushMachineMemory g α ε (pushNeighborUpdated g ε δ logical v) out) ∧
      out.scalar.queries=st.scalar.queries+1 ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a60,aDegree,⟨pma⟩,aQ,aW,aO,aH⟩ := push_degree_memory m g ω α ε logical st hh pm v hv
  have a40 := (ea.pointer_frame 40 (by decide)).trans hv
  have a13 := (ea.real_register_frame 13 (by decide)).trans hd
  obtain ⟨b,eb,⟨pmb⟩,b40,bI,bQ,bW,bO,bH⟩ := push_residual_memory m g ω α ε δ logical a aH pma v a40 a13
  have bDegree : b.scalar.integerMemory (vertexRecordAddress 16 v.val 0)=((g.neighbors v).length : ℤ) := by
    rw [bI]
    exact aDegree
  obtain ⟨steps,out,ec,hSteps,⟨pmc⟩,c40,cQ,cW,cO,cH⟩ := push_refresh_memory m g ω α ε (pushResidualUpdated logical v δ)
    b bH pmb v b40 bDegree
  have ex := MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨74+(75+steps),out,ex,by omega,⟨pmc⟩,cQ.trans (bQ.trans aQ),?_,cO.trans (bO.trans aO),cH⟩
  rw [cW,bW,aW]; push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushNeighborQuery

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma push_neighbor_query_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε : ℝ) (logical : PushState n) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : PushMachineMemory g α ε logical st) (v : Fin n) (i : ℕ)
    (hv : st.scalar.core.ptrs 63=(v.val : ℤ)) (hi : st.scalar.core.ptrs 62=(i : ℤ))
    (hi' : i < (g.neighbors v).length) :
    ∃ out, MachineEval m g ω (.atom (.scalar (.nbr 40 63 62))) st 1 out ∧
      out.scalar.core.ptrs 40=((g.neighbors v)[i].val : ℤ) ∧
      Nonempty (PushMachineMemory g α ε logical out) ∧
      out.scalar.queries=st.scalar.queries+1 ∧ out.work=st.work+1 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨out,ex,h40,hI,hR,hQ,hW,hO,hH⟩ := neighbor_query_exec m g ω st hh 40 63 62
  have hP : ∀ j ∈ ([0,20,41,50,90,91,92] : List ℕ), out.scalar.core.ptrs j=st.scalar.core.ptrs j := by
    intro j hj
    apply ex.pointer_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hG : ∀ j ∈ ([20,30,31] : List ℕ), out.scalar.core.regs j=st.scalar.core.regs j := by
    intro j hj
    exact ex.real_register_frame j (by simp [MachineCode.registerTargets,registerTargets])
  refine ⟨out,ex,?_,⟨pm.frame hI hR hP hG⟩,hQ,hW,hO,hH⟩
  rw [h40,hv,hi,neighbor_answer_vertex g v i hi']

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushNeighborLoopCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushNeighborsFold {n : ℕ} (g : InputGraph n) (ε δ : ℝ) (logical : PushState n)
    (vertices : List (Fin n)) : PushState n :=
  vertices.foldl (pushNeighborUpdated g ε δ) logical

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushNeighborBodyExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2400000 in
lemma push_neighbor_body_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε δ : ℝ) (logical : PushState n) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : PushMachineMemory g α ε logical st) (v : Fin n) (i : ℕ)
    (hv : st.scalar.core.ptrs 63=(v.val : ℤ)) (hi : st.scalar.core.ptrs 62=(i : ℤ))
    (hlen : st.scalar.core.ptrs 67=((g.neighbors v).length : ℤ))
    (hi' : i < (g.neighbors v).length) (hd : st.scalar.core.regs 13=δ) :
    ∃ steps out, MachineEval m g ω pushNeighborBodyCode st steps out ∧ steps ≤ 467 ∧
      Nonempty (PushMachineMemory g α ε (pushNeighborUpdated g ε δ logical (g.neighbors v)[i]) out) ∧
      out.scalar.core.ptrs 62=((i+1 : ℕ) : ℤ) ∧ out.scalar.core.ptrs 63=(v.val : ℤ) ∧
      out.scalar.core.ptrs 67=((g.neighbors v).length : ℤ) ∧ out.scalar.core.regs 13=δ ∧
      out.scalar.queries=st.scalar.queries+2 ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a40,⟨pma⟩,aQ,aW,aO,aH⟩ := push_neighbor_query_memory m g ω α ε logical st hh pm v i hv hi hi'
  have a13 := (ea.real_register_frame 13 (by decide)).trans hd
  obtain ⟨steps,b,eb,hSteps,⟨pmb⟩,bQ,bW,bO,bH⟩ := push_neighbor_update_memory m g ω α ε δ logical a aH pma (g.neighbors v)[i] a40 a13
  have b62 := (eb.pointer_frame 62 (by decide)).trans ((ea.pointer_frame 62 (by decide)).trans hi)
  let out := payUnit (pointerWrite b 62 (b.scalar.core.ptrs 62+1))
  have ec : MachineEval m g ω (coreCode (.pinc 62)) b 1 out := pinc_eval m g ω b 62 bH
  have ex := MachineEval.seq ea (MachineEval.seq eb ec)
  have pmOut := (pmb.pointerWrite 62 (b.scalar.core.ptrs 62+1) (by decide)).payUnit
  have h62 : out.scalar.core.ptrs 62=((i+1 : ℕ) : ℤ) := by simp [out,payUnit,pcSet,pointerWrite,b62]
  refine ⟨1+(steps+1),out,ex,by omega,⟨pmOut⟩,h62,?_,?_,?_,?_,?_,?_,bH⟩
  · exact (ex.pointer_frame 63 (by decide)).trans hv
  · exact (ex.pointer_frame 67 (by decide)).trans hlen
  · exact (ex.real_register_frame 13 (by decide)).trans hd
  · change b.scalar.queries= _
    omega
  · change b.work+1= _
    rw [bW,aW]; push_cast; ring
  · exact bO.trans aO

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushNeighborLoopExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2600000 in
lemma push_neighbor_loop_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε δ : ℝ) (v : Fin n) (remaining : ℕ) :
    ∀ (i : ℕ) (logical : PushState n) (st : MachineState), st.scalar.halted=false →
    PushMachineMemory g α ε logical st → st.scalar.core.ptrs 63=(v.val : ℤ) →
    st.scalar.core.ptrs 62=(i : ℤ) → st.scalar.core.ptrs 67=((g.neighbors v).length : ℤ) →
    i+remaining=(g.neighbors v).length → st.scalar.core.regs 13=δ →
    ∃ steps out, MachineEval m g ω pushNeighborLoopCode st steps out ∧ steps ≤ 469*remaining+1 ∧
      Nonempty (PushMachineMemory g α ε (pushNeighborsFold g ε δ logical ((g.neighbors v).drop i)) out) ∧
      out.scalar.core.ptrs 62=((g.neighbors v).length : ℤ) ∧ out.scalar.core.ptrs 63=(v.val : ℤ) ∧
      out.scalar.core.ptrs 67=((g.neighbors v).length : ℤ) ∧ out.scalar.core.regs 13=δ ∧
      out.scalar.queries=st.scalar.queries+2*remaining ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction remaining with
  | zero =>
    intro i logical st hh pm hv hi hlen hsum hd
    have he : i=(g.neighbors v).length := by omega
    have ex : MachineEval m g ω pushNeighborLoopCode st 1 (payUnit st) :=
      MachineEval.pointerDone hh (by rw [hlen,hi,he])
    refine ⟨1,payUnit st,ex,by omega,?_,by simpa only [payUnit_ptrs,he] using hi,hv,hlen,hd,by simp [payUnit,pcSet],by simp [payUnit,pcSet],rfl,hh⟩
    simpa only [he,List.drop_length,pushNeighborsFold,List.foldl_nil] using (Nonempty.intro pm.payUnit)
  | succ remaining ih =>
    intro i logical st hh pm hv hi hlen hsum hd
    have hi' : i < (g.neighbors v).length := by omega
    obtain ⟨u,mid,eb,hu,⟨pmMid⟩,hm62,hm63,hm67,hm13,hmQ,hmW,hmO,hmH⟩ :=
      push_neighbor_body_memory m g ω α ε δ logical (payUnit st) hh pm.payUnit v i hv hi hlen hi' hd
    obtain ⟨w,out,er,hw,⟨pmOut⟩,ho62,ho63,ho67,ho13,hoQ,hoW,hoO,hoH⟩ :=
      ih (i+1) (pushNeighborUpdated g ε δ logical (g.neighbors v)[i]) (payUnit mid) hmH pmMid.payUnit
        hm63 hm62 hm67 (by omega) hm13
    have ex : MachineEval m g ω pushNeighborLoopCode st (1+u+1+w) out :=
      MachineEval.pointerNext hh (by rw [hlen,hi]; exact not_le.mpr (by exact_mod_cast hi')) eb er
    refine ⟨1+u+1+w,out,ex,by omega,?_,ho62,ho63,ho67,ho13,?_,?_,hoO.trans hmO,hoH⟩
    · simpa only [pushNeighborsFold,List.drop_eq_getElem_cons hi',List.foldl_cons] using (Nonempty.intro pmOut)
    · change out.scalar.queries= _
      change out.scalar.queries=mid.scalar.queries+2*remaining at hoQ
      change mid.scalar.queries=st.scalar.queries+2 at hmQ
      omega
    · rw [hoW,payUnit_work,hmW,payUnit_work]
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushPositiveCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushPositiveLogical {n : ℕ} (g : InputGraph n) (α ε : ℝ) (logical : PushState n) (v : Fin n) : PushState n :=
  pushNeighborsFold g ε ((1-α)*(logical.r v/((g.neighbors v).length : ℝ)))
    (pushSupportUpdated (pushScalarUpdated logical v (g.neighbors v).length) v) (g.neighbors v)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushPositiveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2600000 in
lemma push_positive_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε : ℝ) (logical : PushState n) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : PushMachineMemory g α ε logical st) (v : Fin n)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) (hd : st.scalar.core.ptrs 60=((g.neighbors v).length : ℤ))
    (hDegree : st.scalar.integerMemory (vertexRecordAddress 16 v.val 0)=((g.neighbors v).length : ℤ)) :
    ∃ steps out, MachineEval m g ω pushPositiveCode st steps out ∧ steps ≤ 469*(g.neighbors v).length+390 ∧
      Nonempty (PushMachineMemory g α ε (pushPositiveLogical g α ε logical v) out) ∧
      out.scalar.queries=st.scalar.queries+2*(g.neighbors v).length ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,⟨pma⟩,a12,a13,a40,aI,aQ,aW,aO,aH⟩ := push_scalar_memory m g ω α ε logical st hh pm v (g.neighbors v).length hv hd
  have a60 := (ea.pointer_frame 60 (by decide)).trans hd
  have aDegree : a.scalar.integerMemory (vertexRecordAddress 16 v.val 0)=((g.neighbors v).length : ℤ) := by rw [aI]; exact hDegree
  obtain ⟨u,b,eb,hu,⟨pmb⟩,b40,bQ,bW,bO,bH⟩ := push_support_memory m g ω α ε
    (pushScalarUpdated logical v (g.neighbors v).length) a aH pma v a40 aDegree
  have b60 := (eb.pointer_frame 60 (by decide)).trans a60
  have b13 := (eb.real_register_frame 13 (by decide)).trans a13
  obtain ⟨c,ec,c63,c67,c62,⟨pmc⟩,cQ,cW,cO,cH⟩ := push_neighbors_prepare_memory m g ω α ε
    (pushSupportUpdated (pushScalarUpdated logical v (g.neighbors v).length) v) b bH pmb v b40 b60
  have c13 := (ec.real_register_frame 13 (by decide)).trans b13
  obtain ⟨w,out,ed,hw,⟨pmd⟩,d62,d63,d67,d13,dQ,dW,dO,dH⟩ := push_neighbor_loop_memory m g ω α ε
    ((1-α)*(logical.r v/((g.neighbors v).length : ℝ))) v (g.neighbors v).length 0
    (pushSupportUpdated (pushScalarUpdated logical v (g.neighbors v).length) v) c cH pmc c63 c62 c67 (by omega) c13
  have ex := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  refine ⟨224+(u+(3+w)),out,ex,by omega,?_,by rw [dQ,cQ,bQ,aQ],?_,dO.trans (cO.trans (bO.trans aO)),dH⟩
  · simpa only [pushPositiveLogical,List.drop_zero] using (Nonempty.intro pmd)
  · rw [dW,cW,bW,aW]; push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushNeighborsDenotation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma push_neighbor_updated_r {n : ℕ} (g : InputGraph n) (ε δ : ℝ) (logical : PushState n) (v : Fin n) :
    (pushNeighborUpdated g ε δ logical v).r=Function.update logical.r v (logical.r v+δ) := by
  unfold pushNeighborUpdated pushRefreshed
  split_ifs <;> rfl
lemma push_neighbor_updated_z {n : ℕ} (g : InputGraph n) (ε δ : ℝ) (logical : PushState n) (v : Fin n) :
    (pushNeighborUpdated g ε δ logical v).z=logical.z := by
  unfold pushNeighborUpdated pushRefreshed
  split_ifs <;> rfl
lemma push_neighbor_updated_support {n : ℕ} (g : InputGraph n) (ε δ : ℝ) (logical : PushState n) (v : Fin n) :
    (pushNeighborUpdated g ε δ logical v).support=logical.support := by
  unfold pushNeighborUpdated pushRefreshed
  split_ifs <;> rfl

lemma push_neighbor_updated_queue {n : ℕ} (g : InputGraph n) (ε δ : ℝ) (logical : PushState n) (v : Fin n) :
    (pushNeighborUpdated g ε δ logical v).queue=logical.queue++
      (if v ∉ logical.queue ∧ ε*((g.neighbors v).length : ℝ) < logical.r v+δ then [v] else []) := by
  classical
  simp only [pushNeighborUpdated,pushRefreshed,pushResidualUpdated,Function.update_self]
  by_cases ht : ε*((g.neighbors v).length : ℝ) < logical.r v+δ
  · rw [if_pos ht]
    simp only [pushQueueUpdated]
    by_cases hq : v ∈ logical.queue <;> simp [hq,ht]
  · rw [if_neg ht]
    simp [ht]

lemma push_neighbors_fold_r {n : ℕ} (g : InputGraph n) (ε δ : ℝ) (vertices : List (Fin n))
    (hn : vertices.Nodup) (logical : PushState n) :
    (pushNeighborsFold g ε δ logical vertices).r=fun u => logical.r u+(if u ∈ vertices then δ else 0) := by
  classical
  induction vertices generalizing logical with
  | nil => funext u; simp [pushNeighborsFold]
  | cons v rest ih =>
    rw [List.nodup_cons] at hn
    change (pushNeighborsFold g ε δ (pushNeighborUpdated g ε δ logical v) rest).r= _
    rw [ih hn.2,push_neighbor_updated_r]
    funext u
    by_cases he : u=v
    · subst u
      simp [hn.1]
    · simp only [Function.update_of_ne he,List.mem_cons]
      by_cases hu : u ∈ rest <;> simp [he,hu]

lemma push_neighbors_fold_z {n : ℕ} (g : InputGraph n) (ε δ : ℝ) (vertices : List (Fin n))
    (logical : PushState n) : (pushNeighborsFold g ε δ logical vertices).z=logical.z := by
  induction vertices generalizing logical with
  | nil => rfl
  | cons v rest ih =>
    change (pushNeighborsFold g ε δ (pushNeighborUpdated g ε δ logical v) rest).z= _
    rw [ih,push_neighbor_updated_z]
lemma push_neighbors_fold_support {n : ℕ} (g : InputGraph n) (ε δ : ℝ) (vertices : List (Fin n))
    (logical : PushState n) : (pushNeighborsFold g ε δ logical vertices).support=logical.support := by
  induction vertices generalizing logical with
  | nil => rfl
  | cons v rest ih =>
    change (pushNeighborsFold g ε δ (pushNeighborUpdated g ε δ logical v) rest).support= _
    rw [ih,push_neighbor_updated_support]

lemma push_neighbors_fold_queue {n : ℕ} (g : InputGraph n) (ε δ : ℝ) (vertices : List (Fin n))
    (hn : vertices.Nodup) (logical : PushState n) :
    (pushNeighborsFold g ε δ logical vertices).queue=logical.queue++vertices.filter
      (fun u => u ∉ logical.queue ∧ ε*((g.neighbors u).length : ℝ) < logical.r u+δ) := by
  classical
  induction vertices generalizing logical with
  | nil => simp [pushNeighborsFold]
  | cons v rest ih =>
    rw [List.nodup_cons] at hn
    change (pushNeighborsFold g ε δ (pushNeighborUpdated g ε δ logical v) rest).queue= _
    rw [ih hn.2]
    have hFilter : rest.filter (fun u => u ∉ (pushNeighborUpdated g ε δ logical v).queue ∧
        ε*((g.neighbors u).length : ℝ) < (pushNeighborUpdated g ε δ logical v).r u+δ)=
        rest.filter (fun u => u ∉ logical.queue ∧ ε*((g.neighbors u).length : ℝ) < logical.r u+δ) := by
      apply List.filter_congr
      intro u hu
      have hne : u ≠ v := by intro he; subst u; exact hn.1 hu
      rw [push_neighbor_updated_r,Function.update_of_ne hne,push_neighbor_updated_queue]
      split_ifs <;> simp [hne]
    rw [hFilter,push_neighbor_updated_queue,List.filter_cons]
    by_cases hq : v ∈ logical.queue <;>
      by_cases ht : ε*((g.neighbors v).length : ℝ) < logical.r v+δ <;>
      simp [hq,ht,List.append_assoc]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushPositiveDenotation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2200000 in
lemma push_positive_denotation {n : ℕ} (g : InputGraph n) (α ε : ℝ) (logical : PushState n)
    (v : Fin n) (rest : List (Fin n)) (hq : logical.queue=v::rest) (hn : logical.queue.Nodup)
    (hQ : logical.queued=logical.queue.toFinset) (hdone : logical.done=false)
    (ht : ε*((g.neighbors v).length : ℝ) < logical.r v) :
    let online := pushPositiveLogical g α ε (pushDequeued logical v rest) v
    online.z=(pushStep g α ε logical).z ∧ online.r=(pushStep g α ε logical).r ∧
      online.queue=(pushStep g α ε logical).queue ∧ online.support=(pushStep g α ε logical).support := by
  classical
  have hd : LocalPush.deg g.graph v=((g.neighbors v).length : ℝ) := by
    simp [LocalPush.deg,input_degree]
  have hs : ε*LocalPush.deg g.graph v < logical.r v := by rw [hd]; exact ht
  have hn' := List.nodup_cons.mp (hq ▸ hn)
  have hQ' : logical.queued.erase v=rest.toFinset := by
    simp [hQ,hq,hn'.1]
  dsimp only
  simp only [pushStep,hdone,Bool.false_eq_true,if_false,hq,hs,if_true]
  dsimp only [pushPositiveLogical]
  refine ⟨?_,?_,?_,?_⟩
  · rw [push_neighbors_fold_z]
    simp only [pushSupportUpdated,pushScalarUpdated,pushDequeued,hd]
  · rw [push_neighbors_fold_r g ε _ _ (g.nodup v)]
    funext u
    simp only [pushSupportUpdated,pushScalarUpdated,pushDequeued,hd,Function.update_apply]
  · rw [push_neighbors_fold_queue g ε _ _ (g.nodup v)]
    simp only [pushSupportUpdated,pushScalarUpdated,pushDequeued,hQ']
    congr 1
    apply List.filter_congr
    intro u hu
    simp [hd,Function.update_apply,hu,LocalPush.deg,input_degree]
  · rw [push_neighbors_fold_support]
    rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushIterationExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 3200000 in
lemma push_iteration_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε : ℝ) (logical : PushState n) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : PushMachineMemory g α ε logical st) (v : Fin n) (rest : List (Fin n))
    (hq : logical.queue=v::rest) (hn : logical.queue.Nodup)
    (hQ : logical.queued=logical.queue.toFinset) (hdone : logical.done=false) :
    ∃ steps out, MachineEval m g ω pushIterationCode st steps out ∧
      steps ≤ 200*((pushStep g α ε logical).work-logical.work) ∧
      Nonempty (PushMachineMemory g α ε (pushStep g α ε logical) out) ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a40,⟨pma⟩,aQ,aW,aO,aH⟩ := push_dequeue_memory m g ω α ε logical st hh pm v rest hq hn
  obtain ⟨b,eb,b60,bDegree,⟨pmb⟩,bQ,bW,bO,bH⟩ := push_degree_memory m g ω α ε (pushDequeued logical v rest) a aH pma v a40
  have b40 := (eb.pointer_frame 40 (by decide)).trans a40
  obtain ⟨c,ec,hTest,⟨pmc⟩,c40,cQ,cW,cO,cH⟩ := push_eligibility_memory m g ω α ε (pushDequeued logical v rest) b bH pmb v b40 bDegree
  have c60 : c.scalar.core.ptrs 60=((g.neighbors v).length : ℤ) :=
    (push_eligibility_degree m g ω b c 150 bH 16 v.val pmb.zeroPointer b40 pmb.widthPointer ec).trans bDegree
  have cDegree : c.scalar.integerMemory (vertexRecordAddress 16 v.val 0)=((g.neighbors v).length : ℤ) := by
    rw [ec.integer_memory_frame (by decide)]
    exact bDegree
  have hd : LocalPush.deg g.graph v=((g.neighbors v).length : ℝ) := by simp [LocalPush.deg,input_degree]
  by_cases ht : ε*((g.neighbors v).length : ℝ) < logical.r v
  · have ht' : ε*((g.neighbors v).length : ℝ) < (pushDequeued logical v rest).r v := ht
    obtain ⟨u,d,ed,hu,⟨pmd⟩,dQ,dW,dO,dH⟩ := push_positive_memory m g ω α ε
      (pushDequeued logical v rest) (payUnit c) cH pmc.payUnit v c40 c60 cDegree
    have ee : MachineEval m g ω (.branchReal 23 .skip pushPositiveCode) c (1+u+1) (payUnit d) :=
      MachineEval.realPos cH (not_le.mpr (hTest.mpr ht')) ed
    have ex := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ee))
    have he := push_positive_denotation g α ε logical v rest hq hn hQ hdone ht
    have pmOut := pmd.payUnit.agree he.1.symm he.2.1.symm he.2.2.1.symm he.2.2.2.symm
    refine ⟨81+(74+(150+(1+u+1))),payUnit d,ex,?_,⟨pmOut⟩,?_,dO.trans (cO.trans (bO.trans aO)),dH⟩
    · have hs : ε*LocalPush.deg g.graph v < logical.r v := by rw [hd]; exact ht
      simp only [pushStep,hdone,Bool.false_eq_true,if_false,hq,hs,if_true,Nat.add_sub_cancel_left]
      omega
    · change d.work+1= _
      rw [dW,payUnit_work,cW,bW,aW]; push_cast; ring
  · have ht' : ¬ ε*((g.neighbors v).length : ℝ) < (pushDequeued logical v rest).r v := ht
    have hn23 : c.scalar.core.regs 23 ≤ 0 := le_of_not_gt (fun h => ht' (hTest.mp h))
    have ed : MachineEval m g ω (.branchReal 23 .skip pushPositiveCode) c 1 (payUnit c) :=
      MachineEval.realNonpos cH hn23 (MachineEval.skip (payUnit c))
    have ex := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
    have hs : ¬ ε*LocalPush.deg g.graph v < logical.r v := by rw [hd]; exact ht
    have he : pushStep g α ε logical={ logical with queue := rest, queued := logical.queued.erase v, work := logical.work+4 } := by
      simp [pushStep,hdone,hq,hs]
    have pmOut := pmc.payUnit.agree (b:=pushStep g α ε logical) (by rw [he]; rfl) (by rw [he]; rfl) (by rw [he]; rfl) (by rw [he]; rfl)
    refine ⟨306,payUnit c,ex,?_,⟨pmOut⟩,?_,cO.trans (bO.trans aO),cH⟩
    · rw [he]; simp
    · change c.work+1= _
      rw [cW,bW,aW]; norm_num; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushStepIterationFacts

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma push_step_work_mono {n : ℕ} (g : InputGraph n) (α ε : ℝ) (logical : PushState n) :
    logical.work ≤ (pushStep g α ε logical).work := by
  unfold pushStep
  split_ifs
  · exact le_rfl
  · split <;> dsimp only
    · omega
    · split_ifs <;> simp only <;> omega

lemma push_iterate_work_mono {n : ℕ} (g : InputGraph n) (α ε : ℝ) (logical : PushState n) (t : ℕ) :
    logical.work ≤ ((pushStep g α ε)^[t] logical).work := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (push_step_work_mono g α ε _)

lemma push_step_work_increase {n : ℕ} (g : InputGraph n) (α ε : ℝ) (logical : PushState n)
    (h : logical.done=false) (hne : logical.queue ≠ []) :
    logical.work+4 ≤ (pushStep g α ε logical).work := by
  cases hq : logical.queue with
  | nil => exact (hne hq).elim
  | cons v rest =>
    simp only [pushStep,h,Bool.false_eq_true,if_false,hq]
    split_ifs <;> simp only <;> omega

lemma push_empty_iterate_agrees {n : ℕ} (g : InputGraph n) (α ε : ℝ) (logical : PushState n)
    (hq : logical.queue=[]) (t : ℕ) :
    let final := (pushStep g α ε)^[t] logical
    final.z=logical.z ∧ final.r=logical.r ∧ final.queue=[] ∧ final.support=logical.support := by
  induction t generalizing logical with
  | zero => exact ⟨rfl,rfl,hq,rfl⟩
  | succ t ih =>
    have he : (pushStep g α ε logical).queue=[] ∧ (pushStep g α ε logical).z=logical.z ∧
        (pushStep g α ε logical).r=logical.r ∧ (pushStep g α ε logical).support=logical.support := by
      unfold pushStep
      split_ifs <;> simp_all
    rw [Function.iterate_succ_apply]
    obtain ⟨hz,hr,hq',hs⟩ := ih (pushStep g α ε logical) he.1
    exact ⟨hz.trans he.2.1,hr.trans he.2.2.1,hq',hs.trans he.2.2.2⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushWhileExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 3200000 in
lemma push_while_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (s : Fin n) (ω : ℕ → Bool)
    (α ε : ℝ) (hα : 0 < α ∧ α < 1) (hε : 0 < ε) (t : ℕ) :
    ∀ (logical : PushState n) (st : MachineState), st.scalar.halted=false →
    PushMachineMemory g α ε logical st → PushInvariant g s α ε logical →
    ((pushStep g α ε)^[t] logical).queue=[] →
    ∃ steps out, MachineEval m g ω pushWhileCode st steps out ∧
      steps ≤ 201*(((pushStep g α ε)^[t] logical).work-logical.work)+1 ∧
      Nonempty (PushMachineMemory g α ε ((pushStep g α ε)^[t] logical) out) ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction t with
  | zero =>
    intro logical st hh pm hinv hq
    change logical.queue=[] at hq
    have h90 : st.scalar.core.ptrs 90=0 := pm.queue.zero_iff.mpr hq
    refine ⟨1,payUnit st,MachineEval.pointerDone hh (by rw [h90,pm.zeroPointer]),?_,⟨pm.payUnit⟩,by simp [payUnit,pcSet],rfl,hh⟩
    simp
  | succ t ih =>
    intro logical st hh pm hinv hqFinal
    cases hq : logical.queue with
    | nil =>
      have h90 : st.scalar.core.ptrs 90=0 := pm.queue.zero_iff.mpr hq
      have he := push_empty_iterate_agrees g α ε logical hq (t+1)
      have pmOut := pm.payUnit.agree (b:=(pushStep g α ε)^[t+1] logical) he.1 he.2.1 (he.2.2.1.trans hq.symm) he.2.2.2
      refine ⟨1,payUnit st,MachineEval.pointerDone hh (by rw [h90,pm.zeroPointer]),by omega,⟨pmOut⟩,by simp [payUnit,pcSet],rfl,hh⟩
    | cons v rest =>
      have hne : logical.queue ≠ [] := by rw [hq]; simp
      have hd : logical.done=false := Bool.eq_false_iff.mpr (fun h => hne (hinv.done_queue h))
      have hp : 0 < st.scalar.core.ptrs 90 := by
        have hlist := pm.queue.to_list
        rw [hq,List.map_cons] at hlist
        obtain ⟨next,S,hpos,_⟩ := hlist.cons_view
        omega
      obtain ⟨u,mid,eb,hu,⟨pmMid⟩,hmW,hmO,hmH⟩ := push_iteration_memory m g ω α ε logical
        (payUnit st) hh pm.payUnit v rest hq hinv.queue_nodup hinv.queued_eq hd
      have hqNext : ((pushStep g α ε)^[t] (pushStep g α ε logical)).queue=[] := by
        simpa only [Function.iterate_succ_apply] using hqFinal
      have hiNext := push_step_invariant g s α ε hα hε logical hinv
      obtain ⟨w,out,er,hw,⟨pmOut⟩,hoW,hoO,hoH⟩ := ih (pushStep g α ε logical) (payUnit mid) hmH pmMid.payUnit hiNext hqNext
      have ex : MachineEval m g ω pushWhileCode st (1+u+1+w) out :=
        MachineEval.pointerNext hh (by rw [pm.zeroPointer]; omega) eb er
      refine ⟨1+u+1+w,out,ex,?_,?_,?_,hoO.trans hmO,hoH⟩
      · have hinc := push_step_work_increase g α ε logical hd hne
        have hm := push_iterate_work_mono g α ε (pushStep g α ε logical) t
        rw [Function.iterate_succ_apply]
        omega
      · simpa only [Function.iterate_succ_apply] using (Nonempty.intro pmOut)
      · rw [hoW,payUnit_work,hmW,payUnit_work]; push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushOutputBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2200000 in
lemma push_output_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (head next : ℤ) (v : Fin n) (α z : ℝ)
    (h0 : st.scalar.core.ptrs 0=0) (h41 : st.scalar.core.ptrs 41=16) (hhead : st.scalar.core.ptrs 94=head)
    (hkey : st.scalar.integerMemory head=(v.val : ℤ)) (hnext : st.scalar.integerMemory (head+2)=next)
    (hdeg : st.scalar.integerMemory (vertexRecordAddress 16 v.val 0)=((g.neighbors v).length : ℤ))
    (ha : st.scalar.core.regs 30=α) (hz : st.scalar.core.mem (vertexRecordAddress 16 v.val 0)=z) :
    ∃ out, MachineEval m g ω pushOutputBodyCode st 154 out ∧ out.scalar.core.ptrs 94=next ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+154 ∧
      out.output=st.output++[((v.val : ℤ),α*((g.neighbors v).length : ℝ)*z)] ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a40,a94,a44,aI,aR,aQ,aW,aO,aH⟩ := push_output_read_exec m g ω st hh head next v hhead hkey hnext
  have a0 := (ea.pointer_frame 0 (by decide)).trans h0
  have a41 := (ea.pointer_frame 41 (by decide)).trans h41
  obtain ⟨b,eb,b10,bI,bR,bW,bO,bH⟩ := vertex_real_load_exec m g ω a aH 16 v.val 0 a0 a40 a41 a44
  have b0 := (eb.pointer_frame 0 (by decide)).trans a0
  have b40 := (eb.pointer_frame 40 (by decide)).trans a40
  have b41 := (eb.pointer_frame 41 (by decide)).trans a41
  have b10' : b.scalar.core.regs 10=z := by rw [b10,aR]; exact hz
  obtain ⟨c,ec,c60,cI,cR,cQ,cW,cO,cH⟩ := vertex_field_read_exec m g ω b bH 16 v.val 0 60 b0 b40 b41
  have c60' : c.scalar.core.ptrs 60=((g.neighbors v).length : ℤ) := by rw [c60,bI,aI]; exact hdeg
  have c40 := (ec.pointer_frame 40 (by decide)).trans b40
  have c10 := (ec.real_register_frame 10 (by decide)).trans b10'
  have c30 := (ec.real_register_frame 30 (by decide)).trans ((eb.real_register_frame 30 (by decide)).trans ((ea.real_register_frame 30 (by decide)).trans ha))
  obtain ⟨out,ed,dI,dR,dQ,dW,dO,dH⟩ := push_output_scalar_exec m g ω c cH v α z (g.neighbors v).length c40 c60' c30 c10
  have ex : MachineEval m g ω pushOutputBodyCode st 154 out := by
    have e := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
    convert e using 1 <;> rfl
  refine ⟨out,ex,?_,dI.trans (cI.trans (bI.trans aI)),dR.trans (cR.trans (bR.trans aR)),ex.query_frame (by decide),?_,?_,dH⟩
  · exact (ed.pointer_frame 94 (by decide)).trans ((ec.pointer_frame 94 (by decide)).trans ((eb.pointer_frame 94 (by decide)).trans a94))
  · rw [dW,cW,bW,aW]; norm_num; ring
  · rw [dO,cO,bO,aO]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushOutputLoop

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 2400000 in
lemma push_output_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (vertices : List (Fin n)) (head : ℤ) (F : Finset ℤ) (α : ℝ) (z : Fin n → ℝ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (h41 : st.scalar.core.ptrs 41=16) (hhead : st.scalar.core.ptrs 94=head)
    (h : VertexListRep st.scalar.integerMemory head vertices F) (ha : st.scalar.core.regs 30=α)
    (hz : ∀ v ∈ vertices, st.scalar.core.mem (vertexRecordAddress 16 v.val 0)=z v)
    (hdeg : ∀ v ∈ vertices, st.scalar.integerMemory (vertexRecordAddress 16 v.val 0)=((g.neighbors v).length : ℤ)) :
    ∃ out, MachineEval m g ω pushOutputLoopCode st (156*vertices.length+1) out ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(156*vertices.length+1 : ℕ) ∧
      out.output=st.output++vertices.map (fun v => ((v.val : ℤ),α*((g.neighbors v).length : ℝ)*z v)) ∧ out.scalar.halted=false := by
  induction vertices generalizing st head F with
  | nil =>
    have hhead' : st.scalar.core.ptrs 94=0 := hhead.trans h.nil.1
    refine ⟨payUnit st,MachineEval.pointerDone hh (by rw [hhead',h0]),rfl,rfl,rfl,by simp [payUnit,pcSet],by simp [payUnit,pcSet],hh⟩
  | cons v vertices ih =>
    obtain ⟨next,S,hpos,hkey,hchild,hnext,hTail,hF,hsep⟩ := h.cons_view
    obtain ⟨mid,eb,hm94,hmI,hmR,hmQ,hmW,hmO,hmH⟩ := push_output_body_exec m g ω (payUnit st) hh head next v α (z v)
      h0 h41 hhead hkey hnext (hdeg v (by simp)) ha (hz v (by simp))
    have hm0 := (eb.pointer_frame 0 (by decide)).trans h0
    have hm41 := (eb.pointer_frame 41 (by decide)).trans h41
    have hm30 := (eb.real_register_frame 30 (by decide)).trans ha
    have hmTail : VertexListRep mid.scalar.integerMemory next vertices S := by rw [hmI]; exact hTail
    have hmz : ∀ u ∈ vertices, mid.scalar.core.mem (vertexRecordAddress 16 u.val 0)=z u := by
      intro u hu; rw [hmR]; exact hz u (by simp [hu])
    have hmd : ∀ u ∈ vertices, mid.scalar.integerMemory (vertexRecordAddress 16 u.val 0)=((g.neighbors u).length : ℤ) := by
      intro u hu; rw [hmI]; exact hdeg u (by simp [hu])
    obtain ⟨out,er,hoI,hoR,hoQ,hoW,hoO,hoH⟩ := ih next S (payUnit mid) hmH hm0 hm41 hm94 hmTail hm30 hmz hmd
    have ex : MachineEval m g ω pushOutputLoopCode st (156*(v::vertices).length+1) out := by
      have e := MachineEval.pointerNext (r:=94) (s:=0) hh (by rw [hhead,h0]; omega) eb er
      convert e using 1 <;> (first | rfl | simp [List.length_cons]; omega)
    refine ⟨out,ex,hoI.trans hmI,hoR.trans hmR,hoQ.trans hmQ,?_,?_,hoH⟩
    · rw [hoW,payUnit_work,hmW,payUnit_work]
      push_cast
      simp only [List.length_cons]
      push_cast
      ring
    · rw [hoO]
      change mid.output++_ = _
      rw [hmO]
      simp [payUnit,pcSet,List.append_assoc]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushOutputExecution

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1600000 in
lemma push_output_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (α ε : ℝ) (logical : PushState n) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : PushMachineMemory g α ε logical st) (hOut : st.output=[])
    (hz : ∀ v ∉ logical.support, logical.z v=0) :
    ∃ out, MachineEval m g ω pushOutputCode st (156*logical.support.card+2) out ∧
      outputVector out.output=potentialOutput g.graph α logical.z ∧
      out.work=st.work+(156*logical.support.card+2 : ℕ) ∧ out.scalar.halted=false := by
  let a := payUnit (pointerWrite st 94 (st.scalar.core.ptrs 92))
  have ea : MachineEval m g ω (coreCode (.pcopy 94 92)) st 1 a := pcopy_eval m g ω st 94 92 hh
  have a0 := (ea.pointer_frame 0 (by decide)).trans pm.zeroPointer
  have a41 := (ea.pointer_frame 41 (by decide)).trans pm.widthPointer
  have a30 := (ea.real_register_frame 30 (by decide)).trans pm.alphaRegister
  have a94 : a.scalar.core.ptrs 94=st.scalar.core.ptrs 92 := by simp [a,payUnit,pcSet,pointerWrite]
  have hdeg : ∀ v ∈ pm.supportVertices, a.scalar.integerMemory (vertexRecordAddress 16 v.val 0)=((g.neighbors v).length : ℤ) := by
    intro v hv
    apply pm.supportDegree v
    rw [←pm.supportSet]
    simpa using hv
  obtain ⟨out,eb,hI,hR,hQ,hW,hO,hH⟩ := push_output_loop_exec m g ω pm.supportVertices (st.scalar.core.ptrs 92) pm.supportCells α logical.z
    a hh a0 a41 a94 pm.support a30 (fun v hv => pm.potential v) hdeg
  have hLength : pm.supportVertices.length=logical.support.card := by
    rw [←pm.supportSet,List.toFinset_card_of_nodup pm.supportNodup]
  have ex : MachineEval m g ω pushOutputCode st (156*logical.support.card+2) out := by
    have e := MachineEval.seq ea eb
    convert e using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,?_,?_,hH⟩
  · have ho : out.output=pm.supportVertices.map (fun v => ((v.val : ℤ),α*((g.neighbors v).length : ℝ)*logical.z v)) := by
      simpa only [a,payUnit,pcSet,pointerWrite,hOut,List.nil_append] using hO
    rw [ho]
    exact push_output_list_potential g α logical pm.supportVertices pm.supportNodup pm.supportSet hz
  · rw [hW]
    change st.work+1+(156*pm.supportVertices.length+1 : ℕ)= _
    rw [hLength]; push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushSupportWork

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma push_step_support_work {n : ℕ} (g : InputGraph n) (α ε : ℝ) (logical : PushState n)
    (h : logical.support.card ≤ logical.work) :
    (pushStep g α ε logical).support.card ≤ (pushStep g α ε logical).work := by
  classical
  by_cases hd : logical.done=true
  · simpa [pushStep,hd] using h
  · have hf : logical.done=false := Bool.eq_false_iff.mpr hd
    cases hq : logical.queue with
    | nil =>
      simp only [pushStep,hf,Bool.false_eq_true,if_false,hq]
      omega
    | cons v rest =>
      simp only [pushStep,hf,Bool.false_eq_true,if_false,hq]
      by_cases ht : ε*LocalPush.deg g.graph v < logical.r v
      · simp only [if_pos ht]
        have hc := Finset.card_insert_le (s:=logical.support) v
        omega
      · simp only [if_neg ht]
        omega

lemma push_run_support_work {n : ℕ} (g : InputGraph n) (s : Fin n) (α ε : ℝ) (t : ℕ) :
    (pushRun g s α ε t).support.card ≤ (pushRun g s α ε t).work := by
  induction t with
  | zero => simp [pushRun,pushInit]
  | succ t ih =>
    simpa only [pushRun,Function.iterate_succ_apply'] using push_step_support_work g α ε (pushRun g s α ε t) ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushCoreExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2400000 in
lemma push_core_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε) (hs : 0 < g.graph.degree s)
    (hseed : st.scalar.integerMemory 0=(s.val : ℤ)) (ha : st.scalar.core.mem 0=α) (he : st.scalar.core.mem 1=ε)
    (hIz : ∀ z, z < 0 → st.scalar.integerMemory z=0) (hRz : ∀ z, z < 0 → st.scalar.core.mem z=0)
    (hOut : st.output=[]) (t : ℕ) (ht : (pushRun g s α ε t).done=true) :
    ∃ steps out, MachineEval m g ω pushCoreCode st steps out ∧ steps ≤ 500*(pushRun g s α ε t).work ∧
      outputVector out.output=potentialOutput g.graph α (pushRun g s α ε t).z ∧
      out.work=st.work+steps ∧ out.scalar.halted=false := by
  obtain ⟨u,a,ea,hu,⟨pma⟩,aQ,aW,aO,aH⟩ := push_init_exec m g ω st hh s α ε hseed ha he hIz hRz
  have hInv := push_run_invariant g s α ε hα hε hs t
  obtain ⟨v,b,eb,hv,⟨pmb⟩,bW,bO,bH⟩ := push_while_memory m g s ω α ε hα hε t (pushInit s) a aH pma
    (push_init_invariant g s α ε hε hs) (hInv.done_queue ht)
  have bOut : b.output=[] := bO.trans (aO.trans hOut)
  obtain ⟨out,ec,cVector,cW,cH⟩ := push_output_memory m g ω α ε (pushRun g s α ε t) b bH pmb bOut hInv.support_z
  have ex := MachineEval.seq ea (MachineEval.seq eb ec)
  have hCard := push_run_support_work g s α ε t
  have hLow : 4 ≤ (pushRun g s α ε t).work := by
    simpa only [pushRun,pushInit] using push_iterate_work_mono g α ε (pushInit s) t
  change v ≤ 201*((pushRun g s α ε t).work-4)+1 at hv
  refine ⟨u+(v+(156*(pushRun g s α ε t).support.card+2)),out,ex,by omega,cVector,?_,cH⟩
  rw [cW,bW,aW]; push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushCoreBound

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2000000 in
lemma push_core_bound (m : SolveModel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ω : ℕ → Bool)
      (st : MachineState), 0 < α → α < 1 → 0 < ε → ε ≤ 1 → 0 < g.graph.degree s →
      st.scalar.halted=false → st.scalar.integerMemory 0=(s.val : ℤ) → st.scalar.core.mem 0=α → st.scalar.core.mem 1=ε →
      (∀ z, z < 0 → st.scalar.integerMemory z=0) → (∀ z, z < 0 → st.scalar.core.mem z=0) → st.output=[] →
      ∃ steps out, MachineEval m g ω pushCoreCode st steps out ∧
        (steps : ℝ≥0∞) ≤ ENNReal.ofReal (C/(α*ε)) ∧
        ACL g.graph α ε s (outputVector out.output) ∧ (∀ v : Fin n, 0 ≤ outputVector out.output v) ∧
        out.work=st.work+steps ∧ out.scalar.halted=false := by
  obtain ⟨C,hC,hSource⟩ := push_correctness_work
  refine ⟨500*C,by positivity,?_⟩
  intro n g s α ε ω st ha ha1 he he1 hs hh hseed hα hε hIz hRz hOut
  obtain ⟨hWork,t,ht,hz,hr,hVector,hACL⟩ := hSource n g s α ε ha ha1 he he1 hs
  obtain ⟨u,out,ex,hu,hV,hW,hH⟩ := push_core_exec m g ω st hh s α ε ⟨ha,ha1⟩ he hs hseed hα hε hIz hRz hOut t ht
  have hT : ((pushRun g s α ε t).work : ℝ≥0∞) ≤ pushWork g s α ε := by
    unfold pushWork
    rw [if_pos ⟨t,ht⟩]
    exact le_iSup (fun t => ((pushRun g s α ε t).work : ℝ≥0∞)) t
  have hU : (u : ℝ≥0∞) ≤ (500 : ℝ≥0∞)*((pushRun g s α ε t).work : ℝ≥0∞) := by exact_mod_cast hu
  have hBound : (u : ℝ≥0∞) ≤ ENNReal.ofReal (500*C/(α*ε)) := by
    calc
      _ ≤ 500*((pushRun g s α ε t).work : ℝ≥0∞) := hU
      _ ≤ 500*pushWork g s α ε := by gcongr
      _ ≤ 500*ENNReal.ofReal (C/(α*ε)) := by gcongr
      _ = ENNReal.ofReal (500*C/(α*ε)) := by
        rw [show (500 : ℝ≥0∞)=ENNReal.ofReal (500 : ℝ) by norm_num,←ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
  refine ⟨u,out,ex,hBound,?_,?_,hW,hH⟩
  · rw [hV,←hVector]
    exact hACL
  · intro v
    rw [hV]
    exact mul_nonneg (mul_nonneg ha.le (by unfold LocalPush.deg; positivity)) (hz v)

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution : ∀ (m : SolveModel),
∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ω : ℕ → Bool)
      (st : MachineState), 0 < α → α < 1 → 0 < ε → ε ≤ 1 → 0 < g.graph.degree s →
      st.scalar.halted=false → st.scalar.integerMemory 0=(s.val : ℤ) → st.scalar.core.mem 0=α → st.scalar.core.mem 1=ε →
      (∀ z, z < 0 → st.scalar.integerMemory z=0) → (∀ z, z < 0 → st.scalar.core.mem z=0) → st.output=[] →
      ∃ steps out, MachineEval m g ω pushCoreCode st steps out ∧
        (steps : ℝ≥0∞) ≤ ENNReal.ofReal (C/(α*ε)) ∧
        ACL g.graph α ε s (outputVector out.output) ∧ (∀ v : Fin n, 0 ≤ outputVector out.output v) ∧
        out.work=st.work+steps ∧ out.scalar.halted=false := by
  exact @NearlyOptimalPPR.Computation.push_core_bound
