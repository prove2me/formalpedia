-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.priority_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:26:05.86518+00:00
-- url     : https://prove2.me/submissions/98507f7b-0ef7-459e-89af-e7c8b17f6e29

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

-- Proof module: Solutions.BinomialQueue

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp

instance keyLE_total : Batteries.TotalBLE keyLE where
  total := by simp only [keyLE,decide_eq_true_eq]; omega

lemma node_lower_bound (a r : ℕ) (t : HeapNode ℕ) (h : t.WF keyLE a r) :
    ∀ v ∈ nodeSupport t, a ≤ v := by
  induction t generalizing a r with
  | nil => simp [nodeSupport]
  | node b c s ic is =>
    obtain ⟨r',hr,hab,hc,hs⟩ := h
    intro v hv
    simp only [nodeSupport,Finset.mem_insert,Finset.mem_union] at hv
    rcases hv with rfl|hv|hv
    · simpa only [keyLE,decide_eq_true_eq] using hab
    · have hh : a ≤ b := by simpa only [keyLE,decide_eq_true_eq] using hab
      exact hh.trans (ic b r' hc v hv)
    · exact is a r' hs v hv

end SparseQueue
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

lemma SlotRep.root_nonnegative {I : ℤ → ℤ} {p : ℤ} {v : Option RankedTree} {F : Finset ℤ}
    (h : SlotRep I p v F) : 0 ≤ p := by
  cases v with
  | none => rcases h with ⟨rfl,h⟩; omega
  | some t => have hh := h.root_view.choose_spec.choose_spec.1; omega

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

-- Proof module: Solutions.MinScanRoutine

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def chooseMinRoutine : PointerRoutine := .sequence [
  .atom (.copy 27 29),.atom (.copy 28 26),.atom (.copy 31 30)]

def compareMinRoutine : PointerRoutine := .branch 27 0 chooseMinRoutine
  (.branch 30 31 chooseMinRoutine .skip)

def inspectMinRoutine : PointerRoutine := .branch 29 0 .skip
  (.seq (.atom (.load 30 29)) compareMinRoutine)

def minScanBodyRoutine : PointerRoutine := .sequence [
  .atom (.add 32 13 26),.atom (.load 29 32),inspectMinRoutine,.atom (.inc 26)]

lemma minScanBodyRoutine_code : minScanBodyRoutine.code=minScanBodyCode := rfl

set_option maxHeartbeats 800000 in
lemma min_scan_body_run (I : ℤ → ℤ) (P : ℕ → ℤ) :
    let root := I (P 13+P 26)
    let pick := ¬root ≤ P 0 ∧ (P 27 ≤ P 0 ∨ I root ≤ P 31)
    let result := minScanBodyRoutine.run I P
    result.1 ≤ 12 ∧ result.2 26=P 26+1 ∧
      result.2 27=(if pick then root else P 27) ∧
      result.2 28=(if pick then P 26 else P 28) ∧
      result.2 31=(if pick then I root else P 31) := by
  by_cases hr : I (P 13+P 26) ≤ P 0 <;>
    by_cases hb : P 27 ≤ P 0 <;>
    by_cases hk : I (I (P 13+P 26)) ≤ P 31
  all_goals
    simp [minScanBodyRoutine,inspectMinRoutine,compareMinRoutine,chooseMinRoutine,
      PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,
      PointerOp.result,hr,hb,hk]

end
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

-- Proof module: Solutions.SequenceComposition

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma MachineEval.sequence_continue {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    (codes : List MachineCode) {b : MachineCode} {st mid out : MachineState} {u v : ℕ}
    (ea : MachineEval m g ω (sequenceCode codes) st u mid)
    (eb : MachineEval m g ω b mid v out) :
    MachineEval m g ω (sequenceCode (codes++[b])) st (u+v) out := by
  induction codes generalizing st mid u with
  | nil =>
    cases ea
    simpa [sequenceCode] using MachineEval.seq eb (MachineEval.skip out)
  | cons a codes ih =>
    change MachineEval m g ω (.seq a (sequenceCode codes)) st u mid at ea
    cases ea with
    | seq e0 e1 =>
      have e := MachineEval.seq e0 (ih e1 eb)
      convert e using 1 <;> (first | rfl | omega)

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

lemma QueuedFlags.clear {n : ℕ} {I : ℤ → ℤ} {width offset : ℕ} {domain : Finset (Fin n)} {queued : Finset ℕ}
    (h : QueuedFlags I width offset domain queued) (hoff : offset < width) (v : Fin n) :
    QueuedFlags (Function.update I (vertexRecordAddress width v.val offset) 0)
      width offset domain (queued.erase v.val) := by
  intro u hu
  by_cases he : u=v
  · subst u
    simp
  · have hval : u.val ≠ v.val := by intro h; exact he (Fin.ext h)
    rw [vertex_integer_update_other_vertex I width v.val u.val offset offset 0 hoff hoff hval,h u hu]
    simp [hval]

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

-- Proof module: Solutions.HeapDetach

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section

set_option maxHeartbeats 500000 in
lemma ForestRep.detach {I : ℤ → ℤ} {p : ℤ} {a : ℕ} {c s : HeapNode ℕ} {F : Finset ℤ}
    (h : ForestRep I p (.node a c s) F) :
    ∃ cp sp C S, I (p+1)=cp ∧ I (p+2)=sp ∧ F=nodeCells p ∪ C ∪ S ∧
      ForestRep (Function.update I (p+2) 0) p (.node a c .nil) (nodeCells p ∪ C) ∧
      ForestRep (Function.update I (p+2) 0) sp s S ∧ Disjoint (nodeCells p ∪ C) S ∧
      (∀ z, z ∉ F → Function.update I (p+2) 0 z=I z) := by
  cases h with
  | node p a cp sp c s C S hp hk hc hs rc rs hdC hdS hdCS =>
    have hC : p+2 ∉ C := by
      intro h
      exact Finset.disjoint_left.mp hdC (by simp [nodeCells]) h
    have hS : p+2 ∉ S := by
      intro h
      exact Finset.disjoint_left.mp hdS (by simp [nodeCells]) h
    have hc' : ForestRep (Function.update I (p+2) 0) cp c C := rc.frame_write_outside hC
    have hs' : ForestRep (Function.update I (p+2) 0) sp s S := rs.frame_write_outside hS
    have hk' : Function.update I (p+2) 0 p=(a : ℤ) := by simp [Function.update_of_ne (by omega : p ≠ p+2),hk]
    have hch' : Function.update I (p+2) 0 (p+1)=cp := by simp [Function.update_of_ne (by omega : p+1 ≠ p+2),hc]
    have hrep := ForestRep.node p a cp 0 c .nil C ∅ hp hk' hch' (by simp) hc' ForestRep.nil hdC (by simp) (by simp)
    refine ⟨cp,sp,C,S,hc,hs,rfl,?_,hs',Finset.disjoint_union_left.mpr ⟨hdS,hdCS⟩,?_⟩
    · simpa using hrep
    · intro z hz
      apply Function.update_of_ne
      intro he
      subst z
      exact hz (by simp [nodeCells])

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapDetachCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma heapDetachCode_wellFormed : heapDetachCode.wellFormed := by
  simp [heapDetachCode,sequenceCode,coreCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 800000 in
lemma heap_detach_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω heapDetachCode st 6 out ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (st.scalar.core.ptrs 5+2) 0 ∧
      out.scalar.core.ptrs 5=st.scalar.core.ptrs 5 ∧
      out.scalar.core.ptrs 22=st.scalar.integerMemory (st.scalar.core.ptrs 5+2) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+6 ∧ out.output=st.output := by
  let P := st.scalar.core.ptrs 5
  let I := st.scalar.integerMemory
  let A := payUnit (pointerWrite st 0 0)
  let B := payUnit (pointerWrite A 23 P)
  let C := payUnit (pointerWrite B 23 (P+1))
  let D := payUnit (pointerWrite C 23 (P+2))
  let E := payUnit (pointerWrite D 22 (I (P+2)))
  let out := payUnit (integerWrite E (P+2) 0)
  have ah : A.scalar.halted=false := by simp [A,payUnit,pcSet,pointerWrite,hh]
  have bh : B.scalar.halted=false := by simp [B,payUnit,pcSet,pointerWrite,ah]
  have ch : C.scalar.halted=false := by simp [C,payUnit,pcSet,pointerWrite,bh]
  have dh : D.scalar.halted=false := by simp [D,payUnit,pcSet,pointerWrite,ch]
  have eh : E.scalar.halted=false := by simp [E,payUnit,pcSet,pointerWrite,dh]
  have ea := pset_eval m g ω st 0 0 hh
  have eb : MachineEval m g ω (coreCode (.pcopy 23 5)) A 1 B := by
    have hp : A.scalar.core.ptrs 5=P := by simp [A,payUnit,pcSet,pointerWrite,P]
    simpa only [B,coreCode,hp] using pcopy_eval m g ω A 23 5 ah
  have ec : MachineEval m g ω (coreCode (.pinc 23)) B 1 C := by
    have hp : B.scalar.core.ptrs 23=P := by simp [B,payUnit,pcSet,pointerWrite]
    simpa only [C,coreCode,hp] using pinc_eval m g ω B 23 bh
  have ed : MachineEval m g ω (coreCode (.pinc 23)) C 1 D := by
    have hp : C.scalar.core.ptrs 23=P+1 := by simp [C,payUnit,pcSet,pointerWrite]
    simpa [D,coreCode,hp,Int.add_assoc] using pinc_eval m g ω C 23 ch
  have ee : MachineEval m g ω (.atom (.scalar (.integerLoad 22 23))) D 1 E := by
    have hv : D.scalar.integerMemory (D.scalar.core.ptrs 23)=I (P+2) := by simp [D,C,B,A,payUnit,pcSet,pointerWrite,I]
    simpa only [E,hv] using integerLoad_eval m g ω D 22 23 dh
  have eo : MachineEval m g ω (.atom (.scalar (.integerStore 23 0))) E 1 out := by
    have hp : E.scalar.core.ptrs 23=P+2 := by simp [E,D,payUnit,pcSet,pointerWrite]
    have hz : E.scalar.core.ptrs 0=0 := by simp [E,D,C,B,A,payUnit,pcSet,pointerWrite]
    simpa only [out,hp,hz] using integerStore_eval m g ω E 23 0 eh
  refine ⟨out,?_,?_,?_,?_,?_,?_,?_⟩
  · unfold heapDetachCode sequenceCode
    exact MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee (MachineEval.seq eo (MachineEval.skip out))))))
  all_goals simp [out,E,D,C,B,A,payUnit,pcSet,pointerWrite,integerWrite,P,I] <;> ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RankQueueMass

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section
open Finset

def RankedTree.Unique (t : RankedTree) : Prop := t.support.card=t.size

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

lemma nodeSupport_card_le (t : HeapNode ℕ) : (nodeSupport t).card ≤ t.realSize := by
  induction t with
  | nil => simp [nodeSupport]
  | node a c s hc hs =>
    have h1 := Finset.card_insert_le a (nodeSupport c ∪ nodeSupport s)
    have h2 := Finset.card_union_le (nodeSupport c) (nodeSupport s)
    simp only [nodeSupport,HeapNode.realSize]
    omega

lemma node_unique_parts (a : ℕ) (c s : HeapNode ℕ)
    (h : (nodeSupport (.node a c s)).card=(HeapNode.node a c s).realSize) :
    a ∉ nodeSupport c ∪ nodeSupport s ∧ Disjoint (nodeSupport c) (nodeSupport s) ∧
      (nodeSupport c).card=c.realSize ∧ (nodeSupport s).card=s.realSize := by
  have hc := nodeSupport_card_le c
  have hs := nodeSupport_card_le s
  have h1 := Finset.card_insert_le a (nodeSupport c ∪ nodeSupport s)
  have h2 := Finset.card_union_le (nodeSupport c) (nodeSupport s)
  simp only [nodeSupport,HeapNode.realSize] at h
  refine ⟨?_,Finset.card_union_eq_card_add_card.mp (by omega),by omega,by omega⟩
  intro ha
  have he := Finset.card_insert_of_mem ha
  omega

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

-- Proof module: Solutions.RankQueueUnique

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp Finset
noncomputable section

lemma slotKeys_card_le_mass (slots : RankSlots) (length : ℕ) :
    (slotKeySet slots length).card ≤ slotMass slots length := by
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro r hr
  cases hs : slots r with
  | none => simp
  | some t =>
    have h := nodeSupport_card_le (.node t.key t.children .nil)
    simpa [RankedTree.support,nodeSupport,RankedTree.size,HeapNode.realSize] using h

lemma slotMass_clear (slots : RankSlots) (length r : ℕ) (t : RankedTree)
    (hr : r < length) (ht : slots r=some t) :
    slotMass (Function.update slots r none) length+t.size=slotMass slots length := by
  have hr' : r ∈ range length := mem_range.mpr hr
  have ho := Finset.sum_erase_add (range length) (fun j => (slots j).elim 0 RankedTree.size) hr'
  have hn := Finset.sum_erase_add (range length)
    (fun j => ((Function.update slots r none) j).elim 0 RankedTree.size) hr'
  have he : (∑ j ∈ (range length).erase r, ((Function.update slots r none) j).elim 0 RankedTree.size)=
      ∑ j ∈ (range length).erase r, (slots j).elim 0 RankedTree.size := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  simp only [Function.update_self,Option.elim_none,add_zero] at hn
  rw [he] at hn
  calc
    slotMass (Function.update slots r none) length+t.size =
        (∑ j ∈ (range length).erase r, (slots j).elim 0 RankedTree.size)+t.size :=
      congrArg (fun z => z+t.size) hn.symm
    _ = slotMass slots length := by simpa only [slotMass,ht,Option.elim_some] using ho

lemma slotKeys_clear (slots : RankSlots) (length r : ℕ) (t : RankedTree)
    (hr : r < length) (ht : slots r=some t) :
    slotKeySet slots length=slotKeySet (Function.update slots r none) length ∪ t.support := by
  ext v
  constructor
  · intro hv
    obtain ⟨j,hj,hv⟩ := Finset.mem_biUnion.mp hv
    by_cases he : j=r
    · subst j
      exact Finset.mem_union_right _ (by simpa only [ht,Option.elim_some] using hv)
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨j,hj,by simpa only [Function.update_of_ne he] using hv⟩
  · intro hv
    rcases Finset.mem_union.mp hv with hv|hv
    · obtain ⟨j,hj,hv⟩ := Finset.mem_biUnion.mp hv
      by_cases he : j=r
      · subst j; simp at hv
      · exact Finset.mem_biUnion.mpr ⟨j,hj,by simpa only [Function.update_of_ne he] using hv⟩
    · exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_range.mpr hr,by simpa only [ht,Option.elim_some] using hv⟩

lemma numeric_unique_parts (slots : RankSlots) (length r : ℕ) (t : RankedTree)
    (hr : r < length) (ht : slots r=some t)
    (hu : (slotKeySet slots length).card=slotMass slots length) :
    t.Unique ∧
      (slotKeySet (Function.update slots r none) length).card=slotMass (Function.update slots r none) length ∧
      Disjoint (slotKeySet (Function.update slots r none) length) t.support := by
  have hm := slotMass_clear slots length r t hr ht
  have hk := slotKeys_clear slots length r t hr ht
  have hc := slotKeys_card_le_mass (Function.update slots r none) length
  have htcard : t.support.card ≤ t.size := by
    simpa [RankedTree.support,nodeSupport,RankedTree.size,HeapNode.realSize] using
      nodeSupport_card_le (.node t.key t.children .nil)
  have hUnion := Finset.card_union_le (slotKeySet (Function.update slots r none) length) t.support
  rw [←hk,hu] at hUnion
  have heq : (slotKeySet (Function.update slots r none) length ∪ t.support).card=
      (slotKeySet (Function.update slots r none) length).card+t.support.card := by
    rw [←hk,hu]
    omega
  exact ⟨by unfold RankedTree.Unique; omega,by omega,Finset.card_union_eq_card_add_card.mp heq⟩

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

-- Proof module: Solutions.HeapDrainCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma heapDrainPrefixCode_wellFormed : heapDrainPrefixCode.wellFormed := by
  simp [heapDrainPrefixCode,sequenceCode,coreCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 500000 in
lemma heap_drain_prefix_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω heapDrainPrefixCode st 3 out ∧
      out.scalar.core.ptrs 5=st.scalar.core.ptrs 22 ∧
      out.scalar.core.ptrs 24=st.scalar.core.ptrs 24-1 ∧
      out.scalar.core.ptrs 14=st.scalar.core.ptrs 24-1 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+3 ∧ out.output=st.output := by
  let A := payUnit (pointerWrite st 5 (st.scalar.core.ptrs 22))
  let B := payUnit (pointerWrite A 24 (st.scalar.core.ptrs 24-1))
  let out := payUnit (pointerWrite B 14 (st.scalar.core.ptrs 24-1))
  have ah : A.scalar.halted=false := by simp [A,payUnit,pcSet,pointerWrite,hh]
  have bh : B.scalar.halted=false := by simp [B,payUnit,pcSet,pointerWrite,ah]
  have ea := pcopy_eval m g ω st 5 22 hh
  have eb : MachineEval m g ω (coreCode (.pdec 24)) A 1 B := by
    have hv : A.scalar.core.ptrs 24=st.scalar.core.ptrs 24 := by simp [A,payUnit,pcSet,pointerWrite]
    simpa only [B,coreCode,hv] using pdec_eval m g ω A 24 ah
  have ec : MachineEval m g ω (coreCode (.pcopy 14 24)) B 1 out := by
    have hv : B.scalar.core.ptrs 24=st.scalar.core.ptrs 24-1 := by simp [B,payUnit,pcSet,pointerWrite]
    simpa only [out,coreCode,hv] using pcopy_eval m g ω B 14 24 bh
  refine ⟨out,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.skip out)))
  all_goals simp [out,B,A,payUnit,pcSet,pointerWrite] <;> ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapDrainInvariant

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section

structure DrainInv (st : MachineState) (base : ℤ) (length rank a N : ℕ) (slots : RankSlots)
    (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ) (forest : HeapNode ℕ) (F : Finset ℤ) : Prop where
  zero : st.scalar.core.ptrs 0=0
  basePointer : st.scalar.core.ptrs 13=base
  rankPointer : st.scalar.core.ptrs 24=(rank : ℤ)
  queue : RankArrayRep st.scalar.integerMemory base length slots roots feet
  forestRep : ForestRep st.scalar.integerMemory (st.scalar.core.ptrs 22) forest F
  separate : Disjoint F (queueCells base length feet)
  valid : forest.WF keyLE a rank
  massBound : slotMass slots length+forest.realSize ≤ N

lemma DrainInv.pay {st : MachineState} {base : ℤ} {length rank a N : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} {forest : HeapNode ℕ} {F : Finset ℤ}
    (h : DrainInv st base length rank a N slots roots feet forest F) :
    DrainInv (payUnit st) base length rank a N slots roots feet forest F :=
  ⟨h.zero,h.basePointer,h.rankPointer,h.queue,h.forestRep,h.separate,h.valid,h.massBound⟩

lemma DrainInv.tail_positive {st : MachineState} {base : ℤ} {length rank a N : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} {k : ℕ} {c s : HeapNode ℕ} {F : Finset ℤ}
    (h : DrainInv st base length rank a N slots roots feet (.node k c s) F) :
    0 < st.scalar.core.ptrs 22 := by
  have hp := h.forestRep.positive_cells (st.scalar.core.ptrs 22) (h.forestRep.root_cells (by simp [nodeCells]))
  omega

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapCarryZero

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma heap_carry_zero {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {st out : MachineState} {u : ℕ} (hh : st.scalar.halted=false)
    (e : MachineEval m g ω heapCarryCode st u out) : out.scalar.core.ptrs 0=0 := by
  change MachineEval m g ω (.seq (coreCode (.pset 0 0)) _) st u out at e
  cases e with
  | seq ea er =>
    have hz : _ := ea
    cases ea with
    | atom i st hready =>
      have hm : (pcSet (atomState m g ω (.scalar (.core (.pset 0 0))) st) 0).scalar.core.ptrs 0=0 := by
        rw [pset_atomState m g ω st 0 0 hh]
        simp [pcSet,payUnit,pointerWrite]
      exact (er.pointer_frame 0 (by decide)).trans hm

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapDrainStep

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section

set_option maxHeartbeats 2000000 in
lemma heap_drain_step (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base : ℤ) (length rank a N R : ℕ)
    (slots : RankSlots) (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ)
    (key : ℕ) (children tail : HeapNode ℕ) (F : Finset ℤ)
    (h : DrainInv st base length rank a N slots roots feet (.node key children tail) F)
    (hcap : R < length) (hpow : N < 2^R) :
    ∃ steps out rank' slots' roots' feet' F', MachineEval m g ω heapDrainBodyCode st steps out ∧
      steps ≤ 21*R+14 ∧ rank=rank'+1 ∧
      DrainInv out base length rank' a N slots' roots' feet' tail F' ∧
      slotsSupport slots' ∪ ↑(nodeSupport tail)=slotsSupport slots ∪ ↑(nodeSupport (.node key children tail)) ∧
      F' ∪ queueCells base length feet'=F ∪ queueCells base length feet ∧
      (∀ z, z ∉ F ∪ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+steps ∧ out.output=st.output ∧
      out.scalar.halted=false := by
  obtain ⟨r,hr,hakey,hchildren,htailWF⟩ := h.valid
  have hrank : rank=r+1 := by omega
  have hweight : 2^r ≤ N := by
    have hs := hchildren.realSize_eq
    have hm := h.massBound
    simp only [HeapNode.realSize] at hm
    omega
  have hrR : r ≤ R := by
    by_contra hn
    have hp : 2^R ≤ 2^r := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  obtain ⟨pre,ep,hp5,hp24,hp14,hip,hrealp,hworkp,houtp⟩ := heap_drain_prefix_exec m g ω st hh
  have preh : pre.scalar.halted=false := (ep.halted heapDrainPrefixCode_wellFormed).trans hh
  have hpreForest : ForestRep pre.scalar.integerMemory (pre.scalar.core.ptrs 5) (.node key children tail) F := by
    rw [hp5,hip]
    exact h.forestRep
  obtain ⟨cp,sp,C,S,hcp,hsp,hF,hhead,htail,hheadS,hdetachframe⟩ := hpreForest.detach
  let H := nodeCells (pre.scalar.core.ptrs 5) ∪ C
  have hF' : F=H ∪ S := hF
  have hH : H ⊆ F := by rw [hF']; exact Finset.subset_union_left
  have hS : S ⊆ F := by rw [hF']; exact Finset.subset_union_right
  have hHSep : Disjoint H (queueCells base length feet) := h.separate.mono_left hH
  have hSSep : Disjoint S (queueCells base length feet) := h.separate.mono_left hS
  obtain ⟨det,ed,hid,hd5,hd22,hrd,hwd,hod⟩ := heap_detach_exec m g ω pre preh
  have deth : det.scalar.halted=false := (ed.halted heapDetachCode_wellFormed).trans preh
  have hqpre : RankArrayRep pre.scalar.integerMemory base length slots roots feet := by rw [hip]; exact h.queue
  have hqdet : RankArrayRep det.scalar.integerMemory base length slots roots feet := by
    apply hqpre.frame
    intro z hz
    rw [hid]
    exact hdetachframe z (by intro hf; exact Finset.disjoint_left.mp h.separate hf hz)
  let tree : RankedTree := ⟨key,children⟩
  have htreedet : ForestRep det.scalar.integerMemory (det.scalar.core.ptrs 5) (.node tree.key tree.children .nil) H := by
    rw [hid,hd5]
    exact hhead
  have htaildet : ForestRep det.scalar.integerMemory (det.scalar.core.ptrs 22) tail S := by
    rw [hid,hd22,hsp]
    exact htail
  have hbasepre : pre.scalar.core.ptrs 13=base :=
    (ep.pointer_frame 13 (by decide)).trans h.basePointer
  have hbasedet : det.scalar.core.ptrs 13=base :=
    (ed.pointer_frame 13 (by decide)).trans hbasepre
  have hr14 : det.scalar.core.ptrs 14=(r : ℤ) := by
    rw [ed.pointer_frame 14 (by decide),hp14,h.rankPointer,hrank]
    push_cast
    ring
  have hfree : slots (r+(R-r))=none := by
    rw [Nat.add_sub_of_le hrR]
    exact free_rank_of_mass slots length R N h.queue.valid hcap (by have hm := h.massBound; omega) hpow
  obtain ⟨u,out,slots',roots',feet',ec,hu,hqout,hcontents,hrealc,hwc,hoc,howned,hframe⟩ :=
    heap_carry_exec m g ω det deth base length (R-r) r slots roots feet tree H
      hbasedet hr14 hqdet htreedet hHSep hchildren (by omega) hfree
  have outh : out.scalar.halted=false := (ec.halted heapCarryCode_wellFormed).trans deth
  have htailout : ForestRep out.scalar.integerMemory (out.scalar.core.ptrs 22) tail S := by
    rw [ec.pointer_frame 22 (by decide)]
    apply htaildet.frame
    intro z hz
    apply hframe
    intro hz'
    rcases Finset.mem_union.mp hz' with hz'|hz'
    · exact Finset.disjoint_left.mp hheadS hz' hz
    · exact Finset.disjoint_left.mp hSSep hz hz'
  have hnewSep : Disjoint S (queueCells base length feet') := by
    rw [howned]
    exact Finset.disjoint_union_right.mpr ⟨hheadS.symm,hSSep⟩
  have hmass := carry_mass_conservation hqdet hqout htreedet hHSep howned
  have hbound : slotMass slots' length+tail.realSize ≤ N := by
    have hm := h.massBound
    simp only [HeapNode.realSize] at hm
    simp only [tree,RankedTree.size] at hmass
    omega
  have hiout : DrainInv out base length r a N slots' roots' feet' tail S := by
    refine ⟨?_,?_,?_,hqout,htailout,hnewSep,htailWF,hbound⟩
    · exact heap_carry_zero deth ec
    · exact (ec.pointer_frame 13 (by decide)).trans hbasedet
    · rw [ec.pointer_frame 24 (by decide),ed.pointer_frame 24 (by decide),hp24,h.rankPointer,hrank]
      push_cast
      ring
  refine ⟨3+6+u,out,r,slots',roots',feet',S,?_,by omega,hrank,hiout,?_,?_,?_,
    hrealc.trans (hrd.trans hrealp),?_,hoc.trans (hod.trans houtp),outh⟩
  · have e := MachineEval.seq ep (MachineEval.seq ed (MachineEval.seq ec (MachineEval.skip out)))
    convert e using 1 <;> (first | rfl | omega)
  · rw [hcontents]
    ext v
    simp [tree,RankedTree.support,nodeSupport,Set.mem_union,or_assoc,or_comm,or_left_comm]
  · rw [howned,hF']
    ac_rfl
  · intro z hz
    have hnH : z ∉ H ∪ queueCells base length feet := by
      intro hz'
      apply hz
      rcases Finset.mem_union.mp hz' with hz'|hz'
      · exact Finset.mem_union_left _ (hH hz')
      · exact Finset.mem_union_right _ hz'
    rw [hframe z hnH,hid,hdetachframe z (by intro hf; exact hz (Finset.mem_union_left _ hf)),hip]
  · rw [hwc,hwd,hworkp]
    push_cast
    ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapDrainLoop

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section

set_option maxHeartbeats 2000000 in
lemma heap_drain_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (base : ℤ) (length rank a N R : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (slots : RankSlots) (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ) (forest : HeapNode ℕ) (F : Finset ℤ)
    (h : DrainInv st base length rank a N slots roots feet forest F)
    (hcap : R < length) (hpow : N < 2^R) :
    ∃ steps out slots' roots' feet', MachineEval m g ω heapDrainCode st steps out ∧
      steps ≤ (21*R+16)*rank+1 ∧
      DrainInv out base length 0 a N slots' roots' feet' .nil ∅ ∧
      slotsSupport slots'=slotsSupport slots ∪ ↑(nodeSupport forest) ∧
      queueCells base length feet'=F ∪ queueCells base length feet ∧
      (∀ z, z ∉ F ∪ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+steps ∧ out.output=st.output ∧
      out.scalar.halted=false := by
  induction rank generalizing st slots roots feet forest F with
  | zero =>
    cases forest with
    | nil =>
      obtain ⟨hp,hF⟩ := h.forestRep.nil_iff
      subst F
      have ed : MachineEval m g ω heapDrainCode st 1 (payUnit st) :=
        MachineEval.pointerDone (r:=22) (s:=0) (body:=heapDrainBodyCode) hh (by rw [hp,h.zero])
      refine ⟨1,payUnit st,slots,roots,feet,ed,by omega,h.pay,?_,by simp,?_,rfl,by simp,rfl,hh⟩
      · simp [nodeSupport]
      · intros; rfl
    | node k c s =>
      obtain ⟨r,hr,_⟩ := h.valid
      omega
  | succ rank ih =>
    cases forest with
    | nil =>
      have he : rank+1=0 := h.valid
      omega
    | node k c s =>
      obtain ⟨u,mid,r',ss,rr,ff,S,eb,hu,hrank,hm,hkeys,howned,hframe,hreal,hwork,hout,hhm⟩ :=
        heap_drain_step m g ω (payUnit st) hh base length (rank+1) a N R slots roots feet k c s F h.pay hcap hpow
      have he : r'=rank := by omega
      subst r'
      obtain ⟨v,out,ss',rr',ff',er,hv,ho,hkeys',howned',hframe',hreal',hwork',hout',hho⟩ :=
        ih (payUnit mid) hhm ss rr ff s S hm.pay
      refine ⟨1+u+1+v,out,ss',rr',ff',?_,by nlinarith,ho,?_,?_,?_,
        hreal'.trans hreal,?_,hout'.trans hout,hho⟩
      · exact MachineEval.pointerNext (r:=22) (s:=0) hh (by have hp := h.tail_positive; rw [h.zero]; omega) eb er
      · exact hkeys'.trans hkeys
      · exact howned'.trans howned
      · intro z hz
        exact (hframe' z (by simpa only [howned] using hz)).trans (hframe z hz)
      · rw [hwork',payUnit_work,hwork,payUnit_work]
        push_cast
        ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MinScanInvariant

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section


def ScanMinimum (I : ℤ → ℤ) (roots : ℕ → ℤ) (i : ℕ) (p r k : ℤ) : Prop :=
  (p=0 ∧ ∀ j < i, roots j=0) ∨
  ∃ j < i, p=roots j ∧ 0<roots j ∧ r=(j : ℤ) ∧ k=I (roots j) ∧
    ∀ t < i, 0<roots t → I (roots j) ≤ I (roots t)

lemma ScanMinimum.zero (I : ℤ → ℤ) (roots : ℕ → ℤ) (r k : ℤ) :
    ScanMinimum I roots 0 0 r k := Or.inl ⟨rfl,by omega⟩

set_option maxHeartbeats 800000 in
lemma ScanMinimum.advance {I : ℤ → ℤ} {roots : ℕ → ℤ} {i : ℕ} {p r k : ℤ}
    (h : ScanMinimum I roots i p r k) (hi : 0 ≤ roots i) :
    let pick := ¬ roots i ≤ 0 ∧ (p ≤ 0 ∨ I (roots i) ≤ k)
    ScanMinimum I roots (i+1) (if pick then roots i else p)
      (if pick then (i : ℤ) else r) (if pick then I (roots i) else k) := by
  dsimp only
  by_cases hz : roots i=0
  · simp only [hz,le_refl,not_true_eq_false,false_and,if_false]
    rcases h with ⟨hp,hall⟩|⟨j,hj,hp,hpos,hr,hk,hall⟩
    · exact Or.inl ⟨hp,by intro t ht; by_cases he : t=i; simpa [he] using hz; exact hall t (by omega)⟩
    · refine Or.inr ⟨j,by omega,hp,hpos,hr,hk,?_⟩
      intro t ht hpos'
      have ht' : t < i := by
        by_contra hn
        have he : t=i := by omega
        rw [he,hz] at hpos'
        omega
      exact hall t ht' hpos'
  · have hpos : 0<roots i := by omega
    rcases h with ⟨hp,hall⟩|⟨j,hj,hp,hpos',hr,hk,hall⟩
    · have hpick : ¬roots i ≤ 0 ∧ (p ≤ 0 ∨ I (roots i) ≤ k) := ⟨by omega,Or.inl (by omega)⟩
      simp only [if_pos hpick]
      refine Or.inr ⟨i,by omega,rfl,hpos,rfl,rfl,?_⟩
      intro t ht hp'
      have he : t=i := by by_contra hn; have he := hall t (by omega); omega
      simp [he]
    · by_cases hc : I (roots i) ≤ k
      · have hpick : ¬roots i ≤ 0 ∧ (p ≤ 0 ∨ I (roots i) ≤ k) := ⟨by omega,Or.inr hc⟩
        simp only [if_pos hpick]
        refine Or.inr ⟨i,by omega,rfl,hpos,rfl,rfl,?_⟩
        intro t ht hp'
        by_cases he : t=i
        · simp [he]
        · have hh : I (roots i) ≤ I (roots j) := by simpa [hk] using hc
          exact hh.trans (hall t (by omega) hp')
      · have hnpick : ¬(¬roots i ≤ 0 ∧ (p ≤ 0 ∨ I (roots i) ≤ k)) := by omega
        simp only [if_neg hnpick]
        refine Or.inr ⟨j,by omega,hp,hpos',hr,hk,?_⟩
        intro t ht hp'
        by_cases he : t=i
        · rw [he]; omega
        · exact hall t (by omega) hp'

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapMinScanBody

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 900000 in
lemma heap_min_scan_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base : ℤ) (length i : ℕ)
    (roots : ℕ → ℤ) (hz : st.scalar.core.ptrs 0=0)
    (hb : st.scalar.core.ptrs 13=base) (hindex : st.scalar.core.ptrs 26=(i : ℤ))
    (ha : st.scalar.integerMemory (base+(i : ℤ))=roots i) (hn : 0 ≤ roots i)
    (hm : ScanMinimum st.scalar.integerMemory roots i (st.scalar.core.ptrs 27)
      (st.scalar.core.ptrs 28) (st.scalar.core.ptrs 31)) :
    ∃ steps out, MachineEval m g ω minScanBodyCode st steps out ∧ steps ≤ 12 ∧
      out.scalar.core.ptrs 0=0 ∧ out.scalar.core.ptrs 13=base ∧
      out.scalar.core.ptrs 25=st.scalar.core.ptrs 25 ∧ out.scalar.core.ptrs 26=(i+1 : ℕ) ∧
      ScanMinimum out.scalar.integerMemory roots (i+1) (out.scalar.core.ptrs 27)
        (out.scalar.core.ptrs 28) (out.scalar.core.ptrs 31) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨out,e,hp,hi,hr,hw,ho,hho⟩ := minScanBodyRoutine.execute m g ω st hh
  rw [minScanBodyRoutine_code] at e
  have hf (r : ℕ) (hr : r ∉ minScanBodyCode.pointerTargets) :
      out.scalar.core.ptrs r=st.scalar.core.ptrs r := e.pointer_frame r hr
  obtain ⟨hc,hindex',hroot,hrank,hkey⟩ := min_scan_body_run st.scalar.integerMemory st.scalar.core.ptrs
  have hload : st.scalar.integerMemory (st.scalar.core.ptrs 13+st.scalar.core.ptrs 26)=roots i := by rw [hb,hindex,ha]
  rw [hload,hz] at hroot hrank hkey
  have hm' := hm.advance hn
  refine ⟨_,out,e,hc,?_,?_,?_,?_,?_,hi,hr,hw,ho,hho⟩
  · exact (hf 0 (by decide)).trans hz
  · exact (hf 13 (by decide)).trans hb
  · exact hf 25 (by decide)
  · rw [hp,hindex',hindex]; simp
  · rw [hi,hp,hroot,hrank,hkey,hindex]
    exact hm'

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapMinScanLoop

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 1200000 in
lemma heap_min_scan_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (base : ℤ) (length fuel i : ℕ) (roots : ℕ → ℤ) (st : MachineState)
    (hh : st.scalar.halted=false) (hz : st.scalar.core.ptrs 0=0)
    (hb : st.scalar.core.ptrs 13=base) (hl : st.scalar.core.ptrs 25=(length : ℤ))
    (hindex : st.scalar.core.ptrs 26=(i : ℤ)) (hlen : i+fuel=length)
    (ha : ∀ r < length, st.scalar.integerMemory (base+(r : ℤ))=roots r)
    (hn : ∀ r < length, 0 ≤ roots r)
    (hm : ScanMinimum st.scalar.integerMemory roots i (st.scalar.core.ptrs 27)
      (st.scalar.core.ptrs 28) (st.scalar.core.ptrs 31)) :
    ∃ steps out, MachineEval m g ω minScanLoopCode st steps out ∧ steps ≤ 14*fuel+1 ∧
      out.scalar.core.ptrs 0=0 ∧ out.scalar.core.ptrs 13=base ∧
      out.scalar.core.ptrs 25=(length : ℤ) ∧ out.scalar.core.ptrs 26=(length : ℤ) ∧
      ScanMinimum out.scalar.integerMemory roots length (out.scalar.core.ptrs 27)
        (out.scalar.core.ptrs 28) (out.scalar.core.ptrs 31) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction fuel generalizing i st with
  | zero =>
    have he : i=length := by omega
    subst i
    refine ⟨1,payUnit st,?_,by omega,hz,hb,hl,hindex,hm,rfl,rfl,by simp,rfl,hh⟩
    exact MachineEval.pointerDone (r:=25) (s:=26) (body:=minScanBodyCode) hh (by rw [hl,hindex])
  | succ fuel ih =>
    have hil : i < length := by omega
    obtain ⟨u,mid,eb,hu,hzm,hbm,hlm,him,hmm,himem,hrmem,hwm,hom,hhm⟩ :=
      heap_min_scan_body_exec m g ω (payUnit st) hh base length i roots hz hb hindex (ha i hil) (hn i hil) hm
    obtain ⟨v,out,er,hv,hzo,hbo,hlo,hio,hmo,hiout,hrout,hwo,hoo,hho⟩ :=
      ih (i+1) (payUnit mid) hhm hzm hbm (hlm.trans hl) him (by omega)
        (by intro r hr; rw [show (payUnit mid).scalar.integerMemory=st.scalar.integerMemory from himem]; exact ha r hr)
        hmm
    refine ⟨1+u+1+v,out,?_,by omega,hzo,hbo,hlo,hio,hmo,hiout.trans himem,
      hrout.trans hrmem,?_,hoo.trans hom,hho⟩
    · exact MachineEval.pointerNext (r:=25) (s:=26) hh (by rw [hl,hindex]; omega) eb er
    · rw [hwo,payUnit_work,hwm,payUnit_work]
      push_cast
      ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapMinScanExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def minScanInitRoutine : PointerRoutine := .sequence [
  .atom (.set 0 0),.atom (.set 26 0),.atom (.set 27 0),.atom (.set 28 0)]

set_option maxHeartbeats 1000000 in
lemma heap_min_scan_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base : ℤ) (length : ℕ) (roots : ℕ → ℤ)
    (hb : st.scalar.core.ptrs 13=base) (hl : st.scalar.core.ptrs 25=(length : ℤ))
    (ha : ∀ r < length, st.scalar.integerMemory (base+(r : ℤ))=roots r)
    (hn : ∀ r < length, 0 ≤ roots r) :
    ∃ steps out, MachineEval m g ω heapMinScanCode st steps out ∧ steps ≤ 14*length+5 ∧
      out.scalar.core.ptrs 0=0 ∧ out.scalar.core.ptrs 13=base ∧
      out.scalar.core.ptrs 25=(length : ℤ) ∧ out.scalar.core.ptrs 26=(length : ℤ) ∧
      ScanMinimum out.scalar.integerMemory roots length (out.scalar.core.ptrs 27)
        (out.scalar.core.ptrs 28) (out.scalar.core.ptrs 31) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨mid,ei,hp,hi,hr,hw,ho,hhm⟩ := minScanInitRoutine.execute m g ω st hh
  have einit : MachineEval m g ω minScanInitRoutine.code st 4 mid := ei
  have hzm : mid.scalar.core.ptrs 0=0 := by
    rw [hp]; simp [minScanInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result]
  have hbm : mid.scalar.core.ptrs 13=base := by
    rw [hp]; simpa [minScanInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result] using hb
  have hlm : mid.scalar.core.ptrs 25=(length : ℤ) := by
    rw [hp]; simpa [minScanInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result] using hl
  have him : mid.scalar.core.ptrs 26=0 := by
    rw [hp]; simp [minScanInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result]
  have hpm : mid.scalar.core.ptrs 27=0 := by
    rw [hp]; simp [minScanInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result]
  have hmm : ScanMinimum mid.scalar.integerMemory roots 0 (mid.scalar.core.ptrs 27)
      (mid.scalar.core.ptrs 28) (mid.scalar.core.ptrs 31) := by
    rw [hpm]; exact ScanMinimum.zero _ _ _ _
  obtain ⟨v,out,el,hv,hzo,hbo,hlo,hio,hmo,hiout,hrout,hwo,hoo,hho⟩ :=
    heap_min_scan_loop_exec m g ω base length length 0 roots mid hhm hzm hbm hlm him (by omega)
      (by simpa only [hi] using ha) hn hmm
  refine ⟨4+v,out,?_,by omega,hzo,hbo,hlo,hio,hmo,hiout.trans hi,hrout.trans hr,?_,hoo.trans ho,hho⟩
  · change MachineEval m g ω (sequenceCode [coreCode (.pset 0 0),coreCode (.pset 26 0),
        coreCode (.pset 27 0),coreCode (.pset 28 0)]) st 4 mid at einit
    exact einit.sequence_continue _ el
  · rw [hwo,hw]
    change st.work+(4 : ℕ)+v=st.work+((4+v : ℕ) : ℝ≥0∞)
    push_cast
    ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapMinScanCorrectness

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section

lemma SlotRep.key {I : ℤ → ℤ} {p : ℤ} {t : RankedTree} {F : Finset ℤ}
    (h : SlotRep I p (some t) F) : I p=(t.key : ℤ) := by
  cases h
  assumption

lemma SlotRep.positive {I : ℤ → ℤ} {p : ℤ} {t : RankedTree} {F : Finset ℤ}
    (h : SlotRep I p (some t) F) : 0 < p := by
  cases h
  omega

lemma RankedTree.key_lower_bound (r : ℕ) (t : RankedTree) (h : t.valid r) :
    ∀ v ∈ t.support, t.key ≤ v := by
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl|hv
  · exact le_rfl
  · exact node_lower_bound t.key r t.children h v hv

set_option maxHeartbeats 700000 in
lemma scanMinimum_correct {I : ℤ → ℤ} {base : ℤ} {length : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} {p r k : ℤ}
    (hq : RankArrayRep I base length slots roots feet)
    (hm : ScanMinimum I roots length p r k) :
    (p=0 ∧ slotsSupport slots=∅) ∨
      ∃ j t, j < length ∧ slots j=some t ∧ p=roots j ∧ 0<p ∧
        r=(j : ℤ) ∧ k=(t.key : ℤ) ∧ t.key ∈ slotsSupport slots ∧
        ∀ v ∈ slotsSupport slots, t.key ≤ v := by
  rcases hm with ⟨hp,hempty⟩|⟨j,hj,hp,hpos,hr,hk,hmin⟩
  · refine Or.inl ⟨hp,?_⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro v ⟨j,t,hj,hv⟩
    have hjl : j < length := by
      by_contra hn
      have hn := hq.bounded j (by omega)
      rw [hj] at hn
      contradiction
    have hn := hq.node j hjl
    rw [hj] at hn
    have hroot := hn.positive
    have hz := hempty j hjl
    omega
  · have hslot : ∃ t, slots j=some t := by
      cases he : slots j with
      | none => have he' := hq.node j hj; rw [he] at he'; exact False.elim (by have hz := he'.1; omega)
      | some t => exact ⟨t,rfl⟩
    obtain ⟨t,ht⟩ := hslot
    have hrep := hq.node j hj
    rw [ht] at hrep
    have hkey := hrep.key
    refine Or.inr ⟨j,t,hj,ht,hp,by omega,hr,hk.trans hkey,?_,?_⟩
    · exact ⟨j,t,ht,Finset.mem_insert_self _ _⟩
    · rintro v ⟨j',t',ht',hv⟩
      have hj' : j' < length := by
        by_contra hn
        have hn := hq.bounded j' (by omega)
        rw [ht'] at hn
        contradiction
      have hr' := hq.node j' hj'
      rw [ht'] at hr'
      have hlo := hmin j' hj' hr'.positive
      rw [hkey,hr'.key] at hlo
      have hnat : t.key ≤ t'.key := by exact_mod_cast hlo
      exact hnat.trans (t'.key_lower_bound j' (hq.valid j' t' ht') v hv)

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapDeletePreparation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 1000000 in
lemma heap_delete_prepare_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base p cp : ℤ) (rank : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hb : st.scalar.core.ptrs 13=base)
    (hp : st.scalar.core.ptrs 27=p) (hr : st.scalar.core.ptrs 28=(rank : ℤ))
    (hc : st.scalar.integerMemory (p+1)=cp) :
    ∃ out, MachineEval m g ω heapDeletePrepareCode st 7 out ∧
      out.scalar.core.ptrs 0=0 ∧ out.scalar.core.ptrs 13=base ∧
      out.scalar.core.ptrs 22=cp ∧ out.scalar.core.ptrs 24=(rank : ℤ) ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (base+(rank : ℤ)) 0 ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+7 ∧ out.output=st.output ∧
      out.scalar.halted=false := by
  obtain ⟨mid,e,hptr,hi,hreal,hw,ho,hmh⟩ := heapDeletePrefixRoutine.execute m g ω st hh
  have em : MachineEval m g ω heapDeletePrefixRoutine.code st 6 mid := e
  have hptr0 : mid.scalar.core.ptrs 0=0 := by
    rw [hptr]; simpa [heapDeletePrefixRoutine,PointerRoutine.sequence,PointerRoutine.run,
      PointerOp.update,PointerOp.destination,PointerOp.result] using hz
  have hptr15 : mid.scalar.core.ptrs 15=base+(rank : ℤ) := by
    rw [hptr]; simp [heapDeletePrefixRoutine,PointerRoutine.sequence,PointerRoutine.run,
      PointerOp.update,PointerOp.destination,PointerOp.result,hb,hr]
  let out := payUnit (integerWrite mid (base+(rank : ℤ)) 0)
  have eo : MachineEval m g ω (.atom (.scalar (.integerStore 15 0))) mid 1 out := by
    simpa only [out,hptr15,hptr0] using integerStore_eval m g ω mid 15 0 hmh
  refine ⟨out,MachineEval.seq em eo,hptr0,?_,?_,?_,?_,hreal,?_,ho,hmh⟩
  · change mid.scalar.core.ptrs 13=base
    rw [hptr]; simpa [heapDeletePrefixRoutine,PointerRoutine.sequence,PointerRoutine.run,
      PointerOp.update,PointerOp.destination,PointerOp.result] using hb
  · change mid.scalar.core.ptrs 22=cp
    rw [hptr]; simp [heapDeletePrefixRoutine,PointerRoutine.sequence,PointerRoutine.run,
      PointerOp.update,PointerOp.destination,PointerOp.result,hp,hc]
  · change mid.scalar.core.ptrs 24=(rank : ℤ)
    rw [hptr]; simp [heapDeletePrefixRoutine,PointerRoutine.sequence,PointerRoutine.run,
      PointerOp.update,PointerOp.destination,PointerOp.result,hr]
  · change Function.update mid.scalar.integerMemory (base+(rank : ℤ)) 0= _
    rw [hi]
  · change mid.work+1=st.work+7
    rw [hw]
    change st.work+(6 : ℕ)+1=st.work+7
    norm_num
    ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapDeleteOccupied

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section

set_option maxHeartbeats 1800000 in
lemma heap_delete_occupied_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base : ℤ) (length rank N R : ℕ)
    (slots : RankSlots) (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ) (tree : RankedTree)
    (hq : RankArrayRep st.scalar.integerMemory base length slots roots feet)
    (hr : rank < length) (ht : slots rank=some tree)
    (hz : st.scalar.core.ptrs 0=0) (hb : st.scalar.core.ptrs 13=base)
    (hp : st.scalar.core.ptrs 27=roots rank) (hri : st.scalar.core.ptrs 28=(rank : ℤ))
    (hmass : slotMass slots length ≤ N) (hcap : R < length) (hpow : N < 2^R) :
    ∃ steps out slots' roots' feet', MachineEval m g ω heapDeleteOccupiedCode st steps out ∧
      steps ≤ (21*R+16)*rank+8 ∧
      RankArrayRep out.scalar.integerMemory base length slots' roots' feet' ∧
      slotsSupport slots'=slotsSupport (Function.update slots rank none) ∪ ↑(nodeSupport tree.children) ∧
      queueCells base length feet=nodeCells (roots rank) ∪ queueCells base length feet' ∧
      Disjoint (nodeCells (roots rank)) (queueCells base length feet') ∧
      slotMass slots' length+1=slotMass slots length ∧
      (∀ z, z ∉ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+steps ∧ out.output=st.output ∧
      out.scalar.halted=false := by
  have htree := hq.node rank hr
  rw [ht] at htree
  obtain ⟨cp,C,hpos,hkey,hchild,hnext,hC,hsep,hFoot⟩ := htree.root_view
  obtain ⟨pre,ep,hzp,hbp,htailp,hrp,hip,hrealp,hworkp,houtp,hhp⟩ :=
    heap_delete_prepare_exec m g ω st hh base (roots rank) cp rank hz hb hp hri hchild
  have hqpre : RankArrayRep pre.scalar.integerMemory base length
      (Function.update slots rank none) (Function.update roots rank 0) (Function.update feet rank ∅) := by
    rw [hip]
    exact hq.clear rank hr
  have hCsub : C ⊆ feet rank := by rw [hFoot]; exact Finset.subset_union_right
  have hcell : base+(rank : ℤ) ∉ C := by
    intro hc
    exact Finset.disjoint_left.mp (hq.separate rank hr)
      ((mem_arrayCells _ _ _).mpr ⟨rank,hr,rfl⟩) (hCsub hc)
  have hCpre : ForestRep pre.scalar.integerMemory (pre.scalar.core.ptrs 22) tree.children C := by
    rw [hip,htailp]
    exact hC.frame_write_outside hcell
  have hCsep : Disjoint C (queueCells base length (Function.update feet rank ∅)) :=
    (hq.removed_disjoint rank hr).mono_left hCsub
  have hmassClear := slotMass_clear slots length rank tree hr ht
  have hmassChildren : slotMass (Function.update slots rank none) length+tree.children.realSize ≤ N := by
    simp only [RankedTree.size] at hmassClear
    omega
  have hInv : DrainInv pre base length rank tree.key N (Function.update slots rank none)
      (Function.update roots rank 0) (Function.update feet rank ∅) tree.children C :=
    ⟨hzp,hbp,hrp,hqpre,hCpre,hCsep,hq.valid rank tree ht,hmassChildren⟩
  obtain ⟨u,out,slots',roots',feet',ed,hu,hout,hcontents,howned,hframe,hreal,hwork,houtput,hho⟩ :=
    heap_drain_exec m g ω base length rank tree.key N R pre hhp _ _ _ _ C hInv hcap hpow
  have hclearOwned := queueCells_clear_union base length rank feet hr
  have hpartition : queueCells base length feet=nodeCells (roots rank) ∪ queueCells base length feet' := by
    rw [howned]
    rw [hFoot] at hclearOwned
    calc
      queueCells base length feet = queueCells base length (Function.update feet rank ∅) ∪ (nodeCells (roots rank) ∪ C) := hclearOwned.symm
      _ = nodeCells (roots rank) ∪ (C ∪ queueCells base length (Function.update feet rank ∅)) := by ac_rfl
  have hrootClear : Disjoint (nodeCells (roots rank)) (queueCells base length (Function.update feet rank ∅)) :=
    (hq.removed_disjoint rank hr).mono_left (by rw [hFoot]; exact Finset.subset_union_left)
  have hrootSep : Disjoint (nodeCells (roots rank)) (queueCells base length feet') := by
    rw [howned]
    exact Finset.disjoint_union_right.mpr ⟨hsep,hrootClear⟩
  have hmassOut : slotMass slots' length+1=slotMass slots length := by
    have hc := congrArg Finset.card hpartition
    rw [Finset.card_union_of_disjoint hrootSep,nodeCells_card,hq.queue_card,hout.queue.queue_card] at hc
    omega
  refine ⟨7+u,out,slots',roots',feet',MachineEval.seq ep ed,by omega,hout.queue,hcontents,
    hpartition,hrootSep,hmassOut,?_,hreal.trans hrealp,?_,houtput.trans houtp,hho⟩
  · intro z hz'
    have hnot : z ∉ C ∪ queueCells base length (Function.update feet rank ∅) := by
      rw [←howned]
      intro hc
      exact hz' (by rw [hpartition]; exact Finset.mem_union_right _ hc)
    rw [hframe z hnot,hip]
    apply Function.update_of_ne
    intro he
    subst z
    exact hz' (Finset.mem_union_left _ ((mem_arrayCells _ _ _).mpr ⟨rank,hr,rfl⟩))
  · rw [hwork,hworkp]
    push_cast
    ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueueDeleteKeys

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp Finset
noncomputable section

lemma delete_keys_erase (slots : RankSlots) (length rank : ℕ) (tree : RankedTree)
    (hr : rank < length) (ht : slots rank=some tree)
    (hu : (slotKeySet slots length).card=slotMass slots length) :
    (slotKeySet slots length).erase tree.key=
      slotKeySet (Function.update slots rank none) length ∪ nodeSupport tree.children := by
  obtain ⟨htu,hqu,hd⟩ := numeric_unique_parts slots length rank tree hr ht hu
  have hNodeUnique : (nodeSupport (.node tree.key tree.children .nil)).card=
      (HeapNode.node tree.key tree.children .nil).realSize := by
    simpa [RankedTree.Unique,RankedTree.support,RankedTree.size,nodeSupport,HeapNode.realSize] using htu
  have hparts := node_unique_parts tree.key tree.children .nil hNodeUnique
  have hnotChild : tree.key ∉ nodeSupport tree.children := by
    intro hc
    exact hparts.1 (Finset.mem_union_left _ hc)
  have hnotQueue : tree.key ∉ slotKeySet (Function.update slots rank none) length := by
    intro hq
    exact Finset.disjoint_left.mp hd hq (Finset.mem_insert_self _ _)
  rw [slotKeys_clear slots length rank tree hr ht]
  ext v
  by_cases he : v=tree.key
  · subst v; simp [RankedTree.support,hnotQueue,hnotChild]
  · simp [RankedTree.support,he]

lemma delete_numeric_unique (slots slots' : RankSlots) (length rank : ℕ) (tree : RankedTree)
    (hr : rank < length) (ht : slots rank=some tree)
    (hu : (slotKeySet slots length).card=slotMass slots length)
    (hk : slotKeySet slots' length=(slotKeySet slots length).erase tree.key)
    (hm : slotMass slots' length+1=slotMass slots length) :
    (slotKeySet slots' length).card=slotMass slots' length := by
  have hmem : tree.key ∈ slotKeySet slots length :=
    Finset.mem_biUnion.mpr ⟨rank,Finset.mem_range.mpr hr,by simp [ht,RankedTree.support]⟩
  rw [hk,Finset.card_erase_of_mem hmem,hu]
  omega

lemma delete_keys_from_contents (slots slots' : RankSlots) (length rank : ℕ) (tree : RankedTree)
    (hr : rank < length) (ht : slots rank=some tree)
    (hu : (slotKeySet slots length).card=slotMass slots length)
    (hb : ∀ r, length ≤ r → slots r=none)
    (hb' : ∀ r, length ≤ r → slots' r=none)
    (hc : slotsSupport slots'=slotsSupport (Function.update slots rank none) ∪ ↑(nodeSupport tree.children)) :
    slotKeySet slots' length=(slotKeySet slots length).erase tree.key := by
  have hbClear : ∀ r, length ≤ r → (Function.update slots rank none) r=none := by
    intro r hr'
    rw [Function.update_of_ne (by omega)]
    exact hb r hr'
  apply Finset.coe_injective
  rw [slotKeySet_coe slots' length hb',delete_keys_erase slots length rank tree hr ht hu,
    Finset.coe_union,slotKeySet_coe _ length hbClear]
  exact hc

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapPopExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section


def PopKeys (slots slots' : RankSlots) (length : ℕ) (key : Option ℕ) : Prop :=
  match key with
  | none => slotsSupport slots=∅ ∧ slotsSupport slots'=∅ ∧ slotMass slots' length=slotMass slots length
  | some v => v ∈ slotKeySet slots length ∧
      (∀ u ∈ slotKeySet slots length, v ≤ u) ∧
      slotKeySet slots' length=(slotKeySet slots length).erase v ∧
      slotMass slots' length+1=slotMass slots length

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapPopClassified

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 2000000 in
lemma heap_pop_classified_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base : ℤ) (length N R : ℕ)
    (slots : RankSlots) (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ)
    (hq : RankArrayRep st.scalar.integerMemory base length slots roots feet)
    (hb : st.scalar.core.ptrs 13=base) (hl : st.scalar.core.ptrs 25=(length : ℤ))
    (hu : (slotKeySet slots length).card=slotMass slots length)
    (hmass : slotMass slots length ≤ N) (hcap : R < length) (hpow : N < 2^R) :
    ∃ steps out slots' roots' feet' key, MachineEval m g ω heapPopCode st steps out ∧
      steps ≤ 14*length+(21*R+16)*R+15 ∧
      RankArrayRep out.scalar.integerMemory base length slots' roots' feet' ∧
      PopKeys slots slots' length key ∧
      (slotKeySet slots' length).card=slotMass slots' length ∧
      (∀ v, key=some v → out.scalar.core.ptrs 31=(v : ℤ)) ∧
      (match key with | none => out.scalar.core.ptrs 27=0 | some _ => 0<out.scalar.core.ptrs 27) ∧
      queueCells base length feet' ⊆ queueCells base length feet ∧
      (∀ z, z ∉ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+steps ∧ out.output=st.output ∧
      out.scalar.halted=false := by
  obtain ⟨u,mid,es,huSteps,hzm,hbm,hlm,him,hmin,himem,hrmem,hwm,hom,hhm⟩ :=
    heap_min_scan_exec m g ω st hh base length roots hb hl hq.array (fun r hr => (hq.node r hr).root_nonnegative)
  have hqmid : RankArrayRep mid.scalar.integerMemory base length slots roots feet := by rw [himem]; exact hq
  rcases scanMinimum_correct hqmid hmin with ⟨hempty,hkeysEmpty⟩|⟨r,t,hr,ht,hroot,hpos,hrank,hkey,hmem,hminimum⟩
  · have eb : MachineEval m g ω (.branchPointer 27 0 .skip heapDeleteOccupiedCode) mid 1 (payUnit mid) := by
      have ee := MachineEval.pointerLe (m:=m) (g:=g) (ω:=ω) (r:=27) (s:=0) (a:=.skip) (b:=heapDeleteOccupiedCode) hhm
        (by rw [hempty,hzm]) (MachineEval.skip (payUnit mid))
      simpa using ee
    refine ⟨u+1,payUnit mid,slots,roots,feet,none,MachineEval.seq es eb,by omega,hqmid,
      ⟨hkeysEmpty,hkeysEmpty,rfl⟩,hu,?_,hempty,Finset.Subset.refl _,?_,hrmem,?_,hom,hhm⟩
    · intro v hv; cases hv
    · intro z hz; exact congrFun himem z
    · rw [payUnit_work,hwm]
      push_cast
      ring
  · have hrR : r ≤ R := by
      have hw := rank_weight_le_mass slots length r t hq.valid hr ht
      by_contra hn
      have hp : 2^R ≤ 2^r := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    obtain ⟨v,del,ss,rr,ff,ed,hv,hqd,hcontents,hpart,hsep,hmass',hframe,hreal,hwork,houtput,hhd⟩ :=
      heap_delete_occupied_exec m g ω (payUnit mid) hhm base length r N R slots roots feet t
        hqmid hr ht hzm hbm hroot hrank hmass hcap hpow
    have eb : MachineEval m g ω (.branchPointer 27 0 .skip heapDeleteOccupiedCode) mid (1+v+1) (payUnit del) :=
      MachineEval.pointerGt (r:=27) (s:=0) (a:=.skip) hhm (by rw [hzm]; omega) ed
    have hkeys := delete_keys_from_contents slots ss length r t hr ht hu hq.bounded hqd.bounded hcontents
    have hunique := delete_numeric_unique slots ss length r t hr ht hu hkeys hmass'
    have hmemFin : t.key ∈ slotKeySet slots length := by
      rw [←slotKeySet_coe slots length hq.bounded] at hmem
      exact hmem
    have hminFin : ∀ u ∈ slotKeySet slots length, t.key ≤ u := by
      intro u hu'
      apply hminimum
      rw [←slotKeySet_coe slots length hq.bounded]
      exact hu'
    refine ⟨u+(1+v+1),payUnit del,ss,rr,ff,some t.key,MachineEval.seq es eb,?_,hqd,
      ⟨hmemFin,hminFin,hkeys,hmass'⟩,hunique,?_,?_,?_,?_,hreal.trans hrmem,?_,houtput.trans hom,hhd⟩
    · have hmul : (21*R+16)*r ≤ (21*R+16)*R := Nat.mul_le_mul_left _ hrR
      omega
    · intro k hk
      cases Option.some.inj hk
      exact (ed.pointer_frame 31 (by decide)).trans hkey
    · change 0 < del.scalar.core.ptrs 27
      rw [ed.pointer_frame 27 (by decide)]
      exact hpos
    · rw [hpart]; exact Finset.subset_union_right
    · intro z hz
      exact (hframe z hz).trans (congrFun himem z)
    · rw [payUnit_work,hwork,payUnit_work,hwm]
      push_cast
      ring


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

-- Proof module: Solutions.ExteriorQueuedTestExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 2000000 in
lemma exterior_queued_test_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex levelBase flagOffset : ℕ) (q : ℝ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 50=(width : ℤ)) (hlevel : st.scalar.core.ptrs 87=(levelBase : ℤ))
    (hFlagOffset : st.scalar.core.ptrs 88=(flagOffset : ℤ)) (hq : st.scalar.core.regs 20=q)
    (hactive : 0 ≤ st.scalar.integerMemory (vertexRecordAddress width vertex (levelBase+2))) :
    ∃ steps out, MachineEval m g ω exteriorQueuedTestCode st steps out ∧ steps ≤ 16*width+42 ∧
      (0 < out.scalar.core.regs 23 ↔ st.scalar.integerMemory (vertexRecordAddress width vertex (levelBase+2))=0 ∧
        q*(st.scalar.integerMemory (vertexRecordAddress width vertex 0) : ℝ) <
          st.scalar.core.mem (vertexRecordAddress width vertex (levelBase+1))) ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (vertexRecordAddress width vertex flagOffset) 0 ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let pre := payUnit (pointerWrite st 41 (width : ℤ))
  have ep : MachineEval m g ω (coreCode (.pcopy 41 50)) st 1 pre := by
    simpa only [pre,coreCode,hw] using pcopy_eval m g ω st 41 50 hh
  have hp0 := (ep.pointer_frame 0 (by decide)).trans hz
  have hp40 := (ep.pointer_frame 40 (by decide)).trans hv
  have hp41 : pre.scalar.core.ptrs 41=(width : ℤ) := by simp [pre,payUnit,pcSet,pointerWrite]
  have hp87 := (ep.pointer_frame 87 (by decide)).trans hlevel
  have hp20 := (ep.real_register_frame 20 (by decide)).trans hq
  obtain ⟨u,mid,em,hu,hm23,hmTest,hmI,hmR,hmQ,hmW,hmO,hmH⟩ := exterior_eligibility_exec m g ω pre hh
    width vertex levelBase q hp0 hp40 hp41 hp87 hp20 hactive
  have hm0 := (em.pointer_frame 0 (by decide)).trans hp0
  have hm40 := (em.pointer_frame 40 (by decide)).trans hp40
  have hm41 := (em.pointer_frame 41 (by decide)).trans hp41
  have hm88 := (em.pointer_frame 88 (by decide)).trans ((ep.pointer_frame 88 (by decide)).trans hFlagOffset)
  obtain ⟨out,ec,hoI,hoR,hoRegs,hoQ,hoW,hoO,hoH⟩ := vertex_flag_clear_exec m g ω mid hmH width vertex flagOffset hm0 hm40 hm41 hm88
  have eRun := MachineEval.seq ep (MachineEval.seq em ec)
  refine ⟨1+(u+(4*width+9)),out,eRun,by omega,?_,?_,hoR.trans hmR,?_,?_,hoO.trans hmO,hoH⟩
  · rw [hoRegs]
    exact hmTest
  · rw [hoI,hmI]
    rfl
  · exact eRun.query_frame (by
      simp [exteriorQueuedTestCode,MachineCode.allAtoms,coreCode,queryReadOnly,
        exteriorEligibilityCode_queryReadOnly,vertexFlagClearCode_queryReadOnly])
  · rw [hoW,hmW]
    change st.work+1+u+(4*width+9 : ℕ)= _
    push_cast
    ring

end
end SparseQueue
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

lemma ExteriorQueueMemory.clear {n : ℕ} {I : ℤ → ℤ} {R : ℤ → ℝ}
    {width levelBase flagOffset : ℕ} {q : ℝ} {domain : Finset (Fin n)} {valid queued : Finset ℕ}
    (h : ExteriorQueueMemory I R width levelBase flagOffset q domain valid queued)
    (hflag : flagOffset < width) (hactive : levelBase+2 < width)
    (hneqActive : flagOffset ≠ levelBase+2) (hneqDegree : flagOffset ≠ 0) (v : Fin n) :
    ExteriorQueueMemory (Function.update I (vertexRecordAddress width v.val flagOffset) 0) R
      width levelBase flagOffset q domain valid (queued.erase v.val) := by
  have hdegree : 0 < width := by omega
  have fieldFrame (u : Fin n) (field : ℕ) (hf : field < width) (hne : field ≠ flagOffset) :=
    vertex_integer_update_other_field I width v.val u.val flagOffset field 0 hflag hf hne
  refine ⟨(Finset.erase_subset _ _).trans h.queuedDomain,h.flags.clear hflag v,?_,?_⟩
  · intro u hu
    rw [fieldFrame u (levelBase+2) hactive (Ne.symm hneqActive)]
    exact h.activeNonnegative u hu
  · intro u hu
    rw [fieldFrame u (levelBase+2) hactive (Ne.symm hneqActive),fieldFrame u 0 hdegree (Ne.symm hneqDegree)]
    exact h.eligibility u hu

lemma ExteriorQueueMemory.key_in_domain {n : ℕ} {I : ℤ → ℤ} {R : ℤ → ℝ}
    {width levelBase flagOffset : ℕ} {q : ℝ} {domain : Finset (Fin n)} {valid queued : Finset ℕ}
    (h : ExteriorQueueMemory I R width levelBase flagOffset q domain valid queued)
    {key : ℕ} (hk : key ∈ queued) : ∃ v : Fin n, v ∈ domain ∧ v.val=key := by
  obtain ⟨v,hv,hvkey⟩ := Finset.mem_image.mp (h.queuedDomain hk)
  exact ⟨v,hv,hvkey⟩

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

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.KeyListRepresentation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section


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

-- Proof module: Solutions.QueuePotential

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma queueMass_exchange {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (st out : MachineState)
    (old : RecursiveMachineMemory g s α ε ell length logical st)
    (next : RecursiveMachineMemory g s α ε ell length logical out)
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

lemma RecursiveMachineMemory.frame_mass_le_total {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {machine : MachineState}
    (memory : RecursiveMachineMemory g s α ε ell length logical machine) (i : ℕ) (hi : i ≤ logical.top) :
    (memory.frames i hi).queueMass ≤ memory.queueMass := by
  have hMem : i ∈ Finset.range (logical.top+1) := Finset.mem_range.mpr (by omega)
  have hSum := Finset.single_le_sum (f:=fun j => if hj : j ≤ logical.top then (memory.frames j hj).queueMass else 0)
    (fun j hj => Nat.zero_le _) hMem
  change Nat.le _ _ at hSum
  change Nat.le _ _
  simpa only [RecursiveMachineMemory.queueMass,dif_pos hi] using hSum

lemma RecursiveMachineMemory.exterior_mass_le_total {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {machine : MachineState}
    (memory : RecursiveMachineMemory g s α ε ell length logical machine) (i : ℕ) (hi : i ≤ logical.top) :
    (memory.frames i hi).exteriorObject.mass ≤ memory.queueMass :=
  (Nat.le_add_right _ _).trans (memory.frame_mass_le_total i hi)

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

-- Proof module: Solutions.ExteriorQueuedTestRefinement

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 1600000 in
lemma exterior_queued_test_refinement (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width levelBase flagOffset : ℕ)
    (hflag : flagOffset < width) (hactive : levelBase+2 < width)
    (hneqActive : flagOffset ≠ levelBase+2) (hneqDegree : flagOffset ≠ 0)
    (base : ℤ) (length : ℕ) (slots : RankSlots) (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ)
    (q : ℝ) (domain : Finset (Fin n)) (valid queued : Finset ℕ) (v : Fin n) (hv : v ∈ domain)
    (hqueue : RankArrayRep st.scalar.integerMemory base length slots roots feet)
    (hkeys : slotKeySet slots length=queued.erase v.val)
    (hdata : ExteriorQueueMemory st.scalar.integerMemory st.scalar.core.mem width levelBase flagOffset q domain valid queued)
    (hz : st.scalar.core.ptrs 0=0) (hvertex : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 50=(width : ℤ)) (hlevel : st.scalar.core.ptrs 87=(levelBase : ℤ))
    (hFlagOffset : st.scalar.core.ptrs 88=(flagOffset : ℤ)) (hq : st.scalar.core.regs 20=q) :
    ∃ steps out, MachineEval m g ω exteriorQueuedTestCode st steps out ∧ steps ≤ 16*width+42 ∧
      RankArrayRep out.scalar.integerMemory base length slots roots feet ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase flagOffset q
        domain valid (slotKeySet slots length) ∧
      (0 < out.scalar.core.regs 23 ↔ v.val ∈ valid) ∧
      out.scalar.integerMemory=Function.update st.scalar.integerMemory (vertexRecordAddress width v.val flagOffset) 0 ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨steps,out,ex,hs,hTest,hI,hR,hQ,hW,hO,hH⟩ := exterior_queued_test_exec m g ω st hh
    width v.val levelBase flagOffset q hz hvertex hw hlevel hFlagOffset hq (hdata.activeNonnegative v hv)
  refine ⟨steps,out,ex,hs,?_,?_,hTest.trans (hdata.eligibility v hv).symm,hI,hR,hQ,hW,hO,hH⟩
  · rw [hI]
    exact hqueue.negative_write _ _ (vertexRecordAddress_negative _ _ _)
  · rw [hI,hR,hkeys]
    exact hdata.clear hflag hactive hneqActive hneqDegree v

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapCleanDecision

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma heap_clean_empty_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω heapCleanEmptyCode st 2 out ∧
      out.scalar.core.regs 24=0 ∧ out.scalar.core.ptrs 97=0 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+2 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let pre := payUnit (realWrite st 24 0)
  let out := payUnit (pointerWrite pre 97 0)
  have ep := const_eval m g ω st 24 0 hh
  have eo := pset_eval m g ω pre 97 0 hh
  refine ⟨out,MachineEval.seq ep eo,?_,?_,rfl,rfl,?_,rfl,hh⟩
  all_goals simp [out,pre,payUnit,pcSet,realWrite,pointerWrite] <;> ring

lemma heap_clean_found_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω heapCleanFoundCode st 2 out ∧
      out.scalar.core.regs 24=0 ∧ out.scalar.core.ptrs 97=1 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+2 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let pre := payUnit (realWrite st 24 0)
  let out := payUnit (pointerWrite pre 97 1)
  have ep := const_eval m g ω st 24 0 hh
  have eo := pset_eval m g ω pre 97 1 hh
  refine ⟨out,MachineEval.seq ep eo,?_,?_,rfl,rfl,?_,rfl,hh⟩
  all_goals simp [out,pre,payUnit,pcSet,realWrite,pointerWrite] <;> ring

lemma heap_clean_decision_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (hflag : st.scalar.core.regs 24=1) :
    ∃ steps out, MachineEval m g ω heapCleanDecisionCode st steps out ∧
      steps ≤ 4 ∧ out.scalar.core.regs 24=(if st.scalar.core.regs 23 ≤ 0 then 1 else 0) ∧
      (¬ st.scalar.core.regs 23 ≤ 0 → out.scalar.core.ptrs 97=1) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  classical
  by_cases hg : st.scalar.core.regs 23 ≤ 0
  · have ex : MachineEval m g ω heapCleanDecisionCode st 1 (payUnit st) :=
      MachineEval.realNonpos hh hg (MachineEval.skip (payUnit st))
    exact ⟨1,payUnit st,ex,by omega,by simpa [hg] using hflag,by intro hn; exact False.elim (hn hg),
      rfl,rfl,by simp,rfl,hh⟩
  · obtain ⟨mid,em,hm24,hm97,hmI,hmR,hmW,hmO,hmH⟩ := heap_clean_found_exec m g ω (payUnit st) hh
    have ex : MachineEval m g ω heapCleanDecisionCode st 4 (payUnit mid) := MachineEval.realPos hh hg em
    refine ⟨4,payUnit mid,ex,by omega,by simpa only [payUnit_regs,if_neg hg] using hm24,fun _ => hm97,
      hmI,hmR,?_,hmO,hmH⟩
    change mid.work+1= _
    rw [hmW,payUnit_work]
    norm_num
    ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapCleanOutcome

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def HeapCleanOutcome (valid : Finset ℕ) (key : Option ℕ) (st : MachineState) : Prop :=
  match key with
  | none => st.scalar.core.regs 24=0 ∧ st.scalar.core.ptrs 97=0
  | some v =>
      (v ∈ valid → st.scalar.core.regs 24=0 ∧ st.scalar.core.ptrs 97=1 ∧ st.scalar.core.ptrs 40=(v : ℤ)) ∧
      (v ∉ valid → st.scalar.core.regs 24=1)

lemma HeapCleanOutcome.payUnit {valid : Finset ℕ} {key : Option ℕ} {st : MachineState}
    (h : HeapCleanOutcome valid key st) : HeapCleanOutcome valid key (payUnit st) := by
  cases key <;> exact h

lemma heap_clean_decision_valid (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (hflag : st.scalar.core.regs 24=1)
    (valid : Finset ℕ) (v : ℕ) (hkey : st.scalar.core.ptrs 40=(v : ℤ))
    (ht : 0 < st.scalar.core.regs 23 ↔ v ∈ valid) :
    ∃ steps out, MachineEval m g ω heapCleanDecisionCode st steps out ∧ steps ≤ 4 ∧
      HeapCleanOutcome valid (some v) out ∧ out.scalar.integerMemory=st.scalar.integerMemory ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨steps,out,ex,hs,h24,h97,hI,hR,hW,hO,hH⟩ := heap_clean_decision_exec m g ω st hh hflag
  refine ⟨steps,out,ex,hs,⟨?_,?_⟩,hI,hR,hW,hO,hH⟩
  · intro hv
    have hn : ¬st.scalar.core.regs 23 ≤ 0 := not_le.mpr (ht.mpr hv)
    exact ⟨by simpa only [if_neg hn] using h24,h97 hn,(ex.pointer_frame 40 (by decide)).trans hkey⟩
  · intro hv
    have hn : st.scalar.core.regs 23 ≤ 0 := le_of_not_gt (fun hh => hv (ht.mp hh))
    simpa only [if_pos hn] using h24

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapPopMemoryFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma RankArrayRep.outside_negative {I : ℤ → ℤ} {base : ℤ} {length : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} (h : RankArrayRep I base length slots roots feet)
    {z : ℤ} (hz : z < 0) : z ∉ queueCells base length feet := by
  intro hm
  have hp := h.positive_cells z hm
  omega

lemma negative_frame_from_queue {I J : ℤ → ℤ} {base : ℤ} {length : ℕ} {slots : RankSlots}
    {roots : ℕ → ℤ} {feet : ℕ → Finset ℤ} (h : RankArrayRep I base length slots roots feet)
    (he : ∀ z, z ∉ queueCells base length feet → J z=I z) : ∀ z, z < 0 → J z=I z :=
  fun z hz => he z (h.outside_negative hz)

lemma slotKeySet_empty_of_support {slots : RankSlots} {length : ℕ} (hb : ∀ r, length ≤ r → slots r=none)
    (he : slotsSupport slots=∅) : slotKeySet slots length=∅ := by
  apply Finset.coe_injective
  rw [slotKeySet_coe slots length hb,he]
  simp

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorQueueCleanBody

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def cleanContextRegisters : Finset ℕ := {13,25,50,87,88}

set_option maxHeartbeats 3000000 in
lemma exterior_queue_clean_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width levelBase flagOffset : ℕ)
    (hflag : flagOffset < width) (hactive : levelBase+2 < width)
    (hneqActive : flagOffset ≠ levelBase+2) (hneqDegree : flagOffset ≠ 0)
    (base : ℤ) (length N R : ℕ) (slots : RankSlots) (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ)
    (q : ℝ) (domain : Finset (Fin n)) (valid : Finset ℕ)
    (hqueue : RankArrayRep st.scalar.integerMemory base length slots roots feet)
    (hdata : ExteriorQueueMemory st.scalar.integerMemory st.scalar.core.mem width levelBase flagOffset q
      domain valid (slotKeySet slots length))
    (hb : st.scalar.core.ptrs 13=base) (hl : st.scalar.core.ptrs 25=(length : ℤ))
    (hw : st.scalar.core.ptrs 50=(width : ℤ)) (hlevel : st.scalar.core.ptrs 87=(levelBase : ℤ))
    (hFlagOffset : st.scalar.core.ptrs 88=(flagOffset : ℤ)) (hq : st.scalar.core.regs 20=q)
    (hcontinue : st.scalar.core.regs 24=1)
    (hu : (slotKeySet slots length).card=slotMass slots length)
    (hmass : slotMass slots length ≤ N) (hcap : R < length) (hpow : N < 2^R) :
    ∃ steps out slots' roots' feet' key,
      MachineEval m g ω (heapCleanBodyCode exteriorQueuedTestCode) st steps out ∧
      steps ≤ 14*length+(21*R+16)*R+15+16*width+50 ∧
      RankArrayRep out.scalar.integerMemory base length slots' roots' feet' ∧
      PopKeys slots slots' length key ∧ (slotKeySet slots' length).card=slotMass slots' length ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase flagOffset q
        domain valid (slotKeySet slots' length) ∧ HeapCleanOutcome valid key out ∧
      (∀ r ∈ cleanContextRegisters, out.scalar.core.ptrs r=st.scalar.core.ptrs r) ∧
      out.scalar.core.regs 20=q ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      queueCells base length feet' ⊆ queueCells base length feet ∧
      (∀ v : Fin n, ∀ field < width, field ≠ flagOffset → out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field)) ∧
      (∀ z, 0 ≤ z → z ∉ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨u,a,ss,rr,ff,key,ep,huSteps,hqa,hPop,hUnique,h31,hClass,hOwned,hI,hReal,hW,hO,hH⟩ :=
    heap_pop_classified_exec m g ω st hh base length N R slots roots feet hqueue hb hl hu hmass hcap hpow
  have hNeg := negative_frame_from_queue hqueue hI
  have haData : ExteriorQueueMemory a.scalar.integerMemory a.scalar.core.mem width levelBase flagOffset q
      domain valid (slotKeySet slots length) := hdata.frame hNeg (fun z hz => congrFun hReal z)
  let b := payUnit (pointerWrite a 0 0)
  have ez : MachineEval m g ω (coreCode (.pset 0 0)) a 1 b := pset_eval m g ω a 0 0 hH
  have b0 : b.scalar.core.ptrs 0=0 := by simp [b,payUnit,pcSet,pointerWrite]
  have bH : b.scalar.halted=false := hH
  cases key with
  | none =>
    have hkeysOld : slotKeySet slots length=∅ := slotKeySet_empty_of_support hqueue.bounded hPop.1
    have hkeysNew : slotKeySet ss length=∅ := slotKeySet_empty_of_support hqa.bounded hPop.2.1
    obtain ⟨out,ee,ho24,ho97,hoI,hoR,hoW,hoO,hoH⟩ := heap_clean_empty_exec m g ω (payUnit b) bH
    have ebranch : MachineEval m g ω (.branchPointer 27 0 heapCleanEmptyCode
        (.seq (coreCode (.pcopy 40 31)) (.seq exteriorQueuedTestCode heapCleanDecisionCode))) b 3 out :=
      MachineEval.pointerLe bH (by rw [b0]; exact (ez.pointer_frame 27 (by decide)).trans hClass |>.le)
        ee
    have eRun := MachineEval.seq ep (MachineEval.seq ez ebranch)
    have hoQueue : RankArrayRep out.scalar.integerMemory base length ss rr ff := by
      rw [hoI]
      exact hqa
    have hoData : ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase flagOffset q
        domain valid (slotKeySet ss length) := by
      have hd : ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase flagOffset q
          domain valid (slotKeySet slots length) := by
        rw [hoI,hoR]
        exact haData
      simpa only [hkeysOld,hkeysNew] using hd
    refine ⟨u+(1+3),out,ss,rr,ff,none,eRun,by omega,hoQueue,hPop,hUnique,hoData,⟨ho24,ho97⟩,?_,?_,
      hoR.trans hReal,hOwned,?_,?_,?_,?_,hoO.trans hO,hoH⟩
    · intro r hr
      exact eRun.pointer_frame r (by revert r; decide)
    · exact (eRun.real_register_frame 20 (by decide)).trans hq
    · intro v field hf' hne
      change out.scalar.integerMemory _= _
      rw [hoI]
      exact hNeg _ (vertexRecordAddress_negative _ _ _)
    · intro z hz' hn
      change out.scalar.integerMemory z= _
      rw [hoI]
      exact hI z hn
    · exact eRun.query_frame (by decide)
    · rw [hoW,payUnit_work]
      change a.work+1+1+2= _
      rw [hW]
      push_cast
      ring
  | some key =>
    obtain ⟨v,hv,hvkey⟩ := hdata.key_in_domain hPop.1
    have ha31 : a.scalar.core.ptrs 31=(key : ℤ) := h31 key rfl
    have b31 := (ez.pointer_frame 31 (by decide)).trans ha31
    let c := payUnit (pointerWrite (payUnit b) 40 (key : ℤ))
    have ec : MachineEval m g ω (coreCode (.pcopy 40 31)) (payUnit b) 1 c := by
      simpa only [c,coreCode,payUnit_ptrs,b31] using pcopy_eval m g ω (payUnit b) 40 31 bH
    have c0 := (ec.pointer_frame 0 (by decide)).trans b0
    have c40 : c.scalar.core.ptrs 40=(v.val : ℤ) := by simp [c,payUnit,pcSet,pointerWrite,hvkey]
    have c50 := (ec.pointer_frame 50 (by decide)).trans ((ez.pointer_frame 50 (by decide)).trans
      ((ep.pointer_frame 50 (by decide)).trans hw))
    have c87 := (ec.pointer_frame 87 (by decide)).trans ((ez.pointer_frame 87 (by decide)).trans
      ((ep.pointer_frame 87 (by decide)).trans hlevel))
    have c88 := (ec.pointer_frame 88 (by decide)).trans ((ez.pointer_frame 88 (by decide)).trans
      ((ep.pointer_frame 88 (by decide)).trans hFlagOffset))
    have c20 := (ec.real_register_frame 20 (by decide)).trans ((ez.real_register_frame 20 (by decide)).trans
      ((ep.real_register_frame 20 (by decide)).trans hq))
    have c24 := (ec.real_register_frame 24 (by decide)).trans ((ez.real_register_frame 24 (by decide)).trans
      ((ep.real_register_frame 24 (by decide)).trans hcontinue))
    have cKeys : slotKeySet ss length=(slotKeySet slots length).erase v.val := by rw [hvkey]; exact hPop.2.2.1
    obtain ⟨t,d,et,ht,hqd,hdData,hdTest,hdI,hdR,hdQ,hdW,hdO,hdH⟩ := exterior_queued_test_refinement m g ω c bH
      width levelBase flagOffset hflag hactive hneqActive hneqDegree base length ss rr ff q domain valid
      (slotKeySet slots length) v hv hqa cKeys haData c0 c40 c50 c87 c88 c20
    have d24 := (et.real_register_frame 24 (by decide)).trans c24
    have d40 : d.scalar.core.ptrs 40=(key : ℤ) := by
      rw [←hvkey]
      exact (et.pointer_frame 40 (by decide)).trans c40
    have dTest : 0<d.scalar.core.regs 23 ↔ key ∈ valid := by simpa only [hvkey] using hdTest
    obtain ⟨vSteps,out,ed,hvSteps,hoOutcome,hoI,hoR,hoW,hoO,hoH⟩ := heap_clean_decision_valid m g ω d hdH d24 valid key d40 dTest
    have ebranch : MachineEval m g ω (.branchPointer 27 0 heapCleanEmptyCode
        (.seq (coreCode (.pcopy 40 31)) (.seq exteriorQueuedTestCode heapCleanDecisionCode))) b
        (1+(1+(t+vSteps))+1) (payUnit out) :=
      MachineEval.pointerGt bH (by rw [b0,ez.pointer_frame 27 (by decide)]; exact not_le.mpr hClass)
        (MachineEval.seq ec (MachineEval.seq et ed))
    have eRun := MachineEval.seq ep (MachineEval.seq ez ebranch)
    have hoQueue : RankArrayRep (payUnit out).scalar.integerMemory base length ss rr ff := by rw [show (payUnit out).scalar.integerMemory=out.scalar.integerMemory from rfl,hoI]; exact hqd
    have hoData : ExteriorQueueMemory (payUnit out).scalar.integerMemory (payUnit out).scalar.core.mem
        width levelBase flagOffset q domain valid (slotKeySet ss length) := by
      change ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem _ _ _ _ _ _ _
      rw [hoI,hoR]
      exact hdData
    refine ⟨u+(1+(1+(1+(t+vSteps))+1)),payUnit out,ss,rr,ff,some key,eRun,by omega,hoQueue,hPop,hUnique,
      hoData,hoOutcome.payUnit,?_,?_,hoR.trans (hdR.trans hReal),hOwned,?_,?_,?_,?_,hoO.trans (hdO.trans hO),hoH⟩
    · intro r hr
      exact eRun.pointer_frame r (by revert r; decide)
    · exact (eRun.real_register_frame 20 (by decide)).trans hq
    · intro other field hf' hne
      change out.scalar.integerMemory _= _
      rw [hoI,hdI]
      change Function.update a.scalar.integerMemory (vertexRecordAddress width v.val flagOffset) 0
        (vertexRecordAddress width other.val field)=st.scalar.integerMemory _
      rw [vertex_integer_update_other_field _ _ _ _ _ _ _ hflag hf' hne]
      exact hNeg _ (vertexRecordAddress_negative _ _ _)
    · intro z hz' hn
      change out.scalar.integerMemory z= _
      rw [hoI,hdI]
      change Function.update a.scalar.integerMemory (vertexRecordAddress width v.val flagOffset) 0 z=st.scalar.integerMemory z
      have haNeg := vertexRecordAddress_negative width v.val flagOffset
      rw [Function.update_of_ne (by omega : z ≠ vertexRecordAddress width v.val flagOffset)]
      exact hI z hn
    · exact eRun.query_frame (by decide)
    · change out.work+1= _
      rw [hoW,hdW]
      change a.work+1+1+1+t+vSteps+1= _
      rw [hW]
      push_cast
      ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LazyQueueRefinement

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section


lemma lazy_erase_stale {queued valid : Finset ℕ} {v : ℕ} (h : valid ⊆ queued) (hv : v ∉ valid) :
    valid ⊆ queued.erase v := by
  intro u hu
  exact Finset.mem_erase.mpr ⟨by intro he; subst u; exact hv hu,h hu⟩


inductive LazyPopTrace (valid : Finset ℕ) : Finset ℕ → Option ℕ → Finset ℕ → ℕ → Prop where
  | empty : LazyPopTrace valid ∅ none ∅ 0
  | take {q : Finset ℕ} (hq : q.Nonempty) (hv : q.min' hq ∈ valid) :
      LazyPopTrace valid q (some (q.min' hq)) (q.erase (q.min' hq)) 1
  | discard {q out : Finset ℕ} {key : Option ℕ} {steps : ℕ} (hq : q.Nonempty)
      (hv : q.min' hq ∉ valid) (next : LazyPopTrace valid (q.erase (q.min' hq)) key out steps) :
      LazyPopTrace valid q key out (steps+1)

set_option maxHeartbeats 1000000 in
lemma LazyPopTrace.correct {valid queued out : Finset ℕ} {key : Option ℕ} {steps : ℕ}
    (ht : LazyPopTrace valid queued key out steps) (hsub : valid ⊆ queued) :
    out ⊆ queued ∧ out.card+steps=queued.card ∧
      (match key with
       | none => valid=∅
       | some v => v ∈ valid ∧ (∀ u ∈ valid, v ≤ u) ∧ valid.erase v ⊆ out) := by
  induction ht with
  | empty =>
    exact ⟨Finset.Subset.refl _,by simp,Finset.subset_empty.mp hsub⟩
  | @take q hq hv =>
    refine ⟨Finset.erase_subset _ _,by simpa using Finset.card_erase_add_one (Finset.min'_mem q hq),hv,?_,?_⟩
    · intro u hu
      exact Finset.min'_le _ _ (hsub hu)
    · exact Finset.erase_subset_erase _ hsub
  | @discard q out key steps hq hv ht ih =>
    obtain ⟨ho,hcard,hkey⟩ := ih (lazy_erase_stale hsub hv)
    refine ⟨ho.trans (Finset.erase_subset _ _),?_,?_⟩
    · have hc := Finset.card_erase_add_one (Finset.min'_mem q hq)
      omega
    · cases key <;> simpa only using hkey

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapCleanTrace

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def cleanProbeCount (key : Option ℕ) (removed : ℕ) : ℕ := removed+if key.isNone then 1 else 0

lemma cleanProbeCount_succ (key : Option ℕ) (removed : ℕ) :
    cleanProbeCount key (removed+1)=cleanProbeCount key removed+1 := by
  cases key <;> simp [cleanProbeCount] <;> omega

lemma PopKeys.trace_take {slots slots' : RankSlots} {length key : ℕ} {valid : Finset ℕ}
    (hp : PopKeys slots slots' length (some key)) (hv : key ∈ valid) :
    LazyPopTrace valid (slotKeySet slots length) (some key) (slotKeySet slots' length) 1 := by
  have hne : (slotKeySet slots length).Nonempty := ⟨key,hp.1⟩
  have hm : (slotKeySet slots length).min' hne=key := le_antisymm
    (Finset.min'_le _ _ hp.1) (hp.2.1 _ (Finset.min'_mem _ _))
  have ht := LazyPopTrace.take hne (by rw [hm]; exact hv)
  rw [hm] at ht
  rw [hp.2.2.1]
  exact ht

lemma PopKeys.trace_discard {slots slots' : RankSlots} {length key : ℕ} {valid out : Finset ℕ}
    {result : Option ℕ} {removed : ℕ}
    (hp : PopKeys slots slots' length (some key)) (hv : key ∉ valid)
    (ht : LazyPopTrace valid (slotKeySet slots' length) result out removed) :
    LazyPopTrace valid (slotKeySet slots length) result out (removed+1) := by
  have hne : (slotKeySet slots length).Nonempty := ⟨key,hp.1⟩
  have hm : (slotKeySet slots length).min' hne=key := le_antisymm
    (Finset.min'_le _ _ hp.1) (hp.2.1 _ (Finset.min'_mem _ _))
  have htail : LazyPopTrace valid ((slotKeySet slots length).erase ((slotKeySet slots length).min' hne)) result out removed := by
    rw [hm,←hp.2.2.1]
    exact ht
  exact LazyPopTrace.discard hne (by rw [hm]; exact hv) htail

lemma PopKeys.mass_le {slots slots' : RankSlots} {length : ℕ} {key : Option ℕ}
    (hp : PopKeys slots slots' length key) : slotMass slots' length ≤ slotMass slots length := by
  cases key with
  | none => exact hp.2.2.le
  | some key => have hm := hp.2.2.2; omega

lemma clean_loop_charge_step (B body tail removed : ℕ) (key : Option ℕ)
    (hb : body ≤ B) (ht : tail ≤ cleanProbeCount key removed*(B+2)+1) :
    1+body+1+tail ≤ cleanProbeCount key (removed+1)*(B+2)+1 := by
  rw [cleanProbeCount_succ]
  nlinarith

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorQueueCleanLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def CleanOutputSpec (key : Option ℕ) (st : MachineState) : Prop :=
  match key with
  | none => st.scalar.core.ptrs 97=0
  | some v => st.scalar.core.ptrs 97=1 ∧ st.scalar.core.ptrs 40=(v : ℤ)

lemma while_real_exit {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {body : MachineCode} {r u : ℕ} {st mid : MachineState} (hh : st.scalar.halted=false)
    (hg : ¬st.scalar.core.regs r ≤ 0) (eb : MachineEval m g ω body (payUnit st) u mid)
    (hmH : mid.scalar.halted=false) (hm : mid.scalar.core.regs r ≤ 0) :
    MachineEval m g ω (.whileReal r body) st (u+3) (payUnit (payUnit mid)) := by
  have er : MachineEval m g ω (.whileReal r body) (payUnit mid) 1 (payUnit (payUnit mid)) := MachineEval.realDone hmH hm
  have ee := MachineEval.realNext hh hg eb er
  convert ee using 1 <;> (first | rfl | omega)

set_option maxHeartbeats 4000000 in
lemma exterior_queue_clean_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width levelBase flagOffset : ℕ)
    (hflag : flagOffset < width) (hactive : levelBase+2 < width)
    (hneqActive : flagOffset ≠ levelBase+2) (hneqDegree : flagOffset ≠ 0)
    (base : ℤ) (length N R : ℕ) (q : ℝ) (domain : Finset (Fin n)) (valid : Finset ℕ)
    (fuel : ℕ) (st : MachineState) (slots : RankSlots) (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ)
    (hh : st.scalar.halted=false)
    (hqueue : RankArrayRep st.scalar.integerMemory base length slots roots feet)
    (hdata : ExteriorQueueMemory st.scalar.integerMemory st.scalar.core.mem width levelBase flagOffset q
      domain valid (slotKeySet slots length)) (hsub : valid ⊆ slotKeySet slots length)
    (hb : st.scalar.core.ptrs 13=base) (hl : st.scalar.core.ptrs 25=(length : ℤ))
    (hw : st.scalar.core.ptrs 50=(width : ℤ)) (hlevel : st.scalar.core.ptrs 87=(levelBase : ℤ))
    (hFlagOffset : st.scalar.core.ptrs 88=(flagOffset : ℤ)) (hq : st.scalar.core.regs 20=q)
    (hcontinue : st.scalar.core.regs 24=1)
    (hu : (slotKeySet slots length).card=slotMass slots length)
    (hmass : slotMass slots length ≤ N) (hcap : R < length) (hpow : N < 2^R)
    (hmassFuel : slotMass slots length ≤ fuel) :
    ∃ steps out slots' roots' feet' key removed,
      MachineEval m g ω (.whileReal 24 (heapCleanBodyCode exteriorQueuedTestCode)) st steps out ∧
      steps ≤ cleanProbeCount key removed*(cleanBodyBound width length R+2)+1 ∧
      RankArrayRep out.scalar.integerMemory base length slots' roots' feet' ∧
      (slotKeySet slots' length).card=slotMass slots' length ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase flagOffset q
        domain valid (slotKeySet slots' length) ∧
      LazyPopTrace valid (slotKeySet slots length) key (slotKeySet slots' length) removed ∧
      out.scalar.core.regs 24=0 ∧ CleanOutputSpec key out ∧
      (∀ r ∈ cleanContextRegisters, out.scalar.core.ptrs r=st.scalar.core.ptrs r) ∧
      out.scalar.core.regs 20=q ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      queueCells base length feet' ⊆ queueCells base length feet ∧
      (∀ v : Fin n, ∀ field < width, field ≠ flagOffset → out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field)) ∧
      (∀ z, 0 ≤ z → z ∉ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  induction fuel using Nat.strong_induction_on generalizing st slots roots feet with
  | h fuel ih =>
    obtain ⟨u,mid,ss,rr,ff,popped,eb,huSteps,hqmid,hPop,hUnique,hmData,hmOutcome,hmCtx,hm20,hmR,hmFoot,hmFields,hmPos,hmQ,hmW,hmO,hmH⟩ :=
      exterior_queue_clean_body_exec m g ω (payUnit st) hh width levelBase flagOffset hflag hactive hneqActive hneqDegree
        base length N R slots roots feet q domain valid hqueue hdata hb hl hw hlevel hFlagOffset hq hcontinue hu hmass hcap hpow
    have huBound : u ≤ cleanBodyBound width length R := huSteps
    have hg : ¬st.scalar.core.regs 24 ≤ 0 := by rw [hcontinue]; norm_num
    cases popped with
    | none =>
      have hkeysOld : slotKeySet slots length=∅ := slotKeySet_empty_of_support hqueue.bounded hPop.1
      have hkeysNew : slotKeySet ss length=∅ := slotKeySet_empty_of_support hqmid.bounded hPop.2.1
      have ht : LazyPopTrace valid (slotKeySet slots length) none (slotKeySet ss length) 0 := by
        rw [hkeysOld,hkeysNew]
        exact LazyPopTrace.empty
      have ex := while_real_exit hh hg eb hmH (by rw [hmOutcome.1])
      refine ⟨u+3,payUnit (payUnit mid),ss,rr,ff,none,0,ex,?_,hqmid,hUnique,hmData,ht,
        hmOutcome.1,hmOutcome.2,hmCtx,hm20,hmR,hmFoot,hmFields,hmPos,hmQ,?_,hmO,hmH⟩
      · simpa [cleanProbeCount,Nat.add_assoc] using Nat.add_le_add_right huBound 3
      · change mid.work+1+1= _
        rw [hmW,payUnit_work]
        push_cast
        ring
    | some key =>
      by_cases hv : key ∈ valid
      · obtain ⟨hm24,hm97,hm40⟩ := hmOutcome.1 hv
        have ht := hPop.trace_take hv
        have ex := while_real_exit hh hg eb hmH (by rw [hm24])
        refine ⟨u+3,payUnit (payUnit mid),ss,rr,ff,some key,1,ex,?_,hqmid,hUnique,hmData,ht,
          hm24,⟨hm97,hm40⟩,hmCtx,hm20,hmR,hmFoot,hmFields,hmPos,hmQ,?_,hmO,hmH⟩
        · simpa [cleanProbeCount,Nat.add_assoc] using Nat.add_le_add_right huBound 3
        · change mid.work+1+1= _
          rw [hmW,payUnit_work]
          push_cast
          ring
      · have hm24 : mid.scalar.core.regs 24=1 := hmOutcome.2 hv
        have hmassDecrease := hPop.2.2.2
        have hless : slotMass ss length < fuel := by omega
        have hmSub : valid ⊆ slotKeySet ss length := by
          rw [hPop.2.2.1]
          exact lazy_erase_stale hsub hv
        have hm13 := (hmCtx 13 (by decide)).trans hb
        have hm25 := (hmCtx 25 (by decide)).trans hl
        have hm50 := (hmCtx 50 (by decide)).trans hw
        have hm87 := (hmCtx 87 (by decide)).trans hlevel
        have hm88 := (hmCtx 88 (by decide)).trans hFlagOffset
        obtain ⟨vSteps,out,ts,tr,tf,result,removed,er,hvSteps,hqout,hUniqueOut,hoData,hTrace,ho24,hoSpec,hoCtx,ho20,hoR,hoFoot,hoFields,hoPos,hoQ,hoW,hoO,hoH⟩ :=
          ih (slotMass ss length) hless (payUnit mid) ss rr ff hmH hqmid hmData hmSub hm13 hm25 hm50 hm87 hm88 hm20 hm24
            hUnique (hPop.mass_le.trans hmass) (by omega)
        have ex := MachineEval.realNext hh hg eb er
        refine ⟨1+u+1+vSteps,out,ts,tr,tf,result,removed+1,ex,
          clean_loop_charge_step _ _ _ _ _ huBound hvSteps,hqout,hUniqueOut,hoData,hPop.trace_discard hv hTrace,
          ho24,hoSpec,?_,ho20,hoR.trans hmR,hoFoot.trans hmFoot,?_,?_,hoQ.trans hmQ,?_,hoO.trans hmO,hoH⟩
        · intro r hr
          exact (hoCtx r hr).trans (hmCtx r hr)
        · intro v field hf' hne
          exact (hoFields v field hf' hne).trans (hmFields v field hf' hne)
        · intro z hz' hn
          exact (hoPos z hz' (fun hm => hn (hmFoot hm))).trans (hmPos z hz' hn)
        · rw [hoW,payUnit_work,hmW,payUnit_work]
          push_cast
          ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorQueueCleanExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 2300000 in
lemma exterior_queue_clean_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width levelBase flagOffset : ℕ)
    (hflag : flagOffset < width) (hactive : levelBase+2 < width)
    (hneqActive : flagOffset ≠ levelBase+2) (hneqDegree : flagOffset ≠ 0)
    (base : ℤ) (length N R : ℕ) (q : ℝ) (domain : Finset (Fin n)) (valid : Finset ℕ)
    (st : MachineState) (slots : RankSlots) (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ)
    (hh : st.scalar.halted=false)
    (hqueue : RankArrayRep st.scalar.integerMemory base length slots roots feet)
    (hdata : ExteriorQueueMemory st.scalar.integerMemory st.scalar.core.mem width levelBase flagOffset q
      domain valid (slotKeySet slots length)) (hsub : valid ⊆ slotKeySet slots length)
    (hb : st.scalar.core.ptrs 13=base) (hl : st.scalar.core.ptrs 25=(length : ℤ))
    (hw : st.scalar.core.ptrs 50=(width : ℤ)) (hlevel : st.scalar.core.ptrs 87=(levelBase : ℤ))
    (hFlagOffset : st.scalar.core.ptrs 88=(flagOffset : ℤ)) (hq : st.scalar.core.regs 20=q)
    (hu : (slotKeySet slots length).card=slotMass slots length)
    (hmass : slotMass slots length ≤ N) (hcap : R < length) (hpow : N < 2^R) :
    ∃ steps out slots' roots' feet' key removed,
      MachineEval m g ω exteriorQueueCleanCode st steps out ∧
      steps ≤ cleanProbeCount key removed*(cleanBodyBound width length R+2)+2 ∧
      RankArrayRep out.scalar.integerMemory base length slots' roots' feet' ∧
      (slotKeySet slots' length).card=slotMass slots' length ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase flagOffset q
        domain valid (slotKeySet slots' length) ∧
      LazyPopTrace valid (slotKeySet slots length) key (slotKeySet slots' length) removed ∧
      (match key with
       | none => valid=∅ ∧ out.scalar.core.ptrs 97=0
       | some v => v ∈ valid ∧ (∀ u ∈ valid, v ≤ u) ∧ valid.erase v ⊆ slotKeySet slots' length ∧
           out.scalar.core.ptrs 97=1 ∧ out.scalar.core.ptrs 40=(v : ℤ)) ∧
      slotMass slots' length+cleanProbeCount key removed=slotMass slots length+(if key.isNone then 1 else 0) ∧
      out.scalar.core.regs 24=0 ∧
      (∀ r ∈ cleanContextRegisters, out.scalar.core.ptrs r=st.scalar.core.ptrs r) ∧
      out.scalar.core.regs 20=q ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      queueCells base length feet' ⊆ queueCells base length feet ∧
      (∀ v : Fin n, ∀ field < width, field ≠ flagOffset → out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field)) ∧
      (∀ z, 0 ≤ z → z ∉ queueCells base length feet → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  let pre := payUnit (realWrite st 24 1)
  have ep : MachineEval m g ω (coreCode (.const 24 1)) st 1 pre := const_eval m g ω st 24 1 hh
  have hp24 : pre.scalar.core.regs 24=1 := by simp [pre,payUnit,pcSet,realWrite]
  have hp20 := (ep.real_register_frame 20 (by decide)).trans hq
  obtain ⟨u,out,ss,rr,ff,key,removed,el,huSteps,hqo,hUnique,hoData,hTrace,h24,hSpec,hCtx,h20,hR,hFoot,hFields,hPos,hQ,hW,hO,hH⟩ :=
    exterior_queue_clean_loop_exec m g ω width levelBase flagOffset hflag hactive hneqActive hneqDegree base length N R q domain valid
      (slotMass slots length) pre slots roots feet hh hqueue hdata hsub hb hl hw hlevel hFlagOffset hp20 hp24 hu hmass hcap hpow le_rfl
  have hCorrect := hTrace.correct hsub
  have hMass : slotMass ss length+cleanProbeCount key removed=slotMass slots length+(if key.isNone then 1 else 0) := by
    have hc := hCorrect.2.1
    rw [hu,hUnique] at hc
    unfold cleanProbeCount
    omega
  have eRun := MachineEval.seq ep el
  refine ⟨1+u,out,ss,rr,ff,key,removed,eRun,by omega,hqo,hUnique,hoData,hTrace,?_,hMass,h24,hCtx,h20,hR,hFoot,hFields,hPos,hQ,?_,hO,hH⟩
  · cases key with
    | none => exact ⟨hCorrect.2.2,hSpec⟩
    | some v => exact ⟨hCorrect.2.2.1,hCorrect.2.2.2.1,hCorrect.2.2.2.2,hSpec⟩
  · rw [hW]
    change st.work+1+u= _
    push_cast
    ring

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorCleanObject

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

set_option maxHeartbeats 4000000 in
lemma exterior_clean_object_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width levelBase flagOffset length N R : ℕ)
    (hflag : flagOffset < width) (hactive : levelBase+2 < width)
    (hneqActive : flagOffset ≠ levelBase+2) (hneqDegree : flagOffset ≠ 0)
    (base floor : ℤ) (q : ℝ) (domain : Finset (Fin n)) (valid : Finset ℕ)
    (obj : RankQueueObject st.scalar.integerMemory base length (st.scalar.core.ptrs 20) floor)
    (ctx : ExteriorQueueContext st width levelBase flagOffset length base floor q)
    (hdata : ExteriorQueueMemory st.scalar.integerMemory st.scalar.core.mem width levelBase flagOffset q domain valid obj.keys)
    (hCover : valid ⊆ obj.keys) (hmass : obj.mass ≤ N) (hcap : R < length) (hpow : N < 2^R) :
    ∃ steps out, ∃ next : RankQueueObject out.scalar.integerMemory base length (out.scalar.core.ptrs 20) floor,
    ∃ key removed,
      MachineEval m g ω exteriorCleanObjectCode st steps out ∧
      steps ≤ cleanProbeCount key removed*(cleanBodyBound width length R+2)+3 ∧
      ExteriorQueueContext out width levelBase flagOffset length base floor q ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase flagOffset q domain valid next.keys ∧
      LazyPopTrace valid obj.keys key next.keys removed ∧
      (match key with
       | none => valid=∅ ∧ out.scalar.core.ptrs 97=0
       | some v => v ∈ valid ∧ (∀ u ∈ valid, v ≤ u) ∧ valid.erase v ⊆ next.keys ∧
           out.scalar.core.ptrs 97=1 ∧ out.scalar.core.ptrs 40=(v : ℤ)) ∧
      next.mass+cleanProbeCount key removed=obj.mass+(if key.isNone then 1 else 0) ∧
      steps+(cleanBodyBound width length R+2)*next.mass ≤
        (cleanBodyBound width length R+2)*obj.mass+(cleanBodyBound width length R+2)+3 ∧
      next.cells ⊆ obj.cells ∧ out.scalar.core.ptrs 20=st.scalar.core.ptrs 20 ∧
      (∀ v : Fin n, ∀ field < width, field ≠ flagOffset →
        out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field)) ∧
      (∀ z, 0 ≤ z → z ∉ obj.cells → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨u,mid,ss,rr,ff,key,removed,ex,hu,hRep,hUnique,hData,hTrace,hSpec,hMass,h24,hCtx,hq,hR,hFoot,hFields,hPos,hQ,hW,hO,hH⟩ :=
    exterior_queue_clean_exec m g ω width levelBase flagOffset hflag hactive hneqActive hneqDegree base length N R q domain valid
      st obj.slots obj.roots obj.feet hh obj.representation hdata hCover ctx.basePointer ctx.lengthPointer
      ctx.widthPointer ctx.levelPointer ctx.flagPointer ctx.threshold obj.unique hmass hcap hpow
  have hFree : mid.scalar.core.ptrs 20=st.scalar.core.ptrs 20 := ex.pointer_frame 20 (by decide)
  let out := payUnit (pointerWrite mid 0 0)
  have el : MachineEval m g ω (coreCode (.pset 0 0)) mid 1 out := pset_eval m g ω mid 0 0 hH
  let next : RankQueueObject out.scalar.integerMemory base length (out.scalar.core.ptrs 20) floor := {
    slots := ss
    roots := rr
    feet := ff
    representation := hRep
    unique := hUnique
    below := by intro z hz; change z < mid.scalar.core.ptrs 20; rw [hFree]; exact obj.below z (hFoot hz)
    above := by intro z hz; exact obj.above z (hFoot hz)
  }
  have nextCtx : ExteriorQueueContext out width levelBase flagOffset length base floor q := {
    zero := by simp [out,payUnit,pcSet,pointerWrite]
    basePointer := (hCtx 13 (by simp [cleanContextRegisters])).trans ctx.basePointer
    lengthPointer := (hCtx 25 (by simp [cleanContextRegisters])).trans ctx.lengthPointer
    widthPointer := (hCtx 50 (by simp [cleanContextRegisters])).trans ctx.widthPointer
    levelPointer := (hCtx 87 (by simp [cleanContextRegisters])).trans ctx.levelPointer
    flagPointer := (hCtx 88 (by simp [cleanContextRegisters])).trans ctx.flagPointer
    threshold := hq
    floorBound := by change floor ≤ mid.scalar.core.ptrs 20; rw [hFree]; exact ctx.floorBound
  }
  have nextSpec : match (generalizing := false) key with
      | none => valid=∅ ∧ out.scalar.core.ptrs 97=0
      | some v => v ∈ valid ∧ (∀ u ∈ valid, v ≤ u) ∧ valid.erase v ⊆ next.keys ∧
          out.scalar.core.ptrs 97=1 ∧ out.scalar.core.ptrs 40=(v : ℤ) := by
    cases key <;> simpa only [out,payUnit,pcSet,pointerWrite,next,RankQueueObject.keys,Function.update_of_ne (by decide : (97 : ℕ)≠0),
      Function.update_of_ne (by decide : (40 : ℕ)≠0)] using hSpec
  have hBal : next.mass+cleanProbeCount key removed=obj.mass+(if key.isNone then 1 else 0) := hMass
  refine ⟨u+1,out,next,key,removed,MachineEval.seq ex el,by omega,nextCtx,hData,hTrace,nextSpec,hBal,?_,hFoot,hFree,
    hFields,hPos,hR,hQ,?_,hO,hH⟩
  · let P := cleanBodyBound width length R+2
    change u+1+P*next.mass ≤ P*obj.mass+P+3
    have hBound : u ≤ cleanProbeCount key removed*P+2 := hu
    calc
      u+1+P*next.mass ≤ P*(next.mass+cleanProbeCount key removed)+3 := by nlinarith
      _ = P*(obj.mass+(if key.isNone then 1 else 0))+3 := by rw [hBal]
      _ ≤ P*obj.mass+P+3 := by cases key <;> simp [mul_add]
  · change mid.work+1= _
    rw [hW]
    push_cast
    ring

end
end SparseQueue
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

-- Proof module: Solutions.ExteriorPeekObject

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def ExteriorPeekSpec (valid : Finset ℕ) (out : MachineState) (key : Option ℕ) : Prop :=
  match key with
  | none => valid=∅ ∧ out.scalar.core.ptrs 97=0
  | some k => k ∈ valid ∧ (∀ u ∈ valid, k ≤ u) ∧ out.scalar.core.ptrs 97=1 ∧ out.scalar.core.ptrs 40=(k : ℤ)

lemma LazyPopTrace.some_positive {valid queued next : Finset ℕ} {key : Option ℕ} {removed : ℕ}
    (trace : LazyPopTrace valid queued key next removed) : key.isSome=true → 0 < removed := by
  cases trace <;> simp

set_option maxHeartbeats 5500000 in
lemma exterior_peek_object_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width levelBase flagOffset length N R : ℕ)
    (hflag : flagOffset < width) (hactive : levelBase+2 < width)
    (hneqActive : flagOffset ≠ levelBase+2) (hneqDegree : flagOffset ≠ 0)
    (base floor : ℤ) (hfloor : 2 ≤ floor) (q : ℝ) (domain : Finset (Fin n)) (valid : Finset ℕ)
    (obj : RankQueueObject st.scalar.integerMemory base length (st.scalar.core.ptrs 20) floor)
    (ctx : ExteriorQueueContext st width levelBase flagOffset length base floor q)
    (hdata : ExteriorQueueMemory st.scalar.integerMemory st.scalar.core.mem width levelBase flagOffset q domain valid obj.keys)
    (hCover : valid ⊆ obj.keys) (hmass : obj.mass ≤ N) (hcap : R < length) (hpow : N < 2^R) :
    ∃ steps out, ∃ next : RankQueueObject out.scalar.integerMemory base length (out.scalar.core.ptrs 20) floor,
    ∃ key,
      MachineEval m g ω exteriorPeekObjectCode st steps out ∧
      ExteriorQueueContext out width levelBase flagOffset length base floor q ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase flagOffset q domain valid next.keys ∧
      valid ⊆ next.keys ∧ ExteriorPeekSpec valid out key ∧ next.mass ≤ obj.mass ∧
      steps+(cleanBodyBound width length R+2)*next.mass ≤
        (cleanBodyBound width length R+2)*obj.mass+2*(cleanBodyBound width length R+2)+(21*R+20*width+70)+6 ∧
      st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 ∧ out.scalar.core.ptrs 20 ≤ st.scalar.core.ptrs 20+3 ∧
      next.cells ⊆ nodeCells (st.scalar.core.ptrs 20) ∪ obj.cells ∧
      (∀ other : Fin n, ∀ field < width, field ≠ flagOffset →
        out.scalar.integerMemory (vertexRecordAddress width other.val field)=st.scalar.integerMemory (vertexRecordAddress width other.val field)) ∧
      (∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 → z ∉ obj.cells → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨u,a,aObj,key,removed,ea,hu,aCtx,aData,aTrace,aSpec,aBalance,aAmort,aCells,aFree,aFields,aPos,aR,aQ,aW,aO,aH⟩ :=
    exterior_clean_object_exec m g ω st hh width levelBase flagOffset length N R hflag hactive hneqActive hneqDegree
      base floor q domain valid obj ctx hdata hCover hmass hcap hpow
  cases hKey : key with
  | none =>
    have hSpec : valid=∅ ∧ a.scalar.core.ptrs 97=0 := by simpa only [hKey] using aSpec
    have eb : MachineEval m g ω (.branchPointer 97 0 .skip exteriorQueueRefreshCode) a 1 (payUnit a) :=
      MachineEval.pointerLe aH (by rw [hSpec.2,aCtx.zero]) (MachineEval.skip (payUnit a))
    have hMass : aObj.mass ≤ obj.mass := by
      rw [hKey] at aBalance
      simp only [cleanProbeCount,Option.isNone_none,if_true] at aBalance
      omega
    refine ⟨u+1,payUnit a,aObj,none,MachineEval.seq ea eb,aCtx.payUnit,aData,?_,hSpec,hMass,?_,?_,?_,
      aCells.trans Finset.subset_union_right,aFields,(fun z hz hf hn => aPos z hz hn),aR,aQ,?_,aO,aH⟩
    · rw [hSpec.1]; exact Finset.empty_subset _
    · change u+1+(cleanBodyBound width length R+2)*aObj.mass ≤ _
      nlinarith [aAmort]
    · exact le_of_eq aFree.symm
    · change a.scalar.core.ptrs 20 ≤ st.scalar.core.ptrs 20+3
      rw [aFree]; omega
    · change a.work+1= _
      rw [aW]; push_cast; ring
  | some k =>
    have hSpec : k ∈ valid ∧ (∀ u ∈ valid, k ≤ u) ∧ valid.erase k ⊆ aObj.keys ∧
        a.scalar.core.ptrs 97=1 ∧ a.scalar.core.ptrs 40=(k : ℤ) := by
      simpa only [hKey] using aSpec
    obtain ⟨v,hv,hvk⟩ := hdata.key_in_domain (hCover hSpec.1)
    have hPop : 0 < removed := aTrace.some_positive (by simp [hKey])
    have hCleanMass : aObj.mass+1 ≤ obj.mass := by
      rw [hKey] at aBalance
      simp only [cleanProbeCount,Option.isNone_some,if_false,add_zero] at aBalance
      omega
    have hMassN : aObj.mass ≤ N := by omega
    obtain ⟨w,b,bObj,eb,hw,bCtx,bData,bKeys,bMass,bFree,bFreeUp,bCells,bFields,bPos,bR,bQ,bW,bO,bH⟩ :=
      exterior_refresh_object_exec m g ω (payUnit a) aH width levelBase flagOffset length N R hflag hactive hneqActive hneqDegree
        base floor hfloor q domain valid aObj aCtx.payUnit aData v hv (by change a.scalar.core.ptrs 40=(v.val : ℤ); rw [hSpec.2.2.2.2,hvk]) hMassN hcap hpow
    have eb' : MachineEval m g ω (.branchPointer 97 0 .skip exteriorQueueRefreshCode) a (1+w+1) (payUnit b) :=
      MachineEval.pointerGt aH (by rw [hSpec.2.2.2.1,aCtx.zero]; norm_num) eb
    have hCoverNew : valid ⊆ bObj.keys := by
      rw [bKeys]
      change valid ⊆ if v.val ∈ valid then insert v.val aObj.keys else aObj.keys
      rw [hvk,if_pos hSpec.1]
      intro k' hk'
      by_cases he : k'=k
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert.mpr (Or.inr (hSpec.2.2.1 (Finset.mem_erase.mpr ⟨he,hk'⟩)))
    have hPeek : ExteriorPeekSpec valid (payUnit b) (some k) := by
      refine ⟨hSpec.1,hSpec.2.1,?_,?_⟩
      · exact (eb.pointer_frame 97 (by decide)).trans hSpec.2.2.2.1
      · exact (eb.pointer_frame 40 (by decide)).trans hSpec.2.2.2.2
    refine ⟨u+(1+w+1),payUnit b,bObj,some k,MachineEval.seq ea eb',bCtx.payUnit,bData,hCoverNew,hPeek,?_,?_,?_,?_,?_,?_,?_,
      bR.trans aR,bQ.trans aQ,?_,bO.trans aO,bH⟩
    · change bObj.mass ≤ obj.mass
      change bObj.mass ≤ aObj.mass+1 at bMass
      omega
    · change u+(1+w+1)+(cleanBodyBound width length R+2)*bObj.mass ≤ _
      change bObj.mass ≤ aObj.mass+1 at bMass
      have hPotential := Nat.mul_le_mul_left (cleanBodyBound width length R+2) bMass
      nlinarith [aAmort]
    · change a.scalar.core.ptrs 20 ≤ b.scalar.core.ptrs 20 at bFree
      rw [←aFree]; exact bFree
    · change b.scalar.core.ptrs 20 ≤ a.scalar.core.ptrs 20+3 at bFreeUp
      rw [←aFree]; exact bFreeUp
    · intro z hz
      rcases Finset.mem_union.mp (bCells hz) with hn|ho
      · apply Finset.mem_union_left
        change z ∈ nodeCells (a.scalar.core.ptrs 20) at hn
        rw [aFree] at hn
        exact hn
      · exact Finset.mem_union_right _ (aCells ho)
    · intro other field hf hn
      exact (bFields other field hf hn).trans (aFields other field hf hn)
    · intro z hz hf hn
      have hnA : z ∉ aObj.cells := fun hm => hn (aCells hm)
      exact (bPos z hz (by change z < a.scalar.core.ptrs 20; rw [aFree]; exact hf) hnA).trans (aPos z hz hn)
    · change b.work+1= _
      rw [bW,payUnit_work,aW]
      push_cast
      ring

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

-- Proof module: Solutions.PeekLevelExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 5500000 in
lemma peek_level_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length capacity rank i : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hi : i ≤ logical.top) (hDepth : logical.top ≤ ell) (hIndex : st.scalar.core.ptrs 109=(i : ℤ))
    (hMass : (pm.frames i hi).exteriorObject.mass ≤ capacity) (hcap : rank < length) (hpow : capacity < 2^rank) :
    ∃ steps out,
    ∃ next : RankQueueObject out.scalar.integerMemory (pm.frames i hi).exteriorBase length (out.scalar.core.ptrs 20)
      (128+32*((ell+2 : ℕ) : ℤ)),
    ∃ key,
      MachineEval m g ω peekLevelCode st steps out ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem (16*(ell+3)) (16*(i+1)) (16*(i+1)+3)
        (logical.frames i).q (parentDomain logical i) ((logical.frames i).exterior.image Fin.val) next.keys ∧
      (logical.frames i).exterior.image Fin.val ⊆ next.keys ∧
      ExteriorPeekSpec ((logical.frames i).exterior.image Fin.val) out key ∧
      next.mass ≤ (pm.frames i hi).exteriorObject.mass ∧
      steps+(cleanBodyBound (16*(ell+3)) length rank+2)*next.mass ≤
        (cleanBodyBound (16*(ell+3)) length rank+2)*(pm.frames i hi).exteriorObject.mass+
        2*(cleanBodyBound (16*(ell+3)) length rank+2)+(21*rank+20*(16*(ell+3))+70)+42 ∧
      st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 ∧ out.scalar.core.ptrs 20 ≤ st.scalar.core.ptrs 20+3 ∧
      next.cells ⊆ nodeCells (st.scalar.core.ptrs 20) ∪ (pm.frames i hi).exteriorObject.cells ∧
      (∀ v : Fin n, ∀ field < 16*(ell+3), field ≠ 16*(i+1)+3 →
        out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)) ∧
      (∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 → z ∉ (pm.frames i hi).exteriorObject.cells →
        out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.core.ptrs 100=(logical.top : ℤ) ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let f := pm.frames i hi
  let width := 16*(ell+3)
  let base := 16*(i+1)
  let floor := 128+32*((ell+2 : ℕ) : ℤ)
  let valid := (logical.frames i).exterior.image Fin.val
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω peekLevelPrefixInstructions
    (by simp [peekLevelPrefixInstructions,unitInstruction,straightInstruction]) st hh
  let a := linearRun m g ω peekLevelPrefixInstructions st
  have a100 : a.scalar.core.ptrs 100=(i : ℤ) := by
    simp [a,linearRun,peekLevelPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh,hIndex]
  have a108 : a.scalar.core.ptrs 108=(logical.top : ℤ) := by
    simp [a,linearRun,peekLevelPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh,pm.top]
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,peekLevelPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have aR : a.scalar.core.mem=st.scalar.core.mem := by
    simp [a,linearRun,peekLevelPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,peekLevelPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  change a.work=st.work+2 at aW
  have aFree : a.scalar.core.ptrs 20=st.scalar.core.ptrs 20 := ea.pointer_frame 20 (by decide)
  obtain ⟨c,ec,cCtx,cI,cR,cFree,cW,cO,cH⟩ := exterior_frame_context_exec m g ω a aH i width length
    f.exteriorBase floor (logical.frames i).q a100 ((ea.pointer_frame 50 (by decide)).trans pm.width)
    ((congrFun aI 5).trans pm.lengthMemory) ((congrFun aI _).trans f.exteriorPointer)
    ((congrFun aR _).trans f.q) ((ea.real_register_frame 31 (by decide)).trans pm.one)
    ((ea.pointer_frame 0 (by decide)).trans pm.zero) (by rw [aFree]; exact pm.allocator)
  have cI0 := cI.trans aI
  have cR0 := cR.trans aR
  have cFree0 := cFree.trans aFree
  let obj := f.exteriorObject.frame (fun z hz => congrFun cI0 z) (le_of_eq cFree0.symm)
  have cData : ExteriorQueueMemory c.scalar.integerMemory c.scalar.core.mem width base (base+3)
      (logical.frames i).q (parentDomain logical i) valid obj.keys := by
    change ExteriorQueueMemory _ _ _ _ _ _ _ _ f.exteriorObject.keys
    rw [cI0,cR0]
    exact f.exteriorData
  obtain ⟨u,b,bObj,key,eb,bCtx,bData,bCover,bSpec,bMass,bAmort,bFree,bFreeUp,bCells,bFields,bPos,bR,bQ,bW,bO,bH⟩ :=
    exterior_peek_object_exec m g ω c cH width base (base+3) length capacity rank
      (by dsimp [base,width]; omega) (by dsimp [base,width]; omega) (by omega) (by dsimp [base]; omega)
      f.exteriorBase floor (by dsimp [floor]; omega) (logical.frames i).q (parentDomain logical i) valid
      obj cCtx cData f.exteriorCover hMass hcap hpow
  have b108 := ((MachineEval.seq ec eb).pointer_frame 108 (by decide)).trans a108
  let out := payUnit (pointerWrite b 100 (logical.top : ℤ))
  have el : MachineEval m g ω (coreCode (.pcopy 100 108)) b 1 out := by
    simpa only [out,coreCode,b108] using pcopy_eval m g ω b 100 108 bH
  have outSpec : ExteriorPeekSpec valid out key := by
    cases key <;> simpa [ExteriorPeekSpec,out,payUnit,pcSet,pointerWrite] using bSpec
  refine ⟨2+(33+(u+1)),out,bObj,key,MachineEval.seq ea (MachineEval.seq ec (MachineEval.seq eb el)),bData,bCover,outSpec,?_,?_,?_,?_,?_,?_,?_,
    bR.trans cR0,?_,by simp [out,payUnit,pcSet,pointerWrite],?_,?_,bO.trans (cO.trans aO),bH⟩
  · change bObj.mass ≤ f.exteriorObject.mass at bMass
    exact bMass
  · change 2+(33+(u+1))+(cleanBodyBound width length rank+2)*bObj.mass ≤ _
    change u+(cleanBodyBound width length rank+2)*bObj.mass ≤
      (cleanBodyBound width length rank+2)*f.exteriorObject.mass+2*(cleanBodyBound width length rank+2)+
        (21*rank+20*width+70)+6 at bAmort
    dsimp only [width,f] at bAmort ⊢
    omega
  · change c.scalar.core.ptrs 20 ≤ b.scalar.core.ptrs 20 at bFree
    rw [←cFree0]; exact bFree
  · change b.scalar.core.ptrs 20 ≤ c.scalar.core.ptrs 20+3 at bFreeUp
    rw [←cFree0]; exact bFreeUp
  · change bObj.cells ⊆ nodeCells (st.scalar.core.ptrs 20) ∪ f.exteriorObject.cells
    change bObj.cells ⊆ nodeCells (c.scalar.core.ptrs 20) ∪ f.exteriorObject.cells at bCells
    rw [cFree0] at bCells
    exact bCells
  · intro v field hf hn
    exact (bFields v field hf hn).trans (congrFun cI0 _)
  · intro z hz hzF hn
    exact (bPos z hz (by rw [cFree0]; exact hzF) hn).trans (congrFun cI0 z)
  · exact bCtx.zero
  · rw [el.query_frame (by decide),bQ,ec.query_frame (by decide),ea.query_frame (by decide)]
  · change b.work+1= _
    rw [bW,cW,aW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PriorityAdvance

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 3000000 in
lemma priority_advance_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length index stop : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (found : Bool)
    (hFlag : st.scalar.core.ptrs 97=if found then 1 else 0)
    (hIndex : st.scalar.core.ptrs 109=(index : ℤ)) (hStop : st.scalar.core.ptrs 111=(stop : ℤ)) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω priorityAdvanceCode st (if found then 4 else 2) out ∧
      memory.queueMass=pm.queueMass ∧
      out.scalar.core.ptrs 109=(if found then (stop : ℤ) else ((index+1 : ℕ) : ℤ)) ∧
      out.scalar.core.ptrs 112=(if found then (index : ℤ) else st.scalar.core.ptrs 112) ∧
      out.scalar.core.ptrs 111=st.scalar.core.ptrs 111 ∧ out.scalar.core.ptrs 97=st.scalar.core.ptrs 97 ∧
      out.scalar.core.ptrs 40=st.scalar.core.ptrs 40 ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(if found then 4 else 2 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  cases found with
  | false =>
    let out := payUnit (pointerWrite (payUnit st) 109 (st.scalar.core.ptrs 109+1))
    have el : MachineEval m g ω (coreCode (.pinc 109)) (payUnit st) 1 out := pinc_eval m g ω (payUnit st) 109 hh
    have ex : MachineEval m g ω priorityAdvanceCode st 2 out :=
      MachineEval.pointerLe hh (by rw [hFlag,pm.zero]; norm_num) el
    let memory := pm.frame (out:=out) rfl rfl (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl <;> rfl) (by intros; rfl) rfl
    refine ⟨out,memory,ex,rfl,?_,rfl,rfl,rfl,rfl,rfl,?_,rfl,hh⟩
    · simp [out,payUnit,pcSet,pointerWrite,hIndex]
    · change st.work+1+1= _
      norm_num
      ring
  | true =>
    let a := payUnit (pointerWrite (payUnit st) 112 (index : ℤ))
    have ea : MachineEval m g ω (coreCode (.pcopy 112 109)) (payUnit st) 1 a := by
      have hIndex' : (payUnit st).scalar.core.ptrs 109=(index : ℤ) := hIndex
      simpa only [a,coreCode,hIndex'] using pcopy_eval m g ω (payUnit st) 112 109 hh
    let b := payUnit (pointerWrite a 109 (stop : ℤ))
    have eb : MachineEval m g ω (coreCode (.pcopy 109 111)) a 1 b := by
      have a111 : a.scalar.core.ptrs 111=(stop : ℤ) := by simpa [a,payUnit,pcSet,pointerWrite] using hStop
      simpa only [b,coreCode,a111] using pcopy_eval m g ω a 109 111 hh
    let out := payUnit b
    have ex : MachineEval m g ω priorityAdvanceCode st 4 out :=
      MachineEval.pointerGt hh (by rw [hFlag,pm.zero]; norm_num)
        (MachineEval.seq ea eb)
    let memory := pm.frame (out:=out) rfl rfl (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl <;> rfl) (by intros; rfl) rfl
    refine ⟨out,memory,ex,rfl,?_,?_,rfl,rfl,rfl,rfl,?_,rfl,hh⟩
    · simp [out,b,a,payUnit,pcSet,pointerWrite]
    · simp [out,b,a,payUnit,pcSet,pointerWrite]
    · change st.work+1+1+1+1= _
      norm_num
      ring

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

-- Proof module: Solutions.RecursiveFrameExterior

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def RecursiveFrameMemory.exterior_frame {n : ℕ} {g : InputGraph n} {logical : RecursiveState n}
    {j width length : ℕ} {st out : MachineState} {floor : ℤ}
    (f : RecursiveFrameMemory g logical j width length st floor)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hHeaderI : ∀ slot < 32, out.scalar.integerMemory (levelHeaderAddress j slot)=st.scalar.integerMemory (levelHeaderAddress j slot))
    (hHeaderR : ∀ slot < 32, out.scalar.core.mem (levelHeaderAddress j slot)=st.scalar.core.mem (levelHeaderAddress j slot))
    (hFieldsI : ∀ v ∈ parentDomain logical j, ∀ field < 16*(j+1)+7, field ≠ 16*(j+1)+3 →
      out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field))
    (hFieldsR : ∀ v ∈ parentDomain logical j, ∀ field < 16*(j+1)+7,
      out.scalar.core.mem (vertexRecordAddress width v.val field)=st.scalar.core.mem (vertexRecordAddress width v.val field))
    (hOwned : ∀ z ∈ f.activeFoot ∪ f.cacheFoot ∪ f.highObject.cells,
      out.scalar.integerMemory z=st.scalar.integerMemory z)
    (next : RankQueueObject out.scalar.integerMemory f.exteriorBase length (out.scalar.core.ptrs 20) floor)
    (hData : ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width (16*(j+1)) (16*(j+1)+3)
      (logical.frames j).q (parentDomain logical j) ((logical.frames j).exterior.image Fin.val) next.keys)
    (hCover : (logical.frames j).exterior.image Fin.val ⊆ next.keys) :
    RecursiveFrameMemory g logical j width length out floor := by
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
    exteriorObject := next
    highObject := high
    exteriorData := hData
    exteriorCover := hCover
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
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
  · rw [hHeaderI 4 (by decide)]
    apply f.cacheRep.frame
    intro z hz
    apply hOwned
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
  · intro v hv
    rw [hFieldsR v hv _ (by omega),hFieldsI v hv _ (by omega) (by omega),hFieldsI v hv 0 (by omega) (by omega),hFieldsR v hv _ (by omega)]
    exact f.highBoolean v hv
  · intro v hv
    rw [hFieldsI v hv _ (by omega) (by omega)]
    exact f.highFlags v hv
  · intro v hv
    rw [hFieldsI v hv _ (by omega) (by omega),hFieldsI v hv 0 (by omega) (by omega),hFieldsR v hv _ (by omega)]
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

-- Proof module: Solutions.QueueObjectFrames

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma queue_disjoint_after_growth {F Q next : Finset ℤ} {free : ℤ}
    (hBelow : ∀ z ∈ F, z < free) (hSep : Disjoint F Q)
    (hOld : ∀ z ∈ next, z < free → z ∈ Q) : Disjoint F next := by
  apply Finset.disjoint_left.mpr
  intro z hz hn
  exact Finset.disjoint_left.mp hSep hz (hOld z hn (hBelow z hz))

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FramePieceSeparation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma RecursiveFrameMemory.exterior_separate {n : ℕ} {g : InputGraph n} {logical : RecursiveState n}
    {j width length : ℕ} {machine : MachineState} {floor : ℤ}
    (f : RecursiveFrameMemory g logical j width length machine floor) (h : f.pieces.Pairwise Disjoint) :
    Disjoint (f.activeFoot ∪ f.cacheFoot ∪ f.highObject.cells) f.exteriorObject.cells := by
  have hA := h.rel_get_of_lt (a:=⟨0,by simp [RecursiveFrameMemory.pieces]⟩) (b:=⟨2,by simp [RecursiveFrameMemory.pieces]⟩) (by change (0 : ℕ)<2; omega)
  have hC := h.rel_get_of_lt (a:=⟨1,by simp [RecursiveFrameMemory.pieces]⟩) (b:=⟨2,by simp [RecursiveFrameMemory.pieces]⟩) (by change (1 : ℕ)<2; omega)
  have hH := h.rel_get_of_lt (a:=⟨2,by simp [RecursiveFrameMemory.pieces]⟩) (b:=⟨3,by simp [RecursiveFrameMemory.pieces]⟩) (by change (2 : ℕ)<3; omega)
  change Disjoint f.activeFoot f.exteriorObject.cells at hA
  change Disjoint f.cacheFoot f.exteriorObject.cells at hC
  change Disjoint f.exteriorObject.cells f.highObject.cells at hH
  exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hA,hC⟩,hH.symm⟩

lemma replace_exterior_pieces (A C Q H Q' : Finset ℤ) (free : ℤ)
    (hp : [A,C,Q,H].Pairwise Disjoint)
    (hBelow : ∀ z ∈ A ∪ C ∪ H, z < free)
    (hOld : ∀ z ∈ Q', z < free → z ∈ Q) : [A,C,Q',H].Pairwise Disjoint := by
  have hAC : Disjoint A C := hp.rel_get_of_lt (a:=⟨0,by norm_num⟩) (b:=⟨1,by norm_num⟩) (by change (0 : ℕ)<1; omega)
  have hAQ : Disjoint A Q := hp.rel_get_of_lt (a:=⟨0,by norm_num⟩) (b:=⟨2,by norm_num⟩) (by change (0 : ℕ)<2; omega)
  have hAH : Disjoint A H := hp.rel_get_of_lt (a:=⟨0,by norm_num⟩) (b:=⟨3,by norm_num⟩) (by change (0 : ℕ)<3; omega)
  have hCQ : Disjoint C Q := hp.rel_get_of_lt (a:=⟨1,by norm_num⟩) (b:=⟨2,by norm_num⟩) (by change (1 : ℕ)<2; omega)
  have hCH : Disjoint C H := hp.rel_get_of_lt (a:=⟨1,by norm_num⟩) (b:=⟨3,by norm_num⟩) (by change (1 : ℕ)<3; omega)
  have hQH : Disjoint Q H := hp.rel_get_of_lt (a:=⟨2,by norm_num⟩) (b:=⟨3,by norm_num⟩) (by change (2 : ℕ)<3; omega)
  have hAQ' := queue_disjoint_after_growth
    (fun z hz => hBelow z (Finset.mem_union_left _ (Finset.mem_union_left _ hz))) hAQ hOld
  have hCQ' := queue_disjoint_after_growth
    (fun z hz => hBelow z (Finset.mem_union_left _ (Finset.mem_union_right _ hz))) hCQ hOld
  have hHQ' := queue_disjoint_after_growth (fun z hz => hBelow z (Finset.mem_union_right _ hz)) hQH.symm hOld
  simpa [List.pairwise_cons] using (show (Disjoint A C ∧ Disjoint A Q' ∧ Disjoint A H) ∧
    (Disjoint C Q' ∧ Disjoint C H) ∧ Disjoint Q' H from ⟨⟨hAC,hAQ',hAH⟩,⟨hCQ',hCH⟩,hHQ'.symm⟩)

end
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

-- Proof module: Solutions.ExteriorMemoryReplacement

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 7000000 in
lemma replace_exterior_memory {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length j : ℕ) (st out : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hj : j ≤ logical.top) (hDepth : logical.top ≤ ell)
    (next : RankQueueObject out.scalar.integerMemory (pm.frames j hj).exteriorBase length
      (out.scalar.core.ptrs 20) (128+32*((ell+2 : ℕ) : ℤ)))
    (hData : ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem (16*(ell+3)) (16*(j+1)) (16*(j+1)+3)
      (logical.frames j).q (parentDomain logical j) ((logical.frames j).exterior.image Fin.val) next.keys)
    (hCover : (logical.frames j).exterior.image Fin.val ⊆ next.keys)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hOld : ∀ z ∈ next.cells, z < st.scalar.core.ptrs 20 → z ∈ (pm.frames j hj).exteriorObject.cells)
    (hFields : ∀ v : Fin n, ∀ field < 16*(ell+3), field ≠ 16*(j+1)+3 →
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field))
    (hPos : ∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 → z ∉ (pm.frames j hj).exteriorObject.cells →
      out.scalar.integerMemory z=st.scalar.integerMemory z)
    (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hZero : out.scalar.core.ptrs 0=0) (hTop : out.scalar.core.ptrs 100=(logical.top : ℤ))
    (hWidth : out.scalar.core.ptrs 50=((16*(ell+3) : ℕ) : ℤ))
    (hAlpha : out.scalar.core.regs 30=α) (hOne : out.scalar.core.regs 31=1) (hOutput : out.output=[]) :
    ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      memory.queueMass+(pm.frames j hj).exteriorObject.mass=pm.queueMass+next.mass := by
  let f := pm.frames j hj
  let floor := 128+32*((ell+2 : ℕ) : ℤ)
  have hHeader (i : ℕ) (hi : i ≤ logical.top) (slot : ℕ) (hs : slot < 32) :
      out.scalar.integerMemory (levelHeaderAddress i slot)=st.scalar.integerMemory (levelHeaderAddress i slot) := by
    apply hPos
    · have := levelHeaderAddress_positive i slot; omega
    · have := pm.allocator
      unfold levelHeaderAddress
      omega
    · intro hz
      have hlo := f.exteriorObject.above _ hz
      unfold levelHeaderAddress at hlo
      omega
  have hOtherBelow : ∀ z ∈ f.activeFoot ∪ f.cacheFoot ∪ f.highObject.cells, z < st.scalar.core.ptrs 20 := by
    intro z hz
    rcases Finset.mem_union.mp hz with hac|hh
    · rcases Finset.mem_union.mp hac with ha|hc
      · exact f.activeBelow z ha
      · exact f.cacheBelow z hc
    · exact f.highObject.below z hh
  have hOtherAbove : ∀ z ∈ f.activeFoot ∪ f.cacheFoot ∪ f.highObject.cells, floor ≤ z := by
    intro z hz
    rcases Finset.mem_union.mp hz with hac|hh
    · rcases Finset.mem_union.mp hac with ha|hc
      · exact f.activeAbove z ha
      · exact f.cacheAbove z hc
    · exact f.highObject.above z hh
  have hOwnOther : ∀ z ∈ f.activeFoot ∪ f.cacheFoot ∪ f.highObject.cells,
      out.scalar.integerMemory z=st.scalar.integerMemory z := by
    intro z hz
    exact hPos z (by have := hOtherAbove z hz; dsimp only [floor] at this; omega) (hOtherBelow z hz)
      (fun hq => Finset.disjoint_left.mp (f.exterior_separate (pm.pieceSeparation j hj)) hz hq)
  let current := f.exterior_frame hFree (hHeader j hj) (by intros; exact congrFun hR _)
    (fun v hv field hf hn => hFields v field (by omega) hn) (by intros; exact congrFun hR _) hOwnOther next hData hCover
  have hCurrentPieces : current.pieces.Pairwise Disjoint :=
    replace_exterior_pieces f.activeFoot f.cacheFoot f.exteriorObject.cells f.highObject.cells next.cells
      (st.scalar.core.ptrs 20) (pm.pieceSeparation j hj) hOtherBelow hOld
  have hCurrentOld : ∀ z ∈ current.owned, z < st.scalar.core.ptrs 20 → z ∈ f.owned := by
    intro z hz hzOld
    change z ∈ f.activeFoot ∪ f.cacheFoot ∪ next.cells ∪ f.highObject.cells at hz
    rcases Finset.mem_union.mp hz with hacq|hh
    · rcases Finset.mem_union.mp hacq with hac|hq
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hac)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hOld z hq hzOld))
    · exact Finset.mem_union_right _ hh
  have hOtherOwned (i : ℕ) (hi : i ≤ logical.top) (hne : i ≠ j) :
      ∀ z ∈ (pm.frames i hi).owned, out.scalar.integerMemory z=st.scalar.integerMemory z := by
    intro z hz
    have hlo := (pm.frames i hi).owned_below z hz
    have hhi := (pm.frames i hi).owned_above z hz
    apply hPos z (by omega) hlo
    intro hzQ
    exact Finset.disjoint_left.mp (pm.frameSeparation i hi j hj hne) hz
      (Finset.mem_union_left _ (Finset.mem_union_right _ hzQ))
  let other (i : ℕ) (hi : i ≤ logical.top) (hne : i ≠ j) := (pm.frames i hi).scoped_frame hFree
    (hHeader i hi) (by intros; exact congrFun hR _)
    (fun v hv field hf hneeded => hFields v field (by omega) (by omega))
    (by intros; exact congrFun hR _) (hOtherOwned i hi hne)
  let frames (i : ℕ) (hi : i ≤ logical.top) : RecursiveFrameMemory g logical i (16*(ell+3)) length out floor :=
    if he : i=j then by subst i; exact current else other i hi he
  have allCurrent : frames j hj=current := by simp [frames]
  have allOther (i : ℕ) (hi : i ≤ logical.top) (hne : i ≠ j) : frames i hi=other i hi hne := by
    simp only [frames,dif_neg hne]
  have ownedOther (i : ℕ) (hi : i ≤ logical.top) (hne : i ≠ j) :
      (frames i hi).owned=(pm.frames i hi).owned := by rw [allOther i hi hne]; rfl
  have hGlobalI (z : ℤ) (hz : 0 ≤ z) (hs : z < 128) : out.scalar.integerMemory z=st.scalar.integerMemory z := by
    apply hPos z hz (by have := pm.allocator; omega)
    intro hm
    have := f.exteriorObject.above z hm
    omega
  have hCacheSep : Disjoint (cachedRowCells g st.scalar.integerMemory (16*(ell+3)) logical.stored) f.exteriorObject.cells := by
    apply Finset.disjoint_left.mpr
    intro z hz hzQ
    exact Finset.disjoint_left.mp (pm.cacheSeparation j hj)
      (Finset.mem_union_left _ (Finset.mem_union_right _ hzQ)) hz
  have hCache : GraphCache g out.scalar.integerMemory (16*(ell+3)) logical.stored (out.scalar.core.ptrs 20) :=
    pm.graphCache.queue_frame g f.exteriorObject.cells hCacheSep hFree
      (fun v field hf => hFields v field (by omega) (by omega)) hPos
  have hRows : cachedRowCells g out.scalar.integerMemory (16*(ell+3)) logical.stored=
      cachedRowCells g st.scalar.integerMemory (16*(ell+3)) logical.stored := by
    unfold cachedRowCells
    apply Finset.biUnion_congr rfl
    intro v hv
    rw [hFields v 1 (by omega) (by omega)]
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
    alphaMemory := (congrFun hR 0).trans pm.alphaMemory
    epsilonMemory := (congrFun hR 1).trans pm.epsilonMemory
    depthMemory := (hGlobalI 2 (by norm_num) (by norm_num)).trans pm.depthMemory
    lengthMemory := (hGlobalI 5 (by norm_num) (by norm_num)).trans pm.lengthMemory
    seedMemory := (hGlobalI 0 (by norm_num) (by norm_num)).trans pm.seedMemory
    allocator := pm.allocator.trans hFree
    potential := fun v => (congrFun hR _).trans (pm.potential v)
    seedMarker := fun v => (congrFun hR _).trans (pm.seedMarker v)
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
    rw [hFields v 1 (by omega) (by omega)]
    exact pm.rowAbove v hv
  · intro v hv
    rw [hFields v 0 (by omega) (by omega)]
    exact pm.knownDegree v hv
  · intro v hv
    rw [hFields v 0 (by omega) (by omega)]
    exact pm.unknownDegree v hv
  · intro i hi
    by_cases he : i=j
    · subst i; rw [allCurrent]; exact hCurrentPieces
    · rw [allOther i hi he]
      exact pm.pieceSeparation i hi
  · intro i hi k hk hik
    by_cases hei : i=j <;> by_cases hek : k=j
    · exact False.elim (hik (hei.trans hek.symm))
    · subst i
      rw [allCurrent,ownedOther k hk hek]
      apply Finset.disjoint_right.mpr
      intro z hz hzCurrent
      have hzOld := (pm.frames k hk).owned_below z hz
      exact Finset.disjoint_left.mp (pm.frameSeparation j hj k hk (Ne.symm hek)) (hCurrentOld z hzCurrent hzOld) hz
    · subst k
      rw [ownedOther i hi hei,allCurrent]
      exact queue_disjoint_after_growth (pm.frames i hi).owned_below
        (pm.frameSeparation i hi j hj hei) hCurrentOld
    · rw [ownedOther i hi hei,ownedOther k hk hek]
      exact pm.frameSeparation i hi k hk hik
  · intro i hi
    rw [hRows]
    by_cases he : i=j
    · subst i
      rw [allCurrent]
      apply Finset.disjoint_right.mpr
      intro z hz hzCurrent
      exact Finset.disjoint_left.mp (pm.cacheSeparation j hj) (hCurrentOld z hzCurrent (hRowsBelow z hz)) hz
    · rw [ownedOther i hi he]
      exact pm.cacheSeparation i hi
  · apply queueMass_exchange g logical s α ε ell length st out pm _ j hj f.exteriorObject.mass next.mass
    · intro i hi he
      change (frames i hi).queueMass=(pm.frames i hi).queueMass
      rw [allOther i hi he]
      rfl
    · change (frames j hj).queueMass+f.exteriorObject.mass=f.queueMass+next.mass
      rw [allCurrent]
      change next.mass+f.highObject.mass+f.exteriorObject.mass=(f.exteriorObject.mass+f.highObject.mass)+next.mass
      omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PeekLevelSimulation

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 5500000 in
lemma peek_level_simulation (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length capacity rank i : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hi : i ≤ logical.top) (hDepth : logical.top ≤ ell) (hIndex : st.scalar.core.ptrs 109=(i : ℤ))
    (hMass : (pm.frames i hi).exteriorObject.mass ≤ capacity) (hcap : rank < length) (hpow : capacity < 2^rank) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
    ∃ key,
      MachineEval m g ω peekLevelCode st steps out ∧
      ExteriorPeekSpec ((logical.frames i).exterior.image Fin.val) out key ∧
      memory.queueMass ≤ pm.queueMass ∧
      steps+(cleanBodyBound (16*(ell+3)) length rank+2)*memory.queueMass ≤
        (cleanBodyBound (16*(ell+3)) length rank+2)*pm.queueMass+
        2*(cleanBodyBound (16*(ell+3)) length rank+2)+(21*rank+20*(16*(ell+3))+70)+42 ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  obtain ⟨steps,out,next,key,ex,hData,hCover,hSpec,hNextMass,hAmort,hFree,hFreeUp,hCells,hFields,hPos,hR,h0,hTop,hQ,hW,hO,hH⟩ :=
    peek_level_exec m g ω logical s α ε ell length capacity rank i st hh pm hi hDepth hIndex hMass hcap hpow
  have hOld : ∀ z ∈ next.cells, z < st.scalar.core.ptrs 20 → z ∈ (pm.frames i hi).exteriorObject.cells := by
    intro z hz hzOld
    rcases Finset.mem_union.mp (hCells hz) with hn|ho
    · have hm := (nodeCells_mem_iff (st.scalar.core.ptrs 20) z).mp hn
      omega
    · exact ho
  obtain ⟨memory,hExchange⟩ := replace_exterior_memory g logical s α ε ell length i st out pm hi hDepth next hData hCover hFree
    hOld hFields hPos hR h0 hTop ((ex.pointer_frame 50 (by decide)).trans pm.width)
    ((ex.real_register_frame 30 (by decide)).trans pm.alphaRegister)
    ((ex.real_register_frame 31 (by decide)).trans pm.one) (hO.trans pm.output)
  refine ⟨steps,out,memory,key,ex,hSpec,by omega,?_,hQ,hW,hO,hH,(fun v => hFields v 7 (by omega) (by omega))⟩
  have hPotential := congrArg (fun z : ℕ => (cleanBodyBound (16*(ell+3)) length rank+2)*z) hExchange
  have hPotential' : (cleanBodyBound (16*(ell+3)) length rank+2)*memory.queueMass+
      (cleanBodyBound (16*(ell+3)) length rank+2)*(pm.frames i hi).exteriorObject.mass=
      (cleanBodyBound (16*(ell+3)) length rank+2)*pm.queueMass+
      (cleanBodyBound (16*(ell+3)) length rank+2)*next.mass := by
    calc
      _ = (cleanBodyBound (16*(ell+3)) length rank+2)*(memory.queueMass+(pm.frames i hi).exteriorObject.mass) := by ring
      _ = (cleanBodyBound (16*(ell+3)) length rank+2)*(pm.queueMass+next.mass) := hPotential
      _ = _ := by ring
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingSelection

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pending_push_none_of_empty {n : ℕ} (logical : RecursiveState n)
    (hEmpty : ∀ i ≤ logical.top, (logical.frames i).exterior=∅) : pendingPush logical=none := by
  classical
  unfold pendingPush
  dsimp only
  have hLevels : ¬((Finset.range (logical.top+1)).filter (fun i => (logical.frames i).exterior.Nonempty)).Nonempty := by
    rintro ⟨i,hi⟩
    have h := (Finset.mem_filter.mp hi).2
    rw [hEmpty i (by have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega)] at h
    simpa using h
  rw [dif_neg hLevels]

lemma pending_push_of_first_min {n : ℕ} (logical : RecursiveState n) (t : ℕ) (v : Fin n)
    (ht : t ≤ logical.top) (hv : v ∈ (logical.frames t).exterior)
    (hEmpty : ∀ i < t, (logical.frames i).exterior=∅)
    (hMin : ∀ u ∈ (logical.frames t).exterior, v.val ≤ u.val) : pendingPush logical=some (t,v) := by
  classical
  let levels := (Finset.range (logical.top+1)).filter (fun i => (logical.frames i).exterior.Nonempty)
  have hExt : (logical.frames t).exterior.Nonempty := ⟨v,hv⟩
  have hMem : t ∈ levels := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hExt⟩
  have hLevels : levels.Nonempty := ⟨t,hMem⟩
  have hFirst : levels.min' hLevels=t := by
    apply le_antisymm (Finset.min'_le _ _ hMem)
    by_contra hn
    have he := hEmpty (levels.min' hLevels) (by omega)
    have hNonempty := (Finset.mem_filter.mp (Finset.min'_mem levels hLevels)).2
    rw [he] at hNonempty
    simpa using hNonempty
  have hVertex : (logical.frames t).exterior.min' hExt=v := by
    apply le_antisymm (Finset.min'_le _ _ hv)
    exact hMin _ (Finset.min'_mem _ hExt)
  change (if h : levels.Nonempty then
    if h' : (logical.frames (levels.min' h)).exterior.Nonempty then
      some (levels.min' h,(logical.frames (levels.min' h)).exterior.min' h') else none else none)= _
  rw [dif_pos hLevels,hFirst,dif_pos hExt,hVertex]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PriorityLoopExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 8500000 in
lemma priority_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length capacity rank remaining : ℕ)
    (hDepth : logical.top ≤ ell) (hcap : rank < length) (hpow : capacity < 2^rank) :
    ∀ (index : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
      (pm : RecursiveMachineMemory g s α ε ell length logical st),
      index+remaining=logical.top+1 → st.scalar.core.ptrs 109=(index : ℤ) →
      st.scalar.core.ptrs 111=((logical.top+1 : ℕ) : ℤ) → st.scalar.core.ptrs 97=0 →
      st.scalar.core.ptrs 112=(-1) → (∀ i < index, (logical.frames i).exterior=∅) →
      pm.queueMass ≤ capacity →
      ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
        MachineEval m g ω priorityLoopCode st steps out ∧ PendingSelectionSpec logical out ∧
        memory.queueMass ≤ pm.queueMass ∧
        steps+(cleanBodyBound (16*(ell+3)) length rank+2)*memory.queueMass ≤
          (cleanBodyBound (16*(ell+3)) length rank+2)*pm.queueMass+
          remaining*(2*(cleanBodyBound (16*(ell+3)) length rank+2)+(21*rank+20*(16*(ell+3))+70)+50)+1 ∧
        out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
        (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
          st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let H := 2*P+(21*rank+20*(16*(ell+3))+70)+50
  induction remaining with
  | zero =>
    intro index st hh pm hCount hIndex hStop hFlag hLevel hEmpty hMass
    have hPending : pendingPush logical=none := pending_push_none_of_empty logical (fun i hi => hEmpty i (by omega))
    have ex : MachineEval m g ω priorityLoopCode st 1 (payUnit st) :=
      MachineEval.pointerDone hh (by rw [hStop,hIndex]; omega)
    refine ⟨1,payUnit st,pm.payUnit,ex,?_,le_rfl,?_,rfl,?_,rfl,hh,(fun _ => rfl)⟩
    · simpa only [PendingSelectionSpec,hPending,payUnit,pcSet] using And.intro hFlag hLevel
    · change 1+P*pm.queueMass ≤ P*pm.queueMass+0*H+1
      omega
    · simpa only [Nat.cast_one] using payUnit_work st
  | succ remaining ih =>
    intro index st hh pm hCount hIndex hStop hFlag hLevel hEmpty hMass
    have hi : index ≤ logical.top := by omega
    have hLocalMass : (pm.payUnit.frames index hi).exteriorObject.mass ≤ capacity := by
      exact (pm.payUnit.exterior_mass_le_total index hi).trans hMass
    obtain ⟨u,a,aPM,key,ea,aSpec,aMass,aAmort,aQ,aW,aO,aH,aMarks⟩ :=
      peek_level_simulation m g ω logical s α ε ell length capacity rank index (payUnit st) hh pm.payUnit
        hi hDepth hIndex hLocalMass hcap hpow
    change aPM.queueMass ≤ pm.queueMass at aMass
    change u+P*aPM.queueMass ≤ P*pm.queueMass+2*P+(21*rank+20*(16*(ell+3))+70)+42 at aAmort
    have aIndex := (ea.pointer_frame 109 (by decide)).trans hIndex
    have aStop := (ea.pointer_frame 111 (by decide)).trans hStop
    have aLevel := (ea.pointer_frame 112 (by decide)).trans hLevel
    have hGuard : ¬st.scalar.core.ptrs 111 ≤ st.scalar.core.ptrs 109 := by rw [hStop,hIndex]; omega
    cases hKey : key with
    | none =>
      have hSpec : ((logical.frames index).exterior.image Fin.val)=∅ ∧ a.scalar.core.ptrs 97=0 := by
        simpa only [ExteriorPeekSpec,hKey] using aSpec
      have hExt : (logical.frames index).exterior=∅ := Finset.image_eq_empty.mp hSpec.1
      obtain ⟨b,bPM,eb,bMass,bIndex,bLevel,bStop,bFlag,bVertex,bQ,bW,bO,bH⟩ :=
        priority_advance_exec m g ω logical s α ε ell length index (logical.top+1) a aH aPM false
          hSpec.2 aIndex aStop
      change b.scalar.core.ptrs 109=((index+1 : ℕ) : ℤ) at bIndex
      change b.scalar.core.ptrs 112=a.scalar.core.ptrs 112 at bLevel
      change b.work=a.work+2 at bW
      have hEmptyNext : ∀ i < index+1, (logical.frames i).exterior=∅ := by
        intro i hi'
        by_cases hlo : i < index
        · exact hEmpty i hlo
        · have he : i=index := by omega
          simpa only [he] using hExt
      have bBound : bPM.payUnit.queueMass ≤ capacity := by
        change bPM.queueMass ≤ capacity
        rw [bMass]
        omega
      obtain ⟨w,out,cPM,er,cSpec,cMass,cAmort,cQ,cW,cO,cH,cMarks⟩ :=
        ih (index+1) (payUnit b) bH bPM.payUnit (by omega) bIndex
          (bStop.trans aStop) (bFlag.trans hSpec.2) (bLevel.trans aLevel) hEmptyNext bBound
      change cPM.queueMass ≤ bPM.queueMass at cMass
      change w+P*cPM.queueMass ≤ P*bPM.queueMass+remaining*H+1 at cAmort
      rw [bMass] at cMass cAmort
      have eBody : MachineEval m g ω priorityBodyCode (payUnit st) (u+2) b := MachineEval.seq ea eb
      have ex : MachineEval m g ω priorityLoopCode st (1+(u+2)+1+w) out :=
        MachineEval.pointerNext hh hGuard eBody er
      refine ⟨1+(u+2)+1+w,out,cPM,ex,cSpec,cMass.trans aMass,?_,cQ.trans (bQ.trans aQ),?_,cO.trans (bO.trans aO),cH,?_⟩
      · change 1+(u+2)+1+w+P*cPM.queueMass ≤ P*pm.queueMass+(remaining+1)*H+1
        have hProduct : (remaining+1)*H=remaining*H+H := by ring
        rw [hProduct]
        omega
      · rw [cW,payUnit_work,bW,aW,payUnit_work]
        push_cast
        ring
      · intro v
        exact (cMarks v).trans ((congrFun (eb.integer_memory_frame (by decide)) _).trans (aMarks v))
    | some k =>
      have hSpec : k ∈ (logical.frames index).exterior.image Fin.val ∧
          (∀ u ∈ (logical.frames index).exterior.image Fin.val, k ≤ u) ∧
          a.scalar.core.ptrs 97=1 ∧ a.scalar.core.ptrs 40=(k : ℤ) := by
        simpa only [ExteriorPeekSpec,hKey] using aSpec
      obtain ⟨v,hv,hvk⟩ := Finset.mem_image.mp hSpec.1
      have hPending : pendingPush logical=some (index,v) := pending_push_of_first_min logical index v hi hv hEmpty
        (fun u hu => by rw [hvk]; exact hSpec.2.1 u.val (Finset.mem_image.mpr ⟨u,hu,rfl⟩))
      obtain ⟨b,bPM,eb,bMass,bIndex,bLevel,bStop,bFlag,bVertex,bQ,bW,bO,bH⟩ :=
        priority_advance_exec m g ω logical s α ε ell length index (logical.top+1) a aH aPM true
          hSpec.2.2.1 aIndex aStop
      change b.scalar.core.ptrs 109=((logical.top+1 : ℕ) : ℤ) at bIndex
      change b.scalar.core.ptrs 112=(index : ℤ) at bLevel
      change b.work=a.work+4 at bW
      have er : MachineEval m g ω priorityLoopCode (payUnit b) 1 (payUnit (payUnit b)) :=
        MachineEval.pointerDone bH (by change b.scalar.core.ptrs 111 ≤ b.scalar.core.ptrs 109; rw [bStop,aStop,bIndex])
      have eBody : MachineEval m g ω priorityBodyCode (payUnit st) (u+4) b := MachineEval.seq ea eb
      have ex : MachineEval m g ω priorityLoopCode st (1+(u+4)+1+1) (payUnit (payUnit b)) :=
        MachineEval.pointerNext hh hGuard eBody er
      let memory := bPM.payUnit.payUnit
      have hOutSpec : PendingSelectionSpec logical (payUnit (payUnit b)) := by
        rw [PendingSelectionSpec,hPending]
        refine ⟨bFlag.trans hSpec.2.2.1,bLevel,?_⟩
        exact bVertex.trans (hSpec.2.2.2.trans (by rw [hvk]))
      refine ⟨1+(u+4)+1+1,payUnit (payUnit b),memory,ex,hOutSpec,?_,?_,bQ.trans aQ,?_,bO.trans aO,bH,?_⟩
      · change bPM.queueMass ≤ pm.queueMass
        rw [bMass]
        exact aMass
      · change 1+(u+4)+1+1+P*bPM.queueMass ≤ P*pm.queueMass+(remaining+1)*H+1
        rw [bMass]
        have hProduct : (remaining+1)*H=remaining*H+H := by ring
        rw [hProduct]
        omega
      · change b.work+1+1= _
        rw [bW,aW,payUnit_work]
        push_cast
        ring
      · intro v
        exact (congrFun (eb.integer_memory_frame (by decide)) _).trans (aMarks v)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PriorityExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 4500000 in
lemma priority_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length capacity rank : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hDepth : logical.top ≤ ell) (hMass : pm.queueMass ≤ capacity) (hcap : rank < length) (hpow : capacity < 2^rank) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω priorityCode st steps out ∧ PendingSelectionSpec logical out ∧
      memory.queueMass ≤ pm.queueMass ∧
      steps+(cleanBodyBound (16*(ell+3)) length rank+2)*memory.queueMass ≤
        (cleanBodyBound (16*(ell+3)) length rank+2)*pm.queueMass+
        (logical.top+1)*(2*(cleanBodyBound (16*(ell+3)) length rank+2)+(21*rank+20*(16*(ell+3))+70)+50)+6 ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  let a := linearRun m g ω priorityInitInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω priorityInitInstructions
    (by simp [priorityInitInstructions,unitInstruction,straightInstruction]) st hh
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,priorityInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have aR : a.scalar.core.mem=st.scalar.core.mem := by
    simp [a,linearRun,priorityInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,priorityInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  let aPM := pm.frame (out:=a) aI aR (by
    intro r hr
    apply ea.pointer_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> decide) (by
    intro r hr
    apply ea.real_register_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> decide) aO
  have aIndex : a.scalar.core.ptrs 109=0 := by
    simp [a,linearRun,priorityInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have aStop : a.scalar.core.ptrs 111=((logical.top+1 : ℕ) : ℤ) := by
    simp [a,linearRun,priorityInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh,pm.top]
  have aFlag : a.scalar.core.ptrs 97=0 := by
    simp [a,linearRun,priorityInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  have aLevel : a.scalar.core.ptrs 112=(-1) := by
    simp [a,linearRun,priorityInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      LocalPush.coreProgram,scalarProgram,SmaleNinth.RAMStep,hh]
  obtain ⟨u,out,memory,eb,hSpec,hMem,hAmort,hQ,hW,hO,hH,hMarks⟩ :=
    priority_loop_exec m g ω logical s α ε ell length capacity rank (logical.top+1) hDepth hcap hpow
      0 a aH aPM (by omega) aIndex aStop aFlag aLevel (by intros; omega) hMass
  change a.work=st.work+5 at aW
  refine ⟨5+u,out,memory,MachineEval.seq ea eb,hSpec,hMem,?_,?_,?_,hO.trans aO,hH,(fun v => (hMarks v).trans (congrFun aI _))⟩
  · change u+(cleanBodyBound (16*(ell+3)) length rank+2)*memory.queueMass ≤
      (cleanBodyBound (16*(ell+3)) length rank+2)*pm.queueMass+
      (logical.top+1)*(2*(cleanBodyBound (16*(ell+3)) length rank+2)+(21*rank+20*(16*(ell+3))+70)+50)+1 at hAmort
    omega
  · exact hQ.trans (ea.query_frame (by decide))
  · rw [hW,aW]
    push_cast
    ring

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

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution : ∀ (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length capacity rank : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hDepth : logical.top ≤ ell) (hMass : pm.queueMass ≤ capacity) (hcap : rank < length) (hpow : capacity < 2^rank),
∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω priorityCode st steps out ∧ PendingSelectionSpec logical out ∧
      memory.queueMass ≤ pm.queueMass ∧
      steps+(cleanBodyBound (16*(ell+3)) length rank+2)*memory.queueMass ≤
        (cleanBodyBound (16*(ell+3)) length rank+2)*pm.queueMass+
        (logical.top+1)*(2*(cleanBodyBound (16*(ell+3)) length rank+2)+(21*rank+20*(16*(ell+3))+70)+50)+6 ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  exact @NearlyOptimalPPR.Computation.priority_exec
