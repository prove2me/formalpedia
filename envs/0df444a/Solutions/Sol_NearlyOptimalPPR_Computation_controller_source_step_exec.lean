-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.controller_source_step_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:29:58.729693+00:00
-- url     : https://prove2.me/submissions/300baafe-dae1-4c0e-8627-5f8960142b06

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
import Theorems.Thm_NearlyOptimalPPR_Computation_controller_pc_exec
import Theorems.Thm_NearlyOptimalPPR_Computation_normalization_composes
import Theorems.Thm_NearlyOptimalPPR_Computation_push_correctness_work
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_level_work
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_residual_error
import Theorems.Thm_NearlyOptimalPPR_Computation_root_component_solve_exec
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

-- Proof module: Solutions.CompilerBoundaryFacts

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma compiler_source_graphCut_nonneg (g : InputGraph n) (H : Finset (Fin n)) : 0 ≤ graphCut g H := by
  apply Finset.sum_nonneg
  intro v _
  apply Finset.sum_nonneg
  intro u _
  split <;> norm_num

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma compiler_source_boundary_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    (debit st j w).boundaryEdges = st.boundaryEdges := rfl
@[simp] lemma compiler_source_boundary_changeFrame (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).boundaryEdges = st.boundaryEdges := rfl
@[simp] lemma compiler_source_boundary_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).boundaryEdges = st.boundaryEdges := rfl
@[simp] lemma compiler_source_active_debit (st : RecursiveState n) (j i : ℕ) (w : ℝ≥0∞) :
    ((debit st j w).frames i).active = (st.frames i).active := by
  classical
  simp [debit]
@[simp] lemma compiler_source_active_changeFrame (st : RecursiveState n) (j i : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) :
    ((changeFrame st j f).frames i).active =
      if i = j then (f (st.frames j)).active else (st.frames i).active := by
  classical
  by_cases h : i = j <;> simp [changeFrame,h]
@[simp] lemma compiler_source_active_refresh (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).active = (st.frames i).active := by
  classical
  by_cases h : i ≤ st.top <;> simp [refreshKeys,h]

@[simp] lemma compiler_source_boundary_id_debit (g : InputGraph n) (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    BoundaryIdentity g (debit st j w) ↔ BoundaryIdentity g st := by
  simp [BoundaryIdentity]

@[simp] lemma compiler_source_boundary_id_changeFrame (g : InputGraph n) (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hf : (f (st.frames j)).active = (st.frames j).active) :
    BoundaryIdentity g (changeFrame st j f) ↔ BoundaryIdentity g st := by
  by_cases he : (0 : ℕ) = j <;> simp_all (config := {maxSteps := 500000}) [BoundaryIdentity]

@[simp] lemma compiler_source_boundary_id_changePC (g : InputGraph n) (st : RecursiveState n) (pc : NormalizePC) :
    BoundaryIdentity g (changePC st pc) ↔ BoundaryIdentity g st :=
  compiler_source_boundary_id_changeFrame g st st.top _ rfl

@[simp] lemma compiler_source_boundary_id_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    BoundaryIdentity g (refreshKeys g st T) ↔ BoundaryIdentity g st := by simp [BoundaryIdentity]

@[simp] lemma compiler_source_boundary_id_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    BoundaryIdentity g (jointUpdate g α st h) ↔ BoundaryIdentity g st := by
  simp [BoundaryIdentity,jointUpdate]

@[simp] lemma compiler_source_boundary_id_finish (g : InputGraph n) (st : RecursiveState n) :
    BoundaryIdentity g (finishEpisode st) ↔ BoundaryIdentity g st := by
  by_cases he : (0 : ℕ) = st.top <;> simp [finishEpisode,BoundaryIdentity,he]

@[simp] lemma compiler_source_boundary_id_complete (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α : ℝ) (st : RecursiveState n) :
    BoundaryIdentity g (completeComponent m g s α st) ↔ BoundaryIdentity g st := Iff.rfl

@[simp] lemma compiler_source_boundary_id_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    BoundaryIdentity g (endCall g α st) ↔ BoundaryIdentity g st := by
  unfold endCall
  dsimp only
  split <;> rfl

@[simp] lemma compiler_source_active_ite (P : Prop) [Decidable P] (a b : RecursiveState n) (i : ℕ) :
    ((if P then a else b).frames i).active =
      if P then (a.frames i).active else (b.frames i).active := by split <;> rfl
@[simp] lemma compiler_source_boundary_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).boundaryEdges = if P then a.boundaryEdges else b.boundaryEdges := by split <;> rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerReachableFacts

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_stored_active_domain {n : ℕ} (g : InputGraph n) (st : RecursiveState n)
    (hStored : StoredInvariant g st) (j : ℕ) (hj : j ≤ st.top) :
    (st.frames j).active ⊆ st.stored ∧ ∀ v ∈ (st.frames j).active, 0<g.graph.degree v :=
  ⟨hStored.1 j hj,fun v hv => hStored.2 v (hStored.1 j hj hv)⟩

lemma compiler_stored_cache_high_domain {n : ℕ} (g : InputGraph n) (st : RecursiveState n)
    (hStored : StoredInvariant g st) (hRegion : RegionInvariant st) (j : ℕ) (hj : j ≤ st.top) :
    (st.frames j).cache ∪ (st.frames j).high ⊆ st.stored ∧
      ∀ v ∈ (st.frames j).cache ∪ (st.frames j).high, 0<g.graph.degree v := by
  have hActive : (st.frames j).cache ∪ (st.frames j).high ⊆ (st.frames j).active :=
    Finset.union_subset (hRegion j hj).2.2.2 (hRegion j hj).2.2.1
  exact ⟨hActive.trans (hStored.1 j hj),fun v hv => hStored.2 v (hStored.1 j hj (hActive hv))⟩

lemma compiler_boundary_nat {n : ℕ} (g : InputGraph n) (st : RecursiveState n)
    (hBoundary : BoundaryIdentity g st) : ∃ b : ℕ, st.boundaryEdges=(b : ℤ) := by
  have hNonnegative : 0 ≤ st.boundaryEdges := by
    rw [show st.boundaryEdges=graphCut g (st.frames 0).active from hBoundary]
    exact compiler_source_graphCut_nonneg g _
  exact ⟨st.boundaryEdges.toNat,by omega⟩

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

lemma recursiveStep_spawnChild (m : SolveModel) {n : ℕ} (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (logical : RecursiveState n) (hd : logical.done=false)
    (hComp : ¬componentComplete logical) (hPC : (logical.frames logical.top).pc=.normalize)
    (hEx : ¬anyExhausted logical) (hDepth : logical.top ≠ ell) :
    recursiveStep m g s α ell [] logical=spawnChildState g ell logical := by
  simp [recursiveStep,hd,hComp,hPC,hEx,hDepth,spawnChildState]

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

-- Proof module: Solutions.ControllerMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


def ControllerMemory.payUnit {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st) :
    ControllerMemory g s α ε ell length logical (NearlyOptimalPPR.Computation.payUnit st) := {
  one := memory.one
  doneFlag := memory.doneFlag
  halted := memory.halted
  live := fun h => (memory.live h).payUnit
  epoch := memory.epoch
  output := memory.output
}

lemma ControllerMemory.payUnit_mass {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st) :
    memory.payUnit.mass=memory.mass := by
  unfold ControllerMemory.mass
  split_ifs <;> rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerMemoryConstruction

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def ControllerMemory.ofLive {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (h150 : st.scalar.core.ptrs 150=0) (h151 : st.scalar.core.ptrs 151=1)
    (hh : st.scalar.halted=false) (hE : EpochInvariant (n:=n) (16*(ell+3)) st) :
    ControllerMemory g s α ε ell length logical st := {
  one := h151
  doneFlag := by rw [hDone]; exact h150
  halted := hh
  live := fun _ => pm
  epoch := fun _ => hE
  output := by intro h; have hBad := hDone.symm.trans h; cases hBad
}

lemma ControllerMemory.ofLive_mass {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (h150 : st.scalar.core.ptrs 150=0) (h151 : st.scalar.core.ptrs 151=1)
    (hh : st.scalar.halted=false) (hE : EpochInvariant (n:=n) (16*(ell+3)) st) :
    (ControllerMemory.ofLive pm hDone h150 h151 hh hE).mass=pm.queueMass := by
  unfold ControllerMemory.mass
  rw [dif_pos hDone]
  rfl

def ControllerMemory.ofDone {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState}
    (hDone : logical.done=true) (h150 : st.scalar.core.ptrs 150=1) (h151 : st.scalar.core.ptrs 151=1)
    (hh : st.scalar.halted=false) (hOutput : outputVector (n:=n) st.output=outputVector (n:=n) logical.output) :
    ControllerMemory g s α ε ell length logical st := {
  one := h151
  doneFlag := by rw [hDone]; exact h150
  halted := hh
  live := by intro h; have hBad := h.symm.trans hDone; cases hBad
  epoch := by intro h; have hBad := h.symm.trans hDone; cases hBad
  output := fun _ => hOutput
}

lemma ControllerMemory.mass_done {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=true) : memory.mass=0 := by
  unfold ControllerMemory.mass
  rw [dif_neg (by rw [hDone]; decide)]

lemma ControllerMemory.mass_live {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) : memory.mass=(memory.live hDone).queueMass := by
  unfold ControllerMemory.mass
  rw [dif_pos hDone]


end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerLiveTransport

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def ControllerMemory.nextLive {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {s : Fin n} {α ε : ℝ} {ell length : ℕ} {logical next : RecursiveState n}
    {st out : MachineState} {code : MachineCode} {steps : ℕ}
    (memory : ControllerMemory g s α ε ell length logical st) (hDone : logical.done=false)
    (pm : RecursiveMachineMemory g s α ε ell length next out) (hNext : next.done=false)
    (e : MachineEval m g ω code st steps out) (h150 : 150 ∉ code.pointerTargets) (h151 : 151 ∉ code.pointerTargets)
    (hh : out.scalar.halted=false) (hEpoch : EpochInvariant (n:=n) (16*(ell+3)) out) :
    ControllerMemory g s α ε ell length next out :=
  ControllerMemory.ofLive pm hNext (by rw [e.pointer_frame 150 h150,memory.doneFlag,hDone]; rfl)
    ((e.pointer_frame 151 h151).trans memory.one) hh hEpoch

lemma ControllerMemory.nextLive_mass {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {s : Fin n} {α ε : ℝ} {ell length : ℕ} {logical next : RecursiveState n}
    {st out : MachineState} {code : MachineCode} {steps : ℕ}
    (memory : ControllerMemory g s α ε ell length logical st) (hDone : logical.done=false)
    (pm : RecursiveMachineMemory g s α ε ell length next out) (hNext : next.done=false)
    (e : MachineEval m g ω code st steps out) (h150 : 150 ∉ code.pointerTargets) (h151 : 151 ∉ code.pointerTargets)
    (hh : out.scalar.halted=false) (hEpoch : EpochInvariant (n:=n) (16*(ell+3)) out) :
    (memory.nextLive hDone pm hNext e h150 h151 hh hEpoch).mass=pm.queueMass :=
  ControllerMemory.ofLive_mass _ _ _ _ _ _

lemma ControllerMemory.indexInvariant {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {s : Fin n} {α ε : ℝ} {ell length : ℕ} {logical : RecursiveState n}
    {st out : MachineState} {code : MachineCode} {steps : ℕ}
    (memory : ControllerMemory g s α ε ell length logical st) (hDone : logical.done=false)
    (e : MachineEval m g ω code st steps out) (h53 : 53 ∉ code.pointerTargets)
    (hMarks : ∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
      st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) :
    EpochInvariant (n:=n) (16*(ell+3)) out := by
  intro v
  rw [hMarks v,e.pointer_frame 53 h53]
  exact memory.epoch hDone v

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerPointerFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def ControllerMemory.dispatchWrite {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st) (value : ℤ) :
    ControllerMemory g s α ε ell length logical (pointerWrite st 153 value) := {
  one := by simpa [pointerWrite] using memory.one
  doneFlag := by simpa [pointerWrite] using memory.doneFlag
  halted := memory.halted
  live := fun h => (memory.live h).pointerWrite 153 value (by decide)
  epoch := by intro h v; exact memory.epoch h v
  output := memory.output
}

lemma ControllerMemory.dispatchWrite_mass {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st) (value : ℤ) :
    (memory.dispatchWrite value).mass=memory.mass := by
  unfold ControllerMemory.mass
  split_ifs <;> rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerCachePotential

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma ControllerMemory.potential_payUnit {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st)
    (P Q : ℕ) : memory.payUnit.potential P Q=memory.potential P Q := by
  simp only [ControllerMemory.potential,ControllerMemory.payUnit_mass]

lemma ControllerMemory.potential_dispatchWrite {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st)
    (P Q : ℕ) (z : ℤ) : (memory.dispatchWrite z).potential P Q=memory.potential P Q := by
  simp only [ControllerMemory.potential,ControllerMemory.dispatchWrite_mass]


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

-- Proof module: Solutions.BudgetScanCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma budgetScanMarkCode_wellFormed : budgetScanMarkCode.wellFormed := by
  refine ⟨levelHeaderRealToCode_wellFormed 3 60,levelHeaderRealToCode_wellFormed 4 61,?_,?_,trivial⟩ <;>
    simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma budgetScanBodyCode_wellFormed : budgetScanBodyCode.wellFormed := by
  refine ⟨levelHeaderIntegerToCode_wellFormed 9 166,⟨trivial,budgetScanMarkCode_wellFormed⟩,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma budgetScanCode_wellFormed : budgetScanCode.wellFormed := by
  refine ⟨?_,budgetScanBodyCode_wellFormed,?_⟩ <;>
    simp [budgetScanInitRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
      coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetScanMarkExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 5000000 in
lemma budget_scan_mark_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (level : ℕ) (Q W : ℝ) (st : MachineState) (hh : st.scalar.halted=false)
    (hLevel : st.scalar.core.ptrs 100=(level : ℤ)) (hOne : st.scalar.core.regs 31=1)
    (hQ : st.scalar.core.mem (levelHeaderAddress level 3)=Q)
    (hW : st.scalar.core.mem (levelHeaderAddress level 4)=W) :
    ∃ out, MachineEval m g ω budgetScanMarkCode st 23 out ∧
      out.scalar.core.ptrs 160=(if Q ≤ W then 1 else st.scalar.core.ptrs 160) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+23 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a60,aI,aR,aWork,aOutput,aH⟩ := level_header_real_to_exec m g ω st hh level 3 60 hLevel hOne
  have aLevel := (ea.pointer_frame 100 (by decide)).trans hLevel
  have aOne := (ea.real_register_frame 31 (by decide)).trans hOne
  have aQ : a.scalar.core.regs 60=Q := a60.trans hQ
  obtain ⟨b,eb,b61,bI,bR,bWork,bOutput,bH⟩ := level_header_real_to_exec m g ω a aH level 4 61 aLevel aOne
  have bW : b.scalar.core.regs 61=W := by rw [b61,aR]; exact hW
  have bQ := (eb.real_register_frame 60 (by decide)).trans aQ
  let mid := payUnit (realWrite b 62 (Q-W))
  have ec : MachineEval m g ω (coreCode (.sub 62 60 61)) b 1 mid := by
    simpa only [coreCode,RealOperation.instruction,RealOperation.value,bQ,bW,mid] using binary_eval m g ω b .sub 62 60 61 bH
  have hMid : mid.scalar.core.regs 62=Q-W := by simp [mid,payUnit,pcSet,realWrite]
  have hMidH : mid.scalar.halted=false := bH
  have hPrefix := MachineEval.seq ea (MachineEval.seq eb ec)
  have hMidI : mid.scalar.integerMemory=st.scalar.integerMemory := bI.trans aI
  have hMidR : mid.scalar.core.mem=st.scalar.core.mem := bR.trans aR
  have hMidO : mid.output=st.output := bOutput.trans aOutput
  have hMid160 : mid.scalar.core.ptrs 160=st.scalar.core.ptrs 160 :=
    hPrefix.pointer_frame 160 (by decide)
  by_cases hEx : Q ≤ W
  · let out := payUnit (pointerWrite (payUnit mid) 160 1)
    have ed : MachineEval m g ω (coreCode (.pset 160 1)) (payUnit mid) 1 out := pset_eval m g ω (payUnit mid) 160 1 hMidH
    have er : MachineEval m g ω (.branchReal 62 (coreCode (.pset 160 1)) .skip) mid 2 out :=
      MachineEval.realNonpos hMidH (by rw [hMid]; linarith) ed
    have ex : MachineEval m g ω budgetScanMarkCode st 23 out := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec er))
    refine ⟨out,ex,?_,hMidI,hMidR,?_,hMidO,bH⟩
    · simp [out,payUnit,pcSet,pointerWrite,hEx]
    · change b.work+1+1+1= _
      rw [bWork,aWork]
      norm_num; ring
  · let out := payUnit (payUnit mid)
    have er : MachineEval m g ω (.branchReal 62 (coreCode (.pset 160 1)) .skip) mid 2 out :=
      MachineEval.realPos hMidH (by rw [hMid]; linarith) (MachineEval.skip (payUnit mid))
    have ex : MachineEval m g ω budgetScanMarkCode st 23 out := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec er))
    refine ⟨out,ex,?_,hMidI,hMidR,?_,hMidO,bH⟩
    · change mid.scalar.core.ptrs 160= _
      rw [hMid160,if_neg hEx]
    · change b.work+1+1+1= _
      rw [bWork,aWork]
      norm_num; ring

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

-- Proof module: Solutions.BudgetScanBodyExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 6000000 in
lemma budget_scan_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (level : ℕ) (Q W : ℝ) (openBudget : Bool) (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (hLevel : st.scalar.core.ptrs 100=(level : ℤ)) (hOne : st.scalar.core.regs 31=1)
    (hOpen : st.scalar.integerMemory (levelHeaderAddress level 9)=if openBudget then 1 else 0)
    (hQ : st.scalar.core.mem (levelHeaderAddress level 3)=Q)
    (hW : st.scalar.core.mem (levelHeaderAddress level 4)=W) :
    ∃ steps out, MachineEval m g ω budgetScanBodyCode st steps out ∧ steps ≤ 36 ∧
      out.scalar.core.ptrs 100=((level+1 : ℕ) : ℤ) ∧
      out.scalar.core.ptrs 160=(if openBudget=true ∧ Q ≤ W then 1 else st.scalar.core.ptrs 160) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a166,aI,aR,aWork,aOutput,aH⟩ := level_header_integer_to_exec m g ω st hh level 9 166 hLevel
  have aOpen := a166.trans hOpen
  have a0 := (ea.pointer_frame 0 (by decide)).trans h0
  have a100 := (ea.pointer_frame 100 (by decide)).trans hLevel
  have a160 := ea.pointer_frame 160 (by decide)
  have a31 := (ea.real_register_frame 31 (by decide)).trans hOne
  cases hBool : openBudget with
  | false =>
    have aClosed : a.scalar.core.ptrs 166=0 := by simpa only [hBool,Bool.false_eq_true,if_false] using aOpen
    let mid := payUnit a
    have eb : MachineEval m g ω (.branchPointer 166 0 .skip budgetScanMarkCode) a 1 mid :=
      MachineEval.pointerLe aH (by rw [aClosed,a0]) (MachineEval.skip (payUnit a))
    let out := payUnit (pointerWrite mid 100 ((level : ℤ)+1))
    have ec : MachineEval m g ω (coreCode (.pinc 100)) mid 1 out := by
      simpa only [coreCode,mid,payUnit_ptrs,a100,out] using pinc_eval m g ω mid 100 aH
    have ex : MachineEval m g ω budgetScanBodyCode st 12 out := MachineEval.seq ea (MachineEval.seq eb ec)
    refine ⟨12,out,ex,by omega,?_,?_,aI,aR,ex.unit_work budgetScanBodyCode_wellFormed (by decide) hh,aOutput,aH⟩
    · simp [out,payUnit,pcSet,pointerWrite]
    · change a.scalar.core.ptrs 160= _
      simp only [hBool,Bool.false_eq_true,false_and,if_false]
      exact a160
  | true =>
    have aOpened : a.scalar.core.ptrs 166=1 := by simpa only [hBool,if_true] using aOpen
    have aQ : a.scalar.core.mem (levelHeaderAddress level 3)=Q := by rw [aR]; exact hQ
    have aW : a.scalar.core.mem (levelHeaderAddress level 4)=W := by rw [aR]; exact hW
    obtain ⟨b,eb,b160,bI,bR,bWork,bOutput,bH⟩ := budget_scan_mark_exec m g ω level Q W (payUnit a) aH a100 a31 aQ aW
    let mid := payUnit b
    have ec : MachineEval m g ω (.branchPointer 166 0 .skip budgetScanMarkCode) a 25 mid :=
      MachineEval.pointerGt aH (by rw [aOpened,a0]; omega) eb
    have b100 := (eb.pointer_frame 100 (by decide)).trans a100
    let out := payUnit (pointerWrite mid 100 ((level : ℤ)+1))
    have ed : MachineEval m g ω (coreCode (.pinc 100)) mid 1 out := by
      simpa only [coreCode,mid,payUnit_ptrs,b100,out] using pinc_eval m g ω mid 100 bH
    have ex : MachineEval m g ω budgetScanBodyCode st 36 out := MachineEval.seq ea (MachineEval.seq ec ed)
    refine ⟨36,out,ex,le_rfl,?_,?_,bI.trans aI,bR.trans aR,ex.unit_work budgetScanBodyCode_wellFormed (by decide) hh,bOutput.trans aOutput,bH⟩
    · simp [out,payUnit,pcSet,pointerWrite]
    · change b.scalar.core.ptrs 160= _
      rw [b160]
      simp only [hBool,true_and,payUnit_ptrs,a160]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetScanLoopExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma budget_prefix_succ {n : ℕ} (logical : RecursiveState n) (index : ℕ) :
    (∃ j < index+1, exhausted logical j) ↔ exhausted logical index ∨ ∃ j < index, exhausted logical j := by
  constructor
  · rintro ⟨j,hj,he⟩
    by_cases hEq : j=index
    · exact Or.inl (hEq ▸ he)
    · exact Or.inr ⟨j,by omega,he⟩
  · rintro (he|⟨j,hj,he⟩)
    · exact ⟨index,by omega,he⟩
    · exact ⟨j,by omega,he⟩

set_option maxHeartbeats 8000000 in
lemma budget_scan_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (limit index remaining : ℕ) (hCount : index+remaining=limit)
    (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (h100 : st.scalar.core.ptrs 100=(index : ℤ))
    (h164 : st.scalar.core.ptrs 164=(limit : ℤ)) (hOne : st.scalar.core.regs 31=1)
    (hAcc : st.scalar.core.ptrs 160=(if ∃ j < index, exhausted logical j then 1 else 0))
    (hOpen : ∀ j < limit, st.scalar.integerMemory (levelHeaderAddress j 9)=if (logical.frames j).openBudget then 1 else 0)
    (hQ : ∀ j < limit, st.scalar.core.mem (levelHeaderAddress j 3)=(logical.frames j).Q)
    (hW : ∀ j < limit, st.scalar.core.mem (levelHeaderAddress j 4)=(logical.frames j).W) :
    ∃ steps out, MachineEval m g ω budgetScanLoopCode st steps out ∧ steps ≤ 38*remaining+1 ∧
      out.scalar.core.ptrs 100=(limit : ℤ) ∧
      out.scalar.core.ptrs 160=(if ∃ j < limit, exhausted logical j then 1 else 0) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  classical
  induction remaining generalizing st index with
  | zero =>
    have hi : index=limit := by omega
    refine ⟨1,payUnit st,MachineEval.pointerDone hh (by rw [h164,h100,hi]),by omega,?_,?_,rfl,rfl,rfl,by simp,rfl,hh⟩
    · simpa only [payUnit_ptrs,hi] using h100
    · simpa only [payUnit_ptrs,hi] using hAcc
  | succ remaining ih =>
    have hi : index < limit := by omega
    obtain ⟨u,mid,eb,hu,hm100,hm160,hmI,hmR,hmWork,hmOutput,hmH⟩ := budget_scan_body_exec m g ω index
      (logical.frames index).Q (logical.frames index).W (logical.frames index).openBudget (payUnit st) hh
      h0 h100 hOne (hOpen index hi) (hQ index hi) (hW index hi)
    have hm0 := (eb.pointer_frame 0 (by decide)).trans h0
    have hm164 := (eb.pointer_frame 164 (by decide)).trans h164
    have hmOne := (eb.real_register_frame 31 (by decide)).trans hOne
    have hmAcc : mid.scalar.core.ptrs 160=(if ∃ j < index+1, exhausted logical j then 1 else 0) := by
      rw [hm160]
      have hCurrentIff : ((logical.frames index).openBudget=true ∧
          (logical.frames index).Q ≤ (logical.frames index).W) ↔ exhausted logical index := Iff.rfl
      simp only [payUnit_ptrs,hCurrentIff,hAcc]
      by_cases hCurrent : exhausted logical index <;> by_cases hOld : ∃ j < index, exhausted logical j <;>
        simp only [budget_prefix_succ,hCurrent,hOld,true_or,false_or,if_true,if_false]
    have hmOpen : ∀ j < limit, mid.scalar.integerMemory (levelHeaderAddress j 9)=if (logical.frames j).openBudget then 1 else 0 := by
      rw [hmI]; exact hOpen
    have hmQ : ∀ j < limit, mid.scalar.core.mem (levelHeaderAddress j 3)=(logical.frames j).Q := by rw [hmR]; exact hQ
    have hmW : ∀ j < limit, mid.scalar.core.mem (levelHeaderAddress j 4)=(logical.frames j).W := by rw [hmR]; exact hW
    obtain ⟨v,out,er,hv,ho100,ho160,hoI,hoR,hoQ,hoWork,hoOutput,hoH⟩ :=
      ih (index+1) (by omega) (payUnit mid) hmH hm0 hm100 hm164 hmOne hmAcc hmOpen hmQ hmW
    have ex : MachineEval m g ω budgetScanLoopCode st (1+u+1+v) out :=
      MachineEval.pointerNext hh (by rw [h164,h100]; omega) eb er
    refine ⟨1+u+1+v,out,ex,by omega,ho100,ho160,hoI.trans hmI,hoR.trans hmR,?_,
      ex.unit_work budgetScanBodyCode_wellFormed (by decide) hh,hoOutput.trans hmOutput,hoH⟩
    exact hoQ.trans (eb.query_frame (by decide))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetScanExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 9000000 in
lemma budget_scan_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length limit : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hLimit : limit ≤ logical.top+1) (h164 : st.scalar.core.ptrs 164=(limit : ℤ)) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω budgetScanCode st steps out ∧ steps ≤ 38*limit+5 ∧
      out.scalar.core.ptrs 160=(if ∃ j < limit, exhausted logical j then 1 else 0) ∧
      memory.queueMass=pm.queueMass ∧ out.work=st.work+steps ∧ out.scalar.queries=st.scalar.queries ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,aP,aI,aR,aW,aO,aH⟩ := budgetScanInitRoutine.execute m g ω st hh
  have ea3 : MachineEval m g ω budgetScanInitRoutine.code st 3 a := ea
  have a0 := (ea.pointer_frame 0 (by decide)).trans pm.zero
  have a164 := (ea.pointer_frame 164 (by decide)).trans h164
  have a31 := (ea.real_register_frame 31 (by decide)).trans pm.one
  have a100 : a.scalar.core.ptrs 100=0 := by
    rw [aP]; simp [budgetScanInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result]
  have a165 : a.scalar.core.ptrs 165=st.scalar.core.ptrs 100 := by
    rw [aP]; simp [budgetScanInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result]
  have a160 : a.scalar.core.ptrs 160=(if ∃ j < 0, exhausted logical j then 1 else 0) := by
    rw [aP]; simp [budgetScanInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result]
  have aOpen : ∀ j < limit, a.scalar.integerMemory (levelHeaderAddress j 9)=if (logical.frames j).openBudget then 1 else 0 := by
    intro j hj
    rw [aI]
    exact (pm.frames j (by omega)).openBudget
  have aQ : ∀ j < limit, a.scalar.core.mem (levelHeaderAddress j 3)=(logical.frames j).Q := by
    intro j hj
    rw [aR]
    exact (pm.frames j (by omega)).Q
  have aBudgetW : ∀ j < limit, a.scalar.core.mem (levelHeaderAddress j 4)=(logical.frames j).W := by
    intro j hj
    rw [aR]
    exact (pm.frames j (by omega)).W
  obtain ⟨u,b,eb,hu,b100,b160,bI,bR,bQ,bW,bO,bH⟩ := budget_scan_loop_exec m g ω logical limit 0 limit (by omega)
    a aH a0 a100 a164 a31 (by simpa using a160) aOpen aQ aBudgetW
  have b165 := (eb.pointer_frame 165 (by decide)).trans a165
  let out := payUnit (pointerWrite b 100 (st.scalar.core.ptrs 100))
  have ec : MachineEval m g ω (coreCode (.pcopy 100 165)) b 1 out := by
    simpa only [coreCode,b165,out] using pcopy_eval m g ω b 100 165 bH
  have ex : MachineEval m g ω budgetScanCode st (3+(u+1)) out := MachineEval.seq ea3 (MachineEval.seq eb ec)
  have hI : out.scalar.integerMemory=st.scalar.integerMemory := bI.trans aI
  have hR : out.scalar.core.mem=st.scalar.core.mem := bR.trans aR
  have hO : out.output=st.output := bO.trans aO
  have hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact ex.pointer_frame 0 (by decide)
    · exact ex.pointer_frame 20 (by decide)
    · exact ex.pointer_frame 50 (by decide)
    · simp [out,payUnit,pcSet,pointerWrite]
  have hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ex.real_register_frame _ (by decide)
  let memory := pm.frame hI hR hP hG hO
  refine ⟨3+(u+1),out,memory,ex,by omega,?_,rfl,
    ex.unit_work budgetScanCode_wellFormed (by decide) hh,ex.query_frame (by decide),hO,bH⟩
  have hFlag := (ec.pointer_frame 160 (by decide)).trans b160
  by_cases hExists : ∃ j < limit, exhausted logical j <;>
    simpa only [hExists,if_true,if_false] using hFlag

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetCheckExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

def budgetCheckLimit {n : ℕ} (logical : RecursiveState n) (ancestorsOnly : Bool) : ℕ :=
  if ancestorsOnly then logical.top else logical.top+1
def budgetCheckPredicate {n : ℕ} (logical : RecursiveState n) (ancestorsOnly : Bool) : Prop :=
  if ancestorsOnly then ancestorExhausted logical else anyExhausted logical

lemma budgetCheckCode_wellFormed (ancestorsOnly : Bool) : (budgetCheckCode ancestorsOnly).wellFormed := by
  refine ⟨?_,budgetScanCode_wellFormed⟩
  cases ancestorsOnly <;> simp [budgetCheckPrefixRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 10000000 in
lemma budget_check_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ) (ancestorsOnly : Bool)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω (budgetCheckCode ancestorsOnly) st steps out ∧ steps ≤ 38*(logical.top+1)+7 ∧
      out.scalar.core.ptrs 160=(if budgetCheckPredicate logical ancestorsOnly then 1 else 0) ∧
      memory.queueMass=pm.queueMass ∧ out.work=st.work+steps ∧ out.scalar.queries=st.scalar.queries ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,ep,hP,hI,hR,hW,hO,hH⟩ := (budgetCheckPrefixRoutine ancestorsOnly).execute m g ω st hh
  have hPrefixCost : ((budgetCheckPrefixRoutine ancestorsOnly).run st.scalar.integerMemory st.scalar.core.ptrs).1 ≤ 2 := by
    cases ancestorsOnly <;> simp [budgetCheckPrefixRoutine,PointerRoutine.sequence,PointerRoutine.run]
  have h164 : pre.scalar.core.ptrs 164=(budgetCheckLimit logical ancestorsOnly : ℤ) := by
    rw [hP]
    cases ancestorsOnly <;> simp [budgetCheckPrefixRoutine,budgetCheckLimit,PointerRoutine.sequence,PointerRoutine.run,
      PointerOp.update,PointerOp.destination,PointerOp.result,pm.top]
  have hPtrs : ∀ r ∈ ([0,20,50,100] : List ℕ), pre.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    cases ancestorsOnly <;>
      (simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
       rcases hr with rfl|rfl|rfl|rfl <;> exact ep.pointer_frame _ (by decide))
  have hRegs : ∀ r ∈ ([30,31] : List ℕ), pre.scalar.core.regs r=st.scalar.core.regs r := by
    intro r hr
    cases ancestorsOnly <;>
      (simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
       rcases hr with rfl|rfl <;> exact ep.real_register_frame _ (by decide))
  let preMemory := pm.frame hI hR hPtrs hRegs hO
  have hLimit : budgetCheckLimit logical ancestorsOnly ≤ logical.top+1 := by
    cases ancestorsOnly <;> simp [budgetCheckLimit]
  obtain ⟨u,out,memory,eb,hu,h160,hMass,hWork,hQuery,hOutput,hHalt⟩ := budget_scan_exec m g ω logical s α ε ell length
    (budgetCheckLimit logical ancestorsOnly) pre hH preMemory hLimit h164
  have hPred : (∃ j < budgetCheckLimit logical ancestorsOnly, exhausted logical j) ↔ budgetCheckPredicate logical ancestorsOnly := by
    cases ancestorsOnly <;> simp [budgetCheckLimit,budgetCheckPredicate,anyExhausted,ancestorExhausted,Nat.lt_succ_iff]
  have ex := MachineEval.seq ep eb
  refine ⟨_,out,memory,ex,by omega,?_,hMass,?_,?_,hOutput.trans hO,hHalt⟩
  · simpa only [hPred] using h160
  · exact ex.unit_work (budgetCheckCode_wellFormed ancestorsOnly) (by cases ancestorsOnly <;> decide) hh
  · exact hQuery.trans (ep.query_frame (by cases ancestorsOnly <;> decide))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetStatusExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma budgetStatusCode_wellFormed : budgetStatusCode.wellFormed := by
  refine ⟨budgetCheckCode_wellFormed _,?_,budgetCheckCode_wellFormed _⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 10000000 in
lemma budget_status_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω budgetStatusCode st steps out ∧ steps ≤ 76*(logical.top+1)+15 ∧
      out.scalar.core.ptrs 170=(if ancestorExhausted logical then 1 else 0) ∧
      out.scalar.core.ptrs 160=(if anyExhausted logical then 1 else 0) ∧
      memory.queueMass=pm.queueMass ∧ out.scalar.integerMemory=st.scalar.integerMemory ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+steps ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨u,a,am,ea,hu,aFlag,aMass,aW,aQ,aO,aH⟩ := budget_check_exec m g ω logical s α ε ell length true st hh pm
  let b := payUnit (pointerWrite a 170 (a.scalar.core.ptrs 160))
  have eb : MachineEval m g ω (coreCode (.pcopy 170 160)) a 1 b := pcopy_eval m g ω a 170 160 aH
  let bm := (am.pointerWrite 170 (a.scalar.core.ptrs 160) (by decide)).payUnit
  obtain ⟨v,out,memory,ec,hv,cFlag,cMass,cW,cQ,cO,cH⟩ := budget_check_exec m g ω logical s α ε ell length false b aH bm
  have ex : MachineEval m g ω budgetStatusCode st (u+(1+v)) out := MachineEval.seq ea (MachineEval.seq eb ec)
  have b170 : b.scalar.core.ptrs 170=(if ancestorExhausted logical then 1 else 0) := by
    change Function.update a.scalar.core.ptrs 170 (a.scalar.core.ptrs 160) 170=_
    simpa [budgetCheckPredicate] using aFlag
  refine ⟨u+(1+v),out,memory,ex,by omega,(ec.pointer_frame 170 (by decide)).trans b170,cFlag,?_,
    ex.integer_memory_frame (by decide),ex.real_memory_frame (by decide),
    ex.unit_work budgetStatusCode_wellFormed (by decide) hh,cQ.trans aQ,cO.trans aO,cH⟩
  change memory.queueMass=am.queueMass at cMass
  exact cMass.trans aMass

lemma any_exhausted_of_no_ancestor {n : ℕ} (logical : RecursiveState n)
    (h : ¬ancestorExhausted logical) : anyExhausted logical ↔ exhausted logical logical.top := by
  constructor
  · rintro ⟨i,hi,he⟩
    have heq : i=logical.top := by
      by_contra hn
      exact h ⟨i,by omega,he⟩
    simpa only [heq] using he
  · exact fun he => ⟨logical.top,le_rfl,he⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerBudgetFlags

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma ControllerBudgetFlags.payUnit {n : ℕ} {logical : RecursiveState n} {st : MachineState}
    (h : ControllerBudgetFlags logical st) : ControllerBudgetFlags logical (payUnit st) := h

lemma ControllerBudgetFlags.dispatchWrite {n : ℕ} {logical : RecursiveState n} {st : MachineState}
    (h : ControllerBudgetFlags logical st) (z : ℤ) : ControllerBudgetFlags logical (pointerWrite st 153 z) := by
  simpa only [ControllerBudgetFlags,pointerWrite,Function.update_of_ne (show (160 : ℕ) ≠ 153 by decide),
    Function.update_of_ne (show (170 : ℕ) ≠ 153 by decide)] using h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerBeginEpisodeSource

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_begin_view {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (logical : RecursiveState n)
    (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hPC : (logical.frames logical.top).pc=.beginEpisode) :
    recursiveStep m g s α ell schedule logical=compilerBeginEpisode m g logical := by
  simp only [recursiveStep,hDone,Bool.false_eq_true,if_false,hComp,hPC]
  rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerFinishRequestSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_finish_view {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (logical : RecursiveState n)
    (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hPC : (logical.frames logical.top).pc=.finishEpisode)
    (hAncestor : ¬ancestorExhausted logical) (hCurrent : ¬exhausted logical logical.top) :
    recursiveStep m g s α ell schedule logical=compilerFinishRequest g logical := by
  classical
  simp only [recursiveStep,hDone,Bool.false_eq_true,if_false,hComp,hPC,hAncestor,hCurrent]
  simp only [compilerFinishRequest,compilerSetNeedFull,changePC,changeFrame,finishEpisode,debit,
    Function.update_self,Function.update_idem]

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

-- Proof module: Solutions.CompilerLeafSolveSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_leaf_view {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (logical : RecursiveState n)
    (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hPC : (logical.frames logical.top).pc=.leafDrain)
    (hBudget : ¬anyExhausted logical) (hPending : pendingPush logical=none)
    (hHigh : (logical.frames logical.top).high ≠ ∅)
    (hStored : (logical.frames logical.top).cache ∪ (logical.frames logical.top).high ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames logical.top).cache ∪ (logical.frames logical.top).high,
      0<g.graph.degree v) :
    recursiveStep m g s α ell schedule logical=compilerLeafSolve m g α logical := by
  simp only [recursiveStep,hDone,Bool.false_eq_true,if_false,hComp,hPC,hBudget,hPending,
    Option.isSome_none,hHigh,if_pos (And.intro hStored hDegree)]
  rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerFullSolveSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_full_view {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (logical : RecursiveState n)
    (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hPC : (logical.frames logical.top).pc=.fullSolve)
    (hBudget : ¬anyExhausted logical)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames logical.top).active, 0<g.graph.degree v) :
    recursiveStep m g s α ell schedule logical=compilerFullSolve m g α logical := by
  simp only [recursiveStep,hDone,Bool.false_eq_true,if_false,hComp,hPC,hBudget,
    if_pos (And.intro hStored hDegree)]
  rfl

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

-- Proof module: Solutions.SparseEncoding

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

def decodeEntries (k : ℕ) (entries : List SparseEntry) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => (entries.map fun a => if a.row=(i.val : ℤ) ∧ a.column=(j.val : ℤ) then a.value else 0).sum


@[simp] lemma decodeEntries_nil (k : ℕ) : decodeEntries k []=0 := by
  ext i j
  simp [decodeEntries]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RowAssemblyRemainder

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def remainingRowsBudget {n k : ℕ} (g : InputGraph n) (e : Fin k → Fin n) (i : ℕ) : ℕ :=
  (((List.finRange k).drop i).map (fun row => (g.neighbors (e row)).length+1)).sum

def remainingPrincipalEntries {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) (i : ℕ) : List SparseEntry :=
  ((List.finRange k).drop i).flatMap (principalRowEntries g α e)

@[simp] lemma remainingRowsBudget_done {n k : ℕ} (g : InputGraph n) (e : Fin k → Fin n) : remainingRowsBudget g e k=0 := by
  have hd : (List.finRange k).drop k=[] := by simpa only [List.length_finRange] using (List.drop_length (l:=List.finRange k))
  simp only [remainingRowsBudget,hd,List.map_nil,List.sum_nil]

@[simp] lemma remainingPrincipalEntries_done {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) :
    remainingPrincipalEntries g α e k=[] := by
  have hd : (List.finRange k).drop k=[] := by simpa only [List.length_finRange] using (List.drop_length (l:=List.finRange k))
  simp only [remainingPrincipalEntries,hd,List.flatMap_nil]

@[simp] lemma remainingPrincipalEntries_zero {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) :
    remainingPrincipalEntries g α e 0=principalEntries g α e := by simp [remainingPrincipalEntries,principalEntries]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LeafDecisionExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma compiler_leaf_decision_view {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (logical : RecursiveState n)
    (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hPC : (logical.frames logical.top).pc=.leafDrain)
    (hBudget : ¬anyExhausted logical) (hPending : pendingPush logical=none)
    (hStored : (logical.frames logical.top).cache ∪ (logical.frames logical.top).high ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames logical.top).cache ∪ (logical.frames logical.top).high,
      0<g.graph.degree v) :
    recursiveStep m g s α ell schedule logical=compilerLeafDecision m g α logical := by
  classical
  by_cases hHigh : (logical.frames logical.top).high=∅
  · simp [recursiveStep,hDone,hComp,hPC,hBudget,hPending,hHigh,compilerLeafDecision]
  · rw [compilerLeafDecision,if_neg hHigh]
    exact compiler_leaf_view m g s α ell schedule logical hDone hComp hPC hBudget hPending hHigh hStored hDegree

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.InitialEmptyExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_initial_empty_view {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (logical : RecursiveState n)
    (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hPC : (logical.frames logical.top).pc=.initialDrain)
    (hAncestor : ¬ancestorExhausted logical) (hPending : pendingPush logical=none) :
    recursiveStep m g s α ell schedule logical=compilerInitialEmpty logical := by
  classical
  simp only [recursiveStep,hDone,Bool.false_eq_true,if_false,hComp,hPC,hAncestor,hPending,
    Option.isSome_none,compilerInitialEmpty]
  split_ifs <;> rfl

end
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

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RestartRequestExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_restart_view {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (logical : RecursiveState n)
    (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hPC : (logical.frames logical.top).pc=.restartDrain)
    (hAncestor : ¬ancestorExhausted logical) (hPending : pendingPush logical=none) :
    recursiveStep m g s α ell schedule logical=compilerRestartRequest logical := by
  simp only [recursiveStep,hDone,Bool.false_eq_true,if_false,hComp,hPC,hAncestor,hPending,
    Option.isSome_none]
  simp only [compilerRestartRequest,compilerSetNeedFull,changePC,changeFrame,debit,
    Function.update_self,Function.update_idem]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerFullExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_full_decision_view {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (logical : RecursiveState n)
    (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hPC : (logical.frames logical.top).pc=.fullSolve)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames logical.top).active, 0<g.graph.degree v) :
    recursiveStep m g s α ell schedule logical=compilerFullDecision m g α logical := by
  by_cases hAny : anyExhausted logical
  · simp [recursiveStep,hDone,hComp,hPC,hAny,compilerFullDecision]
  · rw [compilerFullDecision,if_neg hAny]
    exact compiler_full_view m g s α ell schedule logical hDone hComp hPC hAny hStored hDegree

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerInitialRestart

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_initial_controller_view {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (logical : RecursiveState n)
    (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hPC : (logical.frames logical.top).pc=.initialDrain) :
    recursiveStep m g s α ell schedule logical=compilerInitialRestart g α logical .initialDrain (compilerInitialEmpty logical) := by
  by_cases hA : ancestorExhausted logical
  · simp [recursiveStep,hDone,hComp,hPC,hA,compilerInitialRestart]
  · rw [compilerInitialRestart,if_pos hA]
    cases hp : pendingPush logical with
    | none =>
      rw [compilerPriorityChoice,hp]
      simp only [Option.isSome_none,Bool.false_eq_true,if_false]
      exact compiler_initial_empty_view m g s α ell schedule logical hDone hComp hPC hA hp
    | some pair =>
      obtain ⟨t,v⟩ := pair
      simp [recursiveStep,hDone,hComp,hPC,hA,hp,compilerPriorityChoice,compilerSelectedDrain,compilerDrain]

lemma compiler_restart_controller_view {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (logical : RecursiveState n)
    (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hPC : (logical.frames logical.top).pc=.restartDrain) :
    recursiveStep m g s α ell schedule logical=compilerInitialRestart g α logical .restartDrain (compilerRestartRequest logical) := by
  by_cases hA : ancestorExhausted logical
  · simp [recursiveStep,hDone,hComp,hPC,hA,compilerInitialRestart]
  · rw [compilerInitialRestart,if_pos hA]
    cases hp : pendingPush logical with
    | none =>
      rw [compilerPriorityChoice,hp]
      simp only [Option.isSome_none,Bool.false_eq_true,if_false]
      exact compiler_restart_view m g s α ell schedule logical hDone hComp hPC hA hp
    | some pair =>
      obtain ⟨t,v⟩ := pair
      simp [recursiveStep,hDone,hComp,hPC,hA,hp,compilerPriorityChoice,compilerSelectedDrain,compilerDrain]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerNormalizeDecision

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_normalize_decision_view {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (logical : RecursiveState n) (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hPC : (logical.frames logical.top).pc=.normalize) :
    recursiveStep m g s α ell [] logical=compilerNormalizeDecision g ell logical := by
  by_cases hAny : anyExhausted logical
  · simp [recursiveStep,hDone,hComp,hPC,hAny,compilerNormalizeDecision]
  · rw [compilerNormalizeDecision,if_pos hAny]
    by_cases hEq : logical.top=ell
    · have hPC' : (logical.frames ell).pc=.normalize := by simpa only [hEq] using hPC
      simp [recursiveStep,hDone,hComp,hPC',hAny,hEq,compilerNormalizeInner]
    · rw [compilerNormalizeInner,if_neg hEq]
      exact recursiveStep_spawnChild m g s α ell logical hDone hComp hPC hAny hEq

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerLeafDecision

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_leaf_controller_view {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (logical : RecursiveState n)
    (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hPC : (logical.frames logical.top).pc=.leafDrain)
    (hStored : (logical.frames logical.top).cache ∪ (logical.frames logical.top).high ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames logical.top).cache ∪ (logical.frames logical.top).high, 0<g.graph.degree v) :
    recursiveStep m g s α ell schedule logical=compilerLeafController m g α logical := by
  by_cases hAny : anyExhausted logical
  · simp [recursiveStep,hDone,hComp,hPC,hAny,compilerLeafController]
  · rw [compilerLeafController,if_pos hAny]
    cases hp : pendingPush logical with
    | none =>
      rw [compilerPendingDecision,hp]
      exact compiler_leaf_decision_view m g s α ell schedule logical hDone hComp hPC hAny hp hStored hDegree
    | some pair =>
      obtain ⟨t,v⟩ := pair
      simp [recursiveStep,hDone,hComp,hPC,hAny,compilerPendingDecision,hp]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerFinishDecision

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_finish_decision_view {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (logical : RecursiveState n)
    (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hPC : (logical.frames logical.top).pc=.finishEpisode) :
    recursiveStep m g s α ell schedule logical=compilerFinishDecision g logical := by
  by_cases hA : ancestorExhausted logical
  · simp [recursiveStep,hDone,hComp,hPC,hA,compilerFinishDecision]
  · have hAny := any_exhausted_of_no_ancestor logical hA
    by_cases hE : exhausted logical logical.top
    · have hY := hAny.mpr hE
      simp [recursiveStep,hDone,hComp,hPC,hA,hE,compilerFinishDecision,hY]
    · have hY : ¬anyExhausted logical := fun h => hE (hAny.mp h)
      rw [compilerFinishDecision,if_pos hA,if_pos hY]
      exact compiler_finish_view m g s α ell schedule logical hDone hComp hPC hA hE

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerAfterDecision

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_after_decision_view {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (logical : RecursiveState n)
    (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hPC : (logical.frames logical.top).pc=.afterChild) :
    recursiveStep m g s α ell schedule logical=compilerAfterDecision g α logical := by
  by_cases hA : ancestorExhausted logical
  · simp [recursiveStep,hDone,hComp,hPC,hA,compilerAfterDecision]
  · have hAny := any_exhausted_of_no_ancestor logical hA
    by_cases hE : exhausted logical logical.top
    · have hY := hAny.mpr hE
      simp [recursiveStep,hDone,hComp,hPC,hA,hE,compilerAfterDecision,hY]
    · have hY : ¬anyExhausted logical := fun h => hE (hAny.mp h)
      simp [recursiveStep,hDone,hComp,hPC,hA,hE,compilerAfterDecision,hY,compilerDrain]
      cases pendingPush logical <;> rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MachineSequenceAssociation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma MachineEval.seq_assoc {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {a b c : MachineCode} {st out : MachineState} {u : ℕ}
    (e : MachineEval m g ω (.seq (.seq a b) c) st u out) :
    MachineEval m g ω (.seq a (.seq b c)) st u out := by
  cases e with
  | seq eab ec =>
    cases eab with
    | seq ea eb =>
      simpa only [Nat.add_assoc] using MachineEval.seq ea (MachineEval.seq eb ec)

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerOrdinaryPrelude

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 14000000 in
lemma controller_ordinary_prelude_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) :
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length logical out,
      MachineEval m g ω (.seq budgetStatusCode (levelHeaderIntegerToCode 0 152)) st steps out ∧
      steps ≤ 76*(logical.top+1)+25 ∧ next.mass=memory.mass ∧
      next.potential P Q=memory.potential P Q ∧ ControllerBudgetFlags logical out ∧
      out.scalar.core.ptrs 152=(normalizePCNumber (logical.frames logical.top).pc : ℤ) ∧
      out.work=st.work+steps := by
  let pm := memory.live hDone
  obtain ⟨u,a,am,ea,hu,a170,a160,aMass,aI,aR,aW,aQ,aO,aH⟩ :=
    budget_status_exec m g ω logical s α ε ell length st memory.halted pm
  obtain ⟨out,eb,b152,bI,bR,bW,bO,bH⟩ :=
    level_header_integer_to_exec m g ω a aH logical.top 0 152 am.top
  let bm := am.frame bI bR (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact eb.pointer_frame _ (by decide)) (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact eb.real_register_frame _ (by decide)) bO
  have ex := MachineEval.seq ea eb
  have hEpoch : EpochInvariant (n:=n) (16*(ell+3)) out :=
    memory.indexInvariant hDone ex (by decide) (fun v => congrFun (bI.trans aI) _)
  let next := memory.nextLive hDone bm hDone ex (by decide) (by decide) bH hEpoch
  have hMass : next.mass=memory.mass := by
    rw [ControllerMemory.nextLive_mass]
    change am.queueMass=memory.mass
    rw [aMass, memory.mass_live hDone]
  refine ⟨u+10,out,next,ex,by omega,hMass,?_,?_,?_,?_⟩
  · simp only [ControllerMemory.potential,hMass]
  · exact ⟨(eb.pointer_frame 160 (by decide)).trans a160,
      (eb.pointer_frame 170 (by decide)).trans a170⟩
  · exact b152.trans (am.frames logical.top le_rfl).pc
  · rw [bW,aW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NumberedDispatchBounded

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 15000000 in
lemma numbered_dispatch_bounded_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (logical next : RecursiveState n)
    (potential : ∀ {logical : RecursiveState n} {st : MachineState}, ControllerMemory g s α ε ell length logical st → ℕ)
    (hPay : ∀ {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st),
      potential memory.payUnit=potential memory)
    (hWrite : ∀ {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st) (z : ℤ),
      potential (memory.dispatchWrite z)=potential memory)
    (selected : MachineCode) (M D : ℕ) (charge : ℝ≥0∞) (Q : MachineState → Prop)
    (hQpay : ∀ st, Q st → Q (payUnit st))
    (hQwrite : ∀ st z, Q st → Q (pointerWrite st 153 z))
    (body : ∀ st, ∀ memory : ControllerMemory g s α ε ell length logical st, Q st → memory.mass ≤ M →
      ∃ steps out, ∃ memory' : ControllerMemory g s α ε ell length next out,
        MachineEval m g ω selected st steps out ∧ memory'.mass ≤ M+D ∧
        out.work+(potential memory' : ℝ≥0∞) ≤ st.work+(potential memory : ℝ≥0∞)+charge) :
    ∀ index branches start, branches[index]?=some selected → ∀ st,
      ∀ memory : ControllerMemory g s α ε ell length logical st,
      st.scalar.core.ptrs 152=((start+index : ℕ) : ℤ) → Q st → memory.mass ≤ M →
      ∃ steps out, ∃ memory' : ControllerMemory g s α ε ell length next out,
        MachineEval m g ω (numberedDispatchCode start branches) st steps out ∧ memory'.mass ≤ M+D ∧
        out.work+(potential memory' : ℝ≥0∞) ≤
          st.work+(potential memory : ℝ≥0∞)+((3*index+2 : ℕ) : ℝ≥0∞)+charge := by
  intro index
  induction index with
  | zero =>
    intro branches start hLookup st memory hIndex hQ hMass
    cases branches with
    | nil => simp at hLookup
    | cons b bs =>
      have he : b=selected := by simpa using hLookup
      subst b
      let a := payUnit (pointerWrite st 153 (start : ℤ))
      let am := (memory.dispatchWrite (start : ℤ)).payUnit
      have ea : MachineEval m g ω (coreCode (.pset 153 (start : ℤ))) st 1 a := pset_eval m g ω st 153 (start : ℤ) memory.halted
      obtain ⟨u,out,nm,eb,nMass,hW⟩ := body (payUnit a) am.payUnit (hQpay a (hQpay _ (hQwrite st _ hQ))) (by simpa only [am,ControllerMemory.payUnit_mass,ControllerMemory.dispatchWrite_mass] using hMass)
      have ex : MachineEval m g ω (numberedDispatchCode start (selected::bs)) st (1+(1+u)) out :=
        MachineEval.seq ea (MachineEval.pointerLe am.halted (by simp [a,payUnit,pcSet,pointerWrite,hIndex]) eb)
      refine ⟨_,out,nm,ex,nMass,?_⟩
      rw [hPay,hPay,hWrite] at hW
      change out.work+(potential nm : ℝ≥0∞) ≤ (st.work+1+1)+(potential memory : ℝ≥0∞)+charge at hW
      calc
        _ ≤ (st.work+1+1)+(potential memory : ℝ≥0∞)+charge := hW
        _ = _ := by simp only [Nat.mul_zero,Nat.zero_add,Nat.cast_ofNat]; ring
  | succ index ih =>
    intro branches start hLookup st memory hIndex hQ hMass
    cases branches with
    | nil => simp at hLookup
    | cons b bs =>
      have hTail : bs[index]?=some selected := by simpa using hLookup
      let a := payUnit (pointerWrite st 153 (start : ℤ))
      let am := (memory.dispatchWrite (start : ℤ)).payUnit
      have ea : MachineEval m g ω (coreCode (.pset 153 (start : ℤ))) st 1 a := pset_eval m g ω st 153 (start : ℤ) memory.halted
      have hIndex' : (payUnit a).scalar.core.ptrs 152=(((start+1)+index : ℕ) : ℤ) := by
        change Function.update st.scalar.core.ptrs 153 (start : ℤ) 152=_
        rw [Function.update_of_ne (by decide),hIndex]
        push_cast
        omega
      obtain ⟨u,out,nm,eb,nMass,hW⟩ := ih bs (start+1) hTail (payUnit a) am.payUnit hIndex'
        (hQpay a (hQpay _ (hQwrite st _ hQ))) (by simpa only [am,ControllerMemory.payUnit_mass,ControllerMemory.dispatchWrite_mass] using hMass)
      have ex : MachineEval m g ω (numberedDispatchCode start (b::bs)) st (1+(1+u+1)) (payUnit out) :=
        MachineEval.seq ea (MachineEval.pointerGt am.halted (by
          change ¬Function.update st.scalar.core.ptrs 153 (start : ℤ) 152 ≤ Function.update st.scalar.core.ptrs 153 (start : ℤ) 153
          rw [Function.update_of_ne (by decide),Function.update_self,hIndex]
          push_cast
          omega) eb)
      refine ⟨_,payUnit out,nm.payUnit,ex,by simpa only [ControllerMemory.payUnit_mass] using nMass,?_⟩
      rw [hPay,hPay,hWrite] at hW
      rw [hPay,payUnit_work]
      change out.work+(potential nm : ℝ≥0∞) ≤
        (st.work+1+1)+(potential memory : ℝ≥0∞)+((3*index+2 : ℕ) : ℝ≥0∞)+charge at hW
      calc
        _ = (out.work+(potential nm : ℝ≥0∞))+1 := by ac_rfl
        _ ≤ ((st.work+1+1)+(potential memory : ℝ≥0∞)+((3*index+2 : ℕ) : ℝ≥0∞)+charge)+1 := add_le_add hW le_rfl
        _ = _ := by push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerOrdinaryExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma controller_pc_lookup (pc : NormalizePC) : controllerBranches[normalizePCNumber pc]?=some (controllerPCCode pc) := by
  cases pc <;> rfl

set_option maxHeartbeats 18000000 in
lemma controller_ordinary_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical target : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P Q M D : ℕ) (charge : ℝ≥0∞)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hMass : memory.mass ≤ M)
    (body : ∀ a, ∀ mem : ControllerMemory g s α ε ell length logical a,
      ControllerBudgetFlags logical a → mem.mass ≤ M →
      ∃ u out, ∃ next : ControllerMemory g s α ε ell length target out,
        MachineEval m g ω (controllerPCCode (logical.frames logical.top).pc) a u out ∧
        next.mass ≤ M+D ∧
        out.work+(next.potential P Q : ℝ≥0∞) ≤ a.work+(mem.potential P Q : ℝ≥0∞)+charge) :
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length target out,
      MachineEval m g ω controllerOrdinaryCode st steps out ∧ next.mass ≤ M+D ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+
        ((76*(logical.top+1)+25+(3*normalizePCNumber (logical.frames logical.top).pc+2) : ℕ) : ℝ≥0∞)+charge := by
  obtain ⟨u,a,am,ea,hu,aMass,aPhi,aFlags,a152,aW⟩ := controller_ordinary_prelude_exec m g ω logical s α ε ell length P Q st memory hDone
  let φ := fun {logical : RecursiveState n} {st : MachineState} (mem : ControllerMemory g s α ε ell length logical st) => mem.potential P Q
  obtain ⟨v,out,next,eb,bMass,bW⟩ := numbered_dispatch_bounded_exec m g ω s α ε ell length logical target φ
    (fun mem => mem.potential_payUnit P Q) (fun mem z => mem.potential_dispatchWrite P Q z)
    (controllerPCCode (logical.frames logical.top).pc) M D charge (ControllerBudgetFlags logical)
    (fun _ h => h.payUnit) (fun _ _ h => h.dispatchWrite _) body
    (normalizePCNumber (logical.frames logical.top).pc) controllerBranches 0 (controller_pc_lookup _) a am
    (by simpa only [Nat.zero_add] using a152) aFlags (by rw [aMass]; exact hMass)
  have ex : MachineEval m g ω controllerOrdinaryCode st (u+v) out := (MachineEval.seq ea eb).seq_assoc
  refine ⟨u+v,out,next,ex,bMass,?_⟩
  change out.work+(next.potential P Q : ℝ≥0∞) ≤ a.work+(am.potential P Q : ℝ≥0∞)+_+charge at bW
  rw [aW,aPhi] at bW
  have hCast : (u : ℝ≥0∞) ≤ ((76*(logical.top+1)+25 : ℕ) : ℝ≥0∞) := by exact_mod_cast hu
  calc
    _ ≤ (st.work+(u : ℝ≥0∞))+(memory.potential P Q : ℝ≥0∞)+((3*normalizePCNumber (logical.frames logical.top).pc+2 : ℕ) : ℝ≥0∞)+charge := bW
    _ ≤ (st.work+((76*(logical.top+1)+25 : ℕ) : ℝ≥0∞))+(memory.potential P Q : ℝ≥0∞)+((3*normalizePCNumber (logical.frames logical.top).pc+2 : ℕ) : ℝ≥0∞)+charge := by gcongr
    _ = _ := by push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerComponentExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 10000000 in
lemma controller_component_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ) (epoch : ℤ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hα : 0<α ∧ α<1) (hNonempty : (logical.frames 0).active.Nonempty)
    (hStored : (logical.frames 0).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames 0).active, 0<g.graph.degree v)
    (hEpoch : st.scalar.core.ptrs 53=epoch)
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch) :
    let size := volumeNat g (logical.frames 0).active+(logical.frames 0).active.card
    let cost := (10*(logical.frames 0).active.card+5)+((24*(16*(ell+3))+100)*size+28)+
      ((4*(16*(ell+3))+21)*(logical.frames 0).active.card+6)+4
    ∃ steps out, MachineEval m g ω controllerComponentCode st steps out ∧ steps ≤ cost+1 ∧
      outputVector out.output=potentialOutput g.graph α (solveOn g α (logical.frames 0).active (LocalPush.e s)) ∧
      out.work ≤ st.work+(cost : ℕ)+solveCharge m (logical.frames 0).active.card size ∧
      out.scalar.core.ptrs 150=1 ∧ out.scalar.core.ptrs 151=st.scalar.core.ptrs 151 ∧ out.scalar.halted=false := by
  dsimp only
  obtain ⟨u,a,ea,hu,aVector,aW,aH⟩ := root_component_solve_exec m g ω logical s α ε ell length epoch st hh pm hDepth hα hNonempty hStored hDegree hEpoch hbound
  let out := payUnit (pointerWrite a 150 1)
  have eb : MachineEval m g ω stopControllerCode a 1 out := pset_eval m g ω a 150 1 aH
  have ex : MachineEval m g ω controllerComponentCode st (u+1) out := MachineEval.seq ea eb
  refine ⟨u+1,out,ex,by omega,aVector,?_,by simp [out,payUnit,pcSet,pointerWrite],ex.pointer_frame 151 (by decide),aH⟩
  change a.work+1 ≤ _
  calc
    _ ≤ (st.work+((10*(logical.frames 0).active.card+5)+((24*(16*(ell+3))+100)*(volumeNat g (logical.frames 0).active+(logical.frames 0).active.card)+28)+
      ((4*(16*(ell+3))+21)*(logical.frames 0).active.card+6)+3 : ℕ)+solveCharge m (logical.frames 0).active.card (volumeNat g (logical.frames 0).active+(logical.frames 0).active.card))+1 := add_le_add aW le_rfl
    _ = _ := by push_cast; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerSparseDenotation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_sparse_vector {n : ℕ} (T : Finset (Fin n)) (x : Fin n → ℝ) (v : Fin n) :
    outputVector (sparseOn T x) v = if v ∈ T then x v else 0 := by
  classical
  simp only [outputVector,sparseOn,List.map_map]
  have he : ∀ u : Fin n, ((u.val : ℤ) = (v.val : ℤ)) ↔ u = v := by
    intro u
    simp only [Int.natCast_inj,Fin.val_inj]
  rw [← List.sum_toFinset _ (T.nodup_toList.filter _)]
  simp only [List.toFinset_filter]
  by_cases hx : x v = 0 <;> by_cases hv : v ∈ T <;> simp [he,hx,hv]

lemma compiler_sparse_vector_eq {n : ℕ} (T : Finset (Fin n)) (x : Fin n → ℝ)
    (hOutside : ∀ v ∉ T, x v=0) : outputVector (sparseOn T x)=x := by
  funext v
  rw [compiler_sparse_vector]
  split
  · rfl
  · exact (hOutside v ‹_›).symm

lemma ControllerMemory.potential_done {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=true) (P Q : ℕ) : memory.potential P Q=0 := by
  rw [ControllerMemory.potential,memory.mass_done hDone,hDone]
  simp

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerComponentPotential

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 16000000 in
lemma controller_component_potential_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) (hα : 0<α ∧ α<1)
    (hNonempty : (logical.frames 0).active.Nonempty)
    (hStored : (logical.frames 0).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames 0).active, 0<g.graph.degree v) :
    let C := (logical.frames 0).active
    let size := volumeNat g C+C.card
    let cost := (10*C.card+5)+((24*(16*(ell+3))+100)*size+28)+((4*(16*(ell+3))+21)*C.card+6)+4
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (completeComponent m g s α logical) out,
      MachineEval m g ω controllerComponentCode st steps out ∧ next.mass ≤ memory.mass ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+(cost : ℕ)+solveCharge m C.card size := by
  dsimp only
  obtain ⟨u,out,ex,hu,hVector,hWork,h150,h151,hH⟩ := controller_component_exec m g ω logical s α ε ell length (st.scalar.core.ptrs 53) st memory.halted (memory.live hDone) hDepth hα hNonempty hStored hDegree rfl (memory.epoch hDone)
  have hTarget : (completeComponent m g s α logical).done=true := rfl
  have hOutput : outputVector (n:=n) out.output=outputVector (n:=n) (completeComponent m g s α logical).output := by
    rw [hVector]
    change potentialOutput g.graph α (solveOn g α (logical.frames 0).active (LocalPush.e s))=
      outputVector (sparseOn (logical.frames 0).active (potentialOutput g.graph α (solveOn g α (logical.frames 0).active (LocalPush.e s))))
    symm
    apply compiler_sparse_vector_eq
    intro v hv
    simp only [potentialOutput,solveOn,dif_neg hv,mul_zero]
  let next : ControllerMemory g s α ε ell length (completeComponent m g s α logical) out :=
    ControllerMemory.ofDone hTarget h150 (h151.trans memory.one) hH hOutput
  refine ⟨u,out,next,ex,?_,?_⟩
  · rw [next.mass_done hTarget]
    exact Nat.zero_le _
  · rw [next.potential_done hTarget P Q,Nat.cast_zero,add_zero]
    exact hWork.trans (by
      simpa only [add_assoc,add_left_comm,add_comm,zero_add,add_zero] using
        add_le_add (le_refl (st.work+(((10*(logical.frames 0).active.card+5)+((24*(16*(ell+3))+100)*(volumeNat g (logical.frames 0).active+(logical.frames 0).active.card)+28)+((4*(16*(ell+3))+21)*(logical.frames 0).active.card+6)+4 : ℕ) : ℝ≥0∞)+solveCharge m (logical.frames 0).active.card (volumeNat g (logical.frames 0).active+(logical.frames 0).active.card)))
          (show (0 : ℝ≥0∞) ≤ (memory.potential P Q : ℝ≥0∞) by positivity))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerStepData

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped ENNReal

lemma controller_next_eq_step {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (logical : RecursiveState n) (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hStored : StoredInvariant g logical) (hRegion : RegionInvariant logical) :
    recursiveStep m g s α ell [] logical=controllerNext m g α ell logical := by
  have hActive := compiler_stored_active_domain g logical hStored logical.top le_rfl
  have hCache := compiler_stored_cache_high_domain g logical hStored hRegion logical.top le_rfl
  cases hPC : (logical.frames logical.top).pc
  all_goals rw [controllerNext,hPC]
  · exact compiler_initial_controller_view m g s α ell [] logical hDone hComp hPC
  · exact compiler_begin_view m g s α ell [] logical hDone hComp hPC
  · exact compiler_full_decision_view m g s α ell [] logical hDone hComp hPC hActive.1 hActive.2
  · exact compiler_normalize_decision_view m g s α ell logical hDone hComp hPC
  · exact compiler_leaf_controller_view m g s α ell [] logical hDone hComp hPC hCache.1 hCache.2
  · exact compiler_after_decision_view m g s α ell [] logical hDone hComp hPC
  · exact compiler_finish_decision_view m g s α ell [] logical hDone hComp hPC
  · exact compiler_restart_controller_view m g s α ell [] logical hDone hComp hPC
  · simp [recursiveStep,hDone,hComp,hPC]
  · simp [recursiveStep,hDone,hComp,hPC]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerComponentTest

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 5000000 in
lemma controller_component_test_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω controllerComponentTestRoutine.code st 4 out ∧ memory.queueMass=pm.queueMass ∧
      out.scalar.core.ptrs 176=((logical.frames 0).active.card : ℤ) ∧ out.scalar.core.ptrs 177=logical.boundaryEdges ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+4 ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨out,ex,hP,hI,hR,hW,hO,hH⟩ := controllerComponentTestRoutine.execute m g ω st hh
  let memory := pm.frame hI hR (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ex.pointer_frame _ (by decide)) (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ex.real_register_frame _ (by decide)) hO
  refine ⟨out,memory,ex,rfl,?_,?_,hI,hR,hW,ex.query_frame (by decide),hO,hH⟩
  · rw [hP]
    have h := (pm.frames 0 (Nat.zero_le _)).activeCount
    simpa [controllerComponentTestRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
      PointerOp.destination,PointerOp.result,levelHeaderAddress] using h
  · rw [hP]
    simpa [controllerComponentTestRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
      PointerOp.destination,PointerOp.result] using pm.boundary

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerComponentTestRuntime

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma controller_component_test_runtime_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st) (hDone : logical.done=false) :
    ∃ out, ∃ next : ControllerMemory g s α ε ell length logical out,
      MachineEval m g ω controllerComponentTestRoutine.code st 4 out ∧ next.mass=memory.mass ∧
      next.potential P Q=memory.potential P Q ∧
      out.scalar.core.ptrs 176=((logical.frames 0).active.card : ℤ) ∧ out.scalar.core.ptrs 177=logical.boundaryEdges ∧
      out.work=st.work+4 := by
  let pm := memory.live hDone
  obtain ⟨out,om,ex,oMass,o176,o177,oI,oR,oW,oQ,oO,oH⟩ := controller_component_test_exec m g ω logical s α ε ell length st memory.halted pm
  let next := memory.nextLive hDone om hDone ex (by decide) (by decide) oH
    (memory.indexInvariant hDone ex (by decide) (fun v => congrFun oI _))
  have hn : next.mass=om.queueMass := ControllerMemory.nextLive_mass _ _ _ _ _ _ _ _ _
  have hMass : next.mass=memory.mass := hn.trans (oMass.trans (memory.mass_live hDone).symm)
  exact ⟨out,next,ex,hMass,by simp only [ControllerMemory.potential,hMass],o176,o177,oW⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerBodyExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 18000000 in
lemma controller_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical target : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P Q M M' : ℕ)
    (ordinaryCharge componentCharge : ℝ≥0∞)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hMass : memory.mass ≤ M) (hBoundary : 0≤logical.boundaryEdges)
    (ordinary : ¬componentComplete logical → ∀ a, ∀ mem : ControllerMemory g s α ε ell length logical a,
      mem.mass ≤ M → ∃ u out, ∃ next : ControllerMemory g s α ε ell length target out,
        MachineEval m g ω controllerOrdinaryCode a u out ∧ next.mass ≤ M' ∧
        out.work+(next.potential P Q : ℝ≥0∞) ≤ a.work+(mem.potential P Q : ℝ≥0∞)+ordinaryCharge)
    (component : componentComplete logical → ∀ a, ∀ mem : ControllerMemory g s α ε ell length logical a,
      mem.mass ≤ M → ∃ u out, ∃ next : ControllerMemory g s α ε ell length target out,
        MachineEval m g ω controllerComponentCode a u out ∧ next.mass ≤ M' ∧
        out.work+(next.potential P Q : ℝ≥0∞) ≤ a.work+(mem.potential P Q : ℝ≥0∞)+componentCharge) :
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length target out,
      MachineEval m g ω controllerBodyCode st steps out ∧ next.mass ≤ M' ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+
        (if componentComplete logical then componentCharge else ordinaryCharge)+8 := by
  obtain ⟨a,am,ea,aMass,aPhi,a176,a177,aW⟩ := controller_component_test_runtime_exec m g ω logical s α ε ell length P Q st memory hDone
  have amM : am.mass ≤ M := by rw [aMass]; exact hMass
  have amM1 : am.payUnit.mass ≤ M := by simpa only [ControllerMemory.payUnit_mass] using amM
  have amM2 : am.payUnit.payUnit.mass ≤ M := by simpa only [ControllerMemory.payUnit_mass] using amM
  have hZero : a.scalar.core.ptrs 0=0 := (am.live hDone).zero
  by_cases hComp : componentComplete logical
  · have hCount : 0<(logical.frames 0).active.card := Finset.card_pos.mpr hComp.1
    obtain ⟨u,out,next,eb,bMass,bW⟩ := component hComp (payUnit (payUnit a)) am.payUnit.payUnit amM2
    have eInner : MachineEval m g ω (.branchPointer 177 0 controllerComponentCode controllerOrdinaryCode) (payUnit a) (1+u) out :=
      MachineEval.pointerLe am.halted (by change a.scalar.core.ptrs 177 ≤ a.scalar.core.ptrs 0; rw [a177,hComp.2,hZero]) eb
    have eOuter : MachineEval m g ω (.branchPointer 176 0 controllerOrdinaryCode (.branchPointer 177 0 controllerComponentCode controllerOrdinaryCode)) a (1+(1+u)+1) (payUnit out) :=
      MachineEval.pointerGt am.halted (by rw [a176,hZero]; exact_mod_cast (by omega : ¬(logical.frames 0).active.card ≤ 0)) eInner
    refine ⟨_,payUnit out,next.payUnit,MachineEval.seq ea eOuter,by simpa only [ControllerMemory.payUnit_mass] using bMass,?_⟩
    rw [if_pos hComp,ControllerMemory.potential_payUnit,payUnit_work]
    rw [payUnit_work,payUnit_work,ControllerMemory.potential_payUnit,ControllerMemory.potential_payUnit,aW,aPhi] at bW
    calc
      _ = (out.work+(next.potential P Q : ℝ≥0∞))+1 := by ac_rfl
      _ ≤ ((((st.work+4)+1)+1)+(memory.potential P Q : ℝ≥0∞)+componentCharge)+1 := add_le_add bW le_rfl
      _ ≤ _ := by
        have h78 : (7 : ℝ≥0∞) ≤ 8 := by norm_num
        calc
          _ = st.work+(memory.potential P Q : ℝ≥0∞)+componentCharge+7 := by ring
          _ ≤ _ := add_le_add le_rfl h78
  · rw [if_neg hComp]
    by_cases hEmpty : (logical.frames 0).active=∅
    · obtain ⟨u,out,next,eb,bMass,bW⟩ := ordinary hComp (payUnit a) am.payUnit amM1
      have eOuter : MachineEval m g ω (.branchPointer 176 0 controllerOrdinaryCode (.branchPointer 177 0 controllerComponentCode controllerOrdinaryCode)) a (1+u) out :=
        MachineEval.pointerLe am.halted (by rw [a176,hEmpty,hZero]; simp) eb
      refine ⟨_,out,next,MachineEval.seq ea eOuter,bMass,?_⟩
      rw [payUnit_work,ControllerMemory.potential_payUnit,aW,aPhi] at bW
      exact bW.trans (by
        have h58 : (5 : ℝ≥0∞) ≤ 8 := by norm_num
        calc
          _ = st.work+(memory.potential P Q : ℝ≥0∞)+ordinaryCharge+5 := by ring
          _ ≤ _ := add_le_add le_rfl h58)
    · have hNonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
      have hCount := Finset.card_pos.mpr hNonempty
      have hB : 0<logical.boundaryEdges := by
        have hNe : logical.boundaryEdges≠0 := fun h => hComp ⟨hNonempty,h⟩
        omega
      obtain ⟨u,out,next,eb,bMass,bW⟩ := ordinary hComp (payUnit (payUnit a)) am.payUnit.payUnit amM2
      have eInner : MachineEval m g ω (.branchPointer 177 0 controllerComponentCode controllerOrdinaryCode) (payUnit a) (1+u+1) (payUnit out) :=
        MachineEval.pointerGt am.halted (by change ¬a.scalar.core.ptrs 177 ≤ a.scalar.core.ptrs 0; rw [a177,hZero]; omega) eb
      have eOuter : MachineEval m g ω (.branchPointer 176 0 controllerOrdinaryCode (.branchPointer 177 0 controllerComponentCode controllerOrdinaryCode)) a (1+(1+u+1)+1) (payUnit (payUnit out)) :=
        MachineEval.pointerGt am.halted (by rw [a176,hZero]; exact_mod_cast (by omega : ¬(logical.frames 0).active.card ≤ 0)) eInner
      refine ⟨_,payUnit (payUnit out),next.payUnit.payUnit,MachineEval.seq ea eOuter,by simpa only [ControllerMemory.payUnit_mass] using bMass,?_⟩
      rw [ControllerMemory.potential_payUnit,ControllerMemory.potential_payUnit,payUnit_work,payUnit_work]
      rw [payUnit_work,payUnit_work,ControllerMemory.potential_payUnit,ControllerMemory.potential_payUnit,aW,aPhi] at bW
      calc
        _ = (out.work+(next.potential P Q : ℝ≥0∞))+2 := by ring
        _ ≤ ((((st.work+4)+1)+1)+(memory.potential P Q : ℝ≥0∞)+ordinaryCharge)+2 := add_le_add bW le_rfl
        _ = _ := by ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerStepExecution

set_option autoImplicit false
set_option maxRecDepth 20000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 24000000 in
lemma controller_source_step_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank Q M : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) (hα : 0<α ∧ α<1)
    (hRegion : RegionInvariant logical) (hKeys : KeysInvariant g logical) (hBoundary : BoundaryIdentity g logical)
    (hParameters : ParameterInvariant logical) (hStored : StoredInvariant g logical) (hNumerical : NumericalInvariant g logical)
    (hm : memory.mass ≤ M) (capacities : ¬componentComplete logical → ControllerCapacities g logical ell M N)
    (hCredit : 4*(16*(ell+3))+17 ≤ Q) (hCap : rank < length) (hPow : N < 2^rank) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (recursiveStep m g s α ell [] logical) out,
      MachineEval m g ω controllerBodyCode st steps out ∧ next.mass ≤ M+controllerSourceGrowth g ell logical ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+controllerBodyCharge m g logical ell length rank Q := by
  dsimp only
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  have hNonnegative : 0≤logical.boundaryEdges := by
    obtain ⟨b,hb⟩ := compiler_boundary_nat g logical hBoundary
    rw [hb]
    positivity
  suffices h : ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (recursiveStep m g s α ell [] logical) out,
      MachineEval m g ω controllerBodyCode st steps out ∧ next.mass ≤ M+controllerSourceGrowth g ell logical ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+
        (if componentComplete logical then controllerComponentCharge m g logical ell else controllerOrdinaryCharge m g logical ell length rank Q)+8 by
    simpa only [controllerBodyCharge,add_assoc] using h
  apply controller_body_exec m g ω logical (recursiveStep m g s α ell [] logical) s α ε ell length P Q M
    (M+controllerSourceGrowth g ell logical) (controllerOrdinaryCharge m g logical ell length rank Q) (controllerComponentCharge m g logical ell)
    st memory hDone hm hNonnegative
  · intro hComp a mem hm
    have hNext := controller_next_eq_step m g s α ell logical hDone hComp hStored hRegion
    have body : ∀ a, ∀ mem : ControllerMemory g s α ε ell length logical a,
        ControllerBudgetFlags logical a → mem.mass ≤ M →
        ∃ u out, ∃ next : ControllerMemory g s α ε ell length (recursiveStep m g s α ell [] logical) out,
          MachineEval m g ω (controllerPCCode (logical.frames logical.top).pc) a u out ∧
          next.mass ≤ M+controllerStepGrowth g ell logical ∧
          out.work+(next.potential P Q : ℝ≥0∞) ≤ a.work+(mem.potential P Q : ℝ≥0∞)+controllerPCCharge m g logical ell length rank Q := by
      intro a mem flags hm
      have result := controller_pc_exec m g ω logical s α ε ell length N rank Q M a mem hDone hDepth hα hRegion hKeys hBoundary hParameters hStored hNumerical flags hm (capacities hComp) hCredit hCap hPow
      rw [←hNext] at result
      exact result
    have result := controller_ordinary_exec m g ω logical (recursiveStep m g s α ell [] logical) s α ε ell length P Q M (controllerStepGrowth g ell logical) (controllerPCCharge m g logical ell length rank Q) a mem hDone hm body
    simpa only [controllerSourceGrowth,if_neg hComp,controllerOrdinaryCharge,add_assoc] using result
  · intro hComp a mem hm
    have hNext : recursiveStep m g s α ell [] logical=completeComponent m g s α logical := by simp only [recursiveStep,hDone,Bool.false_eq_true,if_false,hComp,if_true]
    obtain ⟨u,out,next,ex,hMass,hWork⟩ := controller_component_potential_exec m g ω logical s α ε ell length P Q a mem hDone hDepth hα hComp.1 (hStored.1 0 (Nat.zero_le _)) (fun v hv => hStored.2 v (hStored.1 0 (Nat.zero_le _) hv))
    have hOut : next.mass ≤ M+controllerSourceGrowth g ell logical := by
      rw [next.mass_done (show (completeComponent m g s α logical).done=true from rfl)]
      exact Nat.zero_le _
    have result : ∃ u out, ∃ next : ControllerMemory g s α ε ell length (completeComponent m g s α logical) out,
        MachineEval m g ω controllerComponentCode a u out ∧ next.mass ≤ M+controllerSourceGrowth g ell logical ∧
        out.work+(next.potential P Q : ℝ≥0∞) ≤ a.work+(mem.potential P Q : ℝ≥0∞)+controllerComponentCharge m g logical ell :=
      ⟨u,out,next,ex,hOut,by simpa only [controllerComponentCharge,add_assoc] using hWork⟩
    rw [←hNext] at result
    exact result

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution : ∀ (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank Q M : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) (hα : 0<α ∧ α<1)
    (hRegion : RegionInvariant logical) (hKeys : KeysInvariant g logical) (hBoundary : BoundaryIdentity g logical)
    (hParameters : ParameterInvariant logical) (hStored : StoredInvariant g logical) (hNumerical : NumericalInvariant g logical)
    (hm : memory.mass ≤ M) (capacities : ¬componentComplete logical → ControllerCapacities g logical ell M N)
    (hCredit : 4*(16*(ell+3))+17 ≤ Q) (hCap : rank < length) (hPow : N < 2^rank),
let P := cleanBodyBound (16*(ell+3)) length rank+2
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (recursiveStep m g s α ell [] logical) out,
      MachineEval m g ω controllerBodyCode st steps out ∧ next.mass ≤ M+controllerSourceGrowth g ell logical ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+controllerBodyCharge m g logical ell length rank Q := by
  exact @NearlyOptimalPPR.Computation.controller_source_step_exec
