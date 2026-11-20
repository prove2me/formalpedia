-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.pending_touched_refresh_foreign_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:46:17.6062+00:00
-- url     : https://prove2.me/submissions/a118f51f-17d5-454b-adcd-41d070e5c37d

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
import Theorems.Thm_NearlyOptimalPPR_Computation_queue_pair_refresh_exec
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

-- Proof module: Solutions.HeapLinkCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma heapLinkCode_wellFormed : heapLinkCode.wellFormed := by
  simp [heapLinkCode,sequenceCode,coreCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PointerSwapCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma swapRootsCode_wellFormed : swapRootsCode.wellFormed := by
  simp [swapRootsCode,sequenceCode,coreCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FramePendingKeys

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section


namespace FramePendingKeys

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

-- Proof module: Solutions.VertexFlagSet

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexFlagSetCode_wellFormed : vertexFlagSetCode.wellFormed := by
  simp [vertexFlagSetCode,vertexIntegerStoreCode,vertexAddressCode_wellFormed,
    coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.MachinePendingKeys

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

namespace MachinePendingKeys

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

-- Proof module: Solutions.BatchKeyRestoration

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma eligible_insert_list_cover {n : ℕ} (valid queued : Finset ℕ) (vertices : List (Fin n))
    (hOutside : valid \ (vertices.map Fin.val).toFinset ⊆ queued) :
    valid ⊆ eligibleInsertList valid queued vertices := by
  classical
  rw [eligible_insert_list_eq]
  intro x hx
  by_cases ht : x ∈ (vertices.map Fin.val).toFinset
  · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx,ht⟩)
  · exact Finset.mem_union_left _ (hOutside (Finset.mem_sdiff.mpr ⟨hx,ht⟩))

end
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

-- Proof module: Solutions.PendingQueuePotential

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

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

-- Proof module: Solutions.StoredNeighborMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma storedNeighborVertex_eq {n : ℕ} (g : InputGraph n) (source : Fin n) (i : ℕ)
    (hi : i < (g.neighbors source).length) : storedNeighborVertex g source i=(g.neighbors source)[i] := by
  simp [storedNeighborVertex,List.getElem?_eq_getElem hi]

lemma storedNeighborVertex_mem {n : ℕ} (g : InputGraph n) (source : Fin n) (i : ℕ)
    (hi : i < (g.neighbors source).length) : storedNeighborVertex g source i ∈ g.neighbors source := by
  rw [storedNeighborVertex_eq g source i hi]
  exact List.getElem_mem hi

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CachedSourceNeighborRead

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma cachedSourceNeighborReadCode_wellFormed : cachedSourceNeighborReadCode.wellFormed := by
  refine ⟨?_,?_,?_⟩
  all_goals simp [cachedSourceNeighborPrefixCode,cachedSourceNeighborPrefixInstructions,cachedSourceNeighborSuffixCode,
    cachedSourceNeighborSuffixInstructions,vertexFieldReadCode,vertexIntegerLoadCode,vertexAddressCode_wellFormed,
    linearCode,sequenceCode,coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 4500000 in
lemma cached_source_neighbor_read_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (source : Fin n) (width index : ℕ)
    (stored : Finset (Fin n)) (free : ℤ) (cache : GraphCache g st.scalar.integerMemory width stored free)
    (hs : source ∈ stored) (hi : index < (g.neighbors source).length)
    (h0 : st.scalar.core.ptrs 0=0) (hWidth : st.scalar.core.ptrs 50=(width : ℤ))
    (hIndex : st.scalar.core.ptrs 109=(index : ℤ)) (hSource : st.scalar.core.ptrs 116=(source.val : ℤ)) :
    ∃ out, MachineEval m g ω cachedSourceNeighborReadCode st (4*width+14) out ∧
      out.scalar.core.ptrs 40=(((g.neighbors source)[index]'hi).val : ℤ) ∧
      out.scalar.core.ptrs 122=(index : ℤ) ∧ out.scalar.integerMemory=st.scalar.integerMemory ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.core.regs=st.scalar.core.regs ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*width+14 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  let a := linearRun m g ω cachedSourceNeighborPrefixInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω cachedSourceNeighborPrefixInstructions
    (by simp [cachedSourceNeighborPrefixInstructions,unitInstruction,straightInstruction]) st hh
  have a122 : a.scalar.core.ptrs 122=(index : ℤ) := by
    simp [a,linearRun,cachedSourceNeighborPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hIndex]
  have a40 : a.scalar.core.ptrs 40=(source.val : ℤ) := by
    simp [a,linearRun,cachedSourceNeighborPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hSource]
  have a41 : a.scalar.core.ptrs 41=(width : ℤ) := by
    simp [a,linearRun,cachedSourceNeighborPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hWidth]
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,cachedSourceNeighborPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aR : a.scalar.core.mem=st.scalar.core.mem := by
    simp [a,linearRun,cachedSourceNeighborPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,cachedSourceNeighborPrefixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  obtain ⟨b,eb,b121,bI,bR,bQ,bW,bO,bH⟩ := vertex_field_read_exec m g ω a aH width source.val 1 121
    ((ea.pointer_frame 0 (by decide)).trans h0) a40 a41
  have b122 := (eb.pointer_frame 122 (by decide)).trans a122
  have b121' : b.scalar.core.ptrs 121=st.scalar.integerMemory (vertexRecordAddress width source.val 1) := by rw [b121,aI]
  have hRow : b.scalar.integerMemory (st.scalar.integerMemory (vertexRecordAddress width source.val 1)+(index : ℤ))=
      (((g.neighbors source)[index]'hi).val : ℤ) := by
    rw [bI,aI]
    exact cache.adjacency source hs index hi hi
  let out := linearRun m g ω cachedSourceNeighborSuffixInstructions b
  obtain ⟨ec,cW,cH⟩ := linear_execute m g ω cachedSourceNeighborSuffixInstructions
    (by simp [cachedSourceNeighborSuffixInstructions,unitInstruction,straightInstruction]) b bH
  have ex : MachineEval m g ω cachedSourceNeighborReadCode st (4*width+14) out := by
    have er := MachineEval.seq ea (MachineEval.seq eb ec)
    convert er using 1 <;> (first | rfl | change 4*width+14=3+((4*width+9)+2); omega)
  refine ⟨out,ex,?_,(ec.pointer_frame 122 (by decide)).trans b122,?_,?_,ex.register_frame (by
    simp [cachedSourceNeighborReadCode,cachedSourceNeighborPrefixCode,cachedSourceNeighborPrefixInstructions,
      cachedSourceNeighborSuffixCode,cachedSourceNeighborSuffixInstructions,vertexFieldReadCode,vertexIntegerLoadCode,
      vertexAddressCode_registerReadOnly,linearCode,sequenceCode,coreCode,MachineCode.allAtoms,registerReadOnly]),
    ex.query_frame (by decide),ex.unit_work cachedSourceNeighborReadCode_wellFormed (by decide) hh,?_,cH⟩
  · simp [out,linearRun,cachedSourceNeighborSuffixInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH,b121',b122,hRow]
  · have cI : out.scalar.integerMemory=b.scalar.integerMemory := by
      simp [out,linearRun,cachedSourceNeighborSuffixInstructions,atomState,machineStep,pcSet,LocalPush.step,
        scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH]
    exact cI.trans (bI.trans aI)
  · have cR : out.scalar.core.mem=b.scalar.core.mem := by
      simp [out,linearRun,cachedSourceNeighborSuffixInstructions,atomState,machineStep,pcSet,LocalPush.step,
        scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH]
    exact cR.trans (bR.trans aR)
  · have cO : out.output=b.output := by
      simp [out,linearRun,cachedSourceNeighborSuffixInstructions,atomState,machineStep,pcSet,LocalPush.step,
        scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH]
    exact cO.trans (bO.trans aO)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingNeighborRefreshBody

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pendingNeighborRefreshBodyCode_wellFormed : pendingNeighborRefreshBodyCode.wellFormed := by
  refine ⟨cachedSourceNeighborReadCode_wellFormed,pendingVertexRefreshCode_wellFormed,?_⟩
  simp [pendingNeighborRefreshTailCode,pendingNeighborRefreshTailInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

def pendingNeighborBooleanMemoryUpdate {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (width : ℕ) (source : Fin n) (degrees : Fin n → ℤ) (i : ℕ) (R : ℤ → ℝ) : ℤ → ℝ :=
  levelRealMemoryFold (pendingBooleanMemoryUpdate logical width (storedNeighborVertex g source i)
    (degrees (storedNeighborVertex g source i))) 0 (logical.top+1) R

set_option maxHeartbeats 8000000 in
lemma pending_neighbor_refresh_body_foreign_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length N R : ℕ) (logical : RecursiveState n)
    (hDepth : logical.top ≤ ell)
    (hActiveDomain : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hExtDomain : ∀ i ≤ logical.top, (logical.frames i).exterior ⊆ parentDomain logical i)
    (hHighDomain : ∀ i ≤ logical.top, (logical.frames i).high ⊆ parentDomain logical i)
    (source : Fin n) (hs : source ∈ logical.stored) (degrees : Fin n → ℤ)
    (index : ℕ) (hi : index < (g.neighbors source).length)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : MachinePendingKeys g s α ε ell length logical st)
    (hSource : st.scalar.core.ptrs 116=(source.val : ℤ))
    (hDegree : st.scalar.core.ptrs 120=((g.neighbors source).length : ℤ))
    (hDegrees : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)=degrees v)
    (hIndex : st.scalar.core.ptrs 109=(index : ℤ))
    (hMass : pm.queueMass+2*(logical.top+1) ≤ N) (hCap : R < length) (hPow : N < 2^R) :
    ∃ steps out, ∃ memory : MachinePendingKeys g s α ε ell length logical out,
      MachineEval m g ω pendingNeighborRefreshBodyCode st steps out ∧
      steps ≤ (logical.top+1)*(42*R+60*(16*(ell+3))+284)+4*(16*(ell+3))+23 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1) ∧
      out.scalar.core.ptrs 109=((index+1 : ℕ) : ℤ) ∧ out.scalar.core.ptrs 111=((g.neighbors source).length : ℤ) ∧
      (∀ i, ∀ hi : i ≤ logical.top,
        (memory.frames i hi).exteriorObject.keys=(if storedNeighborVertex g source index ∈ (logical.frames i).exterior then
          insert (storedNeighborVertex g source index).val (pm.frames i hi).exteriorObject.keys else (pm.frames i hi).exteriorObject.keys)) ∧
      (∀ i, ∀ hi : i ≤ logical.top,
        (memory.frames i hi).highObject.keys=(if storedNeighborVertex g source index ∈ (logical.frames i).high then
          insert (storedNeighborVertex g source index).val (pm.frames i hi).highObject.keys else (pm.frames i hi).highObject.keys)) ∧
      out.scalar.core.mem=pendingNeighborBooleanMemoryUpdate g logical (16*(ell+3)) source degrees index st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧ PendingIntegerFrame pm memory := by
  let width := 16*(ell+3)
  let v := (g.neighbors source)[index]'hi
  obtain ⟨a,ea,a40,a122,aI,aR,aRegs,aQ,aW,aO,aH⟩ := cached_source_neighbor_read_exec m g ω st hh source width index
    logical.stored (st.scalar.core.ptrs 20) pm.graphCache hs hi pm.zero pm.width hIndex hSource
  have aP : ∀ r ∈ ([0,20,50,100] : List ℕ), a.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ea.pointer_frame _ (by decide)
  let aMem := pm.frame aI aR aP (by intros r hr; exact congrFun aRegs r) aO
  obtain ⟨u,b,bMem,eb,hu,bMass,bExt,bHigh,bR,bQ,bW,bO,bH,bFrame⟩ := pending_vertex_refresh_foreign_exec m g ω s α ε ell length N R logical
    a aH aMem hDepth hActiveDomain hExtDomain hHighDomain v a40 hMass hCap hPow
  have ePrefix := MachineEval.seq ea eb
  have b122 : b.scalar.core.ptrs 122=(index : ℤ) := (eb.pointer_frame 122 (by decide)).trans a122
  have b120 : b.scalar.core.ptrs 120=((g.neighbors source).length : ℤ) := (ePrefix.pointer_frame 120 (by decide)).trans hDegree
  let out := linearRun m g ω pendingNeighborRefreshTailInstructions b
  obtain ⟨ec,cW,cH⟩ := linear_execute m g ω pendingNeighborRefreshTailInstructions
    (by simp [pendingNeighborRefreshTailInstructions,unitInstruction,straightInstruction]) b bH
  have c109 : out.scalar.core.ptrs 109=((index+1 : ℕ) : ℤ) := by
    simp [out,linearRun,pendingNeighborRefreshTailInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH,b122]
  have c111 : out.scalar.core.ptrs 111=((g.neighbors source).length : ℤ) := by
    simp [out,linearRun,pendingNeighborRefreshTailInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH,b120]
  have cI : out.scalar.integerMemory=b.scalar.integerMemory := by
    simp [out,linearRun,pendingNeighborRefreshTailInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH]
  have cR : out.scalar.core.mem=b.scalar.core.mem := by
    simp [out,linearRun,pendingNeighborRefreshTailInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH]
  have cO : out.output=b.output := by
    simp [out,linearRun,pendingNeighborRefreshTailInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,bH]
  have cP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=b.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ec.pointer_frame _ (by decide)
  have cG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=b.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ec.real_register_frame _ (by decide)
  let memory := bMem.frame cI cR cP cG cO
  have ex : MachineEval m g ω pendingNeighborRefreshBodyCode st ((4*width+14)+(u+3)) out :=
    MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨(4*width+14)+(u+3),out,memory,ex,by dsimp [width] at hu ⊢; omega,bMass,c109,c111,?_,?_,?_,
    ex.query_frame (by decide),ex.unit_work pendingNeighborRefreshBodyCode_wellFormed (by decide) hh,cO.trans (bO.trans aO),cH,((PendingIntegerFrame.frame pm aI aR aP (by intros r hr; exact congrFun aRegs r) aO).trans bFrame).trans (PendingIntegerFrame.frame bMem cI cR cP cG cO)⟩
  · intro i hi'
    change (bMem.frames i hi').exteriorObject.keys=_
    have hKeys : (aMem.frames i hi').exteriorObject.keys=(pm.frames i hi').exteriorObject.keys := rfl
    simpa only [storedNeighborVertex_eq g source index hi,hKeys] using bExt i hi'
  · intro i hi'
    change (bMem.frames i hi').highObject.keys=_
    have hKeys : (aMem.frames i hi').highObject.keys=(pm.frames i hi').highObject.keys := rfl
    simpa only [storedNeighborVertex_eq g source index hi,hKeys] using bHigh i hi'
  · rw [cR,bR,aR,aI,hDegrees v]
    simp only [pendingNeighborBooleanMemoryUpdate,storedNeighborVertex_eq g source index hi]
    rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EligibleInsertListTyped

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma mem_fin_val_image {n : ℕ} (valid : Finset (Fin n)) (v : Fin n) : v.val ∈ valid.image Fin.val ↔ v ∈ valid := by
  constructor
  · intro h
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
    exact (Fin.ext he : w=v) ▸ hw
  · intro h
    exact Finset.mem_image.mpr ⟨v,h,rfl⟩

lemma eligible_insert_list_cons_typed {n : ℕ} (valid : Finset (Fin n)) (queued : Finset ℕ) (v : Fin n) (vertices : List (Fin n)) :
    eligibleInsertList (valid.image Fin.val) queued (v::vertices)=
      eligibleInsertList (valid.image Fin.val) (if v ∈ valid then insert v.val queued else queued) vertices := by
  classical
  simp only [eligibleInsertList,List.foldl_cons,mem_fin_val_image]


end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingNeighborRefreshLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma pendingNeighborRefreshLoopCode_wellFormed : pendingNeighborRefreshLoopCode.wellFormed := pendingNeighborRefreshBodyCode_wellFormed

set_option maxHeartbeats 12000000 in
lemma pending_neighbor_refresh_loop_foreign_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length N R : ℕ) (logical : RecursiveState n)
    (hDepth : logical.top ≤ ell) (hCap : R < length) (hPow : N < 2^R)
    (hActiveDomain : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hExtDomain : ∀ i ≤ logical.top, (logical.frames i).exterior ⊆ parentDomain logical i)
    (hHighDomain : ∀ i ≤ logical.top, (logical.frames i).high ⊆ parentDomain logical i)
    (source : Fin n) (hs : source ∈ logical.stored) (degrees : Fin n → ℤ) (remaining : ℕ) :
    ∀ (index : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
      (pm : MachinePendingKeys g s α ε ell length logical st),
      index+remaining=(g.neighbors source).length → st.scalar.core.ptrs 109=(index : ℤ) →
      st.scalar.core.ptrs 111=((g.neighbors source).length : ℤ) → st.scalar.core.ptrs 120=((g.neighbors source).length : ℤ) →
      st.scalar.core.ptrs 116=(source.val : ℤ) →
      (∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)=degrees v) →
      pm.queueMass+2*(logical.top+1)*remaining ≤ N →
      ∃ steps out, ∃ memory : MachinePendingKeys g s α ε ell length logical out,
        MachineEval m g ω pendingNeighborRefreshLoopCode st steps out ∧
        steps ≤ remaining*((logical.top+1)*(42*R+60*(16*(ell+3))+284)+4*(16*(ell+3))+25)+1 ∧
        memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*remaining ∧
        out.scalar.core.ptrs 109=((g.neighbors source).length : ℤ) ∧ out.scalar.core.ptrs 111=((g.neighbors source).length : ℤ) ∧
        (∀ i, ∀ hi : i ≤ logical.top, (memory.frames i hi).exteriorObject.keys=
          eligibleInsertList ((logical.frames i).exterior.image Fin.val) (pm.frames i hi).exteriorObject.keys ((g.neighbors source).drop index)) ∧
        (∀ i, ∀ hi : i ≤ logical.top, (memory.frames i hi).highObject.keys=
          eligibleInsertList ((logical.frames i).high.image Fin.val) (pm.frames i hi).highObject.keys ((g.neighbors source).drop index)) ∧
        out.scalar.core.mem=levelRealMemoryFold (pendingNeighborBooleanMemoryUpdate g logical (16*(ell+3)) source degrees)
          index remaining st.scalar.core.mem ∧
        out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧ PendingIntegerFrame pm memory := by
  let H := (logical.top+1)*(42*R+60*(16*(ell+3))+284)+4*(16*(ell+3))+23
  let Q := 2*(logical.top+1)
  induction remaining with
  | zero =>
    intro index st hh pm hCount hIndex hStop hDegree hSource hDegrees hBudget
    have he : index=(g.neighbors source).length := by omega
    have ex : MachineEval m g ω pendingNeighborRefreshLoopCode st 1 (payUnit st) :=
      MachineEval.pointerDone hh (by rw [hStop,hIndex,he])
    refine ⟨1,payUnit st,pm.payUnit,ex,by omega,by change pm.queueMass ≤ pm.queueMass+0; omega,?_,hStop,?_,?_,rfl,rfl,
      ex.unit_work pendingNeighborRefreshLoopCode_wellFormed (by decide) hh,rfl,hh,PendingIntegerFrame.payUnit pm⟩
    · change st.scalar.core.ptrs 109=((g.neighbors source).length : ℤ)
      simpa only [he] using hIndex
    · intro i hi
      simp only [he,List.drop_length,eligibleInsertList,List.foldl_nil]
      rfl
    · intro i hi
      simp only [he,List.drop_length,eligibleInsertList,List.foldl_nil]
      rfl
  | succ remaining ih =>
    intro index st hh pm hCount hIndex hStop hDegree hSource hDegrees hBudget
    have hi : index < (g.neighbors source).length := by omega
    have hProductQ : Q*(remaining+1)=Q*remaining+Q := by ring
    change pm.queueMass+Q*(remaining+1) ≤ N at hBudget
    rw [hProductQ] at hBudget
    obtain ⟨u,b,bMem,eb,hu,bMass,b109,b111,bExt,bHigh,bR,bQ,bW,bO,bH,bFrame⟩ := pending_neighbor_refresh_body_foreign_exec m g ω
      s α ε ell length N R logical hDepth hActiveDomain hExtDomain hHighDomain source hs degrees index hi (payUnit st) hh pm.payUnit
      hSource hDegree hDegrees hIndex (by change pm.queueMass+Q ≤ N; omega) hCap hPow
    have bDegree := (eb.pointer_frame 120 (by decide)).trans hDegree
    have bSource := (eb.pointer_frame 116 (by decide)).trans hSource
    have bDegrees : ∀ v : Fin n, b.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)=degrees v :=
      fun v => (pm.degree_frame bMem v).trans (hDegrees v)
    have bBudget : bMem.queueMass+Q*remaining ≤ N := by
      change bMem.queueMass ≤ pm.queueMass+Q at bMass
      omega
    obtain ⟨w,out,next,er,hw,cMass,c109,c111,cExt,cHigh,cR,cQ,cW,cO,cH,cFrame⟩ :=
      ih (index+1) (payUnit b) bH bMem.payUnit (by omega) b109 b111 bDegree bSource bDegrees bBudget
    have ex : MachineEval m g ω pendingNeighborRefreshLoopCode st (1+u+1+w) out :=
      MachineEval.pointerNext hh (by rw [hStop,hIndex]; omega) eb er
    refine ⟨1+u+1+w,out,next,ex,?_,?_,c109,c111,?_,?_,?_,ex.query_frame (by decide),
      ex.unit_work pendingNeighborRefreshLoopCode_wellFormed (by decide) hh,cO.trans bO,cH,(((PendingIntegerFrame.payUnit pm).trans bFrame).trans (PendingIntegerFrame.payUnit bMem)).trans cFrame⟩
    · have hProduct : (remaining+1)*(H+2)=remaining*(H+2)+(H+2) := by ring
      change u ≤ H at hu
      change w ≤ remaining*(H+2)+1 at hw
      change 1+u+1+w ≤ (remaining+1)*(H+2)+1
      rw [hProduct]
      omega
    · change bMem.queueMass ≤ pm.queueMass+Q at bMass
      change next.queueMass ≤ bMem.queueMass+Q*remaining at cMass
      change next.queueMass ≤ pm.queueMass+Q*(remaining+1)
      rw [hProductQ]
      omega
    · intro i hi'
      have hB : (bMem.frames i hi').exteriorObject.keys=(if (g.neighbors source)[index] ∈ (logical.frames i).exterior then
          insert ((g.neighbors source)[index]).val (pm.frames i hi').exteriorObject.keys else (pm.frames i hi').exteriorObject.keys) := by
        have hKeys : (pm.payUnit.frames i hi').exteriorObject.keys=(pm.frames i hi').exteriorObject.keys := rfl
        simpa only [storedNeighborVertex_eq g source index hi,hKeys] using bExt i hi'
      have hcExt := cExt i hi'
      change (next.frames i hi').exteriorObject.keys=_
      change (next.frames i hi').exteriorObject.keys=
        eligibleInsertList ((logical.frames i).exterior.image Fin.val) (bMem.frames i hi').exteriorObject.keys ((g.neighbors source).drop (index+1)) at hcExt
      rw [hcExt,List.drop_eq_getElem_cons hi,eligible_insert_list_cons_typed,hB]
    · intro i hi'
      have hB : (bMem.frames i hi').highObject.keys=(if (g.neighbors source)[index] ∈ (logical.frames i).high then
          insert ((g.neighbors source)[index]).val (pm.frames i hi').highObject.keys else (pm.frames i hi').highObject.keys) := by
        have hKeys : (pm.payUnit.frames i hi').highObject.keys=(pm.frames i hi').highObject.keys := rfl
        simpa only [storedNeighborVertex_eq g source index hi,hKeys] using bHigh i hi'
      have hcHigh := cHigh i hi'
      change (next.frames i hi').highObject.keys=_
      change (next.frames i hi').highObject.keys=
        eligibleInsertList ((logical.frames i).high.image Fin.val) (bMem.frames i hi').highObject.keys ((g.neighbors source).drop (index+1)) at hcHigh
      rw [hcHigh,List.drop_eq_getElem_cons hi,eligible_insert_list_cons_typed,hB]
    · change out.scalar.core.mem=levelRealMemoryFold (pendingNeighborBooleanMemoryUpdate g logical (16*(ell+3)) source degrees)
        (index+1) remaining (pendingNeighborBooleanMemoryUpdate g logical (16*(ell+3)) source degrees index st.scalar.core.mem)
      change out.scalar.core.mem=levelRealMemoryFold (pendingNeighborBooleanMemoryUpdate g logical (16*(ell+3)) source degrees)
        (index+1) remaining b.scalar.core.mem at cR
      rw [cR,bR]
      rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingNeighborRefresh

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma pendingNeighborRefreshCode_wellFormed : pendingNeighborRefreshCode.wellFormed := by
  refine ⟨?_,pendingNeighborRefreshLoopCode_wellFormed,?_⟩
  all_goals simp [pendingNeighborRefreshInitCode,pendingNeighborRefreshInitInstructions,linearCode,sequenceCode,coreCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 8000000 in
lemma pending_neighbor_refresh_foreign_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length N R : ℕ) (logical : RecursiveState n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : MachinePendingKeys g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hActiveDomain : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hExtDomain : ∀ i ≤ logical.top, (logical.frames i).exterior ⊆ parentDomain logical i)
    (hHighDomain : ∀ i ≤ logical.top, (logical.frames i).high ⊆ parentDomain logical i)
    (source : Fin n) (hs : source ∈ logical.stored) (hSource : st.scalar.core.ptrs 116=(source.val : ℤ))
    (hDegree : st.scalar.core.ptrs 120=((g.neighbors source).length : ℤ))
    (hMass : pm.queueMass+2*(logical.top+1)*(g.neighbors source).length ≤ N) (hCap : R < length) (hPow : N < 2^R) :
    ∃ steps out, ∃ memory : MachinePendingKeys g s α ε ell length logical out,
      MachineEval m g ω pendingNeighborRefreshCode st steps out ∧
      steps ≤ (g.neighbors source).length*((logical.top+1)*(42*R+60*(16*(ell+3))+284)+4*(16*(ell+3))+25)+4 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*(g.neighbors source).length ∧
      out.scalar.core.ptrs 40=(source.val : ℤ) ∧
      (∀ i, ∀ hi : i ≤ logical.top, (memory.frames i hi).exteriorObject.keys=
        eligibleInsertList ((logical.frames i).exterior.image Fin.val) (pm.frames i hi).exteriorObject.keys (g.neighbors source)) ∧
      (∀ i, ∀ hi : i ≤ logical.top, (memory.frames i hi).highObject.keys=
        eligibleInsertList ((logical.frames i).high.image Fin.val) (pm.frames i hi).highObject.keys (g.neighbors source)) ∧
      out.scalar.core.mem=levelRealMemoryFold (pendingNeighborBooleanMemoryUpdate g logical (16*(ell+3)) source
        (fun v => st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)))
        0 (g.neighbors source).length st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧ PendingIntegerFrame pm memory := by
  let a := linearRun m g ω pendingNeighborRefreshInitInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω pendingNeighborRefreshInitInstructions
    (by simp [pendingNeighborRefreshInitInstructions,unitInstruction,straightInstruction]) st hh
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,pendingNeighborRefreshInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aR : a.scalar.core.mem=st.scalar.core.mem := by
    simp [a,linearRun,pendingNeighborRefreshInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,pendingNeighborRefreshInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
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
    simp [a,linearRun,pendingNeighborRefreshInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have a111 : a.scalar.core.ptrs 111=((g.neighbors source).length : ℤ) := by
    simp [a,linearRun,pendingNeighborRefreshInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hDegree]
  obtain ⟨u,b,bMem,eb,hu,bMass,b109,b111,bExt,bHigh,bR,bQ,bW,bO,bH,bFrame⟩ := pending_neighbor_refresh_loop_foreign_exec m g ω s α ε
    ell length N R logical hDepth hCap hPow hActiveDomain hExtDomain hHighDomain source hs
    (fun v => st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)) (g.neighbors source).length 0 a aH aMem
    (by omega) a109 a111 ((ea.pointer_frame 120 (by decide)).trans hDegree) ((ea.pointer_frame 116 (by decide)).trans hSource)
    (by intro v; rw [aI]) hMass
  have ePrefix := MachineEval.seq ea eb
  have b116 := (ePrefix.pointer_frame 116 (by decide)).trans hSource
  let out := payUnit (pointerWrite b 40 (source.val : ℤ))
  have ec : MachineEval m g ω (coreCode (.pcopy 40 116)) b 1 out := by
    simpa only [out,coreCode,b116] using pcopy_eval m g ω b 40 116 bH
  let memory := (bMem.pointerWrite 40 (source.val : ℤ) (by decide)).payUnit
  have ex : MachineEval m g ω pendingNeighborRefreshCode st (2+(u+1)) out := MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨2+(u+1),out,memory,ex,by omega,bMass,by simp [out,payUnit,pcSet,pointerWrite],?_,?_,?_,
    ex.query_frame (by decide),ex.unit_work pendingNeighborRefreshCode_wellFormed (by decide) hh,bO.trans aO,bH,(((PendingIntegerFrame.frame pm aI aR aP aG aO).trans bFrame).trans (PendingIntegerFrame.pointerWrite bMem 40 (source.val : ℤ) (by decide))).trans (PendingIntegerFrame.payUnit (bMem.pointerWrite 40 (source.val : ℤ) (by decide)))⟩
  · intro i hi
    change (bMem.frames i hi).exteriorObject.keys=_
    have hKeys : (aMem.frames i hi).exteriorObject.keys=(pm.frames i hi).exteriorObject.keys := rfl
    simpa only [List.drop_zero,hKeys] using bExt i hi
  · intro i hi
    change (bMem.frames i hi).highObject.keys=_
    have hKeys : (aMem.frames i hi).highObject.keys=(pm.frames i hi).highObject.keys := rfl
    simpa only [List.drop_zero,hKeys] using bHigh i hi
  · change b.scalar.core.mem=_
    rw [bR,aR]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingNeighborBooleanMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma pending_neighbor_boolean_step_at {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (ell : ℕ) (hDepth : logical.top ≤ ell) (source u : Fin n) (degrees : Fin n → ℤ)
    (j : ℕ) (hj : j ≤ logical.top) (i : ℕ) (R : ℤ → ℝ) :
    pendingNeighborBooleanMemoryUpdate g logical (16*(ell+3)) source degrees i R
        (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+4))=
      (if u=storedNeighborVertex g source i ∧ u ∈ parentDomain logical j then sourceHighBooleanValue logical j u (degrees u)
        else R (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+4))) := by
  classical
  unfold pendingNeighborBooleanMemoryUpdate
  by_cases he : u=storedNeighborVertex g source i
  · rw [←he,pending_boolean_fold_at logical ell hDepth u _ j hj]
    simp only [true_and]
  · rw [pending_boolean_fold_other_vertex logical ell hDepth _ u he _ _ (by omega)]
    rw [if_neg (fun h => he h.1)]

lemma pending_neighbor_boolean_fold_at {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (ell : ℕ) (hDepth : logical.top ≤ ell) (source u : Fin n) (degrees : Fin n → ℤ)
    (j : ℕ) (hj : j ≤ logical.top) (R : ℤ → ℝ) :
    levelRealMemoryFold (pendingNeighborBooleanMemoryUpdate g logical (16*(ell+3)) source degrees)
        0 (g.neighbors source).length R (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+4))=
      (if g.graph.Adj source u ∧ u ∈ parentDomain logical j then sourceHighBooleanValue logical j u (degrees u)
        else R (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+4))) := by
  classical
  rw [level_real_payload_eq]
  have h := level_payload_overwrite (pendingNeighborBooleanMemoryUpdate g logical (16*(ell+3)) source degrees)
    (fun i => u=storedNeighborVertex g source i ∧ u ∈ parentDomain logical j) (g.neighbors source).length
    (fun R' => R' (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+4)))
    (sourceHighBooleanValue logical j u (degrees u))
    (fun i hi R' => pending_neighbor_boolean_step_at g logical ell hDepth source u degrees j hj i R')
    (g.neighbors source).length 0 R (by omega)
  have hExist : (∃ i, 0 ≤ i ∧ i < 0+(g.neighbors source).length ∧ u=storedNeighborVertex g source i ∧ u ∈ parentDomain logical j) ↔
      g.graph.Adj source u ∧ u ∈ parentDomain logical j := by
    rw [←g.correct source u]
    constructor
    · rintro ⟨i,hi0,hi,he,hd⟩
      exact ⟨he ▸ storedNeighborVertex_mem g source i (by omega),hd⟩
    · rintro ⟨hu,hd⟩
      obtain ⟨i,hi,he⟩ := List.getElem_of_mem hu
      exact ⟨i,Nat.zero_le _,by omega,((storedNeighborVertex_eq g source i hi).trans he).symm,hd⟩
  simpa only [hExist] using h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingNeighborBooleanRestoration

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma MachinePendingKeys.boolean_neighbors_complete {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st out : MachineState}
    (old : MachinePendingKeys g s α ε ell length logical st)
    (next : MachinePendingKeys g s α ε ell length logical out) (hDepth : logical.top ≤ ell)
    (visited : Finset (Fin n)) (source : Fin n)
    (hOld : ∀ j ≤ logical.top, HighBooleanRecords st.scalar.integerMemory st.scalar.core.mem (16*(ell+3)) (16*(j+1))
      (logical.frames j).theta (parentDomain logical j ∩ visited))
    (hR : out.scalar.core.mem=levelRealMemoryFold
      (pendingNeighborBooleanMemoryUpdate g logical (16*(ell+3)) source
        (fun v => st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)))
      0 (g.neighbors source).length st.scalar.core.mem) :
    ∀ j ≤ logical.top, HighBooleanRecords out.scalar.integerMemory out.scalar.core.mem (16*(ell+3)) (16*(j+1))
      (logical.frames j).theta (parentDomain logical j ∩ (visited ∪ (g.neighbors source).toFinset)) := by
  intro j hj u hu
  have huD := (Finset.mem_inter.mp hu).1
  by_cases hAdj : g.graph.Adj source u
  · calc
      out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+4))=
          sourceHighBooleanValue logical j u (st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) u.val 0)) := by
        rw [hR,pending_neighbor_boolean_fold_at g logical ell hDepth source u _ j hj,if_pos ⟨hAdj,huD⟩]
      _ = _ := (next.high_boolean_value j hj u huD _ (old.degree_frame next u)).symm
  · have hNot : u ∉ (g.neighbors source).toFinset := by
      intro hu'
      exact hAdj ((g.correct source u).mp (List.mem_toFinset.mp hu'))
    have hVisited : u ∈ visited := (Finset.mem_union.mp (Finset.mem_inter.mp hu).2).resolve_right hNot
    have hBit : out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+4))=
        st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+4)) := by
      rw [hR,pending_neighbor_boolean_fold_at g logical ell hDepth source u _ j hj,if_neg (fun h => hAdj h.1)]
    rw [hBit,old.active_frame next j hj u huD,old.degree_frame next u,
      ((next.frames j hj).residual u huD).trans ((old.frames j hj).residual u huD).symm]
    exact hOld j hj u (Finset.mem_inter.mpr ⟨huD,hVisited⟩)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingBooleanPositive

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pending_boolean_fold_positive {n : ℕ} (logical : RecursiveState n) (width : ℕ) (v : Fin n) (degree : ℤ)
    (R : ℤ → ℝ) (z : ℤ) (hz : 0 ≤ z) :
    levelRealMemoryFold (pendingBooleanMemoryUpdate logical width v degree) 0 (logical.top+1) R z=R z := by
  apply level_memory_frame (limit:=logical.top+1)
  · intro i hi R'
    unfold pendingBooleanMemoryUpdate
    split_ifs
    · apply Function.update_of_ne
      have := vertexRecordAddress_negative width v.val (16*(i+1)+4)
      omega
    · rfl
  · omega

lemma pending_neighbor_boolean_fold_positive {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (width : ℕ)
    (source : Fin n) (degrees : Fin n → ℤ) (R : ℤ → ℝ) (z : ℤ) (hz : 0 ≤ z) :
    levelRealMemoryFold (pendingNeighborBooleanMemoryUpdate g logical width source degrees) 0 (g.neighbors source).length R z=R z := by
  apply level_memory_frame (limit:=(g.neighbors source).length)
  · intro i hi R'
    unfold pendingNeighborBooleanMemoryUpdate
    exact pending_boolean_fold_positive logical width _ _ R' z hz
  · omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingTouchedRefresh

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma pendingTouchedRefreshCode_wellFormed : pendingTouchedRefreshCode.wellFormed :=
  ⟨pendingVertexRefreshCode_wellFormed,pendingNeighborRefreshCode_wellFormed⟩

set_option maxHeartbeats 12000000 in
lemma pending_touched_refresh_foreign_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length N R : ℕ) (logical : RecursiveState n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : MachinePendingKeys g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hActiveDomain : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hExtDomain : ∀ i ≤ logical.top, (logical.frames i).exterior ⊆ parentDomain logical i)
    (hHighDomain : ∀ i ≤ logical.top, (logical.frames i).high ⊆ parentDomain logical i)
    (source : Fin n) (hs : source ∈ logical.stored)
    (hSource : st.scalar.core.ptrs 116=(source.val : ℤ)) (hVertex : st.scalar.core.ptrs 40=(source.val : ℤ))
    (hDegree : st.scalar.core.ptrs 120=((g.neighbors source).length : ℤ))
    (hMass : pm.queueMass+2*(logical.top+1)*((g.neighbors source).length+1) ≤ N) (hCap : R < length) (hPow : N < 2^R)
    (hExtOutside : ∀ i, ∀ hi : i ≤ logical.top,
      (logical.frames i).exterior.image Fin.val \ (insert source (g.neighbors source).toFinset).image Fin.val ⊆ (pm.frames i hi).exteriorObject.keys)
    (hHighOutside : ∀ i, ∀ hi : i ≤ logical.top,
      (logical.frames i).high.image Fin.val \ (insert source (g.neighbors source).toFinset).image Fin.val ⊆ (pm.frames i hi).highObject.keys)
    (hBoolOutside : ∀ i ≤ logical.top,
      HighBooleanRecords st.scalar.integerMemory st.scalar.core.mem (16*(ell+3)) (16*(i+1)) (logical.frames i).theta
        (parentDomain logical i \ insert source (g.neighbors source).toFinset)) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω pendingTouchedRefreshCode st steps out ∧
      steps ≤ ((g.neighbors source).length+1)*((logical.top+1)*(42*R+60*(16*(ell+3))+284)+4*(16*(ell+3))+25)+10 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*((g.neighbors source).length+1) ∧
      out.scalar.core.ptrs 40=(source.val : ℤ) ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ z : ℤ, 0 ≤ z → out.scalar.core.mem z=st.scalar.core.mem z) ∧ PendingIntegerFrame pm (MachinePendingKeys.ofMemory memory) := by
  classical
  let Q := 2*(logical.top+1)
  let A := (logical.top+1)*(42*R+60*(16*(ell+3))+284)
  let D := (g.neighbors source).length
  let T := insert source (g.neighbors source).toFinset
  let visited := Finset.univ \ T
  have hCapacity : pm.queueMass+Q*D+Q ≤ N := by
    have hRing : Q*(D+1)=Q*D+Q := by ring
    change pm.queueMass+Q*(D+1) ≤ N at hMass
    rw [hRing] at hMass
    omega
  obtain ⟨u,a,aMem,ea,hu,aMass,aExt,aHigh,aR,aQ,aW,aO,aH,aFrame⟩ := pending_vertex_refresh_foreign_exec m g ω s α ε ell length N R logical
    st hh pm hDepth hActiveDomain hExtDomain hHighDomain source hVertex (by change pm.queueMass+Q ≤ N; omega) hCap hPow
  have aBudget : aMem.queueMass+Q*D ≤ N := by
    change aMem.queueMass ≤ pm.queueMass+Q at aMass
    omega
  obtain ⟨w,out,bMem,eb,hw,bMass,b40,bExt,bHigh,bR,bQ,bW,bO,bH,bFrame⟩ := pending_neighbor_refresh_foreign_exec m g ω s α ε ell length N R logical
    a aH aMem hDepth hActiveDomain hExtDomain hHighDomain source hs
    ((ea.pointer_frame 116 (by decide)).trans hSource) ((ea.pointer_frame 120 (by decide)).trans hDegree) aBudget hCap hPow
  have hInitial : ∀ i ≤ logical.top,
      HighBooleanRecords st.scalar.integerMemory st.scalar.core.mem (16*(ell+3)) (16*(i+1)) (logical.frames i).theta
        (parentDomain logical i ∩ visited) := by
    intro i hi v hv
    have hv' : v ∈ parentDomain logical i \ T := by
      rcases Finset.mem_inter.mp hv with ⟨hd,hv⟩
      exact Finset.mem_sdiff.mpr ⟨hd,(Finset.mem_sdiff.mp hv).2⟩
    exact hBoolOutside i hi v hv'
  have hA := pm.boolean_refresh_complete aMem hDepth visited source hInitial aR
  have hB := aMem.boolean_neighbors_complete bMem hDepth (insert source visited) source hA bR
  have hAll : insert source visited ∪ (g.neighbors source).toFinset=Finset.univ := by
    ext v
    by_cases hv : v=source <;> by_cases hn : v ∈ (g.neighbors source).toFinset <;>
      simp [visited,T,hv,hn]
  have hBool : ∀ i ≤ logical.top,
      HighBooleanRecords out.scalar.integerMemory out.scalar.core.mem (16*(ell+3)) (16*(i+1)) (logical.frames i).theta
        (parentDomain logical i) := by
    intro i hi
    simpa only [hAll,Finset.inter_univ] using hB i hi
  have hVertices : ((source::g.neighbors source).map Fin.val).toFinset=T.image Fin.val := by
    ext k
    simp only [T,List.mem_toFinset,List.mem_map,Finset.mem_image,List.mem_cons,Finset.mem_insert]
  have hExt : ∀ i, ∀ hi : i ≤ logical.top,
      (logical.frames i).exterior.image Fin.val ⊆ (bMem.frames i hi).exteriorObject.keys := by
    intro i hi
    have hKeys : (bMem.frames i hi).exteriorObject.keys=
        eligibleInsertList ((logical.frames i).exterior.image Fin.val) (pm.frames i hi).exteriorObject.keys (source::g.neighbors source) := by
      rw [bExt i hi,eligible_insert_list_cons_typed,aExt i hi]
    rw [hKeys]
    apply eligible_insert_list_cover
    rw [hVertices]
    exact hExtOutside i hi
  have hHigh : ∀ i, ∀ hi : i ≤ logical.top,
      (logical.frames i).high.image Fin.val ⊆ (bMem.frames i hi).highObject.keys := by
    intro i hi
    have hKeys : (bMem.frames i hi).highObject.keys=
        eligibleInsertList ((logical.frames i).high.image Fin.val) (pm.frames i hi).highObject.keys (source::g.neighbors source) := by
      rw [bHigh i hi,eligible_insert_list_cons_typed,aHigh i hi]
    rw [hKeys]
    apply eligible_insert_list_cover
    rw [hVertices]
    exact hHighOutside i hi
  let memory := bMem.finish hExt hBool hHigh
  have ex : MachineEval m g ω pendingTouchedRefreshCode st (u+w) out := MachineEval.seq ea eb
  refine ⟨u+w,out,memory,ex,?_,?_,b40,ex.query_frame (by decide),
    ex.unit_work pendingTouchedRefreshCode_wellFormed (by decide) hh,bO.trans aO,bH,?_,?_⟩
  · change u ≤ A+6 at hu
    change w ≤ D*(A+4*(16*(ell+3))+25)+4 at hw
    change u+w ≤ (D+1)*(A+4*(16*(ell+3))+25)+10
    have hRing : (D+1)*(A+4*(16*(ell+3))+25)=D*(A+4*(16*(ell+3))+25)+(A+4*(16*(ell+3))+25) := by ring
    rw [hRing]
    omega
  · change aMem.queueMass ≤ pm.queueMass+Q at aMass
    change bMem.queueMass ≤ aMem.queueMass+Q*D at bMass
    change bMem.queueMass ≤ pm.queueMass+Q*(D+1)
    have hRing : Q*(D+1)=Q*D+Q := by ring
    rw [hRing]
    omega

  · intro z hz
    rw [bR,pending_neighbor_boolean_fold_positive g logical (16*(ell+3)) source _ _ z hz,
      aR,pending_boolean_fold_positive logical (16*(ell+3)) source _ _ z hz]

  · change PendingIntegerFrame pm bMem
    exact aFrame.trans bFrame

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution : ∀ (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length N R : ℕ) (logical : RecursiveState n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : MachinePendingKeys g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hActiveDomain : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hExtDomain : ∀ i ≤ logical.top, (logical.frames i).exterior ⊆ parentDomain logical i)
    (hHighDomain : ∀ i ≤ logical.top, (logical.frames i).high ⊆ parentDomain logical i)
    (source : Fin n) (hs : source ∈ logical.stored)
    (hSource : st.scalar.core.ptrs 116=(source.val : ℤ)) (hVertex : st.scalar.core.ptrs 40=(source.val : ℤ))
    (hDegree : st.scalar.core.ptrs 120=((g.neighbors source).length : ℤ))
    (hMass : pm.queueMass+2*(logical.top+1)*((g.neighbors source).length+1) ≤ N) (hCap : R < length) (hPow : N < 2^R)
    (hExtOutside : ∀ i, ∀ hi : i ≤ logical.top,
      (logical.frames i).exterior.image Fin.val \ (insert source (g.neighbors source).toFinset).image Fin.val ⊆ (pm.frames i hi).exteriorObject.keys)
    (hHighOutside : ∀ i, ∀ hi : i ≤ logical.top,
      (logical.frames i).high.image Fin.val \ (insert source (g.neighbors source).toFinset).image Fin.val ⊆ (pm.frames i hi).highObject.keys)
    (hBoolOutside : ∀ i ≤ logical.top,
      HighBooleanRecords st.scalar.integerMemory st.scalar.core.mem (16*(ell+3)) (16*(i+1)) (logical.frames i).theta
        (parentDomain logical i \ insert source (g.neighbors source).toFinset)),
∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω pendingTouchedRefreshCode st steps out ∧
      steps ≤ ((g.neighbors source).length+1)*((logical.top+1)*(42*R+60*(16*(ell+3))+284)+4*(16*(ell+3))+25)+10 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*((g.neighbors source).length+1) ∧
      out.scalar.core.ptrs 40=(source.val : ℤ) ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ z : ℤ, 0 ≤ z → out.scalar.core.mem z=st.scalar.core.mem z) ∧ PendingIntegerFrame pm (MachinePendingKeys.ofMemory memory) := by
  exact @NearlyOptimalPPR.Computation.pending_touched_refresh_foreign_exec
