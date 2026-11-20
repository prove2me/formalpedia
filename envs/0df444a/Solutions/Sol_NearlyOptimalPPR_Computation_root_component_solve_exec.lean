-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.root_component_solve_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:28:01.250917+00:00
-- url     : https://prove2.me/submissions/28ba1999-7031-454e-9f1e-1124f57c92fe

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
-- Proof module: Solutions.JointCoordinateSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open Matrix
noncomputable section

def jointCoordinateUpdate {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (v : Fin n) (δ : ℝ) : RecursiveState n :=
  refreshKeys g (jointUpdate g α logical (fun u => if u=v then δ else 0)) (insert v (g.neighbors v).toFinset)

end
end NearlyOptimalPPR.Computation

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

lemma ForestRep.nil_iff {I : ℤ → ℤ} {p : ℤ} {F : Finset ℤ}
    (h : ForestRep I p .nil F) : p=0 ∧ F=∅ := by cases h; exact ⟨rfl,rfl⟩

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

-- Proof module: Solutions.AdjacencyMetadataSemantics

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma vertexRecordAddress_offset_injective (width vertex i j : ℕ)
    (h : vertexRecordAddress width vertex i=vertexRecordAddress width vertex j) : i=j := by
  unfold vertexRecordAddress at h
  omega

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

lemma GraphCache.below_frame {n : ℕ} {g : InputGraph n} {I J : ℤ → ℤ} {width : ℕ}
    {stored : Finset (Fin n)} {free : ℤ} (h : GraphCache g I width stored free)
    (he : ∀ z, z < free → J z=I z) : GraphCache g J width stored free := by
  apply h.frame g I J width stored free
  · intro v field hf
    apply he
    have hn := vertexRecordAddress_negative width v.val field
    have hb := h.freeBound
    omega
  · intro v hv i hi
    exact he _ (h.belowFree v hv i hi)

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

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndexMarkCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def indexMarkWords (I : ℤ → ℤ) (width vertex : ℕ) (epoch index : ℤ) : ℤ → ℤ :=
  Function.update (Function.update I (vertexRecordAddress width vertex 7) epoch)
    (vertexRecordAddress width vertex 8) (index+1)

set_option maxHeartbeats 1200000 in
lemma index_mark_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) :
    ∃ out, MachineEval m g ω indexMarkCode st (8*width+20) out ∧
      out.scalar.integerMemory=indexMarkWords st.scalar.integerMemory width vertex
        (st.scalar.core.ptrs 53) (st.scalar.core.ptrs 75) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(8*width+20 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨A,ea,hAI,hAR,hAQ,hAW,hAO,hAH⟩ := vertex_field_write_exec m g ω st hh width vertex 7 53 hz hv hw
  let B := payUnit (pointerWrite A 51 (st.scalar.core.ptrs 75))
  let C := payUnit (pointerWrite B 51 (st.scalar.core.ptrs 75+1))
  have a75 := ea.pointer_frame 75 (by decide)
  have eb : MachineEval m g ω (coreCode (.pcopy 51 75)) A 1 B := by
    simpa only [B,coreCode,a75] using pcopy_eval m g ω A 51 75 hAH
  have bH : B.scalar.halted=false := hAH
  have b51 : B.scalar.core.ptrs 51=st.scalar.core.ptrs 75 := by simp [B,payUnit,pcSet,pointerWrite]
  have ec : MachineEval m g ω (coreCode (.pinc 51)) B 1 C := by
    simpa only [C,coreCode,b51] using pinc_eval m g ω B 51 bH
  have cH : C.scalar.halted=false := hAH
  have c51 : C.scalar.core.ptrs 51=st.scalar.core.ptrs 75+1 := by simp [C,payUnit,pcSet,pointerWrite]
  have c0 : C.scalar.core.ptrs 0=0 := by simpa [C,B,payUnit,pcSet,pointerWrite] using (ea.pointer_frame 0 (by decide)).trans hz
  have c40 : C.scalar.core.ptrs 40=(vertex : ℤ) := by simpa [C,B,payUnit,pcSet,pointerWrite] using (ea.pointer_frame 40 (by decide)).trans hv
  have c41 : C.scalar.core.ptrs 41=(width : ℤ) := by simpa [C,B,payUnit,pcSet,pointerWrite] using (ea.pointer_frame 41 (by decide)).trans hw
  obtain ⟨out,ed,hDI,hDR,hDQ,hDW,hDO,hDH⟩ := vertex_field_write_exec m g ω C cH width vertex 8 51 c0 c40 c41
  have e : MachineEval m g ω indexMarkCode st (8*width+20) out := by
    have ee := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,e,?_,hDR.trans hAR,?_,?_,hDO.trans hAO,hDH⟩
  · rw [hDI,c51]
    change Function.update A.scalar.integerMemory (vertexRecordAddress width vertex 8) (st.scalar.core.ptrs 75+1)= _
    rw [hAI]
    rfl
  · exact e.query_frame (by simp [indexMarkCode,MachineCode.allAtoms,vertexFieldWriteCode_queryReadOnly,coreCode,queryReadOnly])
  · rw [hDW]
    change A.work+1+1+(4*width+9 : ℕ)= _
    rw [hAW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndexTable

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma indexMarkWords_self (I : ℤ → ℤ) (width vertex : ℕ) (epoch index : ℤ) :
    indexMarkWords I width vertex epoch index (vertexRecordAddress width vertex 7)=epoch ∧
      indexMarkWords I width vertex epoch index (vertexRecordAddress width vertex 8)=index+1 := by
  have hn : vertexRecordAddress width vertex 7 ≠ vertexRecordAddress width vertex 8 := by
    intro he; have h := vertexRecordAddress_offset_injective _ _ _ _ he; omega
  simp [indexMarkWords,Function.update_of_ne hn]

lemma indexMarkWords_other (I : ℤ → ℤ) (width vertex other field : ℕ)
    (hw : 9 ≤ width) (hf : field < width) (ho : other ≠ vertex) (epoch index : ℤ) :
    indexMarkWords I width vertex epoch index (vertexRecordAddress width other field)=
      I (vertexRecordAddress width other field) := by
  have hn (i : ℕ) (hi : i < 9) : vertexRecordAddress width other field ≠ vertexRecordAddress width vertex i := by
    intro he
    exact ho (vertexRecordAddress_injective width other vertex field i hf (by omega) he).1
  simp [indexMarkWords,Function.update_of_ne (hn 7 (by omega)),Function.update_of_ne (hn 8 (by omega))]

lemma indexMarkWords_tag {n : ℕ} (I : ℤ → ℤ) (width : ℕ) (v u : Fin n) (hw : 9 ≤ width) (epoch index : ℤ) :
    indexMarkWords I width v.val epoch index (vertexRecordAddress width u.val 7)=
      if u=v then epoch else I (vertexRecordAddress width u.val 7) := by
  by_cases he : u=v
  · subst u; simpa using (indexMarkWords_self I width v.val epoch index).1
  · rw [if_neg he]
    exact indexMarkWords_other I width v.val u.val 7 hw (by omega) (by intro h; exact he (Fin.ext h)) epoch index

lemma indexMarkWords_index {n : ℕ} (I : ℤ → ℤ) (width : ℕ) (v u : Fin n) (hw : 9 ≤ width) (epoch index : ℤ) :
    indexMarkWords I width v.val epoch index (vertexRecordAddress width u.val 8)=
      if u=v then index+1 else I (vertexRecordAddress width u.val 8) := by
  by_cases he : u=v
  · subst u; simpa using (indexMarkWords_self I width v.val epoch index).2
  · rw [if_neg he]
    exact indexMarkWords_other I width v.val u.val 8 hw (by omega) (by intro h; exact he (Fin.ext h)) epoch index


def IndexPrefix {n k : ℕ} (I : ℤ → ℤ) (width : ℕ) (epoch : ℤ) (e : Fin k → Fin n) (upto : ℕ) : Prop :=
  (∀ v : Fin n, I (vertexRecordAddress width v.val 7) ≤ epoch) ∧
  (∀ v : Fin n, I (vertexRecordAddress width v.val 7)=epoch ↔ ∃ j : Fin k, j.val<upto ∧ e j=v) ∧
  (∀ j : Fin k, j.val<upto → I (vertexRecordAddress width (e j).val 8)=(j.val : ℤ)+1)

lemma indexPrefix_empty {n k : ℕ} (I : ℤ → ℤ) (width : ℕ) (epoch : ℤ) (e : Fin k → Fin n)
    (h : ∀ v : Fin n, I (vertexRecordAddress width v.val 7)<epoch) : IndexPrefix I width epoch e 0 := by
  refine ⟨fun v => (h v).le,?_,?_⟩
  · intro v
    constructor
    · intro he; have hv := h v; omega
    · rintro ⟨j,hj,_⟩; omega
  · intro j hj; omega

set_option maxHeartbeats 1400000 in
lemma indexPrefix_advance {n k : ℕ} (I : ℤ → ℤ) (width : ℕ) (epoch : ℤ) (e : Fin k → Fin n)
    (he : Function.Injective e) (hw : 9 ≤ width) (i : Fin k)
    (h : IndexPrefix I width epoch e i.val) :
    IndexPrefix (indexMarkWords I width (e i).val epoch i.val) width epoch e (i.val+1) := by
  refine ⟨?_,?_,?_⟩
  · intro v
    rw [indexMarkWords_tag I width (e i) v hw]
    split_ifs
    · exact le_rfl
    · exact h.1 v
  · intro v
    rw [indexMarkWords_tag I width (e i) v hw]
    by_cases hv : v=e i
    · rw [if_pos hv]
      constructor
      · intro _; exact ⟨i,by omega,hv.symm⟩
      · intro _; rfl
    · rw [if_neg hv,h.2.1 v]
      constructor
      · rintro ⟨j,hj,hjv⟩
        exact ⟨j,by omega,hjv⟩
      · rintro ⟨j,hj,hjv⟩
        have hji : j ≠ i := by intro hji; subst j; exact hv hjv.symm
        have hval : j.val ≠ i.val := fun hval => hji (Fin.ext hval)
        exact ⟨j,by omega,hjv⟩
  · intro j hj
    rw [indexMarkWords_index I width (e i) (e j) hw]
    by_cases hji : j=i
    · subst j; simp
    · have hneq : e j ≠ e i := fun hEq => hji (he hEq)
      rw [if_neg hneq]
      apply h.2.2 j
      have hval : j.val ≠ i.val := fun hval => hji (Fin.ext hval)
      omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndexMarkMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma indexMarkWords_nonnegative (I : ℤ → ℤ) (width vertex : ℕ) (epoch index z : ℤ) (hz : 0 ≤ z) :
    indexMarkWords I width vertex epoch index z=I z := by
  have hn (i : ℕ) : z ≠ vertexRecordAddress width vertex i := by
    have h := vertexRecordAddress_negative width vertex i
    omega
  simp [indexMarkWords,Function.update_of_ne (hn 7),Function.update_of_ne (hn 8)]

lemma indexMarkWords_cache_fields (I : ℤ → ℤ) (width vertex other field : ℕ) (hw : 9 ≤ width)
    (hf : field < 3) (epoch index : ℤ) :
    indexMarkWords I width vertex epoch index (vertexRecordAddress width other field)=
      I (vertexRecordAddress width other field) := by
  have hn (i : ℕ) (hi : 7 ≤ i ∧ i < 9) : vertexRecordAddress width other field ≠ vertexRecordAddress width vertex i := by
    intro he
    have h := (vertexRecordAddress_injective width other vertex field i (by omega) (by omega) he).2
    omega
  simp [indexMarkWords,Function.update_of_ne (hn 7 (by omega)),Function.update_of_ne (hn 8 (by omega))]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndexMarkBody

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma indexMarkBodyCode_queryReadOnly : indexMarkBodyCode.allAtoms queryReadOnly := by
  simp [indexMarkBodyCode,indexMarkCode,MachineCode.allAtoms,vertexFieldWriteCode_queryReadOnly,coreCode,queryReadOnly]

set_option maxHeartbeats 1400000 in
lemma index_mark_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width : ℕ) (v : Fin n)
    (base epoch : ℤ) (i : ℕ) (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hb : st.scalar.core.ptrs 80=base) (he : st.scalar.core.ptrs 53=epoch)
    (hi : st.scalar.core.ptrs 75=(i : ℤ)) (hval : st.scalar.integerMemory (base+(i : ℤ))=(v.val : ℤ)) :
    ∃ out, MachineEval m g ω indexMarkBodyCode st (8*width+23) out ∧
      out.scalar.core.ptrs 75=(i+1 : ℕ) ∧
      out.scalar.integerMemory=indexMarkWords st.scalar.integerMemory width v.val epoch i ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(8*width+23 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let A := payUnit (pointerWrite st 81 (base+(i : ℤ)))
  let B := payUnit (pointerWrite A 40 (v.val : ℤ))
  have ea : MachineEval m g ω (.atom (.scalar (.pointerAdd 81 80 75))) st 1 A := by
    simpa only [A,hb,hi] using pointerAdd_eval m g ω st 81 80 75 hh
  have ah : A.scalar.halted=false := hh
  have eb : MachineEval m g ω (.atom (.scalar (.integerLoad 40 81))) A 1 B := by
    have hv : A.scalar.integerMemory (A.scalar.core.ptrs 81)=(v.val : ℤ) := by
      simpa [A,payUnit,pcSet,pointerWrite] using hval
    simpa only [B,hv] using integerLoad_eval m g ω A 40 81 ah
  have bh : B.scalar.halted=false := hh
  have b0 : B.scalar.core.ptrs 0=0 := by simpa [B,A,payUnit,pcSet,pointerWrite] using hz
  have b40 : B.scalar.core.ptrs 40=(v.val : ℤ) := by simp [B,payUnit,pcSet,pointerWrite]
  have b41 : B.scalar.core.ptrs 41=(width : ℤ) := by simpa [B,A,payUnit,pcSet,pointerWrite] using hw
  obtain ⟨mid,ec,hmI,hmR,hmQ,hmW,hmO,hmH⟩ := index_mark_exec m g ω B bh width v.val b0 b40 b41
  have hm75 : mid.scalar.core.ptrs 75=(i : ℤ) := by
    exact (ec.pointer_frame 75 (by decide)).trans (by simpa [B,A,payUnit,pcSet,pointerWrite] using hi)
  have b53 : B.scalar.core.ptrs 53=epoch := by simpa [B,A,payUnit,pcSet,pointerWrite] using he
  have b75 : B.scalar.core.ptrs 75=(i : ℤ) := by simpa [B,A,payUnit,pcSet,pointerWrite] using hi
  rw [b53,b75] at hmI
  let out := payUnit (pointerWrite mid 75 (i+1 : ℕ))
  have eo : MachineEval m g ω (coreCode (.pinc 75)) mid 1 out := by
    simpa only [out,coreCode,hm75,Nat.cast_add,Nat.cast_one] using pinc_eval m g ω mid 75 hmH
  have e : MachineEval m g ω indexMarkBodyCode st (8*width+23) out := by
    have ee := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec eo))
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,e,by simp [out,payUnit,pcSet,pointerWrite],hmI,hmR,
    e.query_frame indexMarkBodyCode_queryReadOnly,?_,hmO,hmH⟩
  · change mid.work+1= _
    rw [hmW]
    change st.work+1+1+(8*width+20 : ℕ)+1= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndexMarkLoop

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2000000 in
lemma index_mark_loop_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width : ℕ) (hw9 : 9 ≤ width) (e : Fin k → Fin n) (he : Function.Injective e)
    (base epoch : ℤ) (hb0 : 0 ≤ base) (remaining i : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hb : st.scalar.core.ptrs 80=base) (hE : st.scalar.core.ptrs 53=epoch)
    (hk : st.scalar.core.ptrs 77=(k : ℤ)) (hi : st.scalar.core.ptrs 75=(i : ℤ))
    (hlen : i+remaining=k) (henum : EnumerationStored st.scalar.integerMemory base e)
    (hprefix : IndexPrefix st.scalar.integerMemory width epoch e i) :
    ∃ out, MachineEval m g ω indexMarkLoopCode st (remaining*(8*width+25)+1) out ∧
      out.scalar.core.ptrs 0=0 ∧ out.scalar.core.ptrs 41=(width : ℤ) ∧ out.scalar.core.ptrs 80=base ∧
      out.scalar.core.ptrs 53=epoch ∧ out.scalar.core.ptrs 77=(k : ℤ) ∧ out.scalar.core.ptrs 75=(k : ℤ) ∧
      EnumerationStored out.scalar.integerMemory base e ∧ IndexPrefix out.scalar.integerMemory width epoch e k ∧
      (∀ z, 0 ≤ z → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ v : Fin n, ∀ field < 3, out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field)) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(remaining*(8*width+25)+1 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction remaining generalizing st i with
  | zero =>
    have heq : i=k := by omega
    refine ⟨payUnit st,?_,hz,hw,hb,hE,hk,by simpa [heq] using hi,henum,?_,
      (by intros; rfl),(by intros; rfl),rfl,rfl,by simp,rfl,hh⟩
    · simpa only [indexMarkLoopCode,Nat.zero_mul,Nat.zero_add] using
        (MachineEval.pointerDone (m:=m) (g:=g) (ω:=ω) (r:=77) (s:=75) (body:=indexMarkBodyCode) hh (by rw [hk,hi,heq]))
    · simpa only [payUnit,pcSet,heq] using hprefix
  | succ remaining ih =>
    have hik : i < k := by omega
    let ii : Fin k := ⟨i,hik⟩
    obtain ⟨mid,eb,hm75,hmI,hmR,hmQ,hmW,hmO,hmH⟩ :=
      index_mark_body_exec m g ω (payUnit st) hh width (e ii) base epoch i hz hw hb hE hi (henum ii)
    have hm0 := (eb.pointer_frame 0 (by decide)).trans hz
    have hm41 := (eb.pointer_frame 41 (by decide)).trans hw
    have hm80 := (eb.pointer_frame 80 (by decide)).trans hb
    have hm53 := (eb.pointer_frame 53 (by decide)).trans hE
    have hm77 := (eb.pointer_frame 77 (by decide)).trans hk
    have hmPositive : ∀ z, 0 ≤ z → mid.scalar.integerMemory z=st.scalar.integerMemory z := by
      intro z hz'
      rw [hmI]
      exact indexMarkWords_nonnegative _ _ _ _ _ _ hz'
    have hmFields : ∀ v : Fin n, ∀ field < 3, mid.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field) := by
      intro v field hf
      rw [hmI]
      exact indexMarkWords_cache_fields _ _ _ _ _ hw9 hf _ _
    have hmEnum : EnumerationStored mid.scalar.integerMemory base e := by
      intro j
      rw [hmPositive _ (by omega)]
      exact henum j
    have hmPrefix : IndexPrefix mid.scalar.integerMemory width epoch e (i+1) := by
      rw [hmI]
      exact indexPrefix_advance _ _ _ e he hw9 ii hprefix
    obtain ⟨out,er,ho0,ho41,ho80,ho53,ho77,ho75,hoEnum,hoPrefix,hoPositive,hoFields,hoR,hoQ,hoW,hoO,hoH⟩ :=
      ih (i+1) (payUnit mid) hmH hm0 hm41 hm80 hm53 hm77 hm75 (by omega) hmEnum hmPrefix
    refine ⟨out,?_,ho0,ho41,ho80,ho53,ho77,ho75,hoEnum,hoPrefix,?_,?_,
      hoR.trans hmR,hoQ.trans hmQ,?_,hoO.trans hmO,hoH⟩
    · have eRun := MachineEval.pointerNext (r:=77) (s:=75) hh (by rw [hk,hi]; omega) eb er
      convert eRun using 1 <;> (first | rfl | ring)
    · intro z hz'
      exact (hoPositive z hz').trans (hmPositive z hz')
    · intro v field hf
      exact (hoFields v field hf).trans (hmFields v field hf)
    · rw [hoW,payUnit_work,hmW,payUnit_work]
      push_cast
      ring

end
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

-- Proof module: Solutions.JointSolveIterationState

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def jointSolveIterationState {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) (h : Fin n → ℝ)
    (index count : ℕ) (logical : RecursiveState n) : RecursiveState n :=
  match count with
  | 0 => logical
  | remaining+1 => if hi : index < k then
      jointSolveIterationState g α e h (index+1) remaining (jointCoordinateUpdate g α logical (e ⟨index,hi⟩) (h (e ⟨index,hi⟩)))
    else logical

def jointSolveIterationVolume {n k : ℕ} (g : InputGraph n) (e : Fin k → Fin n) (index count : ℕ) : ℕ :=
  match count with
  | 0 => 0
  | remaining+1 => if hi : index < k then
      (g.neighbors (e ⟨index,hi⟩)).length+1+jointSolveIterationVolume g e (index+1) remaining else 0

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointSolveIterationVolume

set_option autoImplicit false
set_option maxRecDepth 10000
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma joint_iteration_volume_sum {n k : ℕ} (g : InputGraph n) (e : Fin k → Fin n) (index count : ℕ) :
    jointSolveIterationVolume g e index count=
      ∑ j ∈ Finset.range count, if hj : index+j < k then (g.neighbors (e ⟨index+j,hj⟩)).length+1 else 0 := by
  induction count generalizing index with
  | zero => simp [jointSolveIterationVolume]
  | succ count ih =>
    rw [Finset.sum_range_succ']
    by_cases hi : index < k
    · rw [jointSolveIterationVolume,dif_pos hi,ih]
      simp only [Nat.add_zero,dif_pos hi]
      have hRest : (∑ j ∈ Finset.range count, if hj : (index+1)+j < k then (g.neighbors (e ⟨(index+1)+j,hj⟩)).length+1 else 0)=
          ∑ j ∈ Finset.range count, if hj : index+(j+1) < k then (g.neighbors (e ⟨index+(j+1),hj⟩)).length+1 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        have he : index+1+j=index+(j+1) := by omega
        simp only [he]
      rw [hRest]
      exact Nat.add_comm _ _
    · have hNever : ∀ j : ℕ, ¬ index+j < k := by intros; omega
      simp only [jointSolveIterationVolume,dif_neg hi,Nat.add_zero,dif_neg hi,zero_add]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      rw [dif_neg (hNever (j+1))]

lemma joint_iteration_volume_full {n k : ℕ} (g : InputGraph n) (e : Fin k → Fin n) :
    jointSolveIterationVolume g e 0 k=∑ i : Fin k, ((g.neighbors (e i)).length+1) := by
  rw [joint_iteration_volume_sum,Finset.sum_fin_eq_sum_range]
  simp only [Nat.zero_add]

lemma joint_iteration_volume_domain {n k : ℕ} (g : InputGraph n) (e : Fin k → Fin n) (he : Function.Injective e) :
    jointSolveIterationVolume g e 0 k=volumeNat g (Finset.univ.image e)+(Finset.univ.image e).card := by
  rw [joint_iteration_volume_full,Finset.sum_add_distrib]
  have hVolume : (∑ i : Fin k, (g.neighbors (e i)).length)=volumeNat g (Finset.univ.image e) := by
    unfold volumeNat
    rw [Finset.sum_image]
    exact fun a ha b hb h => he h
  rw [hVolume]
  simp [Finset.card_image_of_injective _ he]

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

lemma vertexEnumerationCode_queryReadOnly : vertexEnumerationCode.allAtoms queryReadOnly := by
  simp [vertexEnumerationCode,vertexEnumerationInit,PointerRoutine.sequence,PointerRoutine.code,
    PointerOp.instruction,vertexListCopyLoopCode,MachineCode.allAtoms,
    vertexListCopyBodyCode_queryReadOnly,coreCode,queryReadOnly]

lemma vertexEnumeration_injective {n : ℕ} (vertices : List (Fin n)) (h : vertices.Nodup) :
    Function.Injective (vertexEnumeration vertices) := by
  exact List.nodup_iff_injective_getElem.mp h

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

lemma vertex_enumeration_member {n : ℕ} (vertices : List (Fin n)) (i : Fin vertices.length) :
    vertexEnumeration vertices i ∈ vertices := List.get_mem vertices i

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolveExecution

set_option autoImplicit false
open scoped ENNReal
open Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma writeAnswer_at (st : LocalPush.State) (r : SolveRegisters) (k : ℕ) (x : Fin k → ℝ) (i : Fin k) :
    (writeAnswer st r k x).core.mem (st.core.ptrs r.answer+(i.val : ℤ))=x i := by
  simp [writeAnswer,i.isLt]

lemma writeAnswer_outside (st : LocalPush.State) (r : SolveRegisters) (k : ℕ) (x : Fin k → ℝ) (a : ℤ)
    (ha : ¬(0 ≤ a-st.core.ptrs r.answer ∧ (a-st.core.ptrs r.answer).toNat < k)) :
    (writeAnswer st r k x).core.mem a=st.core.mem a := by
  unfold writeAnswer
  exact dif_neg ha

set_option maxHeartbeats 1000000 in
lemma solve_instruction_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (r : SolveRegisters)
    (hd : 0<st.scalar.core.ptrs r.dimension) (hl : 0 ≤ st.scalar.core.ptrs r.length)
    (hA : SDDM (suppliedMatrix st.scalar r (st.scalar.core.ptrs r.dimension).toNat
      (st.scalar.core.ptrs r.length).toNat)) :
    let k := (st.scalar.core.ptrs r.dimension).toNat
    let q := (st.scalar.core.ptrs r.length).toNat
    ∃ out, MachineEval m g ω (.atom (.solve r)) st 1 out ∧
      out.scalar.core.mem=(writeAnswer st.scalar r k ((suppliedMatrix st.scalar r k q)⁻¹ *ᵥ
        (fun i : Fin k => st.scalar.core.mem (st.scalar.core.ptrs r.rhs+i.val)))).core.mem ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.ptrs=st.scalar.core.ptrs ∧
      out.scalar.core.regs=st.scalar.core.regs ∧
      out.work=st.work+solveCharge m k q ∧ out.output=st.output ∧ out.scalar.halted=false := by
  dsimp only
  let k := (st.scalar.core.ptrs r.dimension).toNat
  let q := (st.scalar.core.ptrs r.length).toNat
  let x := (suppliedMatrix st.scalar r k q)⁻¹ *ᵥ
    (fun i : Fin k => st.scalar.core.mem (st.scalar.core.ptrs r.rhs+i.val))
  let out := pcSet (atomState m g ω (.solve r) st) 0
  have hvalid : 0 < (pcSet st 0).scalar.core.ptrs r.dimension ∧
      0 ≤ (pcSet st 0).scalar.core.ptrs r.length ∧
      SDDM (suppliedMatrix (pcSet st 0).scalar r
        ((pcSet st 0).scalar.core.ptrs r.dimension).toNat ((pcSet st 0).scalar.core.ptrs r.length).toNat) := ⟨hd,hl,hA⟩
  have stepEq : atomState m g ω (.solve r) st=
      {scalar:=writeAnswer (pcSet st 0).scalar r k x,output:=st.output,work:=st.work+solveCharge m k q} := by
    simp only [atomState,machineStep,pcSet_halted,hh,Bool.false_eq_true,if_false,
      pcSet_pc,List.getElem?_cons_zero,if_pos hvalid]
    rfl
  have e : MachineEval m g ω (.atom (.solve r)) st 1 out := MachineEval.atom _ st (by rw [stepEq]; rfl)
  refine ⟨out,e,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals simp [out,stepEq,pcSet,writeAnswer,hh,k,q,x]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SparseEncoding

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

def decodeEntries (k : ℕ) (entries : List SparseEntry) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => (entries.map fun a => if a.row=(i.val : ℤ) ∧ a.column=(j.val : ℤ) then a.value else 0).sum


def EntriesStored (st : LocalPush.State) (r : SolveRegisters) (entries : List SparseEntry) : Prop :=
  ∀ i (hi : i < entries.length),
    st.integerMemory (st.core.ptrs r.rows+(i : ℤ))=entries[i].row ∧
    st.integerMemory (st.core.ptrs r.columns+(i : ℤ))=entries[i].column ∧
    st.core.mem (st.core.ptrs r.values+(i : ℤ))=entries[i].value

lemma suppliedMatrix_decode (st : LocalPush.State) (r : SolveRegisters) (k : ℕ) (entries : List SparseEntry)
    (h : EntriesStored st r entries) : suppliedMatrix st r k entries.length=decodeEntries k entries := by
  ext i j
  unfold suppliedMatrix decodeEntries
  rw [Finset.sum_range,←List.ofFn_getElem_eq_map entries
    (fun a => if a.row=(i.val : ℤ) ∧ a.column=(j.val : ℤ) then a.value else 0),List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨hr,hc,hv⟩ := h a.val a.isLt
  simp only [hr,hc,hv]

@[simp] lemma decodeEntries_nil (k : ℕ) : decodeEntries k []=0 := by
  ext i j
  simp [decodeEntries]

lemma decodeEntries_append (k : ℕ) (a b : List SparseEntry) :
    decodeEntries k (a++b)=decodeEntries k a+decodeEntries k b := by
  ext i j
  simp [decodeEntries,List.map_append,List.sum_append]

lemma decodeEntries_cons (k : ℕ) (a : SparseEntry) (entries : List SparseEntry) (i j : Fin k) :
    decodeEntries k (a::entries) i j=
      (if a.row=(i.val : ℤ) ∧ a.column=(j.val : ℤ) then a.value else 0)+decodeEntries k entries i j := by
  simp [decodeEntries]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.TripletAppendCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


def tripletIntegerWords (I : ℤ → ℤ) (rowAddress columnAddress : ℤ) (a : SparseEntry) : ℤ → ℤ :=
  Function.update (Function.update I rowAddress a.row) columnAddress a.column

def currentTriplet (st : MachineState) : SparseEntry := ⟨st.scalar.core.ptrs 75,st.scalar.core.ptrs 76,st.scalar.core.regs 10⟩

lemma tripletAppendCode_queryReadOnly : tripletAppendCode.allAtoms queryReadOnly := by
  simp [tripletAppendCode,linearCode,tripletAppendInstructions,sequenceCode,MachineCode.allAtoms,queryReadOnly]

set_option maxHeartbeats 2000000 in
lemma triplet_append_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω tripletAppendCode st 7 out ∧
      out.scalar.core.ptrs 74=st.scalar.core.ptrs 74+1 ∧
      out.scalar.integerMemory=tripletIntegerWords st.scalar.integerMemory
        (st.scalar.core.ptrs 71+st.scalar.core.ptrs 74) (st.scalar.core.ptrs 72+st.scalar.core.ptrs 74) (currentTriplet st) ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (st.scalar.core.ptrs 73+st.scalar.core.ptrs 74) (st.scalar.core.regs 10) ∧
      out.scalar.core.regs=st.scalar.core.regs ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+7 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let out := linearRun m g ω tripletAppendInstructions st
  obtain ⟨e,hw,hH⟩ := linear_execute m g ω tripletAppendInstructions
    (by simp [tripletAppendInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨out,e,?_,?_,?_,?_,e.query_frame tripletAppendCode_queryReadOnly,hw,?_,hH⟩
  all_goals
    simp [out,linearRun,tripletAppendInstructions,tripletIntegerWords,currentTriplet,atomState,machineStep,pcSet,
      LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EntriesStoredAppend

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 1000000 in
lemma entriesStored_append (st out : LocalPush.State) (r : SolveRegisters) (entries : List SparseEntry)
    (a : SparseEntry) (capacity : ℕ) (hcap : entries.length < capacity)
    (hsep : Disjoint (arrayCells (st.core.ptrs r.rows) capacity) (arrayCells (st.core.ptrs r.columns) capacity))
    (h : EntriesStored st r entries)
    (hr : out.core.ptrs r.rows=st.core.ptrs r.rows)
    (hc : out.core.ptrs r.columns=st.core.ptrs r.columns)
    (hv : out.core.ptrs r.values=st.core.ptrs r.values)
    (hI : out.integerMemory=tripletIntegerWords st.integerMemory
      (st.core.ptrs r.rows+(entries.length : ℤ)) (st.core.ptrs r.columns+(entries.length : ℤ)) a)
    (hR : out.core.mem=Function.update st.core.mem (st.core.ptrs r.values+(entries.length : ℤ)) a.value) :
    EntriesStored out r (entries++[a]) := by
  have hcross (i j : ℕ) (hi : i < capacity) (hj : j < capacity) :
      st.core.ptrs r.rows+(i : ℤ) ≠ st.core.ptrs r.columns+(j : ℤ) := by
    intro heq
    exact Finset.disjoint_left.mp hsep ((mem_arrayCells _ _ _).mpr ⟨i,hi,rfl⟩)
      ((mem_arrayCells _ _ _).mpr ⟨j,hj,heq⟩)
  intro i hi
  rw [hr,hc,hv,hI,hR]
  by_cases hil : i < entries.length
  · have hri : st.core.ptrs r.rows+(i : ℤ) ≠ st.core.ptrs r.rows+(entries.length : ℤ) := by omega
    have hci : st.core.ptrs r.columns+(i : ℤ) ≠ st.core.ptrs r.columns+(entries.length : ℤ) := by omega
    have hvi : st.core.ptrs r.values+(i : ℤ) ≠ st.core.ptrs r.values+(entries.length : ℤ) := by omega
    have hrc := hcross i entries.length (by omega) hcap
    have hcr := (hcross entries.length i hcap (by omega)).symm
    simp only [tripletIntegerWords,Function.update_of_ne hri,Function.update_of_ne hci,
      Function.update_of_ne hvi,Function.update_of_ne hrc,Function.update_of_ne hcr]
    simpa only [List.getElem_append_left hil] using h i hil
  · have he : i=entries.length := by simp only [List.length_append,List.length_singleton] at hi; omega
    subst i
    have hrc := hcross entries.length entries.length hcap hcap
    simp [tripletIntegerWords,Function.update_of_ne hrc]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolveBufferAllocation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

structure SolveBufferLayout (st : LocalPush.State) (base : ℤ) (dimension capacity : ℕ) : Prop where
  rows : st.core.ptrs 71=base
  columns : st.core.ptrs 72=base+(capacity : ℤ)
  values : st.core.ptrs 73=base+2*(capacity : ℤ)
  rhs : st.core.ptrs 78=base+3*(capacity : ℤ)
  answer : st.core.ptrs 79=base+3*(capacity : ℤ)+(dimension : ℤ)
  free : st.core.ptrs 20=base+3*(capacity : ℤ)+2*(dimension : ℤ)
  dimensionPointer : st.core.ptrs 77=(dimension : ℤ)
  capacityPointer : st.core.ptrs 82=(capacity : ℤ)

set_option maxHeartbeats 1500000 in
lemma solve_buffer_allocation_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base : ℤ) (dimension capacity : ℕ)
    (hb : st.scalar.core.ptrs 20=base) (hd : st.scalar.core.ptrs 77=(dimension : ℤ))
    (hc : st.scalar.core.ptrs 82=(capacity : ℤ)) :
    ∃ out, MachineEval m g ω solveBufferRoutine.code st 11 out ∧
      SolveBufferLayout out.scalar base dimension capacity ∧ out.scalar.core.ptrs 74=0 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+11 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨out,e,hp,hI,hR,hW,hO,hH⟩ := solveBufferRoutine.execute m g ω st hh
  refine ⟨out,e,?_,?_,hI,hR,hW,hO,hH⟩
  · constructor
    all_goals rw [hp]; simp [solveBufferRoutine,PointerRoutine.sequence,PointerRoutine.run,
      PointerOp.update,PointerOp.destination,PointerOp.result,hb,hd,hc] <;> ring
  · rw [hp]
    simp [solveBufferRoutine,PointerRoutine.sequence,PointerRoutine.run,
      PointerOp.update,PointerOp.destination,PointerOp.result]

lemma buffer_rows_columns_disjoint (base : ℤ) (capacity : ℕ) :
    Disjoint (arrayCells base capacity) (arrayCells (base+(capacity : ℤ)) capacity) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨i,hi,he⟩ := (mem_arrayCells _ _ _).mp hz
  obtain ⟨j,hj,he'⟩ := (mem_arrayCells _ _ _).mp hz'
  omega

lemma SolveBufferLayout.rows_columns_disjoint {st : LocalPush.State} {base : ℤ} {dimension capacity : ℕ}
    (h : SolveBufferLayout st base dimension capacity) :
    Disjoint (arrayCells (st.core.ptrs 71) capacity) (arrayCells (st.core.ptrs 72) capacity) := by
  rw [h.rows,h.columns]
  exact buffer_rows_columns_disjoint base capacity

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SparseAssemblyState

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def solveBufferRegisters : Finset ℕ := {71,72,73,78,79,20,77,82}

lemma SolveBufferLayout.frame {st out : LocalPush.State} {base : ℤ} {dimension capacity : ℕ}
    (h : SolveBufferLayout st base dimension capacity)
    (hp : ∀ r ∈ solveBufferRegisters, out.core.ptrs r=st.core.ptrs r) :
    SolveBufferLayout out base dimension capacity := by
  constructor
  · exact (hp 71 (by decide)).trans h.rows
  · exact (hp 72 (by decide)).trans h.columns
  · exact (hp 73 (by decide)).trans h.values
  · exact (hp 78 (by decide)).trans h.rhs
  · exact (hp 79 (by decide)).trans h.answer
  · exact (hp 20 (by decide)).trans h.free
  · exact (hp 77 (by decide)).trans h.dimensionPointer
  · exact (hp 82 (by decide)).trans h.capacityPointer

lemma MachineEval.solve_buffer_frame {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {code : MachineCode} {st out : MachineState} {u : ℕ} (e : MachineEval m g ω code st u out)
    {base : ℤ} {dimension capacity : ℕ} (h : SolveBufferLayout st.scalar base dimension capacity)
    (hp : Disjoint solveBufferRegisters code.pointerTargets) : SolveBufferLayout out.scalar base dimension capacity := by
  apply h.frame
  intro r hr
  exact e.pointer_frame r (by intro ht; exact Finset.disjoint_left.mp hp hr ht)

lemma EntriesStored.readOnly {st out : LocalPush.State} {r : SolveRegisters} {entries : List SparseEntry}
    (h : EntriesStored st r entries) (hI : out.integerMemory=st.integerMemory) (hR : out.core.mem=st.core.mem)
    (hr : out.core.ptrs r.rows=st.core.ptrs r.rows) (hc : out.core.ptrs r.columns=st.core.ptrs r.columns)
    (hv : out.core.ptrs r.values=st.core.ptrs r.values) : EntriesStored out r entries := by
  intro i hi
  rw [hr,hc,hv,hI,hR]
  exact h i hi

structure SparseAssemblyState (st : MachineState) (base : ℤ) (dimension capacity : ℕ) (entries : List SparseEntry) : Prop where
  layout : SolveBufferLayout st.scalar base dimension capacity
  contents : EntriesStored st.scalar preparedSolveRegisters entries
  count : st.scalar.core.ptrs 74=(entries.length : ℤ)

lemma SparseAssemblyState.readOnly {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {code : MachineCode} {st out : MachineState} {u : ℕ} (e : MachineEval m g ω code st u out)
    {base : ℤ} {dimension capacity : ℕ} {entries : List SparseEntry}
    (h : SparseAssemblyState st base dimension capacity entries)
    (hProtected : Disjoint (insert 74 solveBufferRegisters) code.pointerTargets)
    (hI : out.scalar.integerMemory=st.scalar.integerMemory) (hR : out.scalar.core.mem=st.scalar.core.mem) :
    SparseAssemblyState out base dimension capacity entries := by
  have hp (r : ℕ) (hr : r ∈ insert 74 solveBufferRegisters) := e.pointer_frame r
    (by intro ht; exact Finset.disjoint_left.mp hProtected hr ht)
  refine ⟨e.solve_buffer_frame h.layout (hProtected.mono_left (Finset.subset_insert _ _)),?_,?_⟩
  · apply h.contents.readOnly hI hR
    · exact hp 71 (by decide)
    · exact hp 72 (by decide)
    · exact hp 73 (by decide)
  · exact (hp 74 (by decide)).trans h.count

lemma tripletIntegerWords_below (I : ℤ → ℤ) (rowAddress columnAddress lower z : ℤ) (a : SparseEntry)
    (hr : lower ≤ rowAddress) (hc : lower ≤ columnAddress) (hz : z < lower) :
    tripletIntegerWords I rowAddress columnAddress a z=I z := by
  simp [tripletIntegerWords,Function.update_of_ne (by omega : z ≠ rowAddress),
    Function.update_of_ne (by omega : z ≠ columnAddress)]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrincipalSolves

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma principal_signs {n : ℕ} (g : InputGraph n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (T : Finset (Fin n))
    (hT : ∀ v ∈ T, 0 < g.graph.degree v) :
    let A := (LocalPush.Lα g.graph α).submatrix (fun v : T => v.val) (fun v : T => v.val)
    (∀ i j, i ≠ j → A i j ≤ 0) ∧ (∀ i, 0 < ∑ j, A i j) := by
  classical
  let H := g.graph.induce (↑T : Set (Fin n))
  letI : DecidableRel H.Adj := Classical.decRel _
  let A := (LocalPush.Lα g.graph α).submatrix (fun v : T => v.val) (fun v : T => v.val)
  have hdegree (i : T) : H.degree i ≤ g.graph.degree i.val := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    apply Fintype.card_le_of_injective
      (fun u : H.neighborSet i => (⟨u.val.val, u.property⟩ : g.graph.neighborSet i.val))
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : g.graph.neighborSet i.val => w.val) h
  have hA : A = Matrix.diagonal (fun i : T => LocalPush.deg g.graph i.val) -
      (1-α) • H.adjMatrix ℝ := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [A, LocalPush.Lα, LocalPush.degM, LocalPush.adjM, Matrix.submatrix_apply]
    · have hij' : i.val ≠ j.val := fun he => hij (Subtype.ext he)
      simp [A, LocalPush.Lα, LocalPush.degM, LocalPush.adjM,
        Matrix.submatrix_apply, Matrix.diagonal_apply_ne _ hij', Matrix.diagonal_apply_ne _ hij,
        SimpleGraph.adjMatrix_apply]
      simp only [H, SimpleGraph.induce_adj]
  constructor
  · intro i j hij
    have hij' : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    simp only [A, Matrix.submatrix_apply, LocalPush.Lα, Matrix.sub_apply,
      LocalPush.degM, Matrix.diagonal_apply_ne _ hij', LocalPush.adjM,
      Matrix.smul_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply]
    split <;> linarith [hα.2]
  · intro i
    have hr : (∑ j, A i j) = LocalPush.deg g.graph i.val - (1-α) * (H.degree i : ℝ) := by
      calc
        _ = (A *ᵥ (fun _ => (1 : ℝ))) i := by simp [Matrix.mulVec, dotProduct]
        _ = _ := by
          rw [hA, Matrix.sub_mulVec, Matrix.smul_mulVec]
          simp [Matrix.mulVec_diagonal, SimpleGraph.adjMatrix_mulVec_apply]
    rw [hr]
    have hd : (0 : ℝ) < LocalPush.deg g.graph i.val := by
      unfold LocalPush.deg
      exact_mod_cast hT i.val i.property
    have hd' : (H.degree i : ℝ) ≤ LocalPush.deg g.graph i.val := by
      unfold LocalPush.deg
      exact_mod_cast hdegree i
    have hh := mul_le_mul_of_nonneg_left hd' (sub_nonneg.mpr hα.2.le)
    nlinarith [mul_pos hα.1 hd]

lemma symm_rows_sdd {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hSymm : A.IsSymm)
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0) (hRow : ∀ i, 0 < ∑ j, A i j) :
    LocalPush.IsSDD A := by
  refine ⟨hSymm, ?_⟩
  intro i
  have he : ∑ j ∈ univ.erase i, |A i j| = -(∑ j ∈ univ.erase i, A i j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact abs_of_nonpos (hOff i j (Ne.symm (Finset.mem_erase.mp hj).1))
  rw [he, Finset.sum_erase_eq_sub (mem_univ i)]
  linarith [hRow i]

lemma principal_posDef {n : ℕ} (g : InputGraph n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (T : Finset (Fin n))
    (hT : ∀ v ∈ T, 0 < g.graph.degree v) :
    ((LocalPush.Lα g.graph α).submatrix (fun v : T => v.val) (fun v : T => v.val)).PosDef := by
  classical
  have he : (LocalPush.Lα g.graph α).submatrix (fun v : T => v.val) (fun v : T => v.val) =
      Matrix.diagonal (fun v : T => α * LocalPush.deg g.graph v.val) +
        (1-α) • ((g.graph.lapMatrix ℝ).submatrix (fun v : T => v.val) (fun v : T => v.val)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LocalPush.Lα, LocalPush.degM, LocalPush.adjM, SimpleGraph.lapMatrix, SimpleGraph.degMatrix, LocalPush.deg]
      ring
    · have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp [LocalPush.Lα, LocalPush.degM, LocalPush.adjM, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij']
  rw [he]
  apply Matrix.PosDef.add_posSemidef
  · apply Matrix.PosDef.diagonal
    intro i
    apply mul_pos hα.1
    unfold LocalPush.deg
    exact_mod_cast hT i.val i.property
  · exact ((g.graph.posSemidef_lapMatrix ℝ).submatrix _).smul (sub_nonneg.mpr hα.2.le)

lemma principal_SDDM {n : ℕ} (g : InputGraph n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (T : Finset (Fin n))
    (hT : ∀ v ∈ T, 0 < g.graph.degree v) :
    let A := (LocalPush.Lα g.graph α).submatrix (fun v : T => v.val) (fun v : T => v.val)
    A.PosDef ∧ LocalPush.IsSDD A ∧ (∀ i j, i ≠ j → A i j ≤ 0) := by
  have hh := principal_signs g α hα T hT
  refine ⟨principal_posDef g α hα T hT, ?_, hh.1⟩
  apply symm_rows_sdd _ _ hh.1 hh.2
  apply Matrix.IsSymm.submatrix
  exact (Matrix.isSymm_diagonal _).sub ((g.graph.isSymm_adjMatrix).smul (1-α))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndexedPrincipalSDDM

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma indexed_principal_SDDM {n k : ℕ} (g : InputGraph n) (α : ℝ)
    (hα : 0<α ∧ α<1) (e : Fin k → Fin n) (he : Function.Injective e)
    (hd : ∀ i, 0<g.graph.degree (e i)) :
    SDDM ((LocalPush.Lα g.graph α).submatrix e e) := by
  classical
  let T : Finset (Fin n) := Finset.univ.image e
  let f : Fin k → T := fun i => ⟨e i,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨?_,?_⟩
    · intro i j hij
      exact he (congrArg Subtype.val hij)
    · intro v
      obtain ⟨i,hi,hiv⟩ := Finset.mem_image.mp v.property
      refine ⟨i,?_⟩
      exact Subtype.ext hiv
  let E : Fin k ≃ T := Equiv.ofBijective f hf
  have hT : ∀ v ∈ T, 0<g.graph.degree v := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact hd i
  let A : Matrix (Fin k) (Fin k) ℝ := (LocalPush.Lα g.graph α).submatrix e e
  let B : Matrix T T ℝ := (LocalPush.Lα g.graph α).submatrix Subtype.val Subtype.val
  have hAB : A=B.submatrix E E := rfl
  have hB := principal_SDDM g α hα T hT
  have hSigns := principal_signs g α hα T hT
  have hPos : A.PosDef := by
    rw [hAB]
    exact hB.1.submatrix E.injective
  have hOff : ∀ i j, i ≠ j → A i j ≤ 0 := by
    intro i j hij
    change B (E i) (E j) ≤ 0
    exact hSigns.1 (E i) (E j) (fun heq => hij (E.injective heq))
  have hRow : ∀ i, 0<∑ j, A i j := by
    intro i
    change 0<∑ j, B (E i) (E j)
    rw [E.sum_comp]
    exact hSigns.2 (E i)
  refine ⟨hPos,symm_rows_sdd A ?_ hOff hRow,hOff⟩
  rw [hAB]
  exact hB.2.1.1.submatrix E

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndexedSolveAgreement

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma indexed_solveOn_eq {n k : ℕ} (g : InputGraph n) (α : ℝ)
    (e : Fin k → Fin n) (he : Function.Injective e) (b : Fin n → ℝ) (i : Fin k) :
    (((LocalPush.Lα g.graph α).submatrix e e)⁻¹ *ᵥ (fun j => b (e j))) i=
      solveOn g α (Finset.univ.image e) b (e i) := by
  classical
  let T : Finset (Fin n) := Finset.univ.image e
  let f : Fin k → T := fun j => ⟨e j,Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨?_,?_⟩
    · intro j j' h
      exact he (congrArg Subtype.val h)
    · intro v
      obtain ⟨j,hj,hv⟩ := Finset.mem_image.mp v.property
      exact ⟨j,Subtype.ext hv⟩
  let E : Fin k ≃ T := Equiv.ofBijective f hf
  let B : Matrix T T ℝ := (LocalPush.Lα g.graph α).submatrix Subtype.val Subtype.val
  have hA : (LocalPush.Lα g.graph α).submatrix e e=B.submatrix E E := rfl
  rw [hA,Matrix.inv_submatrix_equiv]
  calc
    ((B⁻¹.submatrix E E) *ᵥ (fun j => b (e j))) i=
        (B⁻¹ *ᵥ (fun j : T => b j.val)) (E i) := by
      change (∑ j, B⁻¹ (E i) (E j)*b (E j).val)=∑ j : T, B⁻¹ (E i) j*b j.val
      exact E.sum_comp (fun j : T => B⁻¹ (E i) j*b j.val)
    _ = solveOn g α T b (e i) := by
      change (B⁻¹ *ᵥ (fun j : T => b j.val)) (E i)=solveOn g α T b (E i).val
      simp only [solveOn,dif_pos (E i).property]
      rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrincipalEntries

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma enumerationIndex_eq_some {n k : ℕ} (e : Fin k → Fin n) (he : Function.Injective e)
    (v : Fin n) (j : Fin k) : enumerationIndex e v=some j ↔ e j=v := by
  unfold enumerationIndex
  split_ifs with h
  · constructor
    · intro heq
      have heq' : Classical.choose h=j := Option.some.inj heq
      rw [←heq']
      exact Classical.choose_spec h
    · intro hj
      have heq : Classical.choose h=j := he ((Classical.choose_spec h).trans hj.symm)
      simp [heq]
  · simp only [reduceCtorEq,false_iff]
    intro hj
    exact h ⟨j,hj⟩

lemma principalRowEntries_length_le {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) (i : Fin k) :
    (principalRowEntries g α e i).length ≤ (g.neighbors (e i)).length+1 := by
  simp only [principalRowEntries,List.length_cons]
  have h := List.length_filterMap_le (f:=fun v => (enumerationIndex e v).map fun j => (⟨i.val,j.val,α-1⟩ : SparseEntry)) (l:=g.neighbors (e i))
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndexLookupAgreement

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def storedEnumerationIndex {n : ℕ} (I : ℤ → ℤ) (width : ℕ) (epoch : ℤ) (v : Fin n) : Option ℤ :=
  if I (vertexRecordAddress width v.val 7)=epoch then some (I (vertexRecordAddress width v.val 8)-1) else none

lemma storedEnumerationIndex_agrees {n k : ℕ} (I : ℤ → ℤ) (width : ℕ) (epoch : ℤ)
    (e : Fin k → Fin n) (he : Function.Injective e) (v : Fin n)
    (h : IndexPrefix I width epoch e k) :
    storedEnumerationIndex I width epoch v=(enumerationIndex e v).map (fun i => (i.val : ℤ)) := by
  cases heq : enumerationIndex e v with
  | none =>
    have ht : I (vertexRecordAddress width v.val 7) ≠ epoch := by
      intro ht
      obtain ⟨j,hj,hjv⟩ := (h.2.1 v).mp ht
      have hLookup := (enumerationIndex_eq_some e he v j).mpr hjv
      rw [heq] at hLookup
      contradiction
    simp [storedEnumerationIndex,ht]
  | some j =>
    have hjv := (enumerationIndex_eq_some e he v j).mp heq
    have ht := (h.2.1 v).mpr ⟨j,j.isLt,hjv⟩
    have hi : I (vertexRecordAddress width v.val 8)=(j.val : ℤ)+1 := by
      rw [←hjv]
      exact h.2.2 j j.isLt
    simp [storedEnumerationIndex,ht,hi]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndexLookupCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma indexLookupCode_queryReadOnly : indexLookupCode.allAtoms queryReadOnly := by
  simp [indexLookupCode,indexLookupPresentCode,MachineCode.allAtoms,vertexFieldReadCode_queryReadOnly,coreCode,queryReadOnly]

set_option maxHeartbeats 1000000 in
lemma index_lookup_present_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width vertex : ℕ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(vertex : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) :
    ∃ out, MachineEval m g ω indexLookupPresentCode st (4*width+11) out ∧
      out.scalar.core.ptrs 68=1 ∧
      out.scalar.core.ptrs 76=st.scalar.integerMemory (vertexRecordAddress width vertex 8)-1 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+(4*width+11 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨mid,em,hm76,hmI,hmR,hmQ,hmW,hmO,hmH⟩ := vertex_field_read_exec m g ω st hh width vertex 8 76 hz hv hw
  let A := payUnit (pointerWrite mid 76 (st.scalar.integerMemory (vertexRecordAddress width vertex 8)-1))
  let out := payUnit (pointerWrite A 68 1)
  have ea : MachineEval m g ω (coreCode (.pdec 76)) mid 1 A := by
    simpa only [A,coreCode,hm76] using pdec_eval m g ω mid 76 hmH
  have ah : A.scalar.halted=false := hmH
  have eo : MachineEval m g ω (coreCode (.pset 68 1)) A 1 out := pset_eval m g ω A 68 1 ah
  refine ⟨out,?_,by simp [out,payUnit,pcSet,pointerWrite],?_,hmI,hmR,?_,hmO,hmH⟩
  · have e := MachineEval.seq em (MachineEval.seq ea eo)
    convert e using 1 <;> (first | rfl | omega)
  · simp [out,A,payUnit,pcSet,pointerWrite]
  · change mid.work+1+1= _
    rw [hmW]
    push_cast
    ring

set_option maxHeartbeats 1800000 in
lemma index_lookup_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width : ℕ) (v : Fin n) (epoch : ℤ)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hE : st.scalar.core.ptrs 53=epoch)
    (hbound : st.scalar.integerMemory (vertexRecordAddress width v.val 7) ≤ epoch) :
    ∃ steps out, MachineEval m g ω indexLookupCode st steps out ∧ steps ≤ 8*width+22 ∧
      (out.scalar.core.ptrs 68=0 ∨ out.scalar.core.ptrs 68=1) ∧
      (if out.scalar.core.ptrs 68=0 then none else some (out.scalar.core.ptrs 76))=
        storedEnumerationIndex st.scalar.integerMemory width epoch v ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let pre := payUnit (pointerWrite st 68 0)
  have ep : MachineEval m g ω (coreCode (.pset 68 0)) st 1 pre := pset_eval m g ω st 68 0 hh
  have preH : pre.scalar.halted=false := hh
  have pre0 : pre.scalar.core.ptrs 0=0 := by simpa [pre,payUnit,pcSet,pointerWrite] using hz
  have pre40 : pre.scalar.core.ptrs 40=(v.val : ℤ) := by simpa [pre,payUnit,pcSet,pointerWrite] using hv
  have pre41 : pre.scalar.core.ptrs 41=(width : ℤ) := by simpa [pre,payUnit,pcSet,pointerWrite] using hw
  obtain ⟨mid,em,hm65,hmI,hmR,hmQ,hmW,hmO,hmH⟩ := vertex_field_read_exec m g ω pre preH width v.val 7 65 pre0 pre40 pre41
  have hm53 : mid.scalar.core.ptrs 53=epoch := (em.pointer_frame 53 (by decide)).trans (by simpa [pre,payUnit,pcSet,pointerWrite] using hE)
  have hm0 := (em.pointer_frame 0 (by decide)).trans pre0
  have hm40 := (em.pointer_frame 40 (by decide)).trans pre40
  have hm41 := (em.pointer_frame 41 (by decide)).trans pre41
  have hm68 : mid.scalar.core.ptrs 68=0 := (em.pointer_frame 68 (by decide)).trans (by simp [pre,payUnit,pcSet,pointerWrite])
  change mid.scalar.core.ptrs 65=st.scalar.integerMemory (vertexRecordAddress width v.val 7) at hm65
  by_cases ht : st.scalar.integerMemory (vertexRecordAddress width v.val 7)=epoch
  · obtain ⟨out,el,ho68,ho76,hoI,hoR,hoW,hoO,hoH⟩ := index_lookup_present_exec m g ω (payUnit mid) hmH width v.val hm0 hm40 hm41
    have eb := MachineEval.pointerLe (r:=53) (s:=65) (b:=.skip) hmH (by rw [hm53,hm65,ht]) el
    have ee := MachineEval.seq ep (MachineEval.seq em eb)
    refine ⟨_,out,ee,by omega,Or.inr ho68,?_,hoI.trans hmI,hoR.trans hmR,
      ee.query_frame indexLookupCode_queryReadOnly,?_,hoO.trans hmO,hoH⟩
    · rw [ho68]
      change (if (1 : ℤ)=0 then none else some (out.scalar.core.ptrs 76))= _
      simp only [one_ne_zero,if_false]
      rw [ho76]
      change some (mid.scalar.integerMemory (vertexRecordAddress width v.val 8)-1)= _
      rw [hmI]
      simp [storedEnumerationIndex,pre,payUnit,pcSet,pointerWrite,ht]
    · rw [hoW,payUnit_work,hmW]
      change st.work+1+(4*width+9 : ℕ)+1+(4*width+11 : ℕ)= _
      push_cast
      ring
  · have eb : MachineEval m g ω (.branchPointer 53 65 indexLookupPresentCode .skip) mid 2 (payUnit (payUnit mid)) := by
      have e := MachineEval.pointerGt (m:=m) (g:=g) (ω:=ω) (r:=53) (s:=65) (a:=indexLookupPresentCode) hmH
        (by rw [hm53,hm65]; omega) (MachineEval.skip (payUnit mid))
      simpa using e
    have ee := MachineEval.seq ep (MachineEval.seq em eb)
    refine ⟨_,payUnit (payUnit mid),ee,by omega,Or.inl hm68,?_,hmI,hmR,
      ee.query_frame indexLookupCode_queryReadOnly,?_,hmO,hmH⟩
    · change (if mid.scalar.core.ptrs 68=0 then none else some (mid.scalar.core.ptrs 76))= _
      simp [hm68,storedEnumerationIndex,ht]
    · change mid.work+1+1= _
      rw [hmW]
      change st.work+1+(4*width+9 : ℕ)+1+1= _
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AssemblyTransport

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma SparseAssemblyState.pay {st : MachineState} {base : ℤ} {dimension capacity : ℕ} {entries : List SparseEntry}
    (h : SparseAssemblyState st base dimension capacity entries) :
    SparseAssemblyState (payUnit st) base dimension capacity entries :=
  ⟨h.layout.frame (by intros; rfl),h.contents,h.count⟩

lemma IndexPrefix.frame {n k : ℕ} {I J : ℤ → ℤ} {width : ℕ} {epoch : ℤ} {e : Fin k → Fin n} {upto : ℕ}
    (h : IndexPrefix I width epoch e upto)
    (ht : ∀ v : Fin n, J (vertexRecordAddress width v.val 7)=I (vertexRecordAddress width v.val 7))
    (hi : ∀ v : Fin n, J (vertexRecordAddress width v.val 8)=I (vertexRecordAddress width v.val 8)) :
    IndexPrefix J width epoch e upto := by
  refine ⟨?_,?_,?_⟩
  · intro v; rw [ht]; exact h.1 v
  · intro v; rw [ht]; exact h.2.1 v
  · intro j hj; rw [hi]; exact h.2.2 j hj

lemma indexLookupCode_registerReadOnly : indexLookupCode.allAtoms registerReadOnly := by
  simp [indexLookupCode,indexLookupPresentCode,vertexFieldReadCode,vertexIntegerLoadCode,
    MachineCode.allAtoms,coreCode,registerReadOnly,vertexAddressCode_registerReadOnly]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.TripletAppendAssembly

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 1200000 in
lemma triplet_append_assembly_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base : ℤ) (dimension capacity : ℕ)
    (entries : List SparseEntry) (h : SparseAssemblyState st base dimension capacity entries)
    (hcap : entries.length < capacity) :
    ∃ out, MachineEval m g ω tripletAppendCode st 7 out ∧
      SparseAssemblyState out base dimension capacity (entries++[currentTriplet st]) ∧
      (∀ z, z < base → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ z, z < base → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.core.regs=st.scalar.core.regs ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+7 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨out,e,h74,hI,hR,hRegs,hQ,hW,hO,hH⟩ := triplet_append_exec m g ω st hh
  rw [h.count] at hI hR h74
  have hoLayout := e.solve_buffer_frame h.layout (by decide)
  have hoEntries : EntriesStored out.scalar preparedSolveRegisters (entries++[currentTriplet st]) := by
    apply entriesStored_append st.scalar out.scalar preparedSolveRegisters entries (currentTriplet st) capacity hcap
      h.layout.rows_columns_disjoint h.contents
    · exact e.pointer_frame 71 (by decide)
    · exact e.pointer_frame 72 (by decide)
    · exact e.pointer_frame 73 (by decide)
    · exact hI
    · exact hR
  have hoCount : out.scalar.core.ptrs 74=((entries++[currentTriplet st]).length : ℤ) := by
    simpa [List.length_append] using h74
  refine ⟨out,e,⟨hoLayout,hoEntries,hoCount⟩,?_,?_,hRegs,hQ,hW,hO,hH⟩
  · intro z hz
    rw [hI]
    apply tripletIntegerWords_below _ _ _ base z _ _ _ hz
    · rw [h.layout.rows]; omega
    · rw [h.layout.columns]; omega
  · intro z hz
    rw [hR]
    apply Function.update_of_ne
    rw [h.layout.values]
    omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OffDiagonalAppend

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def optionalRowEntry {n k : ℕ} (e : Fin k → Fin n) (v : Fin n) (row : Fin k) (c : ℝ) : List SparseEntry :=
  ((enumerationIndex e v).map fun j => (⟨row.val,j.val,c⟩ : SparseEntry)).toList

lemma offDiagonalEntryCode_queryReadOnly : offDiagonalEntryCode.allAtoms queryReadOnly := by
  simp [offDiagonalEntryCode,MachineCode.allAtoms,indexLookupCode_queryReadOnly,tripletAppendCode_queryReadOnly]

set_option maxHeartbeats 2500000 in
lemma off_diagonal_append_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width capacity : ℕ) (base epoch : ℤ)
    (e : Fin k → Fin n) (he : Function.Injective e) (v : Fin n) (row : Fin k) (c : ℝ)
    (entries : List SparseEntry) (h : SparseAssemblyState st base k capacity entries)
    (hcap : entries.length < capacity) (hbase : 0 ≤ base)
    (hTable : IndexPrefix st.scalar.integerMemory width epoch e k)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hE : st.scalar.core.ptrs 53=epoch)
    (hrow : st.scalar.core.ptrs 75=(row.val : ℤ)) (hc : st.scalar.core.regs 10=c) :
    ∃ steps out, MachineEval m g ω offDiagonalEntryCode st steps out ∧ steps ≤ 8*width+31 ∧
      SparseAssemblyState out base k capacity (entries++optionalRowEntry e v row c) ∧
      IndexPrefix out.scalar.integerMemory width epoch e k ∧
      (∀ z, z < base → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ z, z < base → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨u,mid,el,hu,hFlag,hLookup,hI,hR,hQ,hW,hO,hH⟩ :=
    index_lookup_exec m g ω st hh width v epoch hz hv hw hE (hTable.1 v)
  have hmState : SparseAssemblyState mid base k capacity entries :=
    SparseAssemblyState.readOnly el h (by decide) hI hR
  have hm0 := (el.pointer_frame 0 (by decide)).trans hz
  have hm75 := (el.pointer_frame 75 (by decide)).trans hrow
  have hm10 : mid.scalar.core.regs 10=c := (congrFun (el.register_frame indexLookupCode_registerReadOnly) 10).trans hc
  rw [storedEnumerationIndex_agrees st.scalar.integerMemory width epoch e he v hTable] at hLookup
  cases hIndex : enumerationIndex e v with
  | none =>
    have hm68 : mid.scalar.core.ptrs 68=0 := by
      by_contra hn
      simp only [hIndex,Option.map_none,if_neg hn] at hLookup
      contradiction
    have eb : MachineEval m g ω (.branchPointer 68 0 .skip tripletAppendCode) mid 1 (payUnit mid) := by
      have ee := MachineEval.pointerLe (m:=m) (g:=g) (ω:=ω) (r:=68) (s:=0) (b:=tripletAppendCode) hH
        (by rw [hm68,hm0]) (MachineEval.skip (payUnit mid))
      simpa using ee
    have ee := MachineEval.seq el eb
    have hoState : SparseAssemblyState (payUnit mid) base k capacity (entries++optionalRowEntry e v row c) := by
      simpa only [optionalRowEntry,hIndex,Option.map_none,Option.toList_none,List.append_nil] using hmState.pay
    refine ⟨u+1,payUnit mid,ee,by omega,hoState,?_,?_,?_,ee.query_frame offDiagonalEntryCode_queryReadOnly,
      ?_,hO,hH⟩
    · change IndexPrefix mid.scalar.integerMemory width epoch e k
      rw [hI]; exact hTable
    · intro z hz'; exact congrFun hI z
    · intro z hz'; exact congrFun hR z
    · rw [payUnit_work,hW]
      push_cast
      ring
  | some j =>
    have hm68ne : mid.scalar.core.ptrs 68 ≠ 0 := by
      intro hz'
      simp only [hIndex,Option.map_some,if_pos hz'] at hLookup
      contradiction
    have hm68 : mid.scalar.core.ptrs 68=1 := hFlag.resolve_left hm68ne
    have hm76 : mid.scalar.core.ptrs 76=(j.val : ℤ) := by
      simp only [hIndex,Option.map_some,if_neg hm68ne] at hLookup
      exact Option.some.inj hLookup
    obtain ⟨out,ea,hoState,hoI,hoR,hoRegs,hoQ,hoW,hoO,hoH⟩ :=
      triplet_append_assembly_exec m g ω (payUnit mid) hH base k capacity entries hmState.pay hcap
    have ht : currentTriplet (payUnit mid)=(⟨row.val,j.val,c⟩ : SparseEntry) := by
      simp [currentTriplet,payUnit,pcSet,hm75,hm76,hm10]
    rw [ht] at hoState
    have eb : MachineEval m g ω (.branchPointer 68 0 .skip tripletAppendCode) mid 9 (payUnit out) :=
      MachineEval.pointerGt (r:=68) (s:=0) (a:=.skip) hH (by rw [hm68,hm0]; norm_num) ea
    have ee := MachineEval.seq el eb
    have hoState' : SparseAssemblyState (payUnit out) base k capacity (entries++optionalRowEntry e v row c) := by
      simpa only [optionalRowEntry,hIndex,Option.map_some,Option.toList_some] using hoState.pay
    have hoIBelow : ∀ z, z < base → out.scalar.integerMemory z=st.scalar.integerMemory z :=
      fun z hz' => (hoI z hz').trans (congrFun hI z)
    have hoRBelow : ∀ z, z < base → out.scalar.core.mem z=st.scalar.core.mem z :=
      fun z hz' => (hoR z hz').trans (congrFun hR z)
    refine ⟨u+9,payUnit out,ee,by omega,hoState',?_,hoIBelow,hoRBelow,
      ee.query_frame offDiagonalEntryCode_queryReadOnly,?_,hoO.trans hO,hoH⟩
    · apply hTable.frame
      · intro v'
        exact hoIBelow _ ((vertexRecordAddress_negative _ _ _).trans_le hbase)
      · intro v'
        exact hoIBelow _ ((vertexRecordAddress_negative _ _ _).trans_le hbase)
    · rw [payUnit_work,hoW,payUnit_work,hW]
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NeighborAssemblyBody

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma tripletAppendCode_registerReadOnly : tripletAppendCode.allAtoms registerReadOnly := by
  simp [tripletAppendCode,linearCode,tripletAppendInstructions,sequenceCode,MachineCode.allAtoms,registerReadOnly]

lemma offDiagonalEntryCode_registerReadOnly : offDiagonalEntryCode.allAtoms registerReadOnly := by
  simp [offDiagonalEntryCode,MachineCode.allAtoms,indexLookupCode_registerReadOnly,tripletAppendCode_registerReadOnly]

lemma neighborAssemblyBodyCode_queryReadOnly : neighborAssemblyBodyCode.allAtoms queryReadOnly := by
  simp [neighborAssemblyBodyCode,MachineCode.allAtoms,offDiagonalEntryCode_queryReadOnly,coreCode,queryReadOnly]

lemma neighborAssemblyBodyCode_registerReadOnly : neighborAssemblyBodyCode.allAtoms registerReadOnly := by
  simp [neighborAssemblyBodyCode,MachineCode.allAtoms,offDiagonalEntryCode_registerReadOnly,coreCode,registerReadOnly]

set_option maxHeartbeats 2200000 in
lemma neighbor_assembly_body_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width capacity : ℕ) (base adjacencyBase epoch : ℤ)
    (e : Fin k → Fin n) (he : Function.Injective e) (row : Fin k) (c : ℝ) (i : ℕ)
    (hi : i < (g.neighbors (e row)).length) (entries : List SparseEntry)
    (h : SparseAssemblyState st base k capacity entries) (hcap : entries.length < capacity) (hbase : 0 ≤ base)
    (hTable : IndexPrefix st.scalar.integerMemory width epoch e k)
    (hStored : AdjacencyStored st.scalar.integerMemory adjacencyBase (g.neighbors (e row)) (g.neighbors (e row)).length)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hE : st.scalar.core.ptrs 53=epoch) (hrow : st.scalar.core.ptrs 75=(row.val : ℤ))
    (ha : st.scalar.core.ptrs 61=adjacencyBase) (hindex : st.scalar.core.ptrs 62=(i : ℤ))
    (hc : st.scalar.core.regs 10=c) :
    ∃ steps out, MachineEval m g ω neighborAssemblyBodyCode st steps out ∧ steps ≤ 8*width+34 ∧
      out.scalar.core.ptrs 62=(i+1 : ℕ) ∧
      SparseAssemblyState out base k capacity (entries++optionalRowEntry e (g.neighbors (e row))[i] row c) ∧
      IndexPrefix out.scalar.integerMemory width epoch e k ∧
      (∀ z, z < base → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ z, z < base → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.core.regs 10=c ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let v := (g.neighbors (e row))[i]
  let A := payUnit (pointerWrite st 64 (adjacencyBase+(i : ℤ)))
  let B := payUnit (pointerWrite A 40 (v.val : ℤ))
  have ea : MachineEval m g ω (.atom (.scalar (.pointerAdd 64 61 62))) st 1 A := by
    simpa only [A,ha,hindex] using pointerAdd_eval m g ω st 64 61 62 hh
  have ah : A.scalar.halted=false := hh
  have eb : MachineEval m g ω (.atom (.scalar (.integerLoad 40 64))) A 1 B := by
    have hval : A.scalar.integerMemory (A.scalar.core.ptrs 64)=(v.val : ℤ) := by
      simpa [A,payUnit,pcSet,pointerWrite,v] using hStored i hi hi
    simpa only [B,hval] using integerLoad_eval m g ω A 40 64 ah
  have bh : B.scalar.halted=false := hh
  have ep := MachineEval.seq ea eb
  have hB : SparseAssemblyState B base k capacity entries := SparseAssemblyState.readOnly ep h (by decide) rfl rfl
  have b0 : B.scalar.core.ptrs 0=0 := by simpa [B,A,payUnit,pcSet,pointerWrite] using hz
  have b40 : B.scalar.core.ptrs 40=(v.val : ℤ) := by simp [B,payUnit,pcSet,pointerWrite]
  have b41 : B.scalar.core.ptrs 41=(width : ℤ) := by simpa [B,A,payUnit,pcSet,pointerWrite] using hw
  have b53 : B.scalar.core.ptrs 53=epoch := by simpa [B,A,payUnit,pcSet,pointerWrite] using hE
  have b75 : B.scalar.core.ptrs 75=(row.val : ℤ) := by simpa [B,A,payUnit,pcSet,pointerWrite] using hrow
  obtain ⟨u,mid,ec,hu,hmidState,hmidTable,hmidI,hmidR,hmidQ,hmidW,hmidO,hmidH⟩ :=
    off_diagonal_append_exec m g ω B bh width capacity base epoch e he v row c entries hB hcap hbase hTable
      b0 b40 b41 b53 b75 hc
  have mid62 : mid.scalar.core.ptrs 62=(i : ℤ) :=
    (ec.pointer_frame 62 (by decide)).trans (by simpa [B,A,payUnit,pcSet,pointerWrite] using hindex)
  let out := payUnit (pointerWrite mid 62 (i+1 : ℕ))
  have ed : MachineEval m g ω (coreCode (.pinc 62)) mid 1 out := by
    simpa only [out,coreCode,mid62,Nat.cast_add,Nat.cast_one] using pinc_eval m g ω mid 62 hmidH
  have eRun := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  have hOut : SparseAssemblyState out base k capacity (entries++optionalRowEntry e v row c) :=
    SparseAssemblyState.readOnly ed hmidState (by decide) rfl rfl
  refine ⟨1+(1+(u+1)),out,eRun,by omega,by simp [out,payUnit,pcSet,pointerWrite],hOut,hmidTable,hmidI,hmidR,?_,
    eRun.query_frame neighborAssemblyBodyCode_queryReadOnly,?_,hmidO,hmidH⟩
  · exact (congrFun (eRun.register_frame neighborAssemblyBodyCode_registerReadOnly) 10).trans hc
  · change mid.work+1= _
    rw [hmidW]
    change st.work+1+1+u+1= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NeighborRemainder

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma optionalRowEntry_length {n k : ℕ} (e : Fin k → Fin n) (v : Fin n) (row : Fin k) (c : ℝ) :
    (optionalRowEntry e v row c).length ≤ 1 := by
  cases hi : enumerationIndex e v <;> simp [optionalRowEntry,hi]

def remainingRowEntries {n k : ℕ} (e : Fin k → Fin n) (row : Fin k) (c : ℝ)
    (neighbors : List (Fin n)) (i : ℕ) : List SparseEntry :=
  (neighbors.drop i).flatMap (fun v => optionalRowEntry e v row c)

lemma remainingRowEntries_cons {n k : ℕ} (e : Fin k → Fin n) (row : Fin k) (c : ℝ)
    (neighbors : List (Fin n)) (i : ℕ) (hi : i < neighbors.length) :
    remainingRowEntries e row c neighbors i=optionalRowEntry e neighbors[i] row c++
      remainingRowEntries e row c neighbors (i+1) := by
  unfold remainingRowEntries
  rw [List.drop_eq_getElem_cons hi,List.flatMap_cons]

lemma optionalRowEntries_filterMap {n k : ℕ} (e : Fin k → Fin n) (row : Fin k) (c : ℝ)
    (neighbors : List (Fin n)) :
    neighbors.flatMap (fun v => optionalRowEntry e v row c)=
      neighbors.filterMap (fun v => (enumerationIndex e v).map fun j => (⟨row.val,j.val,c⟩ : SparseEntry)) := by
  induction neighbors with
  | nil => simp
  | cons v vs ih =>
    simp only [optionalRowEntry] at ih
    cases h : enumerationIndex e v <;> simp [List.flatMap_cons,optionalRowEntry,h,ih]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NeighborAssemblyLoop

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 3000000 in
lemma neighbor_assembly_loop_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width capacity : ℕ) (base adjacencyBase epoch : ℤ) (e : Fin k → Fin n) (he : Function.Injective e)
    (row : Fin k) (c : ℝ) (remaining i : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (entries : List SparseEntry) (h : SparseAssemblyState st base k capacity entries)
    (hcap : entries.length+remaining ≤ capacity) (hbase : 0 ≤ base)
    (hTable : IndexPrefix st.scalar.integerMemory width epoch e k)
    (hStored : AdjacencyStored st.scalar.integerMemory adjacencyBase (g.neighbors (e row)) (g.neighbors (e row)).length)
    (hAdjBelow : ∀ j < (g.neighbors (e row)).length, adjacencyBase+(j : ℤ) < base)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hE : st.scalar.core.ptrs 53=epoch) (hrow : st.scalar.core.ptrs 75=(row.val : ℤ))
    (ha : st.scalar.core.ptrs 61=adjacencyBase) (hd : st.scalar.core.ptrs 60=((g.neighbors (e row)).length : ℤ))
    (hindex : st.scalar.core.ptrs 62=(i : ℤ)) (hc : st.scalar.core.regs 10=c)
    (hlen : i+remaining=(g.neighbors (e row)).length) :
    ∃ steps out, MachineEval m g ω neighborAssemblyLoopCode st steps out ∧ steps ≤ remaining*(8*width+36)+1 ∧
      out.scalar.core.ptrs 62=((g.neighbors (e row)).length : ℤ) ∧
      SparseAssemblyState out base k capacity (entries++remainingRowEntries e row c (g.neighbors (e row)) i) ∧
      IndexPrefix out.scalar.integerMemory width epoch e k ∧
      (∀ z, z < base → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ z, z < base → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.core.regs 10=c ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction remaining generalizing st i entries with
  | zero =>
    have hi : i=(g.neighbors (e row)).length := by omega
    have es : MachineEval m g ω neighborAssemblyLoopCode st 1 (payUnit st) :=
      MachineEval.pointerDone (r:=60) (s:=62) (body:=neighborAssemblyBodyCode) hh (by rw [hd,hindex,hi])
    refine ⟨1,payUnit st,es,by simp,by simpa [hi] using hindex,?_,hTable,
      (by intros; rfl),(by intros; rfl),hc,rfl,by simp,rfl,hh⟩
    simpa only [remainingRowEntries,hi,List.drop_length,List.flatMap_nil,List.append_nil] using h.pay
  | succ remaining ih =>
    have hi : i < (g.neighbors (e row)).length := by omega
    obtain ⟨u,mid,eb,hu,hm62,hmState,hmTable,hmI,hmR,hm10,hmQ,hmW,hmO,hmH⟩ :=
      neighbor_assembly_body_exec m g ω (payUnit st) hh width capacity base adjacencyBase epoch e he row c i hi entries
        h.pay (by omega) hbase hTable hStored hz hw hE hrow ha hindex hc
    have hm0 := (eb.pointer_frame 0 (by decide)).trans hz
    have hm41 := (eb.pointer_frame 41 (by decide)).trans hw
    have hm53 := (eb.pointer_frame 53 (by decide)).trans hE
    have hm75 := (eb.pointer_frame 75 (by decide)).trans hrow
    have hm61 := (eb.pointer_frame 61 (by decide)).trans ha
    have hm60 := (eb.pointer_frame 60 (by decide)).trans hd
    have hmStored : AdjacencyStored mid.scalar.integerMemory adjacencyBase (g.neighbors (e row)) (g.neighbors (e row)).length := by
      intro j hj hj'
      rw [hmI _ (hAdjBelow j hj')]
      exact hStored j hj hj'
    have hmCap : (entries++optionalRowEntry e (g.neighbors (e row))[i] row c).length+remaining ≤ capacity := by
      have hLen := optionalRowEntry_length e (g.neighbors (e row))[i] row c
      simp only [List.length_append]
      omega
    obtain ⟨v,out,er,hv,ho62,hoState,hoTable,hoI,hoR,ho10,hoQ,hoW,hoO,hoH⟩ :=
      ih (i+1) (payUnit mid) hmH _ hmState.pay hmCap hmTable hmStored hm0 hm41 hm53 hm75 hm61 hm60 hm62 hm10 (by omega)
    have hList : (entries++optionalRowEntry e (g.neighbors (e row))[i] row c)++
        remainingRowEntries e row c (g.neighbors (e row)) (i+1)=entries++remainingRowEntries e row c (g.neighbors (e row)) i := by
      rw [remainingRowEntries_cons e row c (g.neighbors (e row)) i hi]
      simp [List.append_assoc]
    rw [hList] at hoState
    refine ⟨1+u+1+v,out,?_,by nlinarith,ho62,hoState,hoTable,?_,?_,ho10,hoQ.trans hmQ,?_,hoO.trans hmO,hoH⟩
    · exact MachineEval.pointerNext (r:=60) (s:=62) hh (by rw [hd,hindex]; omega) eb er
    · intro z hz'
      exact (hoI z hz').trans (hmI z hz')
    · intro z hz'
      exact (hoR z hz').trans (hmR z hz')
    · rw [hoW,payUnit_work,hmW,payUnit_work]
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DiagonalAppend

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1500000 in
lemma diagonal_append_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (base : ℤ) (dimension capacity row degree : ℕ)
    (entries : List SparseEntry) (h : SparseAssemblyState st base dimension capacity entries)
    (hcap : entries.length < capacity) (hr : st.scalar.core.ptrs 75=(row : ℤ))
    (hd : st.scalar.core.ptrs 60=(degree : ℤ)) :
    ∃ out, MachineEval m g ω diagonalAppendCode st 9 out ∧
      SparseAssemblyState out base dimension capacity (entries++[⟨row,row,(degree : ℝ)⟩]) ∧
      (∀ z, z < base → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ z, z < base → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+9 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let A := payUnit (pointerWrite st 76 row)
  let B := payUnit (realWrite A 10 degree)
  have ea : MachineEval m g ω (coreCode (.pcopy 76 75)) st 1 A := by
    simpa only [A,coreCode,hr] using pcopy_eval m g ω st 76 75 hh
  have ah : A.scalar.halted=false := hh
  have a60 : A.scalar.core.ptrs 60=(degree : ℤ) := by simpa [A,payUnit,pcSet,pointerWrite] using hd
  have eb : MachineEval m g ω (.atom (.scalar (.pointerReal 10 60))) A 1 B := by
    simpa only [B,a60,Int.cast_natCast] using pointerReal_eval m g ω A 10 60 ah
  have bh : B.scalar.halted=false := hh
  have hAB : SparseAssemblyState B base dimension capacity entries := by
    have e := MachineEval.seq ea eb
    exact h.readOnly e (by decide) rfl rfl
  obtain ⟨out,ec,hoState,hoI,hoR,hoRegs,hoQ,hoW,hoO,hoH⟩ :=
    triplet_append_assembly_exec m g ω B bh base dimension capacity entries hAB hcap
  have ha : currentTriplet B=(⟨row,row,(degree : ℝ)⟩ : SparseEntry) := by
    simp [currentTriplet,B,A,payUnit,pcSet,pointerWrite,realWrite,hr]
  rw [ha] at hoState
  refine ⟨out,MachineEval.seq ea (MachineEval.seq eb ec),hoState,hoI,hoR,?_,?_,hoO,hoH⟩
  · have e := MachineEval.seq ea (MachineEval.seq eb ec)
    exact e.query_frame (by simp [diagonalAppendCode,MachineCode.allAtoms,tripletAppendCode_queryReadOnly,coreCode,queryReadOnly])
  · rw [hoW]
    change st.work+1+1+7= _
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrincipalRowAssembly

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma principalRowAssemblyCode_queryReadOnly : principalRowAssemblyCode.allAtoms queryReadOnly := by
  simp [principalRowAssemblyCode,cacheReadCode,MachineCode.allAtoms,vertexFieldReadCode_queryReadOnly,
    diagonalAppendCode,tripletAppendCode_queryReadOnly,RealOperation.instruction,neighborAssemblyLoopCode,
    neighborAssemblyBodyCode_queryReadOnly,coreCode,queryReadOnly]

set_option maxHeartbeats 3500000 in
lemma principal_row_assembly_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width capacity : ℕ) (base epoch : ℤ)
    (e : Fin k → Fin n) (he : Function.Injective e) (row : Fin k) (α : ℝ)
    (stored : Finset (Fin n)) (entries : List SparseEntry)
    (h : SparseAssemblyState st base k capacity entries)
    (hcap : entries.length+(g.neighbors (e row)).length+1 ≤ capacity)
    (hcache : GraphCache g st.scalar.integerMemory width stored base) (hmem : e row ∈ stored)
    (hTable : IndexPrefix st.scalar.integerMemory width epoch e k)
    (hz : st.scalar.core.ptrs 0=0) (hv : st.scalar.core.ptrs 40=((e row).val : ℤ))
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hE : st.scalar.core.ptrs 53=epoch)
    (hrow : st.scalar.core.ptrs 75=(row.val : ℤ)) (ha : st.scalar.core.regs 12=α-1) (h1 : st.scalar.core.regs 11=1) :
    ∃ steps out, MachineEval m g ω principalRowAssemblyCode st steps out ∧
      steps ≤ ((g.neighbors (e row)).length+1)*(8*width+40) ∧
      SparseAssemblyState out base k capacity (entries++principalRowEntries g α e row) ∧
      IndexPrefix out.scalar.integerMemory width epoch e k ∧
      (∀ z, z < base → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ z, z < base → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let d := (g.neighbors (e row)).length
  let adj := st.scalar.integerMemory (vertexRecordAddress width (e row).val 1)
  have hbase : 0 ≤ base := by have hb := hcache.freeBound; omega
  obtain ⟨read,er,hr60,hr61,hrI,hrR,hrQ,hrW,hrO,hrH⟩ := cache_read_exec m g ω st hh width (e row).val hz hv hw
  rw [hcache.degree (e row) hmem] at hr60
  have hrState : SparseAssemblyState read base k capacity entries := SparseAssemblyState.readOnly er h (by decide) hrI hrR
  have hrRow := (er.pointer_frame 75 (by decide)).trans hrow
  obtain ⟨diag,ed,hdState,hdI,hdR,hdQ,hdW,hdO,hdH⟩ :=
    diagonal_append_exec m g ω read hrH base k capacity row.val d entries hrState (by omega) hrRow hr60
  have diag12 : diag.scalar.core.regs 12=α-1 :=
    (ed.real_register_frame 12 (by decide)).trans ((er.real_register_frame 12 (by decide)).trans ha)
  have diag11 : diag.scalar.core.regs 11=1 :=
    (ed.real_register_frame 11 (by decide)).trans ((er.real_register_frame 11 (by decide)).trans h1)
  let mul := payUnit (realWrite diag 10 (α-1))
  let reset := payUnit (pointerWrite mul 62 0)
  have em : MachineEval m g ω (.atom (RealOperation.mul.instruction 10 12 11)) diag 1 mul := by
    simpa only [mul,diag12,diag11,RealOperation.value,mul_one] using binary_eval m g ω diag .mul 10 12 11 hdH
  have mulH : mul.scalar.halted=false := hdH
  have ez : MachineEval m g ω (coreCode (.pset 62 0)) mul 1 reset := pset_eval m g ω mul 62 0 mulH
  have resetH : reset.scalar.halted=false := hdH
  have ep := MachineEval.seq er (MachineEval.seq ed (MachineEval.seq em ez))
  have resetState : SparseAssemblyState reset base k capacity (entries++[⟨row.val,row.val,(d : ℝ)⟩]) :=
    SparseAssemblyState.readOnly (MachineEval.seq em ez) hdState (by decide) rfl rfl
  have reset0 := (ep.pointer_frame 0 (by decide)).trans hz
  have reset41 := (ep.pointer_frame 41 (by decide)).trans hw
  have reset53 := (ep.pointer_frame 53 (by decide)).trans hE
  have reset75 := (ep.pointer_frame 75 (by decide)).trans hrow
  have reset61 : reset.scalar.core.ptrs 61=adj := by
    exact (ez.pointer_frame 61 (by decide)).trans ((em.pointer_frame 61 (by decide)).trans
      ((ed.pointer_frame 61 (by decide)).trans hr61))
  have reset60 : reset.scalar.core.ptrs 60=(d : ℤ) := by
    exact (ez.pointer_frame 60 (by decide)).trans ((em.pointer_frame 60 (by decide)).trans
      ((ed.pointer_frame 60 (by decide)).trans hr60))
  have reset62 : reset.scalar.core.ptrs 62=0 := by simp [reset,payUnit,pcSet,pointerWrite]
  have reset10 : reset.scalar.core.regs 10=α-1 := by simp [reset,mul,payUnit,pcSet,pointerWrite,realWrite]
  have resetI : ∀ z, z < base → reset.scalar.integerMemory z=st.scalar.integerMemory z :=
    fun z hz' => (hdI z hz').trans (congrFun hrI z)
  have resetR : ∀ z, z < base → reset.scalar.core.mem z=st.scalar.core.mem z :=
    fun z hz' => (hdR z hz').trans (congrFun hrR z)
  have resetTable : IndexPrefix reset.scalar.integerMemory width epoch e k := by
    apply hTable.frame
    · intro v; exact resetI _ ((vertexRecordAddress_negative _ _ _).trans_le hbase)
    · intro v; exact resetI _ ((vertexRecordAddress_negative _ _ _).trans_le hbase)
  have resetAdj : AdjacencyStored reset.scalar.integerMemory adj (g.neighbors (e row)) d := by
    intro i hi hi'
    rw [resetI _ (hcache.belowFree (e row) hmem i hi')]
    exact hcache.adjacency (e row) hmem i hi hi'
  obtain ⟨u,out,el,hu,ho62,hoState,hoTable,hoI,hoR,ho10,hoQ,hoW,hoO,hoH⟩ :=
    neighbor_assembly_loop_exec m g ω width capacity base adj epoch e he row (α-1) d 0 reset resetH
      (entries++[⟨row.val,row.val,(d : ℝ)⟩]) resetState (by simp only [List.length_append,List.length_singleton]; omega)
      hbase resetTable resetAdj (hcache.belowFree (e row) hmem) reset0 reset41 reset53 reset75 reset61 reset60 reset62 reset10 (by omega)
  have hdeg : (d : ℝ)=LocalPush.deg g.graph (e row) := by
    unfold d LocalPush.deg
    rw [compiler_graph_neighbor_degree]
  have hList : (entries++[⟨row.val,row.val,(d : ℝ)⟩])++
      remainingRowEntries e row (α-1) (g.neighbors (e row)) 0=entries++principalRowEntries g α e row := by
    simp [remainingRowEntries,optionalRowEntries_filterMap,principalRowEntries,List.append_assoc,hdeg]
  rw [hList] at hoState
  have eRun := MachineEval.seq er (MachineEval.seq ed (MachineEval.seq em (MachineEval.seq ez el)))
  refine ⟨_,out,eRun,?_,hoState,hoTable,?_,?_,eRun.query_frame principalRowAssemblyCode_queryReadOnly,?_,
    hoO.trans (hdO.trans hrO),hoH⟩
  · change 8*width+18+(9+(1+(1+u))) ≤ (d+1)*(8*width+40)
    nlinarith
  · intro z hz'; exact (hoI z hz').trans (resetI z hz')
  · intro z hz'; exact (hoR z hz').trans (resetR z hz')
  · rw [hoW]
    change diag.work+1+1+u= _
    rw [hdW,hrW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SparseRowDecode

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma list_filterMap_sum {A B : Type} (l : List A) (f : A → Option B) (a : B → ℝ) :
    ((l.filterMap f).map a).sum=(l.map (fun x => (f x).elim 0 a)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => cases he : f x <;> simp [he,ih]

lemma list_nodup_sum_single {A : Type} [DecidableEq A] (l : List A) (hl : l.Nodup) (a : A) (c : ℝ) :
    (l.map (fun v => if v=a then c else 0)).sum=if a ∈ l then c else 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx,hs⟩ := List.nodup_cons.mp hl
    by_cases he : x=a
    · subst x; simp [hx,ih hs]
    · simp [he,Ne.symm he,ih hs]

lemma sparse_index_coefficient {n k : ℕ} (e : Fin k → Fin n) (he : Function.Injective e)
    (v : Fin n) (row i j : Fin k) (c : ℝ) :
    ((enumerationIndex e v).map (fun a => (⟨row.val,a.val,c⟩ : SparseEntry))).elim 0
      (fun a => if a.row=(i.val : ℤ) ∧ a.column=(j.val : ℤ) then a.value else 0)=
        if row=i ∧ v=e j then c else 0 := by
  cases hs : enumerationIndex e v with
  | none =>
    have hv : v ≠ e j := by
      intro hv
      have hh := (enumerationIndex_eq_some e he v j).mpr hv.symm
      rw [hs] at hh
      contradiction
    simp [hv]
  | some a =>
    have hv : e a=v := (enumerationIndex_eq_some e he v a).mp hs
    rw [←hv]
    simp only [Option.map_some,Option.elim_some]
    have hrow : (row.val : ℤ)=(i.val : ℤ) ↔ row=i := by simp [Fin.ext_iff]
    have hcol : (a.val : ℤ)=(j.val : ℤ) ↔ a=j := by simp [Fin.ext_iff]
    simp only [hrow,hcol,he.eq_iff]

set_option maxHeartbeats 1200000 in
lemma principal_row_decode {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n)
    (he : Function.Injective e) (row i j : Fin k) :
    decodeEntries k (principalRowEntries g α e row) i j=
      if row=i then (LocalPush.Lα g.graph α) (e i) (e j) else 0 := by
  rw [principalRowEntries,decodeEntries_cons]
  unfold decodeEntries
  rw [list_filterMap_sum]
  have hmaps :
      (g.neighbors (e row)).map (fun x =>
        ((enumerationIndex e x).map (fun a => (⟨row.val,a.val,α-1⟩ : SparseEntry))).elim 0
          (fun a => if a.row=(i.val : ℤ) ∧ a.column=(j.val : ℤ) then a.value else 0))=
      (g.neighbors (e row)).map (fun v => if row=i ∧ v=e j then α-1 else 0) := by
    apply List.map_congr_left
    intro v hv
    exact sparse_index_coefficient e he v row i j (α-1)
  rw [hmaps]
  by_cases hrow : row=i
  · subst row
    simp only [and_true,true_and,ite_true]
    rw [list_nodup_sum_single _ (g.nodup (e i)) (e j) (α-1)]
    have hij : e i=e j ↔ i=j := he.eq_iff
    have hrowi : (i.val : ℤ)=(i.val : ℤ) := rfl
    have hcol : (i.val : ℤ)=(j.val : ℤ) ↔ i=j := by simp [Fin.ext_iff]
    simp only [g.correct]
    by_cases heq : i=j
    · subst j
      simp [LocalPush.Lα,LocalPush.degM,LocalPush.adjM]
    · have heq' : e i ≠ e j := fun hh => heq (he hh)
      simp only [hcol,heq,and_false,if_false]
      simp [LocalPush.Lα,LocalPush.degM,LocalPush.adjM,Matrix.diagonal_apply_ne _ heq']
      split_ifs <;> ring
  · have hrow' : (row.val : ℤ) ≠ (i.val : ℤ) := by intro hh; apply hrow; exact Fin.ext (by exact_mod_cast hh)
    simp [hrow,hrow']

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrincipalEntriesDecode

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma decodeEntries_flatMap {A : Type} (k : ℕ) (l : List A) (f : A → List SparseEntry) (i j : Fin k) :
    decodeEntries k (l.flatMap f) i j=(l.map (fun a => decodeEntries k (f a) i j)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons,decodeEntries_append,ih]

lemma principal_entries_decode {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n)
    (he : Function.Injective e) : decodeEntries k (principalEntries g α e)=(LocalPush.Lα g.graph α).submatrix e e := by
  ext i j
  unfold principalEntries
  rw [decodeEntries_flatMap,←List.ofFn_eq_map,List.sum_ofFn]
  simp only [principal_row_decode g α e he]
  simp

lemma flatMap_length_sum {A B : Type} (l : List A) (f : A → List B) :
    (l.flatMap f).length=(l.map (fun a => (f a).length)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons,ih]

lemma principal_entries_length_le {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) :
    (principalEntries g α e).length ≤ k+∑ i : Fin k, (g.neighbors (e i)).length := by
  unfold principalEntries
  rw [flatMap_length_sum,←List.ofFn_eq_map,List.sum_ofFn]
  calc
    ∑ i : Fin k, (principalRowEntries g α e i).length ≤
        ∑ i : Fin k, ((g.neighbors (e i)).length+1) := Finset.sum_le_sum (fun i _ => principalRowEntries_length_le g α e i)
    _ = k+∑ i : Fin k, (g.neighbors (e i)).length := by simp [Finset.sum_add_distrib,Nat.add_comm]

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

lemma remainingRowsBudget_cons {n k : ℕ} (g : InputGraph n) (e : Fin k → Fin n) (i : ℕ) (hi : i < k) :
    remainingRowsBudget g e i=(g.neighbors (e ⟨i,hi⟩)).length+1+remainingRowsBudget g e (i+1) := by
  unfold remainingRowsBudget
  rw [List.drop_eq_getElem_cons (by simpa using hi)]
  simp

lemma remainingPrincipalEntries_cons {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n)
    (i : ℕ) (hi : i < k) : remainingPrincipalEntries g α e i=
      principalRowEntries g α e ⟨i,hi⟩++remainingPrincipalEntries g α e (i+1) := by
  unfold remainingPrincipalEntries
  rw [List.drop_eq_getElem_cons (by simpa using hi)]
  simp

@[simp] lemma remainingRowsBudget_done {n k : ℕ} (g : InputGraph n) (e : Fin k → Fin n) : remainingRowsBudget g e k=0 := by
  have hd : (List.finRange k).drop k=[] := by simpa only [List.length_finRange] using (List.drop_length (l:=List.finRange k))
  simp only [remainingRowsBudget,hd,List.map_nil,List.sum_nil]

@[simp] lemma remainingPrincipalEntries_done {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) :
    remainingPrincipalEntries g α e k=[] := by
  have hd : (List.finRange k).drop k=[] := by simpa only [List.length_finRange] using (List.drop_length (l:=List.finRange k))
  simp only [remainingPrincipalEntries,hd,List.flatMap_nil]

lemma remainingRowsBudget_zero {n k : ℕ} (g : InputGraph n) (e : Fin k → Fin n) :
    remainingRowsBudget g e 0=k+∑ i : Fin k, (g.neighbors (e i)).length := by
  unfold remainingRowsBudget
  rw [List.drop_zero,←List.ofFn_eq_map,List.sum_ofFn]
  simp [Finset.sum_add_distrib,Nat.add_comm]

@[simp] lemma remainingPrincipalEntries_zero {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) :
    remainingPrincipalEntries g α e 0=principalEntries g α e := by simp [remainingPrincipalEntries,principalEntries]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DegreeSumCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma degreeSumBodyCode_queryReadOnly : degreeSumBodyCode.allAtoms queryReadOnly := by
  simp [degreeSumBodyCode,degreeSumTailRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.allAtoms,vertexFieldReadCode_queryReadOnly,queryReadOnly]

set_option maxHeartbeats 1800000 in
lemma degree_sum_body_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width : ℕ) (enumBase : ℤ)
    (e : Fin k → Fin n) (i : ℕ) (hi : i < k) (stored : Finset (Fin n)) (free : ℤ)
    (hcache : GraphCache g st.scalar.integerMemory width stored free) (hmem : e ⟨i,hi⟩ ∈ stored)
    (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hb : st.scalar.core.ptrs 80=enumBase) (hrow : st.scalar.core.ptrs 75=(i : ℤ)) :
    ∃ out, MachineEval m g ω degreeSumBodyCode st (4*width+14) out ∧
      out.scalar.core.ptrs 75=(i+1 : ℕ) ∧
      out.scalar.core.ptrs 82=st.scalar.core.ptrs 82+((g.neighbors (e ⟨i,hi⟩)).length : ℤ)+1 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*width+14 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let ii : Fin k := ⟨i,hi⟩
  let A := payUnit (pointerWrite st 81 (enumBase+(i : ℤ)))
  let B := payUnit (pointerWrite A 40 ((e ii).val : ℤ))
  have ea : MachineEval m g ω (.atom (.scalar (.pointerAdd 81 80 75))) st 1 A := by
    simpa only [A,hb,hrow] using pointerAdd_eval m g ω st 81 80 75 hh
  have ah : A.scalar.halted=false := hh
  have eb : MachineEval m g ω (.atom (.scalar (.integerLoad 40 81))) A 1 B := by
    have hv : A.scalar.integerMemory (A.scalar.core.ptrs 81)=((e ii).val : ℤ) := by
      simpa [A,payUnit,pcSet,pointerWrite,ii] using hEnum ii
    simpa only [B,hv] using integerLoad_eval m g ω A 40 81 ah
  have bh : B.scalar.halted=false := hh
  have b0 : B.scalar.core.ptrs 0=0 := by simpa [B,A,payUnit,pcSet,pointerWrite] using hz
  have b40 : B.scalar.core.ptrs 40=((e ii).val : ℤ) := by simp [B,payUnit,pcSet,pointerWrite]
  have b41 : B.scalar.core.ptrs 41=(width : ℤ) := by simpa [B,A,payUnit,pcSet,pointerWrite] using hw
  obtain ⟨mid,ec,hm60,hmI,hmR,hmQ,hmW,hmO,hmH⟩ := vertex_field_read_exec m g ω B bh width (e ii).val 0 60 b0 b40 b41
  change mid.scalar.core.ptrs 60=st.scalar.integerMemory (vertexRecordAddress width (e ii).val 0) at hm60
  rw [hcache.degree (e ii) hmem] at hm60
  have hm75 : mid.scalar.core.ptrs 75=(i : ℤ) :=
    (ec.pointer_frame 75 (by decide)).trans (by simpa [B,A,payUnit,pcSet,pointerWrite] using hrow)
  have hm82 : mid.scalar.core.ptrs 82=st.scalar.core.ptrs 82 :=
    (ec.pointer_frame 82 (by decide)).trans rfl
  obtain ⟨out,ed,hP,hoI,hoR,hoW,hoO,hoH⟩ := degreeSumTailRoutine.execute m g ω mid hmH
  have ed3 : MachineEval m g ω degreeSumTailRoutine.code mid 3 out := ed
  have eRun : MachineEval m g ω degreeSumBodyCode st (4*width+14) out := by
    have ee := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed3))
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,?_,?_,hoI.trans hmI,hoR.trans hmR,eRun.query_frame degreeSumBodyCode_queryReadOnly,?_,hoO.trans hmO,hoH⟩
  · rw [hP]
    simp [degreeSumTailRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
      PointerOp.destination,PointerOp.result,hm75]
  · rw [hP]
    simp [degreeSumTailRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
      PointerOp.destination,PointerOp.result,hm82,hm60,ii]
  · rw [hoW,hmW]
    change st.work+1+1+(4*width+9 : ℕ)+(3 : ℕ)= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DegreeSumExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1800000 in
lemma degree_sum_loop_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width : ℕ) (enumBase : ℤ) (e : Fin k → Fin n) (stored : Finset (Fin n)) (free : ℤ)
    (hmem : ∀ j, e j ∈ stored) (remaining i : ℕ) (z : ℤ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (hcache : GraphCache g st.scalar.integerMemory width stored free)
    (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hb : st.scalar.core.ptrs 80=enumBase) (hk : st.scalar.core.ptrs 77=(k : ℤ))
    (hrow : st.scalar.core.ptrs 75=(i : ℤ)) (hacc : st.scalar.core.ptrs 82=z) (hlen : i+remaining=k) :
    ∃ out, MachineEval m g ω degreeSumLoopCode st (remaining*(4*width+16)+1) out ∧
      out.scalar.core.ptrs 75=(k : ℤ) ∧ out.scalar.core.ptrs 82=z+(remainingRowsBudget g e i : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(remaining*(4*width+16)+1 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  induction remaining generalizing st i z with
  | zero =>
    have hi : i=k := by omega
    refine ⟨payUnit st,?_,by simpa [hi] using hrow,?_,rfl,rfl,rfl,by simp,rfl,hh⟩
    · simpa only [degreeSumLoopCode,Nat.zero_mul,Nat.zero_add] using
        (MachineEval.pointerDone (m:=m) (g:=g) (ω:=ω) (r:=77) (s:=75) (body:=degreeSumBodyCode) hh (by rw [hk,hrow,hi]))
    · simpa only [hi,remainingRowsBudget_done,Nat.cast_zero,add_zero,payUnit,pcSet] using hacc
  | succ remaining ih =>
    have hi : i < k := by omega
    obtain ⟨mid,eb,hm75,hm82,hmI,hmR,hmQ,hmW,hmO,hmH⟩ :=
      degree_sum_body_exec m g ω (payUnit st) hh width enumBase e i hi stored free hcache (hmem ⟨i,hi⟩) hEnum hz hw hb hrow
    have hm0 := (eb.pointer_frame 0 (by decide)).trans hz
    have hm41 := (eb.pointer_frame 41 (by decide)).trans hw
    have hm80 := (eb.pointer_frame 80 (by decide)).trans hb
    have hm77 := (eb.pointer_frame 77 (by decide)).trans hk
    have hmCache : GraphCache g mid.scalar.integerMemory width stored free := by rw [hmI]; exact hcache
    have hmEnum : EnumerationStored mid.scalar.integerMemory enumBase e := by rw [hmI]; exact hEnum
    have hmAcc : mid.scalar.core.ptrs 82=z+((g.neighbors (e ⟨i,hi⟩)).length : ℤ)+1 := by
      change mid.scalar.core.ptrs 82= _
      simpa only [payUnit,pcSet,hacc] using hm82
    obtain ⟨out,er,ho75,ho82,hoI,hoR,hoQ,hoW,hoO,hoH⟩ :=
      ih (i+1) (z+((g.neighbors (e ⟨i,hi⟩)).length : ℤ)+1) (payUnit mid) hmH hmCache hmEnum hm0 hm41 hm80 hm77 hm75 hmAcc (by omega)
    refine ⟨out,?_,ho75,?_,hoI.trans hmI,hoR.trans hmR,hoQ.trans hmQ,?_,hoO.trans hmO,hoH⟩
    · have eRun := MachineEval.pointerNext (r:=77) (s:=75) hh (by rw [hk,hrow]; omega) eb er
      convert eRun using 1 <;> (first | rfl | ring)
    · rw [ho82,remainingRowsBudget_cons g e i hi]
      push_cast
      ring
    · rw [hoW,payUnit_work,hmW,payUnit_work]
      push_cast
      ring

lemma degreeSumCode_queryReadOnly : degreeSumCode.allAtoms queryReadOnly := by
  simp [degreeSumCode,degreeSumInitRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    degreeSumLoopCode,MachineCode.allAtoms,degreeSumBodyCode_queryReadOnly,queryReadOnly]

set_option maxHeartbeats 1400000 in
lemma degree_sum_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width : ℕ) (enumBase : ℤ) (e : Fin k → Fin n) (stored : Finset (Fin n)) (free : ℤ)
    (hmem : ∀ j, e j ∈ stored) (st : MachineState) (hh : st.scalar.halted=false)
    (hcache : GraphCache g st.scalar.integerMemory width stored free)
    (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 50=(width : ℤ))
    (hb : st.scalar.core.ptrs 80=enumBase) (hk : st.scalar.core.ptrs 77=(k : ℤ)) :
    ∃ out, MachineEval m g ω degreeSumCode st (k*(4*width+16)+4) out ∧
      out.scalar.core.ptrs 82=((k+∑ j : Fin k, (g.neighbors (e j)).length : ℕ) : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(k*(4*width+16)+4 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,ep,hp,hI,hR,hW,hO,hH⟩ := degreeSumInitRoutine.execute m g ω st hh
  have ep3 : MachineEval m g ω degreeSumInitRoutine.code st 3 pre := ep
  have pre0 := (ep.pointer_frame 0 (by decide)).trans hz
  have pre80 := (ep.pointer_frame 80 (by decide)).trans hb
  have pre77 := (ep.pointer_frame 77 (by decide)).trans hk
  have pre41 : pre.scalar.core.ptrs 41=(width : ℤ) := by
    rw [hp]; simp [degreeSumInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,hw]
  have pre75 : pre.scalar.core.ptrs 75=0 := by
    rw [hp]; simp [degreeSumInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result]
  have pre82 : pre.scalar.core.ptrs 82=0 := by
    rw [hp]; simp [degreeSumInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result]
  have preCache : GraphCache g pre.scalar.integerMemory width stored free := by rw [hI]; exact hcache
  have preEnum : EnumerationStored pre.scalar.integerMemory enumBase e := by rw [hI]; exact hEnum
  obtain ⟨out,el,ho75,ho82,hoI,hoR,hoQ,hoW,hoO,hoH⟩ :=
    degree_sum_loop_exec m g ω width enumBase e stored free hmem k 0 0 pre hH preCache preEnum pre0 pre41 pre80 pre77 pre75 pre82 (by omega)
  have eRun : MachineEval m g ω degreeSumCode st (k*(4*width+16)+4) out := by
    have ee := MachineEval.seq ep3 el
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,?_,hoI.trans hI,hoR.trans hR,eRun.query_frame degreeSumCode_queryReadOnly,?_,hoO.trans hO,hoH⟩
  · simpa only [zero_add,remainingRowsBudget_zero] using ho82
  · rw [hoW,hW]
    change st.work+(3 : ℕ)+(k*(4*width+16)+1 : ℕ)= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndexPreparation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma indexPreparationCode_queryReadOnly : indexPreparationCode.allAtoms queryReadOnly := by
  simp [indexPreparationCode,indexInitRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    indexMarkLoopCode,MachineCode.allAtoms,indexMarkBodyCode_queryReadOnly,queryReadOnly]

set_option maxHeartbeats 1700000 in
lemma index_preparation_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width : ℕ) (hw9 : 9 ≤ width) (e : Fin k → Fin n) (he : Function.Injective e)
    (base epoch : ℤ) (hb0 : 0 ≤ base) (st : MachineState) (hh : st.scalar.halted=false)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 50=(width : ℤ))
    (hb : st.scalar.core.ptrs 80=base) (hE : st.scalar.core.ptrs 53=epoch)
    (hk : st.scalar.core.ptrs 77=(k : ℤ)) (henum : EnumerationStored st.scalar.integerMemory base e)
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress width v.val 7) ≤ epoch) :
    ∃ out, MachineEval m g ω indexPreparationCode st (k*(8*width+25)+4) out ∧
      out.scalar.core.ptrs 53=epoch+1 ∧ out.scalar.core.ptrs 75=(k : ℤ) ∧
      EnumerationStored out.scalar.integerMemory base e ∧ IndexPrefix out.scalar.integerMemory width (epoch+1) e k ∧
      (∀ z, 0 ≤ z → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ v : Fin n, ∀ field < 3, out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field)) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(k*(8*width+25)+4 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,ei,hp,hI,hR,hW,hO,hH⟩ := indexInitRoutine.execute m g ω st hh
  have ei3 : MachineEval m g ω indexInitRoutine.code st 3 pre := ei
  have h0 := (ei.pointer_frame 0 (by decide)).trans hz
  have h80 := (ei.pointer_frame 80 (by decide)).trans hb
  have h77 := (ei.pointer_frame 77 (by decide)).trans hk
  have h41 : pre.scalar.core.ptrs 41=(width : ℤ) := by
    rw [hp]; simp [indexInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
      PointerOp.destination,PointerOp.result,hw]
  have h53 : pre.scalar.core.ptrs 53=epoch+1 := by
    rw [hp]; simp [indexInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
      PointerOp.destination,PointerOp.result,hE]
  have h75 : pre.scalar.core.ptrs 75=0 := by
    rw [hp]; simp [indexInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
      PointerOp.destination,PointerOp.result]
  have hpEnum : EnumerationStored pre.scalar.integerMemory base e := by rw [hI]; exact henum
  have hpPrefix : IndexPrefix pre.scalar.integerMemory width (epoch+1) e 0 := by
    apply indexPrefix_empty
    intro v
    rw [hI]
    have h := hbound v
    omega
  obtain ⟨out,el,ho0,ho41,ho80,ho53,ho77,ho75,hoEnum,hoPrefix,hoPositive,hoFields,hoR,hoQ,hoW,hoO,hoH⟩ :=
    index_mark_loop_exec m g ω width hw9 e he base (epoch+1) hb0 k 0 pre hH h0 h41 h80 h53 h77 h75
      (by omega) hpEnum hpPrefix
  have eRun : MachineEval m g ω indexPreparationCode st (k*(8*width+25)+4) out := by
    have ee := MachineEval.seq ei3 el
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,ho53,ho75,hoEnum,hoPrefix,?_,?_,hoR.trans hR,eRun.query_frame indexPreparationCode_queryReadOnly,
    ?_,hoO.trans hO,hoH⟩
  · intro z hz'
    exact (hoPositive z hz').trans (congrFun hI z)
  · intro v field hf
    exact (hoFields v field hf).trans (congrFun hI _)
  · rw [hoW,hW]
    change st.work+(3 : ℕ)+(k*(8*width+25)+1 : ℕ)= _
    push_cast
    ring

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

-- Proof module: Solutions.IndexMarkFieldFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma indexMarkWords_field_frame (I : ℤ → ℤ) (width vertex other field : ℕ)
    (hw : 9 ≤ width) (hf : field < width) (hf7 : field ≠ 7) (hf8 : field ≠ 8) (epoch index : ℤ) :
    indexMarkWords I width vertex epoch index (vertexRecordAddress width other field)=
      I (vertexRecordAddress width other field) := by
  have h7 : vertexRecordAddress width other field ≠ vertexRecordAddress width vertex 7 := by
    intro he
    exact hf7 (vertexRecordAddress_injective width other vertex field 7 hf (by omega) he).2
  have h8 : vertexRecordAddress width other field ≠ vertexRecordAddress width vertex 8 := by
    intro he
    exact hf8 (vertexRecordAddress_injective width other vertex field 8 hf (by omega) he).2
  simp [indexMarkWords,Function.update_of_ne h7,Function.update_of_ne h8]

set_option maxHeartbeats 1800000 in
lemma index_mark_loop_field_frame (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width : ℕ) (hw9 : 9 ≤ width) (e : Fin k → Fin n) (base epoch : ℤ) (hb0 : 0 ≤ base)
    (remaining i : ℕ) (st out : MachineState) (steps : ℕ)
    (ex : MachineEval m g ω indexMarkLoopCode st steps out)
    (hh : st.scalar.halted=false) (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hb : st.scalar.core.ptrs 80=base) (hE : st.scalar.core.ptrs 53=epoch)
    (hk : st.scalar.core.ptrs 77=(k : ℤ)) (hi : st.scalar.core.ptrs 75=(i : ℤ))
    (hlen : i+remaining=k) (henum : EnumerationStored st.scalar.integerMemory base e)
    (v : Fin n) (field : ℕ) (hf : field < width) (hf7 : field ≠ 7) (hf8 : field ≠ 8) :
    out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field) := by
  induction remaining generalizing i st out steps with
  | zero =>
    have hik : i=k := by omega
    have ed : MachineEval m g ω indexMarkLoopCode st 1 (payUnit st) :=
      MachineEval.pointerDone hh (by rw [hk,hi,hik])
    obtain ⟨he,rfl⟩ := ex.deterministic ed
    rfl
  | succ remaining ih =>
    have hik : i < k := by omega
    change MachineEval m g ω (.whilePointer 77 75 indexMarkBodyCode) st steps out at ex
    cases ex with
    | pointerDone hh' hg => rw [hk,hi] at hg; omega
    | pointerNext hh' hg eb er =>
      obtain ⟨mid,em,hm75,hmI,hmR,hmQ,hmW,hmO,hmH⟩ := index_mark_body_exec m g ω (payUnit st) hh
        width (e ⟨i,hik⟩) base epoch i hz hw hb hE hi (henum ⟨i,hik⟩)
      have hstate := (eb.deterministic em).2
      rw [hstate] at er
      have hm0 := (em.pointer_frame 0 (by decide)).trans hz
      have hm41 := (em.pointer_frame 41 (by decide)).trans hw
      have hm80 := (em.pointer_frame 80 (by decide)).trans hb
      have hm53 := (em.pointer_frame 53 (by decide)).trans hE
      have hm77 := (em.pointer_frame 77 (by decide)).trans hk
      have hmEnum : EnumerationStored mid.scalar.integerMemory base e := by
        intro j
        rw [hmI,indexMarkWords_nonnegative _ _ _ _ _ _ (by omega)]
        exact henum j
      have hrec := ih (i+1) (payUnit mid) _ _ er hmH hm0 hm41 hm80 hm53 hm77 hm75 (by omega) hmEnum
      apply hrec.trans
      change mid.scalar.integerMemory _=st.scalar.integerMemory _
      rw [hmI]
      exact indexMarkWords_field_frame _ _ _ _ _ hw9 hf hf7 hf8 _ _

set_option maxHeartbeats 1500000 in
lemma index_preparation_field_frame (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width : ℕ) (hw9 : 9 ≤ width) (e : Fin k → Fin n) (base epoch : ℤ) (hb0 : 0 ≤ base)
    (st out : MachineState) (steps : ℕ) (ex : MachineEval m g ω indexPreparationCode st steps out)
    (hh : st.scalar.halted=false) (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 50=(width : ℤ))
    (hb : st.scalar.core.ptrs 80=base) (hE : st.scalar.core.ptrs 53=epoch)
    (hk : st.scalar.core.ptrs 77=(k : ℤ)) (henum : EnumerationStored st.scalar.integerMemory base e)
    (v : Fin n) (field : ℕ) (hf : field < width) (hf7 : field ≠ 7) (hf8 : field ≠ 8) :
    out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field) := by
  change MachineEval m g ω (.seq indexInitRoutine.code indexMarkLoopCode) st steps out at ex
  cases ex with
  | seq ea el =>
    obtain ⟨pre,ep,hp,hI,hR,hW,hO,hH⟩ := indexInitRoutine.execute m g ω st hh
    have hstate := (ea.deterministic ep).2
    rw [hstate] at el
    have h0 := (ep.pointer_frame 0 (by decide)).trans hz
    have h80 := (ep.pointer_frame 80 (by decide)).trans hb
    have h77 := (ep.pointer_frame 77 (by decide)).trans hk
    have h41 : pre.scalar.core.ptrs 41=(width : ℤ) := by
      rw [hp]; simp [indexInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
        PointerOp.destination,PointerOp.result,hw]
    have h53 : pre.scalar.core.ptrs 53=epoch+1 := by
      rw [hp]; simp [indexInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
        PointerOp.destination,PointerOp.result,hE]
    have h75 : pre.scalar.core.ptrs 75=0 := by
      rw [hp]; simp [indexInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,
        PointerOp.destination,PointerOp.result]
    have hpEnum : EnumerationStored pre.scalar.integerMemory base e := by rw [hI]; exact henum
    have hr := index_mark_loop_field_frame m g ω width hw9 e base (epoch+1) hb0 k 0 pre out _ el
      hH h0 h41 h80 h53 h77 h75 (by omega) hpEnum v field hf hf7 hf8
    exact hr.trans (congrFun hI _)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LocalSolvePreparation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2000000 in
lemma local_solve_preparation_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width : ℕ) (hw9 : 9 ≤ width) (base enumBase epoch : ℤ) (hEnumBase : 0 ≤ enumBase)
    (e : Fin k → Fin n) (he : Function.Injective e) (stored : Finset (Fin n))
    (st : MachineState) (hh : st.scalar.halted=false)
    (hcache : GraphCache g st.scalar.integerMemory width stored base) (hmem : ∀ j, e j ∈ stored)
    (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 50=(width : ℤ))
    (hb : st.scalar.core.ptrs 80=enumBase) (hk : st.scalar.core.ptrs 77=(k : ℤ))
    (hf : st.scalar.core.ptrs 20=base) (hE : st.scalar.core.ptrs 53=epoch)
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress width v.val 7) ≤ epoch) :
    let capacity := k+∑ j : Fin k, (g.neighbors (e j)).length
    ∃ out, MachineEval m g ω localSolvePreparationCode st (k*(12*width+41)+20) out ∧
      SparseAssemblyState out base k capacity [] ∧
      GraphCache g out.scalar.integerMemory width stored base ∧
      IndexPrefix out.scalar.integerMemory width (epoch+1) e k ∧
      EnumerationStored out.scalar.integerMemory enumBase e ∧
      out.scalar.core.ptrs 41=(width : ℤ) ∧ out.scalar.core.ptrs 53=epoch+1 ∧
      (∀ z, 0 ≤ z → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ v : Fin n, ∀ field < 3, out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field)) ∧
      (∀ v : Fin n, ∀ field < width, field ≠ 7 → field ≠ 8 →
        out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field)) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(k*(12*width+41)+20 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  dsimp only
  let capacity := k+∑ j : Fin k, (g.neighbors (e j)).length
  obtain ⟨a,ea,ha82,haI,haR,haQ,haW,haO,haH⟩ := degree_sum_exec m g ω width enumBase e stored base hmem st hh hcache hEnum hz hw hb hk
  have a0 := (ea.pointer_frame 0 (by decide)).trans hz
  have a50 := (ea.pointer_frame 50 (by decide)).trans hw
  have a80 := (ea.pointer_frame 80 (by decide)).trans hb
  have a77 := (ea.pointer_frame 77 (by decide)).trans hk
  have a53 := (ea.pointer_frame 53 (by decide)).trans hE
  have aEnum : EnumerationStored a.scalar.integerMemory enumBase e := by rw [haI]; exact hEnum
  have aBound : ∀ v : Fin n, a.scalar.integerMemory (vertexRecordAddress width v.val 7) ≤ epoch := by rw [haI]; exact hbound
  obtain ⟨b,eb,hb53,hb75,hbEnum,hbTable,hbPos,hbFields,hbR,hbQ,hbW,hbO,hbH⟩ :=
    index_preparation_exec m g ω width hw9 e he enumBase epoch hEnumBase a haH a0 a50 a80 a53 a77 aEnum aBound
  have b20 := (eb.pointer_frame 20 (by decide)).trans ((ea.pointer_frame 20 (by decide)).trans hf)
  have b77 := (eb.pointer_frame 77 (by decide)).trans a77
  have b82 := (eb.pointer_frame 82 (by decide)).trans ha82
  have b50 := (eb.pointer_frame 50 (by decide)).trans a50
  have bCache : GraphCache g b.scalar.integerMemory width stored base := by
    apply GraphCache.frame g _ _ width stored base hcache
    · intro v field hf
      exact (hbFields v field hf).trans (congrFun haI _)
    · intro v hv i hi
      have hpos := hcache.basePositive v hv
      exact (hbPos _ (by omega)).trans (congrFun haI _)
  obtain ⟨c,ec,hcLayout,hc74,hcI,hcR,hcW,hcO,hcH⟩ := solve_buffer_allocation_exec m g ω b hbH base k capacity b20 b77 b82
  have c50 := (ec.pointer_frame 50 (by decide)).trans b50
  let out := payUnit (pointerWrite c 41 (width : ℤ))
  have ed : MachineEval m g ω (coreCode (.pcopy 41 50)) c 1 out := by
    simpa only [out,coreCode,c50] using pcopy_eval m g ω c 41 50 hcH
  have eRun : MachineEval m g ω localSolvePreparationCode st (k*(12*width+41)+20) out := by
    have ee := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
    convert ee using 1 <;> (first | rfl | ring)
  have hLayout : SolveBufferLayout out.scalar base k capacity := ed.solve_buffer_frame hcLayout (by decide)
  have hI : out.scalar.integerMemory=b.scalar.integerMemory := hcI
  have hR : out.scalar.core.mem=st.scalar.core.mem := hcR.trans (hbR.trans haR)
  refine ⟨out,eRun,⟨hLayout,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,hR,?_,?_,hcO.trans (hbO.trans haO),hcH⟩
  · intro i hi; simp at hi
  · exact (ed.pointer_frame 74 (by decide)).trans hc74
  · rw [hI]; exact bCache
  · rw [hI]; exact hbTable
  · rw [hI]; exact hbEnum
  · simp [out,payUnit,pcSet,pointerWrite]
  · exact (ed.pointer_frame 53 (by decide)).trans ((ec.pointer_frame 53 (by decide)).trans hb53)
  · intro z hz'; rw [hI,hbPos z hz',haI]
  · intro v field hf'; rw [hI,hbFields v field hf',haI]
  · intro v field hf' hf7 hf8
    rw [hI]
    exact (index_preparation_field_frame m g ω width hw9 e enumBase epoch hEnumBase a b _ eb
      haH a0 a50 a80 a53 a77 aEnum v field hf' hf7 hf8).trans (congrFun haI _)
  · apply eRun.query_frame
    simp [localSolvePreparationCode,MachineCode.allAtoms,degreeSumCode_queryReadOnly,
      indexPreparationCode_queryReadOnly,solveBufferRoutine,PointerRoutine.sequence,
      PointerRoutine.code,PointerOp.instruction,coreCode,queryReadOnly]
  · change c.work+1= _
    rw [hcW,hbW,haW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrincipalAssemblyBody

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma principalAssemblyBodyCode_queryReadOnly : principalAssemblyBodyCode.allAtoms queryReadOnly := by
  simp [principalAssemblyBodyCode,MachineCode.allAtoms,principalRowAssemblyCode_queryReadOnly,coreCode,queryReadOnly]

set_option maxHeartbeats 2600000 in
lemma principal_assembly_body_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width capacity : ℕ) (base enumBase epoch : ℤ)
    (e : Fin k → Fin n) (he : Function.Injective e) (α : ℝ) (i : ℕ) (hi : i < k)
    (stored : Finset (Fin n)) (entries : List SparseEntry)
    (h : SparseAssemblyState st base k capacity entries)
    (hcap : entries.length+(g.neighbors (e ⟨i,hi⟩)).length+1 ≤ capacity)
    (hcache : GraphCache g st.scalar.integerMemory width stored base) (hmem : e ⟨i,hi⟩ ∈ stored)
    (hTable : IndexPrefix st.scalar.integerMemory width epoch e k)
    (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hEnumBelow : ∀ j : Fin k, enumBase+(j.val : ℤ) < base)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hE : st.scalar.core.ptrs 53=epoch) (hbaseE : st.scalar.core.ptrs 80=enumBase)
    (hrow : st.scalar.core.ptrs 75=(i : ℤ)) (ha : st.scalar.core.regs 12=α-1) (h1 : st.scalar.core.regs 11=1) :
    ∃ steps out, MachineEval m g ω principalAssemblyBodyCode st steps out ∧
      steps ≤ ((g.neighbors (e ⟨i,hi⟩)).length+1)*(8*width+43) ∧ out.scalar.core.ptrs 75=(i+1 : ℕ) ∧
      SparseAssemblyState out base k capacity (entries++principalRowEntries g α e ⟨i,hi⟩) ∧
      GraphCache g out.scalar.integerMemory width stored base ∧ IndexPrefix out.scalar.integerMemory width epoch e k ∧
      EnumerationStored out.scalar.integerMemory enumBase e ∧
      (∀ z, z < base → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ z, z < base → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.core.regs 12=α-1 ∧ out.scalar.core.regs 11=1 ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let ii : Fin k := ⟨i,hi⟩
  let A := payUnit (pointerWrite st 81 (enumBase+(i : ℤ)))
  let B := payUnit (pointerWrite A 40 ((e ii).val : ℤ))
  have ea : MachineEval m g ω (.atom (.scalar (.pointerAdd 81 80 75))) st 1 A := by
    simpa only [A,hbaseE,hrow] using pointerAdd_eval m g ω st 81 80 75 hh
  have ah : A.scalar.halted=false := hh
  have eb : MachineEval m g ω (.atom (.scalar (.integerLoad 40 81))) A 1 B := by
    have hval : A.scalar.integerMemory (A.scalar.core.ptrs 81)=((e ii).val : ℤ) := by
      simpa [A,payUnit,pcSet,pointerWrite,ii] using hEnum ii
    simpa only [B,hval] using integerLoad_eval m g ω A 40 81 ah
  have bh : B.scalar.halted=false := hh
  have ep := MachineEval.seq ea eb
  have bState : SparseAssemblyState B base k capacity entries := SparseAssemblyState.readOnly ep h (by decide) rfl rfl
  have b0 : B.scalar.core.ptrs 0=0 := by simpa [B,A,payUnit,pcSet,pointerWrite] using hz
  have b40 : B.scalar.core.ptrs 40=((e ii).val : ℤ) := by simp [B,payUnit,pcSet,pointerWrite]
  have b41 : B.scalar.core.ptrs 41=(width : ℤ) := by simpa [B,A,payUnit,pcSet,pointerWrite] using hw
  have b53 : B.scalar.core.ptrs 53=epoch := by simpa [B,A,payUnit,pcSet,pointerWrite] using hE
  have b75 : B.scalar.core.ptrs 75=(ii.val : ℤ) := by simpa [B,A,payUnit,pcSet,pointerWrite,ii] using hrow
  obtain ⟨u,mid,ec,hu,hmState,hmTable,hmI,hmR,hmQ,hmW,hmO,hmH⟩ :=
    principal_row_assembly_exec m g ω B bh width capacity base epoch e he ii α stored entries bState hcap hcache hmem
      hTable b0 b40 b41 b53 b75 ha h1
  have hm75 : mid.scalar.core.ptrs 75=(i : ℤ) :=
    (ec.pointer_frame 75 (by decide)).trans (by simpa [ii] using b75)
  let out := payUnit (pointerWrite mid 75 (i+1 : ℕ))
  have ed : MachineEval m g ω (coreCode (.pinc 75)) mid 1 out := by
    simpa only [out,coreCode,hm75,Nat.cast_add,Nat.cast_one] using pinc_eval m g ω mid 75 hmH
  have eRun := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  have hoState : SparseAssemblyState out base k capacity (entries++principalRowEntries g α e ii) :=
    SparseAssemblyState.readOnly ed hmState (by decide) rfl rfl
  have hoI : ∀ z, z < base → out.scalar.integerMemory z=st.scalar.integerMemory z := hmI
  have hoR : ∀ z, z < base → out.scalar.core.mem z=st.scalar.core.mem z := hmR
  have hbase : 0 ≤ base := by have hf := hcache.freeBound; omega
  have hoCache : GraphCache g out.scalar.integerMemory width stored base := by
    apply GraphCache.frame g _ _ width stored base hcache
    · intro v field hf
      exact hoI _ ((vertexRecordAddress_negative _ _ _).trans_le hbase)
    · intro v hv j hj
      exact hoI _ (hcache.belowFree v hv j hj)
  have hoEnum : EnumerationStored out.scalar.integerMemory enumBase e := by
    intro j
    rw [hoI _ (hEnumBelow j)]
    exact hEnum j
  refine ⟨1+(1+(u+1)),out,eRun,by nlinarith,by simp [out,payUnit,pcSet,pointerWrite],hoState,hoCache,hmTable,hoEnum,hoI,hoR,
    ?_,?_,eRun.query_frame principalAssemblyBodyCode_queryReadOnly,?_,hmO,hmH⟩
  · exact (eRun.real_register_frame 12 (by decide)).trans ha
  · exact (eRun.real_register_frame 11 (by decide)).trans h1
  · change mid.work+1= _
    rw [hmW]
    change st.work+1+1+u+1= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrincipalAssemblyLoop

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 3500000 in
lemma principal_assembly_loop_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width capacity : ℕ) (base enumBase epoch : ℤ) (e : Fin k → Fin n) (he : Function.Injective e) (α : ℝ)
    (stored : Finset (Fin n)) (hmem : ∀ j, e j ∈ stored) (remaining i : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false) (entries : List SparseEntry)
    (h : SparseAssemblyState st base k capacity entries)
    (hcap : entries.length+remainingRowsBudget g e i ≤ capacity)
    (hcache : GraphCache g st.scalar.integerMemory width stored base)
    (hTable : IndexPrefix st.scalar.integerMemory width epoch e k)
    (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hEnumBelow : ∀ j : Fin k, enumBase+(j.val : ℤ) < base)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hE : st.scalar.core.ptrs 53=epoch) (hbaseE : st.scalar.core.ptrs 80=enumBase)
    (hrow : st.scalar.core.ptrs 75=(i : ℤ)) (ha : st.scalar.core.regs 12=α-1) (h1 : st.scalar.core.regs 11=1)
    (hlen : i+remaining=k) :
    ∃ steps out, MachineEval m g ω principalAssemblyLoopCode st steps out ∧
      steps ≤ (8*width+45)*remainingRowsBudget g e i+1 ∧ out.scalar.core.ptrs 75=(k : ℤ) ∧
      SparseAssemblyState out base k capacity (entries++remainingPrincipalEntries g α e i) ∧
      GraphCache g out.scalar.integerMemory width stored base ∧ IndexPrefix out.scalar.integerMemory width epoch e k ∧
      EnumerationStored out.scalar.integerMemory enumBase e ∧
      (∀ z, z < base → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ z, z < base → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.core.regs 12=α-1 ∧ out.scalar.core.regs 11=1 ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction remaining generalizing st i entries with
  | zero =>
    have hi : i=k := by omega
    have es : MachineEval m g ω principalAssemblyLoopCode st 1 (payUnit st) :=
      MachineEval.pointerDone (r:=77) (s:=75) (body:=principalAssemblyBodyCode) hh
        (by rw [h.layout.dimensionPointer,hrow,hi])
    refine ⟨1,payUnit st,es,by simp [hi],by simpa [hi] using hrow,?_,hcache,hTable,hEnum,
      (by intros; rfl),(by intros; rfl),ha,h1,rfl,by simp,rfl,hh⟩
    simpa only [hi,remainingPrincipalEntries_done,List.append_nil] using h.pay
  | succ remaining ih =>
    have hi : i < k := by omega
    have hBudget := remainingRowsBudget_cons g e i hi
    obtain ⟨u,mid,eb,hu,hm75,hmState,hmCache,hmTable,hmEnum,hmI,hmR,hm12,hm11,hmQ,hmW,hmO,hmH⟩ :=
      principal_assembly_body_exec m g ω (payUnit st) hh width capacity base enumBase epoch e he α i hi stored entries
        h.pay (by omega) hcache (hmem ⟨i,hi⟩) hTable hEnum hEnumBelow hz hw hE hbaseE hrow ha h1
    have hm0 := (eb.pointer_frame 0 (by decide)).trans hz
    have hm41 := (eb.pointer_frame 41 (by decide)).trans hw
    have hm53 := (eb.pointer_frame 53 (by decide)).trans hE
    have hm80 := (eb.pointer_frame 80 (by decide)).trans hbaseE
    have hmCap : (entries++principalRowEntries g α e ⟨i,hi⟩).length+remainingRowsBudget g e (i+1) ≤ capacity := by
      have hLen := principalRowEntries_length_le g α e ⟨i,hi⟩
      simp only [List.length_append]
      omega
    obtain ⟨v,out,er,hv,ho75,hoState,hoCache,hoTable,hoEnum,hoI,hoR,ho12,ho11,hoQ,hoW,hoO,hoH⟩ :=
      ih (i+1) (payUnit mid) hmH _ hmState.pay hmCap hmCache hmTable hmEnum hm0 hm41 hm53 hm80 hm75 hm12 hm11 (by omega)
    have hList : (entries++principalRowEntries g α e ⟨i,hi⟩)++remainingPrincipalEntries g α e (i+1)=
        entries++remainingPrincipalEntries g α e i := by
      rw [remainingPrincipalEntries_cons g α e i hi]
      simp [List.append_assoc]
    rw [hList] at hoState
    refine ⟨1+u+1+v,out,?_,?_,ho75,hoState,hoCache,hoTable,hoEnum,?_,?_,ho12,ho11,hoQ.trans hmQ,?_,hoO.trans hmO,hoH⟩
    · exact MachineEval.pointerNext (r:=77) (s:=75) hh (by rw [h.layout.dimensionPointer,hrow]; omega) eb er
    · rw [hBudget]
      nlinarith
    · intro z hz'; exact (hoI z hz').trans (hmI z hz')
    · intro z hz'; exact (hoR z hz').trans (hmR z hz')
    · rw [hoW,payUnit_work,hmW,payUnit_work]
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MatrixAssemblyInit

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma matrixAssemblyInitCode_queryReadOnly : matrixAssemblyInitCode.allAtoms queryReadOnly := by
  simp [matrixAssemblyInitCode,linearCode,matrixAssemblyInitInstructions,RealOperation.instruction,
    sequenceCode,MachineCode.allAtoms,queryReadOnly]

set_option maxHeartbeats 1400000 in
lemma matrix_assembly_init_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (α : ℝ)
    (hz : st.scalar.core.ptrs 0=0) (hα : st.scalar.core.mem 0=α) :
    ∃ out, MachineEval m g ω matrixAssemblyInitCode st 4 out ∧
      out.scalar.core.regs 12=α-1 ∧ out.scalar.core.regs 11=1 ∧ out.scalar.core.ptrs 75=0 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+4 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let out := linearRun m g ω matrixAssemblyInitInstructions st
  obtain ⟨e,hw,hH⟩ := linear_execute m g ω matrixAssemblyInitInstructions
    (by simp [matrixAssemblyInitInstructions,RealOperation.instruction,unitInstruction,straightInstruction]) st hh
  refine ⟨out,e,?_,?_,?_,?_,?_,e.query_frame matrixAssemblyInitCode_queryReadOnly,hw,?_,hH⟩
  all_goals simp [out,linearRun,matrixAssemblyInitInstructions,RealOperation.instruction,
    atomState,machineStep,pcSet,LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hz,hα]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrincipalMatrixAssembly

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2500000 in
lemma principal_matrix_assembly_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width capacity : ℕ) (base enumBase epoch : ℤ)
    (e : Fin k → Fin n) (he : Function.Injective e) (α : ℝ) (stored : Finset (Fin n))
    (h : SparseAssemblyState st base k capacity [])
    (hcap : k+∑ j : Fin k, (g.neighbors (e j)).length ≤ capacity)
    (hcache : GraphCache g st.scalar.integerMemory width stored base) (hmem : ∀ j, e j ∈ stored)
    (hTable : IndexPrefix st.scalar.integerMemory width epoch e k)
    (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hEnumBelow : ∀ j : Fin k, enumBase+(j.val : ℤ) < base)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hE : st.scalar.core.ptrs 53=epoch) (hbaseE : st.scalar.core.ptrs 80=enumBase) (hα : st.scalar.core.mem 0=α) :
    ∃ steps out, MachineEval m g ω principalMatrixAssemblyCode st steps out ∧ steps ≤ (8*width+45)*capacity+5 ∧
      SparseAssemblyState out base k capacity (principalEntries g α e) ∧
      GraphCache g out.scalar.integerMemory width stored base ∧ IndexPrefix out.scalar.integerMemory width epoch e k ∧
      EnumerationStored out.scalar.integerMemory enumBase e ∧
      suppliedMatrix out.scalar preparedSolveRegisters k (principalEntries g α e).length=(LocalPush.Lα g.graph α).submatrix e e ∧
      (∀ z, z < base → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ z, z < base → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,ep,hp12,hp11,hp75,hpI,hpR,hpQ,hpW,hpO,hpH⟩ := matrix_assembly_init_exec m g ω st hh α hz hα
  have hpState : SparseAssemblyState pre base k capacity [] := SparseAssemblyState.readOnly ep h (by decide) hpI hpR
  have hpCache : GraphCache g pre.scalar.integerMemory width stored base := by rw [hpI]; exact hcache
  have hpTable : IndexPrefix pre.scalar.integerMemory width epoch e k := by rw [hpI]; exact hTable
  have hpEnum : EnumerationStored pre.scalar.integerMemory enumBase e := by rw [hpI]; exact hEnum
  have hp0 := (ep.pointer_frame 0 (by decide)).trans hz
  have hp41 := (ep.pointer_frame 41 (by decide)).trans hw
  have hp53 := (ep.pointer_frame 53 (by decide)).trans hE
  have hp80 := (ep.pointer_frame 80 (by decide)).trans hbaseE
  obtain ⟨u,out,el,hu,ho75,hoState,hoCache,hoTable,hoEnum,hoI,hoR,ho12,ho11,hoQ,hoW,hoO,hoH⟩ :=
    principal_assembly_loop_exec m g ω width capacity base enumBase epoch e he α stored hmem k 0 pre hpH [] hpState
      (by simpa only [List.length_nil,zero_add,remainingRowsBudget_zero] using hcap)
      hpCache hpTable hpEnum hEnumBelow hp0 hp41 hp53 hp80 hp75 hp12 hp11 (by omega)
  simp only [remainingPrincipalEntries_zero,List.nil_append] at hoState
  have hMatrix : suppliedMatrix out.scalar preparedSolveRegisters k (principalEntries g α e).length=
      (LocalPush.Lα g.graph α).submatrix e e :=
    (suppliedMatrix_decode out.scalar preparedSolveRegisters k (principalEntries g α e) hoState.contents).trans
      (principal_entries_decode g α e he)
  have eRun := MachineEval.seq ep el
  refine ⟨4+u,out,eRun,?_,hoState,hoCache,hoTable,hoEnum,hMatrix,?_,?_,hoQ.trans hpQ,?_,hoO.trans hpO,hoH⟩
  · rw [remainingRowsBudget_zero] at hu
    have hmul := Nat.mul_le_mul_left (8*width+45) hcap
    omega
  · intro z hz'; exact (hoI z hz').trans (congrFun hpI z)
  · intro z hz'; exact (hoR z hz').trans (congrFun hpR z)
  · rw [hoW,hpW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RightHandSideBody

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma rightHandSideBodyCode_queryReadOnly : rightHandSideBodyCode.allAtoms queryReadOnly := by
  simp [rightHandSideBodyCode,vertexRealLoadCode,vertexAddressCode_queryReadOnly,
    rightHandSideTailCode,linearCode,rightHandSideTailInstructions,sequenceCode,
    MachineCode.allAtoms,coreCode,queryReadOnly]

set_option maxHeartbeats 1600000 in
lemma right_hand_side_tail_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω rightHandSideTailCode st 3 out ∧
      out.scalar.core.ptrs 75=st.scalar.core.ptrs 75+1 ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (st.scalar.core.ptrs 78+st.scalar.core.ptrs 75) (st.scalar.core.regs 10) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.work=st.work+3 ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨e,hw,hH⟩ := linear_execute m g ω rightHandSideTailInstructions
    (by simp [rightHandSideTailInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,e,?_,?_,?_,hw,?_,hH⟩
  all_goals simp [linearRun,rightHandSideTailInstructions,atomState,machineStep,pcSet,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]

set_option maxHeartbeats 2000000 in
lemma right_hand_side_body_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width offset : ℕ) (enumBase rhsBase : ℤ)
    (e : Fin k → Fin n) (i : ℕ) (hi : i < k)
    (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hOff : st.scalar.core.ptrs 44=(offset : ℤ)) (hEnumBase : st.scalar.core.ptrs 80=enumBase)
    (hRhsBase : st.scalar.core.ptrs 78=rhsBase) (hrow : st.scalar.core.ptrs 75=(i : ℤ)) :
    ∃ out, MachineEval m g ω rightHandSideBodyCode st (4*width+12) out ∧
      out.scalar.core.ptrs 75=(i+1 : ℕ) ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (rhsBase+(i : ℤ))
        (st.scalar.core.mem (vertexRecordAddress width (e ⟨i,hi⟩).val offset)) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(4*width+12 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let ii : Fin k := ⟨i,hi⟩
  let A := payUnit (pointerWrite st 81 (enumBase+(i : ℤ)))
  let B := payUnit (pointerWrite A 40 ((e ii).val : ℤ))
  have ea : MachineEval m g ω (.atom (.scalar (.pointerAdd 81 80 75))) st 1 A := by
    simpa only [A,hEnumBase,hrow] using pointerAdd_eval m g ω st 81 80 75 hh
  have eb : MachineEval m g ω (.atom (.scalar (.integerLoad 40 81))) A 1 B := by
    have hval : A.scalar.integerMemory (A.scalar.core.ptrs 81)=((e ii).val : ℤ) := by
      simpa [A,payUnit,pcSet,pointerWrite,ii] using hEnum ii
    simpa only [B,hval] using integerLoad_eval m g ω A 40 81 hh
  have b0 : B.scalar.core.ptrs 0=0 := by simpa [B,A,payUnit,pcSet,pointerWrite] using hz
  have b40 : B.scalar.core.ptrs 40=((e ii).val : ℤ) := by simp [B,payUnit,pcSet,pointerWrite]
  have b41 : B.scalar.core.ptrs 41=(width : ℤ) := by simpa [B,A,payUnit,pcSet,pointerWrite] using hw
  have b44 : B.scalar.core.ptrs 44=(offset : ℤ) := by simpa [B,A,payUnit,pcSet,pointerWrite] using hOff
  obtain ⟨mid,el,hm10,hmI,hmR,hmW,hmO,hmH⟩ := vertex_real_load_exec m g ω B hh width (e ii).val offset b0 b40 b41 b44
  have hm75 : mid.scalar.core.ptrs 75=(i : ℤ) :=
    (el.pointer_frame 75 (by decide)).trans (by simpa [B,A,payUnit,pcSet,pointerWrite] using hrow)
  have hm78 : mid.scalar.core.ptrs 78=rhsBase :=
    (el.pointer_frame 78 (by decide)).trans (by simpa [B,A,payUnit,pcSet,pointerWrite] using hRhsBase)
  obtain ⟨out,et,ho75,hoR,hoI,hoW,hoO,hoH⟩ := right_hand_side_tail_exec m g ω mid hmH
  have eRun : MachineEval m g ω rightHandSideBodyCode st (4*width+12) out := by
    have ee := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq el et))
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,?_,?_,hoI.trans hmI,eRun.query_frame rightHandSideBodyCode_queryReadOnly,?_,hoO.trans hmO,hoH⟩
  · rw [ho75,hm75]
    push_cast
    rfl
  · rw [hoR,hmR,hm78,hm75,hm10]
    rfl
  · rw [hoW,hmW]
    change st.work+1+1+(4*width+7 : ℕ)+3= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RightHandSideLoop

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2200000 in
lemma right_hand_side_loop_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width offset : ℕ) (enumBase rhsBase : ℤ) (hbase : 0 ≤ rhsBase)
    (e : Fin k → Fin n) (b : Fin n → ℝ) (remaining i : ℕ) (st : MachineState)
    (hh : st.scalar.halted=false) (hz : st.scalar.core.ptrs 0=0)
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hOff : st.scalar.core.ptrs 44=(offset : ℤ))
    (hEnumBase : st.scalar.core.ptrs 80=enumBase) (hRhsBase : st.scalar.core.ptrs 78=rhsBase)
    (hrow : st.scalar.core.ptrs 75=(i : ℤ)) (hk : st.scalar.core.ptrs 77=(k : ℤ))
    (hlen : i+remaining=k) (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hb : ∀ v : Fin n, st.scalar.core.mem (vertexRecordAddress width v.val offset)=b v) :
    ∃ out, MachineEval m g ω rightHandSideLoopCode st (remaining*(4*width+14)+1) out ∧
      out.scalar.core.ptrs 75=(k : ℤ) ∧
      (∀ j : Fin k, i ≤ j.val → out.scalar.core.mem (rhsBase+(j.val : ℤ))=b (e j)) ∧
      (∀ z, z < rhsBase+(i : ℤ) ∨ rhsBase+(k : ℤ) ≤ z → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(remaining*(4*width+14)+1 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction remaining generalizing i st with
  | zero =>
    have hik : i=k := by omega
    subst i
    refine ⟨payUnit st,?_,hrow,?_,(by intros; rfl),rfl,rfl,?_,rfl,hh⟩
    · simpa only [rightHandSideLoopCode,Nat.zero_mul,Nat.zero_add] using
        (MachineEval.pointerDone (m:=m) (g:=g) (ω:=ω) (r:=77) (s:=75) (body:=rightHandSideBodyCode) hh
          (by rw [hk,hrow]))
    · intro j hj; omega
    · simp
  | succ remaining ih =>
    have hi : i < k := by omega
    obtain ⟨mid,eb,hm75,hmR,hmI,hmQ,hmW,hmO,hmH⟩ := right_hand_side_body_exec m g ω (payUnit st) hh
      width offset enumBase rhsBase e i hi hEnum hz hw hOff hEnumBase hRhsBase hrow
    have hmid0 := (eb.pointer_frame 0 (by decide)).trans hz
    have hmid41 := (eb.pointer_frame 41 (by decide)).trans hw
    have hmid44 := (eb.pointer_frame 44 (by decide)).trans hOff
    have hmid80 := (eb.pointer_frame 80 (by decide)).trans hEnumBase
    have hmid78 := (eb.pointer_frame 78 (by decide)).trans hRhsBase
    have hmid77 := (eb.pointer_frame 77 (by decide)).trans hk
    have hmidEnum : EnumerationStored mid.scalar.integerMemory enumBase e := by rw [hmI]; exact hEnum
    have hmidB : ∀ v : Fin n, mid.scalar.core.mem (vertexRecordAddress width v.val offset)=b v := by
      intro v
      rw [hmR]
      have hn := vertexRecordAddress_negative width v.val offset
      have heq : vertexRecordAddress width v.val offset ≠ rhsBase+(i : ℤ) := by omega
      simp only [Function.update_of_ne heq]
      exact hb v
    obtain ⟨out,er,ho75,hoValues,hoFrame,hoI,hoQ,hoW,hoO,hoH⟩ := ih (i+1) (payUnit mid) hmH
      hmid0 hmid41 hmid44 hmid80 hmid78 hm75 hmid77 (by omega) hmidEnum hmidB
    refine ⟨out,?_,ho75,?_,?_,hoI.trans hmI,hoQ.trans hmQ,?_,hoO.trans hmO,hoH⟩
    · have ee := MachineEval.pointerNext (r:=77) (s:=75) hh (by rw [hk,hrow]; omega) eb er
      convert ee using 1 <;> (first | rfl | simp only [Nat.succ_mul]; omega)
    · intro j hj
      by_cases he : j.val=i
      · have hjEq : j=⟨i,hi⟩ := Fin.ext he
        subst j
        have hAt : out.scalar.core.mem (rhsBase+(i : ℤ))=mid.scalar.core.mem (rhsBase+(i : ℤ)) :=
          hoFrame _ (Or.inl (by push_cast; omega))
        rw [hAt,hmR]
        simpa only [payUnit,pcSet,Function.update_self] using hb (e ⟨i,hi⟩)
      · exact hoValues j (by omega)
    · intro z hz'
      have ho : out.scalar.core.mem z=mid.scalar.core.mem z := hoFrame z (by
        rcases hz' with hz'|hz'
        · left; push_cast; omega
        · exact Or.inr hz')
      rw [ho,hmR]
      have he : z ≠ rhsBase+(i : ℤ) := by rcases hz' with hz'|hz' <;> omega
      simp only [Function.update_of_ne he]
      rfl
    · rw [hoW,payUnit_work,hmW,payUnit_work]
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RightHandSidePreparation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1200000 in
lemma right_hand_side_preparation_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width offset : ℕ) (enumBase rhsBase : ℤ) (hbase : 0 ≤ rhsBase)
    (e : Fin k → Fin n) (b : Fin n → ℝ) (st : MachineState)
    (hh : st.scalar.halted=false) (hz : st.scalar.core.ptrs 0=0)
    (hw : st.scalar.core.ptrs 41=(width : ℤ)) (hOff : st.scalar.core.ptrs 44=(offset : ℤ))
    (hEnumBase : st.scalar.core.ptrs 80=enumBase) (hRhsBase : st.scalar.core.ptrs 78=rhsBase)
    (hk : st.scalar.core.ptrs 77=(k : ℤ)) (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hb : ∀ v : Fin n, st.scalar.core.mem (vertexRecordAddress width v.val offset)=b v) :
    ∃ out, MachineEval m g ω rightHandSidePreparationCode st (k*(4*width+14)+2) out ∧
      out.scalar.core.ptrs 75=(k : ℤ) ∧
      (∀ j : Fin k, out.scalar.core.mem (rhsBase+(j.val : ℤ))=b (e j)) ∧
      (∀ z, z < rhsBase ∨ rhsBase+(k : ℤ) ≤ z → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(k*(4*width+14)+2 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let pre := payUnit (pointerWrite st 75 0)
  have ep : MachineEval m g ω (coreCode (.pset 75 0)) st 1 pre := pset_eval m g ω st 75 0 hh
  have h0 := (ep.pointer_frame 0 (by decide)).trans hz
  have h41 := (ep.pointer_frame 41 (by decide)).trans hw
  have h44 := (ep.pointer_frame 44 (by decide)).trans hOff
  have h80 := (ep.pointer_frame 80 (by decide)).trans hEnumBase
  have h78 := (ep.pointer_frame 78 (by decide)).trans hRhsBase
  have h77 := (ep.pointer_frame 77 (by decide)).trans hk
  have h75 : pre.scalar.core.ptrs 75=0 := by simp [pre,payUnit,pcSet,pointerWrite]
  obtain ⟨out,el,ho75,hoValues,hoFrame,hoI,hoQ,hoW,hoO,hoH⟩ :=
    right_hand_side_loop_exec m g ω width offset enumBase rhsBase hbase e b k 0 pre hh h0 h41 h44
      h80 h78 h75 h77 (by omega) hEnum hb
  have eRun : MachineEval m g ω rightHandSidePreparationCode st (k*(4*width+14)+2) out := by
    have ee := MachineEval.seq ep el
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,ho75,fun j => hoValues j (Nat.zero_le _),?_,hoI,hoQ,?_,hoO,hoH⟩
  · intro z hz'
    exact hoFrame z (by simpa only [Nat.cast_zero,add_zero] using hz')
  · rw [hoW]
    change st.work+1+(k*(4*width+14)+1 : ℕ)= _
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RightHandSideAssembly

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma SparseAssemblyState.rhs_frame {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {st out : MachineState} {u : ℕ} {base : ℤ} {k capacity : ℕ} {entries : List SparseEntry}
    (ex : MachineEval m g ω rightHandSidePreparationCode st u out)
    (h : SparseAssemblyState st base k capacity entries) (hc : entries.length ≤ capacity)
    (hI : out.scalar.integerMemory=st.scalar.integerMemory)
    (hR : ∀ z, z < base+3*(capacity : ℤ) → out.scalar.core.mem z=st.scalar.core.mem z) :
    SparseAssemblyState out base k capacity entries := by
  have hp (r : ℕ) (hr : r ∈ insert 74 solveBufferRegisters) : out.scalar.core.ptrs r=st.scalar.core.ptrs r :=
    ex.pointer_frame r (by revert r; decide)
  refine ⟨ex.solve_buffer_frame h.layout (by decide),?_,(hp 74 (by decide)).trans h.count⟩
  intro i hi
  obtain ⟨hr,hc',hv⟩ := h.contents i hi
  refine ⟨?_,?_,?_⟩
  · change out.scalar.integerMemory (out.scalar.core.ptrs 71+(i : ℤ))=entries[i].row
    rw [hp 71 (by decide),hI]
    exact hr
  · change out.scalar.integerMemory (out.scalar.core.ptrs 72+(i : ℤ))=entries[i].column
    rw [hp 72 (by decide),hI]
    exact hc'
  · change out.scalar.core.mem (out.scalar.core.ptrs 73+(i : ℤ))=entries[i].value
    rw [hp 73 (by decide)]
    rw [hR _ (by rw [h.layout.values]; omega)]
    exact hv

set_option maxHeartbeats 1600000 in
lemma right_hand_side_assembly_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width offset capacity : ℕ) (base enumBase : ℤ) (hbase : 0 ≤ base)
    (e : Fin k → Fin n) (b : Fin n → ℝ) (entries : List SparseEntry) (st : MachineState)
    (hh : st.scalar.halted=false) (h : SparseAssemblyState st base k capacity entries) (hc : entries.length ≤ capacity)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hOff : st.scalar.core.ptrs 44=(offset : ℤ)) (hEnumBase : st.scalar.core.ptrs 80=enumBase)
    (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hb : ∀ v : Fin n, st.scalar.core.mem (vertexRecordAddress width v.val offset)=b v) :
    ∃ out, MachineEval m g ω rightHandSidePreparationCode st (k*(4*width+14)+2) out ∧
      SparseAssemblyState out base k capacity entries ∧
      (∀ j : Fin k, out.scalar.core.mem (base+3*(capacity : ℤ)+(j.val : ℤ))=b (e j)) ∧
      (∀ z, z < base+3*(capacity : ℤ) ∨ base+3*(capacity : ℤ)+(k : ℤ) ≤ z → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(k*(4*width+14)+2 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  have hrhs : 0 ≤ base+3*(capacity : ℤ) := by positivity
  obtain ⟨out,ex,ho75,hoValues,hoFrame,hoI,hoQ,hoW,hoO,hoH⟩ :=
    right_hand_side_preparation_exec m g ω width offset enumBase (base+3*(capacity : ℤ)) hrhs e b st
      hh hz hw hOff hEnumBase h.layout.rhs h.layout.dimensionPointer hEnum hb
  exact ⟨out,ex,h.rhs_frame ex hc hoI (fun z hz => hoFrame z (Or.inl hz)),hoValues,hoFrame,hoI,hoQ,hoW,hoO,hoH⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.TypedSolveExecution

set_option autoImplicit false
open Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma typed_solve_instruction_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (r : SolveRegisters) (k q : ℕ)
    (hd : st.scalar.core.ptrs r.dimension=(k : ℤ)) (hl : st.scalar.core.ptrs r.length=(q : ℤ))
    (hk : 0<k) (hA : SDDM (suppliedMatrix st.scalar r k q)) :
    ∃ out, MachineEval m g ω (.atom (.solve r)) st 1 out ∧
      out.scalar.core.mem=(writeAnswer st.scalar r k ((suppliedMatrix st.scalar r k q)⁻¹ *ᵥ
        (fun i : Fin k => st.scalar.core.mem (st.scalar.core.ptrs r.rhs+i.val)))).core.mem ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.ptrs=st.scalar.core.ptrs ∧
      out.scalar.core.regs=st.scalar.core.regs ∧
      out.work=st.work+solveCharge m k q ∧ out.output=st.output ∧ out.scalar.halted=false := by
  have hdPos : 0<st.scalar.core.ptrs r.dimension := by rw [hd]; exact_mod_cast hk
  have hlNonneg : 0 ≤ st.scalar.core.ptrs r.length := by rw [hl]; positivity
  have hdimNat : (st.scalar.core.ptrs r.dimension).toNat=k := by rw [hd,Int.toNat_natCast]
  have hlenNat : (st.scalar.core.ptrs r.length).toNat=q := by rw [hl,Int.toNat_natCast]
  cases hdimNat
  cases hlenNat
  exact solve_instruction_exec m g ω st hh r hdPos hlNonneg hA

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PreparedPrincipalSolve

set_option autoImplicit false
open Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1200000 in
lemma prepared_principal_solve_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n)
    (ω : ℕ → Bool) (st : MachineState) (hh : st.scalar.halted=false)
    (base : ℤ) (capacity : ℕ) (α : ℝ) (hα : 0<α ∧ α<1)
    (e : Fin k → Fin n) (he : Function.Injective e) (hk : 0<k)
    (hd : ∀ i, 0<g.graph.degree (e i)) (entries : List SparseEntry)
    (h : SparseAssemblyState st base k capacity entries)
    (hA : suppliedMatrix st.scalar preparedSolveRegisters k entries.length=(LocalPush.Lα g.graph α).submatrix e e)
    (b : Fin n → ℝ) (hb : ∀ i : Fin k, st.scalar.core.mem (base+3*(capacity : ℤ)+(i.val : ℤ))=b (e i)) :
    ∃ out, MachineEval m g ω (.atom (.solve preparedSolveRegisters)) st 1 out ∧
      (∀ i : Fin k, out.scalar.core.mem (base+3*(capacity : ℤ)+(k : ℤ)+(i.val : ℤ))=
        solveOn g α (Finset.univ.image e) b (e i)) ∧
      (∀ z, z < base+3*(capacity : ℤ)+(k : ℤ) → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.ptrs=st.scalar.core.ptrs ∧
      out.scalar.core.regs=st.scalar.core.regs ∧
      out.work=st.work+solveCharge m k entries.length ∧ out.output=st.output ∧ out.scalar.halted=false := by
  have hSDDM : SDDM (suppliedMatrix st.scalar preparedSolveRegisters k entries.length) := by
    rw [hA]
    exact indexed_principal_SDDM g α hα e he hd
  obtain ⟨out,ex,hR,hI,hP,hRegs,hW,hO,hH⟩ := typed_solve_instruction_exec m g ω st hh
    preparedSolveRegisters k entries.length h.layout.dimensionPointer h.count hk hSDDM
  refine ⟨out,ex,?_,?_,hI,hP,hRegs,hW,hO,hH⟩
  · intro i
    rw [hR]
    have ha : st.scalar.core.ptrs preparedSolveRegisters.answer=base+3*(capacity : ℤ)+(k : ℤ) := h.layout.answer
    rw [← ha,writeAnswer_at,hA]
    have hb' : (fun j : Fin k => st.scalar.core.mem (st.scalar.core.ptrs preparedSolveRegisters.rhs+j.val))=
        (fun j : Fin k => b (e j)) := by
      funext j
      change st.scalar.core.mem (st.scalar.core.ptrs 78+(j.val : ℤ))=b (e j)
      rw [h.layout.rhs]
      exact hb j
    rw [hb']
    exact indexed_solveOn_eq g α e he b i
  · intro z hz
    rw [hR]
    apply writeAnswer_outside
    intro hz'
    have ha : st.scalar.core.ptrs preparedSolveRegisters.answer=base+3*(capacity : ℤ)+(k : ℤ) := h.layout.answer
    rw [ha] at hz'
    omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AssembledPrincipalSolve

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1600000 in
lemma assembled_principal_solve_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width offset capacity : ℕ) (base enumBase : ℤ) (hbase : 0 ≤ base)
    (α : ℝ) (hα : 0<α ∧ α<1) (e : Fin k → Fin n) (he : Function.Injective e)
    (hk : 0<k) (hd : ∀ i, 0<g.graph.degree (e i)) (b : Fin n → ℝ) (st : MachineState)
    (hh : st.scalar.halted=false) (h : SparseAssemblyState st base k capacity (principalEntries g α e))
    (hc : k+∑ i : Fin k, (g.neighbors (e i)).length ≤ capacity)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hOff : st.scalar.core.ptrs 44=(offset : ℤ)) (hEnumBase : st.scalar.core.ptrs 80=enumBase)
    (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hb : ∀ v : Fin n, st.scalar.core.mem (vertexRecordAddress width v.val offset)=b v) :
    ∃ out, MachineEval m g ω assembledPrincipalSolveCode st (k*(4*width+14)+3) out ∧
      (∀ i : Fin k, out.scalar.core.mem (base+3*(capacity : ℤ)+(k : ℤ)+(i.val : ℤ))=
        solveOn g α (Finset.univ.image e) b (e i)) ∧
      (∀ z, z < base+3*(capacity : ℤ) → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧
      (∀ r ∈ solveBufferRegisters, out.scalar.core.ptrs r=st.scalar.core.ptrs r) ∧
      out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+(k*(4*width+14)+2 : ℕ)+solveCharge m k (principalEntries g α e).length ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨pre,ep,hpState,hpValues,hpFrame,hpI,hpQ,hpW,hpO,hpH⟩ := right_hand_side_assembly_exec m g ω
    width offset capacity base enumBase hbase e b (principalEntries g α e) st hh h
    ((principal_entries_length_le g α e).trans hc) hz hw hOff hEnumBase hEnum hb
  have hpA : suppliedMatrix pre.scalar preparedSolveRegisters k (principalEntries g α e).length=
      (LocalPush.Lα g.graph α).submatrix e e :=
    (suppliedMatrix_decode _ _ _ _ hpState.contents).trans (principal_entries_decode g α e he)
  obtain ⟨out,es,hoValues,hoFrame,hoI,hoP,hoRegs,hoW,hoO,hoH⟩ := prepared_principal_solve_exec m g ω pre hpH
    base capacity α hα e he hk hd (principalEntries g α e) hpState hpA b hpValues
  have eRun : MachineEval m g ω assembledPrincipalSolveCode st (k*(4*width+14)+3) out := by
    have ee := MachineEval.seq ep es
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,eRun,hoValues,?_,hoI.trans hpI,?_,?_,?_,hoO.trans hpO,hoH⟩
  · intro z hz'
    exact (hoFrame z (by omega)).trans (hpFrame z (Or.inl hz'))
  · intro r hr
    rw [hoP]
    exact ep.pointer_frame r (by revert r; decide)
  · exact eRun.query_frame (by
      simp [assembledPrincipalSolveCode,rightHandSidePreparationCode,rightHandSideLoopCode,
        MachineCode.allAtoms,rightHandSideBodyCode_queryReadOnly,coreCode,queryReadOnly])
  · rw [hoW,hpW]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrincipalSolvePipeline

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2300000 in
lemma principal_solve_pipeline_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width offset capacity : ℕ) (base enumBase epoch : ℤ)
    (e : Fin k → Fin n) (he : Function.Injective e) (hk : 0<k) (hd : ∀ i, 0<g.graph.degree (e i))
    (α : ℝ) (hα : 0<α ∧ α<1) (b : Fin n → ℝ) (stored : Finset (Fin n))
    (h : SparseAssemblyState st base k capacity [])
    (hcap : k+∑ j : Fin k, (g.neighbors (e j)).length ≤ capacity)
    (hcache : GraphCache g st.scalar.integerMemory width stored base) (hmem : ∀ j, e j ∈ stored)
    (hTable : IndexPrefix st.scalar.integerMemory width epoch e k)
    (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hEnumBelow : ∀ j : Fin k, enumBase+(j.val : ℤ) < base)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 41=(width : ℤ))
    (hE : st.scalar.core.ptrs 53=epoch) (hbaseE : st.scalar.core.ptrs 80=enumBase)
    (hOff : st.scalar.core.ptrs 83=(offset : ℤ)) (hAlpha : st.scalar.core.mem 0=α)
    (hb : ∀ v : Fin n, st.scalar.core.mem (vertexRecordAddress width v.val offset)=b v) :
    ∃ steps out, MachineEval m g ω principalSolvePipelineCode st steps out ∧
      steps ≤ (12*width+59)*capacity+9 ∧
      (∀ i : Fin k, out.scalar.core.mem (base+3*(capacity : ℤ)+(k : ℤ)+(i.val : ℤ))=
        solveOn g α (Finset.univ.image e) b (e i)) ∧
      (∀ z, z < base → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ z, z < base → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.queries=st.scalar.queries ∧
      out.work ≤ st.work+((12*width+59)*capacity+8 : ℕ)+solveCharge m k (principalEntries g α e).length ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨u,pre,ep,hu,hpState,hpCache,hpTable,hpEnum,hpA,hpI,hpR,hpQ,hpW,hpO,hpH⟩ :=
    principal_matrix_assembly_exec m g ω st hh width capacity base enumBase epoch e he α stored h hcap
      hcache hmem hTable hEnum hEnumBelow hz hw hE hbaseE hAlpha
  have hbase : 0 ≤ base := by have hfb := hcache.freeBound; omega
  have hp0 := (ep.pointer_frame 0 (by decide)).trans hz
  have hp41 := (ep.pointer_frame 41 (by decide)).trans hw
  have hp80 := (ep.pointer_frame 80 (by decide)).trans hbaseE
  have hp83 := (ep.pointer_frame 83 (by decide)).trans hOff
  let mid := payUnit (pointerWrite pre 44 (offset : ℤ))
  have ec : MachineEval m g ω (coreCode (.pcopy 44 83)) pre 1 mid := by
    simpa only [coreCode,mid,hp83] using pcopy_eval m g ω pre 44 83 hpH
  have hmState : SparseAssemblyState mid base k capacity (principalEntries g α e) :=
    SparseAssemblyState.readOnly ec hpState (by decide) rfl rfl
  have hm44 : mid.scalar.core.ptrs 44=(offset : ℤ) := by simp [mid,payUnit,pcSet,pointerWrite]
  have hm0 := (ec.pointer_frame 0 (by decide)).trans hp0
  have hm41 := (ec.pointer_frame 41 (by decide)).trans hp41
  have hm80 := (ec.pointer_frame 80 (by decide)).trans hp80
  have hmB : ∀ v : Fin n, mid.scalar.core.mem (vertexRecordAddress width v.val offset)=b v := by
    intro v
    change pre.scalar.core.mem _=b v
    rw [hpR _ ((vertexRecordAddress_negative _ _ _).trans_le hbase)]
    exact hb v
  obtain ⟨out,es,hoValues,hoFrame,hoI,hoP,hoQ,hoW,hoO,hoH⟩ := assembled_principal_solve_exec m g ω
    width offset capacity base enumBase hbase α hα e he hk hd b mid hpH hmState hcap hm0 hm41 hm44 hm80 hpEnum hmB
  have hkc : k ≤ capacity := by omega
  have hcost : u+1+(k*(4*width+14)+2) ≤ (12*width+59)*capacity+8 := by
    have hmul := Nat.mul_le_mul_right (4*width+14) hkc
    nlinarith
  have eRun := MachineEval.seq ep (MachineEval.seq ec es)
  refine ⟨u+(1+(k*(4*width+14)+3)),out,eRun,by omega,hoValues,?_,?_,hoQ.trans hpQ,?_,hoO.trans hpO,hoH⟩
  · intro z hz'
    exact (congrFun hoI z).trans (hpI z hz')
  · intro z hz'
    exact (hoFrame z (by omega)).trans (hpR z hz')
  · rw [hoW]
    change pre.work+1+(k*(4*width+14)+2 : ℕ)+solveCharge m k (principalEntries g α e).length ≤ _
    rw [hpW]
    have hcost' : (u : ℝ≥0∞)+1+(k*(4*width+14)+2 : ℕ) ≤ ((12*width+59)*capacity+8 : ℕ) := by
      exact_mod_cast hcost
    calc
      st.work+u+1+(k*(4*width+14)+2 : ℕ)+solveCharge m k (principalEntries g α e).length =
          st.work+((u : ℝ≥0∞)+1+(k*(4*width+14)+2 : ℕ))+solveCharge m k (principalEntries g α e).length := by ac_rfl
      _ ≤ _ := by gcongr

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CachedPrincipalSolve

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 2500000 in
lemma cached_principal_solve_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width offset : ℕ) (hw9 : 9 ≤ width) (base enumBase epoch : ℤ) (hEnumBase : 0 ≤ enumBase)
    (e : Fin k → Fin n) (he : Function.Injective e) (hk : 0<k) (hd : ∀ i, 0<g.graph.degree (e i))
    (α : ℝ) (hα : 0<α ∧ α<1) (b : Fin n → ℝ) (stored : Finset (Fin n))
    (st : MachineState) (hh : st.scalar.halted=false)
    (hcache : GraphCache g st.scalar.integerMemory width stored base) (hmem : ∀ j, e j ∈ stored)
    (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hEnumBelow : ∀ j : Fin k, enumBase+(j.val : ℤ) < base)
    (hz : st.scalar.core.ptrs 0=0) (hw : st.scalar.core.ptrs 50=(width : ℤ))
    (hb : st.scalar.core.ptrs 80=enumBase) (hkp : st.scalar.core.ptrs 77=(k : ℤ))
    (hf : st.scalar.core.ptrs 20=base) (hE : st.scalar.core.ptrs 53=epoch)
    (hOff : st.scalar.core.ptrs 83=(offset : ℤ)) (hAlpha : st.scalar.core.mem 0=α)
    (hbRecords : ∀ v : Fin n, st.scalar.core.mem (vertexRecordAddress width v.val offset)=b v)
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress width v.val 7) ≤ epoch) :
    let capacity := k+∑ j : Fin k, (g.neighbors (e j)).length
    ∃ steps out, MachineEval m g ω cachedPrincipalSolveCode st steps out ∧
      steps ≤ (24*width+100)*capacity+29 ∧
      SolveBufferLayout out.scalar base k capacity ∧
      GraphCache g out.scalar.integerMemory width stored base ∧
      IndexPrefix out.scalar.integerMemory width (epoch+1) e k ∧
      out.scalar.core.ptrs 53=epoch+1 ∧
      (∀ i : Fin k, out.scalar.core.mem (base+3*(capacity : ℤ)+(k : ℤ)+(i.val : ℤ))=
        solveOn g α (Finset.univ.image e) b (e i)) ∧
      (∀ z, 0 ≤ z → z < base → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      (∀ v : Fin n, ∀ field < width, field ≠ 7 → field ≠ 8 →
        out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field)) ∧
      (∀ z, z < base → out.scalar.core.mem z=st.scalar.core.mem z) ∧
      out.scalar.queries=st.scalar.queries ∧
      out.work ≤ st.work+((24*width+100)*capacity+28 : ℕ)+solveCharge m k (principalEntries g α e).length ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  dsimp only
  let capacity := k+∑ j : Fin k, (g.neighbors (e j)).length
  obtain ⟨pre,ep,hpState,hpCache,hpTable,hpEnum,hp41,hp53,hpPos,hpCacheFields,hpFields,hpR,hpQ,hpW,hpO,hpH⟩ :=
    local_solve_preparation_exec m g ω width hw9 base enumBase epoch hEnumBase e he stored st hh hcache hmem
      hEnum hz hw hb hkp hf hE hbound
  have hp0 := (ep.pointer_frame 0 (by decide)).trans hz
  have hp80 := (ep.pointer_frame 80 (by decide)).trans hb
  have hp83 := (ep.pointer_frame 83 (by decide)).trans hOff
  have hpAlpha : pre.scalar.core.mem 0=α := by rw [hpR]; exact hAlpha
  have hpRecords : ∀ v : Fin n, pre.scalar.core.mem (vertexRecordAddress width v.val offset)=b v := by rw [hpR]; exact hbRecords
  obtain ⟨u,out,es,hu,hoValues,hoI,hoR,hoQ,hoW,hoO,hoH⟩ := principal_solve_pipeline_exec m g ω pre hpH
    width offset capacity base enumBase (epoch+1) e he hk hd α hα b stored hpState (by rfl)
      hpCache hmem hpTable hpEnum hEnumBelow hp0 hp41 hp53 hp80 hp83 hpAlpha hpRecords
  have hkc : k ≤ capacity := by dsimp [capacity]; omega
  have hunit : k*(12*width+41)+20+((12*width+59)*capacity+8) ≤ (24*width+100)*capacity+28 := by
    have hmul := Nat.mul_le_mul_right (12*width+41) hkc
    nlinarith
  have hsteps : k*(12*width+41)+20+u ≤ (24*width+100)*capacity+29 := by omega
  have hbase : 0 ≤ base := by have hb := hcache.freeBound; omega
  have eRun := MachineEval.seq ep es
  refine ⟨k*(12*width+41)+20+u,out,eRun,hsteps,es.solve_buffer_frame hpState.layout (by decide),
    hpCache.below_frame hoI,?_,?_,hoValues,?_,?_,?_,hoQ.trans hpQ,?_,hoO.trans hpO,hoH⟩
  · exact hpTable.frame
      (fun v => hoI _ ((vertexRecordAddress_negative _ _ _).trans_le hbase))
      (fun v => hoI _ ((vertexRecordAddress_negative _ _ _).trans_le hbase))
  · exact (es.pointer_frame 53 (by decide)).trans hp53
  · intro z hz' hzB
    exact (hoI z hzB).trans (hpPos z hz')
  · intro v field hf' hf7 hf8
    exact (hoI _ ((vertexRecordAddress_negative _ _ _).trans_le hbase)).trans (hpFields v field hf' hf7 hf8)
  · intro z hz'
    exact (hoR z hz').trans (congrFun hpR z)
  · rw [hpW] at hoW
    have hc : ((k*(12*width+41)+20 : ℕ) : ℝ≥0∞)+((12*width+59)*capacity+8 : ℕ) ≤
        ((24*width+100)*capacity+28 : ℕ) := by exact_mod_cast hunit
    calc
      out.work ≤ st.work+(k*(12*width+41)+20 : ℕ)+((12*width+59)*capacity+8 : ℕ)+
          solveCharge m k (principalEntries g α e).length := hoW
      _ = st.work+((k*(12*width+41)+20 : ℕ)+((12*width+59)*capacity+8 : ℕ))+
          solveCharge m k (principalEntries g α e).length := by ac_rfl
      _ ≤ _ := by gcongr

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ScopedSolveRHS

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma solveOn_congr_on {n : ℕ} (g : InputGraph n) (α : ℝ) (T : Finset (Fin n))
    (b c : Fin n → ℝ) (h : ∀ v ∈ T, b v=c v) : solveOn g α T b=solveOn g α T c := by
  have he : (fun v : T => b v)=(fun v : T => c v) := by
    funext v
    exact h v v.property
  unfold solveOn
  rw [he]

lemma solveOn_enumeration_records {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n)
    (R : ℤ → ℝ) (width offset : ℕ) (b : Fin n → ℝ)
    (h : ∀ i, R (vertexRecordAddress width (e i).val offset)=b (e i)) :
    solveOn g α (Finset.univ.image e) (fun v => R (vertexRecordAddress width v.val offset))=
      solveOn g α (Finset.univ.image e) b := by
  apply solveOn_congr_on
  intro v hv
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
  exact h i

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

-- Proof module: Solutions.SolveIterationBuffers

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

structure SolveIterationBuffers {n k : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {machine : MachineState}
    (memory : RecursiveMachineMemory g s α ε ell length logical machine)
    (enumBase answerBase : ℤ) (e : Fin k → Fin n) (h : Fin n → ℝ) : Prop where
  enumNonnegative : 0 ≤ enumBase
  answerNonnegative : 0 ≤ answerBase
  enumBelow : ∀ i : Fin k, enumBase+(i.val : ℤ) < machine.scalar.core.ptrs 20
  answerBelow : ∀ i : Fin k, answerBase+(i.val : ℤ) < machine.scalar.core.ptrs 20
  enumForeign : ∀ i : Fin k, ∀ j, ∀ hj : j ≤ logical.top, enumBase+(i.val : ℤ) ∉ (memory.frames j hj).owned
  enumeration : EnumerationStored machine.scalar.integerMemory enumBase e
  answers : ∀ i : Fin k, machine.scalar.core.mem (answerBase+(i.val : ℤ))=h (e i)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CachedPrincipalSolveMemory

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 14000000 in
lemma cached_principal_solve_memory_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length offset : ℕ)
    (base enumBase epoch : ℤ) (hEnumBase : 0 ≤ enumBase)
    (e : Fin k → Fin n) (he : Function.Injective e) (hk : 0<k) (hd : ∀ i, 0<g.graph.degree (e i))
    (hα : 0<α ∧ α<1) (b : Fin n → ℝ) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hmem : ∀ j, e j ∈ logical.stored) (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hEnumBelow : ∀ i : Fin k, enumBase+(i.val : ℤ) < base)
    (hForeign : ∀ i : Fin k, ∀ j, ∀ hj : j ≤ logical.top, enumBase+(i.val : ℤ) ∉ (pm.frames j hj).owned)
    (hb : st.scalar.core.ptrs 80=enumBase) (hkp : st.scalar.core.ptrs 77=(k : ℤ))
    (hf : st.scalar.core.ptrs 20=base) (hE : st.scalar.core.ptrs 53=epoch)
    (hOff : st.scalar.core.ptrs 83=(offset : ℤ))
    (hbRecords : ∀ i : Fin k, st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) (e i).val offset)=b (e i))
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch) :
    let capacity := k+∑ i : Fin k, (g.neighbors (e i)).length
    let answerBase := base+3*(capacity : ℤ)+(k : ℤ)
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω cachedPrincipalSolveCode st steps out ∧
      steps ≤ (24*(16*(ell+3))+100)*capacity+29 ∧
      SolveIterationBuffers memory enumBase answerBase e (solveOn g α (Finset.univ.image e) b) ∧
      memory.queueMass=pm.queueMass ∧ SolveBufferLayout out.scalar base k capacity ∧
      out.scalar.core.ptrs 80=enumBase ∧ out.scalar.core.ptrs 53=epoch+1 ∧
      out.work ≤ st.work+((24*(16*(ell+3))+100)*capacity+28 : ℕ)+solveCharge m k (principalEntries g α e).length ∧
      out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch+1) := by
  dsimp only
  let width := 16*(ell+3)
  let capacity := k+∑ i : Fin k, (g.neighbors (e i)).length
  let raw := fun v : Fin n => st.scalar.core.mem (vertexRecordAddress width v.val offset)
  have hCache : GraphCache g st.scalar.integerMemory width logical.stored base := by rw [←hf]; exact pm.graphCache
  obtain ⟨steps,out,ex,hSteps,hLayout,hOutCache,hTable,hEpoch,hValues,hI,hV,hR,hQ,hWork,hOutput,hHalt⟩ :=
    cached_principal_solve_exec m g ω width offset (by dsimp [width]; omega) base enumBase epoch hEnumBase
      e he hk hd α hα raw logical.stored st hh hCache hmem hEnum hEnumBelow pm.zero pm.width hb hkp hf hE hOff pm.alphaMemory (by intros; rfl) hbound
  have hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 := by rw [hf,hLayout.free]; omega
  let memory := pm.solve_frame hDepth hFree
    (by intro z hz hBelow; exact hI z hz (by rw [←hf]; exact hBelow)) hV
    (by intro z hBelow; exact hR z (by rw [←hf]; exact hBelow))
    (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> exact ex.pointer_frame _ (by decide))
    (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> exact ex.real_register_frame _ (by decide)) hOutput
  have hSolve : solveOn g α (Finset.univ.image e) raw=solveOn g α (Finset.univ.image e) b :=
    solveOn_enumeration_records g α e st.scalar.core.mem width offset b hbRecords
  have hBase : 0 ≤ base := by rw [←hf]; have := pm.allocator; omega
  have buffers : SolveIterationBuffers memory enumBase (base+3*(capacity : ℤ)+(k : ℤ)) e (solveOn g α (Finset.univ.image e) b) := by
    refine ⟨hEnumBase,by omega,?_,?_,?_,?_,?_⟩
    · intro i
      exact (hEnumBelow i).trans_le (by rw [←hf]; exact hFree)
    · intro i
      rw [hLayout.free]
      have hi := i.isLt
      omega
    · intro i j hj
      exact hForeign i j hj
    · intro i
      rw [hI _ (by have := Int.natCast_nonneg i.val; omega) (hEnumBelow i)]
      exact hEnum i
    · intro i
      rw [hValues,hSolve]
  refine ⟨steps,out,memory,ex,hSteps,buffers,rfl,hLayout,?_,hEpoch,hWork,hOutput,hHalt,hTable.1⟩
  exact (ex.pointer_frame 80 (by decide)).trans hb

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

-- Proof module: Solutions.JointSolveIterationRead

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma joint_solve_iteration_read_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (enumBase answerBase : ℤ) (index : ℕ) (v : Fin n) (δ : ℝ)
    (h140 : st.scalar.core.ptrs 140=enumBase) (h141 : st.scalar.core.ptrs 141=answerBase)
    (h143 : st.scalar.core.ptrs 143=(index : ℤ))
    (hEnum : st.scalar.integerMemory (enumBase+(index : ℤ))=(v.val : ℤ))
    (hAnswer : st.scalar.core.mem (answerBase+(index : ℤ))=δ) :
    ∃ out, MachineEval m g ω jointSolveIterationReadCode st 4 out ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧ out.scalar.core.regs 40=δ ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+4 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let out := linearRun m g ω jointSolveIterationReadInstructions st
  obtain ⟨ex,hWork,hHalt⟩ := linear_execute m g ω jointSolveIterationReadInstructions
    (by simp [jointSolveIterationReadInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨out,ex,?_,?_,?_,?_,ex.query_frame (by decide),hWork,?_,hHalt⟩
  all_goals simp [out,linearRun,jointSolveIterationReadInstructions,atomState,machineStep,pcSet,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,h140,h141,h143,hEnum,hAnswer]

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

-- Proof module: Solutions.VertexListCapacity

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertex_list_capacity {n : ℕ} (g : InputGraph n) (vertices : List (Fin n)) (hn : vertices.Nodup) :
    vertices.length+∑ i : Fin vertices.length, (g.neighbors (vertexEnumeration vertices i)).length=
      volumeNat g vertices.toFinset+vertices.toFinset.card := by
  rw [←vertex_enumeration_domain]
  rw [←joint_iteration_volume_domain g _ (vertexEnumeration_injective vertices hn),joint_iteration_volume_full,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolveChargeMonotone

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation

lemma solveCharge_mono (m : SolveModel) {k q k' q' : ℕ} (hk : k ≤ k') (hq : q ≤ q') :
    solveCharge m k q ≤ solveCharge m k' q' := by
  have hs : (k+q : ℝ) ≤ (k'+q' : ℝ) := by exact_mod_cast Nat.add_le_add hk hq
  have hlog : 1+Real.log (2+(k+q : ℝ)) ≤ 1+Real.log (2+(k'+q' : ℝ)) := by
    exact add_le_add le_rfl (Real.log_le_log (by positivity) (by linarith))
  have hnonneg : 0 ≤ 1+Real.log (2+(k+q : ℝ)) := by
    have hbase : (1 : ℝ) ≤ 2+(k+q : ℝ) := by
      have hn : (0 : ℝ) ≤ (k+q : ℝ) := by positivity
      linarith
    have hl : 0 ≤ Real.log (2+(k+q : ℝ)) := Real.log_nonneg hbase
    linarith
  have hp : (1+Real.log (2+(k+q : ℝ)))^m.logPower ≤ (1+Real.log (2+(k'+q' : ℝ)))^m.logPower :=
    pow_le_pow_left₀ hnonneg hlog _
  have hm : m.constant*(k+q : ℝ)*(1+Real.log (2+(k+q : ℝ)))^m.logPower ≤
      m.constant*(k'+q' : ℝ)*(1+Real.log (2+(k'+q' : ℝ)))^m.logPower :=
    mul_le_mul (mul_le_mul_of_nonneg_left hs m.positive.le) hp (pow_nonneg hnonneg _)
      (mul_nonneg m.positive.le (by positivity))
  unfold solveCharge
  exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal hm)

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootComponentPrelude

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma root_component_prelude_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω rootComponentPreludeRoutine.code st 3 out ∧
      out.scalar.core.ptrs 90=st.scalar.integerMemory (levelHeaderAddress 0 1) ∧ out.scalar.core.ptrs 83=2 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+3 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨out,ex,hP,hI,hR,hW,hO,hH⟩ := rootComponentPreludeRoutine.execute m g ω st hh
  refine ⟨out,ex,?_,?_,hI,hR,hW,hO,hH⟩
  all_goals rw [hP]; simp [rootComponentPreludeRoutine,PointerRoutine.sequence,PointerRoutine.run,
    PointerOp.update,PointerOp.destination,PointerOp.result,levelHeaderAddress]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolveAnswerOutputBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 5000000 in
lemma solve_answer_output_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width : ℕ) (enumBase answerBase : ℤ) (index : ℕ) (v : Fin n) (α δ : ℝ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (h41 : st.scalar.core.ptrs 41=(width : ℤ))
    (h140 : st.scalar.core.ptrs 140=enumBase) (h141 : st.scalar.core.ptrs 141=answerBase)
    (h143 : st.scalar.core.ptrs 143=(index : ℤ))
    (hEnum : st.scalar.integerMemory (enumBase+(index : ℤ))=(v.val : ℤ))
    (hAnswer : st.scalar.core.mem (answerBase+(index : ℤ))=δ)
    (hDegree : st.scalar.integerMemory (vertexRecordAddress width v.val 0)=((g.neighbors v).length : ℤ))
    (h30 : st.scalar.core.regs 30=α) (h31 : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω solveAnswerOutputBodyCode st (4*width+19) out ∧
      out.scalar.core.ptrs 143=((index+1 : ℕ) : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*width+19 : ℕ) ∧
      out.output=st.output++[((v.val : ℤ),α*((g.neighbors v).length : ℝ)*δ)] ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a40,aR40,aI,aR,aQ,aW,aO,aH⟩ := joint_solve_iteration_read_exec m g ω st hh enumBase answerBase index v δ h140 h141 h143 hEnum hAnswer
  have a0 := (ea.pointer_frame 0 (by decide)).trans h0
  have a41 := (ea.pointer_frame 41 (by decide)).trans h41
  obtain ⟨b,eb,b60,bI,bR,bQ,bW,bO,bH⟩ := vertex_field_read_exec m g ω a aH width v.val 0 60 a0 a40 a41
  have bDegree : b.scalar.core.ptrs 60=((g.neighbors v).length : ℤ) := by rw [b60,aI]; exact hDegree
  have b40 := (eb.pointer_frame 40 (by decide)).trans a40
  have b30 := (eb.real_register_frame 30 (by decide)).trans ((ea.real_register_frame 30 (by decide)).trans h30)
  have b31 := (eb.real_register_frame 31 (by decide)).trans ((ea.real_register_frame 31 (by decide)).trans h31)
  have bR40 := (eb.real_register_frame 40 (by decide)).trans aR40
  let c := payUnit (realWrite b 10 δ)
  have ec : MachineEval m g ω (coreCode (.mul 10 40 31)) b 1 c := by
    simpa only [coreCode,RealOperation.instruction,RealOperation.value,bR40,b31,mul_one,c] using binary_eval m g ω b .mul 10 40 31 bH
  have c10 : c.scalar.core.regs 10=δ := by simp [c,payUnit,pcSet,realWrite]
  obtain ⟨d,ed,dI,dR,dQ,dW,dO,dH⟩ := push_output_scalar_exec m g ω c bH v α δ (g.neighbors v).length b40 bDegree b30 c10
  let out := payUnit (pointerWrite d 143 (d.scalar.core.ptrs 143+1))
  have ef : MachineEval m g ω (coreCode (.pinc 143)) d 1 out := pinc_eval m g ω d 143 dH
  have ex : MachineEval m g ω solveAnswerOutputBodyCode st (4*width+19) out := by
    have ee := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed ef)))
    convert ee using 1 <;> (first | rfl | ring)
  refine ⟨out,ex,?_,dI.trans (bI.trans aI),dR.trans (bR.trans aR),ex.query_frame (by decide),?_,?_,dH⟩
  · have d143 := (ed.pointer_frame 143 (by decide)).trans ((ec.pointer_frame 143 (by decide)).trans
      ((eb.pointer_frame 143 (by decide)).trans ((ea.pointer_frame 143 (by decide)).trans h143)))
    simp [out,payUnit,pcSet,pointerWrite,d143]
  · change d.work+1= _
    rw [dW]
    change b.work+1+4+1= _
    rw [bW,aW]
    push_cast
    ring
  · change d.output= _
    rw [dO]
    change b.output++_ = _
    rw [bO,aO]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolveAnswerOutputLoop

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def solveAnswerOutputList {n k : ℕ} (g : InputGraph n) (e : Fin k → Fin n) (α : ℝ) (h : Fin n → ℝ)
    (index count : ℕ) (hBound : index+count ≤ k) : SparseOutput :=
  List.ofFn (fun i : Fin count =>
    let v := e ⟨index+i.val,by omega⟩
    ((v.val : ℤ),α*((g.neighbors v).length : ℝ)*h v))

lemma solve_answer_output_list_succ {n k : ℕ} (g : InputGraph n) (e : Fin k → Fin n) (α : ℝ) (h : Fin n → ℝ)
    (index count : ℕ) (hBound : index+(count+1) ≤ k) :
    solveAnswerOutputList g e α h index (count+1) hBound=
      (((e ⟨index,by omega⟩).val : ℤ),α*((g.neighbors (e ⟨index,by omega⟩)).length : ℝ)*h (e ⟨index,by omega⟩))::
      solveAnswerOutputList g e α h (index+1) count (by omega) := by
  unfold solveAnswerOutputList
  rw [List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn
  funext i
  have he : index+(i.val+1)=(index+1)+i.val := by omega
  simp only [Fin.val_succ,he]

set_option maxHeartbeats 7000000 in
lemma solve_answer_output_loop_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width : ℕ) (enumBase answerBase : ℤ) (e : Fin k → Fin n) (α : ℝ) (h : Fin n → ℝ)
    (index count : ℕ) (hCount : index+count=k)
    (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (h41 : st.scalar.core.ptrs 41=(width : ℤ))
    (h140 : st.scalar.core.ptrs 140=enumBase) (h141 : st.scalar.core.ptrs 141=answerBase)
    (h142 : st.scalar.core.ptrs 142=(k : ℤ)) (h143 : st.scalar.core.ptrs 143=(index : ℤ))
    (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hAnswer : ∀ i : Fin k, st.scalar.core.mem (answerBase+(i.val : ℤ))=h (e i))
    (hDegree : ∀ i : Fin k, st.scalar.integerMemory (vertexRecordAddress width (e i).val 0)=((g.neighbors (e i)).length : ℤ))
    (h30 : st.scalar.core.regs 30=α) (h31 : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω solveAnswerOutputLoopCode st ((4*width+21)*count+1) out ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+((4*width+21)*count+1 : ℕ) ∧
      out.output=st.output++solveAnswerOutputList g e α h index count hCount.le ∧ out.scalar.halted=false := by
  induction count generalizing st index with
  | zero =>
    have hi : index=k := by omega
    refine ⟨payUnit st,MachineEval.pointerDone hh (by rw [h142,h143,hi]),rfl,rfl,rfl,by simp,?_,hh⟩
    simp [solveAnswerOutputList,payUnit,pcSet]
  | succ count ih =>
    have hi : index < k := by omega
    let i : Fin k := ⟨index,hi⟩
    obtain ⟨mid,eb,hm143,hmI,hmR,hmQ,hmW,hmO,hmH⟩ :=
      solve_answer_output_body_exec m g ω width enumBase answerBase index (e i) α (h (e i))
        (payUnit st) hh h0 h41 h140 h141 h143 (hEnum i) (hAnswer i) (hDegree i) h30 h31
    have hm0 := (eb.pointer_frame 0 (by decide)).trans h0
    have hm41 := (eb.pointer_frame 41 (by decide)).trans h41
    have hm140 := (eb.pointer_frame 140 (by decide)).trans h140
    have hm141 := (eb.pointer_frame 141 (by decide)).trans h141
    have hm142 := (eb.pointer_frame 142 (by decide)).trans h142
    have hm30 := (eb.real_register_frame 30 (by decide)).trans h30
    have hm31 := (eb.real_register_frame 31 (by decide)).trans h31
    have hmEnum : EnumerationStored mid.scalar.integerMemory enumBase e := by rw [hmI]; exact hEnum
    have hmAnswer : ∀ j : Fin k, mid.scalar.core.mem (answerBase+(j.val : ℤ))=h (e j) := by rw [hmR]; exact hAnswer
    have hmDegree : ∀ j : Fin k, mid.scalar.integerMemory (vertexRecordAddress width (e j).val 0)=((g.neighbors (e j)).length : ℤ) := by rw [hmI]; exact hDegree
    obtain ⟨out,er,hoI,hoR,hoQ,hoW,hoO,hoH⟩ := ih (index+1) (by omega) (payUnit mid) hmH
      hm0 hm41 hm140 hm141 hm142 hm143 hmEnum hmAnswer hmDegree hm30 hm31
    have ex : MachineEval m g ω solveAnswerOutputLoopCode st ((4*width+21)*(count+1)+1) out := by
      have ee := MachineEval.pointerNext (r:=142) (s:=143) hh (by rw [h142,h143]; omega) eb er
      convert ee using 1 <;> (first | rfl | ring)
    refine ⟨out,ex,hoI.trans hmI,hoR.trans hmR,hoQ.trans hmQ,?_,?_,hoH⟩
    · rw [hoW,payUnit_work,hmW,payUnit_work]
      push_cast
      ring
    · rw [hoO]
      change mid.output++_= _
      rw [hmO,solve_answer_output_list_succ]
      simp only [payUnit,pcSet,List.append_assoc,List.singleton_append]
      rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolveAnswerOutputExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 7000000 in
lemma solve_answer_output_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (e : Fin k → Fin n) (h : Fin n → ℝ) (enumBase answerBase : ℤ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (buffers : SolveIterationBuffers pm enumBase answerBase e h)
    (hStored : ∀ i : Fin k, e i ∈ logical.stored)
    (h80 : st.scalar.core.ptrs 80=enumBase) (h79 : st.scalar.core.ptrs 79=answerBase) (h77 : st.scalar.core.ptrs 77=(k : ℤ)) :
    ∃ out, MachineEval m g ω solveAnswerOutputCode st ((4*(16*(ell+3))+21)*k+6) out ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+((4*(16*(ell+3))+21)*k+6 : ℕ) ∧
      out.output=solveAnswerOutputList g e α h 0 k (by omega) ∧ out.scalar.halted=false := by
  obtain ⟨pre,ep,hP,hI,hR,hW,hO,hH⟩ := solveAnswerOutputInitRoutine.execute m g ω st hh
  have ep5 : MachineEval m g ω solveAnswerOutputInitRoutine.code st 5 pre := ep
  have h140 : pre.scalar.core.ptrs 140=enumBase := by
    rw [hP]; simp [solveAnswerOutputInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,h80]
  have h141 : pre.scalar.core.ptrs 141=answerBase := by
    rw [hP]; simp [solveAnswerOutputInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,h79]
  have h142 : pre.scalar.core.ptrs 142=(k : ℤ) := by
    rw [hP]; simp [solveAnswerOutputInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,h77]
  have h143 : pre.scalar.core.ptrs 143=0 := by
    rw [hP]; simp [solveAnswerOutputInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result]
  have h41 : pre.scalar.core.ptrs 41=((16*(ell+3) : ℕ) : ℤ) := by
    rw [hP]; simp [solveAnswerOutputInitRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,pm.width]
  have h0 := (ep.pointer_frame 0 (by decide)).trans pm.zero
  have h30 := (ep.real_register_frame 30 (by decide)).trans pm.alphaRegister
  have h31 := (ep.real_register_frame 31 (by decide)).trans pm.one
  have hEnum : EnumerationStored pre.scalar.integerMemory enumBase e := by rw [hI]; exact buffers.enumeration
  have hAnswer : ∀ i : Fin k, pre.scalar.core.mem (answerBase+(i.val : ℤ))=h (e i) := by rw [hR]; exact buffers.answers
  have hDegree : ∀ i : Fin k, pre.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) (e i).val 0)=((g.neighbors (e i)).length : ℤ) := by
    intro i
    rw [hI]
    apply pm.knownDegree
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hStored i))
  obtain ⟨out,el,hoI,hoR,hoQ,hoW,hoO,hoH⟩ := solve_answer_output_loop_exec m g ω (16*(ell+3)) enumBase answerBase e α h 0 k (by omega)
    pre hH h0 h41 h140 h141 h142 h143 hEnum hAnswer hDegree h30 h31
  have ex : MachineEval m g ω solveAnswerOutputCode st ((4*(16*(ell+3))+21)*k+6) out := by
    have ee := MachineEval.seq ep5 el
    convert ee using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,hoI.trans hI,hoR.trans hR,hoQ.trans (ep.query_frame (by decide)),?_,?_,hoH⟩
  · rw [hoW,hW]
    change st.work+5+_= _
    push_cast
    ring
  · rw [hoO,hO,pm.output,List.nil_append]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolveAnswerOutputDenotation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma solve_answer_output_list_full {n k : ℕ} (g : InputGraph n) (e : Fin k → Fin n) (α : ℝ) (h : Fin n → ℝ) :
    solveAnswerOutputList g e α h 0 k (by omega)=
      (List.ofFn e).map (fun v => ((v.val : ℤ),α*((g.neighbors v).length : ℝ)*h v)) := by
  simp only [solveAnswerOutputList,Nat.zero_add,List.map_ofFn,Function.comp_apply]
  rfl

lemma solve_answer_output_potential {n k : ℕ} (g : InputGraph n) (e : Fin k → Fin n) (α : ℝ) (h : Fin n → ℝ)
    (he : Function.Injective e) (hSupport : ∀ v ∉ Finset.univ.image e, h v=0) :
    outputVector (solveAnswerOutputList g e α h 0 k (by omega))=potentialOutput g.graph α h := by
  classical
  rw [solve_answer_output_list_full]
  funext v
  rw [output_vertex_list (List.ofFn e) (List.nodup_ofFn_ofInjective he)]
  have hMember : v ∈ List.ofFn e ↔ v ∈ Finset.univ.image e := by
    simp only [List.mem_ofFn,Finset.mem_image,Finset.mem_univ,true_and]
  by_cases hv : v ∈ List.ofFn e
  · simp [hv,potentialOutput,LocalPush.deg,input_degree,mul_assoc]
  · have hz : h v=0 := hSupport v (by intro hm; exact hv (hMember.mpr hm))
    simp [hv,potentialOutput,hz]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CachedSolveOutputExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 12000000 in
lemma cached_solve_output_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length offset : ℕ)
    (base enumBase epoch : ℤ) (hEnumBase : 0 ≤ enumBase)
    (e : Fin k → Fin n) (he : Function.Injective e) (hk : 0<k) (hd : ∀ i, 0<g.graph.degree (e i))
    (hα : 0<α ∧ α<1) (b : Fin n → ℝ) (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hmem : ∀ j, e j ∈ logical.stored) (hEnum : EnumerationStored st.scalar.integerMemory enumBase e)
    (hEnumBelow : ∀ i : Fin k, enumBase+(i.val : ℤ) < base)
    (hForeign : ∀ i : Fin k, ∀ j, ∀ hj : j ≤ logical.top, enumBase+(i.val : ℤ) ∉ (pm.frames j hj).owned)
    (hb : st.scalar.core.ptrs 80=enumBase) (hkp : st.scalar.core.ptrs 77=(k : ℤ))
    (hf : st.scalar.core.ptrs 20=base) (hE : st.scalar.core.ptrs 53=epoch)
    (hOff : st.scalar.core.ptrs 83=(offset : ℤ))
    (hbRecords : ∀ i : Fin k, st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) (e i).val offset)=b (e i))
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch) :
    let capacity := k+∑ i : Fin k, (g.neighbors (e i)).length
    let numericCost := (24*(16*(ell+3))+100)*capacity+28
    let outputCost := (4*(16*(ell+3))+21)*k+6
    ∃ steps out, MachineEval m g ω cachedSolveOutputCode st steps out ∧
      steps ≤ numericCost+outputCost+1 ∧
      outputVector out.output=potentialOutput g.graph α (solveOn g α (Finset.univ.image e) b) ∧
      out.work ≤ st.work+(numericCost+outputCost : ℕ)+solveCharge m k (principalEntries g α e).length ∧
      out.scalar.halted=false := by
  dsimp only
  obtain ⟨a,pre,preMemory,ep,ha,buffers,hMass,hLayout,h80,h53,hWorkPre,hOutputPre,hHaltPre,hMarks⟩ :=
    cached_principal_solve_memory_exec m g ω logical s α ε ell length offset base enumBase epoch hEnumBase
      e he hk hd hα b st hh pm hDepth hmem hEnum hEnumBelow hForeign hb hkp hf hE hOff hbRecords hbound
  obtain ⟨out,eo,hoI,hoR,hoQ,hoW,hoO,hoH⟩ := solve_answer_output_exec m g ω logical s α ε ell length e
    (solveOn g α (Finset.univ.image e) b) enumBase _ pre hHaltPre preMemory buffers hmem h80 hLayout.answer hLayout.dimensionPointer
  have hSupport : ∀ v ∉ Finset.univ.image e, solveOn g α (Finset.univ.image e) b v=0 := by
    intro v hv
    simp only [solveOn,dif_neg hv]
  refine ⟨a+((4*(16*(ell+3))+21)*k+6),out,MachineEval.seq ep eo,by omega,?_,?_,hoH⟩
  · rw [hoO]
    exact solve_answer_output_potential g e α _ he hSupport
  · rw [hoW]
    calc
      pre.work+((4*(16*(ell+3))+21)*k+6 : ℕ) ≤
          (st.work+((24*(16*(ell+3))+100)*(k+∑ i : Fin k, (g.neighbors (e i)).length)+28 : ℕ)+
          solveCharge m k (principalEntries g α e).length)+((4*(16*(ell+3))+21)*k+6 : ℕ) := add_le_add hWorkPre le_rfl
      _ = _ := by push_cast; ac_rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ListSolveOutputExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 14000000 in
lemma list_solve_output_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length offset : ℕ)
    (vertices : List (Fin n)) (head epoch : ℤ) (F : Finset ℤ)
    (hNodup : vertices.Nodup) (hNonempty : 0<vertices.length)
    (hd : ∀ v ∈ vertices, 0<g.graph.degree v) (hα : 0<α ∧ α<1) (b : Fin n → ℝ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hmem : ∀ v ∈ vertices, v ∈ logical.stored)
    (hhp : st.scalar.core.ptrs 90=head)
    (hList : VertexListRep st.scalar.integerMemory head vertices F)
    (hBelow : ∀ z ∈ F, z < st.scalar.core.ptrs 20)
    (hE : st.scalar.core.ptrs 53=epoch) (hOff : st.scalar.core.ptrs 83=(offset : ℤ))
    (hbRecords : ∀ v ∈ vertices, st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val offset)=b v)
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch) :
    let capacity := vertices.length+∑ i : Fin vertices.length, (g.neighbors (vertexEnumeration vertices i)).length
    let numericCost := (24*(16*(ell+3))+100)*capacity+28
    let outputCost := (4*(16*(ell+3))+21)*vertices.length+6
    ∃ steps out, MachineEval m g ω listSolveOutputCode st steps out ∧
      steps ≤ (10*vertices.length+5)+numericCost+outputCost+1 ∧
      outputVector out.output=potentialOutput g.graph α (solveOn g α vertices.toFinset b) ∧
      out.work ≤ st.work+((10*vertices.length+5)+numericCost+outputCost : ℕ)+
        solveCharge m vertices.length (principalEntries g α (vertexEnumeration vertices)).length ∧
      out.scalar.halted=false := by
  dsimp only
  let e := vertexEnumeration vertices
  have hDomain : Finset.univ.image e=vertices.toFinset := vertex_enumeration_domain vertices
  obtain ⟨pre,preMemory,ep,h80,h77,h20,hEnum,hEnumBelow,hForeign,hMassPre,hI,hR,hWorkPre,hOutputPre,hHaltPre⟩ :=
    vertex_enumeration_memory_exec m g ω logical s α ε ell length vertices head F st hh pm hDepth hhp hList hBelow
  have hBase : 0 ≤ st.scalar.core.ptrs 20 := by have := pm.allocator; omega
  have hRecords : ∀ i : Fin vertices.length,
      pre.scalar.core.mem (vertexRecordAddress (16*(ell+3)) (e i).val offset)=b (e i) := by
    intro i
    rw [hR]
    exact hbRecords _ (vertex_enumeration_member vertices i)
  have hBound : ∀ v : Fin n, pre.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch := by
    intro v
    rw [hI _ ((vertexRecordAddress_negative _ _ _).trans_le hBase)]
    exact hbound v
  obtain ⟨u,out,ex,hu,hVector,hWorkOut,hHaltOut⟩ :=
    cached_solve_output_exec m g ω logical s α ε ell length offset (pre.scalar.core.ptrs 20)
      (st.scalar.core.ptrs 20) epoch hBase e (vertexEnumeration_injective vertices hNodup) hNonempty
      (fun i => hd _ (vertex_enumeration_member vertices i)) hα b pre hHaltPre preMemory hDepth
      (fun i => hmem _ (vertex_enumeration_member vertices i)) hEnum hEnumBelow hForeign h80 h77 rfl
      ((ep.pointer_frame 53 (by decide)).trans hE) ((ep.pointer_frame 83 (by decide)).trans hOff) hRecords hBound
  dsimp only [e] at hu hWorkOut
  refine ⟨(10*vertices.length+5)+u,out,MachineEval.seq ep ex,by omega,?_,?_,hHaltOut⟩
  · rwa [hDomain] at hVector
  · rw [hWorkPre] at hWorkOut
    convert hWorkOut using 1 <;> (push_cast; ac_rfl)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootComponentSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 14000000 in
lemma root_component_solve_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
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
      ((4*(16*(ell+3))+21)*(logical.frames 0).active.card+6)+3
    ∃ steps out, MachineEval m g ω rootComponentSolveCode st steps out ∧ steps ≤ cost+1 ∧
      outputVector out.output=potentialOutput g.graph α (solveOn g α (logical.frames 0).active (LocalPush.e s)) ∧
      out.work ≤ st.work+(cost : ℕ)+solveCharge m (logical.frames 0).active.card size ∧ out.scalar.halted=false := by
  dsimp only
  let f := pm.frames 0 (Nat.zero_le _)
  obtain ⟨pre,ep,h90,h83,hI,hR,hW,hO,hH⟩ := root_component_prelude_exec m g ω st hh
  let memory := pm.frame hI hR
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> exact ep.pointer_frame _ (by decide))
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl <;> exact ep.real_register_frame _ (by decide)) hO
  have hList : VertexListRep pre.scalar.integerMemory (st.scalar.integerMemory (levelHeaderAddress 0 1)) f.activeVertices f.activeFoot := by
    rw [hI]; exact f.activeRep
  have hBelow : ∀ z ∈ f.activeFoot, z < pre.scalar.core.ptrs 20 := by
    intro z hz
    rw [ep.pointer_frame 20 (by decide)]
    exact f.activeBelow z hz
  have hLength : f.activeVertices.length=(logical.frames 0).active.card := by
    rw [←f.activeSet,List.toFinset_card_of_nodup f.activeNodup]
  have hNonemptyList : 0<f.activeVertices.length := by rw [hLength]; exact Finset.card_pos.mpr hNonempty
  have hMembership : ∀ v ∈ f.activeVertices, v ∈ (logical.frames 0).active := by
    intro v hv
    rw [←f.activeSet]
    exact List.mem_toFinset.mpr hv
  have hRecords : ∀ v ∈ f.activeVertices,
      pre.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val 2)=LocalPush.e s v := by
    intro v hv
    rw [hR]
    exact pm.seedMarker v
  have hBoundPre : ∀ v : Fin n, pre.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch := by
    rw [hI]; exact hbound
  obtain ⟨u,out,ex,hu,hVector,hWork,hHalt⟩ := list_solve_output_exec m g ω logical s α ε ell length 2
    f.activeVertices (st.scalar.integerMemory (levelHeaderAddress 0 1)) epoch f.activeFoot f.activeNodup hNonemptyList
    (fun v hv => hDegree v (hMembership v hv)) hα (LocalPush.e s) pre hH memory hDepth
    (fun v hv => hStored (hMembership v hv)) h90 hList hBelow ((ep.pointer_frame 53 (by decide)).trans hEpoch) h83 hRecords hBoundPre
  have hCapacity : f.activeVertices.length+∑ i : Fin f.activeVertices.length,
      (g.neighbors (vertexEnumeration f.activeVertices i)).length=
        volumeNat g (logical.frames 0).active+(logical.frames 0).active.card := by
    rw [vertex_list_capacity g f.activeVertices f.activeNodup,f.activeSet]
  have hCost : (10*f.activeVertices.length+5)+
      ((24*(16*(ell+3))+100)*(f.activeVertices.length+∑ i : Fin f.activeVertices.length,
        (g.neighbors (vertexEnumeration f.activeVertices i)).length)+28)+
      ((4*(16*(ell+3))+21)*f.activeVertices.length+6)=
      (10*(logical.frames 0).active.card+5)+((24*(16*(ell+3))+100)*
        (volumeNat g (logical.frames 0).active+(logical.frames 0).active.card)+28)+
      ((4*(16*(ell+3))+21)*(logical.frames 0).active.card+6) := by rw [hCapacity,hLength]
  rw [hCost] at hu hWork
  have hEntries := principal_entries_length_le g α (vertexEnumeration f.activeVertices)
  have hCharge := solveCharge_mono m hLength.le (hEntries.trans_eq hCapacity)
  refine ⟨3+u,out,MachineEval.seq ep ex,by omega,?_,?_,hHalt⟩
  · rwa [f.activeSet] at hVector
  · rw [hW] at hWork
    have hh := hWork.trans (add_le_add le_rfl hCharge)
    have hAssoc (A : ℕ) (Z : ℝ≥0∞) :
        st.work+3+(A : ℝ≥0∞)+Z=st.work+((A+3 : ℕ) : ℝ≥0∞)+Z := by
      simp only [Nat.cast_add,Nat.cast_ofNat]
      ac_rfl
    rw [←hAssoc]
    exact hh

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution : ∀ (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ) (epoch : ℤ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hα : 0<α ∧ α<1) (hNonempty : (logical.frames 0).active.Nonempty)
    (hStored : (logical.frames 0).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames 0).active, 0<g.graph.degree v)
    (hEpoch : st.scalar.core.ptrs 53=epoch)
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch),
let size := volumeNat g (logical.frames 0).active+(logical.frames 0).active.card
    let cost := (10*(logical.frames 0).active.card+5)+((24*(16*(ell+3))+100)*size+28)+
      ((4*(16*(ell+3))+21)*(logical.frames 0).active.card+6)+3
    ∃ steps out, MachineEval m g ω rootComponentSolveCode st steps out ∧ steps ≤ cost+1 ∧
      outputVector out.output=potentialOutput g.graph α (solveOn g α (logical.frames 0).active (LocalPush.e s)) ∧
      out.work ≤ st.work+(cost : ℕ)+solveCharge m (logical.frames 0).active.card size ∧ out.scalar.halted=false := by
  exact @NearlyOptimalPPR.Computation.root_component_solve_exec
