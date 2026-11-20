-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.cached_joint_solve_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:46:20.467245+00:00
-- url     : https://prove2.me/submissions/4b8d08bf-1ba6-418e-8bc3-8440e64a8706

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
import Theorems.Thm_NearlyOptimalPPR_Computation_cached_principal_solve_memory_exec
import Theorems.Thm_NearlyOptimalPPR_Computation_normalization_composes
import Theorems.Thm_NearlyOptimalPPR_Computation_pending_touched_refresh_foreign_exec
import Theorems.Thm_NearlyOptimalPPR_Computation_push_correctness_work
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_level_work
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_residual_error
set_option linter.all false
-- Proof module: Solutions.CompilerExteriorSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_refresh_numeric {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).residual=(st.frames i).residual ∧
      ((refreshKeys g st T).frames i).W=(st.frames i).W ∧
      ((refreshKeys g st T).frames i).reference=(st.frames i).reference ∧
      ((refreshKeys g st T).frames i).active=(st.frames i).active ∧
      ((refreshKeys g st T).frames i).cache=(st.frames i).cache := by
  classical
  by_cases hi : i ≤ st.top <;> simp [refreshKeys,hi]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerExteriorStatic

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def compilerStaticFields {n : ℕ} (f : NormalizeFrame n) :=
  (f.N,f.q,f.Q,f.theta,f.block,f.pc,f.openBudget,f.needFull,f.childrenThisEpisode,f.cache)

lemma compiler_refresh_static {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (i : ℕ) :
    compilerStaticFields ((refreshKeys g st T).frames i)=compilerStaticFields (st.frames i) := by
  classical
  by_cases hi : i ≤ st.top <;> simp [compilerStaticFields,refreshKeys,hi]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerExteriorQueueViews

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_refresh_queues_outside {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (i : ℕ) (v : Fin n) (hv : v ∉ T) :
    (v ∈ ((refreshKeys g st T).frames i).exterior ↔ v ∈ (st.frames i).exterior) ∧
    (v ∈ ((refreshKeys g st T).frames i).high ↔ v ∈ (st.frames i).high) := by
  classical
  by_cases hi : i ≤ st.top <;> simp [refreshKeys,hi,hv]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerExteriorOutside

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_refresh_domain {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (i : ℕ) :
    parentDomain (refreshKeys g st T) i=parentDomain st i := by
  unfold parentDomain
  split_ifs
  · rfl
  · rw [(compiler_refresh_numeric g st T (i-1)).2.2.2.1]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointCoordinateSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open Matrix
noncomputable section

def jointCoordinateUpdate {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (v : Fin n) (δ : ℝ) : RecursiveState n :=
  refreshKeys g (jointUpdate g α logical (fun u => if u=v then δ else 0)) (insert v (g.neighbors v).toFinset)

lemma joint_coordinate_top {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) (v : Fin n) (δ : ℝ) :
    (jointCoordinateUpdate g α logical v δ).top=logical.top := rfl

lemma joint_coordinate_active {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) (v : Fin n) (δ : ℝ) (i : ℕ) :
    ((jointCoordinateUpdate g α logical v δ).frames i).active=(logical.frames i).active := by
  classical
  unfold jointCoordinateUpdate
  rw [(compiler_refresh_numeric g _ _ i).2.2.2.1]
  by_cases hi : i ≤ logical.top <;> simp [jointUpdate,hi]

lemma joint_coordinate_domain {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) (v : Fin n) (δ : ℝ) (i : ℕ) :
    parentDomain (jointCoordinateUpdate g α logical v δ) i=parentDomain logical i := by
  unfold parentDomain
  split_ifs
  · rfl
  · exact joint_coordinate_active g α logical v δ (i-1)

lemma joint_coordinate_potential {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) (v u : Fin n) (δ : ℝ) :
    (jointCoordinateUpdate g α logical v δ).x u=logical.x u+(if u=v then δ else 0) := rfl

lemma joint_coordinate_matrix {n : ℕ} (g : InputGraph n) (α : ℝ) (v u : Fin n) (δ : ℝ) :
    (LocalPush.Lα g.graph α *ᵥ (fun w => if w=v then δ else 0)) u=
      (if u=v then LocalPush.deg g.graph v*δ else 0)-
        (if g.graph.Adj u v then (1-α)*δ else 0) := by
  classical
  have hVec : (fun w : Fin n => if w=v then δ else 0)=Pi.single v δ := by
    funext w
    simp [Pi.single_apply,eq_comm]
  rw [hVec,Matrix.mulVec_single]
  by_cases he : u=v
  · subst u
    simp [LocalPush.Lα,LocalPush.degM,LocalPush.adjM,Matrix.diagonal_apply]
  · by_cases ha : g.graph.Adj u v <;>
      simp [LocalPush.Lα,LocalPush.degM,LocalPush.adjM,Matrix.diagonal_apply,he,ha] <;> ring

lemma joint_coordinate_residual {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (v u : Fin n) (δ : ℝ) (i : ℕ) (hi : i ≤ logical.top) (hu : u ∈ parentDomain logical i) :
    ((jointCoordinateUpdate g α logical v δ).frames i).residual u=(logical.frames i).residual u+
      (if u=v then -LocalPush.deg g.graph v*δ else 0)+(if g.graph.Adj u v then (1-α)*δ else 0) := by
  unfold jointCoordinateUpdate
  rw [(compiler_refresh_numeric g _ _ i).1]
  simp only [jointUpdate,if_pos hi,if_pos hu]
  rw [joint_coordinate_matrix]
  by_cases he : u=v <;> by_cases ha : g.graph.Adj u v <;> simp [he,ha] <;> ring

lemma joint_coordinate_static {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) (v : Fin n) (δ : ℝ) (i : ℕ) :
    compilerStaticFields ((jointCoordinateUpdate g α logical v δ).frames i)=compilerStaticFields (logical.frames i) := by
  classical
  unfold jointCoordinateUpdate
  rw [compiler_refresh_static]
  by_cases hi : i ≤ logical.top <;> simp [jointUpdate,compilerStaticFields,hi]

lemma joint_coordinate_reference_budget {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) (v : Fin n) (δ : ℝ) (i : ℕ) :
    ((jointCoordinateUpdate g α logical v δ).frames i).reference=(logical.frames i).reference ∧
      ((jointCoordinateUpdate g α logical v δ).frames i).W=(logical.frames i).W := by
  classical
  unfold jointCoordinateUpdate
  rw [(compiler_refresh_numeric g _ _ i).2.2.1,(compiler_refresh_numeric g _ _ i).2.1]
  by_cases hi : i ≤ logical.top <;> simp [jointUpdate,hi]

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

-- Proof module: Solutions.GraphQueryExecution

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma nodeOf_vertex {n : ℕ} (v : Fin n) : LocalPush.nodeOf n (v.val : ℤ)=some v := by
  simp [LocalPush.nodeOf,v.isLt]

lemma degree_answer_vertex {n : ℕ} (g : InputGraph n) (v : Fin n) :
    LocalPush.degAnswer g.neighbors (v.val : ℤ)=((g.neighbors v).length : ℤ) := by
  simp [LocalPush.degAnswer,nodeOf_vertex]

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

-- Proof module: Solutions.FramePendingNumericTransport

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def FramePendingKeys.numeric_frame {n : ℕ} {g : InputGraph n} {logical next : RecursiveState n}
    {j width length : ℕ} {st out : MachineState} {floor : ℤ}
    (f : FramePendingKeys g logical j width length st floor)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hDomain : parentDomain next j=parentDomain logical j)
    (hActive : (next.frames j).active=(logical.frames j).active)
    (hStatic : compilerStaticFields (next.frames j)=compilerStaticFields (logical.frames j))
    (hHeaderI : ∀ slot < 32, out.scalar.integerMemory (levelHeaderAddress j slot)=st.scalar.integerMemory (levelHeaderAddress j slot))
    (hHeaderR : ∀ slot < 32, slot ≠ 4 → out.scalar.core.mem (levelHeaderAddress j slot)=st.scalar.core.mem (levelHeaderAddress j slot))
    (hW : out.scalar.core.mem (levelHeaderAddress j 4)=(next.frames j).W)
    (hReference : ∀ v ∈ parentDomain next j,
      out.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)))=(next.frames j).reference v)
    (hResidual : ∀ v ∈ parentDomain next j,
      out.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)+1))=(next.frames j).residual v)
    (hFieldsI : ∀ v ∈ parentDomain logical j, ∀ offset, 2 ≤ offset → offset ≤ 6 →
      out.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+offset))=st.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+offset)))
    (hOwned : ∀ z ∈ f.owned, out.scalar.integerMemory z=st.scalar.integerMemory z)
    (hEligibility : ∀ v ∈ parentDomain next j, v.val ∈ (next.frames j).exterior.image Fin.val ↔
      out.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+2))=0 ∧
      (next.frames j).q*(out.scalar.integerMemory (vertexRecordAddress width v.val 0) : ℝ) <
        out.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)+1)))
    (hHighValid : ∀ v ∈ parentDomain next j, v.val ∈ (next.frames j).high.image Fin.val ↔
      out.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+2)) ≠ 0 ∧
      3*(next.frames j).theta*(out.scalar.integerMemory (vertexRecordAddress width v.val 0) : ℝ) ≤
        out.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)+1))) :
    FramePendingKeys g next j width length out floor := by
  have hs : (next.frames j).N=(logical.frames j).N ∧
      (next.frames j).q=(logical.frames j).q ∧ (next.frames j).Q=(logical.frames j).Q ∧
      (next.frames j).theta=(logical.frames j).theta ∧ (next.frames j).block=(logical.frames j).block ∧
      (next.frames j).pc=(logical.frames j).pc ∧ (next.frames j).openBudget=(logical.frames j).openBudget ∧
      (next.frames j).needFull=(logical.frames j).needFull ∧
      (next.frames j).childrenThisEpisode=(logical.frames j).childrenThisEpisode ∧
      (next.frames j).cache=(logical.frames j).cache := by
    simpa only [compilerStaticFields,Prod.mk.injEq] using hStatic
  have hN := hs.1
  have hq := hs.2.1
  have hQ := hs.2.2.1
  have hTheta := hs.2.2.2.1
  have hBlock := hs.2.2.2.2.1
  have hPC := hs.2.2.2.2.2.1
  have hOpen := hs.2.2.2.2.2.2.1
  have hNeed := hs.2.2.2.2.2.2.2.1
  have hChildren := hs.2.2.2.2.2.2.2.2.1
  have hCache := hs.2.2.2.2.2.2.2.2.2
  let ext := f.exteriorObject.frame
    (fun z hz => hOwned z (Finset.mem_union_left _ (Finset.mem_union_right _ hz))) hFree
  let high := f.highObject.frame (fun z hz => hOwned z (Finset.mem_union_right _ hz)) hFree
  refine {
    N := by rw [hN]; exact (hHeaderR 0 (by decide) (by decide)).trans f.N
    q := by rw [hq]; exact (hHeaderR 1 (by decide) (by decide)).trans f.q
    Q := by rw [hQ]; exact (hHeaderR 3 (by decide) (by decide)).trans f.Q
    W := hW
    theta := by rw [hTheta]; exact (hHeaderR 5 (by decide) (by decide)).trans f.theta
    block := by rw [hBlock]; exact (hHeaderI 14 (by decide)).trans f.block
    pc := by rw [hPC]; exact (hHeaderI 0 (by decide)).trans f.pc
    openBudget := by rw [hOpen]; exact (hHeaderI 9 (by decide)).trans f.openBudget
    needFull := by rw [hNeed]; exact (hHeaderI 10 (by decide)).trans f.needFull
    children := by rw [hChildren]; exact (hHeaderI 11 (by decide)).trans f.children
    reference := hReference
    residual := hResidual
    activeFlags := by
      intro v hv
      rw [hDomain] at hv
      rw [hFieldsI v hv 2 (by decide) (by decide),hActive]
      exact f.activeFlags v hv
    cacheFlags := by
      intro v hv
      rw [hDomain] at hv
      rw [hFieldsI v hv 4 (by decide) (by decide),hCache]
      exact f.cacheFlags v hv
    activeVertices := f.activeVertices
    activeFoot := f.activeFoot
    activeRep := ?_
    activeNodup := f.activeNodup
    activeSet := f.activeSet.trans hActive.symm
    activeCount := by rw [hActive]; exact (hHeaderI 3 (by decide)).trans f.activeCount
    activeVolume := by rw [hActive]; exact (hHeaderI 2 (by decide)).trans f.activeVolume
    activeBelow := fun z hz => (f.activeBelow z hz).trans_le hFree
    activeAbove := f.activeAbove
    cacheVertices := f.cacheVertices
    cacheFoot := f.cacheFoot
    cacheRep := ?_
    cacheNodup := f.cacheNodup
    cacheSet := f.cacheSet.trans hCache.symm
    cacheCount := by rw [hCache]; exact (hHeaderI 5 (by decide)).trans f.cacheCount
    cacheVolume := by rw [hCache]; exact (hHeaderI 6 (by decide)).trans f.cacheVolume
    cacheBelow := fun z hz => (f.cacheBelow z hz).trans_le hFree
    cacheAbove := f.cacheAbove
    exteriorBase := f.exteriorBase
    highBase := f.highBase
    exteriorPointer := (hHeaderI 7 (by decide)).trans f.exteriorPointer
    highPointer := (hHeaderI 8 (by decide)).trans f.highPointer
    exteriorObject := ext
    highObject := high
    exteriorData := ?_
    virtualExcluded := by
      intro v hv
      rw [hDomain] at hv
      exact (hFieldsI v hv 5 (by decide) (by decide)).trans (f.virtualExcluded v hv)
    highFlags := ?_
    highDomain := by rw [hDomain]; exact f.highDomain
    highValid := hHighValid
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
  · refine ⟨?_,?_,?_,hEligibility⟩
    · rw [hDomain]; exact f.exteriorData.queuedDomain
    · intro v hv
      rw [hDomain] at hv
      rw [hFieldsI v hv 3 (by decide) (by decide)]
      exact f.exteriorData.flags v hv
    · intro v hv
      rw [hDomain] at hv
      rw [hFieldsI v hv 2 (by decide) (by decide)]
      exact f.exteriorData.activeNonnegative v hv
  · intro v hv
    rw [hDomain] at hv
    rw [hFieldsI v hv 6 (by decide) (by decide)]
    exact f.highFlags v hv

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorEligibilityTransition

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma compiler_fin_val_image {n : ℕ} (T : Finset (Fin n)) (v : Fin n) :
    v.val ∈ T.image Fin.val ↔ v ∈ T := by
  constructor
  · rintro h
    obtain ⟨u,hu,he⟩ := Finset.mem_image.mp h
    exact (Fin.ext he) ▸ hu
  · intro h
    exact Finset.mem_image.mpr ⟨v,h,rfl⟩

lemma compiler_neighbor_degree {n : ℕ} (g : InputGraph n) (v : Fin n) :
    (g.neighbors v).length=g.graph.degree v := by
  have he : (g.neighbors v).toFinset=g.graph.neighborFinset v := by
    ext u
    simp [g.correct]
  rw [←List.toFinset_card_of_nodup (g.nodup v),he,SimpleGraph.card_neighborFinset_eq_degree]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointCoordinateFacts

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma joint_coordinate_outside_queues {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (v u : Fin n) (δ : ℝ) (hu : u ∉ insert v (g.neighbors v).toFinset) (j : ℕ) :
    (u ∈ ((jointCoordinateUpdate g α logical v δ).frames j).exterior ↔ u ∈ (logical.frames j).exterior) ∧
      (u ∈ ((jointCoordinateUpdate g α logical v δ).frames j).high ↔ u ∈ (logical.frames j).high) := by
  classical
  unfold jointCoordinateUpdate
  rw [(compiler_refresh_queues_outside g _ _ j u hu).1,(compiler_refresh_queues_outside g _ _ j u hu).2]
  by_cases hj : j ≤ logical.top <;> simp [jointUpdate,hj]

lemma joint_coordinate_outside_residual {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (v u : Fin n) (δ : ℝ) (hu : u ∉ insert v (g.neighbors v).toFinset) (j : ℕ) :
    ((jointCoordinateUpdate g α logical v δ).frames j).residual u=(logical.frames j).residual u := by
  classical
  have hNe : u ≠ v := by intro h; subst u; simp at hu
  have hAdj : ¬g.graph.Adj u v := by
    intro h
    exact hu (Finset.mem_insert_of_mem (List.mem_toFinset.mpr ((g.correct v u).mpr (g.graph.adj_symm h))))
  unfold jointCoordinateUpdate
  rw [(compiler_refresh_numeric g _ _ j).1]
  by_cases hj : j ≤ logical.top
  · by_cases huD : u ∈ parentDomain logical j
    · simp only [jointUpdate,if_pos hj,if_pos huD]
      rw [joint_coordinate_matrix]
      simp [hNe,hAdj]
    · simp [jointUpdate,hj,huD]
  · simp [jointUpdate,hj]

lemma joint_coordinate_parameters {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (v : Fin n) (δ : ℝ) (j : ℕ) :
    ((jointCoordinateUpdate g α logical v δ).frames j).q=(logical.frames j).q ∧
      ((jointCoordinateUpdate g α logical v δ).frames j).theta=(logical.frames j).theta := by
  have h := joint_coordinate_static g α logical v δ j
  exact ⟨congrArg (fun x => x.2.1) h,congrArg (fun x => x.2.2.2.1) h⟩

lemma joint_coordinate_queue_cover {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (v : Fin n) (δ : ℝ) (j : ℕ) (ext high : Finset ℕ)
    (hExt : (logical.frames j).exterior.image Fin.val ⊆ ext) (hHigh : (logical.frames j).high.image Fin.val ⊆ high) :
    ((jointCoordinateUpdate g α logical v δ).frames j).exterior.image Fin.val \
      (insert v (g.neighbors v).toFinset).image Fin.val ⊆ ext ∧
    ((jointCoordinateUpdate g α logical v δ).frames j).high.image Fin.val \
      (insert v (g.neighbors v).toFinset).image Fin.val ⊆ high := by
  constructor
  · intro k hk
    obtain ⟨hK,hT⟩ := Finset.mem_sdiff.mp hk
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hK
    have hNot : u ∉ insert v (g.neighbors v).toFinset := by simpa only [compiler_fin_val_image] using hT
    exact hExt (Finset.mem_image.mpr ⟨u,(joint_coordinate_outside_queues g α logical v u δ hNot j).1.mp hu,rfl⟩)
  · intro k hk
    obtain ⟨hK,hT⟩ := Finset.mem_sdiff.mp hk
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hK
    have hNot : u ∉ insert v (g.neighbors v).toFinset := by simpa only [compiler_fin_val_image] using hT
    exact hHigh (Finset.mem_image.mpr ⟨u,(joint_coordinate_outside_queues g α logical v u δ hNot j).2.mp hu,rfl⟩)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RefreshKeysCorrect

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma refresh_key_predicates {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (i : ℕ) (v : Fin n) :
    (exteriorKey g (refreshKeys g st T) i v ↔ exteriorKey g st i v) ∧
      (highKey g (refreshKeys g st T) i v ↔ highKey g st i v) := by
  have hq : ((refreshKeys g st T).frames i).q=(st.frames i).q :=
    congrArg (fun x => x.2.1) (compiler_refresh_static g st T i)
  have hTheta : ((refreshKeys g st T).frames i).theta=(st.frames i).theta :=
    congrArg (fun x => x.2.2.2.1) (compiler_refresh_static g st T i)
  simp only [exteriorKey,highKey,compiler_refresh_domain,hq,hTheta,
    (compiler_refresh_numeric g st T i).1,(compiler_refresh_numeric g st T i).2.2.2.1]
  trivial

lemma refresh_keys_complete {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hOutside : ∀ i ≤ st.top, ∀ v ∉ T,
      (v ∈ (st.frames i).exterior ↔ exteriorKey g st i v) ∧
        (v ∈ (st.frames i).high ↔ highKey g st i v)) :
    KeysInvariant g (refreshKeys g st T) := by
  classical
  intro i hi
  change i ≤ st.top at hi
  constructor
  · intro v
    rw [(refresh_key_predicates g st T i v).1]
    by_cases hv : v ∈ T
    · simp [refreshKeys,hi,hv,exteriorKey]
    · simpa [refreshKeys,hi,hv] using (hOutside i hi v hv).1
  · intro v
    rw [(refresh_key_predicates g st T i v).2]
    by_cases hv : v ∈ T
    · simp [refreshKeys,hi,hv,highKey]
    · simpa [refreshKeys,hi,hv] using (hOutside i hi v hv).2

lemma joint_coordinate_keys {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (v : Fin n) (δ : ℝ) (hKeys : KeysInvariant g logical) :
    KeysInvariant g (jointCoordinateUpdate g α logical v δ) := by
  classical
  unfold jointCoordinateUpdate
  apply refresh_keys_complete
  intro i hi u hu
  change i ≤ logical.top at hi
  have hQE := (joint_coordinate_parameters g α logical v δ i).1
  have hTheta := (joint_coordinate_parameters g α logical v δ i).2
  have hRes := joint_coordinate_outside_residual g α logical v u δ hu i
  have hFinalE : exteriorKey g (jointCoordinateUpdate g α logical v δ) i u ↔ exteriorKey g logical i u := by
    simp only [exteriorKey,joint_coordinate_domain,joint_coordinate_active,hQE,hRes]
  have hFinalH : highKey g (jointCoordinateUpdate g α logical v δ) i u ↔ highKey g logical i u := by
    simp only [highKey,joint_coordinate_active,hTheta,hRes]
  have hRef := refresh_key_predicates g (jointUpdate g α logical (fun w => if w=v then δ else 0))
    (insert v (g.neighbors v).toFinset) i u
  have hRawE : exteriorKey g (jointUpdate g α logical (fun w => if w=v then δ else 0)) i u ↔ exteriorKey g logical i u :=
    hRef.1.symm.trans hFinalE
  have hRawH : highKey g (jointUpdate g α logical (fun w => if w=v then δ else 0)) i u ↔ highKey g logical i u :=
    hRef.2.symm.trans hFinalH
  constructor
  · rw [hRawE]
    simpa only [jointUpdate,if_pos hi] using (hKeys i hi).1 u
  · rw [hRawH]
    simpa only [jointUpdate,if_pos hi] using (hKeys i hi).2 u

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

lemma level_memory_additive (update : ℕ → (ℤ → ℝ) → (ℤ → ℝ)) (increment : ℕ → ℝ)
    (limit : ℕ) (z : ℤ) (hStep : ∀ i < limit, ∀ R, update i R z=R z+increment i) (count : ℕ) :
    ∀ (start : ℕ) (R : ℤ → ℝ), start+count ≤ limit →
      levelRealMemoryFold update start count R z=R z+∑ k ∈ Finset.range count, increment (start+k) := by
  induction count with
  | zero => intros; simp [levelRealMemoryFold]
  | succ count ih =>
    intro start R hRange
    rw [levelRealMemoryFold,ih (start+1) (update start R) (by omega),hStep start (by omega),Finset.sum_range_succ']
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

lemma level_payload_frame {Payload Value : Type} (update : ℕ → Payload → Payload) (limit : ℕ)
    (eval : Payload → Value) (hStep : ∀ i < limit, ∀ payload, eval (update i payload)=eval payload) (count : ℕ) :
    ∀ (start : ℕ) (payload : Payload), start+count ≤ limit →
      eval (levelPayloadFold update start count payload)=eval payload := by
  induction count with
  | zero => intros; rfl
  | succ count ih =>
    intro start payload hRange
    rw [levelPayloadFold,ih (start+1) (update start payload) (by omega),hStep start (by omega)]

lemma level_payload_additive {Payload : Type} (update : ℕ → Payload → Payload)
    (increment : ℕ → ℝ) (limit : ℕ) (eval : Payload → ℝ)
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

lemma joint_iteration_top {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) (h : Fin n → ℝ)
    (index count : ℕ) (logical : RecursiveState n) :
    (jointSolveIterationState g α e h index count logical).top=logical.top := by
  induction count generalizing index logical with
  | zero => rfl
  | succ count ih =>
    unfold jointSolveIterationState
    split_ifs
    · rw [ih,joint_coordinate_top]
    · rfl

lemma joint_iteration_keys {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) (h : Fin n → ℝ)
    (index count : ℕ) (logical : RecursiveState n) (hKeys : KeysInvariant g logical) :
    KeysInvariant g (jointSolveIterationState g α e h index count logical) := by
  induction count generalizing index logical with
  | zero => exact hKeys
  | succ count ih =>
    unfold jointSolveIterationState
    split_ifs
    · exact ih (index+1) _ (joint_coordinate_keys g α logical _ _ hKeys)
    · exact hKeys

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

-- Proof module: Solutions.JointSolveCorrection

set_option autoImplicit false
set_option maxRecDepth 10000
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

def jointSolveCorrection {n k : ℕ} (e : Fin k → Fin n) (h : Fin n → ℝ) (index count : ℕ) : Fin n → ℝ :=
  match count with
  | 0 => 0
  | remaining+1 => if hi : index < k then
      (fun u => if u=e ⟨index,hi⟩ then h (e ⟨index,hi⟩) else 0)+jointSolveCorrection e h (index+1) remaining
    else 0

lemma joint_iteration_correction_sum {n k : ℕ} (e : Fin k → Fin n) (h : Fin n → ℝ) (index count : ℕ) :
    jointSolveCorrection e h index count=
      ∑ j ∈ Finset.range count, if hj : index+j < k then (fun u => if u=e ⟨index+j,hj⟩ then h (e ⟨index+j,hj⟩) else 0) else 0 := by
  induction count generalizing index with
  | zero => simp [jointSolveCorrection]
  | succ count ih =>
    rw [Finset.sum_range_succ']
    by_cases hi : index < k
    · rw [jointSolveCorrection,dif_pos hi,ih]
      simp only [Nat.add_zero,dif_pos hi]
      have hRest : (∑ j ∈ Finset.range count, if hj : (index+1)+j < k then (fun u => if u=e ⟨(index+1)+j,hj⟩ then h (e ⟨(index+1)+j,hj⟩) else 0) else 0)=
          ∑ j ∈ Finset.range count, if hj : index+(j+1) < k then (fun u => if u=e ⟨index+(j+1),hj⟩ then h (e ⟨index+(j+1),hj⟩) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        have he : index+1+j=index+(j+1) := by omega
        simp only [he]
      rw [hRest]
      exact add_comm _ _
    · have hNever : ∀ j : ℕ, ¬ index+j < k := by intros; omega
      simp only [jointSolveCorrection,dif_neg hi,Nat.add_zero,dif_neg hi,zero_add,add_zero]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      rw [dif_neg (hNever (j+1))]

lemma joint_iteration_correction_full_sum {n k : ℕ} (e : Fin k → Fin n) (h : Fin n → ℝ) :
    jointSolveCorrection e h 0 k=∑ i : Fin k, (fun u => if u=e i then h (e i) else 0) := by
  rw [joint_iteration_correction_sum,Finset.sum_fin_eq_sum_range]
  simp only [Nat.zero_add]

lemma joint_iteration_correction_full {n k : ℕ} (e : Fin k → Fin n) (h : Fin n → ℝ)
    (he : Function.Injective e) (hSupport : ∀ u ∉ Finset.univ.image e, h u=0) :
    jointSolveCorrection e h 0 k=h := by
  classical
  rw [joint_iteration_correction_full_sum]
  funext u
  rw [Finset.sum_apply]
  by_cases hu : u ∈ Finset.univ.image e
  · obtain ⟨i,hi,heu⟩ := Finset.mem_image.mp hu
    rw [Finset.sum_eq_single i]
    · simp [heu]
    · intro j hj hji
      have hNe : u ≠ e j := by
        intro hEq
        exact hji (he (hEq.symm.trans heu.symm))
      simp [hNe]
    · simp
  · rw [hSupport u hu]
    apply Finset.sum_eq_zero
    intro i hi
    have hNe : u ≠ e i := by intro hEq; exact hu (Finset.mem_image.mpr ⟨i,hi,hEq.symm⟩)
    simp [hNe]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointSolveNumericFold

set_option autoImplicit false
set_option maxRecDepth 10000
open Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma joint_coordinate_residual_total {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (v u : Fin n) (δ : ℝ) (j : ℕ) :
    ((jointCoordinateUpdate g α logical v δ).frames j).residual u=
      if j ≤ logical.top ∧ u ∈ parentDomain logical j then
        (logical.frames j).residual u-(LocalPush.Lα g.graph α *ᵥ (fun w => if w=v then δ else 0)) u
      else (logical.frames j).residual u := by
  classical
  unfold jointCoordinateUpdate
  rw [(compiler_refresh_numeric g _ _ j).1]
  by_cases hj : j ≤ logical.top <;> by_cases hu : u ∈ parentDomain logical j <;> simp [jointUpdate,hj,hu]

lemma joint_iteration_potential {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) (h : Fin n → ℝ)
    (index count : ℕ) (logical : RecursiveState n) (u : Fin n) :
    (jointSolveIterationState g α e h index count logical).x u=logical.x u+jointSolveCorrection e h index count u := by
  induction count generalizing index logical with
  | zero => simp [jointSolveIterationState,jointSolveCorrection]
  | succ count ih =>
    unfold jointSolveIterationState jointSolveCorrection
    by_cases hi : index < k
    · rw [dif_pos hi,dif_pos hi,ih,joint_coordinate_potential]
      simp only [Pi.add_apply]
      ring
    · simp [hi]

lemma joint_iteration_residual {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) (h : Fin n → ℝ)
    (index count : ℕ) (logical : RecursiveState n) (j : ℕ) (u : Fin n) :
    ((jointSolveIterationState g α e h index count logical).frames j).residual u=
      if j ≤ logical.top ∧ u ∈ parentDomain logical j then
        (logical.frames j).residual u-(LocalPush.Lα g.graph α *ᵥ jointSolveCorrection e h index count) u
      else (logical.frames j).residual u := by
  classical
  induction count generalizing index logical with
  | zero => simp [jointSolveIterationState,jointSolveCorrection]
  | succ count ih =>
    unfold jointSolveIterationState jointSolveCorrection
    by_cases hi : index < k
    · rw [dif_pos hi,dif_pos hi,ih,joint_coordinate_top,joint_coordinate_domain,joint_coordinate_residual_total]
      by_cases hD : j ≤ logical.top ∧ u ∈ parentDomain logical j
      · simp only [if_pos hD,Matrix.mulVec_add,Pi.add_apply]
        ring
      · simp only [if_neg hD]
    · simp only [dif_neg hi,Matrix.mulVec_zero,Pi.zero_apply,sub_zero,ite_self]

def jointFrameControl {n : ℕ} (f : NormalizeFrame n) : NormalizeFrame n :=
  {f with residual := 0, exterior := ∅, high := ∅}

def jointStateControl {n : ℕ} (logical : RecursiveState n) : RecursiveState n :=
  {logical with x := 0, frames := fun j => jointFrameControl (logical.frames j)}

lemma joint_coordinate_frame_control {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (v : Fin n) (δ : ℝ) (j : ℕ) :
    jointFrameControl ((jointCoordinateUpdate g α logical v δ).frames j)=jointFrameControl (logical.frames j) := by
  classical
  by_cases hj : j ≤ logical.top <;> simp [jointCoordinateUpdate,jointUpdate,refreshKeys,jointFrameControl,hj]

lemma joint_coordinate_state_control {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (v : Fin n) (δ : ℝ) :
    jointStateControl (jointCoordinateUpdate g α logical v δ)=jointStateControl logical := by
  have hFrames : (fun j => jointFrameControl ((jointCoordinateUpdate g α logical v δ).frames j))=
      (fun j => jointFrameControl (logical.frames j)) := by
    funext j
    exact joint_coordinate_frame_control g α logical v δ j
  change {logical with x := 0,frames := fun j => jointFrameControl ((jointCoordinateUpdate g α logical v δ).frames j)}=
    {logical with x := 0,frames := fun j => jointFrameControl (logical.frames j)}
  rw [hFrames]

lemma joint_iteration_frame_control {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) (h : Fin n → ℝ)
    (index count : ℕ) (logical : RecursiveState n) (j : ℕ) :
    jointFrameControl ((jointSolveIterationState g α e h index count logical).frames j)=jointFrameControl (logical.frames j) := by
  induction count generalizing index logical with
  | zero => rfl
  | succ count ih =>
    unfold jointSolveIterationState
    split_ifs
    · rw [ih,joint_coordinate_frame_control]
    · rfl

lemma joint_iteration_state_control {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) (h : Fin n → ℝ)
    (index count : ℕ) (logical : RecursiveState n) :
    jointStateControl (jointSolveIterationState g α e h index count logical)=jointStateControl logical := by
  induction count generalizing index logical with
  | zero => rfl
  | succ count ih =>
    unfold jointSolveIterationState
    split_ifs
    · rw [ih,joint_coordinate_state_control]
    · rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointSolveSourceAgreement

set_option autoImplicit false
set_option maxRecDepth 10000
open Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma joint_frame_eq_of_data {n : ℕ} (a b : NormalizeFrame n)
    (hControl : jointFrameControl a=jointFrameControl b) (hRes : a.residual=b.residual)
    (hExt : a.exterior=b.exterior) (hHigh : a.high=b.high) : a=b := by
  calc
    a = {jointFrameControl a with residual := a.residual,exterior := a.exterior,high := a.high} := rfl
    _ = {jointFrameControl b with residual := b.residual,exterior := b.exterior,high := b.high} := by rw [hControl,hRes,hExt,hHigh]
    _ = b := rfl

lemma joint_frames_eq_from_keys {n : ℕ} (g : InputGraph n) (a b : RecursiveState n) (j : ℕ)
    (hControl : jointFrameControl (a.frames j)=jointFrameControl (b.frames j))
    (hRes : (a.frames j).residual=(b.frames j).residual) (hD : parentDomain a j=parentDomain b j)
    (hA : (∀ u, u ∈ (a.frames j).exterior ↔ exteriorKey g a j u) ∧ (∀ u, u ∈ (a.frames j).high ↔ highKey g a j u))
    (hB : (∀ u, u ∈ (b.frames j).exterior ↔ exteriorKey g b j u) ∧ (∀ u, u ∈ (b.frames j).high ↔ highKey g b j u)) :
    a.frames j=b.frames j := by
  classical
  have hq := congrArg NormalizeFrame.q hControl
  change (a.frames j).q=(b.frames j).q at hq
  have hTheta := congrArg NormalizeFrame.theta hControl
  change (a.frames j).theta=(b.frames j).theta at hTheta
  have hActive := congrArg NormalizeFrame.active hControl
  change (a.frames j).active=(b.frames j).active at hActive
  apply joint_frame_eq_of_data _ _ hControl hRes
  · ext u
    rw [(hA.1 u),(hB.1 u)]
    simp only [exteriorKey,hD,hq,hActive,hRes]
  · ext u
    rw [(hA.2 u),(hB.2 u)]
    simp only [highKey,hTheta,hActive,hRes]

lemma joint_canonical_frame_control {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (z : Fin n → ℝ) (T : Finset (Fin n)) (j : ℕ) :
    jointFrameControl ((refreshKeys g (jointUpdate g α logical z) (touchedBy g T)).frames j)=jointFrameControl (logical.frames j) := by
  classical
  by_cases hj : j ≤ logical.top <;> simp [refreshKeys,jointUpdate,jointFrameControl,hj]

lemma joint_canonical_state_control {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (z : Fin n → ℝ) (T : Finset (Fin n)) :
    jointStateControl (refreshKeys g (jointUpdate g α logical z) (touchedBy g T))=jointStateControl logical := by
  have hFrames : (fun j => jointFrameControl ((refreshKeys g (jointUpdate g α logical z) (touchedBy g T)).frames j))=
      (fun j => jointFrameControl (logical.frames j)) := by
    funext j
    exact joint_canonical_frame_control g α logical z T j
  change {logical with x := 0,frames := fun j => jointFrameControl ((refreshKeys g (jointUpdate g α logical z) (touchedBy g T)).frames j)}=
    {logical with x := 0,frames := fun j => jointFrameControl (logical.frames j)}
  rw [hFrames]

lemma joint_iteration_unused_frame {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) (h : Fin n → ℝ)
    (index count : ℕ) (logical : RecursiveState n) (j : ℕ) (hj : ¬j ≤ logical.top) :
    (jointSolveIterationState g α e h index count logical).frames j=logical.frames j := by
  classical
  induction count generalizing index logical with
  | zero => rfl
  | succ count ih =>
    unfold jointSolveIterationState
    split_ifs
    · rename_i hi
      rw [ih (index+1) (jointCoordinateUpdate g α logical (e ⟨index,hi⟩) (h (e ⟨index,hi⟩))) hj]
      simp [jointCoordinateUpdate,jointUpdate,refreshKeys,hj]
    · rfl

lemma joint_iteration_source_agreement {n k : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (e : Fin k → Fin n) (h : Fin n → ℝ) (he : Function.Injective e)
    (hSupport : ∀ u ∉ Finset.univ.image e, h u=0) (hKeys : KeysInvariant g logical)
    (hCanonicalKeys : KeysInvariant g (refreshKeys g (jointUpdate g α logical h) (touchedBy g (Finset.univ.image e)))) :
    jointSolveIterationState g α e h 0 k logical=refreshKeys g (jointUpdate g α logical h) (touchedBy g (Finset.univ.image e)) := by
  classical
  let result := jointSolveIterationState g α e h 0 k logical
  let canonical := refreshKeys g (jointUpdate g α logical h) (touchedBy g (Finset.univ.image e))
  have hCorrection := joint_iteration_correction_full e h he hSupport
  have hX : result.x=canonical.x := by
    funext u
    rw [joint_iteration_potential,hCorrection]
    rfl
  have hControl : jointStateControl result=jointStateControl canonical :=
    (joint_iteration_state_control g α e h 0 k logical).trans (joint_canonical_state_control g α logical h _).symm
  have hFrames : result.frames=canonical.frames := by
    funext j
    by_cases hj : j ≤ logical.top
    · have hCtr : jointFrameControl (result.frames j)=jointFrameControl (canonical.frames j) :=
        (joint_iteration_frame_control g α e h 0 k logical j).trans (joint_canonical_frame_control g α logical h _ j).symm
      have hRes : (result.frames j).residual=(canonical.frames j).residual := by
        funext u
        rw [joint_iteration_residual,hCorrection]
        unfold canonical
        rw [(compiler_refresh_numeric g _ _ j).1]
        by_cases hu : u ∈ parentDomain logical j <;> simp [jointUpdate,hj,hu]
      have hD : parentDomain result j=parentDomain canonical j := by
        unfold parentDomain
        split_ifs
        · rfl
        · have hc := (joint_iteration_frame_control g α e h 0 k logical (j-1)).trans
              (joint_canonical_frame_control g α logical h (Finset.univ.image e) (j-1)).symm
          have hA := congrArg NormalizeFrame.active hc
          exact hA
      exact joint_frames_eq_from_keys g result canonical j hCtr hRes hD
        (joint_iteration_keys g α e h 0 k logical hKeys j (by rw [joint_iteration_top]; exact hj)) (hCanonicalKeys j hj)
    · rw [joint_iteration_unused_frame g α e h 0 k logical j hj]
      simp [canonical,refreshKeys,jointUpdate,hj]
  calc
    result = {jointStateControl result with x := result.x,frames := result.frames} := rfl
    _ = {jointStateControl canonical with x := canonical.x,frames := canonical.frames} := by rw [hControl,hX,hFrames]
    _ = canonical := rfl

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingLevelGuard

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pendingLevelGuardCode_wellFormed : pendingLevelGuardCode.wellFormed := ⟨trivial,pendingLevelRefreshCode_wellFormed⟩

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingVertexLevelLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pendingVertexLevelLoopCode_wellFormed : pendingVertexLevelLoopCode.wellFormed := pendingVertexLevelBodyCode_wellFormed

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointRefreshKeys

set_option autoImplicit false
set_option maxRecDepth 10000
open Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma joint_supported_matrix_outside {n : ℕ} (g : InputGraph n) (α : ℝ) (T : Finset (Fin n))
    (h : Fin n → ℝ) (hSupport : ∀ v ∉ T, h v=0) (u : Fin n) (hu : u ∉ touchedBy g T) :
    (LocalPush.Lα g.graph α *ᵥ h) u=0 := by
  classical
  have huT : u ∉ T := by intro hv; exact hu (Finset.mem_union_left _ hv)
  change (∑ v, LocalPush.Lα g.graph α u v*h v)=0
  apply Finset.sum_eq_zero
  intro v hv
  by_cases hvT : v ∈ T
  · have hNe : u ≠ v := by intro he; subst v; exact huT hvT
    have hAdj : ¬g.graph.Adj u v := by
      intro ha
      apply hu
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨v,hvT,List.mem_toFinset.mpr ((g.correct v u).mpr (g.graph.adj_symm ha))⟩
    simp [LocalPush.Lα,LocalPush.degM,LocalPush.adjM,Matrix.diagonal_apply,hNe,hAdj]
  · rw [hSupport v hvT,mul_zero]

lemma joint_refresh_keys {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (T : Finset (Fin n)) (h : Fin n → ℝ) (hSupport : ∀ u ∉ T, h u=0)
    (hKeys : KeysInvariant g logical) :
    KeysInvariant g (refreshKeys g (jointUpdate g α logical h) (touchedBy g T)) := by
  classical
  apply refresh_keys_complete
  intro j hj u hu
  change j ≤ logical.top at hj
  have hMat := joint_supported_matrix_outside g α T h hSupport u hu
  have hDomain : parentDomain (jointUpdate g α logical h) j=parentDomain logical j := by
    unfold parentDomain
    split_ifs
    · rfl
    · unfold jointUpdate
      dsimp only
      split_ifs <;> rfl
  have hRes : ((jointUpdate g α logical h).frames j).residual u=(logical.frames j).residual u := by
    simp [jointUpdate,hj,hMat]
  have hExt : exteriorKey g (jointUpdate g α logical h) j u ↔ exteriorKey g logical j u := by
    unfold exteriorKey
    rw [hDomain,hRes]
    simp only [jointUpdate,if_pos hj]
  have hHigh : highKey g (jointUpdate g α logical h) j u ↔ highKey g logical j u := by
    unfold highKey
    rw [hRes]
    simp only [jointUpdate,if_pos hj]
  constructor
  · rw [hExt]
    simpa only [jointUpdate,if_pos hj] using (hKeys j hj).1 u
  · rw [hHigh]
    simpa only [jointUpdate,if_pos hj] using (hKeys j hj).2 u

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

-- Proof module: Solutions.SolveIterationBuffers

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma SolveIterationBuffers.frame {n k : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical nextLogical : RecursiveState n} {st out : MachineState}
    {old : RecursiveMachineMemory g s α ε ell length logical st}
    {next : RecursiveMachineMemory g s α ε ell length nextLogical out}
    {enumBase answerBase : ℤ} {e : Fin k → Fin n} {h : Fin n → ℝ}
    (buffers : SolveIterationBuffers old enumBase answerBase e h) (fr : MemoryBufferFrame old next) :
    SolveIterationBuffers next enumBase answerBase e h := by
  refine ⟨buffers.enumNonnegative,buffers.answerNonnegative,?_,?_,?_,?_,?_⟩
  · intro i
    exact (buffers.enumBelow i).trans_le fr.free
  · intro i
    exact (buffers.answerBelow i).trans_le fr.free
  · intro i j hj hOwned
    have hjOld : j ≤ logical.top := by rw [←fr.top]; exact hj
    exact buffers.enumForeign i j hjOld (fr.oldOwned j hjOld hj _ hOwned (buffers.enumBelow i))
  · intro i
    rw [fr.integerFrame _ (by have := buffers.enumNonnegative; have := Int.natCast_nonneg i.val; omega)
      (buffers.enumBelow i) (buffers.enumForeign i)]
    exact buffers.enumeration i
  · intro i
    rw [fr.realPositive _ (by have := buffers.answerNonnegative; have := Int.natCast_nonneg i.val; omega)]
    exact buffers.answers i

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorInputsCode

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma exteriorResidualOffsetCode_wellFormed : exteriorResidualOffsetCode.wellFormed := by
  simp [exteriorResidualOffsetCode,exteriorResidualOffsetInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
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

-- Proof module: Solutions.DomainResidualMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma domain_residual_update_at {n : ℕ} (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (v u : Fin n) (delta : ℝ) (i j : ℕ)
    (hi : i ≤ logical.top) (hj : j ≤ logical.top) (R : ℤ → ℝ) :
    domainResidualMemoryUpdate logical (16*(ell+3)) v delta i R
        (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))=
      R (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))+
        (if i=j ∧ u=v ∧ v ∈ parentDomain logical j then delta else 0) := by
  classical
  by_cases he : i=j ∧ u=v
  · obtain ⟨rfl,rfl⟩ := he
    by_cases hv : u ∈ parentDomain logical i <;> simp [domainResidualMemoryUpdate,hv]
  · have hAddr : vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1) ≠
        vertexRecordAddress (16*(ell+3)) v.val (16*(i+1)+1) := by
      intro h
      have h' := vertexRecordAddress_injective (16*(ell+3)) u.val v.val (16*(j+1)+1) (16*(i+1)+1)
        (by omega) (by omega) h
      exact he ⟨by omega,Fin.ext h'.1⟩
    have hNever : ¬(i=j ∧ u=v ∧ v ∈ parentDomain logical j) := fun h => he ⟨h.1,h.2.1⟩
    unfold domainResidualMemoryUpdate
    split_ifs <;> simp [Function.update_of_ne hAddr,hNever]

lemma domain_residual_fold_at {n : ℕ} (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (v u : Fin n) (delta : ℝ) (j : ℕ) (hj : j ≤ logical.top) (R : ℤ → ℝ) :
    levelRealMemoryFold (domainResidualMemoryUpdate logical (16*(ell+3)) v delta) 0 (logical.top+1) R
        (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))=
      R (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))+
        (if u=v ∧ v ∈ parentDomain logical j then delta else 0) := by
  classical
  have h := level_memory_additive (domainResidualMemoryUpdate logical (16*(ell+3)) v delta)
    (fun i => if i=j ∧ u=v ∧ v ∈ parentDomain logical j then delta else 0)
    (logical.top+1) (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))
    (fun i hi R => domain_residual_update_at logical ell hDepth v u delta i j (by omega) hj R)
    (logical.top+1) 0 R (by omega)
  simp only [Nat.zero_add] at h
  have hSum : (∑ k ∈ Finset.range (logical.top+1), if k=j ∧ u=v ∧ v ∈ parentDomain logical j then delta else 0)=
      (if u=v ∧ v ∈ parentDomain logical j then delta else 0) := by
    by_cases ht : u=v ∧ v ∈ parentDomain logical j <;>
      simp [ht,Finset.mem_range,show j < logical.top+1 by omega]
  rw [hSum] at h
  exact h

lemma domain_residual_fold_field_frame {n : ℕ} (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (v u : Fin n) (delta : ℝ) (field : ℕ)
    (hField : field < 16*(ell+3)) (hSafe : ∀ i ≤ logical.top, field ≠ 16*(i+1)+1) (R : ℤ → ℝ) :
    levelRealMemoryFold (domainResidualMemoryUpdate logical (16*(ell+3)) v delta) 0 (logical.top+1) R
      (vertexRecordAddress (16*(ell+3)) u.val field)=R (vertexRecordAddress (16*(ell+3)) u.val field) := by
  apply level_memory_frame (limit:=logical.top+1)
  · intro i hi R'
    have hi' : i ≤ logical.top := by omega
    have hAddr : vertexRecordAddress (16*(ell+3)) u.val field ≠ vertexRecordAddress (16*(ell+3)) v.val (16*(i+1)+1) := by
      intro h
      exact hSafe i hi' (vertexRecordAddress_injective (16*(ell+3)) u.val v.val field (16*(i+1)+1) hField (by omega) h).2
    unfold domainResidualMemoryUpdate
    split_ifs <;> simp [Function.update_of_ne hAddr]
  · omega

lemma domain_residual_fold_positive_frame {n : ℕ} (logical : RecursiveState n) (width : ℕ)
    (v : Fin n) (delta : ℝ) (R : ℤ → ℝ) (z : ℤ) (hz : 0 ≤ z) :
    levelRealMemoryFold (domainResidualMemoryUpdate logical width v delta) 0 (logical.top+1) R z=R z := by
  apply level_memory_frame (limit:=logical.top+1)
  · intro i hi R'
    have hAddr : z ≠ vertexRecordAddress width v.val (16*(i+1)+1) := by
      have := vertexRecordAddress_negative width v.val (16*(i+1)+1)
      omega
    unfold domainResidualMemoryUpdate
    split_ifs <;> simp [Function.update_of_ne hAddr]
  · omega

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

lemma stored_neighbor_indicator_sum {n : ℕ} (g : InputGraph n) (source u : Fin n)
    (domain : Finset (Fin n)) (delta : ℝ) :
    (∑ i ∈ Finset.range (g.neighbors source).length,
      if u=storedNeighborVertex g source i ∧ u ∈ domain then delta else 0)=
      (if u ∈ g.neighbors source ∧ u ∈ domain then delta else 0) := by
  classical
  by_cases hHit : u ∈ g.neighbors source ∧ u ∈ domain
  · obtain ⟨j,hj,hju⟩ := List.getElem_of_mem hHit.1
    have hJ : storedNeighborVertex g source j=u := (storedNeighborVertex_eq g source j hj).trans hju
    rw [if_pos hHit]
    calc
      _ = (if u=storedNeighborVertex g source j ∧ u ∈ domain then delta else 0) := by
        apply Finset.sum_eq_single j
        · intro i hi hij
          have hi' : i < (g.neighbors source).length := Finset.mem_range.mp hi
          have hNe : u ≠ storedNeighborVertex g source i := by
            intro he
            have hEq : (g.neighbors source)[i]=(g.neighbors source)[j] := by
              rw [←storedNeighborVertex_eq g source i hi',←storedNeighborVertex_eq g source j hj,←he,hJ]
            exact hij ((g.nodup source).getElem_inj_iff.mp hEq)
          simp [hNe]
        · intro hj'
          exact False.elim (hj' (Finset.mem_range.mpr hj))
      _ = delta := by simp [hJ,hHit.2]
  · rw [if_neg hHit]
    apply Finset.sum_eq_zero
    intro i hi
    have hMiss : ¬(u=storedNeighborVertex g source i ∧ u ∈ domain) := by
      rintro ⟨hu,hd⟩
      exact hHit ⟨hu ▸ storedNeighborVertex_mem g source i (Finset.mem_range.mp hi),hd⟩
    exact if_neg hMiss

lemma stored_neighbor_fold_residual {n : ℕ} (g : InputGraph n) (source u : Fin n)
    (logical : RecursiveState n) (ell : ℕ) (hDepth : logical.top ≤ ell) (delta : ℝ)
    (j : ℕ) (hj : j ≤ logical.top) (payload : (ℤ → ℤ) × (ℤ → ℝ)) :
    (levelPayloadFold (storedNeighborMemoryUpdate g source logical ell delta) 0
      (g.neighbors source).length payload).2 (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))=
      payload.2 (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))+
        (if g.graph.Adj source u ∧ u ∈ parentDomain logical j then delta else 0) := by
  classical
  have h := level_payload_additive (storedNeighborMemoryUpdate g source logical ell delta)
    (fun i => if u=storedNeighborVertex g source i ∧ u ∈ parentDomain logical j then delta else 0)
    (g.neighbors source).length
    (fun p => p.2 (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1)))
    (by
      intro i hi p
      dsimp [storedNeighborMemoryUpdate]
      rw [domain_residual_fold_at logical ell hDepth _ u delta j hj p.2]
      by_cases he : u=storedNeighborVertex g source i
      · simp [he]
      · simp [he])
    (g.neighbors source).length 0 payload (by omega)
  simp only [Nat.zero_add] at h
  rw [stored_neighbor_indicator_sum] at h
  simpa only [g.correct source u] using h

lemma stored_neighbor_fold_real_positive {n : ℕ} (g : InputGraph n) (source : Fin n)
    (logical : RecursiveState n) (ell : ℕ) (delta : ℝ) (payload : (ℤ → ℤ) × (ℤ → ℝ)) (z : ℤ) (hz : 0 ≤ z) :
    (levelPayloadFold (storedNeighborMemoryUpdate g source logical ell delta) 0
      (g.neighbors source).length payload).2 z=payload.2 z := by
  apply level_payload_frame (storedNeighborMemoryUpdate g source logical ell delta) (limit:=(g.neighbors source).length) (eval:=fun p => p.2 z)
  · intro i hi p
    exact domain_residual_fold_positive_frame logical (16*(ell+3)) _ delta p.2 z hz
  · omega

lemma stored_neighbor_fold_real_field {n : ℕ} (g : InputGraph n) (source u : Fin n)
    (logical : RecursiveState n) (ell : ℕ) (hDepth : logical.top ≤ ell) (delta : ℝ)
    (payload : (ℤ → ℤ) × (ℤ → ℝ)) (field : ℕ) (hf : field < 16*(ell+3))
    (hSafe : ∀ i ≤ logical.top, field ≠ 16*(i+1)+1) :
    (levelPayloadFold (storedNeighborMemoryUpdate g source logical ell delta) 0
      (g.neighbors source).length payload).2 (vertexRecordAddress (16*(ell+3)) u.val field)=
        payload.2 (vertexRecordAddress (16*(ell+3)) u.val field) := by
  apply level_payload_frame (storedNeighborMemoryUpdate g source logical ell delta) (limit:=(g.neighbors source).length)
    (eval:=fun p => p.2 (vertexRecordAddress (16*(ell+3)) u.val field))
  · intro i hi p
    exact domain_residual_fold_field_frame logical ell hDepth _ u delta field hf hSafe p.2
  · omega

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
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointCoordinateCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma jointCoordinatePreludeCode_wellFormed : jointCoordinatePreludeCode.wellFormed := by
  simp [jointCoordinatePreludeCode,jointCoordinatePreludeInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma jointCoordinateSelfCode_wellFormed : jointCoordinateSelfCode.wellFormed := by
  simp [jointCoordinateSelfCode,jointCoordinateSelfInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma jointCoordinateNeighborCode_wellFormed : jointCoordinateNeighborCode.wellFormed := by
  simp [jointCoordinateNeighborCode,jointCoordinateNeighborInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma jointCoordinateNumericCode_wellFormed : jointCoordinateNumericCode.wellFormed :=
  ⟨jointCoordinatePreludeCode_wellFormed,cacheReadCode_wellFormed,exteriorPotentialAddCode_wellFormed,
    jointCoordinateSelfCode_wellFormed,domainResidualLoopCode_wellFormed,jointCoordinateNeighborCode_wellFormed,
    storedNeighborLoopCode_wellFormed⟩
lemma jointCoordinateProgramCode_wellFormed : jointCoordinateProgramCode.wellFormed :=
  ⟨jointCoordinateNumericCode_wellFormed,pendingTouchedRefreshCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointCoordinateScalars

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma joint_coordinate_self_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (degree : ℕ) (δ : ℝ)
    (hDegree : st.scalar.core.ptrs 60=(degree : ℤ)) (hDelta : st.scalar.core.regs 40=δ) :
    ∃ out, MachineEval m g ω jointCoordinateSelfCode st 4 out ∧
      out.scalar.core.regs 41=-((degree : ℝ)*δ) ∧ out.scalar.core.regs 42=(degree : ℝ)*δ ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+4 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let out := linearRun m g ω jointCoordinateSelfInstructions st
  obtain ⟨ex,hWork,hHalt⟩ := linear_execute m g ω jointCoordinateSelfInstructions
    (by simp [jointCoordinateSelfInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨out,ex,?_,?_,?_,?_,ex.query_frame (by decide),hWork,?_,hHalt⟩
  all_goals simp [out,linearRun,jointCoordinateSelfInstructions,atomState,machineStep,pcSet,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hDegree,hDelta]

lemma joint_coordinate_neighbor_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (α δ : ℝ)
    (hOne : st.scalar.core.regs 31=1) (hAlpha : st.scalar.core.regs 30=α) (hDelta : st.scalar.core.regs 40=δ) :
    ∃ out, MachineEval m g ω jointCoordinateNeighborCode st 2 out ∧
      out.scalar.core.regs 41=(1-α)*δ ∧ out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+2 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let out := linearRun m g ω jointCoordinateNeighborInstructions st
  obtain ⟨ex,hWork,hHalt⟩ := linear_execute m g ω jointCoordinateNeighborInstructions
    (by simp [jointCoordinateNeighborInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨out,ex,?_,?_,?_,ex.query_frame (by decide),hWork,?_,hHalt⟩
  all_goals simp [out,linearRun,jointCoordinateNeighborInstructions,atomState,machineStep,pcSet,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hOne,hAlpha,hDelta]

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

-- Proof module: Solutions.JointCoordinateNumericExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def jointCoordinateNumericPayload {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (v : Fin n) (δ : ℝ) (I : ℤ → ℤ) (R : ℤ → ℝ) : (ℤ → ℤ) × (ℤ → ℝ) :=
  levelPayloadFold (storedNeighborMemoryUpdate g v logical ell ((1-α)*δ)) 0 (g.neighbors v).length
    (I,levelRealMemoryFold (domainResidualMemoryUpdate logical (16*(ell+3)) v (-LocalPush.deg g.graph v*δ)) 0 (logical.top+1)
      (Function.update R (vertexRecordAddress (16*(ell+3)) v.val 0) (R (vertexRecordAddress (16*(ell+3)) v.val 0)+δ)))

set_option maxHeartbeats 12000000 in
lemma joint_coordinate_numeric_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε δ : ℝ) (ell length : ℕ) (v : Fin n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : v ∈ logical.stored)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) (hDelta : st.scalar.core.regs 40=δ) :
    let width := 16*(ell+3)
    ∃ steps out, MachineEval m g ω jointCoordinateNumericCode st steps out ∧
      steps ≤ 12*width+52+(logical.top+1)*(8*width+39)+
        (g.neighbors v).length*((logical.top+1)*(8*width+39)+4*width+25) ∧
      (out.scalar.integerMemory,out.scalar.core.mem)=jointCoordinateNumericPayload g logical ell α v δ st.scalar.integerMemory st.scalar.core.mem ∧
      out.scalar.core.ptrs 100=(logical.top : ℤ) ∧ out.scalar.core.ptrs 40=(v.val : ℤ) ∧
      out.scalar.core.ptrs 116=(v.val : ℤ) ∧ out.scalar.core.ptrs 120=((g.neighbors v).length : ℤ) ∧
      out.scalar.queries=st.scalar.queries+(g.neighbors v).length ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  intro width
  let a := linearRun m g ω jointCoordinatePreludeInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω jointCoordinatePreludeInstructions
    (by simp [jointCoordinatePreludeInstructions,unitInstruction,straightInstruction]) st hh
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,jointCoordinatePreludeInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aR : a.scalar.core.mem=st.scalar.core.mem := by
    simp [a,linearRun,jointCoordinatePreludeInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,jointCoordinatePreludeInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have a108 : a.scalar.core.ptrs 108=(logical.top : ℤ) := by
    simp [a,linearRun,jointCoordinatePreludeInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,pm.top]
  have a116 : a.scalar.core.ptrs 116=(v.val : ℤ) := by
    simp [a,linearRun,jointCoordinatePreludeInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hv]
  have a41 : a.scalar.core.ptrs 41=(width : ℤ) := by
    simp [a,linearRun,jointCoordinatePreludeInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,pm.width,width]
  obtain ⟨b,eb,b60,b61,bI,bR,bQ,bW,bO,bH⟩ := cache_read_exec m g ω a aH width v.val
    ((ea.pointer_frame 0 (by decide)).trans pm.zero) ((ea.pointer_frame 40 (by decide)).trans hv) a41
  have eCache := MachineEval.seq ea eb
  have b60' : b.scalar.core.ptrs 60=((g.neighbors v).length : ℤ) := by
    rw [b60,aI]
    exact pm.graphCache.degree v hStored
  have b61' : b.scalar.core.ptrs 61=st.scalar.integerMemory (vertexRecordAddress width v.val 1) := by rw [b61,aI]
  obtain ⟨c,ec,cR,cI,cQ,cW,cO,cH⟩ := exterior_potential_add_exec m g ω b bH width v
    ((eCache.pointer_frame 0 (by decide)).trans pm.zero) ((eCache.pointer_frame 40 (by decide)).trans hv)
    ((eCache.pointer_frame 50 (by decide)).trans pm.width) ((eCache.real_register_frame 31 (by decide)).trans pm.one)
  have ePotential := MachineEval.seq ea (MachineEval.seq eb ec)
  have cR' : c.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width v.val 0)
      (st.scalar.core.mem (vertexRecordAddress width v.val 0)+δ) := by
    rw [cR,bR,aR,eCache.real_register_frame 40 (by decide),hDelta]
  obtain ⟨d,ed,d41,d42,dI,dR,dQ,dW,dO,dH⟩ := joint_coordinate_self_exec m g ω c cH (g.neighbors v).length δ
    ((ec.pointer_frame 60 (by decide)).trans b60') ((ePotential.real_register_frame 40 (by decide)).trans hDelta)
  have eScalar := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  have dI' : d.scalar.integerMemory=st.scalar.integerMemory := dI.trans (cI.trans (bI.trans aI))
  have dRecords : ∀ i ≤ logical.top, v ∈ parentDomain logical i →
      d.scalar.integerMemory (vertexRecordAddress width v.val (16*(i+1)+2))=(if v ∈ (logical.frames i).active then 1 else 0) := by
    intro i hi hvD
    rw [dI']
    exact (pm.frames i hi).activeFlags v hvD
  have dDelta : d.scalar.core.regs 41=-LocalPush.deg g.graph v*δ := by
    rw [d41,compiler_neighbor_degree]
    simp only [LocalPush.deg,neg_mul]
  obtain ⟨r,e,ee,hr,e100,eI,eR,eCtx,eQ,eW,eO,eH⟩ := domain_residual_loop_exec m g ω logical width v (-LocalPush.deg g.graph v*δ) d dH
    hSubset dRecords ((eScalar.pointer_frame 0 (by decide)).trans pm.zero)
    ((eScalar.pointer_frame 50 (by decide)).trans pm.width)
    (((MachineEval.seq eb (MachineEval.seq ec ed)).pointer_frame 108 (by decide)).trans a108)
    ((eScalar.pointer_frame 40 (by decide)).trans hv) ((eScalar.real_register_frame 31 (by decide)).trans pm.one) dDelta
  have eSelf := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed ee)))
  obtain ⟨f,ef,f41,fI,fR,fQ,fW,fO,fH⟩ := joint_coordinate_neighbor_exec m g ω e eH α δ
    ((eSelf.real_register_frame 31 (by decide)).trans pm.one) ((eSelf.real_register_frame 30 (by decide)).trans pm.alphaRegister)
    ((eSelf.real_register_frame 40 (by decide)).trans hDelta)
  have eBefore := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee ef))))
  have fI' : f.scalar.integerMemory=st.scalar.integerMemory := fI.trans (eI.trans dI')
  have fRecords : ∀ i ≤ logical.top, ∀ w ∈ parentDomain logical i,
      f.scalar.integerMemory (vertexRecordAddress width w.val (16*(i+1)+2))=(if w ∈ (logical.frames i).active then 1 else 0) := by
    intro i hi w hw
    rw [fI']
    exact (pm.frames i hi).activeFlags w hw
  obtain ⟨z,out,eg,hz,g40,g100,gData,gCtx,gQ,gW,gO,gH⟩ := stored_neighbor_loop_exec m g ω v logical ell ((1-α)*δ)
    (st.scalar.integerMemory (vertexRecordAddress width v.val 1)) (pm.graphCache.basePositive v hStored) hDepth hSubset f fH
    ((eBefore.pointer_frame 0 (by decide)).trans pm.zero) ((eBefore.pointer_frame 50 (by decide)).trans pm.width)
    (((MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee ef)))).pointer_frame 108 (by decide)).trans a108)
    (((MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee ef)))).pointer_frame 116 (by decide)).trans a116)
    (((MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee ef))).pointer_frame 60 (by decide)).trans b60')
    (((MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee ef))).pointer_frame 61 (by decide)).trans b61')
    ((eBefore.real_register_frame 31 (by decide)).trans pm.one) f41
    (by intro i hi; rw [fI']; simpa only [storedNeighborVertex_eq g v i hi] using pm.graphCache.adjacency v hStored i hi hi) fRecords
  have ex : MachineEval m g ω jointCoordinateNumericCode st (3+((8*width+18)+((4*width+12)+(4+(r+(2+z)))))) out :=
    MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee (MachineEval.seq ef eg)))))
  have afterPrelude := MachineEval.seq eb (MachineEval.seq ec (MachineEval.seq ed (MachineEval.seq ee (MachineEval.seq ef eg))))
  refine ⟨_,out,ex,by dsimp only [width] at hr ⊢; omega,?_,g100,g40,(afterPrelude.pointer_frame 116 (by decide)).trans a116,gCtx.degree,?_,
    ex.unit_work jointCoordinateNumericCode_wellFormed (by decide) hh,gO.trans (fO.trans (eO.trans (dO.trans (cO.trans (bO.trans aO))))),gH⟩
  · rw [gData,fI',fR,eR,dR,cR']
    rfl
  · rw [gQ,fQ,eQ,dQ,cQ,bQ,ea.query_frame (by decide)]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointCoordinateMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma joint_numeric_residual {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (α : ℝ) (v u : Fin n) (δ : ℝ) (I : ℤ → ℤ) (R : ℤ → ℝ)
    (j : ℕ) (hj : j ≤ logical.top) (hu : u ∈ parentDomain logical j) :
    (jointCoordinateNumericPayload g logical ell α v δ I R).2 (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))=
      R (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))+
        (if u=v then -LocalPush.deg g.graph v*δ else 0)+(if g.graph.Adj u v then (1-α)*δ else 0) := by
  classical
  unfold jointCoordinateNumericPayload
  rw [stored_neighbor_fold_residual g v u logical ell hDepth _ j hj]
  dsimp only [Prod.snd]
  rw [domain_residual_fold_at logical ell hDepth v u _ j hj,
    vertex_memory_update_other_field R (16*(ell+3)) v.val u.val 0 (16*(j+1)+1) _ (by omega) (by omega) (by omega)]
  have hAdj : g.graph.Adj v u ↔ g.graph.Adj u v := g.graph.adj_comm v u
  simp only [hAdj,hu,and_true]
  by_cases he : u=v
  · subst u
    simp only [hu,and_self,and_true,if_true]
  · simp only [he,false_and,if_false,hu,and_true]

lemma joint_numeric_potential {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (α : ℝ) (v u : Fin n) (δ : ℝ) (I : ℤ → ℤ) (R : ℤ → ℝ) :
    (jointCoordinateNumericPayload g logical ell α v δ I R).2 (vertexRecordAddress (16*(ell+3)) u.val 0)=
      R (vertexRecordAddress (16*(ell+3)) u.val 0)+(if u=v then δ else 0) := by
  classical
  unfold jointCoordinateNumericPayload
  rw [stored_neighbor_fold_real_field g v u logical ell hDepth _ _ 0 (by omega) (by intros; omega)]
  dsimp only [Prod.snd]
  rw [domain_residual_fold_field_frame logical ell hDepth v u _ 0 (by omega) (by intros; omega)]
  by_cases he : u=v
  · subst u
    simp
  · rw [vertex_memory_update_other_vertex R (16*(ell+3)) v.val u.val 0 0 _ (by omega) (by omega) (fun h => he (Fin.ext h)),if_neg he,add_zero]

lemma joint_numeric_real_field {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (α : ℝ) (v u : Fin n) (δ : ℝ) (I : ℤ → ℤ) (R : ℤ → ℝ)
    (field : ℕ) (hf : field < 16*(ell+3)) (h0 : field ≠ 0) (hSafe : ∀ i ≤ logical.top, field ≠ 16*(i+1)+1) :
    (jointCoordinateNumericPayload g logical ell α v δ I R).2 (vertexRecordAddress (16*(ell+3)) u.val field)=
      R (vertexRecordAddress (16*(ell+3)) u.val field) := by
  unfold jointCoordinateNumericPayload
  rw [stored_neighbor_fold_real_field g v u logical ell hDepth _ _ field hf hSafe]
  dsimp only [Prod.snd]
  rw [domain_residual_fold_field_frame logical ell hDepth v u _ field hf hSafe]
  exact vertex_memory_update_other_field R (16*(ell+3)) v.val u.val 0 field _ (by omega) hf h0

lemma joint_numeric_real_positive {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (v : Fin n) (δ : ℝ) (I : ℤ → ℤ) (R : ℤ → ℝ) (z : ℤ) (hz : 0 ≤ z) :
    (jointCoordinateNumericPayload g logical ell α v δ I R).2 z=R z := by
  unfold jointCoordinateNumericPayload
  rw [stored_neighbor_fold_real_positive g v logical ell _ _ z hz]
  dsimp only [Prod.snd]
  rw [domain_residual_fold_positive_frame logical (16*(ell+3)) v _ _ z hz]
  apply Function.update_of_ne
  have := vertexRecordAddress_negative (16*(ell+3)) v.val 0
  omega

lemma joint_numeric_integer_eq {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (v : Fin n) (δ : ℝ) (I : ℤ → ℤ) (R : ℤ → ℝ)
    (hKnown : ∀ u ∈ g.neighbors v, I (vertexRecordAddress (16*(ell+3)) u.val 0)=((g.neighbors u).length : ℤ)) :
    (jointCoordinateNumericPayload g logical ell α v δ I R).1=I := by
  unfold jointCoordinateNumericPayload
  apply level_payload_invariant (storedNeighborMemoryUpdate g v logical ell ((1-α)*δ)) (g.neighbors v).length
    (fun p => p.1=I) _ (g.neighbors v).length 0 _ (by omega) rfl
  intro i hi payload hp
  change Function.update payload.1 (vertexRecordAddress (16*(ell+3)) (storedNeighborVertex g v i).val 0)
    ((g.neighbors (storedNeighborVertex g v i)).length : ℤ)=I
  rw [hp,←hKnown (storedNeighborVertex g v i) (storedNeighborVertex_mem g v i hi)]
  funext z
  by_cases hz : z=vertexRecordAddress (16*(ell+3)) (storedNeighborVertex g v i).val 0
  · subst z
    simp
  · exact Function.update_of_ne hz _ _

lemma stored_neighbor_known_degree {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (s : Fin n)
    (v u : Fin n) (hv : v ∈ logical.stored) (hu : u ∈ g.neighbors v) :
    u ∈ recursiveDegreeDomain g s logical := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨v,hv,List.mem_toFinset.mpr hu⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointEligibilityTransition

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma joint_transition_eligibility {n : ℕ} (g : InputGraph n) (α : ℝ)
    (logical : RecursiveState n) (δ : ℝ) (source : Fin n) (j width length : ℕ)
    (old out : MachineState) (floor : ℤ)
    (f : RecursiveFrameMemory g logical j width length old floor)
    (hKeys : KeysInvariant g (jointCoordinateUpdate g α logical source δ))
    (hj : j ≤ logical.top)
    (hQ : ((jointCoordinateUpdate g α logical source δ).frames j).q=(logical.frames j).q)
    (hFlags : ∀ u ∈ parentDomain (jointCoordinateUpdate g α logical source δ) j,
      out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+2))=
        if u ∈ ((jointCoordinateUpdate g α logical source δ).frames j).active then 1 else 0)
    (hResidual : ∀ u ∈ parentDomain (jointCoordinateUpdate g α logical source δ) j,
      out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+1))=
        ((jointCoordinateUpdate g α logical source δ).frames j).residual u)
    (hDegree : ∀ u ∈ insert source (g.neighbors source).toFinset,
      out.scalar.integerMemory (vertexRecordAddress width u.val 0)=((g.neighbors u).length : ℤ))
    (hOtherDegree : ∀ u ∉ insert source (g.neighbors source).toFinset,
      out.scalar.integerMemory (vertexRecordAddress width u.val 0)=old.scalar.integerMemory (vertexRecordAddress width u.val 0)) :
    ∀ u ∈ parentDomain (jointCoordinateUpdate g α logical source δ) j,
      u.val ∈ ((jointCoordinateUpdate g α logical source δ).frames j).exterior.image Fin.val ↔
        out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+2))=0 ∧
        ((jointCoordinateUpdate g α logical source δ).frames j).q*(out.scalar.integerMemory (vertexRecordAddress width u.val 0) : ℝ) <
          out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+1)) := by
  classical
  intro u hu
  rw [hFlags u hu,hResidual u hu,compiler_fin_val_image]
  by_cases hT : u ∈ insert source (g.neighbors source).toFinset
  · rw [(hKeys j (by rw [joint_coordinate_top]; exact hj)).1 u,hDegree u hT,compiler_neighbor_degree]
    simp [exteriorKey,hu,LocalPush.deg]
  · have hD : u ∈ parentDomain (jointCoordinateUpdate g α logical source δ) j ↔ u ∈ parentDomain logical j := by rw [joint_coordinate_domain]
    have hA : u ∈ ((jointCoordinateUpdate g α logical source δ).frames j).active ↔ u ∈ (logical.frames j).active := by rw [joint_coordinate_active]
    have hR := joint_coordinate_outside_residual g α logical source u δ hT j
    have huOld := hD.mp hu
    rw [(joint_coordinate_outside_queues g α logical source u δ hT j).1,hOtherDegree u hT,hQ,hR]
    have hOld := f.exteriorData.eligibility u huOld
    rw [compiler_fin_val_image,f.activeFlags u huOld,f.residual u huOld] at hOld
    simpa only [hA] using hOld

lemma joint_transition_high_eligibility {n : ℕ} (g : InputGraph n) (α : ℝ)
    (logical : RecursiveState n) (δ : ℝ) (source : Fin n) (j width length : ℕ)
    (old out : MachineState) (floor : ℤ)
    (f : RecursiveFrameMemory g logical j width length old floor)
    (hKeys : KeysInvariant g (jointCoordinateUpdate g α logical source δ))
    (hj : j ≤ logical.top)
    (hTheta : ((jointCoordinateUpdate g α logical source δ).frames j).theta=(logical.frames j).theta)
    (hFlags : ∀ u ∈ parentDomain (jointCoordinateUpdate g α logical source δ) j,
      out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+2))=
        if u ∈ ((jointCoordinateUpdate g α logical source δ).frames j).active then 1 else 0)
    (hResidual : ∀ u ∈ parentDomain (jointCoordinateUpdate g α logical source δ) j,
      out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+1))=
        ((jointCoordinateUpdate g α logical source δ).frames j).residual u)
    (hDegree : ∀ u ∈ insert source (g.neighbors source).toFinset,
      out.scalar.integerMemory (vertexRecordAddress width u.val 0)=((g.neighbors u).length : ℤ))
    (hOtherDegree : ∀ u ∉ insert source (g.neighbors source).toFinset,
      out.scalar.integerMemory (vertexRecordAddress width u.val 0)=old.scalar.integerMemory (vertexRecordAddress width u.val 0)) :
    ∀ u ∈ parentDomain (jointCoordinateUpdate g α logical source δ) j,
      u.val ∈ ((jointCoordinateUpdate g α logical source δ).frames j).high.image Fin.val ↔
        out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+2)) ≠ 0 ∧
        3*((jointCoordinateUpdate g α logical source δ).frames j).theta*(out.scalar.integerMemory (vertexRecordAddress width u.val 0) : ℝ) ≤
          out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+1)) := by
  classical
  intro u hu
  rw [hFlags u hu,hResidual u hu,compiler_fin_val_image]
  by_cases hT : u ∈ insert source (g.neighbors source).toFinset
  · rw [(hKeys j (by rw [joint_coordinate_top]; exact hj)).2 u,hDegree u hT,compiler_neighbor_degree]
    simp [highKey,LocalPush.deg]
  · have hD : u ∈ parentDomain (jointCoordinateUpdate g α logical source δ) j ↔ u ∈ parentDomain logical j := by rw [joint_coordinate_domain]
    have hA : u ∈ ((jointCoordinateUpdate g α logical source δ).frames j).active ↔ u ∈ (logical.frames j).active := by rw [joint_coordinate_active]
    have hR := joint_coordinate_outside_residual g α logical source u δ hT j
    have huOld := hD.mp hu
    rw [(joint_coordinate_outside_queues g α logical source u δ hT j).2,hOtherDegree u hT,hTheta,hR]
    have hOld := f.highValid u huOld
    rw [compiler_fin_val_image,f.activeFlags u huOld,f.residual u huOld] at hOld
    simpa only [hA] using hOld


end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointCoordinatePendingFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 2500000 in
def joint_coordinate_pending_frame {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε δ : ℝ) (ell length : ℕ) (old out : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (v : Fin n) (hStored : v ∈ logical.stored)
    (hKeys : KeysInvariant g (jointCoordinateUpdate g α logical v δ))
    (hI : out.scalar.integerMemory=old.scalar.integerMemory)
    (hR : out.scalar.core.mem=(jointCoordinateNumericPayload g logical ell α v δ old.scalar.integerMemory old.scalar.core.mem).2)
    (hFree : old.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20) (j : ℕ) (hj : j ≤ logical.top) :
    FramePendingKeys g (jointCoordinateUpdate g α logical v δ) j (16*(ell+3)) length out (128+32*((ell+2 : ℕ) : ℤ)) := by
  have hDomain := joint_coordinate_domain g α logical v δ j
  have hActive := joint_coordinate_active g α logical v δ j
  have hReference := (joint_coordinate_reference_budget g α logical v δ j).1
  have hW := (joint_coordinate_reference_budget g α logical v δ j).2
  have hRes : ∀ u ∈ parentDomain (jointCoordinateUpdate g α logical v δ) j,
      out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))=
        ((jointCoordinateUpdate g α logical v δ).frames j).residual u := by
    intro u hu
    rw [hDomain] at hu
    rw [hR,joint_numeric_residual g logical ell hDepth α v u δ _ _ j hj hu,
      (pm.frames j hj).residual u hu,joint_coordinate_residual g α logical v u δ j hj hu]
  have hFlags : ∀ u ∈ parentDomain (jointCoordinateUpdate g α logical v δ) j,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+2))=
        if u ∈ ((jointCoordinateUpdate g α logical v δ).frames j).active then 1 else 0 := by
    intro u hu
    rw [hDomain] at hu
    rw [hI,hActive]
    exact (pm.frames j hj).activeFlags u hu
  have hDegree : ∀ u ∈ insert v (g.neighbors v).toFinset,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) u.val 0)=((g.neighbors u).length : ℤ) := by
    intro u hu
    rw [hI]
    rcases Finset.mem_insert.mp hu with hu|hu
    · subst u
      exact pm.graphCache.degree v hStored
    · exact pm.knownDegree u (stored_neighbor_known_degree g logical s v u hStored (List.mem_toFinset.mp hu))
  refine (FramePendingKeys.ofMemory (pm.frames j hj)).numeric_frame hFree hDomain hActive
    (joint_coordinate_static g α logical v δ j) ?_ ?_ ?_ ?_ hRes ?_ ?_ ?_ ?_
  · intro slot hs
    exact congrFun hI _
  · intro slot hs hn
    rw [hR]
    exact joint_numeric_real_positive g logical ell α v δ _ _ _ (by have := levelHeaderAddress_positive j slot; omega)
  · rw [hR,joint_numeric_real_positive g logical ell α v δ _ _ _ (by have := levelHeaderAddress_positive j 4; omega),hW]
    exact (pm.frames j hj).W
  · intro u hu
    rw [hDomain] at hu
    rw [hR,hReference,joint_numeric_real_field g logical ell hDepth α v u δ _ _ (16*(j+1)) (by omega) (by omega) (by intros; omega)]
    exact (pm.frames j hj).reference u hu
  · intro u hu offset hlo hhi
    exact congrFun hI _
  · intro z hz
    exact congrFun hI _
  · exact joint_transition_eligibility g α logical δ v j (16*(ell+3)) length old out _ (pm.frames j hj) hKeys hj
      (joint_coordinate_parameters g α logical v δ j).1 hFlags hRes hDegree (by intros; exact congrFun hI _)
  · exact joint_transition_high_eligibility g α logical δ v j (16*(ell+3)) length old out _ (pm.frames j hj) hKeys hj
      (joint_coordinate_parameters g α logical v δ j).2 hFlags hRes hDegree (by intros; exact congrFun hI _)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointCoordinatePendingMemory

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 5000000 in
def joint_coordinate_pending_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε δ : ℝ) (ell length : ℕ) (old out : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (v : Fin n) (hStored : v ∈ logical.stored)
    (hKeys : KeysInvariant g (jointCoordinateUpdate g α logical v δ))
    (hI : out.scalar.integerMemory=old.scalar.integerMemory)
    (hR : out.scalar.core.mem=(jointCoordinateNumericPayload g logical ell α v δ old.scalar.integerMemory old.scalar.core.mem).2)
    (steps : ℕ) (ex : MachineEval m g ω jointCoordinateNumericCode old steps out)
    (hTop : out.scalar.core.ptrs 100=(logical.top : ℤ)) (hOutput : out.output=old.output) :
    MachinePendingKeys g s α ε ell length (jointCoordinateUpdate g α logical v δ) out := by
  have hFree : out.scalar.core.ptrs 20=old.scalar.core.ptrs 20 := ex.pointer_frame 20 (by decide)
  let frames := fun j hj => joint_coordinate_pending_frame g logical s α ε δ ell length old out pm hDepth v hStored
    hKeys hI hR (by rw [hFree]) j hj
  refine {
    zero := (ex.pointer_frame 0 (by decide)).trans pm.zero
    top := hTop
    width := (ex.pointer_frame 50 (by decide)).trans pm.width
    alphaRegister := (ex.real_register_frame 30 (by decide)).trans pm.alphaRegister
    one := (ex.real_register_frame 31 (by decide)).trans pm.one
    alphaMemory := by rw [hR,joint_numeric_real_positive g logical ell α v δ _ _ 0 (by decide)]; exact pm.alphaMemory
    epsilonMemory := by rw [hR,joint_numeric_real_positive g logical ell α v δ _ _ 1 (by decide)]; exact pm.epsilonMemory
    depthMemory := by rw [hI]; exact pm.depthMemory
    lengthMemory := by rw [hI]; exact pm.lengthMemory
    seedMemory := by rw [hI]; exact pm.seedMemory
    allocator := by rw [hFree]; exact pm.allocator
    potential := ?_
    seedMarker := ?_
    boundary := by rw [hI]; exact pm.boundary
    graphCache := by rw [hI,hFree]; exact pm.graphCache
    rowAbove := by rw [hI]; exact pm.rowAbove
    knownDegree := by rw [hI]; exact pm.knownDegree
    unknownDegree := by rw [hI]; exact pm.unknownDegree
    frames := frames
    pieceSeparation := pm.pieceSeparation
    frameSeparation := pm.frameSeparation
    cacheSeparation := ?_
    output := hOutput.trans pm.output
  }
  · intro u
    rw [hR,joint_numeric_potential g logical ell hDepth α v u δ _ _,pm.potential u]
    rfl
  · intro u
    rw [hR,joint_numeric_real_field g logical ell hDepth α v u δ _ _ 2 (by omega) (by omega) (by intros; omega)]
    exact pm.seedMarker u
  · intro j hj
    change Disjoint (pm.frames j hj).owned (cachedRowCells g out.scalar.integerMemory (16*(ell+3)) logical.stored)
    rw [hI]
    exact pm.cacheSeparation j hj

lemma joint_coordinate_pending_memory_mass (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε δ : ℝ) (ell length : ℕ) (old out : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (v : Fin n) (hStored : v ∈ logical.stored)
    (hKeys : KeysInvariant g (jointCoordinateUpdate g α logical v δ))
    (hI : out.scalar.integerMemory=old.scalar.integerMemory)
    (hR : out.scalar.core.mem=(jointCoordinateNumericPayload g logical ell α v δ old.scalar.integerMemory old.scalar.core.mem).2)
    (steps : ℕ) (ex : MachineEval m g ω jointCoordinateNumericCode old steps out)
    (hTop : out.scalar.core.ptrs 100=(logical.top : ℤ)) (hOutput : out.output=old.output) :
    (joint_coordinate_pending_memory m g ω logical s α ε δ ell length old out pm hDepth v hStored hKeys hI hR steps ex hTop hOutput).queueMass=pm.queueMass := rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointCoordinateExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 12000000 in
lemma joint_coordinate_foreign_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε δ : ℝ) (ell length N rank : ℕ) (v : Fin n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : v ∈ logical.stored) (hKeys : KeysInvariant g logical)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) (hDelta : st.scalar.core.regs 40=δ)
    (hMass : pm.queueMass+2*(logical.top+1)*((g.neighbors v).length+1) ≤ N) (hCap : rank < length) (hPow : N < 2^rank) :
    let width := 16*(ell+3)
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (jointCoordinateUpdate g α logical v δ) out,
      MachineEval m g ω jointCoordinateProgramCode st steps out ∧
      steps ≤ 12*width+62+(logical.top+1)*(8*width+39)+
        (g.neighbors v).length*((logical.top+1)*(8*width+39)+4*width+25)+
        ((g.neighbors v).length+1)*((logical.top+1)*(42*rank+60*width+284)+4*width+25) ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*((g.neighbors v).length+1) ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧ MemoryBufferFrame pm memory := by
  intro width
  let next := jointCoordinateUpdate g α logical v δ
  have hNextTop : next.top=logical.top := rfl
  have nextKeys : KeysInvariant g next := joint_coordinate_keys g α logical v δ hKeys
  obtain ⟨u,a,ea,hu,aData,a100,a40,a116,a120,aQ,aW,aO,aH⟩ :=
    joint_coordinate_numeric_exec m g ω logical s α ε δ ell length v st hh pm hDepth hStored hSubset hv hDelta
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    have h := congrArg Prod.fst aData
    change a.scalar.integerMemory=_ at h
    rw [joint_numeric_integer_eq g logical ell α v δ st.scalar.integerMemory st.scalar.core.mem
      (fun w hw => pm.knownDegree w (stored_neighbor_known_degree g logical s v w hStored hw))] at h
    exact h
  have aR : a.scalar.core.mem=(jointCoordinateNumericPayload g logical ell α v δ st.scalar.integerMemory st.scalar.core.mem).2 := congrArg Prod.snd aData
  let memA := joint_coordinate_pending_memory m g ω logical s α ε δ ell length st a pm hDepth v hStored nextKeys aI aR u ea a100 aO
  have aMass : memA.queueMass=pm.queueMass := joint_coordinate_pending_memory_mass m g ω logical s α ε δ ell length st a pm hDepth v hStored nextKeys aI aR u ea a100 aO
  have activeD : ∀ i ≤ next.top, (next.frames i).active ⊆ parentDomain next i := by
    intro i hi
    rw [joint_coordinate_active,joint_coordinate_domain]
    exact hSubset i hi
  have extD : ∀ i ≤ next.top, (next.frames i).exterior ⊆ parentDomain next i := by
    intro i hi w hw
    exact ((nextKeys i hi).1 w).mp hw |>.1
  have highD : ∀ i ≤ next.top, (next.frames i).high ⊆ parentDomain next i := by
    intro i hi w hw
    exact activeD i hi (((nextKeys i hi).2 w).mp hw).1
  have extOutside : ∀ i, ∀ hi : i ≤ next.top,
      (next.frames i).exterior.image Fin.val \ (insert v (g.neighbors v).toFinset).image Fin.val ⊆ (memA.frames i hi).exteriorObject.keys := by
    intro i hi
    change (next.frames i).exterior.image Fin.val \ (insert v (g.neighbors v).toFinset).image Fin.val ⊆ (pm.frames i hi).exteriorObject.keys
    exact (joint_coordinate_queue_cover g α logical v δ i _ _ (pm.frames i hi).exteriorCover (pm.frames i hi).highCover).1
  have highOutside : ∀ i, ∀ hi : i ≤ next.top,
      (next.frames i).high.image Fin.val \ (insert v (g.neighbors v).toFinset).image Fin.val ⊆ (memA.frames i hi).highObject.keys := by
    intro i hi
    change (next.frames i).high.image Fin.val \ (insert v (g.neighbors v).toFinset).image Fin.val ⊆ (pm.frames i hi).highObject.keys
    exact (joint_coordinate_queue_cover g α logical v δ i _ _ (pm.frames i hi).exteriorCover (pm.frames i hi).highCover).2
  have boolOutside : ∀ i ≤ next.top,
      HighBooleanRecords a.scalar.integerMemory a.scalar.core.mem width (16*(i+1)) (next.frames i).theta
        (parentDomain next i \ insert v (g.neighbors v).toFinset) := by
    intro i hi w hw
    have hiOld : i ≤ logical.top := by rw [←hNextTop]; exact hi
    obtain ⟨hwD,hwT⟩ := Finset.mem_sdiff.mp hw
    have hOldD : w ∈ parentDomain logical i := by rw [joint_coordinate_domain] at hwD; exact hwD
    have hNe : w ≠ v := by intro he; subst w; exact hwT (Finset.mem_insert_self _ _)
    have hAdj : ¬g.graph.Adj w v := by
      intro he
      exact hwT (Finset.mem_insert_of_mem (List.mem_toFinset.mpr ((g.correct v w).mpr (g.graph.adj_symm he))))
    have hBits : a.scalar.core.mem (vertexRecordAddress width w.val (16*(i+1)+4))=
        st.scalar.core.mem (vertexRecordAddress width w.val (16*(i+1)+4)) := by
      rw [aR]
      exact joint_numeric_real_field g logical ell hDepth α v w δ _ _ (16*(i+1)+4) (by omega) (by omega) (by intros; omega)
    have hRes : a.scalar.core.mem (vertexRecordAddress width w.val (16*(i+1)+1))=
        st.scalar.core.mem (vertexRecordAddress width w.val (16*(i+1)+1)) := by
      rw [aR,joint_numeric_residual g logical ell hDepth α v w δ _ _ i hi hOldD]
      simp only [hNe,hAdj,if_false,add_zero]
      rfl
    change a.scalar.core.mem (vertexRecordAddress width w.val (16*(i+1)+4))=_
    rw [hBits,aI,hRes,(joint_coordinate_parameters g α logical v δ i).2]
    exact (pm.frames i hi).highBoolean w hOldD
  have budget : memA.queueMass+2*(next.top+1)*((g.neighbors v).length+1) ≤ N := by rw [aMass]; exact hMass
  obtain ⟨r,out,memory,er,hr,rMass,r40,rQ,rW,rO,rH,rPositive,rInteger⟩ := pending_touched_refresh_foreign_exec m g ω s α ε ell length N rank next
    a aH memA hDepth activeD extD highD v hStored a116 a40 a120 budget hCap hPow extOutside highOutside boolOutside
  have ex : MachineEval m g ω jointCoordinateProgramCode st (u+r) out := MachineEval.seq ea er
  refine ⟨_,out,memory,ex,?_,?_,r40,ex.unit_work jointCoordinateProgramCode_wellFormed (by decide) hh,rO.trans aO,rH,?_⟩
  · change r ≤ ((g.neighbors v).length+1)*((logical.top+1)*(42*rank+60*(16*(ell+3))+284)+4*(16*(ell+3))+25)+10 at hr
    dsimp only [width]
    omega
  · simpa only [aMass,hNextTop] using rMass

  · have aFree : a.scalar.core.ptrs 20=st.scalar.core.ptrs 20 := ea.pointer_frame 20 (by decide)
    refine ⟨rfl,?_,?_,?_,?_,fun z => (rInteger.indexFrame z).trans (congrFun aI _)⟩
    · rw [←aFree]
      exact rInteger.free
    · intro i hi hn z hz hBelow
      have hOld : z ∈ (memA.frames i hn).owned := rInteger.oldOwned i hn z hz (by rw [aFree]; exact hBelow)
      exact hOld
    · intro z hz hBelow hOutside
      have hOutsideA : ∀ i, ∀ hi : i ≤ next.top, z ∉ (memA.frames i hi).owned := by
        intro i hi
        change z ∉ (pm.frames i hi).owned
        exact hOutside i hi
      exact (rInteger.integerFrame z hz (by rw [aFree]; exact hBelow) hOutsideA).trans (congrFun aI z)
    · intro z hz
      rw [rPositive z hz,aR,joint_numeric_real_positive g logical ell α v δ _ _ z hz]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointSolveIterationCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma jointSolveIterationInitCode_wellFormed : jointSolveIterationInitCode.wellFormed := by
  simp [jointSolveIterationInitCode,jointSolveIterationInitInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma jointSolveIterationReadCode_wellFormed : jointSolveIterationReadCode.wellFormed := by
  simp [jointSolveIterationReadCode,jointSolveIterationReadInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma jointSolveIterationBodyCode_wellFormed : jointSolveIterationBodyCode.wellFormed := by
  refine ⟨jointSolveIterationReadCode_wellFormed,jointCoordinateProgramCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma jointSolveIterationLoopCode_wellFormed : jointSolveIterationLoopCode.wellFormed := jointSolveIterationBodyCode_wellFormed
lemma jointSolveIterationCode_wellFormed : jointSolveIterationCode.wellFormed :=
  ⟨jointSolveIterationInitCode_wellFormed,jointSolveIterationLoopCode_wellFormed⟩

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

-- Proof module: Solutions.JointSolveIterationBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 10000000 in
lemma joint_solve_iteration_body_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ)
    (e : Fin k → Fin n) (h : Fin n → ℝ) (enumBase answerBase : ℤ) (i : Fin k)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (buffers : SolveIterationBuffers pm enumBase answerBase e h)
    (hDepth : logical.top ≤ ell) (hStored : ∀ j : Fin k, e j ∈ logical.stored) (hKeys : KeysInvariant g logical)
    (hSubset : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (h140 : st.scalar.core.ptrs 140=enumBase) (h141 : st.scalar.core.ptrs 141=answerBase)
    (h143 : st.scalar.core.ptrs 143=(i.val : ℤ))
    (hMass : pm.queueMass+2*(logical.top+1)*((g.neighbors (e i)).length+1) ≤ N) (hCap : rank < length) (hPow : N < 2^rank) :
    let width := 16*(ell+3)
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (jointCoordinateUpdate g α logical (e i) (h (e i))) out,
      MachineEval m g ω jointSolveIterationBodyCode st steps out ∧
      steps ≤ 12*width+67+(logical.top+1)*(8*width+39)+
        (g.neighbors (e i)).length*((logical.top+1)*(8*width+39)+4*width+25)+
        ((g.neighbors (e i)).length+1)*((logical.top+1)*(42*rank+60*width+284)+4*width+25) ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*((g.neighbors (e i)).length+1) ∧
      out.scalar.core.ptrs 143=((i.val+1 : ℕ) : ℤ) ∧ MemoryBufferFrame pm memory ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  intro width
  obtain ⟨a,ea,a40,aR40,aI,aR,aQ,aW,aO,aH⟩ := joint_solve_iteration_read_exec m g ω st hh enumBase answerBase i.val (e i) (h (e i))
    h140 h141 h143 (buffers.enumeration i) (buffers.answers i)
  have aP : ∀ r ∈ ([0,20,50,100] : List ℕ), a.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ea.pointer_frame _ (by decide)
  have aG : ∀ r ∈ ([30,31] : List ℕ), a.scalar.core.regs r=st.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ea.real_register_frame _ (by decide)
  let aMem := pm.frame aI aR aP aG aO
  have aFrame : MemoryBufferFrame pm aMem := MemoryBufferFrame.frame pm aI aR aP aG aO
  obtain ⟨u,b,bMem,eb,hu,bMass,b40,bW,bO,bH,bFrame⟩ := joint_coordinate_foreign_exec m g ω logical s α ε (h (e i)) ell length N rank
    (e i) a aH aMem hDepth (hStored i) hKeys hSubset a40 aR40 hMass hCap hPow
  have ePrefix := MachineEval.seq ea eb
  have b143 : b.scalar.core.ptrs 143=(i.val : ℤ) := (ePrefix.pointer_frame 143 (by decide)).trans h143
  let out := payUnit (pointerWrite b 143 ((i.val+1 : ℕ) : ℤ))
  have ec : MachineEval m g ω (coreCode (.pinc 143)) b 1 out := by
    simpa only [out,coreCode,b143,Nat.cast_add,Nat.cast_one] using pinc_eval m g ω b 143 bH
  let memory := (bMem.pointerWrite 143 ((i.val+1 : ℕ) : ℤ) (by decide)).payUnit
  have ex : MachineEval m g ω jointSolveIterationBodyCode st (4+(u+1)) out := MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨_,out,memory,ex,by dsimp only [width]; omega,bMass,by simp [out,payUnit,pcSet,pointerWrite],?_,
    ex.unit_work jointSolveIterationBodyCode_wellFormed (by decide) hh,bO.trans aO,bH⟩
  exact (((aFrame.trans bFrame).trans (MemoryBufferFrame.pointerWrite bMem 143 ((i.val+1 : ℕ) : ℤ) (by decide))).trans
    (MemoryBufferFrame.payUnit (bMem.pointerWrite 143 ((i.val+1 : ℕ) : ℤ) (by decide))))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointSolveIterationBound

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation

def jointCoordinateBound (ell top rank degree : ℕ) : ℕ :=
  let width := 16*(ell+3)
  12*width+62+(top+1)*(8*width+39)+degree*((top+1)*(8*width+39)+4*width+25)+
    (degree+1)*((top+1)*(42*rank+60*width+284)+4*width+25)

lemma jointCoordinateBound_le (ell top rank degree : ℕ) :
    jointCoordinateBound ell top rank degree+7 ≤ jointSolveIterationFactor ell top rank*(degree+1) := by
  let w := 16*(ell+3)
  have hConst : 12*w+62 ≤ (degree+1)*(12*w+62) := Nat.le_mul_of_pos_left _ (by omega)
  have hExtra : degree*(4*w+25) ≤ (degree+1)*(4*w+25) := Nat.mul_le_mul_right _ (by omega)
  have hFirst : jointCoordinateBound ell top rank degree ≤
      (degree+1)*((top+1)*(42*rank+68*w+323)+20*w+112) := by
    unfold jointCoordinateBound
    change 12*w+62+(top+1)*(8*w+39)+degree*((top+1)*(8*w+39)+4*w+25)+
      (degree+1)*((top+1)*(42*rank+60*w+284)+4*w+25) ≤ _
    have hEq : degree*((top+1)*(8*w+39)+4*w+25)=degree*((top+1)*(8*w+39))+degree*(4*w+25) := by ring
    rw [hEq]
    calc
      _ ≤ (degree+1)*(12*w+62)+(top+1)*(8*w+39)+degree*((top+1)*(8*w+39))+(degree+1)*(4*w+25)+
          (degree+1)*((top+1)*(42*rank+60*w+284)+4*w+25) := by omega
      _ = _ := by ring
  have hLift : (degree+1)*(20*w+112) ≤ (top+1)*((degree+1)*(20*w+112)) := Nat.le_mul_of_pos_left _ (by omega)
  have hBase : jointCoordinateBound ell top rank degree ≤ (top+1)*(degree+1)*(42*rank+88*w+435) := by
    calc
      _ ≤ (degree+1)*((top+1)*(42*rank+68*w+323)+20*w+112) := hFirst
      _ = (top+1)*(degree+1)*(42*rank+68*w+323)+(degree+1)*(20*w+112) := by ring
      _ ≤ (top+1)*(degree+1)*(42*rank+68*w+323)+(top+1)*((degree+1)*(20*w+112)) := by omega
      _ = _ := by ring
  have hSeven : 7 ≤ (top+1)*(degree+1)*7 := Nat.le_mul_of_pos_left _ (by positivity)
  unfold jointSolveIterationFactor
  change jointCoordinateBound ell top rank degree+7 ≤ (top+1)*(42*rank+88*w+442)*(degree+1)
  calc
    _ ≤ (top+1)*(degree+1)*(42*rank+88*w+435)+(top+1)*(degree+1)*7 := by omega
    _ = _ := by ring

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointSolveIterationLoop

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 18000000 in
lemma joint_solve_iteration_loop_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ) (e : Fin k → Fin n) (h : Fin n → ℝ)
    (enumBase answerBase : ℤ) (hCap : rank < length) (hPow : N < 2^rank) (remaining : ℕ) :
    ∀ (index : ℕ) (logical : RecursiveState n) (st : MachineState) (hh : st.scalar.halted=false)
      (pm : RecursiveMachineMemory g s α ε ell length logical st),
      SolveIterationBuffers pm enumBase answerBase e h → index+remaining=k → logical.top ≤ ell →
      (∀ j : Fin k, e j ∈ logical.stored) → KeysInvariant g logical →
      (∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j) →
      st.scalar.core.ptrs 140=enumBase → st.scalar.core.ptrs 141=answerBase → st.scalar.core.ptrs 142=(k : ℤ) → st.scalar.core.ptrs 143=(index : ℤ) →
      pm.queueMass+2*(logical.top+1)*jointSolveIterationVolume g e index remaining ≤ N →
      ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (jointSolveIterationState g α e h index remaining logical) out,
        MachineEval m g ω jointSolveIterationLoopCode st steps out ∧
        steps ≤ jointSolveIterationFactor ell logical.top rank*jointSolveIterationVolume g e index remaining+1 ∧
        memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*jointSolveIterationVolume g e index remaining ∧
        out.scalar.core.ptrs 143=(k : ℤ) ∧ MemoryBufferFrame pm memory ∧
        out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  induction remaining with
  | zero =>
    intro index logical st hh pm buffers hCount hDepth hStored hKeys hSubset h140 h141 h142 h143 hBudget
    have hIndex : index=k := by omega
    have ex : MachineEval m g ω jointSolveIterationLoopCode st 1 (payUnit st) :=
      MachineEval.pointerDone hh (by rw [h142,h143,hIndex])
    refine ⟨1,payUnit st,pm.payUnit,ex,by simp [jointSolveIterationVolume],?_,?_,MemoryBufferFrame.payUnit pm,
      ex.unit_work jointSolveIterationLoopCode_wellFormed (by decide) hh,rfl,hh⟩
    · change pm.queueMass ≤ pm.queueMass+2*(logical.top+1)*0
      omega
    · change st.scalar.core.ptrs 143=(k : ℤ)
      rw [h143,hIndex]
  | succ remaining ih =>
    intro index logical st hh pm buffers hCount hDepth hStored hKeys hSubset h140 h141 h142 h143 hBudget
    have hi : index < k := by omega
    let i : Fin k := ⟨index,hi⟩
    let middle := jointCoordinateUpdate g α logical (e i) (h (e i))
    let D := (g.neighbors (e i)).length+1
    let V := jointSolveIterationVolume g e (index+1) remaining
    let Q := 2*(logical.top+1)
    let F := jointSolveIterationFactor ell logical.top rank
    have hVolume : jointSolveIterationVolume g e index (remaining+1)=D+V := by
      simp only [jointSolveIterationVolume,dif_pos hi]
      rfl
    have hBudget' : pm.queueMass+Q*D+Q*V ≤ N := by
      rw [hVolume] at hBudget
      change pm.queueMass+Q*(D+V) ≤ N at hBudget
      rw [Nat.mul_add] at hBudget
      omega
    have preFrame := MemoryBufferFrame.payUnit pm
    have preBuffers := buffers.frame preFrame
    obtain ⟨u,b,bMem,eb,hu,bMass,b143,bFrame,bW,bO,bH⟩ := joint_solve_iteration_body_exec m g ω logical s α ε ell length N rank e h enumBase answerBase i
      (payUnit st) hh pm.payUnit preBuffers hDepth hStored hKeys hSubset h140 h141 h143
      (by change pm.queueMass+Q*D ≤ N; omega) hCap hPow
    have nextFrame := (preFrame.trans bFrame).trans (MemoryBufferFrame.payUnit bMem)
    have nextBuffers := buffers.frame nextFrame
    have hMiddleTop : middle.top=logical.top := rfl
    have hMiddleStored : ∀ j : Fin k, e j ∈ middle.stored := hStored
    have hMiddleKeys : KeysInvariant g middle := joint_coordinate_keys g α logical (e i) (h (e i)) hKeys
    have hMiddleSubset : ∀ j ≤ middle.top, (middle.frames j).active ⊆ parentDomain middle j := by
      intro j hj
      rw [joint_coordinate_active,joint_coordinate_domain]
      exact hSubset j hj
    have bBudget : bMem.queueMass+2*(middle.top+1)*V ≤ N := by
      change bMem.queueMass ≤ pm.queueMass+Q*D at bMass
      change bMem.queueMass+Q*V ≤ N
      omega
    have b140 := (eb.pointer_frame 140 (by decide)).trans h140
    have b141 := (eb.pointer_frame 141 (by decide)).trans h141
    have b142 := (eb.pointer_frame 142 (by decide)).trans h142
    obtain ⟨w,out,memory,er,hw,cMass,c143,cFrame,cW,cO,cH⟩ := ih (index+1) middle (payUnit b) bH bMem.payUnit nextBuffers
      (by omega) hDepth hMiddleStored hMiddleKeys hMiddleSubset b140 b141 b142 b143 bBudget
    have ex : MachineEval m g ω jointSolveIterationLoopCode st (1+u+1+w) out :=
      MachineEval.pointerNext hh (by rw [h142,h143]; omega) eb er
    have hBodyPaid : u+2 ≤ F*D := by
      have hu' : u+2 ≤ jointCoordinateBound ell logical.top rank (g.neighbors (e i)).length+7 := by
        dsimp only [jointCoordinateBound]
        omega
      exact hu'.trans (jointCoordinateBound_le ell logical.top rank (g.neighbors (e i)).length)
    rw [jointSolveIterationState,dif_pos hi]
    refine ⟨_,out,memory,ex,?_,?_,c143,nextFrame.trans cFrame,
      ex.unit_work jointSolveIterationLoopCode_wellFormed (by decide) hh,cO.trans bO,cH⟩
    · change w ≤ F*V+1 at hw
      rw [hVolume]
      change 1+u+1+w ≤ F*(D+V)+1
      rw [Nat.mul_add]
      omega
    · change memory.queueMass ≤ bMem.queueMass+Q*V at cMass
      change bMem.queueMass ≤ pm.queueMass+Q*D at bMass
      rw [hVolume]
      change memory.queueMass ≤ pm.queueMass+Q*(D+V)
      rw [Nat.mul_add]
      omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointSolveIterationExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 12000000 in
lemma joint_solve_iteration_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ)
    (e : Fin k → Fin n) (h : Fin n → ℝ) (enumBase answerBase : ℤ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (buffers : SolveIterationBuffers pm enumBase answerBase e h)
    (hDepth : logical.top ≤ ell) (hStored : ∀ j : Fin k, e j ∈ logical.stored) (hKeys : KeysInvariant g logical)
    (hSubset : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (h80 : st.scalar.core.ptrs 80=enumBase) (h79 : st.scalar.core.ptrs 79=answerBase) (h77 : st.scalar.core.ptrs 77=(k : ℤ))
    (hMass : pm.queueMass+2*(logical.top+1)*jointSolveIterationVolume g e 0 k ≤ N) (hCap : rank < length) (hPow : N < 2^rank) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (jointSolveIterationState g α e h 0 k logical) out,
      MachineEval m g ω jointSolveIterationCode st steps out ∧
      steps ≤ jointSolveIterationFactor ell logical.top rank*jointSolveIterationVolume g e 0 k+5 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*jointSolveIterationVolume g e 0 k ∧
      MemoryBufferFrame pm memory ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let a := linearRun m g ω jointSolveIterationInitInstructions st
  obtain ⟨ea,aW,aH⟩ := linear_execute m g ω jointSolveIterationInitInstructions
    (by simp [jointSolveIterationInitInstructions,unitInstruction,straightInstruction]) st hh
  have aI : a.scalar.integerMemory=st.scalar.integerMemory := by
    simp [a,linearRun,jointSolveIterationInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aR : a.scalar.core.mem=st.scalar.core.mem := by
    simp [a,linearRun,jointSolveIterationInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  have aO : a.output=st.output := by
    simp [a,linearRun,jointSolveIterationInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
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
  have aFrame : MemoryBufferFrame pm aMem := MemoryBufferFrame.frame pm aI aR aP aG aO
  have a140 : a.scalar.core.ptrs 140=enumBase := by
    simp [a,linearRun,jointSolveIterationInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,h80]
  have a141 : a.scalar.core.ptrs 141=answerBase := by
    simp [a,linearRun,jointSolveIterationInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,h79]
  have a142 : a.scalar.core.ptrs 142=(k : ℤ) := by
    simp [a,linearRun,jointSolveIterationInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,h77]
  have a143 : a.scalar.core.ptrs 143=0 := by
    simp [a,linearRun,jointSolveIterationInitInstructions,atomState,machineStep,pcSet,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh]
  obtain ⟨u,out,memory,eb,hu,bMass,b143,bFrame,bW,bO,bH⟩ := joint_solve_iteration_loop_exec m g ω s α ε ell length N rank e h enumBase answerBase hCap hPow k
    0 logical a aH aMem (buffers.frame aFrame) (by omega) hDepth hStored hKeys hSubset a140 a141 a142 a143 hMass
  have ex : MachineEval m g ω jointSolveIterationCode st (4+u) out := MachineEval.seq ea eb
  exact ⟨_,out,memory,ex,by omega,bMass,aFrame.trans bFrame,ex.unit_work jointSolveIterationCode_wellFormed (by decide) hh,bO.trans aO,bH⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.JointSolveCanonicalExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 12000000 in
lemma joint_solve_canonical_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ)
    (e : Fin k → Fin n) (h : Fin n → ℝ) (enumBase answerBase : ℤ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (buffers : SolveIterationBuffers pm enumBase answerBase e h)
    (hDepth : logical.top ≤ ell) (he : Function.Injective e)
    (hSupport : ∀ u ∉ Finset.univ.image e, h u=0)
    (hStored : ∀ j : Fin k, e j ∈ logical.stored) (hKeys : KeysInvariant g logical)
    (hCanonicalKeys : KeysInvariant g (refreshKeys g (jointUpdate g α logical h) (touchedBy g (Finset.univ.image e))))
    (hSubset : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (h80 : st.scalar.core.ptrs 80=enumBase) (h79 : st.scalar.core.ptrs 79=answerBase) (h77 : st.scalar.core.ptrs 77=(k : ℤ))
    (hMass : pm.queueMass+2*(logical.top+1)*(volumeNat g (Finset.univ.image e)+(Finset.univ.image e).card) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length
      (refreshKeys g (jointUpdate g α logical h) (touchedBy g (Finset.univ.image e))) out,
      MachineEval m g ω jointSolveIterationCode st steps out ∧
      steps ≤ jointSolveIterationFactor ell logical.top rank*(volumeNat g (Finset.univ.image e)+(Finset.univ.image e).card)+5 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*(volumeNat g (Finset.univ.image e)+(Finset.univ.image e).card) ∧
      MemoryBufferFrame pm memory ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  have hAgreement := joint_iteration_source_agreement g α logical e h he hSupport hKeys hCanonicalKeys
  have hVolume := joint_iteration_volume_domain g e he
  have hBudget : pm.queueMass+2*(logical.top+1)*jointSolveIterationVolume g e 0 k ≤ N := by rw [hVolume]; exact hMass
  have result := joint_solve_iteration_exec m g ω logical s α ε ell length N rank e h enumBase answerBase st hh pm buffers
    hDepth hStored hKeys hSubset h80 h79 h77 hBudget hCap hPow
  rw [hAgreement] at result
  simpa only [hVolume] using result

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CachedJointSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma solve_enumeration_capacity {n k : ℕ} (g : InputGraph n) (e : Fin k → Fin n) (he : Function.Injective e) :
    k+∑ i : Fin k, (g.neighbors (e i)).length=volumeNat g (Finset.univ.image e)+(Finset.univ.image e).card := by
  rw [←joint_iteration_volume_domain g e he,joint_iteration_volume_full,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
  omega

set_option maxHeartbeats 16000000 in
lemma cached_joint_solve_exec (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank offset : ℕ)
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
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch)
    (hKeys : KeysInvariant g logical)
    (hSubset : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (hMass : pm.queueMass+2*(logical.top+1)*(volumeNat g (Finset.univ.image e)+(Finset.univ.image e).card) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let size := volumeNat g (Finset.univ.image e)+(Finset.univ.image e).card
    let numericCost := (24*(16*(ell+3))+100)*size+28
    let updateCost := jointSolveIterationFactor ell logical.top rank*size+5
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length
      (refreshKeys g (jointUpdate g α logical (solveOn g α (Finset.univ.image e) b)) (touchedBy g (Finset.univ.image e))) out,
      MachineEval m g ω cachedJointSolveCode st steps out ∧
      steps ≤ numericCost+updateCost+1 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*size ∧
      out.work ≤ st.work+(numericCost+updateCost : ℕ)+solveCharge m k (principalEntries g α e).length ∧
      out.output=st.output ∧ out.scalar.halted=false ∧
      (out.scalar.core.ptrs 53=epoch+1 ∧ ∀ v : Fin n,
        out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch+1) := by
  dsimp only
  obtain ⟨a,pre,preMemory,ep,ha,buffers,hMassPre,hLayout,h80,h53,hWorkPre,hOutputPre,hHaltPre,hMarks⟩ :=
    cached_principal_solve_memory_exec m g ω logical s α ε ell length offset base enumBase epoch hEnumBase
      e he hk hd hα b st hh pm hDepth hmem hEnum hEnumBelow hForeign hb hkp hf hE hOff hbRecords hbound
  have hSize := solve_enumeration_capacity g e he
  have hSupport : ∀ u ∉ Finset.univ.image e, solveOn g α (Finset.univ.image e) b u=0 := by
    intro u hu
    simp only [solveOn,dif_neg hu]
  have hCanonicalKeys := joint_refresh_keys g α logical (Finset.univ.image e)
    (solveOn g α (Finset.univ.image e) b) hSupport hKeys
  have hBudget : preMemory.queueMass+2*(logical.top+1)*(volumeNat g (Finset.univ.image e)+(Finset.univ.image e).card) ≤ N := by
    rw [hMassPre]
    exact hMass
  obtain ⟨c,out,memory,ec,hc,hMassOut,hBufferFrame,hWorkOut,hOutputOut,hHaltOut⟩ :=
    joint_solve_canonical_exec m g ω logical s α ε ell length N rank e (solveOn g α (Finset.univ.image e) b)
      enumBase _ pre hHaltPre preMemory buffers hDepth he hSupport hmem hKeys hCanonicalKeys hSubset
      h80 hLayout.answer hLayout.dimensionPointer hBudget hCap hPow
  rw [hSize] at ha hWorkPre
  refine ⟨a+c,out,memory,MachineEval.seq ep ec,by omega,?_,?_,hOutputOut.trans hOutputPre,hHaltOut,
    ⟨(ec.pointer_frame 53 (by decide)).trans h53,fun v => (hBufferFrame.indexFrame v).le.trans (hMarks v)⟩⟩
  · rw [hMassPre] at hMassOut
    exact hMassOut
  · rw [hWorkOut]
    have hNat : (c : ℝ≥0∞) ≤ (jointSolveIterationFactor ell logical.top rank*
        (volumeNat g (Finset.univ.image e)+(Finset.univ.image e).card)+5 : ℕ) := by exact_mod_cast hc
    calc
      pre.work+c ≤ (st.work+((24*(16*(ell+3))+100)*(volumeNat g (Finset.univ.image e)+(Finset.univ.image e).card)+28 : ℕ)+
          solveCharge m k (principalEntries g α e).length)+
          (jointSolveIterationFactor ell logical.top rank*(volumeNat g (Finset.univ.image e)+(Finset.univ.image e).card)+5 : ℕ) := add_le_add hWorkPre hNat
      _ = _ := by push_cast; ac_rfl

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution : ∀ (m : SolveModel) {n k : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank offset : ℕ)
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
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch)
    (hKeys : KeysInvariant g logical)
    (hSubset : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (hMass : pm.queueMass+2*(logical.top+1)*(volumeNat g (Finset.univ.image e)+(Finset.univ.image e).card) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank),
let size := volumeNat g (Finset.univ.image e)+(Finset.univ.image e).card
    let numericCost := (24*(16*(ell+3))+100)*size+28
    let updateCost := jointSolveIterationFactor ell logical.top rank*size+5
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length
      (refreshKeys g (jointUpdate g α logical (solveOn g α (Finset.univ.image e) b)) (touchedBy g (Finset.univ.image e))) out,
      MachineEval m g ω cachedJointSolveCode st steps out ∧
      steps ≤ numericCost+updateCost+1 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*size ∧
      out.work ≤ st.work+(numericCost+updateCost : ℕ)+solveCharge m k (principalEntries g α e).length ∧
      out.output=st.output ∧ out.scalar.halted=false ∧
      (out.scalar.core.ptrs 53=epoch+1 ∧ ∀ v : Fin n,
        out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch+1) := by
  exact @NearlyOptimalPPR.Computation.cached_joint_solve_exec
