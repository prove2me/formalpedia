-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.exterior_activation_raw_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:46:19.85839+00:00
-- url     : https://prove2.me/submissions/37426a73-ca30-4d9c-800a-047d18ed3731

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
import Theorems.Thm_NearlyOptimalPPR_Computation_exterior_activation_apply_exec
import Theorems.Thm_NearlyOptimalPPR_Computation_exterior_numeric_prefix_exec
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


@[simp] lemma pcSet_payUnit_zero (st : MachineState) : pcSet (payUnit st) 0=payUnit st := rfl

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

-- Proof module: Solutions.IntegerScaleCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma integerScaleCode_wellFormed : integerScaleCode.wellFormed := by
  simp [integerScaleCode,integerScaleLoopCode,integerScaleBodyCode,integerScaleBodyRoutine,
    PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,sequenceCode,coreCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

lemma unitInstruction_work (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (i : Instruction) (hi : unitInstruction i) (st : MachineState) (hh : st.scalar.halted=false) :
    (atomState m g ω i st).work=st.work+1 := by
  cases i <;> simp_all [unitInstruction,atomState,machineStep,pcSet,hh]

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

-- Proof module: Solutions.CodePredicateDecidable

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

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
lemma levelHeaderIntegerStoreCode_wellFormed (slot : ℕ) : (levelHeaderIntegerStoreCode slot).wellFormed := by
  refine ⟨levelHeaderAddressCode_wellFormed slot,?_⟩
  simp [MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma levelHeaderRealLoadCode_wellFormed (slot : ℕ) : (levelHeaderRealLoadCode slot).wellFormed := by
  refine ⟨levelHeaderAddressCode_wellFormed slot,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma levelHeaderRealStoreCode_wellFormed (slot : ℕ) : (levelHeaderRealStoreCode slot).wellFormed := by
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

-- Proof module: Solutions.LevelHeaderIntegerFrom

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderIntegerFromCode_wellFormed (slot source : ℕ) : (levelHeaderIntegerFromCode slot source).wellFormed := by
  refine ⟨?_,levelHeaderIntegerStoreCode_wellFormed slot⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexAddressExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexAddressCode_wellFormed : vertexAddressCode.wellFormed := by
  refine ⟨integerScaleCode_wellFormed,?_⟩
  simp [vertexAddressTailCode,sequenceCode,coreCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexFieldWrite

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexFieldWriteCode_wellFormed (field source : ℕ) : (vertexFieldWriteCode field source).wellFormed := by
  simp [vertexFieldWriteCode,fieldWritePrepRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    vertexIntegerStoreCode,MachineCode.wellFormed,vertexAddressCode_wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AdjacencyMetadata

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma adjacencyMetadataCode_wellFormed : adjacencyMetadataCode.wellFormed := by
  refine ⟨vertexFieldWriteCode_wellFormed 0 60,vertexFieldWriteCode_wellFormed 1 61,?_,vertexFieldWriteCode_wellFormed 2 51⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AdjacencyFetchCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma adjacencyFetchBodyCode_wellFormed : adjacencyFetchBodyCode.wellFormed := by
  simp [adjacencyFetchBodyCode,sequenceCode,coreCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.QueuedFlagRead

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma queuedFlagReadCode_wellFormed : queuedFlagReadCode.wellFormed := by
  simp [queuedFlagReadCode,vertexIntegerLoadCode,vertexAddressCode_wellFormed,
    coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

lemma cache_write_cells_below_positive (width vertex : ℕ) (free z : ℤ) (degree : ℕ)
    (hz : 0 ≤ z) (hBelow : z < free) : z ∉ cacheWriteCells width vertex free degree := by
  intro h
  rcases Finset.mem_union.mp h with hArray|hMeta
  · obtain ⟨i,hi,he⟩ := (mem_arrayCells free z degree).mp hArray
    have hi0 := Int.natCast_nonneg i
    omega
  · have hNe (k : ℕ) : z ≠ vertexRecordAddress width vertex k := by
      have := vertexRecordAddress_negative width vertex k
      omega
    simpa only [Finset.mem_insert,Finset.mem_singleton,hNe 0,hNe 1,hNe 2,or_self] using hMeta

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PayloadFoldProperties

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma level_payload_frame {Payload Value : Type} (update : ℕ → Payload → Payload) (limit : ℕ)
    (eval : Payload → Value) (hStep : ∀ i < limit, ∀ payload, eval (update i payload)=eval payload) (count : ℕ) :
    ∀ (start : ℕ) (payload : Payload), start+count ≤ limit →
      eval (levelPayloadFold update start count payload)=eval payload := by
  induction count with
  | zero => intros; rfl
  | succ count ih =>
    intro start payload hRange
    rw [levelPayloadFold,ih (start+1) (update start payload) (by omega),hStep start (by omega)]

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

end MemoryBufferFrame
end
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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderArithmetic

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderIncrementCode_wellFormed (slot : ℕ) : (levelHeaderIncrementCode slot).wellFormed := by
  refine ⟨levelHeaderIntegerLoadCode_wellFormed slot,?_,levelHeaderIntegerStoreCode_wellFormed slot⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameListMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma level_header_below_end (level slot : ℕ) (hs : slot < 32) :
    levelHeaderAddress level slot < 128+32*((level+1 : ℕ) : ℤ) := by
  unfold levelHeaderAddress
  push_cast
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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredNeighborMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma stored_neighbor_fold_integer_positive {n : ℕ} (g : InputGraph n) (source : Fin n)
    (logical : RecursiveState n) (ell : ℕ) (delta : ℝ) (payload : (ℤ → ℤ) × (ℤ → ℝ)) (z : ℤ) (hz : 0 ≤ z) :
    (levelPayloadFold (storedNeighborMemoryUpdate g source logical ell delta) 0
      (g.neighbors source).length payload).1 z=payload.1 z := by
  apply level_payload_frame (storedNeighborMemoryUpdate g source logical ell delta) (limit:=(g.neighbors source).length) (eval:=fun p => p.1 z)
  · intro i hi p
    have hn : z ≠ vertexRecordAddress (16*(ell+3)) (storedNeighborVertex g source i).val 0 := by
      have := vertexRecordAddress_negative (16*(ell+3)) (storedNeighborVertex g source i).val 0
      omega
    exact Function.update_of_ne hn _ _
  · omega

lemma stored_neighbor_fold_integer_field {n : ℕ} (g : InputGraph n) (source u : Fin n)
    (logical : RecursiveState n) (ell : ℕ) (delta : ℝ) (payload : (ℤ → ℤ) × (ℤ → ℝ))
    (field : ℕ) (hf : field < 16*(ell+3)) (h0 : field ≠ 0) :
    (levelPayloadFold (storedNeighborMemoryUpdate g source logical ell delta) 0
      (g.neighbors source).length payload).1 (vertexRecordAddress (16*(ell+3)) u.val field)=
        payload.1 (vertexRecordAddress (16*(ell+3)) u.val field) := by
  apply level_payload_frame (storedNeighborMemoryUpdate g source logical ell delta) (limit:=(g.neighbors source).length)
    (eval:=fun p => p.1 (vertexRecordAddress (16*(ell+3)) u.val field))
  · intro i hi p
    exact vertex_integer_update_other_field p.1 (16*(ell+3)) (storedNeighborVertex g source i).val u.val 0 field _
      (by omega) hf h0
  · omega

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
lemma exteriorActivationPrepareCode_wellFormed : exteriorActivationPrepareCode.wellFormed := by
  refine ⟨?_,levelContextCode_wellFormed⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma exteriorActivationApplyCode_wellFormed : exteriorActivationApplyCode.wellFormed := by
  refine ⟨activationBoundaryCode_wellFormed,exteriorActivationPrepareCode_wellFormed,
    frameListInsertCode_wellFormed 1 3 2 2,activationScalarsCode_wellFormed,activationChildAdmitCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma exteriorActivationCode_wellFormed : exteriorActivationCode.wellFormed :=
  ⟨trivial,exteriorActivationApplyCode_wellFormed⟩
lemma exteriorNumericPrefixCode_wellFormed : exteriorNumericPrefixCode.wellFormed :=
  ⟨exteriorScalarCode_wellFormed,cacheRowCode_wellFormed,exteriorPotentialAddCode_wellFormed,
    exteriorSelfBudgetLoopCode_wellFormed,storedNeighborLoopCode_wellFormed⟩
lemma exteriorNumericRawCode_wellFormed : exteriorNumericRawCode.wellFormed :=
  ⟨exteriorNumericPrefixCode_wellFormed,exteriorActivationCode_wellFormed⟩
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorNumericMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma exterior_numeric_payload_integer_field {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (t : ℕ) (v u : Fin n) (δ : ℝ) (I : ℤ → ℤ) (R : ℤ → ℝ) (field : ℕ)
    (hf : field < 16*(ell+3)) (hn : field ≠ 0) :
    (exteriorNumericPayload g logical ell α t v δ I R).1 (vertexRecordAddress (16*(ell+3)) u.val field)=
      I (vertexRecordAddress (16*(ell+3)) u.val field) := by
  unfold exteriorNumericPayload
  exact stored_neighbor_fold_integer_field g v u logical ell _ _ field hf hn

lemma exterior_numeric_payload_integer_positive {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (t : ℕ) (v : Fin n) (δ : ℝ) (I : ℤ → ℤ) (R : ℤ → ℝ) (z : ℤ) (hz : 0 ≤ z) :
    (exteriorNumericPayload g logical ell α t v δ I R).1 z=I z := by
  unfold exteriorNumericPayload
  exact stored_neighbor_fold_integer_positive g v logical ell _ _ z hz

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorNumericFrames

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma exterior_numeric_old_heap {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (t : ℕ) (v : Fin n) (δ : ℝ) (J I : ℤ → ℤ) (R : ℤ → ℝ) (free z : ℤ)
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val free (g.neighbors v).length → J z=I z)
    (hz : 0 ≤ z) (hBelow : z < free) :
    (exteriorNumericPayload g logical ell α t v δ J R).1 z=I z := by
  rw [exterior_numeric_payload_integer_positive g logical ell α t v δ J R z hz]
  exact hJ z (cache_write_cells_below_positive (16*(ell+3)) v.val free z _ hz hBelow)

lemma exterior_numeric_integer_field_frame {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (t : ℕ) (v u : Fin n) (δ : ℝ) (J I : ℤ → ℤ) (R : ℤ → ℝ) (free : ℤ)
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val free (g.neighbors v).length → J z=I z)
    (hFree : 0 ≤ free) (field : ℕ) (hLo : 3 ≤ field) (hHi : field < 16*(ell+3)) :
    (exteriorNumericPayload g logical ell α t v δ J R).1 (vertexRecordAddress (16*(ell+3)) u.val field)=
      I (vertexRecordAddress (16*(ell+3)) u.val field) := by
  rw [exterior_numeric_payload_integer_field g logical ell α t v u δ J R field hHi (by omega)]
  exact hJ _ (cache_write_cells_negative_field (16*(ell+3)) v.val u.val field free _ hFree (by omega) hHi hLo)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorActivationRawExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 15000000 in
lemma exterior_activation_raw_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length t boundary : ℕ) (v : Fin n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (ht : t ≤ logical.top) (hvDomain : v ∈ parentDomain logical t)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hSelected : st.scalar.core.ptrs 112=(t : ℤ)) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hBoundary : logical.boundaryEdges=(boundary : ℤ))
    (hAdmit : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8) :
    let width := 16*(ell+3)
    let δ := compilerExteriorDelta g α logical t v
    let free := if v ∈ logical.stored then st.scalar.core.ptrs 20 else st.scalar.core.ptrs 20+((g.neighbors v).length : ℤ)
    ∃ steps out, ∃ J : ℤ → ℤ,
      MachineEval m g ω exteriorNumericRawCode st steps out ∧
      steps ≤ 84*width+442+(logical.top+1)*(4*width+60)+
        (g.neighbors v).length*((logical.top+1)*(8*width+39)+8*width+50) ∧
      GraphCache g J width (insert v logical.stored) free ∧
      (∀ z, z ∉ cacheWriteCells width v.val (st.scalar.core.ptrs 20) (g.neighbors v).length → J z=st.scalar.integerMemory z) ∧
      J (vertexRecordAddress width v.val 1)=(if v ∈ logical.stored then st.scalar.integerMemory (vertexRecordAddress width v.val 1) else st.scalar.core.ptrs 20) ∧
      out.scalar.integerMemory=exteriorActivationIntegerMemory g v (logical.frames 0).active boundary t logical.top width free
        (exteriorNumericPayload g logical ell α t v δ J st.scalar.core.mem).1 ∧
      out.scalar.core.mem=exteriorActivationRealMemory (exteriorNumericPayload g logical ell α t v δ J st.scalar.core.mem).2
        v.val t logical.top width ((logical.frames t).q*LocalPush.deg g.graph v/2) (logical.frames t).openBudget ∧
      VertexListRep out.scalar.integerMemory (out.scalar.integerMemory (levelHeaderAddress t 1))
        (v::(pm.frames t ht).activeVertices) (nodeCells free ∪ (pm.frames t ht).activeFoot) ∧
      (∀ z ∈ nodeCells free ∪ (pm.frames t ht).activeFoot, z < free+3) ∧
      out.scalar.core.ptrs 20=free+3 ∧ out.scalar.core.ptrs 100=(logical.top : ℤ) ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧ out.scalar.core.ptrs 116=(v.val : ℤ) ∧
      out.scalar.core.ptrs 120=((g.neighbors v).length : ℤ) ∧
      out.scalar.queries=st.scalar.queries+1+(if v ∈ logical.stored then 0 else (g.neighbors v).length+1)+(g.neighbors v).length ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  intro width δ free
  obtain ⟨u,a,J,ea,hu,jCache,jFrame,aPayload,aCache,aFree,a40,a100,a120,a121,a108,a112,a116,a114,
    aR40,aR41,aR42,aR43,aR46,aQ,aW,aO,aH,jBase⟩ :=
    exterior_numeric_prefix_exec m g ω logical s α ε ell length t v st hh pm hDepth ht hvDomain hSubset hSelected hv
  have aI : a.scalar.integerMemory=(exteriorNumericPayload g logical ell α t v δ J st.scalar.core.mem).1 := congrArg Prod.fst aPayload
  have aR : a.scalar.core.mem=(exteriorNumericPayload g logical ell α t v δ J st.scalar.core.mem).2 := congrArg Prod.snd aPayload
  have hFree : st.scalar.core.ptrs 20 ≤ free := by dsimp [free]; split_ifs <;> omega
  have hOldFree : 0 ≤ st.scalar.core.ptrs 20 := by have := pm.allocator; omega
  have hHeap (z : ℤ) (hz : 0 ≤ z) (hBelow : z < st.scalar.core.ptrs 20) : a.scalar.integerMemory z=st.scalar.integerMemory z := by
    rw [aI]
    exact exterior_numeric_old_heap g logical ell α t v δ J st.scalar.integerMemory st.scalar.core.mem _ z jFrame hz hBelow
  have hHeader (slot : ℕ) (hs : slot < 32) : a.scalar.integerMemory (levelHeaderAddress t slot)=st.scalar.integerMemory (levelHeaderAddress t slot) := by
    apply hHeap
    · have := levelHeaderAddress_positive t slot; omega
    · have := level_header_below_end t slot hs
      have := pm.allocator
      omega
  have hList : VertexListRep a.scalar.integerMemory (a.scalar.integerMemory (levelHeaderAddress t 1))
      (pm.frames t ht).activeVertices (pm.frames t ht).activeFoot := by
    rw [hHeader 1 (by decide)]
    apply (pm.frames t ht).activeRep.frame
    intro z hz
    exact hHeap z (by have := (pm.frames t ht).activeAbove z hz; omega) ((pm.frames t ht).activeBelow z hz)
  have hRoot : t=0 → ∀ w : Fin n, a.scalar.integerMemory (vertexRecordAddress width w.val 18)=
      if w ∈ (logical.frames 0).active then 1 else 0 := by
    intro ht0 w
    rw [aI,exterior_numeric_integer_field_frame g logical ell α t v w δ J st.scalar.integerMemory st.scalar.core.mem _ jFrame hOldFree 18 (by decide) (by omega)]
    exact (pm.frames 0 (by omega)).activeFlags w (by simp [parentDomain])
  obtain ⟨k,c,ec,hk,c100,c20,c0,cI,cR,cRep,cBelow,cQ,cW,cO,cH,c40⟩ := exterior_activation_apply_exec m g ω (payUnit a) aH
    v (logical.frames 0).active boundary t logical.top width free (J (vertexRecordAddress width v.val 1)) (logical.frames t).openBudget
    (pm.frames t ht).activeVertices (pm.frames t ht).activeFoot (by omega)
    ((ea.pointer_frame 0 (by decide)).trans pm.zero) ((ea.pointer_frame 50 (by decide)).trans pm.width)
    a108 a112 a116 a40 a120 a121 aFree ((ea.real_register_frame 31 (by decide)).trans pm.one)
    (by have := pm.allocator; omega) (hHeap 7 (by decide) (by have := pm.allocator; omega) |>.trans (pm.boundary.trans hBoundary))
    ((hHeader 9 (by decide)).trans (pm.frames t ht).openBudget) hList
    (fun z hz => ((pm.frames t ht).activeBelow z hz).trans_le hFree)
    (fun z hz => by have := (pm.frames t ht).activeAbove z hz; omega)
    (by intro i hi; rw [←a121]; rw [show a.scalar.core.ptrs 121=a.scalar.integerMemory (vertexRecordAddress width v.val 1) by
      rw [a121,aI,exterior_numeric_payload_integer_field g logical ell α t v v δ J _ 1 (by omega) (by decide)]]
        ; exact aCache.adjacency v (Finset.mem_insert_self _ _) i hi hi)
    hRoot
  let out := payUnit c
  have eAct : MachineEval m g ω exteriorActivationCode a (1+k+1) out := by
    apply MachineEval.pointerGt aH
    · rw [a114]
      have hYes : relative logical t v+min ((logical.frames t).residual v/(5*LocalPush.deg g.graph v))
        (3*(logical.frames t).q/8-relative logical t v)=3*(logical.frames t).q/8 := hAdmit
      rw [if_pos hYes,(ea.pointer_frame 0 (by decide)).trans pm.zero]
      norm_num
    · exact ec
  have ex : MachineEval m g ω exteriorNumericRawCode st (u+(1+k+1)) out := MachineEval.seq ea eAct
  refine ⟨_,out,J,ex,?_,jCache,jFrame,jBase,?_,?_,cRep,cBelow,c20,c100,c0,?_,?_,?_,?_,
    ex.unit_work exteriorNumericRawCode_wellFormed (by decide) hh,cO.trans aO,cH⟩
  · change u ≤ 36*width+161+(logical.top+1)*(4*width+60)+(g.neighbors v).length*((logical.top+1)*(8*width+39)+4*width+31) at hu
    have hRing : (g.neighbors v).length*((logical.top+1)*(8*width+39)+8*width+50)=
      (g.neighbors v).length*((logical.top+1)*(8*width+39)+4*width+31)+(g.neighbors v).length*(4*width+19) := by ring
    rw [hRing]
    omega
  · change c.scalar.integerMemory=_
    rw [cI]
    change exteriorActivationIntegerMemory g v (logical.frames 0).active boundary t logical.top width free a.scalar.integerMemory=_
    rw [aI]
  · change c.scalar.core.mem=_
    rw [cR]
    change exteriorActivationRealMemory a.scalar.core.mem v.val t logical.top width (a.scalar.core.regs 43) (logical.frames t).openBudget=_
    rw [aR,aR43]
  · exact c40
  · exact (ec.pointer_frame 116 (by decide)).trans a116
  · exact (ec.pointer_frame 120 (by decide)).trans a120
  · change c.scalar.queries=_
    rw [cQ]
    change a.scalar.queries=_
    exact aQ

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution : ∀ (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length t boundary : ℕ) (v : Fin n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (ht : t ≤ logical.top) (hvDomain : v ∈ parentDomain logical t)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hSelected : st.scalar.core.ptrs 112=(t : ℤ)) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hBoundary : logical.boundaryEdges=(boundary : ℤ))
    (hAdmit : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8),
let width := 16*(ell+3)
    let δ := compilerExteriorDelta g α logical t v
    let free := if v ∈ logical.stored then st.scalar.core.ptrs 20 else st.scalar.core.ptrs 20+((g.neighbors v).length : ℤ)
    ∃ steps out, ∃ J : ℤ → ℤ,
      MachineEval m g ω exteriorNumericRawCode st steps out ∧
      steps ≤ 84*width+442+(logical.top+1)*(4*width+60)+
        (g.neighbors v).length*((logical.top+1)*(8*width+39)+8*width+50) ∧
      GraphCache g J width (insert v logical.stored) free ∧
      (∀ z, z ∉ cacheWriteCells width v.val (st.scalar.core.ptrs 20) (g.neighbors v).length → J z=st.scalar.integerMemory z) ∧
      J (vertexRecordAddress width v.val 1)=(if v ∈ logical.stored then st.scalar.integerMemory (vertexRecordAddress width v.val 1) else st.scalar.core.ptrs 20) ∧
      out.scalar.integerMemory=exteriorActivationIntegerMemory g v (logical.frames 0).active boundary t logical.top width free
        (exteriorNumericPayload g logical ell α t v δ J st.scalar.core.mem).1 ∧
      out.scalar.core.mem=exteriorActivationRealMemory (exteriorNumericPayload g logical ell α t v δ J st.scalar.core.mem).2
        v.val t logical.top width ((logical.frames t).q*LocalPush.deg g.graph v/2) (logical.frames t).openBudget ∧
      VertexListRep out.scalar.integerMemory (out.scalar.integerMemory (levelHeaderAddress t 1))
        (v::(pm.frames t ht).activeVertices) (nodeCells free ∪ (pm.frames t ht).activeFoot) ∧
      (∀ z ∈ nodeCells free ∪ (pm.frames t ht).activeFoot, z < free+3) ∧
      out.scalar.core.ptrs 20=free+3 ∧ out.scalar.core.ptrs 100=(logical.top : ℤ) ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧ out.scalar.core.ptrs 116=(v.val : ℤ) ∧
      out.scalar.core.ptrs 120=((g.neighbors v).length : ℤ) ∧
      out.scalar.queries=st.scalar.queries+1+(if v ∈ logical.stored then 0 else (g.neighbors v).length+1)+(g.neighbors v).length ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by
  exact @NearlyOptimalPPR.Computation.exterior_activation_raw_exec
