-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.finish_episode_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:29:35.167079+00:00
-- url     : https://prove2.me/submissions/fe4d19da-addb-458c-a1b8-1efc6fb137ab

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


def pointerWrite (st : MachineState) (r : ℕ) (x : ℤ) : MachineState :=
  {st with scalar := {st.scalar with core := {st.scalar.core with ptrs := Function.update st.scalar.core.ptrs r x}}}

@[simp] lemma pcSet_payUnit_zero (st : MachineState) : pcSet (payUnit st) 0=payUnit st := rfl

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

-- Proof module: Solutions.LevelHeaderTo

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderIntegerToCode_wellFormed (slot target : ℕ) : (levelHeaderIntegerToCode slot target).wellFormed := by
  refine ⟨levelHeaderIntegerLoadCode_wellFormed slot,?_⟩
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

-- Proof module: Solutions.FinishEpisodeSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma finish_episode_active {n : ℕ} (logical : RecursiveState n) (j : ℕ) :
    ((finishEpisode logical).frames j).active=(logical.frames j).active := by
  classical
  by_cases hj : j=logical.top <;> simp [finishEpisode,changeFrame,hj]

lemma finish_episode_domain {n : ℕ} (logical : RecursiveState n) (j : ℕ) :
    parentDomain (finishEpisode logical) j=parentDomain logical j := by
  unfold parentDomain
  split_ifs
  · rfl
  · exact finish_episode_active logical (j-1)

lemma finish_episode_selected {n : ℕ} (logical : RecursiveState n) :
    (finishEpisode logical).frames logical.top=
      {logical.frames logical.top with openBudget := false,cache := ∅} := by
  simp only [finishEpisode,changeFrame,Function.update_self]

lemma finish_episode_other {n : ℕ} (logical : RecursiveState n) (j : ℕ) (hj : j ≠ logical.top) :
    (finishEpisode logical).frames j=logical.frames j := by
  simp only [finishEpisode,changeFrame,Function.update_of_ne hj]

lemma finish_episode_exterior {n : ℕ} (logical : RecursiveState n) (j : ℕ) :
    ((finishEpisode logical).frames j).exterior=(logical.frames j).exterior := by
  by_cases hj : j=logical.top
  · subst j; rw [finish_episode_selected]
  · rw [finish_episode_other logical j hj]

lemma finish_episode_high {n : ℕ} (logical : RecursiveState n) (j : ℕ) :
    ((finishEpisode logical).frames j).high=(logical.frames j).high := by
  by_cases hj : j=logical.top
  · subst j; rw [finish_episode_selected]
  · rw [finish_episode_other logical j hj]

lemma finish_episode_theta {n : ℕ} (logical : RecursiveState n) (j : ℕ) :
    ((finishEpisode logical).frames j).theta=(logical.frames j).theta := by
  by_cases hj : j=logical.top
  · subst j; rw [finish_episode_selected]
  · rw [finish_episode_other logical j hj]

lemma canonical_high_filter {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (hKeys : KeysInvariant g logical) (j : ℕ) (hj : j ≤ logical.top) :
    (logical.frames j).active.filter
      (fun v => 3*(logical.frames j).theta*LocalPush.deg g.graph v ≤ (logical.frames j).residual v)=
      (logical.frames j).high := by
  classical
  ext v
  simpa only [Finset.mem_filter,highKey] using ((hKeys j hj).2 v).symm

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

lemma finish_mass {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} {visited : Finset (Fin n)}
    {pm : MachinePendingKeys g s α ε ell length logical st} (inv : PendingVisitedKeys pm visited)
    (hAll : visited=Finset.univ) : (inv.finish hAll).queueMass=pm.queueMass := rfl

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

-- Proof module: Solutions.FrameCacheListClearPrelude

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameCacheListClearPreludeCode_wellFormed : frameCacheListClearPreludeCode.wellFormed := by
  refine ⟨levelHeaderIntegerToCode_wellFormed 4 94,?_⟩
  simp [frameCacheListClearPointerRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

set_option maxHeartbeats 4000000 in
lemma frame_cache_list_clear_prelude_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (level width : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (h100 : st.scalar.core.ptrs 100=(level : ℤ)) (h50 : st.scalar.core.ptrs 50=(width : ℤ)) :
    ∃ out, MachineEval m g ω frameCacheListClearPreludeCode st 19 out ∧
      out.scalar.core.ptrs 94=st.scalar.integerMemory (levelHeaderAddress level 4) ∧
      out.scalar.core.ptrs 182=((16*(level+1)+4 : ℕ) : ℤ) ∧ out.scalar.core.ptrs 41=(width : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+19 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a94,aI,aR,aW,aO,aH⟩ := level_header_integer_to_exec m g ω st hh level 4 94 h100
  have a100 := (ea.pointer_frame 100 (by decide)).trans h100
  have a50 := (ea.pointer_frame 50 (by decide)).trans h50
  obtain ⟨out,eb,hP,hI,hR,hW,hO,hH⟩ := frameCacheListClearPointerRoutine.execute m g ω a aH
  have eb9 : MachineEval m g ω frameCacheListClearPointerRoutine.code a 9 out := eb
  have ex : MachineEval m g ω frameCacheListClearPreludeCode st 19 out := MachineEval.seq ea eb9
  refine ⟨out,ex,?_,?_,?_,hI.trans aI,hR.trans aR,?_,hO.trans aO,hH⟩
  · exact (eb.pointer_frame 94 (by decide)).trans a94
  · rw [hP]
    simp [frameCacheListClearPointerRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,a100]
    ring
  · rw [hP]
    simp [frameCacheListClearPointerRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,a50]
  · rw [hW,aW]
    change st.work+10+9= _
    norm_num; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameCacheListClearExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameCacheListClearCode_wellFormed : frameCacheListClearCode.wellFormed :=
  ⟨frameCacheListClearPreludeCode_wellFormed,clearVertexFieldBodyCode_wellFormed⟩

set_option maxHeartbeats 7000000 in
lemma frame_cache_list_clear_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell) :
    let vertices := (pm.frames logical.top le_rfl).cacheVertices
    ∃ out, MachineEval m g ω frameCacheListClearCode st
      ((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+20) out ∧
      out.scalar.integerMemory=clearVertexFieldRecords (16*(ell+3)) (16*(logical.top+1)+4) vertices st.scalar.integerMemory ∧
      (∀ v ∈ parentDomain logical logical.top, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+20 : ℕ) ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  dsimp only
  let f := pm.frames logical.top le_rfl
  obtain ⟨pre,ep,h94,h182,h41,hI,hR,hW,hO,hH⟩ := frame_cache_list_clear_prelude_exec m g ω logical.top (16*(ell+3)) st hh pm.top pm.width
  have h0 := (ep.pointer_frame 0 (by decide)).trans pm.zero
  have hList : VertexListRep pre.scalar.integerMemory (st.scalar.integerMemory (levelHeaderAddress logical.top 4)) f.cacheVertices f.cacheFoot := by
    rw [hI]
    exact f.cacheRep
  obtain ⟨out,el,hoI,hoR,hoQ,hoW,hoO,hoH⟩ := clear_vertex_field_loop_exec m g ω (16*(ell+3)) (16*(logical.top+1)+4)
    f.cacheVertices (st.scalar.integerMemory (levelHeaderAddress logical.top 4)) f.cacheFoot pre hH h0 h41 h182 h94 hList
  have hLength : f.cacheVertices.length=(logical.frames logical.top).cache.card := by
    rw [←f.cacheSet,List.toFinset_card_of_nodup f.cacheNodup]
  have ex : MachineEval m g ω frameCacheListClearCode st
      ((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+20) out := by
    have ee := MachineEval.seq ep el
    rw [hLength] at ee
    convert ee using 1 <;> (first | rfl | omega)
  have hFinalI : out.scalar.integerMemory=clearVertexFieldRecords (16*(ell+3)) (16*(logical.top+1)+4) f.cacheVertices st.scalar.integerMemory := by rw [hoI,hI]
  refine ⟨out,ex,hFinalI,?_,hoR.trans hR,?_,hoQ.trans (ep.query_frame (by decide)),hoO.trans hO,hoH⟩
  · intro v hv
    rw [hFinalI,clear_vertex_field_records_samefield _ _ _ _ (by omega)]
    by_cases hc : v ∈ (logical.frames logical.top).cache
    · have hm : v ∈ f.cacheVertices := by apply List.mem_toFinset.mp; rw [f.cacheSet]; exact hc
      rw [if_pos hm]
    · have hm : v ∉ f.cacheVertices := by intro hm; apply hc; rw [←f.cacheSet]; exact List.mem_toFinset.mpr hm
      rw [if_neg hm,f.cacheFlags v hv,if_neg hc]
  · rw [hoW,hW,hLength]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FinishEpisodeRawExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def finishEpisodeIntegerMemory {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell : ℕ) : ℤ → ℤ :=
  levelHeaderIntegerSetsMemory
    (clearVertexFieldSetRecords (16*(ell+3)) (16*(logical.top+1)+4)
      (logical.frames logical.top).cache I) logical.top finishEpisodeAssignments
lemma finishEpisodeCode_wellFormed : finishEpisodeCode.wellFormed :=
  ⟨frameCacheListClearCode_wellFormed,levelHeaderIntegerSetsCode_wellFormed _⟩

set_option maxHeartbeats 10000000 in
lemma finish_episode_raw_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell) :
    ∃ out, MachineEval m g ω finishEpisodeCode st
      ((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+60) out ∧
      out.scalar.integerMemory=finishEpisodeIntegerMemory st.scalar.integerMemory logical ell ∧
      (∀ v ∈ parentDomain logical logical.top,
        out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0) ∧
      out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+60 : ℕ) ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,aI,aCache,aR,aW,aQ,aO,aH⟩ :=
    frame_cache_list_clear_exec m g ω logical s α ε ell length st hh pm hDepth
  have a100 := (ea.pointer_frame 100 (by decide)).trans pm.top
  obtain ⟨out,eb,bI,bR,bQ,bW,bO,bH⟩ :=
    level_header_integer_sets_exec m g ω finishEpisodeAssignments a aH logical.top a100
  have ex : MachineEval m g ω finishEpisodeCode st
      ((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+60) out := by
    have eb40 : MachineEval m g ω (levelHeaderIntegerSetsCode finishEpisodeAssignments) a 40 out := eb
    convert MachineEval.seq ea eb40 using 1 <;> (first | rfl | omega)
  refine ⟨out,ex,?_,?_,bR.trans aR,
    ex.unit_work finishEpisodeCode_wellFormed (by decide) hh,bQ.trans aQ,bO.trans aO,bH⟩
  · rw [bI,aI,clear_vertex_field_list_set,(pm.frames logical.top le_rfl).cacheSet]
    rfl
  · intro v hv
    rw [bI]
    have hz := vertexRecordAddress_negative (16*(ell+3)) v.val (16*(logical.top+1)+4)
    have hne : ∀ slot, vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4) ≠ levelHeaderAddress logical.top slot := by
      intro slot he
      have := levelHeaderAddress_positive logical.top slot
      omega
    simpa [levelHeaderIntegerSetsMemory,finishEpisodeAssignments,Function.update_of_ne (hne 4),
      Function.update_of_ne (hne 5),Function.update_of_ne (hne 6),Function.update_of_ne (hne 9)] using aCache v hv

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FinishEpisodeMemoryFacts

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma finish_header_frame (I : ℤ → ℤ) (level : ℕ) (z : ℤ)
    (hNe : ∀ slot ∈ ([4,5,6,9] : List ℕ), z ≠ levelHeaderAddress level slot) :
    levelHeaderIntegerSetsMemory I level finishEpisodeAssignments z=I z := by
  simp [levelHeaderIntegerSetsMemory,finishEpisodeAssignments,
    Function.update_of_ne (hNe 4 (by simp)),Function.update_of_ne (hNe 5 (by simp)),
    Function.update_of_ne (hNe 6 (by simp)),Function.update_of_ne (hNe 9 (by simp))]

lemma finish_raw_integer_below {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell : ℕ)
    (z : ℤ) (hz : z < 128) :
    finishEpisodeIntegerMemory I logical ell z=
      clearVertexFieldSetRecords (16*(ell+3)) (16*(logical.top+1)+4) (logical.frames logical.top).cache I z := by
  apply finish_header_frame
  intro slot hs he
  have := levelHeaderAddress_positive logical.top slot
  omega

lemma finish_raw_integer_global {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell : ℕ)
    (z : ℤ) (hz : 0 ≤ z) (h128 : z < 128) : finishEpisodeIntegerMemory I logical ell z=I z := by
  rw [finish_raw_integer_below _ _ _ _ h128,clear_vertex_field_set_positive _ _ _ _ _ hz]

lemma finish_raw_integer_field {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (v : Fin n) (field : ℕ) (hf : field < 16*(ell+3))
    (hNe : field ≠ 16*(logical.top+1)+4) :
    finishEpisodeIntegerMemory I logical ell (vertexRecordAddress (16*(ell+3)) v.val field)=
      I (vertexRecordAddress (16*(ell+3)) v.val field) := by
  rw [finish_raw_integer_below _ _ _ _ (by have := vertexRecordAddress_negative (16*(ell+3)) v.val field; omega)]
  exact clear_vertex_field_set_other_field _ _ _ _ _ (by omega) hf hNe v

lemma finish_raw_integer_header_same {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell slot : ℕ)
    (hOther : slot ∉ ([4,5,6,9] : List ℕ)) :
    finishEpisodeIntegerMemory I logical ell (levelHeaderAddress logical.top slot)=I (levelHeaderAddress logical.top slot) := by
  rw [finishEpisodeIntegerMemory,finish_header_frame]
  · apply clear_vertex_field_set_positive
    have := levelHeaderAddress_positive logical.top slot
    omega
  · intro field hf he
    have hEq : slot=field := (level_header_same_level logical.top slot field).mp he
    exact hOther (hEq ▸ hf)

lemma finish_raw_integer_header_other {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell j slot : ℕ)
    (hOther : j ≠ logical.top) (hSlot : slot < 32) :
    finishEpisodeIntegerMemory I logical ell (levelHeaderAddress j slot)=I (levelHeaderAddress j slot) := by
  rw [finishEpisodeIntegerMemory,finish_header_frame]
  · apply clear_vertex_field_set_positive
    have := levelHeaderAddress_positive j slot
    omega
  · intro field hf he
    have hField : field < 32 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hf; omega
    exact hOther (levelHeaderAddress_injective j logical.top slot field hSlot hField he).1

lemma finish_raw_integer_above {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (z : ℤ) (hz : 128+32*((ell+2 : ℕ) : ℤ) ≤ z) :
    finishEpisodeIntegerMemory I logical ell z=I z := by
  rw [finishEpisodeIntegerMemory,finish_header_frame]
  · apply clear_vertex_field_set_positive
    omega
  · intro field hf he
    have hField : field < 32 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hf; omega
    unfold levelHeaderAddress at he
    omega

lemma finish_raw_cache_words {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell : ℕ) :
    finishEpisodeIntegerMemory I logical ell (levelHeaderAddress logical.top 4)=0 ∧
    finishEpisodeIntegerMemory I logical ell (levelHeaderAddress logical.top 5)=0 ∧
    finishEpisodeIntegerMemory I logical ell (levelHeaderAddress logical.top 6)=0 ∧
    finishEpisodeIntegerMemory I logical ell (levelHeaderAddress logical.top 9)=0 := by
  simp [finishEpisodeIntegerMemory,finishEpisodeAssignments,levelHeaderIntegerSetsMemory]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FinishEpisodeSelectedMemory

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 12000000 in
def finish_episode_selected_pending_memory {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hI : out.scalar.integerMemory=finishEpisodeIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hCache : ∀ v ∈ parentDomain logical logical.top,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0) :
    FramePendingKeys g (finishEpisode logical) logical.top (16*(ell+3)) length out
      (128+32*((ell+2 : ℕ) : ℤ)) := by
  let f := pm.frames logical.top le_rfl
  let src := logical.frames logical.top
  have hFrame : (finishEpisode logical).frames logical.top=
      {src with Q := src.Q,W := src.W,theta := src.theta,openBudget := false,childrenThisEpisode := src.childrenThisEpisode,cache := ∅,high := src.active.filter (fun v => 3*src.theta*LocalPush.deg g.graph v ≤ src.residual v),pc := src.pc} := by
    rw [canonical_high_filter g logical hKeys logical.top le_rfl,finish_episode_selected]
  have hWords := finish_raw_cache_words st.scalar.integerMemory logical ell
  refine f.reset_cache_pending (next := finishEpisode logical) src.Q src.W src.theta src.pc false src.childrenThisEpisode
    hFrame (finish_episode_domain logical logical.top) hFree
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hCache ?_ ?_
  · intro slot hs hOther
    rw [hI]
    exact finish_raw_integer_header_same _ _ _ _ (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hOther ⊢; tauto)
  · intro slot hs hOther
    exact congrFun hR _
  · rw [hI,finish_raw_integer_header_same _ _ _ _ (by simp)]
    exact f.pc
  · exact (congrFun hR _).trans f.Q
  · exact (congrFun hR _).trans f.W
  · exact (congrFun hR _).trans f.theta
  · rw [hI]
    exact hWords.2.2.2
  · rw [hI,finish_raw_integer_header_same _ _ _ _ (by simp)]
    exact f.children
  · rw [hI]
    exact hWords.1
  · rw [hI]
    exact hWords.2.1
  · rw [hI]
    exact hWords.2.2.1
  · intro v hv field hField
    rw [hI]
    exact finish_raw_integer_field _ _ _ hDepth v field (by omega) (by omega)
  · intro v hv field
    exact congrFun hR _
  · intro v hv
    apply pm.knownDegree
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hStored hv))
  · intro z hz
    rw [hI]
    exact finish_raw_integer_above _ _ _ hDepth z (f.owned_above z hz)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FinishEpisodeOtherMemory

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 8000000 in
def finish_episode_other_frame_memory {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hI : out.scalar.integerMemory=finishEpisodeIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=st.scalar.core.mem)
    (j : ℕ) (hj : j ≤ logical.top) (hOther : j ≠ logical.top) :
    RecursiveFrameMemory g (finishEpisode logical) j (16*(ell+3)) length out
      (128+32*((ell+2 : ℕ) : ℤ)) := by
  let f := pm.frames j hj
  let logicalFrame := f.logical_frame (finish_episode_other logical j hOther) (finish_episode_domain logical j)
  refine logicalFrame.scoped_frame hFree ?_ ?_ ?_ ?_ ?_
  · intro slot hs
    rw [hI]
    exact finish_raw_integer_header_other _ _ _ _ _ hOther hs
  · intro slot hs
    rw [hR]
  · intro v hv field hf hScope
    rw [hI]
    exact finish_raw_integer_field _ _ _ hDepth v field (by omega) (by omega)
  · intro v hv field hf hScope
    rw [hR]
  · intro z hz
    have hOld : z ∈ f.owned := hz
    rw [hI]
    exact finish_raw_integer_above _ _ _ hDepth z (f.owned_above z hOld)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FinishEpisodePendingMemory

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 16000000 in
def finish_episode_pending_machine_memory {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical)
    (hI : out.scalar.integerMemory=finishEpisodeIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hCache : ∀ v ∈ parentDomain logical logical.top,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : MachinePendingKeys g s α ε ell length (finishEpisode logical) out := by
  classical
  have hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 := le_of_eq (hP 20 (by simp)).symm
  let selected := finish_episode_selected_pending_memory pm hDepth hStored hKeys hFree hI hR hCache
  let next := finishEpisode logical
  let frames : ∀ j ≤ next.top, FramePendingKeys g next j (16*(ell+3)) length out (128+32*((ell+2 : ℕ) : ℤ)) :=
    fun j hj => if hEq : j=logical.top then by subst j; exact selected
      else FramePendingKeys.ofMemory (finish_episode_other_frame_memory pm hDepth hFree hI hR j hj hEq)
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
    exact finish_raw_integer_field _ _ _ hDepth v field (by omega) (by omega)
  have hGraph : GraphCache g out.scalar.integerMemory (16*(ell+3)) logical.stored (out.scalar.core.ptrs 20) := by
    apply (pm.graphCache.frame g _ _ _ _ _ hFields ?_).mono_free hFree
    intro v hv i hi
    rw [hI]
    apply finish_raw_integer_above _ _ _ hDepth
    have hBase := pm.rowAbove v hv
    have hi0 := Int.natCast_nonneg i
    omega
  have hGlobal : ∀ z, 0 ≤ z → z < 128 → out.scalar.integerMemory z=st.scalar.integerMemory z := by
    intro z hz h128
    rw [hI]
    exact finish_raw_integer_global _ _ _ z hz h128
  have hVertexR : ∀ v : Fin n, ∀ field,
      out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field)=st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val field) := by
    intro v field
    rw [hR]
  have hRealGlobal : ∀ z, z < 128 → out.scalar.core.mem z=st.scalar.core.mem z := by
    intro z hz
    rw [hR]
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

-- Proof module: Solutions.FinishEpisodePendingProperties

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma finish_episode_pending_machine_frame_mass {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical)
    (hI : out.scalar.integerMemory=finishEpisodeIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hCache : ∀ v ∈ parentDomain logical logical.top,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) (j : ℕ) (hj : j ≤ logical.top) :
    ((finish_episode_pending_machine_memory pm hDepth hStored hKeys hI hR hCache hP hG hO).frames j hj).queueMass=(pm.frames j hj).queueMass := by
  classical
  dsimp only [finish_episode_pending_machine_memory]
  by_cases hEq : j=logical.top
  · subst j
    rw [dif_pos rfl]
    rfl
  · rw [dif_neg hEq]
    rfl

lemma finish_episode_pending_machine_exterior_keys {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical)
    (hI : out.scalar.integerMemory=finishEpisodeIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hCache : ∀ v ∈ parentDomain logical logical.top,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) (j : ℕ) (hj : j ≤ logical.top) :
    ((finish_episode_pending_machine_memory pm hDepth hStored hKeys hI hR hCache hP hG hO).frames j hj).exteriorObject.keys=(pm.frames j hj).exteriorObject.keys := by
  classical
  dsimp only [finish_episode_pending_machine_memory]
  by_cases hEq : j=logical.top
  · subst j
    rw [dif_pos rfl]
    rfl
  · rw [dif_neg hEq]
    rfl

lemma finish_episode_pending_machine_high_keys {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical)
    (hI : out.scalar.integerMemory=finishEpisodeIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hCache : ∀ v ∈ parentDomain logical logical.top,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) (j : ℕ) (hj : j ≤ logical.top) :
    ((finish_episode_pending_machine_memory pm hDepth hStored hKeys hI hR hCache hP hG hO).frames j hj).highObject.keys=(pm.frames j hj).highObject.keys := by
  classical
  dsimp only [finish_episode_pending_machine_memory]
  by_cases hEq : j=logical.top
  · subst j
    rw [dif_pos rfl]
    rfl
  · rw [dif_neg hEq]
    rfl

lemma finish_episode_pending_machine_mass {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical)
    (hI : out.scalar.integerMemory=finishEpisodeIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hCache : ∀ v ∈ parentDomain logical logical.top,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+4))=0)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : (finish_episode_pending_machine_memory pm hDepth hStored hKeys hI hR hCache hP hG hO).queueMass=pm.queueMass := by
  unfold MachinePendingKeys.queueMass RecursiveMachineMemory.queueMass
  change (∑ j ∈ Finset.range (logical.top+1), if hj : j ≤ logical.top then
    ((finish_episode_pending_machine_memory pm hDepth hStored hKeys hI hR hCache hP hG hO).frames j hj).queueMass else 0)= _
  apply Finset.sum_congr rfl
  intro j hj
  have hLive : j ≤ logical.top := by have := Finset.mem_range.mp hj; omega
  simp only [dif_pos hLive]
  exact finish_episode_pending_machine_frame_mass pm hDepth hStored hKeys hI hR hCache hP hG hO j hLive

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FinishEpisodeVisited

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 10000000 in
lemma finish_episode_visited {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (next : MachinePendingKeys g s α ε ell length (finishEpisode logical) out)
    (hDepth : logical.top ≤ ell)
    (hI : out.scalar.integerMemory=finishEpisodeIntegerMemory st.scalar.integerMemory logical ell)
    (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hExtKeys : ∀ j, ∀ hj : j ≤ logical.top, (next.frames j hj).exteriorObject.keys=(pm.frames j hj).exteriorObject.keys)
    (hHighKeys : ∀ j, ∀ hj : j ≤ logical.top, (next.frames j hj).highObject.keys=(pm.frames j hj).highObject.keys) :
    PendingVisitedKeys next Finset.univ := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro j hj v hv
    change j ≤ logical.top at hj
    rw [finish_episode_theta,finish_episode_domain] at *
    have hvD : v ∈ parentDomain logical j := (Finset.mem_inter.mp hv).1
    have hFields : ∀ field, field=0 ∨ field=16*(j+1)+2 →
        out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)=
          st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field) := by
      intro field hf
      rw [hI]
      exact finish_raw_integer_field _ _ _ hDepth v field (by omega) (by omega)
    change out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+4))= _
    rw [hR,hFields _ (by omega),hFields _ (by omega)]
    exact (pm.frames j hj).highBoolean v hvD
  · intro j hj v hv hKey
    rw [finish_episode_exterior] at hKey
    rw [hExtKeys j hj]
    exact (pm.frames j hj).exteriorCover (Finset.mem_image.mpr ⟨v,hKey,rfl⟩)
  · intro j hj v hv hKey
    rw [finish_episode_high] at hKey
    rw [hHighKeys j hj]
    exact (pm.frames j hj).highCover (Finset.mem_image.mpr ⟨v,hKey,rfl⟩)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FinishEpisodeExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 16000000 in
lemma finish_episode_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length (finishEpisode logical) out,
      MachineEval m g ω finishEpisodeCode st
        ((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+60) out ∧
      memory.queueMass=pm.queueMass ∧
      out.work=st.work+((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+60 : ℕ) ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨out,ex,hI,hCache,hR,hW,hQ,hO,hH⟩ := finish_episode_raw_exec m g ω logical s α ε ell length st hh pm hDepth
  have hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ex.pointer_frame _ (by decide)
  have hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ex.real_register_frame _ (by decide)
  let pending := finish_episode_pending_machine_memory pm hDepth hStored hKeys hI hR hCache hP hG hO
  have inv : PendingVisitedKeys pending Finset.univ := finish_episode_visited pm pending hDepth hI hR
    (finish_episode_pending_machine_exterior_keys pm hDepth hStored hKeys hI hR hCache hP hG hO)
    (finish_episode_pending_machine_high_keys pm hDepth hStored hKeys hI hR hCache hP hG hO)
  let memory := inv.finish rfl
  exact ⟨out,memory,ex,(inv.finish_mass rfl).trans
    (finish_episode_pending_machine_mass pm hDepth hStored hKeys hI hR hCache hP hG hO),hW,hQ,hO,hH⟩

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution : ∀ (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical),
∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length (finishEpisode logical) out,
      MachineEval m g ω finishEpisodeCode st
        ((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+60) out ∧
      memory.queueMass=pm.queueMass ∧
      out.work=st.work+((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+60 : ℕ) ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  exact @NearlyOptimalPPR.Computation.finish_episode_exec
