-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.uniform_local_algorithm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:46:21.513833+00:00
-- url     : https://prove2.me/submissions/b0db36ad-0fd3-440b-b52a-a13e261121b7

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
import Theorems.Thm_NearlyOptimalPPR_Computation_compiler_accessible_recursive_running_time
import Theorems.Thm_NearlyOptimalPPR_Computation_controller_source_run_certified
import Theorems.Thm_NearlyOptimalPPR_Computation_normalization_composes
import Theorems.Thm_NearlyOptimalPPR_Computation_push_core_bound
import Theorems.Thm_NearlyOptimalPPR_Computation_push_correctness_work
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_level_work
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_preparation_exec
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_residual_error
set_option linter.all false
-- Proof module: Solutions.CompilerStepDebitFacts

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma compiler_cost_work_changeFrame (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).work=st.work := rfl
@[simp] lemma compiler_cost_work_PC (st : RecursiveState n) (pc : NormalizePC) : (changePC st pc).work=st.work := rfl
@[simp] lemma compiler_cost_work_debit (st : RecursiveState n) (j : ℕ) (c : ℝ≥0∞) : (debit st j c).work=st.work+c := rfl
@[simp] lemma compiler_cost_work_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) : (refreshKeys g st T).work=st.work := rfl
@[simp] lemma compiler_cost_work_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) : (jointUpdate g α st h).work=st.work := rfl
@[simp] lemma compiler_cost_work_finish (st : RecursiveState n) : (finishEpisode st).work=st.work := rfl
@[simp] lemma compiler_cost_work_admit (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) : (admitStage g st t v).work=st.work := by
  unfold admitStage
  dsimp only
  split_ifs <;> rfl
@[simp] lemma compiler_cost_work_raw (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) (δ : ℝ) :
    (rawExterior g α st t v δ).work=st.work := rfl
@[simp] lemma compiler_cost_work_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).work=if P then a.work else b.work := by split <;> rfl
@[simp] lemma compiler_cost_keyCost_debit (st : RecursiveState n) (j : ℕ) (c : ℝ≥0∞) : keyCost (debit st j c)=keyCost st := rfl

@[simp] lemma compiler_cost_work_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) :
    (completeComponent m g s α st).work=st.work+jointCost m g st (st.frames 0).active+((st.frames 0).active.card+1 : ℕ) := by
  simp [completeComponent,debit,add_assoc]

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


def compile (base : ℕ) : MachineCode → Program
  | .skip => []
  | .atom i => [i]
  | .seq a b => compile base a ++ compile (base + size a) b
  | .branchReal r a b =>
      [.scalar (.core (.jle r (base + size b + 2)))] ++
      compile (base+1) b ++
      [.scalar (.core (.pjle 0 0 (base + size a + size b + 2)))] ++
      compile (base + size b + 2) a
  | .branchPointer r s a b =>
      [.scalar (.core (.pjle r s (base + size b + 2)))] ++
      compile (base+1) b ++
      [.scalar (.core (.pjle 0 0 (base + size a + size b + 2)))] ++
      compile (base + size b + 2) a
  | .whileReal r b =>
      [.scalar (.core (.jle r (base + size b + 2)))] ++
      compile (base+1) b ++ [.scalar (.core (.pjle 0 0 base))]
  | .whilePointer r s b =>
      [.scalar (.core (.pjle r s (base + size b + 2)))] ++
      compile (base+1) b ++ [.scalar (.core (.pjle 0 0 base))]

lemma compile_length (base : ℕ) (a : MachineCode) : (compile base a).length = size a := by
  induction a generalizing base <;> simp_all [compile,size] <;> omega


def wellFormed : MachineCode → Prop
  | .skip => True
  | .atom i => straightInstruction i ∧ admissible [i]
  | .seq a b | .branchReal _ a b | .branchPointer _ _ a b => wellFormed a ∧ wellFormed b
  | .whileReal _ b | .whilePointer _ _ b => wellFormed b

lemma admissible_append (a b : Program) : admissible (a++b) ↔ admissible a ∧ admissible b := by
  unfold admissible scalarProgram
  rw [List.map_append]
  unfold LocalPush.Admissible
  simp only [List.mem_append,or_imp,forall_and]

lemma compile_admissible (base : ℕ) (a : MachineCode) (h : wellFormed a) :
    admissible (compile base a) := by
  induction a generalizing base with
  | skip => simp [compile,admissible,scalarProgram,LocalPush.Admissible]
  | atom i => exact h.2
  | seq a b ia ib => exact admissible_append _ _ |>.mpr ⟨ia _ h.1,ib _ h.2⟩
  | branchReal r a b ia ib =>
    simp only [compile,admissible_append]
    refine ⟨⟨⟨?_,ib _ h.2⟩,?_⟩,ia _ h.1⟩ <;>
      simp [admissible,scalarProgram,LocalPush.Admissible]
  | branchPointer r s a b ia ib =>
    simp only [compile,admissible_append]
    refine ⟨⟨⟨?_,ib _ h.2⟩,?_⟩,ia _ h.1⟩ <;>
      simp [admissible,scalarProgram,LocalPush.Admissible]
  | whileReal r b ib =>
    simp only [compile,admissible_append]
    refine ⟨⟨?_,ib _ h⟩,?_⟩ <;> simp [admissible,scalarProgram,LocalPush.Admissible]
  | whilePointer r s b ib =>
    simp only [compile,admissible_append]
    refine ⟨⟨?_,ib _ h⟩,?_⟩ <;> simp [admissible,scalarProgram,LocalPush.Admissible]

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
set_option maxHeartbeats 2000000 in
lemma straight_relocation (m : SolveModel) (p : Program) {n : ℕ} (g : InputGraph n)
    (ω : ℕ → Bool) (st : MachineState) (i : Instruction)
    (hlookup : p[st.scalar.core.pc]?=some i) (hs : straightInstruction i)
    (hh : st.scalar.halted=false) :
    let z := machineStep m [i] g ω (pcSet st 0)
    machineStep m p g ω st=pcSet z (st.scalar.core.pc+z.scalar.core.pc) := by
  classical
  cases i with
  | emit a b => simp [machineStep,pcSet,hh,hlookup]
  | solve r =>
    let k := (st.scalar.core.ptrs r.dimension).toNat
    let q := (st.scalar.core.ptrs r.length).toNat
    let A := suppliedMatrix st.scalar r k q
    let x := A⁻¹ *ᵥ (fun i : Fin k => st.scalar.core.mem (st.scalar.core.ptrs r.rhs+i.val))
    let V := 0 < st.scalar.core.ptrs r.dimension ∧ 0 ≤ st.scalar.core.ptrs r.length ∧ SDDM A
    let L : MachineState := ⟨writeAnswer st.scalar r k x,st.output,st.work+solveCharge m k q⟩
    let R : MachineState := ⟨writeAnswer (pcSet st 0).scalar r k x,st.output,st.work+solveCharge m k q⟩
    let F : MachineState := {st with work := st.work+1}
    let RF : MachineState := pcSet F 0
    simp only [machineStep,pcSet_halted,hh,Bool.false_eq_true,ite_false,hlookup,pcSet_pc,List.getElem?_cons_zero]
    change (if V then L else F)=pcSet (if V then R else RF)
      (st.scalar.core.pc+(if V then R else RF).scalar.core.pc)
    by_cases hv : V
    · simp only [hv,ite_true]
      rfl
    · simp only [hv,ite_false]
      rfl
  | scalar i =>
    cases i with
    | core i =>
      cases i <;> simp_all [straightInstruction,machineStep,pcSet,LocalPush.step,
        scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,List.getElem?_map]
    | halt => simp [straightInstruction] at hs
    | _ =>
      simp [machineStep,pcSet,hh,hlookup,LocalPush.step,scalarProgram,List.getElem?_map]

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

lemma step_real_branch (m : SolveModel) (p : Program) {n : ℕ} (g : InputGraph n)
    (ω : ℕ → Bool) (st : MachineState) (r target : ℕ)
    (hlookup : p[st.scalar.core.pc]?=some (.scalar (.core (.jle r target))))
    (hh : st.scalar.halted=false) :
    machineStep m p g ω st=pcSet (payUnit st)
      (if st.scalar.core.regs r ≤ 0 then target else st.scalar.core.pc+1) := by
  simp [machineStep,payUnit,pcSet,hh,hlookup,LocalPush.step,scalarProgram,
    LocalPush.coreProgram,List.getElem?_map,SmaleNinth.RAMStep]
  split_ifs <;> rfl

lemma step_pointer_branch (m : SolveModel) (p : Program) {n : ℕ} (g : InputGraph n)
    (ω : ℕ → Bool) (st : MachineState) (a b target : ℕ)
    (hlookup : p[st.scalar.core.pc]?=some (.scalar (.core (.pjle a b target))))
    (hh : st.scalar.halted=false) :
    machineStep m p g ω st=pcSet (payUnit st)
      (if st.scalar.core.ptrs a ≤ st.scalar.core.ptrs b then target else st.scalar.core.pc+1) := by
  simp [machineStep,payUnit,pcSet,hh,hlookup,LocalPush.step,scalarProgram,
    LocalPush.coreProgram,List.getElem?_map,SmaleNinth.RAMStep]
  split_ifs <;> rfl

lemma step_unconditional_branch (m : SolveModel) (p : Program) {n : ℕ} (g : InputGraph n)
    (ω : ℕ → Bool) (st : MachineState) (target : ℕ)
    (hlookup : p[st.scalar.core.pc]?=some (.scalar (.core (.pjle 0 0 target))))
    (hh : st.scalar.halted=false) :
    machineStep m p g ω st=pcSet (payUnit st) target := by
  simpa using step_pointer_branch m p g ω st 0 0 target hlookup hh

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

-- Proof module: Solutions.MachineCodeLayout

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


def codeAt (p : Program) (base : ℕ) (block : Program) : Prop :=
  ∀ i, i < block.length → p[base+i]?=block[i]?

lemma codeAt_self (p : Program) : codeAt p 0 p := by intro i hi; simp
lemma codeAt_append_left (p a b : Program) (base : ℕ) (h : codeAt p base (a++b)) :
    codeAt p base a := by
  intro i hi
  rw [h i (by simpa using lt_of_lt_of_le hi (Nat.le_add_right a.length b.length))]
  exact List.getElem?_append_left hi

lemma codeAt_append_right (p a b : Program) (base : ℕ) (h : codeAt p base (a++b)) :
    codeAt p (base+a.length) b := by
  intro i hi
  rw [show base+a.length+i=base+(a.length+i) by omega,h (a.length+i) (by simpa using Nat.add_lt_add_left hi a.length)]
  rw [List.getElem?_append_right (by omega)]
  simp

lemma codeAt_singleton (p : Program) (base : ℕ) (i : Instruction) (h : codeAt p base [i]) :
    p[base]?=some i := by simpa using h 0 (by simp)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MachineCodeCompiler

set_option autoImplicit false
open Finset Matrix MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma machine_iterate_chain {m : SolveModel} {p : Program} {n : ℕ} {g : InputGraph n}
    {ω : ℕ → Bool} {st mid out : MachineState} {u v : ℕ}
    (h : (machineStep m p g ω)^[u] st=mid) (k : (machineStep m p g ω)^[v] mid=out) :
    (machineStep m p g ω)^[u+v] st=out := by
  rw [Nat.add_comm u v,Function.iterate_add_apply,h,k]

lemma atomState_ready_running (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (i : Instruction) (st : MachineState) (h : (atomState m g ω i st).scalar.core.pc=1) :
    st.scalar.halted=false := by
  by_contra hn
  have ht : st.scalar.halted=true := Bool.eq_true_of_not_eq_false hn
  simp [atomState,machineStep,ht] at h

lemma compiled_atom (m : SolveModel) (p : Program) {n : ℕ} (g : InputGraph n)
    (ω : ℕ → Bool) (st : MachineState) (i : Instruction) (base : ℕ)
    (hc : codeAt p base [i]) (hs : straightInstruction i)
    (h : (atomState m g ω i st).scalar.core.pc=1) :
    machineStep m p g ω (pcSet st base)=pcSet (pcSet (atomState m g ω i st) 0) (base+1) := by
  have hh := atomState_ready_running m g ω i st h
  have hl : p[(pcSet st base).scalar.core.pc]?=some i := codeAt_singleton p base i hc
  have he := straight_relocation m p g ω (pcSet st base) i hl hs (by simpa using hh)
  change (machineStep m [i] g ω (pcSet st 0)).scalar.core.pc=1 at h
  simpa only [pcSet_set,pcSet_pc,atomState,h] using he

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompiledLayout

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
open MachineCode

lemma branch_layout (p : Program) (base : ℕ) (h j : Instruction) (a b : MachineCode)
    (hc : codeAt p base ([h]++b.compile (base+1)++[j]++a.compile (base+b.size+2))) :
    p[base]?=some h ∧ codeAt p (base+1) (b.compile (base+1)) ∧
      p[base+b.size+1]?=some j ∧ codeAt p (base+b.size+2) (a.compile (base+b.size+2)) := by
  have hpre := codeAt_append_left p _ _ base hc
  have hhb := codeAt_append_left p _ _ base hpre
  have hh := codeAt_append_left p _ _ base hhb
  have hb := codeAt_append_right p _ _ base hhb
  have hj := codeAt_append_right p _ _ base hpre
  have ha := codeAt_append_right p _ _ base hc
  refine ⟨codeAt_singleton p base h hh,?_,?_,?_⟩
  · simpa using hb
  · have hj' := codeAt_singleton p _ j hj
    simpa [compile_length,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hj'
  · convert ha using 1 <;> simp only [List.length_append,List.length_cons,List.length_nil,compile_length] <;> omega

lemma while_layout (p : Program) (base : ℕ) (h j : Instruction) (b : MachineCode)
    (hc : codeAt p base ([h]++b.compile (base+1)++[j])) :
    p[base]?=some h ∧ codeAt p (base+1) (b.compile (base+1)) ∧
      p[base+b.size+1]?=some j := by
  have hhb := codeAt_append_left p _ _ base hc
  have hh := codeAt_append_left p _ _ base hhb
  have hb := codeAt_append_right p _ _ base hhb
  have hj := codeAt_append_right p _ _ base hc
  refine ⟨codeAt_singleton p base h hh,?_,?_⟩
  · simpa using hb
  · have hj' := codeAt_singleton p _ j hj
    simpa [compile_length,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hj'

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerCorrectness

set_option autoImplicit false
open Finset Matrix MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
open MachineCode

lemma real_step_at (m : SolveModel) (p : Program) {n : ℕ} (g : InputGraph n)
    (ω : ℕ → Bool) (st : MachineState) (base r target : ℕ)
    (h : p[base]?=some (.scalar (.core (.jle r target)))) (hh : st.scalar.halted=false) :
    (machineStep m p g ω)^[1] (pcSet st base)=pcSet (payUnit st)
      (if st.scalar.core.regs r ≤ 0 then target else base+1) := by
  by_cases hg : st.scalar.core.regs r ≤ 0 <;>
    simpa [hg] using step_real_branch m p g ω (pcSet st base) r target h (by simpa using hh)

lemma pointer_step_at (m : SolveModel) (p : Program) {n : ℕ} (g : InputGraph n)
    (ω : ℕ → Bool) (st : MachineState) (base r s target : ℕ)
    (h : p[base]?=some (.scalar (.core (.pjle r s target)))) (hh : st.scalar.halted=false) :
    (machineStep m p g ω)^[1] (pcSet st base)=pcSet (payUnit st)
      (if st.scalar.core.ptrs r ≤ st.scalar.core.ptrs s then target else base+1) := by
  by_cases hg : st.scalar.core.ptrs r ≤ st.scalar.core.ptrs s <;>
    simpa [hg] using step_pointer_branch m p g ω (pcSet st base) r s target h (by simpa using hh)

lemma jump_step_at (m : SolveModel) (p : Program) {n : ℕ} (g : InputGraph n)
    (ω : ℕ → Bool) (st : MachineState) (base target : ℕ)
    (h : p[base]?=some (.scalar (.core (.pjle 0 0 target)))) (hh : st.scalar.halted=false) :
    (machineStep m p g ω)^[1] (pcSet st base)=pcSet (payUnit st) target := by
  simpa using step_unconditional_branch m p g ω (pcSet st base) target h (by simpa using hh)

set_option maxHeartbeats 1000000 in
lemma compiled_execution {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {code : MachineCode} {st out : MachineState} {u : ℕ}
    (e : MachineEval m g ω code st u out) (hw : code.wellFormed)
    (p : Program) (base : ℕ) (hc : codeAt p base (code.compile base)) :
    (machineStep m p g ω)^[u] (pcSet st base)=pcSet out (base+code.size) := by
  induction e generalizing p base with
  | skip st => simp [size]
  | atom i st ready =>
    simpa [compile,size] using compiled_atom m p g ω st i base hc hw.1 ready
  | @seq a b st mid out u v ea eb ia ib =>
    have ha := codeAt_append_left p (a.compile base) (b.compile (base+a.size)) base hc
    have hb := codeAt_append_right p (a.compile base) (b.compile (base+a.size)) base hc
    have hb' : codeAt p (base+a.size) (b.compile (base+a.size)) := by simpa [compile_length] using hb
    have he := machine_iterate_chain (ia hw.1 p base ha) (ib hw.2 p (base+a.size) hb')
    simpa [size,Nat.add_assoc] using he
  | @realNonpos r a b st out u hh guard ea ia =>
    obtain ⟨hhead,hb,hjump,ha⟩ := branch_layout p base _ _ a b hc
    have head := real_step_at m p g ω st base r (base+b.size+2) hhead hh
    simp only [guard,ite_true] at head
    have body := ia hw.1 p (base+b.size+2) ha
    have he := machine_iterate_chain head body
    simpa only [size,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using he
  | @realPos r a b st mid u hh guard eb ib =>
    obtain ⟨hhead,hb,hjump,ha⟩ := branch_layout p base _ _ a b hc
    have head := real_step_at m p g ω st base r (base+b.size+2) hhead hh
    simp only [guard,ite_false] at head
    have body := ib hw.2 p (base+1) hb
    have hm : mid.scalar.halted=false := (eb.halted hw.2).trans (by simpa using hh)
    have jump := jump_step_at m p g ω mid (base+b.size+1) (base+a.size+b.size+2) hjump hm
    have hj : (machineStep m p g ω)^[1] (pcSet mid (base+1+b.size))=
        pcSet (payUnit mid) (base+a.size+b.size+2) := by simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using jump
    have he := machine_iterate_chain (machine_iterate_chain head body) hj
    simpa only [size,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using he
  | @realDone r body st  hh guard  =>
    obtain ⟨hhead,hbody,hjump⟩ := while_layout p base _ _ body hc
    have head := real_step_at m p g ω st base r (base+body.size+2) hhead hh
    simp only [guard,ite_true] at head
    simpa only [size,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using head
  | @realNext r body st mid out u v hh guard eb er ib ir =>
    obtain ⟨hhead,hbody,hjump⟩ := while_layout p base _ _ body hc
    have head := real_step_at m p g ω st base r (base+body.size+2) hhead hh
    simp only [guard,ite_false] at head
    have bodyexec := ib hw p (base+1) hbody
    have hm : mid.scalar.halted=false := (eb.halted hw).trans (by simpa using hh)
    have jump := jump_step_at m p g ω mid (base+body.size+1) base hjump hm
    have hj : (machineStep m p g ω)^[1] (pcSet mid (base+1+body.size))=
        pcSet (payUnit mid) base := by simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using jump
    have tail := ir hw p base hc
    have he := machine_iterate_chain (machine_iterate_chain (machine_iterate_chain head bodyexec) hj) tail
    simpa only [size,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using he
  | @pointerLe r z a b st out u hh guard ea ia =>
    obtain ⟨hhead,hb,hjump,ha⟩ := branch_layout p base _ _ a b hc
    have head := pointer_step_at m p g ω st base r z (base+b.size+2) hhead hh
    simp only [guard,ite_true] at head
    have body := ia hw.1 p (base+b.size+2) ha
    have he := machine_iterate_chain head body
    simpa only [size,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using he
  | @pointerGt r z a b st mid u hh guard eb ib =>
    obtain ⟨hhead,hb,hjump,ha⟩ := branch_layout p base _ _ a b hc
    have head := pointer_step_at m p g ω st base r z (base+b.size+2) hhead hh
    simp only [guard,ite_false] at head
    have body := ib hw.2 p (base+1) hb
    have hm : mid.scalar.halted=false := (eb.halted hw.2).trans (by simpa using hh)
    have jump := jump_step_at m p g ω mid (base+b.size+1) (base+a.size+b.size+2) hjump hm
    have hj : (machineStep m p g ω)^[1] (pcSet mid (base+1+b.size))=
        pcSet (payUnit mid) (base+a.size+b.size+2) := by simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using jump
    have he := machine_iterate_chain (machine_iterate_chain head body) hj
    simpa only [size,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using he
  | @pointerDone r z body st  hh guard  =>
    obtain ⟨hhead,hbody,hjump⟩ := while_layout p base _ _ body hc
    have head := pointer_step_at m p g ω st base r z (base+body.size+2) hhead hh
    simp only [guard,ite_true] at head
    simpa only [size,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using head
  | @pointerNext r z body st mid out u v hh guard eb er ib ir =>
    obtain ⟨hhead,hbody,hjump⟩ := while_layout p base _ _ body hc
    have head := pointer_step_at m p g ω st base r z (base+body.size+2) hhead hh
    simp only [guard,ite_false] at head
    have bodyexec := ib hw p (base+1) hbody
    have hm : mid.scalar.halted=false := (eb.halted hw).trans (by simpa using hh)
    have jump := jump_step_at m p g ω mid (base+body.size+1) base hjump hm
    have hj : (machineStep m p g ω)^[1] (pcSet mid (base+1+body.size))=
        pcSet (payUnit mid) base := by simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using jump
    have tail := ir hw p base hc
    have he := machine_iterate_chain (machine_iterate_chain (machine_iterate_chain head bodyexec) hj) tail
    simpa only [size,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using he

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ScalarCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


@[simp] lemma pcSet_payUnit_zero (st : MachineState) : pcSet (payUnit st) 0=payUnit st := rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PowerCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma powerCode_wellFormed : powerCode.wellFormed := by
  simp [powerCode,powerLoop,powerBody,MachineCode.wellFormed,RealOperation.instruction,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨1,by norm_num⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SquareCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma squareCode_wellFormed : squareCode.wellFormed := by
  simp [squareCode,squareLoop,squareBody,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DepthCandidateCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma depthCandidateCode_wellFormed : depthCandidateCode.wellFormed := by
  refine ⟨squareCode_wellFormed,?_,powerCode_wellFormed⟩
  simp [MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AccessibleDepth

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable


lemma accessibleDepth_min (K : ℝ) (j : ℕ) (hj : j < accessibleDepth K) :
    ((j+2 : ℕ) : ℝ)^((j+2)*(j+2)) ≤ K := by
  exact le_of_not_gt (Nat.find_min (depthPowerTest_exists K) hj)

lemma accessibleDepth_log_lower (K : ℝ) (hK : 0 < K) (hd : 0 < accessibleDepth K) :
    ((accessibleDepth K+1 : ℕ) : ℝ)^2*Real.log ((accessibleDepth K+1 : ℕ) : ℝ) ≤
      Real.log K := by
  have h := accessibleDepth_min K (accessibleDepth K-1) (by omega)
  have he : accessibleDepth K-1+2=accessibleDepth K+1 := by omega
  rw [he] at h
  have hp : (0 : ℝ) < ((accessibleDepth K+1 : ℕ) : ℝ) := by positivity
  have hh := (Real.log_le_log_iff (pow_pos hp _) hK).mpr h
  rw [Real.log_pow] at hh
  simpa only [Nat.cast_mul,pow_two] using hh

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DepthSearchEstimates

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma log_two_bounds : (1/2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at hh ⊢
    linarith
  · have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at hh
    exact hh

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BalancedDepthScalars

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma log_four_gt_one : (1 : ℝ) < Real.log 4 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).mpr
  exact Real.exp_one_lt_three.trans (by norm_num)

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DepthSearchCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma depthSearchCode_wellFormed : depthSearchCode.wellFormed := by
  simp [depthSearchCode,depthLoopCode,depthBodyCode,depthTestCode,depthDecisionCode,
    MachineCode.wellFormed,depthCandidateCode_wellFormed,RealOperation.instruction,sequenceCode,coreCode,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨⟨1,by norm_num⟩,⟨0,by norm_num⟩⟩

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

-- Proof module: Solutions.HeapMinScanCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma heapMinScanCode_wellFormed : heapMinScanCode.wellFormed := by
  simp [heapMinScanCode,minScanLoopCode,minScanBodyCode,inspectMinRootCode,compareMinRootCode,
    chooseMinRootCode,sequenceCode,coreCode,MachineCode.wellFormed,straightInstruction,
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

-- Proof module: Solutions.LevelHeaderCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma levelHeaderAddressCode_wellFormed (slot : ℕ) : (levelHeaderAddressCode slot).wellFormed := by
  simp [levelHeaderAddressCode,levelHeaderAddressInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.LevelHeaderRealFrom

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderRealFromCode_wellFormed (slot source : ℕ) : (levelHeaderRealFromCode slot source).wellFormed := by
  refine ⟨?_,levelHeaderRealStoreCode_wellFormed slot⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderSets

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderIntegerSetsCode_wellFormed (assignments : List (ℕ × ℤ)) :
    (levelHeaderIntegerSetsCode assignments).wellFormed := by
  induction assignments with
  | nil => trivial
  | cons kv rest ih => exact ⟨levelHeaderIntegerSetCode_wellFormed kv.1 kv.2,ih⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelHeaderRealZeros

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelHeaderRealZerosCode_wellFormed (slots : List ℕ) : (levelHeaderRealZerosCode slots).wellFormed := by
  induction slots with
  | nil => trivial
  | cons slot rest ih => exact ⟨levelHeaderRealZeroCode_wellFormed slot,ih⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshHeaderDefaults

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma freshHeaderDefaultsCode_wellFormed : freshHeaderDefaultsCode.wellFormed :=
  ⟨levelHeaderIntegerSetsCode_wellFormed _,levelHeaderRealZerosCode_wellFormed _⟩

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

-- Proof module: Solutions.FrameScalarParameters

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameScalarParametersCode_wellFormed : frameScalarParametersCode.wellFormed :=
  ⟨levelHeaderRealFromCode_wellFormed 0 12,levelHeaderRealFromCode_wellFormed 1 13⟩

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

-- Proof module: Solutions.BlockCandidatePower

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma blockCandidatePowerCode_wellFormed : blockCandidatePowerCode.wellFormed := by
  refine ⟨?_,powerCode_wellFormed⟩
  simp [blockCandidatePrefixCode,linearCode,blockCandidatePrefixInstructions,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BlockCandidateDecision

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma blockCandidateDecisionCode_wellFormed : blockCandidateDecisionCode.wellFormed := by
  simp [blockCandidateDecisionCode,coreCode,RealOperation.instruction,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨0,by norm_num⟩

lemma blockCandidateTestCode_wellFormed : blockCandidateTestCode.wellFormed :=
  ⟨blockCandidatePowerCode_wellFormed,blockCandidateDecisionCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BlockTargetPreparation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma blockTargetPreparationCode_wellFormed : blockTargetPreparationCode.wellFormed := by
  refine ⟨?_,powerCode_wellFormed,?_⟩
  all_goals
    simp [blockTargetPrefixCode,blockTargetTailCode,linearCode,blockTargetPrefixInstructions,
      blockTargetTailInstructions,RealOperation.instruction,sequenceCode,MachineCode.wellFormed,
      straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
    exact ⟨1,by norm_num⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BalancedBlockExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma balancedBlockCode_wellFormed : balancedBlockCode.wellFormed := by
  refine ⟨blockTargetPreparationCode_wellFormed,blockCandidateTestCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameBlockCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameBlockPrepCode_wellFormed : frameBlockPrepCode.wellFormed := by
  simp [frameBlockPrepCode,frameBlockPrepInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma frameThresholdRestoreCode_wellFormed : frameThresholdRestoreCode.wellFormed := by
  refine ⟨levelHeaderRealLoadCode_wellFormed 1,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma frameBlockPreparationCode_wellFormed : frameBlockPreparationCode.wellFormed :=
  ⟨levelHeaderRealLoadCode_wellFormed 0,frameBlockPrepCode_wellFormed,balancedBlockCode_wellFormed,
    levelHeaderIntegerFromCode_wellFormed 14 85,frameThresholdRestoreCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshAllocation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma reserveArrayCode_wellFormed : reserveArrayCode.wellFormed := by
  simp [reserveArrayCode,coreCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RankArrayInitialize

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma rankArrayInitializeCode_wellFormed : rankArrayInitializeCode.wellFormed := by
  simp [rankArrayInitializeCode,rankZeroLoopCode,rankZeroBodyCode,linearCode,rankZeroInstructions,sequenceCode,
    coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RankQueueAllocation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma rankQueueAllocationCode_wellFormed : rankQueueAllocationCode.wellFormed :=
  ⟨reserveArrayCode_wellFormed,rankArrayInitializeCode_wellFormed⟩

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeaderQueueAllocation

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma headerQueueAllocationCode_wellFormed (slot : ℕ) : (headerQueueAllocationCode slot).wellFormed :=
  ⟨rankQueueAllocationCode_wellFormed,levelHeaderIntegerFromCode_wellFormed slot 13⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshQueuePair

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma freshQueuePairCode_wellFormed : freshQueuePairCode.wellFormed :=
  ⟨headerQueueAllocationCode_wellFormed 7,headerQueueAllocationCode_wellFormed 8⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelContextPreparation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma levelContextCode_wellFormed : levelContextCode.wellFormed := by
  simp [levelContextCode,levelContextInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma frameRankLoadCode_wellFormed : frameRankLoadCode.wellFormed := by
  simp [frameRankLoadCode,frameRankLoadInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshHeaderCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma freshHeaderCode_wellFormed : freshHeaderCode.wellFormed :=
  ⟨frameScalarParametersCode_wellFormed,freshHeaderDefaultsCode_wellFormed,frameBlockPreparationCode_wellFormed,
    frameRankLoadCode_wellFormed,freshQueuePairCode_wellFormed,levelContextCode_wellFormed⟩

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

-- Proof module: Solutions.GraphQueryExecution

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma nodeOf_vertex {n : ℕ} (v : Fin n) : LocalPush.nodeOf n (v.val : ℤ)=some v := by
  simp [LocalPush.nodeOf,v.isLt]

lemma degree_answer_vertex {n : ℕ} (g : InputGraph n) (v : Fin n) :
    LocalPush.degAnswer g.neighbors (v.val : ℤ)=((g.neighbors v).length : ℤ) := by
  simp [LocalPush.degAnswer,nodeOf_vertex]

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

-- Proof module: Solutions.HeapDetachCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma heapDetachCode_wellFormed : heapDetachCode.wellFormed := by
  simp [heapDetachCode,sequenceCode,coreCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapDrainCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma heapDrainPrefixCode_wellFormed : heapDrainPrefixCode.wellFormed := by
  simp [heapDrainPrefixCode,sequenceCode,coreCode,MachineCode.wellFormed,straightInstruction,
    admissible,scalarProgram,LocalPush.Admissible]

lemma heapDrainBodyCode_wellFormed : heapDrainBodyCode.wellFormed := by
  simp only [heapDrainBodyCode,sequenceCode,List.foldr,MachineCode.wellFormed]
  exact ⟨heapDrainPrefixCode_wellFormed,heapDetachCode_wellFormed,heapCarryCode_wellFormed,trivial⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeapDeletePreparation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma heapDeletePrepareCode_wellFormed : heapDeletePrepareCode.wellFormed := by
  simp [heapDeletePrepareCode,heapDeletePrefixRoutine,PointerRoutine.sequence,PointerRoutine.code,
    PointerOp.instruction,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma heapDeleteOccupiedCode_wellFormed : heapDeleteOccupiedCode.wellFormed :=
  ⟨heapDeletePrepareCode_wellFormed,heapDrainBodyCode_wellFormed⟩

lemma heapPopCode_wellFormed : heapPopCode.wellFormed :=
  ⟨heapMinScanCode_wellFormed,trivial,heapDeleteOccupiedCode_wellFormed⟩

end
end SparseQueue
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

-- Proof module: Solutions.HeapCleanCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section


lemma heapCleanEmptyCode_wellFormed : heapCleanEmptyCode.wellFormed := by
  simp [heapCleanEmptyCode,coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨0,by norm_num⟩

lemma heapCleanFoundCode_wellFormed : heapCleanFoundCode.wellFormed := by
  simp [heapCleanFoundCode,coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨0,by norm_num⟩

lemma heapCleanBodyCode_wellFormed (test : MachineCode) (h : test.wellFormed) :
    (heapCleanBodyCode test).wellFormed := by
  refine ⟨heapPopCode_wellFormed,?_,heapCleanEmptyCode_wellFormed,?_,h,trivial,heapCleanFoundCode_wellFormed⟩
  all_goals simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma heapCleanCode_wellFormed (test : MachineCode) (h : test.wellFormed) :
    (heapCleanCode test).wellFormed := by
  refine ⟨?_,heapCleanBodyCode_wellFormed test h⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨1,by norm_num⟩

lemma exteriorQueuedTestCode_wellFormed : exteriorQueuedTestCode.wellFormed := by
  refine ⟨?_,exteriorEligibilityCode_wellFormed,vertexFlagClearCode_wellFormed⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma exteriorQueueCleanCode_wellFormed : exteriorQueueCleanCode.wellFormed :=
  heapCleanCode_wellFormed _ exteriorQueuedTestCode_wellFormed

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndexMarkCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma indexMarkCode_wellFormed : indexMarkCode.wellFormed := by
  refine ⟨vertexFieldWriteCode_wellFormed 7 53,?_,?_,vertexFieldWriteCode_wellFormed 8 51⟩
  all_goals simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndexMarkBody

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma indexMarkBodyCode_wellFormed : indexMarkBodyCode.wellFormed := by
  simp [indexMarkBodyCode,MachineCode.wellFormed,indexMarkCode_wellFormed,coreCode,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.ExteriorCleanObject

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma exteriorCleanObjectCode_wellFormed : exteriorCleanObjectCode.wellFormed := by
  refine ⟨exteriorQueueCleanCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end SparseQueue
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

-- Proof module: Solutions.ExteriorPeekObject

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma exteriorPeekObjectCode_wellFormed : exteriorPeekObjectCode.wellFormed :=
  ⟨exteriorCleanObjectCode_wellFormed,trivial,exteriorQueueRefreshCode_wellFormed⟩

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

lemma levelVertexFlagClearCode_wellFormed (offset : ℕ) : (levelVertexFlagClearCode offset).wellFormed := by
  refine ⟨?_,vertexFlagClearCode_wellFormed⟩
  simp [levelVertexOffsetCode,levelVertexOffsetInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.PeekLevelExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma peekLevelCode_wellFormed : peekLevelCode.wellFormed := by
  refine ⟨?_,exteriorFrameContextCode_wellFormed,exteriorPeekObjectCode_wellFormed,?_⟩
  all_goals simp [peekLevelPrefixCode,peekLevelPrefixInstructions,linearCode,sequenceCode,coreCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PriorityAdvance

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma priorityAdvanceCode_wellFormed : priorityAdvanceCode.wellFormed := by
  simp [priorityAdvanceCode,priorityFoundCode,coreCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma priorityLoopCode_wellFormed : priorityLoopCode.wellFormed :=
  ⟨peekLevelCode_wellFormed,priorityAdvanceCode_wellFormed⟩
lemma priorityCode_wellFormed : priorityCode.wellFormed := by
  refine ⟨?_,priorityLoopCode_wellFormed⟩
  simp [priorityInitCode,priorityInitInstructions,linearCode,sequenceCode,coreCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FIFOTailLink

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma fifoTailLinkCode_wellFormed : fifoTailLinkCode.wellFormed := by
  simp [fifoTailLinkCode,linearCode,fifoTailLinkInstructions,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma fifoAppendBranchCode_wellFormed : fifoAppendBranchCode.wellFormed := by
  refine ⟨?_,fifoTailLinkCode_wellFormed⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FIFOAppendExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma fifoAppendCode_wellFormed : fifoAppendCode.wellFormed := by
  refine ⟨heapNodeAllocCode_wellFormed,fifoAppendBranchCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FIFOPopExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma fifoPopCode_wellFormed : fifoPopCode.wellFormed := by
  simp [fifoPopCode,fifoPopHeadCode,linearCode,fifoPopHeadInstructions,sequenceCode,
    coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end SparseQueue
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

-- Proof module: Solutions.BudgetCheckExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma budgetCheckCode_wellFormed (ancestorsOnly : Bool) : (budgetCheckCode ancestorsOnly).wellFormed := by
  refine ⟨?_,budgetScanCode_wellFormed⟩
  cases ancestorsOnly <;> simp [budgetCheckPrefixRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.HighCleanPreparation

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma highCleanPrepareCode_wellFormed : highCleanPrepareCode.wellFormed :=
  ⟨levelHeaderIntegerToCode_wellFormed _ _,levelContextCode_wellFormed,
    frameRankLoadCode_wellFormed,highQueueContextCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HighPeekExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma highPeekCode_wellFormed : highPeekCode.wellFormed :=
  ⟨highCleanPrepareCode_wellFormed,exteriorPeekObjectCode_wellFormed⟩

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
lemma levelHeaderIntegerRealCode_wellFormed (slot target : ℕ) : (levelHeaderIntegerRealCode slot target).wellFormed := by
  refine ⟨levelHeaderIntegerLoadCode_wellFormed slot,?_⟩
  simp [MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.CacheInsertPrelude

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma cacheInsertPreludeCode_wellFormed : cacheInsertPreludeCode.wellFormed := by
  refine ⟨levelContextCode_wellFormed,?_,by simp [vertexIntegerLoadCode,vertexAddressCode_wellFormed,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible],?_⟩ <;>
    simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheInsertExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma cacheInsertCode_wellFormed : cacheInsertCode.wellFormed :=
  ⟨cacheInsertPreludeCode_wellFormed,frameListInsertCode_wellFormed _ _ _ _⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameVertexIntegerRead

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameVertexIntegerReadCode_wellFormed (field : ℕ) :
    (frameVertexIntegerReadCode field).wellFormed := by
  refine ⟨levelContextCode_wellFormed,?_,?_⟩
  · simp [frameVertexReadOffsetRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
      MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  · simp [vertexIntegerLoadCode,vertexAddressCode_wellFormed,MachineCode.wellFormed,
      straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EnsureCacheExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma ensureCacheCode_wellFormed : ensureCacheCode.wellFormed :=
  ⟨frameVertexIntegerReadCode_wellFormed 4,cacheInsertCode_wellFormed,trivial⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HighBitClearRawExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma highBitClearCode_wellFormed : highBitClearCode.wellFormed := by
  refine ⟨frameVertexIntegerReadCode_wellFormed 4,?_,?_⟩ <;>
    simp [vertexRealStoreCode,vertexAddressCode_wellFormed,coreCode,MachineCode.wellFormed,
      straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨0,by norm_num⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HighCollectPointExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma highCollectPointCode_wellFormed : highCollectPointCode.wellFormed :=
  ⟨ensureCacheCode_wellFormed,highBitClearCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HighCleanExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma highCleanCode_wellFormed : highCleanCode.wellFormed :=
  ⟨highCleanPrepareCode_wellFormed,exteriorCleanObjectCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HighCollectLoopExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma highCollectBodyCode_wellFormed : highCollectBodyCode.wellFormed :=
  ⟨highCleanCode_wellFormed,trivial,highCollectPointCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HighCollectExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma highCollectCode_wellFormed : highCollectCode.wellFormed := by
  refine ⟨?_,highCollectBodyCode_wellFormed⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexListCopyBody

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexListCopyBodyCode_wellFormed : vertexListCopyBodyCode.wellFormed := by
  simp [vertexListCopyBodyCode,linearCode,vertexListCopyInstructions,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingArrayRefreshRead

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pendingArrayRefreshReadCode_wellFormed : pendingArrayRefreshReadCode.wellFormed := by
  simp [pendingArrayRefreshReadCode,pendingArrayRefreshReadInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.PendingArrayRefreshBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pendingArrayRefreshBodyCode_wellFormed : pendingArrayRefreshBodyCode.wellFormed := by
  refine ⟨pendingArrayRefreshReadCode_wellFormed,pendingVertexRefreshCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingCacheRestoreExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pendingCacheRestoreCode_wellFormed : pendingCacheRestoreCode.wellFormed :=
  ⟨levelHeaderIntegerToCode_wellFormed _ _,vertexEnumerationCode_wellFormed,pendingArrayRefreshCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LeafCachePreparationExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma leafCachePreparationCode_wellFormed : leafCachePreparationCode.wellFormed :=
  ⟨highCollectCode_wellFormed,pendingCacheRestoreCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LeafRHSArithmetic

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma leafRHSArithmeticCode_wellFormed : leafRHSArithmeticCode.wellFormed := by
  simp [leafRHSArithmeticCode,leafRHSArithmeticInstructions,linearCode,sequenceCode,
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

-- Proof module: Solutions.LeafRHSPointRawExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma leafRHSPointCode_wellFormed : leafRHSPointCode.wellFormed := by
  refine ⟨cacheInsertPreludeCode_wellFormed,?_,vertexRealReadToCode_wellFormed _,
    levelHeaderRealToCode_wellFormed _ _,leafRHSArithmeticCode_wellFormed,?_⟩
  · simp [frameVertexReadOffsetRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
      MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  · simp [vertexRealStoreCode,vertexAddressCode_wellFormed,coreCode,MachineCode.wellFormed,
      straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushOutputRead

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pushOutputReadCode_wellFormed : pushOutputReadCode.wellFormed := by
  simp [pushOutputReadCode,pushOutputReadInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LeafRHSBodyExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma leafRHSBodyCode_wellFormed : leafRHSBodyCode.wellFormed :=
  ⟨pushOutputReadCode_wellFormed,leafRHSPointCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LeafRHSExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma leafRHSCode_wellFormed : leafRHSCode.wellFormed :=
  ⟨levelHeaderIntegerToCode_wellFormed _ _,leafRHSBodyCode_wellFormed⟩

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

-- Proof module: Solutions.TripletAppendCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma tripletAppendCode_wellFormed : tripletAppendCode.wellFormed := by
  simp [tripletAppendCode,linearCode,tripletAppendInstructions,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolveBufferAllocation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma solveBufferRoutine_wellFormed : solveBufferRoutine.code.wellFormed := by
  simp [solveBufferRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndexLookupCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma indexLookupCode_wellFormed : indexLookupCode.wellFormed := by
  simp [indexLookupCode,indexLookupPresentCode,MachineCode.wellFormed,vertexFieldReadCode_wellFormed,
    coreCode,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OffDiagonalAppend

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma offDiagonalEntryCode_wellFormed : offDiagonalEntryCode.wellFormed :=
  ⟨indexLookupCode_wellFormed,trivial,tripletAppendCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NeighborAssemblyBody

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma neighborAssemblyBodyCode_wellFormed : neighborAssemblyBodyCode.wellFormed := by
  simp [neighborAssemblyBodyCode,MachineCode.wellFormed,offDiagonalEntryCode_wellFormed,coreCode,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DiagonalAppend

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma diagonalAppendCode_wellFormed : diagonalAppendCode.wellFormed := by
  simp [diagonalAppendCode,MachineCode.wellFormed,tripletAppendCode_wellFormed,coreCode,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrincipalRowAssembly

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma principalRowAssemblyCode_wellFormed : principalRowAssemblyCode.wellFormed := by
  simp [principalRowAssemblyCode,MachineCode.wellFormed,cacheReadCode_wellFormed,diagonalAppendCode_wellFormed,
    neighborAssemblyLoopCode,neighborAssemblyBodyCode_wellFormed,RealOperation.instruction,coreCode,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.DegreeSumCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma degreeSumCode_wellFormed : degreeSumCode.wellFormed := by
  simp [degreeSumCode,degreeSumInitRoutine,degreeSumLoopCode,degreeSumBodyCode,degreeSumTailRoutine,
    PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,MachineCode.wellFormed,
    vertexFieldReadCode_wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndexPreparation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma indexPreparationCode_wellFormed : indexPreparationCode.wellFormed := by
  refine ⟨?_,indexMarkBodyCode_wellFormed⟩
  simp [indexInitRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LocalSolvePreparation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma localSolvePreparationCode_wellFormed : localSolvePreparationCode.wellFormed := by
  refine ⟨degreeSumCode_wellFormed,indexPreparationCode_wellFormed,solveBufferRoutine_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrincipalAssemblyBody

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma principalAssemblyBodyCode_wellFormed : principalAssemblyBodyCode.wellFormed := by
  simp [principalAssemblyBodyCode,MachineCode.wellFormed,principalRowAssemblyCode_wellFormed,
    coreCode,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MatrixAssemblyInit

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma matrixAssemblyInitCode_wellFormed : matrixAssemblyInitCode.wellFormed := by
  simp [matrixAssemblyInitCode,linearCode,matrixAssemblyInitInstructions,RealOperation.instruction,
    sequenceCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨1,by norm_num⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrincipalMatrixAssembly

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma principalMatrixAssemblyCode_wellFormed : principalMatrixAssemblyCode.wellFormed :=
  ⟨matrixAssemblyInitCode_wellFormed,principalAssemblyBodyCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RightHandSideBody

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma rightHandSideBodyCode_wellFormed : rightHandSideBodyCode.wellFormed := by
  simp [rightHandSideBodyCode,vertexRealLoadCode,vertexAddressCode_wellFormed,
    rightHandSideTailCode,linearCode,rightHandSideTailInstructions,sequenceCode,
    MachineCode.wellFormed,coreCode,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RightHandSidePreparation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma rightHandSidePreparationCode_wellFormed : rightHandSidePreparationCode.wellFormed := by
  refine ⟨?_,rightHandSideBodyCode_wellFormed⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AssembledPrincipalSolve

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma assembledPrincipalSolveCode_wellFormed : assembledPrincipalSolveCode.wellFormed := by
  refine ⟨rightHandSidePreparationCode_wellFormed,?_⟩
  simp [MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨0,by norm_num⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrincipalSolvePipeline

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma principalSolvePipelineCode_wellFormed : principalSolvePipelineCode.wellFormed := by
  refine ⟨principalMatrixAssemblyCode_wellFormed,?_,assembledPrincipalSolveCode_wellFormed⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CachedPrincipalSolve

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma cachedPrincipalSolveCode_wellFormed : cachedPrincipalSolveCode.wellFormed :=
  ⟨localSolvePreparationCode_wellFormed,principalSolvePipelineCode_wellFormed⟩

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
lemma exteriorPushProgramCode_wellFormed : exteriorPushProgramCode.wellFormed :=
  ⟨exteriorNumericRawCode_wellFormed,pendingTouchedRefreshCode_wellFormed⟩

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

-- Proof module: Solutions.CachedJointSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma cachedJointSolveCode_wellFormed : cachedJointSolveCode.wellFormed :=
  ⟨cachedPrincipalSolveCode_wellFormed,jointSolveIterationCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ListJointSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma listJointSolveCode_wellFormed : listJointSolveCode.wellFormed :=
  ⟨vertexEnumerationCode_wellFormed,cachedJointSolveCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheJointSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma cacheJointSolvePreludeCode_wellFormed : cacheJointSolvePreludeCode.wellFormed := by
  refine ⟨levelHeaderIntegerToCode_wellFormed _ _,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma cacheJointSolveCode_wellFormed : cacheJointSolveCode.wellFormed :=
  ⟨cacheJointSolvePreludeCode_wellFormed,listJointSolveCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LeafCachedSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma leafCachedSolveCode_wellFormed : leafCachedSolveCode.wellFormed :=
  ⟨leafRHSCode_wellFormed,cacheJointSolveCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LeafJointSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma leafJointSolveCode_wellFormed : leafJointSolveCode.wellFormed :=
  ⟨leafCachePreparationCode_wellFormed,leafCachedSolveCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ChangePCExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma changePCCode_wellFormed (pc : NormalizePC) : (changePCCode pc).wellFormed := levelHeaderIntegerSetCode_wellFormed _ _

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LeafDecisionExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma leafDecisionCode_wellFormed : leafDecisionCode.wellFormed :=
  ⟨highPeekCode_wellFormed,changePCCode_wellFormed _,leafJointSolveCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.InitialEmptyExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma initialEmptyCode_wellFormed : initialEmptyCode.wellFormed :=
  ⟨levelHeaderIntegerToCode_wellFormed _ _,changePCCode_wellFormed _,changePCCode_wellFormed _⟩

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameResidualSumExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameResidualSumCode_wellFormed : frameResidualSumCode.wellFormed :=
  ⟨frameResidualSumPreludeCode_wellFormed,vertexResidualSumBodyCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeMaximumExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma episodeMaximumCode_wellFormed : episodeMaximumCode.wellFormed := by
  simp [episodeMaximumCode,coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameEpisodeParametersExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameEpisodeParametersCode_wellFormed : frameEpisodeParametersCode.wellFormed :=
  ⟨frameResidualSumCode_wellFormed,episodeBudgetScalarCode_wellFormed⟩

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameCacheClearExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameCacheClearCode_wellFormed : frameCacheClearCode.wellFormed :=
  ⟨frameCacheClearPreludeCode_wellFormed,clearVertexFieldBodyCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodePCExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma episodePCCode_wellFormed : episodePCCode.wellFormed :=
  ⟨levelHeaderIntegerToCode_wellFormed 10 181,levelHeaderIntegerSetCode_wellFormed _ _,levelHeaderIntegerSetCode_wellFormed _ _⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeHeaderExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma episodeHeaderCode_wellFormed : episodeHeaderCode.wellFormed :=
  ⟨levelHeaderRealFromCode_wellFormed 3 75,levelHeaderRealZeroCode_wellFormed 4,
    levelHeaderRealFromCode_wellFormed 5 76,levelHeaderIntegerSetsCode_wellFormed _,episodePCCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeRawExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma episodeRawCode_wellFormed : episodeRawCode.wellFormed :=
  ⟨frameEpisodeParametersCode_wellFormed,frameCacheClearCode_wellFormed,episodeHeaderCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EnumeratedEpisodePendingExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma enumeratedEpisodePendingCode_wellFormed : enumeratedEpisodePendingCode.wellFormed :=
  ⟨levelHeaderIntegerToCode_wellFormed 1 90,vertexEnumerationCode_wellFormed,episodeRawCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BeginEpisodeExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma beginEpisodeCode_wellFormed : beginEpisodeCode.wellFormed :=
  ⟨enumeratedEpisodePendingCode_wellFormed,pendingArrayRefreshCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ActiveJointSolvePrelude

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma activeJointSolvePreludeCode_wellFormed : activeJointSolvePreludeCode.wellFormed := by
  refine ⟨levelHeaderIntegerToCode_wellFormed _ _,levelContextCode_wellFormed,?_⟩
  simp [activeJointOffsetRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ActiveJointSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma activeJointSolveCode_wellFormed : activeJointSolveCode.wellFormed :=
  ⟨activeJointSolvePreludeCode_wellFormed,listJointSolveCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FullJointSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma fullJointSolveCode_wellFormed : fullJointSolveCode.wellFormed :=
  ⟨activeJointSolveCode_wellFormed,changePCCode_wellFormed _⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FullSolveDecisionExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma fullSolveDecisionCode_wellFormed : fullSolveDecisionCode.wellFormed :=
  ⟨levelHeaderIntegerToCode_wellFormed _ _,changePCCode_wellFormed _,fullJointSolveCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshVertexList

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma freshVertexListCode_wellFormed : freshVertexListCode.wellFormed :=
  ⟨pushOutputReadCode_wellFormed,freshVertexCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorPopulateCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma exteriorPopulateCode_wellFormed : exteriorPopulateCode.wellFormed :=
  ⟨pushOutputReadCode_wellFormed,exteriorQueueRefreshCode_wellFormed⟩

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshCallCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma freshCallSetupCode_wellFormed : freshCallSetupCode.wellFormed := by
  refine ⟨freshHeaderCode_wellFormed,?_,freshVertexListCode_wellFormed,?_,exteriorFrameContextCode_wellFormed⟩
  all_goals simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma freshCallCode_wellFormed : freshCallCode.wellFormed :=
  ⟨freshCallSetupCode_wellFormed,SparseQueue.exteriorPopulateCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshChildPreparation

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma freshChildPreparationCode_wellFormed : freshChildPreparationCode.wellFormed := by
  refine ⟨levelHeaderIntegerToCode_wellFormed 1 113,levelHeaderIntegerRealCode_wellFormed 14 12,
    levelHeaderRealToCode_wellFormed 5 13,levelHeaderIncrementCode_wellFormed 11,
    levelHeaderIntegerSetCode_wellFormed 0 5,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma freshChildRawCode_wellFormed : freshChildRawCode.wellFormed :=
  ⟨freshChildPreparationCode_wellFormed,freshCallCode_wellFormed⟩
lemma freshChildCode_wellFormed : freshChildCode.wellFormed := by
  refine ⟨freshChildRawCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.FrameCacheListClearPrelude

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameCacheListClearPreludeCode_wellFormed : frameCacheListClearPreludeCode.wellFormed := by
  refine ⟨levelHeaderIntegerToCode_wellFormed 4 94,?_⟩
  simp [frameCacheListClearPointerRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameCacheListClearExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameCacheListClearCode_wellFormed : frameCacheListClearCode.wellFormed :=
  ⟨frameCacheListClearPreludeCode_wellFormed,clearVertexFieldBodyCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FinishEpisodeRawExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma finishEpisodeCode_wellFormed : finishEpisodeCode.wellFormed :=
  ⟨frameCacheListClearCode_wellFormed,levelHeaderIntegerSetsCode_wellFormed _⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NeedFullArithmetic

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma needFullArithmeticCode_wellFormed : needFullArithmeticCode.wellFormed := by
  simp [needFullArithmeticCode,needFullArithmeticInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨1/2,by norm_num⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SetNeedFullExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma setNeedFullCode_wellFormed (need : Bool) : (setNeedFullCode need).wellFormed := levelHeaderIntegerSetCode_wellFormed _ _

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NeedFullDecisionExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma needFullPrepareCode_wellFormed : needFullPrepareCode.wellFormed :=
  ⟨levelHeaderRealToCode_wellFormed _ _,needFullArithmeticCode_wellFormed⟩
lemma needFullDecisionCode_wellFormed : needFullDecisionCode.wellFormed :=
  ⟨needFullPrepareCode_wellFormed,setNeedFullCode_wellFormed true,setNeedFullCode_wellFormed false⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ReturnPCPreparation

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma returnPCPrepareCode_wellFormed : returnPCPrepareCode.wellFormed := by
  refine ⟨levelHeaderRealToCode_wellFormed _ _,levelHeaderRealToCode_wellFormed _ _,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ReturnPCGuardExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma returnPCGuardCode_wellFormed : returnPCGuardCode.wellFormed := by
  refine ⟨⟨?_,changePCCode_wellFormed _,changePCCode_wellFormed _⟩,changePCCode_wellFormed _⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ReturnPCExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma returnPCCode_wellFormed : returnPCCode.wellFormed :=
  ⟨returnPCPrepareCode_wellFormed,returnPCGuardCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FinishRequestExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma finishRequestCode_wellFormed : finishRequestCode.wellFormed :=
  ⟨frameResidualSumCode_wellFormed,finishEpisodeCode_wellFormed,
    needFullDecisionCode_wellFormed,returnPCCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.InterruptEpisodeExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma interruptEpisodeCode_wellFormed (pc : NormalizePC) : (interruptEpisodeCode pc).wellFormed :=
  ⟨finishEpisodeCode_wellFormed,changePCCode_wellFormed pc⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RestartRequestExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma restartRequestCode_wellFormed : restartRequestCode.wellFormed :=
  ⟨setNeedFullCode_wellFormed _,changePCCode_wellFormed _⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DrainDecisionExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma drainDecisionCode_wellFormed (pc : NormalizePC) : (drainDecisionCode pc).wellFormed :=
  ⟨priorityCode_wellFormed,changePCCode_wellFormed _,exteriorPushProgramCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootSparseOutputPrelude

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma rootSparseOutputPreludeCode_wellFormed : rootSparseOutputPreludeCode.wellFormed := by
  simp [rootSparseOutputPreludeCode,rootSparseOutputPreludeInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨⟨3,by norm_num⟩,⟨8,by norm_num⟩⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushOutputScalar

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pushOutputScalarCode_wellFormed : pushOutputScalarCode.wellFormed := by
  simp [pushOutputScalarCode,pushOutputScalarInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨0,by norm_num⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PruneOutputScalar

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pruneOutputClipCode_wellFormed : pruneOutputClipCode.wellFormed := by
  simp [pruneOutputClipCode,coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨0,by norm_num⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrunedOutputBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma prunedOutputBodyCode_wellFormed : prunedOutputBodyCode.wellFormed := by
  refine ⟨pushOutputReadCode_wellFormed,?_,vertexFieldReadCode_wellFormed 0 60,pruneOutputClipCode_wellFormed,pushOutputScalarCode_wellFormed⟩
  simp [vertexRealLoadCode,vertexAddressCode_wellFormed,coreCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootSparseOutputExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma rootSparseOutputCode_wellFormed : rootSparseOutputCode.wellFormed :=
  ⟨rootSparseOutputPreludeCode_wellFormed,prunedOutputBodyCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootComponentPrelude

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma rootComponentPreludeCode_wellFormed : rootComponentPreludeRoutine.code.wellFormed := by
  simp [rootComponentPreludeRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolveAnswerOutputBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma solveAnswerOutputBodyCode_wellFormed : solveAnswerOutputBodyCode.wellFormed := by
  refine ⟨jointSolveIterationReadCode_wellFormed,vertexFieldReadCode_wellFormed 0 60,?_,pushOutputScalarCode_wellFormed,?_⟩ <;>
    simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolveAnswerOutputExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma solveAnswerOutputCode_wellFormed : solveAnswerOutputCode.wellFormed := by
  refine ⟨?_,solveAnswerOutputBodyCode_wellFormed⟩
  simp [solveAnswerOutputInitRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CachedSolveOutputExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma cachedSolveOutputCode_wellFormed : cachedSolveOutputCode.wellFormed :=
  ⟨cachedPrincipalSolveCode_wellFormed,solveAnswerOutputCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ListSolveOutputExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma listSolveOutputCode_wellFormed : listSolveOutputCode.wellFormed :=
  ⟨vertexEnumerationCode_wellFormed,cachedSolveOutputCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootComponentSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma rootComponentSolveCode_wellFormed : rootComponentSolveCode.wellFormed :=
  ⟨rootComponentPreludeCode_wellFormed,listSolveOutputCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveControllerCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma stopControllerCode_wellFormed : stopControllerCode.wellFormed := by
  simp [stopControllerCode,coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma controllerRootReturnCode_wellFormed : controllerRootReturnCode.wellFormed :=
  ⟨rootSparseOutputCode_wellFormed,stopControllerCode_wellFormed⟩
lemma controllerComponentCode_wellFormed : controllerComponentCode.wellFormed :=
  ⟨rootComponentSolveCode_wellFormed,stopControllerCode_wellFormed⟩
lemma controllerReturnCode_wellFormed : controllerReturnCode.wellFormed := by
  refine ⟨controllerRootReturnCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma controllerInitialCode_wellFormed : controllerInitialCode.wellFormed :=
  ⟨⟨priorityCode_wellFormed,initialEmptyCode_wellFormed,exteriorPushProgramCode_wellFormed,changePCCode_wellFormed _⟩,changePCCode_wellFormed _⟩
lemma controllerFullCode_wellFormed : controllerFullCode.wellFormed :=
  ⟨fullSolveDecisionCode_wellFormed,changePCCode_wellFormed _⟩
lemma controllerDepthCode_wellFormed : controllerDepthCode.wellFormed := by
  simp [controllerDepthCode,controllerDepthRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma controllerNormalizeCode_wellFormed : controllerNormalizeCode.wellFormed :=
  ⟨⟨controllerDepthCode_wellFormed,changePCCode_wellFormed _,freshChildCode_wellFormed⟩,changePCCode_wellFormed _⟩
lemma controllerLeafCode_wellFormed : controllerLeafCode.wellFormed :=
  ⟨⟨priorityCode_wellFormed,leafDecisionCode_wellFormed,exteriorPushProgramCode_wellFormed⟩,changePCCode_wellFormed _⟩
lemma controllerAfterChildCode_wellFormed : controllerAfterChildCode.wellFormed :=
  ⟨⟨drainDecisionCode_wellFormed _,interruptEpisodeCode_wellFormed _⟩,interruptEpisodeCode_wellFormed _⟩
lemma controllerFinishCode_wellFormed : controllerFinishCode.wellFormed :=
  ⟨⟨finishRequestCode_wellFormed,interruptEpisodeCode_wellFormed _⟩,interruptEpisodeCode_wellFormed _⟩
lemma controllerRestartCode_wellFormed : controllerRestartCode.wellFormed :=
  ⟨⟨priorityCode_wellFormed,restartRequestCode_wellFormed,exteriorPushProgramCode_wellFormed,changePCCode_wellFormed _⟩,changePCCode_wellFormed _⟩

lemma numberedDispatchCode_wellFormed (branches : List MachineCode) (start : ℕ)
    (h : ∀ b ∈ branches, b.wellFormed) : (numberedDispatchCode start branches).wellFormed := by
  induction branches generalizing start with
  | nil => trivial
  | cons b bs ih =>
    refine ⟨?_,h b (by simp),ih (start+1) (by intro c hc; exact h c (by simp [hc]))⟩
    simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma controllerOrdinaryCode_wellFormed : controllerOrdinaryCode.wellFormed := by
  refine ⟨budgetStatusCode_wellFormed,levelHeaderIntegerToCode_wellFormed _ _,numberedDispatchCode_wellFormed _ _ ?_⟩
  intro b hb
  simp only [controllerBranches,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | exact controllerInitialCode_wellFormed
    | exact beginEpisodeCode_wellFormed
    | exact controllerFullCode_wellFormed
    | exact controllerNormalizeCode_wellFormed
    | exact controllerLeafCode_wellFormed
    | exact controllerAfterChildCode_wellFormed
    | exact controllerFinishCode_wellFormed
    | exact controllerRestartCode_wellFormed
    | exact controllerReturnCode_wellFormed
lemma controllerBodyCode_wellFormed : controllerBodyCode.wellFormed := by
  refine ⟨?_,controllerOrdinaryCode_wellFormed,controllerComponentCode_wellFormed,controllerOrdinaryCode_wellFormed⟩
  simp [controllerComponentTestRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma recursiveControllerCode_wellFormed : recursiveControllerCode.wellFormed := controllerBodyCode_wellFormed

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.Subpolynomial

set_option autoImplicit false
open Filter Topology
namespace NearlyOptimalPPR.Computation

lemma sqrt_log_ratio_limit :
    Tendsto (fun t : ℝ => Real.sqrt ((Real.log 2 + t) * Real.log (Real.log 4 + t)) / t)
      atTop (𝓝 0) := by
  have hc (a : ℝ) : Tendsto (fun t : ℝ => a / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hr (a : ℝ) : Tendsto (fun t : ℝ => (a+t)/t) atTop (𝓝 1) := by
    have hh := (hc a).add_const 1
    have hh' : Tendsto (fun t : ℝ => a/t+1) atTop (𝓝 1) := by simpa using hh
    apply hh'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp [add_div, ht.ne']
  have hll : Tendsto (fun t : ℝ => Real.log (Real.log 4+t)/t) atTop (𝓝 0) := by
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-Real.log 4) 1 one_ne_zero).comp
      (show Tendsto (fun t : ℝ => Real.log 4 + t) atTop atTop from
        tendsto_const_nhds.add_atTop tendsto_id)
    convert! hh using 1
    ext t
    simp
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ((hr (Real.log 2)).mul hll)
  simp only [one_mul, Real.sqrt_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hprod : 0 ≤ (Real.log 2 + t) * Real.log (Real.log 4 + t) := by
    exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  simp only [Function.comp_apply]
  rw [show ((Real.log 2+t)/t) * (Real.log (Real.log 4+t)/t) =
    ((Real.log 2+t)*Real.log (Real.log 4+t))/(t^2) by ring]
  rw [Real.sqrt_div hprod, Real.sqrt_sq ht0.le]

theorem subpolynomial_envelope (C c : ℝ) (hC : 0 < C) : subpolynomialEnvelope C c := by
  intro η hη
  have hl : Tendsto (fun t : ℝ => Real.log C / t +
      c * (Real.sqrt ((Real.log 2+t)*Real.log (Real.log 4+t))/t)) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds.div_atTop tendsto_id (a := Real.log C)).add
      (sqrt_log_ratio_limit.const_mul c)
    simpa using hh
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hl.eventually_lt_const hη)
  let B := max T 1
  let ε₀ := Real.exp (-B)
  have hB : 1 ≤ B := le_max_right _ _
  have hε₀ : 0 < ε₀ := Real.exp_pos _
  have hε₀one : ε₀ ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    dsimp [B]
    linarith [le_max_right T 1]
  refine ⟨ε₀, hε₀, hε₀one, ?_⟩
  intro ε hε hsmall
  let t := Real.log (1/ε)
  have htlog : t = -Real.log ε := by
    dsimp [t]
    rw [Real.log_div one_ne_zero hε.ne', Real.log_one, zero_sub]
  have hlogε : Real.log ε ≤ -B := by
    have hh := Real.log_le_log hε hsmall
    simpa only [ε₀, Real.log_exp] using hh
  have htB : B ≤ t := by rw [htlog]; linarith
  have htpos : 0 < t := by linarith
  have htT : T ≤ t := (le_max_left _ _).trans htB
  have hbound := hT t htT
  have halg : Real.log C / t + c * (Real.sqrt ((Real.log 2+t)*Real.log (Real.log 4+t))/t) =
      (Real.log C + c * Real.sqrt ((Real.log 2+t)*Real.log (Real.log 4+t)))/t := by ring
  rw [halg] at hbound
  have hexponent : Real.log C + c * Real.sqrt ((Real.log 2+t)*Real.log (Real.log 4+t)) ≤ η*t :=
    ((div_lt_iff₀ htpos).mp hbound).le
  have h2 : Real.log (2/ε) = Real.log 2+t := by
    rw [Real.log_div (by norm_num) hε.ne', htlog]
    ring
  have h4 : Real.log (4/ε) = Real.log 4+t := by
    rw [Real.log_div (by norm_num) hε.ne', htlog]
    ring
  have hK : 0 < 1/ε := by positivity
  calc
    envelope C c ε = (1/ε) * Real.exp
        (Real.log C + c * Real.sqrt ((Real.log 2+t)*Real.log (Real.log 4+t))) := by
      rw [envelope, h2, h4, Real.exp_add, Real.exp_log hC]
      ring
    _ ≤ (1/ε) * Real.exp (η*t) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hK.le
    _ = (1/ε) ^ (1+η) := by
      rw [Real.rpow_add hK, Real.rpow_one, Real.rpow_def_of_pos hK]
      congr 2
      ring

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootInitializedExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma rootInitializedCode_wellFormed : rootInitializedCode.wellFormed := by
  refine ⟨freshCallCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootRegisterPreparation

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma rootRegisterPreparationCode_wellFormed : rootRegisterPreparationRoutine.code.wellFormed := by
  simp [rootRegisterPreparationRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootSeedRealExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma rootSeedRealCode_wellFormed : rootSeedRealCode.wellFormed := by
  simp [rootSeedRealCode,vertexRealStoreCode,MachineCode.wellFormed,coreCode,vertexAddressCode_wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨1,by norm_num⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootSeedMemoryExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma rootSeedMemoryCode_wellFormed : rootSeedMemoryCode.wellFormed :=
  ⟨degreeRecordStoreCode_wellFormed,rootSeedRealCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootSeedListExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma rootSeedListCode_wellFormed : rootSeedListCode.wellFormed := by
  refine ⟨?_,supportListPrependCode_wellFormed,?_⟩
  all_goals simp [rootSeedListPrefixRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootCallParameters

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma rootCallParameterCode_wellFormed : rootCallParameterCode.wellFormed := by
  simp [rootCallParameterCode,rootCallParameterInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨1,by norm_num⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootPreparationExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma rootPreparationCode_wellFormed : rootPreparationCode.wellFormed :=
  ⟨rootRegisterPreparationCode_wellFormed,rootSeedMemoryCode_wellFormed,rootSeedListCode_wellFormed,rootCallParameterCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootInitializationExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma rootInitializationCode_wellFormed : rootInitializationCode.wellFormed :=
  ⟨rootPreparationCode_wellFormed,rootInitializedCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootThresholdExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma rootThresholdCode_wellFormed : rootThresholdCode.wellFormed := by
  simp [rootThresholdCode,linearCode,rootThresholdInstructions,RealOperation.instruction,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨32,by norm_num⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PositiveThresholdSearch

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma thresholdBodyCode_wellFormed : thresholdBodyCode.wellFormed := by
  simp [thresholdBodyCode,RealOperation.instruction,coreCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma rootCapacitySearchCode_wellFormed : rootCapacitySearchCode.wellFormed := by
  simp [rootCapacitySearchCode,thresholdLoopCode,sequenceCode,coreCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible,thresholdBodyCode_wellFormed]
  exact ⟨8,by norm_num⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BinaryCapacityCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma binaryCapacity_spec (N : ℕ) : N < 2^(binaryCapacity N) := Nat.find_spec (binary_capacity_exists N)

lemma binaryCapacityCode_wellFormed : binaryCapacityCode.wellFormed := by
  simp [binaryCapacityCode,binaryCapacityInitRoutine,binaryCapacityLoopCode,binaryCapacityBodyRoutine,
    PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ParameterPreparation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma parameterPreparationCode_wellFormed : parameterPreparationCode.wellFormed := by
  refine ⟨depthSearchCode_wellFormed,rootThresholdCode_wellFormed,rootCapacitySearchCode_wellFormed,
    binaryCapacityCode_wellFormed,?_⟩
  simp [parameterTailRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ParameterHeader

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma parameterHeaderCode_wellFormed : parameterHeaderCode.wellFormed := by
  simp [parameterHeaderCode,linearCode,parameterHeaderInstructions,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AmplifiedQueueRank

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma amplified_queue_capacity (B N r : ℕ) (hN : N < 2^r) :
    (B*N)^B < 2^(amplifiedQueueRank B r) := by
  have hB : B ≤ 2^(binaryCapacity B) := (binaryCapacity_spec B).le
  have hProd : B*N ≤ 2^(r+binaryCapacity B) := by
    calc
      B*N ≤ 2^(binaryCapacity B)*2^r := Nat.mul_le_mul hB hN.le
      _ = _ := by rw [pow_add]; ac_rfl
  have hPower := Nat.pow_le_pow_left hProd B
  have hExp : (2^(r+binaryCapacity B))^B=2^(B*(r+binaryCapacity B)) := by rw [←pow_mul]; congr 1; exact Nat.mul_comm _ _
  rw [hExp] at hPower
  exact hPower.trans_lt (by unfold amplifiedQueueRank; rw [pow_succ]; have := Nat.two_pow_pos (B*(r+binaryCapacity B)); omega)

lemma PointerRoutine.sequence_wellFormed (ops : List PointerRoutine)
    (h : ∀ op ∈ ops, op.code.wellFormed) : (PointerRoutine.sequence ops).code.wellFormed := by
  induction ops with
  | nil => trivial
  | cons op ops ih =>
    exact ⟨h op (by simp),ih (by intro x hx; exact h x (by simp [hx]))⟩

lemma amplifiedQueueRankRoutine_wellFormed (B : ℕ) : (amplifiedQueueRankRoutine B).code.wellFormed := by
  apply PointerRoutine.sequence_wellFormed
  intro op hop
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_replicate] at hop
  rcases hop with (rfl|rfl|rfl)|⟨hB,rfl⟩ <;>
    simp [PointerRoutine.code,PointerOp.instruction,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexFIFOEnqueue

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma vertexFIFOEnqueueCode_wellFormed : vertexFIFOEnqueueCode.wellFormed := by
  refine ⟨?_,fifoAppendCode_wellFormed,?_,vertexFlagSetCode_wellFormed⟩
  all_goals simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushInitCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pushInitPrefixCode_wellFormed : pushInitPrefixCode.wellFormed := by
  simp [pushInitPrefixCode,linearCode,pushInitInstructions,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨1,by norm_num⟩

lemma pushInitCode_wellFormed : pushInitCode.wellFormed := by
  refine ⟨pushInitPrefixCode_wellFormed,?_,vertexFIFOEnqueueCode_wellFormed⟩
  simp [vertexRealStoreCode,vertexAddressCode_wellFormed,coreCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexFIFODequeue

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma vertexFIFODequeueCode_wellFormed : vertexFIFODequeueCode.wellFormed := by
  refine ⟨fifoPopCode_wellFormed,?_,vertexFlagClearCode_wellFormed⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushEligibilityExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pushEligibilityCode_wellFormed : pushEligibilityCode.wellFormed := by
  refine ⟨?_,exteriorEligibilityCode_wellFormed.2.2.1⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushScalarCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pushValueCalcCode_wellFormed : pushValueCalcCode.wellFormed := by
  simp [pushValueCalcCode,linearCode,pushValueCalcInstructions,RealOperation.instruction,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma pushResidualResetCode_wellFormed : pushResidualResetCode.wellFormed := by
  simp [pushResidualResetCode,linearCode,pushResidualResetInstructions,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨0,by norm_num⟩

lemma pushScalarUpdateCode_wellFormed : pushScalarUpdateCode.wellFormed := by
  refine ⟨?_,?_,pushValueCalcCode_wellFormed,vertexRealAddCode_wellFormed,pushResidualResetCode_wellFormed,?_⟩
  all_goals simp [vertexRealLoadCode,vertexRealStoreCode,vertexAddressCode_wellFormed,coreCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SupportInsertCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma supportInsertCode_wellFormed : supportInsertCode.wellFormed := by
  refine ⟨?_,supportListPrependCode_wellFormed,?_,vertexFlagSetCode_wellFormed⟩
  all_goals simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SupportEnsureExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma supportEnsureCode_wellFormed : supportEnsureCode.wellFormed := by
  refine ⟨?_,queuedFlagReadCode_wellFormed,supportInsertCode_wellFormed,trivial⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushNeighborsPreparation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pushNeighborsPrepareCode_wellFormed : pushNeighborsPrepareCode.wellFormed := by
  simp [pushNeighborsPrepareCode,pushNeighborsPrepareInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushResidualCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pushResidualAddCode_wellFormed : pushResidualAddCode.wellFormed := by
  refine ⟨?_,vertexRealAddCode_wellFormed⟩
  simp [pushResidualPrepareCode,pushResidualPrepareInstructions,linearCode,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FIFOEnsureCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma fifoEnsureCode_wellFormed : fifoEnsureCode.wellFormed := by
  refine ⟨?_,queuedFlagReadCode_wellFormed,vertexFIFOEnqueueCode_wellFormed,trivial⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushRefreshCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pushRefreshCode_wellFormed : pushRefreshCode.wellFormed :=
  ⟨pushEligibilityCode_wellFormed,trivial,fifoEnsureCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushNeighborUpdate

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pushNeighborUpdateCode_wellFormed : pushNeighborUpdateCode.wellFormed :=
  ⟨degreeRecordStoreCode_wellFormed,pushResidualAddCode_wellFormed,pushRefreshCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushNeighborLoopCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pushNeighborBodyCode_wellFormed : pushNeighborBodyCode.wellFormed := by
  refine ⟨?_,pushNeighborUpdateCode_wellFormed,?_⟩
  all_goals simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma pushNeighborLoopCode_wellFormed : pushNeighborLoopCode.wellFormed := pushNeighborBodyCode_wellFormed

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushPositiveCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pushPositiveCode_wellFormed : pushPositiveCode.wellFormed :=
  ⟨pushScalarUpdateCode_wellFormed,supportEnsureCode_wellFormed,pushNeighborsPrepareCode_wellFormed,pushNeighborLoopCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushIterationCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pushIterationCode_wellFormed : pushIterationCode.wellFormed :=
  ⟨vertexFIFODequeueCode_wellFormed,degreeRecordStoreCode_wellFormed,pushEligibilityCode_wellFormed,
    trivial,pushPositiveCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushWhileExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma pushWhileCode_wellFormed : pushWhileCode.wellFormed := pushIterationCode_wellFormed

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushOutputBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pushOutputBodyCode_wellFormed : pushOutputBodyCode.wellFormed := by
  refine ⟨pushOutputReadCode_wellFormed,?_,vertexFieldReadCode_wellFormed 0 60,pushOutputScalarCode_wellFormed⟩
  simp [vertexRealLoadCode,vertexAddressCode_wellFormed,coreCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma pushOutputCode_wellFormed : pushOutputCode.wellFormed := by
  refine ⟨?_,pushOutputBodyCode_wellFormed⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushCoreCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma pushCoreCode_wellFormed : pushCoreCode.wellFormed :=
  ⟨pushInitCode_wellFormed,pushWhileCode_wellFormed,pushOutputCode_wellFormed⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MachineHalting

set_option autoImplicit false
open Finset Matrix MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma machineStep_work_mono (m : SolveModel) (p : Program) {n : ℕ} (g : InputGraph n)
    (ω : ℕ → Bool) (st : MachineState) : st.work ≤ (machineStep m p g ω st).work := by
  classical
  unfold machineStep
  split
  · rfl
  · cases h : p[st.scalar.core.pc]? with
    | none => simp
    | some i =>
      cases i with
      | scalar i => simp
      | emit a b => simp
      | solve r => simp only [h]
                   split_ifs <;> simp_all

lemma machineRun_work_mono (m : SolveModel) (p : Program) {n : ℕ} (g : InputGraph n)
    (s : Fin n) (α ε : ℝ) (ω : ℕ → Bool) :
    Monotone (fun t => (machineRun m p g s α ε ω t).work) := by
  apply monotone_nat_of_le_succ
  intro t
  simpa only [machineRun,Function.iterate_succ_apply'] using
    machineStep_work_mono m p g ω (machineRun m p g s α ε ω t)

lemma machineRun_halted_stable (m : SolveModel) (p : Program) {n : ℕ} (g : InputGraph n)
    (s : Fin n) (α ε : ℝ) (ω : ℕ → Bool) (T t : ℕ) (hT : T ≤ t)
    (hh : (machineRun m p g s α ε ω T).scalar.halted=true) :
    machineRun m p g s α ε ω t=machineRun m p g s α ε ω T := by
  have aux : ∀ d, machineRun m p g s α ε ω (T+d)=machineRun m p g s α ε ω T := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [show T+(d+1)=(T+d)+1 by omega]
      simp only [machineRun,Function.iterate_succ_apply']
      change machineStep m p g ω (machineRun m p g s α ε ω (T+d))=_
      rw [ih]
      simp [machineStep,hh]
      rfl
  simpa [Nat.add_sub_of_le hT] using aux (t-T)

lemma executionWork_eq_halted (m : SolveModel) (p : Program) {n : ℕ} (g : InputGraph n)
    (s : Fin n) (α ε : ℝ) (ω : ℕ → Bool) (T : ℕ)
    (hh : (machineRun m p g s α ε ω T).scalar.halted=true) :
    executionWork m p g s α ε ω=(machineRun m p g s α ε ω T).work := by
  classical
  unfold executionWork
  rw [if_pos ⟨T,hh⟩]
  apply le_antisymm
  · apply iSup_le
    intro t
    rcases le_total t T with h|h
    · exact machineRun_work_mono m p g s α ε ω h
    · rw [machineRun_halted_stable m p g s α ε ω T t h hh]
  · exact le_iSup (fun t => (machineRun m p g s α ε ω t).work) T

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.WorkMeasurable

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma scalar_step_cursor (p : LocalPush.Program) {n : ℕ}
    (neighbors : Fin n → List (Fin n)) (ω : ℕ → Bool) (st : LocalPush.State) :
    (LocalPush.step p neighbors ω st).cursor ≤ st.cursor+1 := by
  unfold LocalPush.step
  split
  · exact Nat.le_succ _
  · split <;> first | exact Nat.le_succ _ | exact le_rfl

lemma scalar_step_tape (p : LocalPush.Program) {n : ℕ}
    (neighbors : Fin n → List (Fin n)) (ω ω' : ℕ → Bool) (st : LocalPush.State)
    (hω : ω st.cursor = ω' st.cursor) :
    LocalPush.step p neighbors ω st = LocalPush.step p neighbors ω' st := by
  unfold LocalPush.step
  split
  · rfl
  · split <;> first | rfl | simp only [hω]

lemma machine_step_cursor (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (ω : ℕ → Bool) (st : MachineState) :
    (machineStep m p g ω st).scalar.cursor ≤ st.scalar.cursor+1 := by
  classical
  unfold machineStep
  split
  · exact Nat.le_succ _
  · split
    · exact Nat.le_succ _
    · exact scalar_step_cursor _ _ _ _
    · exact Nat.le_succ _
    · dsimp only
      split <;> exact Nat.le_succ _

lemma machine_step_tape (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (ω ω' : ℕ → Bool) (st : MachineState)
    (hω : ω st.scalar.cursor = ω' st.scalar.cursor) :
    machineStep m p g ω st = machineStep m p g ω' st := by
  classical
  unfold machineStep
  split
  · rfl
  · split
    · rfl
    · rw [scalar_step_tape _ _ ω ω' st.scalar hω]
    · rfl
    · rfl

lemma machine_run_cursor (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ω : ℕ → Bool) (t : ℕ) :
    (machineRun m p g s α ε ω t).scalar.cursor ≤ t := by
  induction t with
  | zero => simp [machineRun, machineInit, LocalPush.initState]
  | succ t ih =>
    have hs := machine_step_cursor m p g ω (machineRun m p g s α ε ω t)
    simpa only [machineRun, Function.iterate_succ_apply'] using
      hs.trans (Nat.add_le_add_right ih 1)

lemma machine_run_prefix (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ω ω' : ℕ → Bool) (t : ℕ)
    (hω : ∀ i < t, ω i = ω' i) :
    machineRun m p g s α ε ω t = machineRun m p g s α ε ω' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hi := ih (fun i hi => hω i (Nat.lt_succ_of_lt hi))
    simp only [machineRun, Function.iterate_succ_apply']
    change machineStep m p g ω (machineRun m p g s α ε ω t) =
      machineStep m p g ω' (machineRun m p g s α ε ω' t)
    rw [← hi]
    apply machine_step_tape
    exact hω _ (Nat.lt_succ_of_le (machine_run_cursor m p g s α ε ω t))

def extendTape {t : ℕ} (a : Fin t → Bool) : ℕ → Bool :=
  fun i => if h : i < t then a ⟨i,h⟩ else false

lemma machine_run_observable_measurable {X : Type*} [MeasurableSpace X]
    (m : SolveModel) (p : Program) {n : ℕ} (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (t : ℕ) (f : MachineState → X) :
    Measurable (fun ω => f (machineRun m p g s α ε ω t)) := by
  let obs : (Fin t → Bool) → X := fun a => f (machineRun m p g s α ε (extendTape a) t)
  have hobs : Measurable obs := measurable_of_countable _
  have hres : Measurable (fun ω : ℕ → Bool => (fun i : Fin t => ω i.val)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  have he : (fun ω : ℕ → Bool => obs (fun i : Fin t => ω i.val)) =
      (fun ω => f (machineRun m p g s α ε ω t)) := by
    funext ω
    apply congrArg f
    apply machine_run_prefix
    intro i hi
    simp [extendTape,hi]
  rw [← he]
  exact hobs.comp hres

theorem execution_work_measurable (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (s : Fin n) (α ε : ℝ) :
    Measurable (executionWork m p g s α ε) := by
  classical
  have hhalt : MeasurableSet {ω : ℕ → Bool | ∃ t, (machineRun m p g s α ε ω t).scalar.halted = true} := by
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro t
    exact (measurableSet_singleton true).preimage
      (machine_run_observable_measurable m p g s α ε t (fun st => st.scalar.halted))
  have hsup : Measurable (fun ω : ℕ → Bool => ⨆ t, (machineRun m p g s α ε ω t).work) :=
    Measurable.iSup (fun t => machine_run_observable_measurable m p g s α ε t (fun st => st.work))
  exact Measurable.ite hhalt hsup measurable_const

lemma expected_work_le (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (s : Fin n) (α ε : ℝ) (B : ℝ≥0∞)
    (hB : ∀ ω, executionWork m p g s α ε ω ≤ B) :
    expectedWork m p g s α ε ≤ B := by
  haveI : IsProbabilityMeasure LocalPush.coinTape := by
    unfold LocalPush.coinTape
    infer_instance
  unfold expectedWork
  calc
    _ ≤ ∫⁻ _ : ℕ → Bool, B ∂LocalPush.coinTape := lintegral_mono hB
    _ = B := by simp

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StructuredProgram

set_option autoImplicit false
open Finset Matrix MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

namespace MachineCode

def program (a : MachineCode) : Program := a.compile 0 ++ [.scalar .halt]

lemma program_admissible (a : MachineCode) (h : a.wellFormed) : admissible a.program := by
  apply (admissible_append _ _).mpr
  refine ⟨compile_admissible 0 a h,?_⟩
  simp [admissible,scalarProgram,LocalPush.Admissible]

lemma program_codeAt (a : MachineCode) : codeAt a.program 0 (a.compile 0) :=
  codeAt_append_left _ _ _ _ (codeAt_self a.program)

lemma program_halt (a : MachineCode) : a.program[a.size]?=some (.scalar .halt) := by
  unfold program
  rw [←compile_length 0 a,List.getElem?_append_right (by omega)]
  simp

end MachineCode

lemma structured_program_run {m : SolveModel} {n : ℕ} {g : InputGraph n} {s : Fin n}
    {α ε : ℝ} {ω : ℕ → Bool} {a : MachineCode} {u : ℕ} {out : MachineState}
    (hw : a.wellFormed) (he : MachineEval m g ω a (machineInit s α ε) u out) :
    let st := machineRun m a.program g s α ε ω (u+1)
    st.scalar.halted=true ∧ st.output=out.output ∧ st.work=out.work+1 := by
  have hx := compiled_execution he hw a.program 0 a.program_codeAt
  simp only [Nat.zero_add] at hx
  change machineRun m a.program g s α ε ω u=pcSet out a.size at hx
  have hh : out.scalar.halted=false := he.halted hw
  have hlookup := a.program_halt
  simp only [machineRun,Function.iterate_succ_apply']
  change let st := machineStep m a.program g ω (machineRun m a.program g s α ε ω u)
    st.scalar.halted=true ∧ st.output=out.output ∧ st.work=out.work+1
  rw [hx]
  simp [machineStep,pcSet,hh,hlookup,LocalPush.step,scalarProgram,List.getElem?_map]

lemma structured_program_work {m : SolveModel} {n : ℕ} {g : InputGraph n} {s : Fin n}
    {α ε : ℝ} {ω : ℕ → Bool} {a : MachineCode} {u : ℕ} {out : MachineState}
    (hw : a.wellFormed) (he : MachineEval m g ω a (machineInit s α ε) u out) :
    executionWork m a.program g s α ε ω=out.work+1 := by
  have hh := structured_program_run hw he
  rw [executionWork_eq_halted m a.program g s α ε ω (u+1) hh.1,hh.2.2]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushProgramCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushProgramPrefixInstructions : List Instruction := [
  .scalar (.core (.pset 0 0)),.scalar (.integerLoad 40 0),.scalar (.deg 60 40)]
def pushProgramPrefixCode : MachineCode := linearCode pushProgramPrefixInstructions

def pushIsolateInstructions : List Instruction := [.scalar (.core (.const 10 1)),.emit 40 10]
def pushIsolateCode : MachineCode := linearCode pushIsolateInstructions

lemma pushProgramPrefixCode_wellFormed : pushProgramPrefixCode.wellFormed := by
  simp [pushProgramPrefixCode,linearCode,pushProgramPrefixInstructions,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma pushIsolateCode_wellFormed : pushIsolateCode.wellFormed := by
  simp [pushIsolateCode,linearCode,pushIsolateInstructions,sequenceCode,
    MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨⟨1,by norm_num⟩,⟨0,by norm_num⟩⟩
set_option maxHeartbeats 1600000 in
lemma push_program_prefix_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (s : Fin n)
    (hseed : st.scalar.integerMemory 0=(s.val : ℤ)) :
    ∃ out, MachineEval m g ω pushProgramPrefixCode st 3 out ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.core.ptrs 40=(s.val : ℤ) ∧ out.scalar.core.ptrs 60=((g.neighbors s).length : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+3 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω pushProgramPrefixInstructions
    (by simp [pushProgramPrefixInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,pushProgramPrefixInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hseed,degree_answer_vertex]

set_option maxHeartbeats 1200000 in
lemma push_isolate_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (s : Fin n) (h40 : st.scalar.core.ptrs 40=(s.val : ℤ)) :
    ∃ out, MachineEval m g ω pushIsolateCode st 2 out ∧
      out.output=st.output++[((s.val : ℤ),(1 : ℝ))] ∧ out.work=st.work+2 ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω pushIsolateInstructions
    (by simp [pushIsolateInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,hW,hH⟩
  simp [linearRun,pushIsolateInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,h40]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.UniformProgramCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def alphaChoiceInstructions : List Instruction := [
  .scalar (.core (.load 30 0)),.scalar (.core (.const 34 (1/2))),.scalar (.core (.sub 34 30 34))]
def alphaChoiceCode : MachineCode := linearCode alphaChoiceInstructions
lemma alphaChoiceCode_wellFormed : alphaChoiceCode.wellFormed := by
  simp [alphaChoiceCode,alphaChoiceInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
    straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
  exact ⟨1/2,by norm_num⟩

def recursiveProgramCode (B : ℕ) : MachineCode := .seq (recursivePreparationCode B) recursiveControllerCode
lemma recursivePreparationCode_wellFormed (B : ℕ) : (recursivePreparationCode B).wellFormed :=
  ⟨parameterPreparationCode_wellFormed,amplifiedQueueRankRoutine_wellFormed B,parameterHeaderCode_wellFormed,rootInitializationCode_wellFormed⟩
lemma recursiveProgramCode_wellFormed (B : ℕ) : (recursiveProgramCode B).wellFormed :=
  ⟨recursivePreparationCode_wellFormed B,recursiveControllerCode_wellFormed⟩

def uniformPPRCode (B : ℕ) : MachineCode := .seq pushProgramPrefixCode
  (.branchPointer 60 0 pushIsolateCode (.seq alphaChoiceCode (.branchReal 34 (recursiveProgramCode B) pushCoreCode)))
def uniformPPRProgram (B : ℕ) : Program := (uniformPPRCode B).program
lemma uniformPPRCode_wellFormed (B : ℕ) : (uniformPPRCode B).wellFormed :=
  ⟨pushProgramPrefixCode_wellFormed,pushIsolateCode_wellFormed,alphaChoiceCode_wellFormed,
    recursiveProgramCode_wellFormed B,pushCoreCode_wellFormed⟩
lemma uniformPPRProgram_admissible (B : ℕ) : admissible (uniformPPRProgram B) :=
  (uniformPPRCode B).program_admissible (uniformPPRCode_wellFormed B)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PushInputMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma push_input_memory_init {n : ℕ} (s : Fin n) (α ε : ℝ) : PushInputMemory s α ε (machineInit s α ε) := by
  constructor
  · simp [machineInit,LocalPush.initState]
  · simp [machineInit,LocalPush.initState]
  · simp [machineInit,LocalPush.initState]
  · intro z hz; simp [machineInit,LocalPush.initState,not_le_of_gt hz]
  · intro z hz; simp [machineInit,LocalPush.initState,not_le_of_gt hz]
  · rfl

lemma PushInputMemory.frame {n : ℕ} {s : Fin n} {α ε : ℝ} {st out : MachineState}
    (h : PushInputMemory s α ε st) (hI : out.scalar.integerMemory=st.scalar.integerMemory)
    (hR : out.scalar.core.mem=st.scalar.core.mem) (hO : out.output=st.output) : PushInputMemory s α ε out := by
  constructor
  · rw [hI]; exact h.seed
  · rw [hR]; exact h.alpha
  · rw [hR]; exact h.epsilon
  · rw [hI]; exact h.integerZero
  · rw [hR]; exact h.realZero
  · exact hO.trans h.output

lemma PushInputMemory.payUnit {n : ℕ} {s : Fin n} {α ε : ℝ} {st : MachineState}
    (h : PushInputMemory s α ε st) : PushInputMemory s α ε (NearlyOptimalPPR.Computation.payUnit st) :=
  h.frame rfl rfl rfl

lemma isolate_vector_acl {n : ℕ} (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hs : g.graph.degree s=0) (hε : 0 < ε) :
    ACL g.graph α ε s (LocalPush.e s) := by
  intro v
  have hp : ppr g.graph α s=LocalPush.e s := by simp [ppr,hs]
  rw [hp,sub_self,abs_zero]
  exact mul_nonneg hε.le (by unfold LocalPush.deg; positivity)

lemma isolate_output_vector {n : ℕ} (s : Fin n) : outputVector [((s.val : ℤ),(1 : ℝ))]=LocalPush.e s := by
  funext v
  simp [outputVector,LocalPush.e,Pi.single_apply,Int.natCast_inj,Fin.val_inj,eq_comm]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EnvelopeLogOverhead

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma loglog_le_envelope_sqrt (ε : ℝ) (he : 0<ε) (he1 : ε≤1) :
    Real.log (Real.log (4/ε)) ≤ Real.sqrt (Real.log (2/ε)*Real.log (Real.log (4/ε))) := by
  let K := 1/ε
  have hK : 1≤K := (le_div_iff₀ he).mpr (by simpa using he1)
  have hL : 0≤Real.log (2/ε) := Real.log_nonneg ((le_div_iff₀ he).mpr (by linarith))
  have hLog : 1<Real.log (4/ε) := by
    have hFour : (4 : ℝ) ≤ 4/ε := (le_div_iff₀ he).mpr (by nlinarith)
    exact lt_of_lt_of_le log_four_gt_one (Real.log_le_log (by norm_num) hFour)
  have hH : 0<Real.log (Real.log (4/ε)) := Real.log_pos hLog
  have h4 : Real.log (4/ε) ≤ 2/ε := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ)<2/ε)
    have hLog4 : Real.log (4/ε)=Real.log (2/ε)+Real.log 2 := by
      rw [←Real.log_mul (by positivity : (2/ε : ℝ)≠0) (by norm_num : (2 : ℝ)≠0)]
      congr 1
      ring
    rw [hLog4]
    have hTwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    linarith
  have hHL : Real.log (Real.log (4/ε)) ≤ Real.log (2/ε) :=
    Real.log_le_log (by linarith) h4
  apply (Real.le_sqrt (le_of_lt hH) (mul_nonneg hL hH.le)).mpr
  nlinarith [mul_nonneg hH.le (sub_nonneg.mpr hHL)]

lemma logarithmic_overhead_absorb (C c A ε : ℝ) (d : ℕ) (hC : 0≤C) (hA : 0≤A)
    (he : 0<ε) (he1 : ε≤1) :
    A*(1+Real.log (2/ε))^d*envelope C c ε ≤
      envelope (A*2^d*C) (c+d) ε := by
  let S := Real.sqrt (Real.log (2/ε)*Real.log (Real.log (4/ε)))
  have hFour : 1<Real.log (4/ε) := by
    exact lt_of_lt_of_le log_four_gt_one (Real.log_le_log (by norm_num) ((le_div_iff₀ he).mpr (by nlinarith)))
  have hL : 0≤Real.log (2/ε) := Real.log_nonneg ((le_div_iff₀ he).mpr (by linarith))
  have hHL := loglog_le_envelope_sqrt ε he he1
  have hBase : 1+Real.log (2/ε) ≤ 2*Real.log (4/ε) := by
    have hMono := Real.log_le_log (by positivity : (0 : ℝ)<2/ε) (show 2/ε ≤ 4/ε by apply div_le_div_of_nonneg_right (by norm_num) he.le)
    linarith
  have hExp : Real.log (4/ε) ≤ Real.exp S := by
    calc
      _ = Real.exp (Real.log (Real.log (4/ε))) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hHL
  have hPow : (1+Real.log (2/ε))^d ≤ (2*Real.exp S)^d := by
    exact pow_le_pow_left₀ (by linarith) (hBase.trans (mul_le_mul_of_nonneg_left hExp (by norm_num))) d
  calc
    _ ≤ A*(2*Real.exp S)^d*envelope C c ε := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPow hA)
      unfold envelope
      positivity
    _ = _ := by
      unfold envelope
      rw [mul_pow,←Real.exp_nat_mul]
      change A*(2^d*Real.exp ((d : ℝ)*S))*(C*(1/ε)*Real.exp (c*S))=
        A*2^d*C*(1/ε)*Real.exp ((c+(d : ℝ))*S)
      rw [add_mul,Real.exp_add]
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EnvelopePolynomial

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma envelope_coarse_power (C c ε : ℝ) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (he : 0 < ε) (he1 : ε ≤ 1) :
    envelope C c ε ≤ C*(1/ε)*(2/ε)^(2*c) := by
  have h2 : 1 < 2/ε := (lt_div_iff₀ he).mpr (by linarith)
  have h4 : 1 < 4/ε := (lt_div_iff₀ he).mpr (by linarith)
  have hL : 0 < Real.log (2/ε) := Real.log_pos h2
  have hlog4 : Real.log (4/ε) ≤ 2*Real.log (2/ε) := by
    have hε := Real.log_nonpos he.le he1
    rw [Real.log_div (by norm_num : (2 : ℝ)≠0) he.ne',
      Real.log_div (by norm_num : (4 : ℝ)≠0) he.ne']
    have hFour : Real.log (4 : ℝ)=2*Real.log 2 := by
      rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num
    rw [hFour]
    linarith
  have hH : Real.log (Real.log (4/ε)) ≤ 2*Real.log (2/ε) := by
    have h := Real.log_le_sub_one_of_pos (Real.log_pos h4)
    linarith
  have hS : Real.sqrt (Real.log (2/ε)*Real.log (Real.log (4/ε))) ≤ 2*Real.log (2/ε) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    have hp := mul_le_mul_of_nonneg_left hH hL.le
    nlinarith [sq_nonneg (Real.log (2/ε))]
  unfold envelope
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    Real.exp (c*Real.sqrt (Real.log (2/ε)*Real.log (Real.log (4/ε))))
        ≤ Real.exp ((2*c)*Real.log (2/ε)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = (2/ε)^(2*c) := by rw [Real.rpow_def_of_pos (by positivity)]; congr 1; ring

lemma envelope_polynomial_capacity (A C c : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hc : 0 ≤ c) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      A*envelope C c ε ≤ ((B : ℝ)/ε)^B := by
  obtain ⟨b,hb⟩ := exists_nat_gt (A*C+2*c+3)
  have hb2c : 2*c ≤ (b : ℝ) := by nlinarith [mul_nonneg hA hC]
  have hbAC : A*C ≤ ((b+1 : ℕ) : ℝ) := by push_cast; nlinarith
  have hb2 : 2 ≤ b+1 := by
    have hr : (2 : ℝ) ≤ (b : ℝ) := by nlinarith [mul_nonneg hA hC]
    have hn : 2 ≤ b := by exact_mod_cast hr
    omega
  refine ⟨b+1,hb2,?_⟩
  intro ε he he1
  let K := 1/ε
  let B := ((b+1 : ℕ) : ℝ)
  have hK : 1 ≤ K := (le_div_iff₀ he).mpr (by simpa using he1)
  have hB : 2 ≤ B := by dsimp only [B]; exact_mod_cast hb2
  have hBK : 1 ≤ B*K := by nlinarith
  have hExp : (2/ε)^(2*c) ≤ (B*K)^b := by
    calc
      (2/ε)^(2*c) ≤ (B*K)^(2*c) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        calc
          2/ε = 2*K := by dsimp only [K]; ring
          _ ≤ B*K := mul_le_mul_of_nonneg_right hB (by linarith)
      _ ≤ (B*K)^(b : ℝ) := Real.rpow_le_rpow_of_exponent_le hBK hb2c
      _ = (B*K)^b := Real.rpow_natCast _ _
  calc
    A*envelope C c ε ≤ A*(C*K*(2/ε)^(2*c)) :=
      mul_le_mul_of_nonneg_left (envelope_coarse_power C c ε hC hc he he1) hA
    _ = (A*C*K)*((2/ε)^(2*c)) := by ring
    _ ≤ (B*K)*(B*K)^b := mul_le_mul (by nlinarith) hExp (by positivity) (by positivity)
    _ = (B/ε)^(b+1) := by dsimp [K]; rw [pow_succ]; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EnvelopeCompilerOverhead

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma envelope_with_log_overhead (C c A : ℝ) (d : ℕ) (hC : 0<C) (hc : 0<c) (hA : 0<A) :
    ∃ C' c' : ℝ, 0<C' ∧ 0<c' ∧ subpolynomialEnvelope C' c' ∧
      ∀ ε : ℝ, 0<ε → ε≤1 → A*(1+Real.log (2/ε))^d*envelope C c ε ≤ envelope C' c' ε := by
  refine ⟨A*2^d*C,c+d,by positivity,by positivity,subpolynomial_envelope _ _ (by positivity),?_⟩
  intro ε he he1
  exact logarithmic_overhead_absorb C c A ε d hC.le hA.le he he1

lemma scaled_polynomial_capacity (B : ℕ) (N K L W : ℝ)
    (hN : 1≤N) (hK : 0≤K) (hKN : K≤N) (hL : 0≤L) (hLN : L≤N)
    (hW : W≤((B : ℝ)*K)^B) :
    L*W ≤ (((B+1 : ℕ) : ℝ)*N)^(B+1) := by
  let A := (((B+1 : ℕ) : ℝ)*N)
  have hN0 : 0≤N := by linarith
  have hB : (B : ℝ) ≤ ((B+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ B
  have hBase : (B : ℝ)*K ≤ A := by
    exact (mul_le_mul_of_nonneg_left hKN (Nat.cast_nonneg B)).trans (mul_le_mul_of_nonneg_right hB hN0)
  have hNA : N≤A := by
    dsimp only [A]
    have h1 : (1 : ℝ) ≤ ((B+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le B)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h1 hN0
  calc
    L*W ≤ L*((B : ℝ)*K)^B := mul_le_mul_of_nonneg_left hW hL
    _ ≤ A*A^B := mul_le_mul (hLN.trans hNA) (pow_le_pow_left₀ (by positivity) hBase B) (by positivity) (by linarith)
    _ = _ := by rw [pow_succ]; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerAccessibleBound

open NearlyOptimalPPR.Computation

set_option linter.all false
set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}



end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BalancedBlocks

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecurrenceAlgebra

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BalancedRecurrence

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AccessibleDepth

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable


end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DepthSearchEstimates

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BalancedDepthScalars

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AccessibleDepthRatio

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BalancedDepthLogs

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CoarseDepthLogs

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CoarseScalarWork

set_option autoImplicit false
set_option maxRecDepth 4096
namespace NearlyOptimalPPR.Computation

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AccessibleDepthComparison

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AccessibleEnvelope

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueueExterior

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameParameters

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DepthInvariant

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma compiler_analysis_top_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).top = if P then a.top else b.top := by split <;> rfl
@[simp] lemma compiler_analysis_top_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) : (debit st j w).top = st.top := rfl
@[simp] lemma compiler_analysis_top_changeFrame (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).top = st.top := rfl
@[simp] lemma compiler_analysis_top_changePC (st : RecursiveState n) (pc : NormalizePC) : (changePC st pc).top = st.top := rfl
@[simp] lemma compiler_analysis_top_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).top = st.top := rfl
@[simp] lemma compiler_analysis_top_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    (jointUpdate g α st h).top = st.top := rfl
@[simp] lemma compiler_analysis_top_finish (st : RecursiveState n) : (finishEpisode st).top = st.top := rfl
@[simp] lemma compiler_analysis_top_complete (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α : ℝ) (st : RecursiveState n) : (completeComponent m g s α st).top = st.top := rfl
@[simp] lemma compiler_analysis_top_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    (endCall g α st).top = if st.top = 0 then st.top else st.top-1 := by
  unfold endCall
  dsimp only
  split <;> rfl
@[simp] lemma compiler_analysis_top_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) : (exteriorPush g α st t v).top = st.top := by
  simp [exteriorPush]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CallIDs

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CallIDStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorStages

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}


end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootCharges

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootLedger

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootLedgerStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootInformation

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

@[simp] lemma compiler_analysis_information_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    (exteriorPush g α st t v).information = st.information := by
  simp [exteriorPush,changeFrame,refreshKeys,debit] <;> (try split_ifs) <;> rfl

@[simp] lemma compiler_analysis_information_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    (debit st j w).information = st.information := rfl
@[simp] lemma compiler_analysis_information_changeFrame (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) : (changeFrame st j f).information = st.information := rfl
@[simp] lemma compiler_analysis_information_PC (st : RecursiveState n) (pc : NormalizePC) :
    (changePC st pc).information = st.information := rfl
@[simp] lemma compiler_analysis_information_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    (jointUpdate g α st h).information = st.information := rfl
@[simp] lemma compiler_analysis_information_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).information = st.information := rfl
@[simp] lemma compiler_analysis_information_finish (st : RecursiveState n) : (finishEpisode st).information = st.information := rfl
@[simp] lemma compiler_analysis_information_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) : (completeComponent m g s α st).information = st.information := rfl
@[simp] lemma compiler_analysis_information_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    (endCall g α st).information = st.information := by unfold endCall; dsimp only; split <;> rfl
@[simp] lemma compiler_analysis_information_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).information = if P then a.information else b.information := by split <;> rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootWorkEnvelope

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.Subpolynomial

set_option autoImplicit false
open Filter Topology
namespace NearlyOptimalPPR.Computation

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootControl

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma compiler_analysis_frame_pc_debit (st : RecursiveState n) (j i : ℕ) (w : ℝ≥0∞) :
    ((debit st j w).frames i).pc = (st.frames i).pc := by simp [debit]
@[simp] lemma compiler_analysis_frame_pc_refresh (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).pc = (st.frames i).pc := by
  by_cases he : i ≤ st.top <;> simp [refreshKeys,he]
@[simp] lemma compiler_analysis_frame_pc_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (i : ℕ) :
    ((jointUpdate g α st h).frames i).pc = (st.frames i).pc := by
  by_cases he : i ≤ st.top <;> simp [jointUpdate,he]
@[simp] lemma compiler_analysis_frame_pc_ite (P : Prop) [Decidable P] (a b : RecursiveState n) (i : ℕ) :
    ((if P then a else b).frames i).pc = if P then (a.frames i).pc else (b.frames i).pc := by
  split <;> rfl
@[simp] lemma compiler_analysis_frame_pc_changeFrame (st : RecursiveState n) (j i : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) :
    ((changeFrame st j f).frames i).pc =
      if i = j then (f (st.frames j)).pc else (st.frames i).pc := by
  by_cases he : i = j <;> simp [changeFrame,he]

@[simp] lemma compiler_analysis_frame_pc_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (i : ℕ) :
    ((exteriorPush g α st t v).frames i).pc = (st.frames i).pc := by
  let f := st.frames t
  let d := LocalPush.deg g.graph v
  let h := min (f.residual v/(5*d)) (3*f.q/8-relative st t v)
  let base : RecursiveState n :=
    {st with
      x := Function.update st.x v (st.x v+h)
      stored := insert v st.stored
      frames := fun i => if i ≤ st.top then
        let fi := st.frames i
        {fi with
          residual := fun w => fi.residual w +
          (if w = v then if i < t then -d*h else if i = t then -5*d*h else 0 else 0) +
          (if w ∈ parentDomain st i ∧ g.graph.Adj w v then (1-α)*h else 0)
          W := fi.W + if fi.openBudget = true ∧ t ≤ i then (1-α)*d*h else 0}
        else st.frames i}
  let admitted := changeFrame base t (fun fi =>
    {fi with
      active := insert v fi.active
      residual := Function.update fi.residual v (fi.residual v+f.q*d/2)
      W := fi.W + if fi.openBudget then (t+3 : ℕ)*f.q*d/2 else 0})
  let child := if t < st.top then changeFrame admitted (t+1) (fun fc =>
    {fc with
      reference := Function.update fc.reference v (admitted.x v)
      residual := Function.update fc.residual v ((admitted.frames t).residual v)}) else admitted
  let final := if t = 0 then {child with boundaryEdges := st.boundaryEdges +
    (g.neighbors v).length - 2*((g.neighbors v).filter (fun w => w ∈ f.active)).length} else child
  have hb (i : ℕ) : (base.frames i).pc = (st.frames i).pc := by
    by_cases hi : i ≤ st.top <;> simp [base,hi]
  have ha (i : ℕ) : (admitted.frames i).pc = (st.frames i).pc := by
    simp only [admitted,compiler_analysis_frame_pc_changeFrame]
    split <;> simp_all [hb]
  have hc (i : ℕ) : (child.frames i).pc = (st.frames i).pc := by
    unfold child
    split
    · simp only [compiler_analysis_frame_pc_changeFrame]
      split <;> simp_all [ha]
    · exact ha i
  have hf (i : ℕ) : (final.frames i).pc = (st.frames i).pc := by
    unfold final
    split <;> exact hc i
  unfold exteriorPush
  simp only [compiler_analysis_frame_pc_debit,compiler_analysis_frame_pc_refresh]
  change ((if relative st t v+h = 3*f.q/8 then final else base).frames i).pc = _
  split
  · exact hf i
  · exact hb i

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.UniformFullCount

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OverheadMonotone

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

end NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable

-- Proof module: Solutions.CompilerSourceOutput
open NearlyOptimalPPR.Computation

set_option linter.all false
set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingPush

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrincipalSolves

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootIdentityControl

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootReturnProof

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RunInvariants

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NormalBranch

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.GraphCut

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ComponentOutput

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BoundaryInvariant

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma compiler_output_boundary_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    (debit st j w).boundaryEdges = st.boundaryEdges := rfl
@[simp] lemma compiler_output_boundary_changeFrame (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).boundaryEdges = st.boundaryEdges := rfl
@[simp] lemma compiler_output_boundary_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).boundaryEdges = st.boundaryEdges := rfl
@[simp] lemma compiler_output_active_debit (st : RecursiveState n) (j i : ℕ) (w : ℝ≥0∞) :
    ((debit st j w).frames i).active = (st.frames i).active := by
  classical
  simp [debit]
@[simp] lemma compiler_output_active_changeFrame (st : RecursiveState n) (j i : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) :
    ((changeFrame st j f).frames i).active =
      if i = j then (f (st.frames j)).active else (st.frames i).active := by
  classical
  by_cases h : i = j <;> simp [changeFrame,h]
@[simp] lemma compiler_output_active_refresh (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).active = (st.frames i).active := by
  classical
  by_cases h : i ≤ st.top <;> simp [refreshKeys,h]

@[simp] lemma compiler_output_boundary_id_debit (g : InputGraph n) (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    BoundaryIdentity g (debit st j w) ↔ BoundaryIdentity g st := by
  simp [BoundaryIdentity]

@[simp] lemma compiler_output_boundary_id_changeFrame (g : InputGraph n) (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hf : (f (st.frames j)).active = (st.frames j).active) :
    BoundaryIdentity g (changeFrame st j f) ↔ BoundaryIdentity g st := by
  by_cases he : (0 : ℕ) = j <;> simp_all (config := {maxSteps := 500000}) [BoundaryIdentity]

@[simp] lemma compiler_output_boundary_id_changePC (g : InputGraph n) (st : RecursiveState n) (pc : NormalizePC) :
    BoundaryIdentity g (changePC st pc) ↔ BoundaryIdentity g st :=
  compiler_output_boundary_id_changeFrame g st st.top _ rfl

@[simp] lemma compiler_output_boundary_id_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    BoundaryIdentity g (refreshKeys g st T) ↔ BoundaryIdentity g st := by simp [BoundaryIdentity]

@[simp] lemma compiler_output_boundary_id_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    BoundaryIdentity g (jointUpdate g α st h) ↔ BoundaryIdentity g st := by
  simp [BoundaryIdentity,jointUpdate]

@[simp] lemma compiler_output_boundary_id_finish (g : InputGraph n) (st : RecursiveState n) :
    BoundaryIdentity g (finishEpisode st) ↔ BoundaryIdentity g st := by
  by_cases he : (0 : ℕ) = st.top <;> simp [finishEpisode,BoundaryIdentity,he]

@[simp] lemma compiler_output_boundary_id_complete (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α : ℝ) (st : RecursiveState n) :
    BoundaryIdentity g (completeComponent m g s α st) ↔ BoundaryIdentity g st := Iff.rfl

@[simp] lemma compiler_output_boundary_id_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    BoundaryIdentity g (endCall g α st) ↔ BoundaryIdentity g st := by
  unfold endCall
  dsimp only
  split <;> rfl

@[simp] lemma compiler_output_active_ite (P : Prop) [Decidable P] (a b : RecursiveState n) (i : ℕ) :
    ((if P then a else b).frames i).active =
      if P then (a.frames i).active else (b.frames i).active := by split <;> rfl
@[simp] lemma compiler_output_boundary_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).boundaryEdges = if P then a.boundaryEdges else b.boundaryEdges := by split <;> rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootControl

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma compiler_output_frame_pc_debit (st : RecursiveState n) (j i : ℕ) (w : ℝ≥0∞) :
    ((debit st j w).frames i).pc = (st.frames i).pc := by simp [debit]
@[simp] lemma compiler_output_frame_pc_refresh (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).pc = (st.frames i).pc := by
  by_cases he : i ≤ st.top <;> simp [refreshKeys,he]
@[simp] lemma compiler_output_frame_pc_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (i : ℕ) :
    ((jointUpdate g α st h).frames i).pc = (st.frames i).pc := by
  by_cases he : i ≤ st.top <;> simp [jointUpdate,he]
@[simp] lemma compiler_output_frame_pc_ite (P : Prop) [Decidable P] (a b : RecursiveState n) (i : ℕ) :
    ((if P then a else b).frames i).pc = if P then (a.frames i).pc else (b.frames i).pc := by
  split <;> rfl
@[simp] lemma compiler_output_frame_pc_changeFrame (st : RecursiveState n) (j i : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) :
    ((changeFrame st j f).frames i).pc =
      if i = j then (f (st.frames j)).pc else (st.frames i).pc := by
  by_cases he : i = j <;> simp [changeFrame,he]

@[simp] lemma compiler_output_frame_pc_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (i : ℕ) :
    ((exteriorPush g α st t v).frames i).pc = (st.frames i).pc := by
  let f := st.frames t
  let d := LocalPush.deg g.graph v
  let h := min (f.residual v/(5*d)) (3*f.q/8-relative st t v)
  let base : RecursiveState n :=
    {st with
      x := Function.update st.x v (st.x v+h)
      stored := insert v st.stored
      frames := fun i => if i ≤ st.top then
        let fi := st.frames i
        {fi with
          residual := fun w => fi.residual w +
          (if w = v then if i < t then -d*h else if i = t then -5*d*h else 0 else 0) +
          (if w ∈ parentDomain st i ∧ g.graph.Adj w v then (1-α)*h else 0)
          W := fi.W + if fi.openBudget = true ∧ t ≤ i then (1-α)*d*h else 0}
        else st.frames i}
  let admitted := changeFrame base t (fun fi =>
    {fi with
      active := insert v fi.active
      residual := Function.update fi.residual v (fi.residual v+f.q*d/2)
      W := fi.W + if fi.openBudget then (t+3 : ℕ)*f.q*d/2 else 0})
  let child := if t < st.top then changeFrame admitted (t+1) (fun fc =>
    {fc with
      reference := Function.update fc.reference v (admitted.x v)
      residual := Function.update fc.residual v ((admitted.frames t).residual v)}) else admitted
  let final := if t = 0 then {child with boundaryEdges := st.boundaryEdges +
    (g.neighbors v).length - 2*((g.neighbors v).filter (fun w => w ∈ f.active)).length} else child
  have hb (i : ℕ) : (base.frames i).pc = (st.frames i).pc := by
    by_cases hi : i ≤ st.top <;> simp [base,hi]
  have ha (i : ℕ) : (admitted.frames i).pc = (st.frames i).pc := by
    simp only [admitted,compiler_output_frame_pc_changeFrame]
    split <;> simp_all [hb]
  have hc (i : ℕ) : (child.frames i).pc = (st.frames i).pc := by
    unfold child
    split
    · simp only [compiler_output_frame_pc_changeFrame]
      split <;> simp_all [ha]
    · exact ha i
  have hf (i : ℕ) : (final.frames i).pc = (st.frames i).pc := by
    unfold final
    split <;> exact hc i
  unfold exteriorPush
  simp only [compiler_output_frame_pc_debit,compiler_output_frame_pc_refresh]
  change ((if relative st t v+h = 3*f.q/8 then final else base).frames i).pc = _
  split
  · exact hf i
  · exact hb i

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.TerminationCases

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma compiler_output_done_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    (debit st j w).done = st.done := rfl
@[simp] lemma compiler_output_done_changeFrame (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) : (changeFrame st j f).done = st.done := rfl
@[simp] lemma compiler_output_done_changePC (st : RecursiveState n) (pc : NormalizePC) :
    (changePC st pc).done = st.done := rfl
@[simp] lemma compiler_output_done_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).done = st.done := rfl
@[simp] lemma compiler_output_done_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    (jointUpdate g α st h).done = st.done := rfl
@[simp] lemma compiler_output_done_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) : (exteriorPush g α st t v).done = st.done := by
  simp only [exteriorPush,compiler_output_done_debit,compiler_output_done_refresh,compiler_output_done_changeFrame]
  split_ifs <;> rfl
@[simp] lemma compiler_output_done_finish (st : RecursiveState n) : (finishEpisode st).done = st.done := rfl
@[simp] lemma compiler_output_done_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    (endCall g α st).done = (if st.top = 0 then true else st.done) := by
  unfold endCall
  dsimp only
  split <;> rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveOutput

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

end
end NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerOverheadCoefficients

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma compiler_overhead_parameters (ell length rank Q top : ℕ) (hTop : top≤ell) :
    let R := compilerOverheadBase ell length rank Q
    1000≤R ∧ 16*(ell+3)≤R ∧ top+1≤R ∧ length≤R ∧ rank≤R ∧ Q≤R ∧
      cleanBodyBound (16*(ell+3)) length rank+2≤R := by
  dsimp only
  unfold compilerOverheadBase
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerDepthLogBound

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_depth_log_bound (K : ℝ) (hK : 1≤K) :
    (accessibleDepth K : ℝ)≤2*(1+Real.log K) := by
  have hLog : 0≤Real.log K := Real.log_nonneg hK
  by_cases hZero : accessibleDepth K=0
  · rw [hZero]
    norm_num
    linarith
  · have hPos : 0<accessibleDepth K := by omega
    have hMin := accessibleDepth_log_lower K (by linarith) hPos
    have hBase : (2 : ℝ)≤((accessibleDepth K+1 : ℕ) : ℝ) := by exact_mod_cast (show 2≤accessibleDepth K+1 by omega)
    have hLogBase : (1/2 : ℝ)≤Real.log ((accessibleDepth K+1 : ℕ) : ℝ) :=
      log_two_bounds.1.trans (Real.log_le_log (by norm_num) hBase)
    have hMul := mul_le_mul_of_nonneg_left hLogBase (sq_nonneg (((accessibleDepth K+1 : ℕ) : ℝ)))
    push_cast at hMin hMul
    have hN : (0 : ℝ)≤(accessibleDepth K : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg ((accessibleDepth K : ℝ)-1)]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerParameterLogBounds

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_nat_log_bound (N : ℕ) (hN : 0<N) :
    ((Nat.log 2 N : ℕ) : ℝ)≤2*Real.log (N : ℝ) := by
  have hPow : (2 : ℝ)^(Nat.log 2 N)≤(N : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : N≠0)
  have hLog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ)<2) _) hPow
  rw [Real.log_pow] at hLog
  nlinarith [mul_nonneg (Nat.cast_nonneg (Nat.log 2 N)) (sub_nonneg.mpr log_two_bounds.1)]

lemma compiler_prepared_scale_bound (ε : ℝ) (he : 0<ε) (he1 : ε≤1) (N : ℕ)
    (hN : (N : ℝ)≤8/rootThreshold ε (accessibleDepth (1/ε))+1) :
    (N : ℝ)≤1281*(1/ε)^2 := by
  let K := 1/ε
  let ell := accessibleDepth K
  have hK : 1≤K := (le_div_iff₀ he).mpr (by simpa using he1)
  have hDepth := compiler_depth_log_bound K hK
  have hLog := Real.log_le_sub_one_of_pos (show 0<K by linarith)
  have hEll : (ell : ℝ)≤2*K := by dsimp only [ell]; linarith
  have hEll3 : (ell : ℝ)+3≤5*K := by linarith
  have hq : 8/rootThreshold ε ell+1=256*((ell : ℝ)+3)*K+1 := by
    unfold rootThreshold kappa
    simp only [Nat.sub_zero,Nat.cast_add,Nat.cast_ofNat]
    dsimp only [K]
    field_simp
    ring
  change (N : ℝ)≤8/rootThreshold ε ell+1 at hN
  rw [hq] at hN
  have hProd := mul_le_mul_of_nonneg_right hEll3 (show 0≤K by linarith)
  change (N : ℝ)≤1281*K^2
  nlinarith [sq_nonneg (K-1)]

lemma compiler_prepared_rank_bound (ε : ℝ) (he : 0<ε) (he1 : ε≤1) (N r : ℕ)
    (hN : 0<N) (hNup : (N : ℝ)≤8/rootThreshold ε (accessibleDepth (1/ε))+1)
    (hr : r≤Nat.log 2 N+1) : (r : ℝ)≤3000*(1+Real.log (1/ε)) := by
  let K := 1/ε
  have hK : 1≤K := (le_div_iff₀ he).mpr (by simpa using he1)
  have hNpos : (0 : ℝ)<N := by exact_mod_cast hN
  have hScale := compiler_prepared_scale_bound ε he he1 N hNup
  have hLogN := Real.log_le_log hNpos hScale
  rw [Real.log_mul (by norm_num : (1281 : ℝ)≠0) (by positivity : ((1/ε)^2 : ℝ)≠0),Real.log_pow] at hLogN
  have hConst := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<1281)
  have hBinary := compiler_nat_log_bound N hN
  have hr' : (r : ℝ)≤(Nat.log 2 N : ℝ)+1 := by exact_mod_cast hr
  have hNonnegative : 0≤Real.log (1/ε) := Real.log_nonneg hK
  nlinarith

lemma compiler_amplified_rank_bound (B r : ℕ) (L : ℝ) (hL : 1≤L) (hr : (r : ℝ)≤3000*L) :
    (amplifiedQueueRank B r : ℝ)≤((B*(3000+binaryCapacity B)+1 : ℕ) : ℝ)*L := by
  unfold amplifiedQueueRank
  push_cast
  have hConstant : (binaryCapacity B : ℝ)≤(binaryCapacity B : ℝ)*L := by nlinarith [show (0 : ℝ)≤(binaryCapacity B : ℝ) from Nat.cast_nonneg (binaryCapacity B)]
  have hMul := mul_le_mul_of_nonneg_left (add_le_add hr hConstant) (show (0 : ℝ)≤(B : ℝ) from Nat.cast_nonneg B)
  nlinarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerFixedCapacity

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_prepared_scale_lower (ε : ℝ) (he : 0<ε) (he1 : ε≤1) (ell N : ℕ)
    (hN : 8≤(N : ℝ)*rootThreshold ε ell) :
    1≤(N : ℝ) ∧ 1/ε≤(N : ℝ) ∧ ((8*(ell+1) : ℕ) : ℝ)≤(N : ℝ) := by
  let K := 1/ε
  have hK : 1≤K := (le_div_iff₀ he).mpr (by simpa using he1)
  have hq : 0<rootThreshold ε ell := by unfold rootThreshold kappa; positivity
  have hNlo : 8/rootThreshold ε ell≤(N : ℝ) := (div_le_iff₀ hq).mpr hN
  have hEq : 8/rootThreshold ε ell=256*((ell : ℝ)+3)*K := by
    unfold rootThreshold kappa
    simp only [Nat.sub_zero,Nat.cast_add,Nat.cast_ofNat]
    dsimp only [K]
    field_simp
    ring
  rw [hEq] at hNlo
  have hEll : (0 : ℝ)≤ell := Nat.cast_nonneg _
  have hCoeff : 1≤256*((ell : ℝ)+3) := by linarith
  have hKN : K≤(N : ℝ) := by nlinarith [mul_nonneg (sub_nonneg.mpr hCoeff) (show 0≤K by linarith)]
  refine ⟨hK.trans hKN,hKN,?_⟩
  push_cast
  nlinarith [mul_nonneg (show 0≤256*((ell : ℝ)+3) by positivity) (sub_nonneg.mpr hK)]

lemma compiler_fixed_capacity (C c : ℝ) (hC : 0≤C) (hc : 0≤c) :
    ∃ B : ℕ, 1≤B ∧ ∀ (ε : ℝ) (N : ℕ), 0<ε → ε≤1 →
      8≤(N : ℝ)*rootThreshold ε (accessibleDepth (1/ε)) →
      ((8*(accessibleDepth (1/ε)+1) : ℕ) : ℝ)*envelope C c ε≤(((B*N)^B : ℕ) : ℝ) := by
  obtain ⟨b,hb,hPoly⟩ := envelope_polynomial_capacity 1 C c (by norm_num) hC hc
  refine ⟨b+1,by omega,?_⟩
  intro ε N he he1 hN
  obtain ⟨hN1,hKN,hLN⟩ := compiler_prepared_scale_lower ε he he1 (accessibleDepth (1/ε)) N hN
  have hE : envelope C c ε≤((b : ℝ)*(1/ε))^b := by
    have h := hPoly ε he he1
    simpa only [one_mul,mul_one_div] using h
  have h := scaled_polynomial_capacity b (N : ℝ) (1/ε) ((8*(accessibleDepth (1/ε)+1) : ℕ) : ℝ)
    (envelope C c ε) hN1 (by positivity) hKN (by positivity) hLN hE
  simpa only [Nat.cast_pow,Nat.cast_mul] using h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveProgramSourceExecution

set_option autoImplicit false
set_option maxRecDepth 20000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def recursivePreparationBound (B ell N r : ℕ) (q : ℝ) : ℕ :=
  (12*(ell+2)^3+4*N+4*r+24)+(B+14)+
    (12*(16*(ell+3))+64+(⌈1/q⌉₊+2)*(4*ell+22)+10*(amplifiedQueueRank B r+1)+264+
      (21*(amplifiedQueueRank B r)+60*(16*(ell+3))+190))

set_option maxHeartbeats 24000000 in
lemma recursive_program_source_execution (m : SolveModel) :
    ∃ (B : ℕ) (C c : ℝ), 1 ≤ B ∧ 1 ≤ C ∧ 0<C ∧ 0<c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ω : ℕ → Bool)
        (st : MachineState), 0<α → α≤1/2 → 0<ε → ε≤1 → 0<g.graph.degree s →
        st.scalar.halted=false → PushInputMemory s α ε st → st.scalar.integerMemory 7=0 →
        let ell := accessibleDepth (1/ε)
        let q := rootThreshold ε ell
        ∃ (N r steps : ℕ) (out : MachineState), MachineEval m g ω (recursiveProgramCode B) st steps out ∧
          8 ≤ (N : ℝ)*q ∧ (N : ℝ) ≤ 8/q+1 ∧ 0<N ∧ N<2^r ∧ r ≤ Nat.log 2 N+1 ∧
          (∀ v : Fin n, 0 ≤ outputVector out.output v) ∧ ACL g.graph α ε s (outputVector out.output) ∧
          let rank := amplifiedQueueRank B r
          let length := rank+1
          let P := cleanBodyBound (16*(ell+3)) length rank+2
          let Q := 4*(16*(ell+3))+17
          let F := compilerOverheadFactor ell length rank Q
          out.work ≤ st.work+(recursivePreparationBound B ell N r q : ℝ≥0∞)+(P : ℝ≥0∞)+
            (F : ℝ≥0∞)*ENNReal.ofReal (envelope C c ε)+1 := by
  obtain ⟨C0,c,hC0,hc,hSub,hSource⟩ := compiler_accessible_recursive_running_time m
  let C := C0+1
  have hC1 : 1 ≤ C := by dsimp only [C]; linarith
  have hC : 0<C := by linarith
  obtain ⟨B,hB,hCapacity⟩ := compiler_fixed_capacity C c hC.le hc.le
  refine ⟨B,C,c,hB,hC1,hC,hc,?_⟩
  intro n g s α ε ω st ha ha1 he he1 hs hh input hBoundary
  dsimp only
  let ell := accessibleDepth (1/ε)
  let q := rootThreshold ε ell
  obtain ⟨N,r,u,a,pm,ea,hLower,hNup,hNpos,hPowPrepared,hr,hu,aMass,a150,a151,a53,aEpoch,aW,aQ,aO,aH⟩ :=
    recursive_preparation_exec m g ω B hB s α ε he he1 st hh input hBoundary
  let rank := amplifiedQueueRank B r
  let length := rank+1
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let Q := 4*(16*(ell+3))+17
  let F := compilerOverheadFactor ell length rank Q
  let runtime := ControllerMemory.ofLive pm (show (recursiveInit g s q ell []).done=false from rfl) a150 a151 aH aEpoch
  have hRuntime : runtime.mass ≤ 1 := by
    have heq : runtime.mass=pm.queueMass := ControllerMemory.ofLive_mass _ _ _ _ _ _
    exact heq.trans_le aMass
  have hSource' := hSource n g s α ε ha ha1 he he1 hs
  have hEnvelope : envelope C0 c ε ≤ envelope C c ε := by
    unfold envelope
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show C0 ≤ C by dsimp only [C]; linarith) (by positivity)) (by positivity)
  have hSourceBound := hSource'.1.trans (ENNReal.ofReal_le_ofReal hEnvelope)
  have hRealCapacity : ((8*(ell+1) : ℕ) : ℝ)*envelope C c ε ≤ (((B*N)^B : ℕ) : ℝ) := hCapacity ε N he he1 hLower
  have hWide : ((8*(ell+1) : ℕ) : ℝ≥0∞)*ENNReal.ofReal (envelope C c ε) ≤ (((B*N)^B : ℕ) : ℝ≥0∞) := by
    have h := ENNReal.ofReal_le_ofReal hRealCapacity
    simpa only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((8*(ell+1) : ℕ) : ℝ)),ENNReal.ofReal_natCast] using h
  obtain ⟨v,out,eb,hNonnegative,hACL,hWork⟩ := controller_source_run_certified m g ω s α ε (envelope C c ε) ell length ((B*N)^B) rank Q
    ⟨ha,ha1⟩ ⟨he,he1⟩ hs hSourceBound hWide hSource'.2 (by omega) (by omega)
    (amplified_queue_capacity B N r hPowPrepared) a runtime hRuntime
  have ex : MachineEval m g ω (recursiveProgramCode B) st (u+v) out := MachineEval.seq ea eb
  have hUnit : a.work ≤ st.work+(recursivePreparationBound B ell N r q : ℝ≥0∞) := by
    rw [aW]
    have hCast : (u : ℝ≥0∞) ≤ (recursivePreparationBound B ell N r q : ℝ≥0∞) :=
      (Nat.cast_le (α:=ℝ≥0∞)).mpr hu
    exact add_le_add le_rfl hCast
  refine ⟨N,r,u+v,out,ex,hLower,hNup,hNpos,hPowPrepared,hr,hNonnegative,hACL,?_⟩
  exact hWork.trans (add_le_add (add_le_add (add_le_add hUnit le_rfl) le_rfl) le_rfl)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerOverheadLogBound

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma compiler_overhead_log_bound (ell rank : ℕ) (L D : ℝ) (hL : 1 ≤ L) (hD : 1 ≤ D)
    (hEll : (ell : ℝ) ≤ 2*L) (hRank : (rank : ℝ) ≤ D*L) :
    (compilerOverheadFactor ell (rank+1) rank (4*(16*(ell+3))+17) : ℝ) ≤
      (4096*(21*D^2+46*D+2781)^2)*L^4 := by
  let w := 16*(ell+3)
  let Q := 4*w+17
  let P := cleanBodyBound w (rank+1) rank+2
  let R := compilerOverheadBase ell (rank+1) rank Q
  have hL0 : 0 ≤ L := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hSqL : L ≤ L^2 := by nlinarith
  have hw : (w : ℝ) ≤ 80*L := by dsimp only [w]; push_cast; nlinarith
  have hQ : (Q : ℝ) ≤ 337*L := by dsimp only [Q]; push_cast; nlinarith
  have hLength : ((rank+1 : ℕ) : ℝ) ≤ (D+1)*L := by push_cast; nlinarith
  have hRankSq : (rank : ℝ)^2 ≤ D^2*L^2 := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg rank) hRank 2
    simpa only [mul_pow] using h
  have hPFormula : (P : ℝ)=21*(rank : ℝ)^2+16*(rank : ℝ)+14*((rank+1 : ℕ) : ℝ)+16*(w : ℝ)+67 := by
    dsimp only [P,cleanBodyBound]
    push_cast
    ring
  have hLinear : 16*(rank : ℝ)+14*((rank+1 : ℕ) : ℝ)+16*(w : ℝ)+67 ≤ (30*D+1361)*L := by nlinarith
  have hP : (P : ℝ) ≤ (21*D^2+44*D+1361)*L^2 := by
    rw [hPFormula]
    have hLin2 := mul_le_mul_of_nonneg_left hSqL (show 0 ≤ 30*D+1361 by positivity)
    have hExtra := mul_nonneg hD0 (sq_nonneg L)
    nlinarith
  have hRFormula : (R : ℝ)=1000+(w : ℝ)+(ell : ℝ)+((rank+1 : ℕ) : ℝ)+(rank : ℝ)+(Q : ℝ)+(P : ℝ) := by
    dsimp only [R,compilerOverheadBase,w,Q,P]
    push_cast
    ring
  have hOuter : 1000+(w : ℝ)+(ell : ℝ)+((rank+1 : ℕ) : ℝ)+(rank : ℝ)+(Q : ℝ) ≤ (1420+2*D)*L := by nlinarith
  have hR : (R : ℝ) ≤ (21*D^2+46*D+2781)*L^2 := by
    rw [hRFormula]
    have hOuter2 := mul_le_mul_of_nonneg_left hSqL (show 0 ≤ 1420+2*D by positivity)
    nlinarith
  have hSquare := pow_le_pow_left₀ (Nat.cast_nonneg R) hR 2
  change (((4096*R^2 : ℕ) : ℝ)) ≤ _
  push_cast
  calc
    _ ≤ 4096*((21*D^2+46*D+2781)*L^2)^2 := mul_le_mul_of_nonneg_left hSquare (by norm_num)
    _ = _ := by ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerPreparationLogBound

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_prepared_nearlinear_scale (ε : ℝ) (he : 0<ε) (he1 : ε ≤ 1) (N : ℕ)
    (hN : (N : ℝ) ≤ 8/rootThreshold ε (accessibleDepth (1/ε))+1) :
    (N : ℝ) ≤ 1281*(1/ε)*(1+Real.log (1/ε)) := by
  let K := 1/ε
  let L := 1+Real.log K
  have hK : 1 ≤ K := (le_div_iff₀ he).mpr (by simpa using he1)
  have hL : 1 ≤ L := by dsimp only [L]; linarith [Real.log_nonneg hK]
  have hDepth := compiler_depth_log_bound K hK
  have hq : 8/rootThreshold ε (accessibleDepth K)+1 =
      256*((accessibleDepth K : ℝ)+3)*K+1 := by
    unfold rootThreshold kappa
    simp only [Nat.sub_zero,Nat.cast_add,Nat.cast_ofNat]
    dsimp only [K]
    field_simp
    ring
  change (N : ℝ) ≤ 8/rootThreshold ε (accessibleDepth K)+1 at hN
  rw [hq] at hN
  have hEll : (accessibleDepth K : ℝ)+3 ≤ 5*L := by dsimp only [L]; linarith
  have hProd := mul_le_mul_of_nonneg_right hEll (show 0 ≤ K by linarith)
  have hKL : 1 ≤ K*L := by nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hL)]
  change (N : ℝ) ≤ 1281*K*L
  nlinarith

lemma compiler_preparation_real_bound (B ell N r rank ceilq : ℕ) (K L D : ℝ)
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hD : 1 ≤ D)
    (hEll : (ell : ℝ) ≤ 2*L) (hN : (N : ℝ) ≤ 1281*K*L)
    (hr : (r : ℝ) ≤ 3000*L) (hRank : (rank : ℝ) ≤ D*L) (hCeil : ceilq ≤ N) :
    (((12*(ell+2)^3+4*N+4*r+24)+(B+14)+
      (12*(16*(ell+3))+64+(ceilq+2)*(4*ell+22)+10*(rank+1)+264+
        (21*rank+60*(16*(ell+3))+190)) : ℕ) : ℝ) ≤
      (100000+100*(B : ℝ)+100*D)*K*L^3 := by
  have hL0 : 0 ≤ L := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hKL : 1 ≤ K*L := by nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hL)]
  have hL2 : L ≤ L^2 := by nlinarith
  have hL3 : L^2 ≤ L^3 := by nlinarith [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hL)]
  have hU1 : 1 ≤ K*L^3 := by nlinarith
  have hUL : L ≤ K*L^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hK) (pow_nonneg hL0 3)]
  have hUKL : K*L ≤ K*L^3 := mul_le_mul_of_nonneg_left (hL2.trans hL3) hK0
  have hUKL2 : K*L^2 ≤ K*L^3 := mul_le_mul_of_nonneg_left hL3 hK0
  have hCube : ((ell : ℝ)+2)^3 ≤ 64*L^3 := by
    have ht : (ell : ℝ)+2 ≤ 4*L := by linarith
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (ell : ℝ)+2) ht 3
    nlinarith
  have hCeilR : (ceilq : ℝ) ≤ N := (Nat.cast_le (α:=ℝ)).mpr hCeil
  have hFirst : (ceilq : ℝ)+2 ≤ 1283*K*L := by nlinarith
  have hSecond : 4*(ell : ℝ)+22 ≤ 30*L := by linarith
  have hProduct : ((ceilq : ℝ)+2)*(4*(ell : ℝ)+22) ≤ 38490*K*L^2 := by
    have hh := mul_le_mul hFirst hSecond (by positivity) (by positivity : 0 ≤ 1283*K*L)
    nlinarith
  have hBU := mul_le_mul_of_nonneg_left hU1 (Nat.cast_nonneg B)
  have hDU := mul_le_mul_of_nonneg_left hUL hD0
  push_cast
  nlinarith

lemma compiler_preparation_log_bound (B : ℕ) (ε : ℝ) (he : 0<ε) (he1 : ε ≤ 1)
    (N r : ℕ) (hLower : 8 ≤ (N : ℝ)*rootThreshold ε (accessibleDepth (1/ε)))
    (hNup : (N : ℝ) ≤ 8/rootThreshold ε (accessibleDepth (1/ε))+1)
    (hNpos : 0<N) (hr : r ≤ Nat.log 2 N+1) :
    let D := ((B*(3000+binaryCapacity B)+1 : ℕ) : ℝ)
    (recursivePreparationBound B (accessibleDepth (1/ε)) N r
      (rootThreshold ε (accessibleDepth (1/ε))) : ℝ) ≤
      (100000+100*(B : ℝ)+100*D)*(1/ε)*(1+Real.log (1/ε))^3 := by
  dsimp only
  let K := 1/ε
  let L := 1+Real.log K
  let ell := accessibleDepth K
  have hK : 1 ≤ K := (le_div_iff₀ he).mpr (by simpa using he1)
  have hL : 1 ≤ L := by dsimp only [L]; linarith [Real.log_nonneg hK]
  have hq : 0<rootThreshold ε ell := by unfold rootThreshold kappa; positivity
  have hInv : 1/rootThreshold ε ell ≤ (N : ℝ) := by
    apply (div_le_iff₀ hq).mpr
    exact le_trans (by norm_num : (1 : ℝ) ≤ 8) hLower
  have hCeil : ⌈1/rootThreshold ε ell⌉₊ ≤ N := Nat.ceil_le.mpr hInv
  exact compiler_preparation_real_bound B ell N r (amplifiedQueueRank B r) _ K L _ hK hL
    (by norm_cast; omega) (compiler_depth_log_bound K hK)
    (compiler_prepared_nearlinear_scale ε he he1 N hNup)
    (compiler_prepared_rank_bound ε he he1 N r hNpos hNup hr)
    (compiler_amplified_rank_bound B r L hL
      (compiler_prepared_rank_bound ε he he1 N r hNpos hNup hr)) hCeil

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveProgramEnvelope

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma compiler_envelope_lower (C c ε : ℝ) (hC : 1 ≤ C) (hc : 0 ≤ c)
    (he : 0<ε) : 1/ε ≤ envelope C c ε := by
  have hExp : 1 ≤ Real.exp (c*Real.sqrt (Real.log (2/ε)*Real.log (Real.log (4/ε)))) :=
    Real.one_le_exp (mul_nonneg hc (Real.sqrt_nonneg _))
  unfold envelope
  have hFirst : 1/ε ≤ C*(1/ε) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (show 0 ≤ 1/ε by positivity)
  exact hFirst.trans (le_mul_of_one_le_right (by positivity) hExp)


lemma compiler_small_potential (ell rank : ℕ) :
    cleanBodyBound (16*(ell+3)) (rank+1) rank+2 ≤
      compilerOverheadFactor ell (rank+1) rank (4*(16*(ell+3))+17) := by
  let R := compilerOverheadBase ell (rank+1) rank (4*(16*(ell+3))+17)
  obtain ⟨hR,_,_,_,_,_,hP⟩ := compiler_overhead_parameters ell (rank+1) rank (4*(16*(ell+3))+17) ell le_rfl
  exact hP.trans (show R ≤ 4096*R^2 by nlinarith only [hR])


lemma compiler_total_real_bound (H P F K L E A Z : ℝ)
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hE : K ≤ E) (hA : 0 ≤ A) (hZ : 0 ≤ Z)
    (hH : H ≤ A*K*L^3) (hP : P ≤ F) (hF : F ≤ Z*L^4) :
    H+P+F*E+1 ≤ (A+2*Z+1)*L^4*E := by
  have hE0 : 0 ≤ E := by linarith
  have hPow : L^3 ≤ L^4 := by nlinarith [mul_nonneg (pow_nonneg (by linarith : 0 ≤ L) 3) (sub_nonneg.mpr hL)]
  have hL4 : 1 ≤ L^4 := one_le_pow₀ hL
  have hH' : H ≤ A*L^4*E := by
    calc
      _ ≤ A*K*L^3 := hH
      _ ≤ A*E*L^4 := mul_le_mul (mul_le_mul_of_nonneg_left hE hA) hPow (by positivity) (by positivity)
      _ = _ := by ring
  have hP' : P ≤ Z*L^4*E := (hP.trans hF).trans (le_mul_of_one_le_right (by positivity) (by linarith))
  have hF' : F*E ≤ Z*L^4*E := mul_le_mul_of_nonneg_right hF hE0
  have hOne : 1 ≤ L^4*E := by nlinarith [mul_nonneg (sub_nonneg.mpr hL4) (show 0 ≤ E by linarith)]
  nlinarith

lemma compiler_add_budget (w a b d e E : ℝ≥0∞) (h : a+b+d+e ≤ E) :
    w+a+b+d+e ≤ w+E := by
  calc
    _ = w+(a+b+d+e) := by ac_rfl
    _ ≤ w+E := add_le_add le_rfl h

set_option maxHeartbeats 250000 in
lemma recursive_program_envelope_execution (m : SolveModel) :
    ∃ (B : ℕ) (C c : ℝ), 1 ≤ B ∧ 0<C ∧ 0<c ∧ subpolynomialEnvelope C c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ω : ℕ → Bool)
        (st : MachineState), 0<α → α ≤ 1/2 → 0<ε → ε ≤ 1 → 0<g.graph.degree s →
        st.scalar.halted=false → PushInputMemory s α ε st → st.scalar.integerMemory 7=0 →
        ∃ steps out, MachineEval m g ω (recursiveProgramCode B) st steps out ∧
          (∀ v : Fin n, 0 ≤ outputVector out.output v) ∧ ACL g.graph α ε s (outputVector out.output) ∧
          out.work ≤ st.work+ENNReal.ofReal (envelope C c ε) := by
  obtain ⟨B,C,c,hB,hC1,hC,hc,hRun⟩ := recursive_program_source_execution m
  let D := ((B*(3000+binaryCapacity B)+1 : ℕ) : ℝ)
  let A := 100000+100*(B : ℝ)+100*D
  let Z := 4096*(21*D^2+46*D+2781)^2
  have hD : 1 ≤ D := by dsimp only [D]; norm_cast; omega
  have hA : 0<A := by dsimp only [A]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  obtain ⟨C',c',hC',hc',hSub,hAbsorb⟩ := envelope_with_log_overhead C c (A+2*Z+1) 4 hC hc (by positivity)
  refine ⟨B,C',c',hB,hC',hc',hSub,?_⟩
  intro n g s α ε ω st ha ha1 he he1 hs hh hi hb
  obtain ⟨N,r,u,out,ex,hLower,hNup,hNpos,hNpow,hr,hNN,hACL,hWork⟩ := hRun n g s α ε ω st ha ha1 he he1 hs hh hi hb
  let ell := accessibleDepth (1/ε)
  let rank := amplifiedQueueRank B r
  let L := 1+Real.log (1/ε)
  let K := 1/ε
  let E := envelope C c ε
  let H := recursivePreparationBound B ell N r (rootThreshold ε ell)
  let P := cleanBodyBound (16*(ell+3)) (rank+1) rank+2
  let F := compilerOverheadFactor ell (rank+1) rank (4*(16*(ell+3))+17)
  have hK : 1 ≤ K := (le_div_iff₀ he).mpr (by simpa using he1)
  have hL : 1 ≤ L := by dsimp only [L]; linarith [Real.log_nonneg hK]
  have hE := compiler_envelope_lower C c ε hC1 hc.le he
  have hH := compiler_preparation_log_bound B ε he he1 N r hLower hNup hNpos hr
  have hRank := compiler_amplified_rank_bound B r L hL (compiler_prepared_rank_bound ε he he1 N r hNpos hNup hr)
  have hF := compiler_overhead_log_bound ell rank L D hL hD (compiler_depth_log_bound K hK) hRank
  have hTotal := compiler_total_real_bound (H : ℝ) (P : ℝ) (F : ℝ) K L E A Z hK hL hE hA.le hZ hH
    ((Nat.cast_le (α:=ℝ)).mpr (compiler_small_potential ell rank)) hF
  have hLog : L ≤ 1+Real.log (2/ε) := by
    dsimp only [L]
    have hm := Real.log_le_log (by positivity : (0 : ℝ)<1/ε) (show 1/ε ≤ 2/ε by gcongr; norm_num)
    linarith
  have hFinal : (H : ℝ)+(P : ℝ)+(F : ℝ)*E+1 ≤ envelope C' c' ε :=
    hTotal.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hLog 4) (by positivity))
      (by dsimp only [E,envelope]; positivity)).trans (hAbsorb ε he he1))
  have hCast : (H : ℝ≥0∞)+(P : ℝ≥0∞)+(F : ℝ≥0∞)*ENNReal.ofReal E+1 ≤ ENNReal.ofReal (envelope C' c' ε) := by
    have ht := ENNReal.ofReal_le_ofReal hFinal
    have hE0 : 0 ≤ E := by dsimp only [E,envelope]; positivity
    have hFE : 0 ≤ (F : ℝ)*E := mul_nonneg (Nat.cast_nonneg F) hE0
    have hHP : 0 ≤ (H : ℝ)+(P : ℝ) := add_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg P)
    rw [ENNReal.ofReal_add (add_nonneg hHP hFE) (by norm_num : (0 : ℝ) ≤ 1),
      ENNReal.ofReal_add hHP hFE,ENNReal.ofReal_add (Nat.cast_nonneg H) (Nat.cast_nonneg P),
      ENNReal.ofReal_mul (Nat.cast_nonneg F)] at ht
    simpa only [ENNReal.ofReal_natCast,ENNReal.ofReal_one] using ht
  refine ⟨u,out,ex,hNN,hACL,?_⟩
  change out.work ≤ st.work+ENNReal.ofReal (envelope C' c' ε)
  change out.work ≤ st.work+(H : ℝ≥0∞)+(P : ℝ≥0∞)+(F : ℝ≥0∞)*ENNReal.ofReal E+1 at hWork
  exact hWork.trans (compiler_add_budget st.work _ _ _ _ _ hCast)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AlphaChoiceExecution

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 1500000 in
lemma alpha_choice_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) {s : Fin n} {α ε : ℝ}
    (input : PushInputMemory s α ε st) (h0 : st.scalar.core.ptrs 0=0) :
    ∃ out, MachineEval m g ω alphaChoiceCode st 3 out ∧
      PushInputMemory s α ε out ∧ out.scalar.core.regs 34=α-1/2 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.work=st.work+3 ∧
      out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω alphaChoiceInstructions
    (by simp [alphaChoiceInstructions,unitInstruction,straightInstruction]) st hh
  have hI : (linearRun m g ω alphaChoiceInstructions st).scalar.integerMemory=st.scalar.integerMemory := by
    simp [linearRun,alphaChoiceInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep]
  have hR : (linearRun m g ω alphaChoiceInstructions st).scalar.core.mem=st.scalar.core.mem := by
    simp [linearRun,alphaChoiceInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep]
  have hO : (linearRun m g ω alphaChoiceInstructions st).output=st.output := by
    simp [linearRun,alphaChoiceInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,
      scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep]
  refine ⟨_,ex,input.frame hI hR hO,?_,hI,hW,hH⟩
  simp [linearRun,alphaChoiceInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,h0,input.alpha]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.UniformCodeExecution

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma envelope_nonnegative (C c ε : ℝ) (hC : 0 ≤ C) (he : 0<ε) : 0 ≤ envelope C c ε := by
  unfold envelope
  positivity

lemma envelope_add_constant (C c A ε : ℝ) (hc : 0 ≤ c) (hA : 0 ≤ A)
    (he : 0<ε) (he1 : ε ≤ 1) : envelope C c ε+A ≤ envelope (C+A) c ε := by
  have hK : 1 ≤ 1/ε := (le_div_iff₀ he).mpr (by simpa using he1)
  have hExp : 1 ≤ Real.exp (c*Real.sqrt (Real.log (2/ε)*Real.log (Real.log (4/ε)))) :=
    Real.one_le_exp (mul_nonneg hc (Real.sqrt_nonneg _))
  have h := mul_le_mul_of_nonneg_left
    (show 1 ≤ (1/ε)*Real.exp (c*Real.sqrt (Real.log (2/ε)*Real.log (Real.log (4/ε)))) by
      nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hExp)]) hA
  unfold envelope
  nlinarith

lemma envelope_coefficient_mono (C D c ε : ℝ) (h : C ≤ D) (he : 0<ε) :
    envelope C c ε ≤ envelope D c ε := by
  unfold envelope
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity)) (by positivity)

lemma envelope_linear_lower (C c ε : ℝ) (hC : 0 ≤ C) (hc : 0 ≤ c) (he : 0<ε) :
    C/ε ≤ envelope C c ε := by
  have hExp : 1 ≤ Real.exp (c*Real.sqrt (Real.log (2/ε)*Real.log (Real.log (4/ε)))) :=
    Real.one_le_exp (mul_nonneg hc (Real.sqrt_nonneg _))
  unfold envelope
  simpa only [mul_one_div] using le_mul_of_one_le_right (show 0 ≤ C*(1/ε) by positivity) hExp

lemma uniform_code_execution (m : SolveModel) :
    ∃ (B : ℕ) (C c : ℝ), 0<C ∧ 0<c ∧ subpolynomialEnvelope C c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ω : ℕ → Bool),
        0<α → α<1 → 0<ε → ε ≤ 1 →
        ∃ steps out, MachineEval m g ω (uniformPPRCode B) (machineInit s α ε) steps out ∧
          ACL g.graph α ε s (outputVector out.output) ∧
          (∀ v : Fin n, 0 ≤ outputVector out.output v) ∧
          (g.graph.degree s=0 → outputVector out.output=LocalPush.e s) ∧
          out.work+1 ≤ ENNReal.ofReal (envelope C c ε) := by
  obtain ⟨B,Cr,c,hB,hCr,hc,hSub,hRec⟩ := recursive_program_envelope_execution m
  obtain ⟨Cp,hCp,hPush⟩ := push_core_bound m
  let C := Cr+2*Cp+20
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨B,C,c,hC,hc,subpolynomial_envelope C c hC,?_⟩
  intro n g s α ε ω ha ha1 he he1
  have hRecBound : envelope Cr c ε+10 ≤ envelope C c ε :=
    (envelope_add_constant Cr c 10 ε hc.le (by norm_num) he he1).trans
      (envelope_coefficient_mono _ _ _ _ (by change Cr+10 ≤ Cr+2*Cp+20; linarith only [hCp]) he)
  have hPushBound : 2*Cp/ε+11 ≤ envelope C c ε :=
    (add_le_add (envelope_linear_lower (2*Cp) c ε (by positivity) hc.le he) le_rfl).trans
      ((envelope_add_constant (2*Cp) c 11 ε hc.le (by norm_num) he he1).trans
        (envelope_coefficient_mono _ _ _ _ (by change 2*Cp+11 ≤ Cr+2*Cp+20; linarith only [hCr]) he))
  have hIsoBound : (7 : ℝ) ≤ envelope C c ε := by
    have h7 := envelope_linear_lower C c ε hC.le hc.le he
    have hDiv : C ≤ C/ε := (le_div_iff₀ he).mpr (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he1 hC.le)
    exact (show (7 : ℝ) ≤ C by dsimp only [C]; linarith only [hCr,hCp]).trans (hDiv.trans h7)
  let st := machineInit s α ε
  have hi : PushInputMemory s α ε st := push_input_memory_init s α ε
  obtain ⟨a,ea,a0,a40,a60,aI,aR,aW,aO,aH⟩ := push_program_prefix_exec m g ω st rfl s hi.seed
  have hai := hi.frame aI aR aO
  have hStW : st.work=0 := rfl
  by_cases hs : g.graph.degree s=0
  · have ha60 : a.scalar.core.ptrs 60=0 := by rw [a60,input_degree,hs]; rfl
    obtain ⟨out,eb,bO,bW,bH⟩ := push_isolate_exec m g ω (payUnit a) aH s a40
    have ec : MachineEval m g ω (.branchPointer 60 0 pushIsolateCode
        (.seq alphaChoiceCode (.branchReal 34 (recursiveProgramCode B) pushCoreCode))) a 3 out :=
      MachineEval.pointerLe aH (by rw [ha60,a0]) eb
    have ex : MachineEval m g ω (uniformPPRCode B) st 6 out := MachineEval.seq ea ec
    have ho : out.output=[((s.val : ℤ),(1 : ℝ))] := by simpa only [payUnit,pcSet,hai.output,List.nil_append] using bO
    have hv : outputVector out.output=LocalPush.e s := by rw [ho]; exact isolate_output_vector s
    refine ⟨6,out,ex,?_,?_,fun _ => hv,?_⟩
    · rw [hv]; exact isolate_vector_acl g s α ε hs he
    · intro v; rw [hv]; simp [LocalPush.e,Pi.single_apply]; split_ifs <;> norm_num
    · have hw : out.work+1=(7 : ℝ≥0∞) := by rw [bW,payUnit_work,aW,hStW]; norm_num
      rw [hw]
      simpa using ENNReal.ofReal_le_ofReal hIsoBound
  · have hs' : 0<g.graph.degree s := Nat.pos_of_ne_zero hs
    have hpos : ¬ a.scalar.core.ptrs 60 ≤ a.scalar.core.ptrs 0 := by
      rw [a60,a0,input_degree]; exact not_le.mpr (by exact_mod_cast hs')
    obtain ⟨b,eb,hbi,b34,bI,bW,bH⟩ := alpha_choice_exec m g ω (payUnit a) aH hai.payUnit a0
    by_cases hα : α ≤ 1/2
    · have hb7 : (payUnit b).scalar.integerMemory 7=0 := by
        change b.scalar.integerMemory 7=0
        rw [bI]
        change a.scalar.integerMemory 7=0
        rw [aI]
        simp [st,machineInit,LocalPush.initState]
      obtain ⟨u,out,er,hNN,hACL,hWork⟩ := hRec n g s α ε ω (payUnit b) ha hα he he1 hs' bH hbi.payUnit hb7
      have ec := MachineEval.realNonpos (b:=pushCoreCode) bH (by rw [b34]; linarith) er
      have ed := MachineEval.seq eb ec
      have ee := MachineEval.pointerGt (r:=60) (s:=0) (a:=pushIsolateCode) aH hpos ed
      have ex : MachineEval m g ω (uniformPPRCode B) st (3+(1+(3+(1+u))+1)) (payUnit out) := MachineEval.seq ea ee
      refine ⟨_,payUnit out,ex,hACL,hNN,fun h => (hs h).elim,?_⟩
      have hw : (payUnit out).work+1 ≤ ENNReal.ofReal (envelope Cr c ε)+10 := by
        change out.work+1+1 ≤ _
        have ht := add_le_add (add_le_add hWork (show (1 : ℝ≥0∞) ≤ 1 from le_rfl)) (show (1 : ℝ≥0∞) ≤ 1 from le_rfl)
        rw [payUnit_work,bW,payUnit_work,aW,hStW] at ht
        have heq : (0 : ℝ≥0∞)+3+1+3+1+ENNReal.ofReal (envelope Cr c ε)+1+1 =
            ENNReal.ofReal (envelope Cr c ε)+10 := by ring
        rw [heq] at ht
        exact ht
      exact hw.trans (by simpa only [ENNReal.ofReal_add (envelope_nonnegative Cr c ε hCr.le he) (by norm_num : (0 : ℝ) ≤ 10),ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hRecBound)
    · obtain ⟨u,out,er,hu,hACL,hNN,hWork,hHalt⟩ := hPush n g s α ε ω (payUnit b) ha ha1 he he1 hs' bH
        hbi.seed hbi.alpha hbi.epsilon hbi.integerZero hbi.realZero hbi.output
      have ec := MachineEval.realPos (a:=recursiveProgramCode B) bH (by rw [b34]; linarith) er
      have ed := MachineEval.seq eb ec
      have ee := MachineEval.pointerGt (r:=60) (s:=0) (a:=pushIsolateCode) aH hpos ed
      have ex : MachineEval m g ω (uniformPPRCode B) st (3+(1+(3+(1+u+1))+1)) (payUnit (payUnit out)) := MachineEval.seq ea ee
      have hReal : Cp/(α*ε) ≤ 2*Cp/ε := by
        apply (div_le_iff₀ (mul_pos ha he)).mpr
        calc
          Cp ≤ Cp*(2*α) := le_mul_of_one_le_right hCp.le (by linarith only [hα])
          _ = (2*Cp/ε)*(α*ε) := by field_simp <;> ring
      have hCore := hu.trans (ENNReal.ofReal_le_ofReal hReal)
      refine ⟨_,payUnit (payUnit out),ex,hACL,hNN,fun h => (hs h).elim,?_⟩
      have hw : (payUnit (payUnit out)).work+1=(u : ℝ≥0∞)+11 := by
        change out.work+1+1+1=_
        rw [hWork,payUnit_work,bW,payUnit_work,aW,hStW]
        ring
      rw [hw]
      exact (add_le_add hCore (show (11 : ℝ≥0∞) ≤ 11 from le_rfl)).trans (by
        simpa only [ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 2*Cp/ε) (by norm_num : (0 : ℝ) ≤ 11),ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hPushBound)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.UniformLocalAlgorithm

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma uniform_local_algorithm_proof (m : SolveModel) :
    ∃ (p : Program) (C c : ℝ), admissible p ∧ 0<C ∧ 0<c ∧
      (∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ),
        0<α → α<1 → 0<ε → ε ≤ 1 →
          successful m p g s α ε ∧ Measurable (executionWork m p g s α ε) ∧
          expectedWork m p g s α ε ≤ ENNReal.ofReal (envelope C c ε)) ∧
      subpolynomialEnvelope C c := by
  obtain ⟨B,C,c,hC,hc,hSub,hCode⟩ := uniform_code_execution m
  refine ⟨uniformPPRProgram B,C,c,uniformPPRProgram_admissible B,hC,hc,?_,hSub⟩
  intro n g s α ε ha ha1 he he1
  have hRun : ∀ ω, ∃ t, (machineRun m (uniformPPRProgram B) g s α ε ω t).scalar.halted=true ∧
      ACL g.graph α ε s (outputVector (machineRun m (uniformPPRProgram B) g s α ε ω t).output) ∧
      (∀ v : Fin n, 0 ≤ outputVector (machineRun m (uniformPPRProgram B) g s α ε ω t).output v) ∧
      (g.graph.degree s=0 → outputVector (machineRun m (uniformPPRProgram B) g s α ε ω t).output=LocalPush.e s) ∧
      executionWork m (uniformPPRProgram B) g s α ε ω ≤ ENNReal.ofReal (envelope C c ε) := by
    intro ω
    obtain ⟨u,out,ex,hACL,hNN,hIso,hWork⟩ := hCode n g s α ε ω ha ha1 he he1
    have hCompiled := structured_program_run (uniformPPRCode_wellFormed B) ex
    have hOutput : (machineRun m (uniformPPRProgram B) g s α ε ω (u+1)).output=out.output := hCompiled.2.1
    have hExec := structured_program_work (uniformPPRCode_wellFormed B) ex
    refine ⟨u+1,hCompiled.1,?_,?_,?_,?_⟩
    · rw [hOutput]; exact hACL
    · rw [hOutput]; exact hNN
    · rw [hOutput]; exact hIso
    · change executionWork m (uniformPPRCode B).program g s α ε ω ≤ _
      rw [hExec]
      exact hWork
  refine ⟨?_,execution_work_measurable m (uniformPPRProgram B) g s α ε,?_⟩
  · apply Filter.Eventually.of_forall
    intro ω
    obtain ⟨t,ht,hACL,hNN,hIso,hBound⟩ := hRun ω
    exact ⟨t,ht,hACL,hNN,hIso⟩
  · apply expected_work_le m (uniformPPRProgram B) g s α ε
    intro ω
    obtain ⟨t,ht,hACL,hNN,hIso,hBound⟩ := hRun ω
    exact hBound

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution (m : SolveModel) :
    ∃ (p : Program) (C c : ℝ), admissible p ∧ 0 < C ∧ 0 < c ∧
      (∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ),
        0 < α → α < 1 → 0 < ε → ε ≤ 1 →
          successful m p g s α ε ∧
          expectedWork m p g s α ε ≤ ENNReal.ofReal (envelope C c ε)) := by
  obtain ⟨p,C,c,hp,hC,hc,hRun,hSub⟩ := uniform_local_algorithm_proof m
  refine ⟨p,C,c,hp,hC,hc,?_⟩
  intro n g s α ε ha ha1 he he1
  obtain ⟨hSuccess,hMeas,hWork⟩ := hRun n g s α ε ha ha1 he he1
  exact ⟨hSuccess,hWork⟩
