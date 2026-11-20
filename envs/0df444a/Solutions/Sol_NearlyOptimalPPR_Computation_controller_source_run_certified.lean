-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.controller_source_run_certified
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:31:00.450398+00:00
-- url     : https://prove2.me/submissions/7ddab5dd-94b4-410e-9125-f7055f7ec25b

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
import Theorems.Thm_NearlyOptimalPPR_Computation_controller_source_step_exec
import Theorems.Thm_NearlyOptimalPPR_Computation_normalization_composes
import Theorems.Thm_NearlyOptimalPPR_Computation_push_correctness_work
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_level_work
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_residual_error
set_option linter.all false
-- Proof module: Solutions.CompilerNatBudget

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def compilerNatBudget (x : ℝ≥0∞) : ℕ := ⌊x.toReal⌋₊

lemma compiler_nat_budget_iff (x : ℝ≥0∞) (hx : x≠⊤) (k : ℕ) :
    k≤compilerNatBudget x ↔ (k : ℝ≥0∞)≤x := by
  constructor
  · intro h
    apply (ENNReal.toReal_le_toReal (by simp) hx).mp
    simpa only [ENNReal.toReal_natCast] using
      (show (k : ℝ)≤(compilerNatBudget x : ℝ) from by exact_mod_cast h).trans (Nat.floor_le ENNReal.toReal_nonneg)
  · intro h
    exact Nat.le_floor (by simpa only [ENNReal.toReal_natCast] using ENNReal.toReal_mono hx h)

lemma compiler_nat_budget_cast_le (x : ℝ≥0∞) (hx : x≠⊤) : (compilerNatBudget x : ℝ≥0∞)≤x :=
  (compiler_nat_budget_iff x hx _).mp le_rfl

lemma compiler_nat_budget_add (x z : ℝ≥0∞) (hx : x≠⊤) (hz : z≠⊤) (d : ℕ) (hd : (d : ℝ≥0∞)≤z) :
    compilerNatBudget x+d≤compilerNatBudget (x+z) := by
  apply (compiler_nat_budget_iff (x+z) (ENNReal.add_ne_top.mpr ⟨hx,hz⟩) _).mpr
  simpa only [Nat.cast_add] using add_le_add (compiler_nat_budget_cast_le x hx) hd

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerExteriorSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_exterior_stages {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v)) (3*(st.frames t).q/8-relative st t v)
    let base := rawExterior g α st t v δ
    let u := if relative st t v+δ = 3*(st.frames t).q/8 then admitStage g base t v else base
    exteriorPush g α st t v = debit (refreshKeys g u (insert v (g.neighbors v).toFinset)) t
      (32*(st.top+1)*((g.neighbors v).length+1)*keyCost (refreshKeys g u (insert v (g.neighbors v).toFinset)) : ℕ) := by
  classical
  dsimp only
  unfold exteriorPush admitStage
  by_cases ht : t ≤ st.top <;> simp only [rawExterior,ht,ite_true,ite_false] <;> rfl

end
end NearlyOptimalPPR.Computation

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

lemma compiler_cost_work_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    (exteriorPush g α st t v).work=st.work+
      (32*(st.top+1)*((g.neighbors v).length+1)*keyCost (exteriorPush g α st t v) : ℕ) := by
  rw [compiler_exterior_stages]
  simp only [compiler_cost_work_debit,compiler_cost_keyCost_debit,compiler_cost_work_refresh,compiler_cost_work_ite,compiler_cost_work_admit,compiler_cost_work_raw,ite_self]

@[simp] lemma compiler_cost_work_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) :
    (completeComponent m g s α st).work=st.work+jointCost m g st (st.frames 0).active+((st.frames 0).active.card+1 : ℕ) := by
  simp [completeComponent,debit,add_assoc]

lemma compiler_cost_work_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    (endCall g α st).work=st.work+if st.top=0 then (8*(st.frames 0).active.card+1 : ℕ) else 0 := by
  unfold endCall
  dsimp only
  split <;> simp [debit]

set_option maxHeartbeats 2000000 in
lemma compiler_cost_recursiveStep_work_debit (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) :
    (recursiveStep m g s α ℓ schedule st).work=st.work+(stepDebit m g α ℓ st).2 := by
  cases hp : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,stepDebit,hpc,hp,compiler_cost_work_end,compiler_cost_work_exterior] <;>
      (try split_ifs) <;> simp_all [debit,add_assoc,Nat.cast_add,Nat.cast_mul] <;> ring
  | some p =>
    obtain ⟨t,v⟩ := p
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,stepDebit,hpc,hp,compiler_cost_work_end,compiler_cost_work_exterior] <;>
      (try split_ifs) <;> simp_all [debit,add_assoc,Nat.cast_add,Nat.cast_mul] <;> ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PendingPush

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation

lemma pending_push_member {n : ℕ} (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hp : pendingPush st = some (t,v)) : t ≤ st.top ∧ v ∈ (st.frames t).exterior := by
  classical
  unfold pendingPush at hp
  dsimp only at hp
  split at hp
  · rename_i hlevel
    split at hp
    · rename_i hrow
      have hh := Option.some.inj hp
      have ht := congrArg Prod.fst hh
      have hv := congrArg Prod.snd hh
      dsimp only at ht hv
      rw [← ht, ← hv]
      refine ⟨?_, Finset.min'_mem _ hrow⟩
      have hl := Finset.min'_mem _ hlevel
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hl).1)
    · simp at hp
  · simp at hp

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerExteriorStatic

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_admit_stored {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    (admitStage g st t v).stored=st.stored := by
  unfold admitStage
  split_ifs <;> rfl

lemma compiler_exterior_stored {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    (exteriorPush g α st t v).stored=insert v st.stored := by
  classical
  rw [compiler_exterior_stages]
  change RecursiveState.stored ((if _ then _ else _) : RecursiveState n)=_
  split_ifs
  · rw [compiler_admit_stored]
    rfl
  · rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StructuredMachine

set_option autoImplicit false
open Finset Matrix MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


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

-- Proof module: Solutions.ScalarCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


@[simp] lemma pcSet_payUnit_zero (st : MachineState) : pcSet (payUnit st) 0=payUnit st := rfl

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
lemma compiler_public_region_run (m : SolveModel) {n : ℕ} (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    RegionInvariant (recursiveRun m g s α q ell schedule t) :=
  (recursive_residual_identities m n g s α q ell schedule t).1
end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma compiler_source_neighbor_count (g : InputGraph n) (v : Fin n) (H : Finset (Fin n)) :
    (((g.neighbors v).filter (fun u => u ∈ H)).length : ℤ) =
      ∑ u ∈ H, if g.graph.Adj v u then 1 else 0 := by
  classical
  have he : ((g.neighbors v).filter (fun u => u ∈ H)).toFinset = H.filter (g.graph.Adj v) := by
    ext u
    simp [g.correct,and_comm]
  rw [← List.toFinset_card_of_nodup ((g.nodup v).filter _),he]
  simp

lemma compiler_source_neighbor_degree (g : InputGraph n) (v : Fin n) :
    (g.neighbors v).length = g.graph.degree v := by
  have he : (g.neighbors v).toFinset = g.graph.neighborFinset v := by
    ext u
    simp [g.correct]
  rw [← List.toFinset_card_of_nodup (g.nodup v),he,SimpleGraph.card_neighborFinset_eq_degree]

lemma compiler_source_graphCut_insert (g : InputGraph n) (H : Finset (Fin n)) (v : Fin n) (hv : v ∉ H) :
    graphCut g (insert v H) = graphCut g H + (g.neighbors v).length -
      2*((g.neighbors v).filter (fun u => u ∈ H)).length := by
  classical
  have hrow (u : Fin n) :
      (∑ w, if g.graph.Adj u w ∧ w ∉ insert v H then (1 : ℤ) else 0) =
        (∑ w, if g.graph.Adj u w ∧ w ∉ H then 1 else 0) -
          (if g.graph.Adj u v then 1 else 0) := by
    have he : (fun w => if g.graph.Adj u w ∧ w ∉ insert v H then (1 : ℤ) else 0) =
        (fun w => (if g.graph.Adj u w ∧ w ∉ H then 1 else 0) -
          (if w = v then (if g.graph.Adj u v then 1 else 0) else 0)) := by
      ext w
      by_cases hw : w = v
      · subst w
        simp [hv]
      · simp [hw]
    rw [he,Finset.sum_sub_distrib]
    simp
  have hnew : (∑ w, if g.graph.Adj v w ∧ w ∉ insert v H then (1 : ℤ) else 0) =
      (g.graph.degree v : ℤ) - ∑ w ∈ H, if g.graph.Adj v w then 1 else 0 := by
    rw [hrow]
    simp only [SimpleGraph.irrefl,ite_false,sub_zero]
    have he : (fun w => if g.graph.Adj v w ∧ w ∉ H then (1 : ℤ) else 0) =
        (fun w => (if g.graph.Adj v w then 1 else 0) -
          (if w ∈ H then (if g.graph.Adj v w then 1 else 0) else 0)) := by
      ext w
      by_cases ha : g.graph.Adj v w <;> by_cases hh : w ∈ H <;> simp [ha,hh]
    rw [he,Finset.sum_sub_distrib,← SimpleGraph.degree_eq_sum_if_adj]
    simp
  unfold graphCut
  rw [Finset.sum_insert hv,hnew]
  simp only [hrow,Finset.sum_sub_distrib]
  have hs : (∑ u ∈ H, if g.graph.Adj u v then (1 : ℤ) else 0) =
      ∑ u ∈ H, if g.graph.Adj v u then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro u _
    simp only [g.graph.adj_comm]
  rw [hs,← compiler_source_neighbor_count,← compiler_source_neighbor_degree]
  ring

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

lemma compiler_source_boundary_exterior_projection (g : InputGraph n) (α : ℝ)
    (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    let h := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)
    let a := relative st t v+h = 3*(st.frames t).q/8
    let u := exteriorPush g α st t v
    u.boundaryEdges = (if a ∧ t = 0 then st.boundaryEdges+(g.neighbors v).length-
      2*((g.neighbors v).filter (fun w => w ∈ (st.frames 0).active)).length else st.boundaryEdges) ∧
    (u.frames 0).active = (if a ∧ t = 0 then insert v (st.frames 0).active else (st.frames 0).active) := by
  classical
  dsimp only
  by_cases ha : relative st t v+min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v) = 3*(st.frames t).q/8
  · by_cases ht : t = 0
    · subst t
      by_cases htop : 0 < st.top
      all_goals simp [exteriorPush,ha,htop,refreshKeys,debit,changeFrame]
    · by_cases htop : t < st.top
      all_goals simp [exteriorPush,ha,ht,htop,refreshKeys,debit,changeFrame,Ne.symm ht]
  · simp [exteriorPush,ha,refreshKeys,debit]

lemma compiler_source_boundary_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hi : BoundaryIdentity g st)
    (hv : t = 0 → v ∉ (st.frames 0).active) :
    BoundaryIdentity g (exteriorPush g α st t v) := by
  classical
  obtain ⟨hb,hH⟩ := compiler_source_boundary_exterior_projection g α st t v
  unfold BoundaryIdentity
  rw [hb,hH]
  split
  · rename_i ha
    rw [compiler_source_graphCut_insert g (st.frames 0).active v (hv ha.2),hi]
  · exact hi

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

lemma compiler_source_boundary_pending (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hr : RegionInvariant st) (hi : BoundaryIdentity g st)
    (hp : pendingPush st = some (t,v)) :
    BoundaryIdentity g (exteriorPush g α st t v) := by
  apply compiler_source_boundary_exterior g α st t v hi
  intro ht
  obtain ⟨hlev,hm⟩ := pending_push_member st t v hp
  subst t
  exact (Finset.mem_sdiff.mp ((hr 0 (Nat.zero_le _)).2.1 hm)).2

@[simp] lemma compiler_source_active_ite (P : Prop) [Decidable P] (a b : RecursiveState n) (i : ℕ) :
    ((if P then a else b).frames i).active =
      if P then (a.frames i).active else (b.frames i).active := by split <;> rfl
@[simp] lemma compiler_source_boundary_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).boundaryEdges = if P then a.boundaryEdges else b.boundaryEdges := by split <;> rfl

set_option maxHeartbeats 1000000 in
lemma compiler_source_boundary_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hr : RegionInvariant st) (hi : BoundaryIdentity g st) :
    BoundaryIdentity g (recursiveStep m g s α ℓ schedule st) := by
  classical
  change st.boundaryEdges = graphCut g (st.frames 0).active at hi
  by_cases htop : st.top = 0
  · have ht : (0 : ℕ) = st.top := htop.symm
    cases hp : pendingPush st with
    | none =>
      cases hpc : (st.frames st.top).pc <;>
        simp only [htop] at hpc <;>
        simp [recursiveStep,hpc,hp,BoundaryIdentity,htop,debit,
          changePC,changeFrame,Function.update_apply,finishEpisode,refreshKeys,
          jointUpdate,completeComponent,endCall,hi]
    | some p =>
      obtain ⟨t,v⟩ := p
      have he := compiler_source_boundary_pending g α st t v hr hi hp
      unfold BoundaryIdentity at he
      cases hpc : (st.frames st.top).pc <;>
        simp only [htop] at hpc <;>
        simp [recursiveStep,hpc,hp,BoundaryIdentity,htop,debit,
          changePC,changeFrame,Function.update_apply,finishEpisode,refreshKeys,
          jointUpdate,completeComponent,endCall,hi,he] <;> split_ifs <;> rfl
  · have ht : (0 : ℕ) ≠ st.top := Ne.symm htop
    cases hp : pendingPush st with
    | none =>
      cases hpc : (st.frames st.top).pc <;>
        simp [recursiveStep,hpc,hp,BoundaryIdentity,htop,ht,debit,
          changePC,changeFrame,Function.update_apply,finishEpisode,refreshKeys,
          jointUpdate,completeComponent,endCall,hi]
    | some p =>
      obtain ⟨t,v⟩ := p
      have he := compiler_source_boundary_pending g α st t v hr hi hp
      unfold BoundaryIdentity at he
      cases hpc : (st.frames st.top).pc <;>
        simp [recursiveStep,hpc,hp,BoundaryIdentity,htop,ht,debit,
          changePC,changeFrame,Function.update_apply,finishEpisode,refreshKeys,
          jointUpdate,completeComponent,endCall,hi,he] <;> split_ifs <;> rfl

lemma compiler_source_boundary_run (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    BoundaryIdentity g (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simp [recursiveRun,recursiveInit,freshFrame,emptyFrame,BoundaryIdentity,graphCut]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      compiler_source_boundary_step m g s α ℓ schedule _ (compiler_public_region_run m g s α q ℓ schedule t) ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerReachableFacts

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_run_invariants (m : SolveModel) {n : ℕ} (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0<α ∧ α<1) (hq : 0<q) (hs : 0<g.graph.degree s) (ell : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ell schedule t
    RegionInvariant st ∧ st.top ≤ ell ∧ KeysInvariant g st ∧ ParameterInvariant st ∧
      StoredInvariant g st ∧ BudgetInvariant st ∧ NumericalInvariant g st ∧ BoundaryIdentity g st := by
  have hResidual := recursive_residual_identities m n g s α q ell schedule t
  have hControl := recursive_control_parameters m n g s α q ell schedule t
  have hQueues := recursive_queue_domains m n g s α q ell schedule t
  exact ⟨hResidual.1,hControl.1,hQueues.1 hq.le,hControl.2.2.2 hq,hQueues.2.2 hq.le hs,hControl.2.1,
    recursive_numerical_invariants m n g s α q hα hq hs ell schedule t,
    compiler_source_boundary_run m g s α q ell schedule t⟩

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerStoredWork

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_volume_mono {n : ℕ} (g : InputGraph n) {S T : Finset (Fin n)} (h : S⊆T) : volumeNat g S≤volumeNat g T := by
  unfold volumeNat
  exact Finset.sum_le_sum_of_subset_of_nonneg h (by intros; positivity)

lemma compiler_card_le_volume {n : ℕ} (g : InputGraph n) (T : Finset (Fin n))
    (h : ∀ v∈T, 0<g.graph.degree v) : T.card≤volumeNat g T := by
  rw [Finset.card_eq_sum_ones,volumeNat]
  apply Finset.sum_le_sum
  intro v hv
  rw [compiler_source_neighbor_degree]
  exact h v hv

lemma compiler_volume_insert_le {n : ℕ} (g : InputGraph n) (v : Fin n) (T : Finset (Fin n)) :
    volumeNat g (insert v T)≤volumeNat g T+(g.neighbors v).length := by
  classical
  by_cases hv : v∈T
  · rw [Finset.insert_eq_of_mem hv]
    omega
  · simp [volumeNat,Finset.sum_insert,hv,Nat.add_comm]

lemma compiler_push_charge_covers_row (j d k : ℕ) (hk : 1≤k) :
    d≤32*(j+1)*(d+1)*k := by
  calc
    d≤d+1 := Nat.le_succ _
    _≤(j+1)*(d+1) := Nat.le_mul_of_pos_left _ (by omega)
    _≤32*((j+1)*(d+1)) := Nat.le_mul_of_pos_left _ (by norm_num)
    _≤(32*((j+1)*(d+1)))*k := Nat.le_mul_of_pos_right _ (by omega)
    _=_ := by ring

lemma compiler_stored_work_exterior {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (t : ℕ) (v : Fin n) (h : (volumeNat g logical.stored : ℝ≥0∞)≤logical.work) :
    (volumeNat g (exteriorPush g α logical t v).stored : ℝ≥0∞)≤(exteriorPush g α logical t v).work := by
  rw [compiler_exterior_stored,compiler_cost_work_exterior]
  have hv : ((volumeNat g (insert v logical.stored) : ℕ) : ℝ≥0∞) ≤
      ((volumeNat g logical.stored+(g.neighbors v).length : ℕ) : ℝ≥0∞) := by exact_mod_cast compiler_volume_insert_le g v logical.stored
  have hN := compiler_push_charge_covers_row logical.top (g.neighbors v).length (keyCost (exteriorPush g α logical t v)) (by unfold keyCost; omega)
  have hCast : (((g.neighbors v).length : ℕ) : ℝ≥0∞)≤((32*(logical.top+1)*((g.neighbors v).length+1)*keyCost (exteriorPush g α logical t v) : ℕ) : ℝ≥0∞) := by exact_mod_cast hN
  exact hv.trans (by simpa only [Nat.cast_add] using add_le_add h hCast)

lemma compiler_stored_change_frame {n : ℕ} (logical : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame logical j f).stored=logical.stored := rfl
lemma compiler_stored_pc {n : ℕ} (logical : RecursiveState n) (pc : NormalizePC) :
    (changePC logical pc).stored=logical.stored := rfl
lemma compiler_stored_debit {n : ℕ} (logical : RecursiveState n) (j : ℕ) (c : ℝ≥0∞) :
    (debit logical j c).stored=logical.stored := rfl
lemma compiler_stored_refresh {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g logical T).stored=logical.stored := rfl
lemma compiler_stored_joint {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) (z : Fin n → ℝ) :
    (jointUpdate g α logical z).stored=logical.stored := rfl
lemma compiler_stored_finish {n : ℕ} (logical : RecursiveState n) : (finishEpisode logical).stored=logical.stored := rfl
lemma compiler_stored_complete {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (logical : RecursiveState n) :
    (completeComponent m g s α logical).stored=logical.stored := rfl
lemma compiler_stored_end {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) :
    (endCall g α logical).stored=logical.stored := by
  unfold endCall
  dsimp only
  split <;> rfl

set_option maxHeartbeats 6000000 in
lemma compiler_stored_step_cases (m : SolveModel) {n : ℕ} (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (logical : RecursiveState n) :
    (recursiveStep m g s α ell schedule logical).stored=logical.stored ∨
      ∃ t v, pendingPush logical=some (t,v) ∧ recursiveStep m g s α ell schedule logical=exteriorPush g α logical t v := by
  by_cases hd : logical.done=true
  · left
    simp only [recursiveStep,hd,if_true]
  by_cases hc : componentComplete logical
  · left
    simp only [recursiveStep,hd,Bool.false_eq_true,if_false,hc,if_true,compiler_stored_complete]
  cases hp : pendingPush logical with
  | none =>
    left
    cases hPC : (logical.frames logical.top).pc <;>
      simp only [recursiveStep,hd,Bool.false_eq_true,hc,if_false,hPC,hp,Option.isSome_none] <;>
      (try split_ifs) <;> simp only [compiler_stored_change_frame,compiler_stored_pc,compiler_stored_debit,
        compiler_stored_refresh,compiler_stored_joint,compiler_stored_finish,compiler_stored_end]
  | some pair =>
    obtain ⟨t,v⟩ := pair
    cases hPC : (logical.frames logical.top).pc <;>
      simp only [recursiveStep,hd,Bool.false_eq_true,hc,if_false,hPC,hp,Option.isSome_some,if_true] <;> (try split_ifs) <;>
      first
      | exact Or.inr ⟨t,v,hp,rfl⟩
      | exact Or.inr ⟨t,v,rfl,rfl⟩
      | exact Or.inl (by simp only [compiler_stored_change_frame,compiler_stored_pc,compiler_stored_debit,
          compiler_stored_refresh,compiler_stored_joint,compiler_stored_finish,compiler_stored_end])

lemma compiler_stored_work_step (m : SolveModel) {n : ℕ} (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (logical : RecursiveState n)
    (h : (volumeNat g logical.stored : ℝ≥0∞)≤logical.work) :
    (volumeNat g (recursiveStep m g s α ell schedule logical).stored : ℝ≥0∞)≤(recursiveStep m g s α ell schedule logical).work := by
  rcases compiler_stored_step_cases m g s α ell schedule logical with hSame|⟨t,v,hp,hStep⟩
  · rw [hSame,compiler_cost_recursiveStep_work_debit]
    exact h.trans (le_add_of_nonneg_right (by positivity))
  · rw [hStep]
    exact compiler_stored_work_exterior g α logical t v h

lemma compiler_stored_work_run (m : SolveModel) {n : ℕ} (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let logical := recursiveRun m g s α q ell schedule t
    (volumeNat g logical.stored : ℝ≥0∞)≤logical.work := by
  dsimp only
  induction t with
  | zero => simp [recursiveRun,recursiveInit,volumeNat]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using compiler_stored_work_step m g s α ell schedule (recursiveRun m g s α q ell schedule t) ih

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

@[simp] lemma RecursiveMachineMemory.frame_queueMass {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hI : out.scalar.integerMemory=st.scalar.integerMemory) (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : (pm.frame hI hR hP hG hO).queueMass=pm.queueMass := rfl

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

lemma ControllerMemory.mass_done {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=true) : memory.mass=0 := by
  unfold ControllerMemory.mass
  rw [dif_neg (by rw [hDone]; decide)]

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

lemma ControllerMemory.potential_live {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (P Q : ℕ) :
    memory.potential P Q=P*memory.mass+Q*recursiveCacheMass logical := by
  unfold ControllerMemory.potential
  rw [hDone]
  rfl


end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetStatusExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

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

-- Proof module: Solutions.PrincipalSolves

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma matrix_maximum_principle {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hOff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hRow : ∀ i, 0 < ∑ j, A i j) (x : V → ℝ)
    (hx : ∀ i, 0 ≤ (A *ᵥ x) i) : ∀ i, 0 ≤ x i := by
  intro v
  by_contra hv
  have hv : x v < 0 := lt_of_not_ge hv
  obtain ⟨w, _, hw⟩ := Finset.exists_min_image univ x ⟨v, mem_univ v⟩
  have hwn : x w < 0 := lt_of_le_of_lt (hw v (mem_univ v)) hv
  have hs : ∑ j, A w j * (x j - x w) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    by_cases hj : j = w
    · simp [hj]
    · exact mul_nonpos_of_nonpos_of_nonneg (hOff w j (Ne.symm hj))
        (sub_nonneg.mpr (hw j (mem_univ j)))
  have he : (A *ᵥ x) w = (∑ j, A w j) * x w + ∑ j, A w j * (x j - x w) := by
    simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    ring
  have hn := mul_neg_of_pos_of_neg (hRow w) hwn
  have hp := hx w
  rw [he] at hp
  linarith

lemma matrix_inverse_positive {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hOff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hRow : ∀ i, 0 < ∑ j, A i j) :
    IsUnit A ∧ ∀ b : V → ℝ, (∀ i, 0 ≤ b i) → ∀ i, 0 ≤ (A⁻¹ *ᵥ b) i := by
  have hu : IsUnit A := by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro x y hxy
    have hp := matrix_maximum_principle A hOff hRow (x-y) (by
      rw [mulVec_sub,hxy,sub_self]
      simp)
    have hn := matrix_maximum_principle A hOff hRow (y-x) (by
      rw [mulVec_sub,hxy,sub_self]
      simp)
    ext v
    have := hp v
    have := hn v
    simp only [Pi.sub_apply] at *
    linarith
  refine ⟨hu, ?_⟩
  intro b hb
  apply matrix_maximum_principle A hOff hRow
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), one_mulVec]
  exact hb

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

lemma principal_inverse_positive {n : ℕ} (g : InputGraph n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (T : Finset (Fin n))
    (hT : ∀ v ∈ T, 0 < g.graph.degree v) :
    IsUnit ((LocalPush.Lα g.graph α).submatrix (fun v : T => v.val) (fun v : T => v.val)) ∧
    ∀ b : T → ℝ, (∀ i, 0 ≤ b i) →
      ∀ i, 0 ≤ (((LocalPush.Lα g.graph α).submatrix (fun v : T => v.val) (fun v : T => v.val))⁻¹ *ᵥ b) i := by
  have hh := principal_signs g α hα T hT
  exact matrix_inverse_positive _ hh.1 hh.2

lemma solveOn_nonneg {n : ℕ} (g : InputGraph n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (T : Finset (Fin n))
    (hT : ∀ v ∈ T, 0 < g.graph.degree v) (b : Fin n → ℝ)
    (hb : ∀ v ∈ T, 0 ≤ b v) : ∀ v, 0 ≤ solveOn g α T b v := by
  intro v
  classical
  unfold solveOn
  split
  · exact (principal_inverse_positive g α hα T hT).2 _ (fun i => hb i.val i.property) _
  · exact le_rfl

lemma mulVec_extend_subtype {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (T : Finset V) (x : T → ℝ) (i : T) :
    (M *ᵥ (fun v => if h : v ∈ T then x ⟨v,h⟩ else 0)) i.val =
      (M.submatrix (fun v : T => v.val) (fun v : T => v.val) *ᵥ x) i := by
  classical
  let xe : V → ℝ := fun v => if h : v ∈ T then x ⟨v,h⟩ else 0
  have he : (fun j : T => M i.val j.val * xe j.val) =
      (fun j : T => M i.val j.val * x j) := by
    ext j
    simp only [xe, dif_pos j.property]
  change (∑ j, M i.val j * xe j) = ∑ j : T, M i.val j.val * x j
  calc
    _ = ∑ j ∈ T, M i.val j * xe j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ T)
      intro j _ hj
      simp [xe, hj]
    _ = ∑ j : T, M i.val j.val * xe j.val :=
      (Finset.sum_coe_sort T (fun j : V => M i.val j * xe j)).symm
    _ = _ := congrArg (fun f : T → ℝ => ∑ j, f j) he

lemma solveOn_exact {n : ℕ} (g : InputGraph n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (T : Finset (Fin n))
    (hT : ∀ v ∈ T, 0 < g.graph.degree v) (b : Fin n → ℝ) :
    ∀ v ∈ T, (LocalPush.Lα g.graph α *ᵥ solveOn g α T b) v = b v := by
  classical
  intro v hv
  let i : T := ⟨v,hv⟩
  unfold solveOn
  have hm := (principal_inverse_positive g α hα T hT).1
  rw [show v = i.val from rfl, mulVec_extend_subtype, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hm), Matrix.one_mulVec]

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

-- Proof module: Solutions.ControllerSparseDenotation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma ControllerMemory.potential_done {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=true) (P Q : ℕ) : memory.potential P Q=0 := by
  rw [ControllerMemory.potential,memory.mass_done hDone,hDone]
  simp

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerGrowthAlgebra

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_nat_scaled_bound (a b factor k : ℕ) (hab : a≤b) (hf : 0<factor) (hk : 0<k) :
    a≤factor*b*k := by
  exact hab.trans ((Nat.le_mul_of_pos_left b hf).trans (Nat.le_mul_of_pos_right _ hk))

lemma compiler_begin_charge_covers_card {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (hCard : (logical.frames logical.top).active.card≤volumeNat g (logical.frames logical.top).active) :
    (logical.frames logical.top).active.card≤16*(volumeNat g (logical.frames logical.top).active+1)*keyCost logical :=
  compiler_nat_scaled_bound _ _ 16 _ (hCard.trans (Nat.le_succ _)) (by norm_num) (by unfold keyCost; positivity)

lemma compiler_joint_heap_growth (m : SolveModel) {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (ell : ℕ) (hDepth : logical.top≤ell) (T : Finset (Fin n)) (a : ℕ)
    (ha : a≤2*(volumeNat g T+T.card+1)) :
    ((2*(logical.top+1)*a : ℕ) : ℝ≥0∞)≤((2*(ell+1) : ℕ) : ℝ≥0∞)*jointCost m g logical T := by
  let size := volumeNat g T+T.card
  let charge := 32*(logical.top+1)*(size+1)*keyCost logical
  have haC : a≤charge := by
    have h32 : 2*(size+1)≤(32*(logical.top+1))*(size+1) := Nat.mul_le_mul_right _ (by omega)
    exact ha.trans (h32.trans (Nat.le_mul_of_pos_right _ (by unfold keyCost; positivity)))
  have hNat : 2*(logical.top+1)*a≤2*(ell+1)*charge := Nat.mul_le_mul (by omega) haC
  have hCast : ((2*(logical.top+1)*a : ℕ) : ℝ≥0∞)≤((2*(ell+1) : ℕ) : ℝ≥0∞)*(charge : ℝ≥0∞) := by exact_mod_cast hNat
  exact hCast.trans (mul_le_mul_of_nonneg_left (show (charge : ℝ≥0∞)≤jointCost m g logical T from le_add_of_nonneg_left (by positivity)) (by positivity))

lemma compiler_push_heap_growth {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (ell t : ℕ) (v : Fin n) (hDepth : logical.top≤ell) :
    ((2*(logical.top+1)*((g.neighbors v).length+1) : ℕ) : ℝ≥0∞)≤
      ((2*(ell+1) : ℕ) : ℝ≥0∞)*((32*(logical.top+1)*((g.neighbors v).length+1)*keyCost (exteriorPush g α logical t v) : ℕ) : ℝ≥0∞) := by
  have hRow : (g.neighbors v).length+1≤32*(logical.top+1)*((g.neighbors v).length+1)*keyCost (exteriorPush g α logical t v) := by
    have h := compiler_nat_scaled_bound ((g.neighbors v).length+1) ((g.neighbors v).length+1)
      (32*(logical.top+1)) (keyCost (exteriorPush g α logical t v)) le_rfl (by positivity) (by unfold keyCost; positivity)
    simpa only [Nat.mul_assoc] using h
  exact_mod_cast Nat.mul_le_mul (show 2*(logical.top+1)≤2*(ell+1) by omega) hRow

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerSourceGrowth

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 4000000 in
lemma compiler_source_heap_growth (m : SolveModel) {n : ℕ} (g : InputGraph n) (α : ℝ) (ell : ℕ)
    (logical : RecursiveState n) (hDone : logical.done=false) (hDepth : logical.top≤ell)
    (hStored : StoredInvariant g logical) (hRegion : RegionInvariant logical) :
    ((controllerSourceGrowth g ell logical : ℕ) : ℝ≥0∞)≤
      ((2*(ell+1) : ℕ) : ℝ≥0∞)*(stepDebit m g α ell logical).2 := by
  by_cases hComp : componentComplete logical
  · simp only [controllerSourceGrowth,if_pos hComp,Nat.cast_zero]
    exact zero_le
  rw [controllerSourceGrowth,if_neg hComp]
  have hActive := compiler_stored_active_domain g logical hStored logical.top le_rfl
  have hCache := compiler_stored_cache_high_domain g logical hStored hRegion logical.top le_rfl
  have hDegreeA := hActive.2
  have hDegreeC := hCache.2
  have hCard := compiler_card_le_volume g (logical.frames logical.top).active hActive.2
  have hCover := compiler_begin_charge_covers_card g logical hCard
  have hBegin : ((2*(logical.top+1)*(logical.frames logical.top).active.card : ℕ) : ℝ≥0∞)≤
      ((2*(ell+1) : ℕ) : ℝ≥0∞)*((16*(volumeNat g (logical.frames logical.top).active+1)*keyCost logical : ℕ) : ℝ≥0∞) := by
    exact_mod_cast Nat.mul_le_mul (show 2*(logical.top+1)≤2*(ell+1) by omega) hCover
  have hChild (extra : ℕ) : (((logical.frames logical.top).active.card : ℕ) : ℝ≥0∞)≤
      ((2*(ell+1) : ℕ) : ℝ≥0∞)*((16*(volumeNat g (logical.frames logical.top).active+1)*keyCost logical+extra : ℕ) : ℝ≥0∞) := by
    exact_mod_cast (hCover.trans ((Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_left _ (by positivity))))
  have hFull := compiler_joint_heap_growth m g logical ell hDepth (logical.frames logical.top).active
    (volumeNat g (logical.frames logical.top).active+(logical.frames logical.top).active.card) (by omega)
  let C := (logical.frames logical.top).cache ∪ (logical.frames logical.top).high
  have hLeaf := compiler_joint_heap_growth m g logical ell hDepth C (C.card+(volumeNat g C+C.card)) (by omega)
  have hPush (t : ℕ) (v : Fin n) := compiler_push_heap_growth g α logical ell t v hDepth
  have hOne : ((2*(logical.top+1) : ℕ) : ℝ≥0∞)≤((2*(ell+1) : ℕ) : ℝ≥0∞)*1 := by
    simpa only [mul_one] using (show ((2*(logical.top+1) : ℕ) : ℝ≥0∞)≤((2*(ell+1) : ℕ) : ℝ≥0∞) from by exact_mod_cast (show 2*(logical.top+1)≤2*(ell+1) by omega))
  by_cases hAny : anyExhausted logical
  · cases hp : pendingPush logical with
    | none =>
      cases hPC : (logical.frames logical.top).pc <;>
        simp only [controllerStepGrowth,hPC,initialRestartGrowth,controllerAfterGrowth,hp,Option.isSome_none,Bool.false_eq_true,
          hAny,not_true_eq_false,if_false,if_true,ite_self,Nat.cast_zero]
      all_goals first | exact zero_le | simpa only [stepDebit,hDone,Bool.false_eq_true,hComp,if_false,hPC] using hBegin
    | some pair =>
      obtain ⟨t,v⟩ := pair
      cases hPC : (logical.frames logical.top).pc <;>
        simp only [controllerStepGrowth,hPC,initialRestartGrowth,controllerAfterGrowth,hp,Option.isSome_some,
          hAny,not_true_eq_false,if_false,if_true,ite_self,Nat.cast_zero]
      all_goals first | exact zero_le | simpa only [stepDebit,hDone,Bool.false_eq_true,hComp,if_false,hPC] using hBegin
  · have hA : ¬ancestorExhausted logical := by
      rintro ⟨i,hi,h⟩
      exact hAny ⟨i,by omega,h⟩
    have hCurrent : ¬exhausted logical logical.top := fun h => hAny ⟨logical.top,le_rfl,h⟩
    cases hp : pendingPush logical with
    | none =>
      cases hPC : (logical.frames logical.top).pc <;>
        simp only [controllerStepGrowth,stepDebit,hDone,Bool.false_eq_true,hComp,hPC,initialRestartGrowth,
          controllerAfterGrowth,controllerPendingGrowth,leafControllerGrowth,leafTightGrowth,drainDegree,hp,Option.isSome_none,
          hAny,hA,hCurrent,if_pos hActive,if_pos hCache,hActive,hCache,and_self,and_true,true_and,implies_true,forall_const,not_false_eq_true,if_true,if_false,ite_self,Nat.cast_zero] <;>
        (try split_ifs) <;> (try dsimp only)
      all_goals try contradiction
      all_goals try simp only [Nat.cast_zero,Nat.zero_add,Nat.mul_one,Nat.add_zero]
      all_goals first | exact zero_le | with_reducible exact hBegin | with_reducible exact hFull | with_reducible exact hLeaf | with_reducible exact hOne | with_reducible exact hChild _
    | some pair =>
      obtain ⟨t,v⟩ := pair
      cases hPC : (logical.frames logical.top).pc <;>
        simp only [controllerStepGrowth,stepDebit,hDone,Bool.false_eq_true,hComp,hPC,initialRestartGrowth,
          controllerAfterGrowth,controllerPendingGrowth,leafControllerGrowth,leafTightGrowth,drainDegree,hp,Option.isSome_some,
          hAny,hA,hCurrent,if_pos hActive,if_pos hCache,hActive,hCache,and_self,and_true,true_and,implies_true,forall_const,not_false_eq_true,if_true,if_false,ite_self,Nat.cast_zero] <;>
        (try split_ifs) <;> (try dsimp only)
      all_goals try contradiction
      all_goals try simp only [Nat.cast_zero,Nat.zero_add,Nat.mul_one,Nat.add_zero]
      all_goals first | exact zero_le | with_reducible exact hBegin | with_reducible exact hFull | with_reducible exact hLeaf | with_reducible exact hOne | with_reducible exact hPush t v | with_reducible exact hChild _

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerWorkPrefix

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_recursive_work_prefix (m : SolveModel) {n : ℕ} (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (ell : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    (recursiveRun m g s α (rootThreshold ε ell) ell schedule t).work ≤ recursiveWork m g s α ε ell schedule := by
  classical
  unfold recursiveWork
  dsimp only
  split
  · exact le_iSup (fun t => (recursiveRun m g s α (rootThreshold ε ell) ell schedule t).work) t
  · exact le_top

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerCapacityProfile

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def compilerHeapBudget {n : ℕ} (logical : RecursiveState n) (ell : ℕ) : ℕ :=
  compilerNatBudget (((2*(ell+1) : ℕ) : ℝ≥0∞)*logical.work)

lemma compiler_heap_budget_cast {n : ℕ} (logical : RecursiveState n) (ell : ℕ) (hFinite : logical.work≠⊤) :
    ((compilerHeapBudget logical ell : ℕ) : ℝ≥0∞)≤((2*(ell+1) : ℕ) : ℝ≥0∞)*logical.work := by
  apply compiler_nat_budget_cast_le
  exact ENNReal.mul_ne_top (by finiteness) hFinite

set_option maxHeartbeats 2000000 in
lemma compiler_heap_budget_step (m : SolveModel) {n : ℕ} (g : InputGraph n) (s : Fin n) (α : ℝ) (ell : ℕ)
    (logical : RecursiveState n) (hDone : logical.done=false) (hDepth : logical.top≤ell)
    (hStored : StoredInvariant g logical) (hRegion : RegionInvariant logical)
    (hFinite : logical.work≠⊤) (hNextFinite : (recursiveStep m g s α ell [] logical).work≠⊤) :
    compilerHeapBudget logical ell+controllerSourceGrowth g ell logical≤
      compilerHeapBudget (recursiveStep m g s α ell [] logical) ell := by
  have hWork := compiler_cost_recursiveStep_work_debit m g s α ell [] logical
  have hChargeFinite : (stepDebit m g α ell logical).2≠⊤ := by
    have h : logical.work+(stepDebit m g α ell logical).2≠⊤ := by rw [←hWork]; exact hNextFinite
    exact (ENNReal.add_ne_top.mp h).2
  unfold compilerHeapBudget
  rw [hWork]
  simpa only [mul_add] using (compiler_nat_budget_add (((2*(ell+1) : ℕ) : ℝ≥0∞)*logical.work)
    (((2*(ell+1) : ℕ) : ℝ≥0∞)*(stepDebit m g α ell logical).2) (ENNReal.mul_ne_top (by finiteness) hFinite)
    (ENNReal.mul_ne_top (by finiteness) hChargeFinite) _
    (compiler_source_heap_growth m g α ell logical hDone hDepth hStored hRegion))

lemma compiler_heap_budget_mono_bound {n : ℕ} (logical : RecursiveState n) (ell N : ℕ)
    (hFinite : logical.work≠⊤) (h : ((2*(ell+1) : ℕ) : ℝ≥0∞)*logical.work≤(N : ℝ≥0∞)) :
    compilerHeapBudget logical ell≤N := by
  exact_mod_cast (compiler_heap_budget_cast logical ell hFinite).trans h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerResourceBounds

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_resource_budget_bound {n : ℕ} (logical : RecursiveState n) (ell N D : ℕ)
    (hFinite : logical.work≠⊤)
    (hGrowth : (D : ℝ≥0∞)≤((6*(ell+1) : ℕ) : ℝ≥0∞)*logical.work)
    (hWide : ((8*(ell+1) : ℕ) : ℝ≥0∞)*logical.work≤(N : ℝ≥0∞)) :
    compilerHeapBudget logical ell+D≤N := by
  have h : (((compilerHeapBudget logical ell+D : ℕ) : ℝ≥0∞))≤(N : ℝ≥0∞) := by
    calc
      _ = ((compilerHeapBudget logical ell : ℕ) : ℝ≥0∞)+(D : ℝ≥0∞) := by push_cast; rfl
      _ ≤ ((2*(ell+1) : ℕ) : ℝ≥0∞)*logical.work+((6*(ell+1) : ℕ) : ℝ≥0∞)*logical.work :=
        add_le_add (compiler_heap_budget_cast logical ell hFinite) hGrowth
      _ = ((8*(ell+1) : ℕ) : ℝ≥0∞)*logical.work := by push_cast; ring
      _ ≤ _ := hWide
  exact_mod_cast h

lemma compiler_resource_from_stored {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell N D : ℕ)
    (hFinite : logical.work≠⊤) (hStored : (volumeNat g logical.stored : ℝ≥0∞)≤logical.work)
    (hD : D≤6*(ell+1)*volumeNat g logical.stored)
    (hWide : ((8*(ell+1) : ℕ) : ℝ≥0∞)*logical.work≤(N : ℝ≥0∞)) :
    compilerHeapBudget logical ell+D≤N := by
  apply compiler_resource_budget_bound logical ell N D hFinite _ hWide
  have hc : (D : ℝ≥0∞)≤((6*(ell+1) : ℕ) : ℝ≥0∞)*((volumeNat g logical.stored : ℕ) : ℝ≥0∞) := by exact_mod_cast hD
  exact hc.trans (mul_le_mul_of_nonneg_left hStored (by positivity))

lemma compiler_source_pending_growth {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (hComp : ¬componentComplete logical) (hAny : ¬anyExhausted logical)
    (hSome : (pendingPush logical).isSome=true)
    (hPC : (logical.frames logical.top).pc ∈ [NormalizePC.initialDrain,.leafDrain,.afterChild,.restartDrain]) :
    controllerSourceGrowth g ell logical=2*(logical.top+1)*(drainDegree g logical+1) := by
  have hA : ¬ancestorExhausted logical := by
    rintro ⟨i,hi,h⟩
    exact hAny ⟨i,by omega,h⟩
  cases hp : pendingPush logical with
  | none => simp [hp] at hSome
  | some pair =>
    obtain ⟨t,v⟩ := pair
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hPC
    rcases hPC with hPC|hPC|hPC|hPC
    all_goals simp [controllerSourceGrowth,hComp,controllerStepGrowth,hPC,initialRestartGrowth,controllerPendingGrowth,controllerAfterGrowth,hA,hAny,hp,drainDegree]

lemma compiler_source_after_growth {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (hComp : ¬componentComplete logical) (hAny : ¬anyExhausted logical)
    (hPC : (logical.frames logical.top).pc=.afterChild) :
    controllerSourceGrowth g ell logical=2*(logical.top+1)*(drainDegree g logical+1) := by
  have hA : ¬ancestorExhausted logical := by
    rintro ⟨i,hi,h⟩
    exact hAny ⟨i,by omega,h⟩
  simp [controllerSourceGrowth,hComp,controllerStepGrowth,hPC,controllerAfterGrowth,hA,hAny]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerStateCapacities

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_domain_growth_bound (top ell a V : ℕ) (hDepth : top≤ell) (ha : a≤3*V) :
    2*(top+1)*a≤6*(ell+1)*V := by
  calc
    _≤2*(ell+1)*(3*V) := Nat.mul_le_mul (by omega) ha
    _=_ := by ring

set_option maxHeartbeats 6000000 in
lemma compiler_capacities_of_work (m : SolveModel) {n : ℕ} (g : InputGraph n) (s : Fin n) (α : ℝ) (ell N : ℕ)
    (logical : RecursiveState n) (hDone : logical.done=false) (hDepth : logical.top≤ell)
    (hStored : StoredInvariant g logical) (hRegion : RegionInvariant logical)
    (hComp : ¬componentComplete logical)
    (hFinite : logical.work≠⊤) (hNextFinite : (recursiveStep m g s α ell [] logical).work≠⊤)
    (hStoredWork : (volumeNat g logical.stored : ℝ≥0∞)≤logical.work)
    (hWide : ((8*(ell+1) : ℕ) : ℝ≥0∞)*logical.work≤(N : ℝ≥0∞))
    (hNextBound : compilerHeapBudget (recursiveStep m g s α ell [] logical) ell≤N) :
    ControllerCapacities g logical ell (compilerHeapBudget logical ell) N := by
  let V := volumeNat g logical.stored
  have hActive := compiler_stored_active_domain g logical hStored logical.top le_rfl
  have hCache := compiler_stored_cache_high_domain g logical hStored hRegion logical.top le_rfl
  have hAV : volumeNat g (logical.frames logical.top).active≤V := compiler_volume_mono g hActive.1
  have hAC : (logical.frames logical.top).active.card≤V := (compiler_card_le_volume g _ hActive.2).trans hAV
  let C := (logical.frames logical.top).cache ∪ (logical.frames logical.top).high
  have hCV : volumeNat g C≤V := compiler_volume_mono g hCache.1
  have hCC : C.card≤V := (compiler_card_le_volume g C hCache.2).trans hCV
  have hBase : compilerHeapBudget logical ell≤N := by
    have h := compiler_resource_from_stored g logical ell N 0 hFinite hStoredWork (by omega) hWide
    simpa only [Nat.add_zero] using h
  have hStep := compiler_heap_budget_step m g s α ell logical hDone hDepth hStored hRegion hFinite hNextFinite
  refine ⟨hBase,?_,?_,?_,?_,?_,?_⟩
  · intro hPC
    exact compiler_resource_from_stored g logical ell N _ hFinite hStoredWork
      (compiler_domain_growth_bound _ _ _ V hDepth (by omega)) hWide
  · intro hPC hAny
    exact compiler_resource_from_stored g logical ell N _ hFinite hStoredWork
      (compiler_domain_growth_bound _ _ _ V hDepth (by omega)) hWide
  · intro hPC hAny hNe
    apply compiler_resource_from_stored g logical ell N _ hFinite hStoredWork _ hWide
    exact (Nat.le_mul_of_pos_left (logical.frames logical.top).active.card (by positivity : 0<2*(logical.top+1))).trans
      (compiler_domain_growth_bound _ _ _ V hDepth (by omega))
  · intro hPC hAny
    by_cases hEmpty : (logical.frames logical.top).high=∅
    · simpa only [leafControllerGrowth,leafTightGrowth,if_pos hEmpty,Nat.add_zero] using hBase
    · simp only [leafControllerGrowth,leafTightGrowth,if_neg hEmpty]
      exact compiler_resource_from_stored g logical ell N _ hFinite hStoredWork
        (compiler_domain_growth_bound _ _ _ V hDepth (by change C.card+(volumeNat g C+C.card)≤3*V; omega)) hWide
  · intro hPC hAny hSome
    rw [compiler_source_pending_growth g logical ell hComp hAny hSome hPC] at hStep
    exact hStep.trans hNextBound
  · intro hPC hAny
    rw [compiler_source_after_growth g logical ell hComp hAny hPC] at hStep
    exact hStep.trans hNextBound

lemma compiler_heap_budget_initial {n : ℕ} (g : InputGraph n) (s : Fin n) (q : ℝ) (ell : ℕ) (schedule : BlockSchedule) :
    1≤compilerHeapBudget (recursiveInit g s q ell schedule) ell := by
  apply (compiler_nat_budget_iff _ (by
    change (((2*(ell+1) : ℕ) : ℝ≥0∞)*((8*(ell+2)*(⌈1/q⌉₊+2) : ℕ) : ℝ≥0∞))≠⊤
    finiteness) 1).mpr
  change ((1 : ℕ) : ℝ≥0∞)≤((2*(ell+1) : ℕ) : ℝ≥0∞)*((8*(ell+2)*(⌈1/q⌉₊+2) : ℕ) : ℝ≥0∞)
  exact_mod_cast (show 1≤2*(ell+1)*(8*(ell+2)*(⌈1/q⌉₊+2)) from Nat.succ_le_of_lt (by positivity))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerLoopExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def controllerChargeSum (charge : ℕ → ℝ≥0∞) (index remaining : ℕ) : ℝ≥0∞ :=
  match remaining with
  | 0 => 0
  | r+1 => charge index+2+controllerChargeSum charge (index+1) r

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerLoopBounded
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 15000000 in
lemma controller_loop_bounded_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (source : ℕ → RecursiveState n) (charge : ℕ → ℝ≥0∞) (capacity : ℕ → ℕ)
    (potential : ∀ {logical : RecursiveState n} {st : MachineState}, ControllerMemory g s α ε ell length logical st → ℕ)
    (hPay : ∀ {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st),
      potential memory.payUnit=potential memory)
    (terminal : ℕ) (hDone : (source terminal).done=true)
    (hLive : ∀ k < terminal, (source k).done=false)
    (step : ∀ k < terminal, ∀ st, ∀ memory : ControllerMemory g s α ε ell length (source k) st, memory.mass ≤ capacity k →
      ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (source (k+1)) out,
        MachineEval m g ω controllerBodyCode st steps out ∧ next.mass ≤ capacity (k+1) ∧
        out.work+(potential next : ℝ≥0∞) ≤ st.work+(potential memory : ℝ≥0∞)+charge k) :
    ∀ remaining index, index+remaining=terminal → ∀ st,
      ∀ memory : ControllerMemory g s α ε ell length (source index) st, memory.mass ≤ capacity index →
      ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (source terminal) out,
        MachineEval m g ω recursiveControllerCode st steps out ∧ next.mass ≤ capacity terminal ∧
        out.work+(potential next : ℝ≥0∞) ≤
          st.work+(potential memory : ℝ≥0∞)+controllerChargeSum charge index remaining+1 := by
  intro remaining
  induction remaining with
  | zero =>
    intro index hIndex st memory hMass
    have hi : index=terminal := by omega
    subst index
    have hFlag : st.scalar.core.ptrs 150=1 := by rw [memory.doneFlag,hDone]; rfl
    have ex : MachineEval m g ω recursiveControllerCode st 1 (payUnit st) :=
      MachineEval.pointerDone memory.halted (by rw [memory.one,hFlag])
    refine ⟨1,payUnit st,memory.payUnit,ex,by simpa only [ControllerMemory.payUnit_mass] using hMass,?_⟩
    rw [payUnit_work,hPay]
    simp only [controllerChargeSum,add_zero]
    exact le_of_eq (by ac_rfl)
  | succ remaining ih =>
    intro index hIndex st memory hMass
    have hi : index < terminal := by omega
    have hFlag : st.scalar.core.ptrs 150=0 := by rw [memory.doneFlag,hLive index hi]; rfl
    obtain ⟨u,a,am,ea,aMass,aW⟩ := step index hi (payUnit st) memory.payUnit (by simpa only [ControllerMemory.payUnit_mass] using hMass)
    obtain ⟨v,out,next,eb,bMass,bW⟩ := ih (index+1) (by omega) (payUnit a) am.payUnit (by simpa only [ControllerMemory.payUnit_mass] using aMass)
    have ex : MachineEval m g ω recursiveControllerCode st (1+u+1+v) out :=
      MachineEval.pointerNext memory.halted (by rw [memory.one,hFlag]; omega) ea eb
    refine ⟨1+u+1+v,out,next,ex,bMass,?_⟩
    rw [hPay,payUnit_work] at aW bW
    calc
      _ ≤ (a.work+1)+(potential am : ℝ≥0∞)+controllerChargeSum charge (index+1) remaining+1 := bW
      _ = (a.work+(potential am : ℝ≥0∞))+(controllerChargeSum charge (index+1) remaining+2) := by ring
      _ ≤ ((st.work+1)+(potential memory : ℝ≥0∞)+charge index)+(controllerChargeSum charge (index+1) remaining+2) :=
        add_le_add aW le_rfl
      _ = _ := by simp only [controllerChargeSum]; ring

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

abbrev compiler_output_region_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_residual_identities m n g s α q ℓ schedule t).1

abbrev compiler_output_root_identity_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_residual_identities m n g s α q ℓ schedule t).2.1

abbrev compiler_output_root_threshold_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_residual_identities m n g s α q ℓ schedule t).2.2.2

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

lemma compiler_output_solveOn_outside (g : InputGraph n) (α : ℝ) (T : Finset (Fin n))
    (b : Fin n → ℝ) (v : Fin n) (hv : v ∉ T) : solveOn g α T b v = 0 := by
  classical
  simp [solveOn,hv]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootReturnProof

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma compiler_output_root_return_residual (g : InputGraph n) (s : Fin n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (ℓ : ℕ) (st : RecursiveState n)
    (hq : 0 < (st.frames 0).q) (hi : RootIdentity g s α st)
    (hr : returnConditions g ℓ 0 st) :
    ∀ v, 0 ≤ residual g.graph α s (prune (st.frames 0).q st.x) v ∧
      residual g.graph α s (prune (st.frames 0).q st.x) v ≤
        ((kappa ℓ 0 : ℝ)+15/8)*(st.frames 0).q*LocalPush.deg g.graph v := by
  classical
  let q := (st.frames 0).q
  let H := (st.frames 0).active
  let c := 3*q/8
  let z := prune q st.x
  let w := st.x-z
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hk : (1 : ℝ) ≤ kappa ℓ 0 := by unfold kappa; norm_cast; omega
  have hd (v : Fin n) : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
  have hcap : ∀ v, (v ∈ H → c ≤ st.x v) ∧ (v ∉ H → 0 ≤ st.x v ∧ st.x v ≤ c) := by
    intro v
    refine ⟨?_,?_⟩
    · exact hr.2.2.2 v
    · intro hv
      have hh := hr.2.2.1 v (by simpa [parentDomain,H] using hv)
      simpa [relative,c,q] using hh
  have hx : ∀ v, 0 ≤ st.x v := by
    intro v
    by_cases hv : v ∈ H
    · exact hc.trans ((hcap v).1 hv)
    · exact ((hcap v).2 hv).1
  have hz : ∀ v, 0 ≤ z v := fun v => le_max_right _ _
  have hw : ∀ v, 0 ≤ w v ∧ w v ≤ c := by
    intro v
    by_cases hv : st.x v ≤ c
    · have he : z v = 0 := max_eq_right (sub_nonpos.mpr hv)
      simpa [w,he] using ⟨hx v,hv⟩
    · have he : z v = st.x v-c := max_eq_left (sub_nonneg.mpr (le_of_not_ge hv))
      have he' : w v = c := by simp [w,he]
      rw [he']
      exact ⟨hc,le_rfl⟩
  have hwactive : ∀ v ∈ H, w v = c := by
    intro v hv
    have he : z v = st.x v-c := max_eq_left (sub_nonneg.mpr ((hcap v).1 hv))
    simp [w,he]
  have hzinactive : ∀ v ∉ H, z v = 0 := by
    intro v hv
    exact max_eq_right (sub_nonpos.mpr ((hcap v).2 hv).2)
  have hraw : ∀ v, 0 ≤ (st.frames 0).residual v ∧
      (st.frames 0).residual v ≤ (kappa ℓ 0 : ℝ)*q*LocalPush.deg g.graph v := by
    intro v
    by_cases hv : v ∈ H
    · exact hr.1 v hv
    · have hh := hr.2.1 0 (by omega) v (by simpa [parentDomain,H] using hv)
      refine ⟨hh.1,hh.2.trans ?_⟩
      have hn : 0 ≤ q*LocalPush.deg g.graph v := mul_nonneg hq.le (hd v)
      nlinarith
  have hmul (y : Fin n → ℝ) (v : Fin n) :
      (LocalPush.Lα g.graph α *ᵥ y) v = LocalPush.deg g.graph v*y v -
        (1-α)*∑ u ∈ g.graph.neighborFinset v, y u := by
    simp [LocalPush.Lα,LocalPush.degM,LocalPush.adjM,sub_mulVec,smul_mulVec,
      Matrix.mulVec_diagonal,SimpleGraph.adjMatrix_mulVec_apply]
  have hsum (v : Fin n) : 0 ≤ ∑ u ∈ g.graph.neighborFinset v, w u :=
    Finset.sum_nonneg (fun u _ => (hw u).1)
  have hsumupper (v : Fin n) : (∑ u ∈ g.graph.neighborFinset v, w u) ≤ LocalPush.deg g.graph v*c := by
    calc
      _ ≤ ∑ u ∈ g.graph.neighborFinset v, c := Finset.sum_le_sum (fun u _ => (hw u).2)
      _ = _ := by simp [LocalPush.deg]
  have hupper (v : Fin n) : (LocalPush.Lα g.graph α *ᵥ w) v ≤ LocalPush.deg g.graph v*c := by
    rw [hmul]
    have hh := mul_le_mul_of_nonneg_left (hw v).2 (hd v)
    nlinarith [mul_nonneg (sub_nonneg.mpr hα.2.le) (hsum v)]
  have hlower (v : Fin n) (hv : v ∈ H) : 0 ≤ (LocalPush.Lα g.graph α *ᵥ w) v := by
    rw [hmul,hwactive v hv]
    have hh := mul_le_mul_of_nonneg_left (hsumupper v) (sub_nonneg.mpr hα.2.le)
    have hn := mul_nonneg (mul_nonneg hα.1.le (hd v)) hc
    nlinarith
  have hres : residual g.graph α s z = residual g.graph α s st.x + LocalPush.Lα g.graph α *ᵥ w := by
    have he : z = st.x-w := by dsimp [w]; abel
    rw [he]
    unfold residual
    rw [Matrix.mulVec_sub]
    abel
  intro v
  have hbase := hi v
  change _ = (st.frames 0).residual v + LocalPush.deg g.graph v*(if v ∈ H then q else 4*st.x v) at hbase
  have hret : LocalPush.deg g.graph v*(if v ∈ H then q else 4*st.x v) ≤ (3*q/2)*LocalPush.deg g.graph v := by
    by_cases hv : v ∈ H
    · simp only [hv,ite_true]
      nlinarith [mul_nonneg hq.le (hd v)]
    · simp only [hv,ite_false]
      have hh := mul_le_mul_of_nonneg_left ((hcap v).2 hv).2 (hd v)
      dsimp [c] at hh
      nlinarith
  refine ⟨?_,?_⟩
  · by_cases hv : v ∈ H
    · have hh := congrFun hres v
      simp only [Pi.add_apply] at hh
      rw [hh,hbase]
      exact add_nonneg (add_nonneg (hraw v).1 (by simp [hv]; exact mul_nonneg (hd v) hq.le)) (hlower v hv)
    · change 0 ≤ LocalPush.e s v - (LocalPush.Lα g.graph α *ᵥ z) v
      rw [hmul,hzinactive v hv]
      have hspos : 0 ≤ ∑ u ∈ g.graph.neighborFinset v, z u := Finset.sum_nonneg (fun u _ => hz u)
      have hepos : 0 ≤ LocalPush.e s v := by simp only [LocalPush.e,Pi.single_apply]; split <;> norm_num
      nlinarith [mul_nonneg (sub_nonneg.mpr hα.2.le) hspos]
  · have hh := congrFun hres v
    simp only [Pi.add_apply] at hh
    rw [hh,hbase]
    have hu := hupper v
    have hr0 := (hraw v).2
    dsimp [c] at hu
    nlinarith

lemma compiler_output_root_threshold_error (ε : ℝ) (hε : 0 < ε) (ℓ : ℕ) :
    0 < rootThreshold ε ℓ ∧
      ((kappa ℓ 0 : ℝ)+15/8)*rootThreshold ε ℓ ≤ ε := by
  have hk : (3 : ℝ) ≤ kappa ℓ 0 := by unfold kappa; norm_cast; omega
  have hk0 : (0 : ℝ) < kappa ℓ 0 := by linarith
  refine ⟨by unfold rootThreshold; positivity, ?_⟩
  unfold rootThreshold
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32*(kappa ℓ 0 : ℝ))).mpr
  nlinarith [mul_pos hε hk0]

lemma compiler_output_sparse_vector (T : Finset (Fin n)) (x : Fin n → ℝ) (v : Fin n) :
    outputVector (sparseOn T x) v = if v ∈ T then x v else 0 := by
  classical
  simp only [outputVector,sparseOn,List.map_map]
  have he : ∀ u : Fin n, ((u.val : ℤ) = (v.val : ℤ)) ↔ u = v := by
    intro u
    simp only [Int.natCast_inj,Fin.val_inj]
  rw [← List.sum_toFinset _ (T.nodup_toList.filter _)]
  simp only [List.toFinset_filter]
  by_cases hx : x v = 0 <;> by_cases hv : v ∈ T <;> simp [he,hx,hv]

lemma compiler_output_normal_root_output_correct (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (st : RecursiveState n) (hq : (st.frames 0).q = rootThreshold ε ℓ)
    (hi : RootIdentity g s α st) (hr : returnConditions g ℓ 0 st) :
    let z := prune (st.frames 0).q st.x
    let o := sparseOn (st.frames 0).active (potentialOutput g.graph α z)
    outputVector o = potentialOutput g.graph α z ∧
      (∀ v : Fin n, 0 ≤ outputVector o v) ∧ ACL g.graph α ε s (outputVector o) := by
  classical
  dsimp only
  have hqpos : 0 < (st.frames 0).q := by rw [hq]; exact (compiler_output_root_threshold_error ε hε.1 ℓ).1
  have hb := compiler_output_root_return_residual g s α hα ℓ st hqpos hi hr
  have hres : ∀ v, 0 ≤ residual g.graph α s (prune (st.frames 0).q st.x) v ∧
      residual g.graph α s (prune (st.frames 0).q st.x) v ≤ ε*LocalPush.deg g.graph v := by
    intro v
    refine ⟨(hb v).1,(hb v).2.trans ?_⟩
    rw [hq]
    have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
    exact mul_le_mul_of_nonneg_right (compiler_output_root_threshold_error ε hε.1 ℓ).2 hd
  have ho : outputVector (sparseOn (st.frames 0).active
        (potentialOutput g.graph α (prune (st.frames 0).q st.x))) =
      potentialOutput g.graph α (prune (st.frames 0).q st.x) := by
    ext v
    rw [compiler_output_sparse_vector]
    by_cases hv : v ∈ (st.frames 0).active
    · simp [hv]
    · have hcap := (hr.2.2.1 v (by simpa [parentDomain] using hv)).2
      simp only [relative,ite_true] at hcap
      have hz : prune (st.frames 0).q st.x v = 0 := max_eq_right (sub_nonpos.mpr hcap)
      simp [hv,potentialOutput,hz]
  refine ⟨ho,?_,?_⟩
  · rw [ho]
    intro v
    unfold potentialOutput
    apply mul_nonneg
    · apply mul_nonneg hα.1.le
      unfold LocalPush.deg
      positivity
    · exact le_max_right _ _
  · rw [ho]
    exact (residual_error g.graph s α ε hα hε hs _ (fun v => le_max_right _ _)).2 hres

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RunInvariants

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma compiler_output_run_root_output_correct (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ)
    (hr : returnConditions g ℓ 0 (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t)) :
    let st := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t
    let z := prune (st.frames 0).q st.x
    let o := sparseOn (st.frames 0).active (potentialOutput g.graph α z)
    outputVector o = potentialOutput g.graph α z ∧
      (∀ v : Fin n, 0 ≤ outputVector o v) ∧ ACL g.graph α ε s (outputVector o) := by
  exact compiler_output_normal_root_output_correct g s α ε hα hε hs ℓ _ (compiler_output_root_threshold_run m g s α (rootThreshold ε ℓ) ℓ schedule t)
    (compiler_output_root_identity_run m g s α (rootThreshold ε ℓ) ℓ schedule t) hr

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NormalBranch

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma compiler_output_normal_return_accuracy (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α ≤ 1/2) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t
    st.top = 0 → (st.frames 0).pc = .normal →
      let z := prune (st.frames 0).q st.x
      let o := sparseOn (st.frames 0).active (potentialOutput g.graph α z)
      (∀ v : Fin n, 0 ≤ outputVector o v) ∧ ACL g.graph α ε s (outputVector o) := by
  dsimp only
  intro htop hpc
  have hn := normalization_composes m n g s α ε ℓ schedule hα hε hs t
  dsimp only at hn
  have hpc' : ((recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).frames
      (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).top).pc = .normal := by
    simpa only [htop] using hpc
  have hr : returnConditions g ℓ 0 (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t) := by
    simpa only [htop] using (hn hpc').2
  have ha : α < 1 := by linarith [hα.2]
  exact (compiler_output_run_root_output_correct m g s α ε ⟨hα.1,ha⟩ hε hs ℓ schedule t hr).2

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.GraphCut

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma compiler_output_neighbor_count (g : InputGraph n) (v : Fin n) (H : Finset (Fin n)) :
    (((g.neighbors v).filter (fun u => u ∈ H)).length : ℤ) =
      ∑ u ∈ H, if g.graph.Adj v u then 1 else 0 := by
  classical
  have he : ((g.neighbors v).filter (fun u => u ∈ H)).toFinset = H.filter (g.graph.Adj v) := by
    ext u
    simp [g.correct,and_comm]
  rw [← List.toFinset_card_of_nodup ((g.nodup v).filter _),he]
  simp

lemma compiler_output_neighbor_degree (g : InputGraph n) (v : Fin n) :
    (g.neighbors v).length = g.graph.degree v := by
  have he : (g.neighbors v).toFinset = g.graph.neighborFinset v := by
    ext u
    simp [g.correct]
  rw [← List.toFinset_card_of_nodup (g.nodup v),he,SimpleGraph.card_neighborFinset_eq_degree]

lemma compiler_output_graphCut_insert (g : InputGraph n) (H : Finset (Fin n)) (v : Fin n) (hv : v ∉ H) :
    graphCut g (insert v H) = graphCut g H + (g.neighbors v).length -
      2*((g.neighbors v).filter (fun u => u ∈ H)).length := by
  classical
  have hrow (u : Fin n) :
      (∑ w, if g.graph.Adj u w ∧ w ∉ insert v H then (1 : ℤ) else 0) =
        (∑ w, if g.graph.Adj u w ∧ w ∉ H then 1 else 0) -
          (if g.graph.Adj u v then 1 else 0) := by
    have he : (fun w => if g.graph.Adj u w ∧ w ∉ insert v H then (1 : ℤ) else 0) =
        (fun w => (if g.graph.Adj u w ∧ w ∉ H then 1 else 0) -
          (if w = v then (if g.graph.Adj u v then 1 else 0) else 0)) := by
      ext w
      by_cases hw : w = v
      · subst w
        simp [hv]
      · simp [hw]
    rw [he,Finset.sum_sub_distrib]
    simp
  have hnew : (∑ w, if g.graph.Adj v w ∧ w ∉ insert v H then (1 : ℤ) else 0) =
      (g.graph.degree v : ℤ) - ∑ w ∈ H, if g.graph.Adj v w then 1 else 0 := by
    rw [hrow]
    simp only [SimpleGraph.irrefl,ite_false,sub_zero]
    have he : (fun w => if g.graph.Adj v w ∧ w ∉ H then (1 : ℤ) else 0) =
        (fun w => (if g.graph.Adj v w then 1 else 0) -
          (if w ∈ H then (if g.graph.Adj v w then 1 else 0) else 0)) := by
      ext w
      by_cases ha : g.graph.Adj v w <;> by_cases hh : w ∈ H <;> simp [ha,hh]
    rw [he,Finset.sum_sub_distrib,← SimpleGraph.degree_eq_sum_if_adj]
    simp
  unfold graphCut
  rw [Finset.sum_insert hv,hnew]
  simp only [hrow,Finset.sum_sub_distrib]
  have hs : (∑ u ∈ H, if g.graph.Adj u v then (1 : ℤ) else 0) =
      ∑ u ∈ H, if g.graph.Adj v u then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro u _
    simp only [g.graph.adj_comm]
  rw [hs,← compiler_output_neighbor_count,← compiler_output_neighbor_degree]
  ring

lemma compiler_output_graphCut_closed (g : InputGraph n) (H : Finset (Fin n)) (hc : graphCut g H = 0)
    (v : Fin n) (hv : v ∈ H) (u : Fin n) (hu : u ∉ H) : ¬g.graph.Adj v u := by
  intro ha
  have hrow : (1 : ℤ) ≤ ∑ w, if g.graph.Adj v w ∧ w ∉ H then 1 else 0 := by
    calc
      _ = (if g.graph.Adj v u ∧ u ∉ H then (1 : ℤ) else 0) := by simp [ha,hu]
      _ ≤ _ := Finset.single_le_sum
        (f := fun w : Fin n => if g.graph.Adj v w ∧ w ∉ H then (1 : ℤ) else 0)
        (fun w _ => by split <;> norm_num) (Finset.mem_univ u)
  have hsum : (∑ w, if g.graph.Adj v w ∧ w ∉ H then (1 : ℤ) else 0) ≤ graphCut g H := by
    apply Finset.single_le_sum _ hv
    intro v _
    apply Finset.sum_nonneg
    intro u _
    split <;> norm_num
  have := hrow.trans hsum
  rw [hc] at this
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ComponentOutput

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma compiler_output_zero_green (g : InputGraph n) (α : ℝ) : green g.graph α 0 = 0 := by
  classical
  ext v
  simp [green,extendPositive,show (fun _ : PositiveVertices g.graph => (0 : ℝ)) = 0 from rfl]

lemma compiler_output_completed_domain_residual (g : InputGraph n) (s : Fin n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (H : Finset (Fin n)) (hs : s ∈ H)
    (hH : ∀ v ∈ H, 0 < g.graph.degree v) (hc : graphCut g H = 0) :
    residual g.graph α s (solveOn g α H (LocalPush.e s)) = 0 := by
  classical
  ext v
  simp only [residual,Pi.sub_apply,Pi.zero_apply]
  by_cases hv : v ∈ H
  · rw [solveOn_exact g α hα H hH (LocalPush.e s) v hv,sub_self]
  · have hvs : v ≠ s := fun h => hv (h ▸ hs)
    have hz : (LocalPush.Lα g.graph α *ᵥ solveOn g α H (LocalPush.e s)) v = 0 := by
      change (∑ u, LocalPush.Lα g.graph α v u*solveOn g α H (LocalPush.e s) u) = 0
      apply Finset.sum_eq_zero
      intro u _
      by_cases hu : u ∈ H
      · have hne : v ≠ u := fun h => hv (h ▸ hu)
        have ha : ¬g.graph.Adj v u := fun h => compiler_output_graphCut_closed g H hc u hu v hv h.symm
        simp [LocalPush.Lα,LocalPush.degM,LocalPush.adjM,Matrix.diagonal_apply_ne _ hne,
          SimpleGraph.adjMatrix_apply,ha]
      · rw [compiler_output_solveOn_outside g α H (LocalPush.e s) u hu,mul_zero]
    rw [hz]
    simp [LocalPush.e,Pi.single_apply,hvs]

lemma compiler_output_completed_domain_output (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε) (hs : 0 < g.graph.degree s)
    (H : Finset (Fin n)) (hsH : s ∈ H)
    (hH : ∀ v ∈ H, 0 < g.graph.degree v) (hc : graphCut g H = 0) :
    let z := solveOn g α H (LocalPush.e s)
    let o := sparseOn H (potentialOutput g.graph α z)
    outputVector o = ppr g.graph α s ∧
      (∀ v : Fin n, 0 ≤ outputVector o v) ∧ ACL g.graph α ε s (outputVector o) := by
  classical
  let z := solveOn g α H (LocalPush.e s)
  have hz : ∀ v, 0 ≤ z v := by
    apply solveOn_nonneg g α hα H hH
    intro v _
    simp only [LocalPush.e,Pi.single_apply]
    split <;> norm_num
  have hr : residual g.graph α s z = 0 := compiler_output_completed_domain_residual g s α hα H hsH hH hc
  have hid := (residual_error g.graph s α 1 hα ⟨by norm_num,by norm_num⟩ hs z hz).1
  rw [hr,compiler_output_zero_green] at hid
  have heq : potentialOutput g.graph α z = ppr g.graph α s := by
    have hh : potentialOutput g.graph α 0 = 0 := by ext v; simp [potentialOutput]
    rw [hh] at hid
    exact (sub_eq_zero.mp hid).symm
  have ho : outputVector (sparseOn H (potentialOutput g.graph α z)) = potentialOutput g.graph α z := by
    ext v
    rw [compiler_output_sparse_vector]
    by_cases hv : v ∈ H
    · simp [hv]
    · have hh : z v = 0 := compiler_output_solveOn_outside g α H (LocalPush.e s) v hv
      simp [hv,potentialOutput,hh]
  dsimp only
  refine ⟨ho.trans heq,?_,?_⟩
  · rw [ho]
    intro v
    unfold potentialOutput
    apply mul_nonneg
    · apply mul_nonneg hα.1.le
      unfold LocalPush.deg
      positivity
    · exact hz v
  · rw [ho,heq]
    intro v
    simp only [sub_self,abs_zero]
    apply mul_nonneg hε.le
    unfold LocalPush.deg
    positivity

lemma compiler_output_connected_domain_positive (g : InputGraph n) (s : Fin n)
    (H : Finset (Fin n)) (hs : s ∈ H) (hpos : 0 < g.graph.degree s)
    (hc : (g.graph.induce (↑H : Set (Fin n))).Connected) :
    ∀ v ∈ H, 0 < g.graph.degree v := by
  intro v hv
  by_cases he : s = v
  · subst v
    exact hpos
  · have hr := (hc.preconnected ⟨s,hs⟩ ⟨v,hv⟩).map
      (SimpleGraph.Embedding.induce (↑H : Set (Fin n))).toHom
    exact SimpleGraph.Reachable.degree_pos_right he hr

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

lemma compiler_output_boundary_exterior_projection (g : InputGraph n) (α : ℝ)
    (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    let h := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)
    let a := relative st t v+h = 3*(st.frames t).q/8
    let u := exteriorPush g α st t v
    u.boundaryEdges = (if a ∧ t = 0 then st.boundaryEdges+(g.neighbors v).length-
      2*((g.neighbors v).filter (fun w => w ∈ (st.frames 0).active)).length else st.boundaryEdges) ∧
    (u.frames 0).active = (if a ∧ t = 0 then insert v (st.frames 0).active else (st.frames 0).active) := by
  classical
  dsimp only
  by_cases ha : relative st t v+min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v) = 3*(st.frames t).q/8
  · by_cases ht : t = 0
    · subst t
      by_cases htop : 0 < st.top
      all_goals simp [exteriorPush,ha,htop,refreshKeys,debit,changeFrame]
    · by_cases htop : t < st.top
      all_goals simp [exteriorPush,ha,ht,htop,refreshKeys,debit,changeFrame,Ne.symm ht]
  · simp [exteriorPush,ha,refreshKeys,debit]

lemma compiler_output_boundary_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hi : BoundaryIdentity g st)
    (hv : t = 0 → v ∉ (st.frames 0).active) :
    BoundaryIdentity g (exteriorPush g α st t v) := by
  classical
  obtain ⟨hb,hH⟩ := compiler_output_boundary_exterior_projection g α st t v
  unfold BoundaryIdentity
  rw [hb,hH]
  split
  · rename_i ha
    rw [compiler_output_graphCut_insert g (st.frames 0).active v (hv ha.2),hi]
  · exact hi

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

lemma compiler_output_boundary_pending (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hr : RegionInvariant st) (hi : BoundaryIdentity g st)
    (hp : pendingPush st = some (t,v)) :
    BoundaryIdentity g (exteriorPush g α st t v) := by
  apply compiler_output_boundary_exterior g α st t v hi
  intro ht
  obtain ⟨hlev,hm⟩ := pending_push_member st t v hp
  subst t
  exact (Finset.mem_sdiff.mp ((hr 0 (Nat.zero_le _)).2.1 hm)).2

@[simp] lemma compiler_output_active_ite (P : Prop) [Decidable P] (a b : RecursiveState n) (i : ℕ) :
    ((if P then a else b).frames i).active =
      if P then (a.frames i).active else (b.frames i).active := by split <;> rfl
@[simp] lemma compiler_output_boundary_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).boundaryEdges = if P then a.boundaryEdges else b.boundaryEdges := by split <;> rfl

set_option maxHeartbeats 1000000 in
lemma compiler_output_boundary_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hr : RegionInvariant st) (hi : BoundaryIdentity g st) :
    BoundaryIdentity g (recursiveStep m g s α ℓ schedule st) := by
  classical
  change st.boundaryEdges = graphCut g (st.frames 0).active at hi
  by_cases htop : st.top = 0
  · have ht : (0 : ℕ) = st.top := htop.symm
    cases hp : pendingPush st with
    | none =>
      cases hpc : (st.frames st.top).pc <;>
        simp only [htop] at hpc <;>
        simp [recursiveStep,hpc,hp,BoundaryIdentity,htop,debit,
          changePC,changeFrame,Function.update_apply,finishEpisode,refreshKeys,
          jointUpdate,completeComponent,endCall,hi]
    | some p =>
      obtain ⟨t,v⟩ := p
      have he := compiler_output_boundary_pending g α st t v hr hi hp
      unfold BoundaryIdentity at he
      cases hpc : (st.frames st.top).pc <;>
        simp only [htop] at hpc <;>
        simp [recursiveStep,hpc,hp,BoundaryIdentity,htop,debit,
          changePC,changeFrame,Function.update_apply,finishEpisode,refreshKeys,
          jointUpdate,completeComponent,endCall,hi,he] <;> split_ifs <;> rfl
  · have ht : (0 : ℕ) ≠ st.top := Ne.symm htop
    cases hp : pendingPush st with
    | none =>
      cases hpc : (st.frames st.top).pc <;>
        simp [recursiveStep,hpc,hp,BoundaryIdentity,htop,ht,debit,
          changePC,changeFrame,Function.update_apply,finishEpisode,refreshKeys,
          jointUpdate,completeComponent,endCall,hi]
    | some p =>
      obtain ⟨t,v⟩ := p
      have he := compiler_output_boundary_pending g α st t v hr hi hp
      unfold BoundaryIdentity at he
      cases hpc : (st.frames st.top).pc <;>
        simp [recursiveStep,hpc,hp,BoundaryIdentity,htop,ht,debit,
          changePC,changeFrame,Function.update_apply,finishEpisode,refreshKeys,
          jointUpdate,completeComponent,endCall,hi,he] <;> split_ifs <;> rfl

lemma compiler_output_boundary_run (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    BoundaryIdentity g (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simp [recursiveRun,recursiveInit,freshFrame,emptyFrame,BoundaryIdentity,graphCut]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      compiler_output_boundary_step m g s α ℓ schedule _ (compiler_output_region_run m g s α q ℓ schedule t) ih

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

set_option maxHeartbeats 1000000 in
lemma compiler_output_root_uninterrupted_step (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hi : (st.frames 0).pc ≠ .interrupted) :
    ((recursiveStep m g s α ℓ schedule st).frames 0).pc ≠ .interrupted := by
  classical
  by_cases ht : st.top = 0
  · have hanc : ¬ancestorExhausted st := by simp [ancestorExhausted,ht]
    cases hp : pendingPush st with
    | none =>
      cases hpc : (st.frames st.top).pc <;>
        simp only [ht] at hpc <;>
        simp [recursiveStep,hpc,hp,ht,hanc,hi,changePC,changeFrame,debit,
          finishEpisode,refreshKeys,jointUpdate,completeComponent,endCall,Function.update_apply] <;> (try split_ifs) <;> simp_all
    | some p =>
      obtain ⟨t,v⟩ := p
      cases hpc : (st.frames st.top).pc <;>
        simp only [ht] at hpc <;>
        simp [recursiveStep,hpc,hp,ht,hanc,hi,changePC,changeFrame,debit,
          finishEpisode,refreshKeys,jointUpdate,completeComponent,endCall,Function.update_apply] <;> (try split_ifs) <;> simp_all
  · have ht' : (0 : ℕ) ≠ st.top := Ne.symm ht
    cases hp : pendingPush st with
    | none =>
      cases hpc : (st.frames st.top).pc <;>
        simp [recursiveStep,hpc,hp,ht,ht',hi,changePC,changeFrame,debit,
          finishEpisode,refreshKeys,jointUpdate,completeComponent,endCall,Function.update_apply] <;> (try split_ifs) <;> simp_all
    | some p =>
      obtain ⟨t,v⟩ := p
      cases hpc : (st.frames st.top).pc <;>
        simp [recursiveStep,hpc,hp,ht,ht',hi,changePC,changeFrame,debit,
          finishEpisode,refreshKeys,jointUpdate,completeComponent,endCall,Function.update_apply] <;> (try split_ifs) <;> simp_all

lemma compiler_output_root_uninterrupted_run (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ((recursiveRun m g s α q ℓ schedule t).frames 0).pc ≠ .interrupted := by
  induction t with
  | zero => simp [recursiveRun,recursiveInit,freshFrame,emptyFrame]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      compiler_output_root_uninterrupted_step m g s α ℓ schedule _ ih

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

lemma compiler_output_step_done_cases (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hd : st.done = false) :
    (recursiveStep m g s α ℓ schedule st).done = true →
      componentComplete st ∨ st.top = 0 ∧
        ((st.frames 0).pc = .normal ∨ (st.frames 0).pc = .interrupted) := by
  classical
  by_cases hc : componentComplete st
  · exact fun _ => Or.inl hc
  · simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hc]
    cases hp : pendingPush st with
    | none =>
      cases hpc : (st.frames st.top).pc <;>
        simp [hpc,hp,debit,hd] <;> (try split_ifs) <;> simp_all <;> aesop
    | some p =>
      obtain ⟨t,v⟩ := p
      cases hpc : (st.frames st.top).pc <;>
        simp [hpc,hp,debit,hd] <;> (try split_ifs) <;> simp_all <;> aesop

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveOutput

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma compiler_output_threshold_le_one (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ : ℕ) :
    rootThreshold ε ℓ ≤ 1 := by
  have hk : (3 : ℝ) ≤ (kappa ℓ 0 : ℝ) := by simp [kappa]
  unfold rootThreshold
  apply (div_le_one (by positivity)).mpr
  linarith

lemma compiler_output_component_return_accuracy (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (hα : 0 < α ∧ α ≤ 1/2) (hε : 0 < ε ∧ ε ≤ 1)
    (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ)
    (hc : componentComplete (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t)) :
    let st := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t
    let o := (completeComponent m g s α st).output
    (∀ v : Fin n, 0 ≤ outputVector o v) ∧ ACL g.graph α ε s (outputVector o) := by
  classical
  let st := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t
  have hc' : (st.frames 0).active.Nonempty ∧ st.boundaryEdges = 0 := hc
  have hreg := active_region_potentials m n g s α (rootThreshold ε ℓ) ℓ schedule hα
    ⟨(compiler_output_root_threshold_error ε hε.1 ℓ).1,compiler_output_threshold_le_one ε hε ℓ⟩ hs t
  obtain ⟨hsH,hconn⟩ := hreg.1 hc'.1
  have hdeg := compiler_output_connected_domain_positive g s (st.frames 0).active hsH hs hconn
  have hcut : graphCut g (st.frames 0).active = 0 := by
    rw [← compiler_output_boundary_run m g s α (rootThreshold ε ℓ) ℓ schedule t]
    exact hc'.2
  have hh := compiler_output_completed_domain_output g s α ε ⟨hα.1,by linarith [hα.2]⟩ hε.1 hs
    (st.frames 0).active hsH hdeg hcut
  exact hh.2

lemma compiler_output_normal_step_output (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hd : st.done = false) (hc : ¬componentComplete st) (ht : st.top = 0)
    (hp : (st.frames 0).pc = .normal) :
    (recursiveStep m g s α ℓ schedule st).output =
      sparseOn (st.frames 0).active (potentialOutput g.graph α (prune (st.frames 0).q st.x)) := by
  classical
  have hp' : (st.frames st.top).pc = .normal := by simpa [ht] using hp
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hc,hp']
  simp [endCall,debit,ht]

lemma compiler_output_recursive_done_accuracy (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (hα : 0 < α ∧ α ≤ 1/2) (hε : 0 < ε ∧ ε ≤ 1)
    (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t
    st.done = true →
      (∀ v : Fin n, 0 ≤ outputVector st.output v) ∧ ACL g.graph α ε s (outputVector st.output) := by
  classical
  induction t with
  | zero => simp [recursiveRun,recursiveInit]
  | succ t ih =>
    let st := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t
    have hrun : recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule (t+1) =
        recursiveStep m g s α ℓ schedule st := by
      simp only [recursiveRun,Function.iterate_succ_apply',st]
    dsimp only
    rw [hrun]
    by_cases hd : st.done = true
    · intro _
      simpa only [recursiveStep,hd,ite_true] using ih hd
    · have hd' : st.done = false := Bool.eq_false_iff.mpr hd
      intro hn
      by_cases hc : componentComplete st
      · have he : recursiveStep m g s α ℓ schedule st = completeComponent m g s α st := by
          simp [recursiveStep,hd,hc]
        rw [he]
        exact compiler_output_component_return_accuracy m g s α ε hα hε hs ℓ schedule t hc
      · have hspl := compiler_output_step_done_cases m g s α ℓ schedule st hd' hn
        obtain ⟨ht,hpc⟩ := hspl.resolve_left hc
        have hno := compiler_output_root_uninterrupted_run m g s α (rootThreshold ε ℓ) ℓ schedule t
        have hp : (st.frames 0).pc = .normal := hpc.resolve_right hno
        have ho := compiler_output_normal_step_output m g s α ℓ schedule st hd' hc ht hp
        rw [ho]
        exact compiler_output_normal_return_accuracy m g s α ε hα hε hs ℓ schedule t ht hp

end
end NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

theorem compiler_source_done_accuracy (m : SolveModel) {n : ℕ} (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (hα : 0<α ∧ α≤1/2) (hε : 0<ε ∧ ε≤1) (hs : 0<g.graph.degree s)
    (ell : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let logical := recursiveRun m g s α (rootThreshold ε ell) ell schedule t
    logical.done=true →
      (∀ v : Fin n, 0≤outputVector logical.output v) ∧ ACL g.graph α ε s (outputVector logical.output) := by
  exact compiler_output_recursive_done_accuracy m g s α ε hα hε hs ell schedule t

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerChargeSum

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation

lemma compiler_charge_sum_bound (work debit charge : ℕ → ℝ≥0∞) (F : ℝ≥0∞) (terminal : ℕ)
    (hWork : ∀ k, work (k+1)=work k+debit k)
    (hCharge : ∀ k<terminal, charge k+2≤F*debit k) :
    ∀ remaining index, index+remaining=terminal →
      F*work index+controllerChargeSum charge index remaining≤F*work terminal := by
  intro remaining
  induction remaining with
  | zero =>
    intro index hEq
    have h : index=terminal := by omega
    subst index
    simp only [controllerChargeSum,add_zero]
    exact le_rfl
  | succ remaining ih =>
    intro index hEq
    have hi : index<terminal := by omega
    have hTail := ih (index+1) (by omega)
    simp only [controllerChargeSum]
    calc
      _ = F*work index+(charge index+2)+controllerChargeSum charge (index+1) remaining := by ring
      _ ≤ F*work index+F*debit index+controllerChargeSum charge (index+1) remaining :=
        add_le_add (add_le_add le_rfl (hCharge index hi)) le_rfl
      _ = F*work (index+1)+controllerChargeSum charge (index+1) remaining := by rw [hWork]; ring
      _ ≤ _ := hTail

lemma compiler_charge_sum_le (work debit charge : ℕ → ℝ≥0∞) (F : ℝ≥0∞) (terminal : ℕ)
    (hWork : ∀ k, work (k+1)=work k+debit k)
    (hCharge : ∀ k<terminal, charge k+2≤F*debit k) :
    controllerChargeSum charge 0 terminal≤F*work terminal := by
  have h := compiler_charge_sum_bound work debit charge F terminal hWork hCharge terminal 0 (Nat.zero_add terminal)
  exact (le_add_of_nonneg_left (by positivity)).trans h

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerSourceRun

set_option autoImplicit false
set_option maxRecDepth 20000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 24000000 in
lemma controller_source_run_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε E : ℝ) (ell length N rank Q terminal : ℕ)
    (hα : 0<α ∧ α ≤ 1/2) (hε : 0<ε ∧ ε ≤ 1) (hs : 0<g.graph.degree s)
    (hBound : recursiveWork m g s α ε ell [] ≤ ENNReal.ofReal E)
    (hWide : ((8*(ell+1) : ℕ) : ℝ≥0∞)*ENNReal.ofReal E ≤ (N : ℝ≥0∞))
    (hDone : (recursiveRun m g s α (rootThreshold ε ell) ell [] terminal).done=true)
    (hLive : ∀ k<terminal, (recursiveRun m g s α (rootThreshold ε ell) ell [] k).done=false)
    (hCredit : 4*(16*(ell+3))+17 ≤ Q) (hCap : rank<length) (hPow : N<2^rank)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length
      (recursiveInit g s (rootThreshold ε ell) ell []) st) (hM : memory.mass ≤ 1) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    let source := fun k => recursiveRun m g s α (rootThreshold ε ell) ell [] k
    let charge := fun k => controllerBodyCharge m g (source k) ell length rank Q
    ∃ steps out, MachineEval m g ω recursiveControllerCode st steps out ∧
      outputVector (n:=n) out.output=outputVector (n:=n) (source terminal).output ∧
      out.work ≤ st.work+(P : ℝ≥0∞)+controllerChargeSum charge 0 terminal+1 := by
  dsimp only
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let source := fun k => recursiveRun m g s α (rootThreshold ε ell) ell [] k
  let charge := fun k => controllerBodyCharge m g (source k) ell length rank Q
  let capacity := fun k => compilerHeapBudget (source k) ell
  let φ := fun {logical : RecursiveState n} {st : MachineState} (mem : ControllerMemory g s α ε ell length logical st) => mem.potential P Q
  have he : 0<ε := hε.1
  have hq : 0<rootThreshold ε ell := by unfold rootThreshold kappa; positivity
  have hα' : 0<α ∧ α<1 := ⟨hα.1,by linarith [hα.2]⟩
  have hPrefix (k : ℕ) : (source k).work ≤ ENNReal.ofReal E :=
    (compiler_recursive_work_prefix m g s α ε ell [] k).trans hBound
  have hFinite (k : ℕ) : (source k).work≠⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hPrefix k)
  have hWideAt (k : ℕ) : ((8*(ell+1) : ℕ) : ℝ≥0∞)*(source k).work ≤ (N : ℝ≥0∞) :=
    (mul_le_mul_of_nonneg_left (hPrefix k) (by positivity)).trans hWide
  have hBudget (k : ℕ) : capacity k ≤ N := by
    apply compiler_heap_budget_mono_bound _ ell N (hFinite k)
    have hc : ((2*(ell+1) : ℕ) : ℝ≥0∞) ≤ ((8*(ell+1) : ℕ) : ℝ≥0∞) := by exact_mod_cast (show 2*(ell+1) ≤ 8*(ell+1) by omega)
    exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans (hWideAt k)
  have hRunNext (k : ℕ) : source (k+1)=recursiveStep m g s α ell [] (source k) := by
    simp only [source,recursiveRun,Function.iterate_succ_apply']
  have step : ∀ k<terminal, ∀ a, ∀ mem : ControllerMemory g s α ε ell length (source k) a,
      mem.mass ≤ capacity k →
      ∃ u out, ∃ next : ControllerMemory g s α ε ell length (source (k+1)) out,
        MachineEval m g ω controllerBodyCode a u out ∧ next.mass ≤ capacity (k+1) ∧
        out.work+(φ next : ℝ≥0∞) ≤ a.work+(φ mem : ℝ≥0∞)+charge k := by
    intro k hk a mem hm
    obtain ⟨hRegion,hDepth,hKeys,hParameters,hStored,hBudgetInvariant,hNumerical,hBoundary⟩ :=
      compiler_run_invariants m g s α (rootThreshold ε ell) hα' hq hs ell [] k
    have hNextFinite : (recursiveStep m g s α ell [] (source k)).work≠⊤ := by rw [←hRunNext k]; exact hFinite (k+1)
    have hNextBound : compilerHeapBudget (recursiveStep m g s α ell [] (source k)) ell ≤ N := by rw [←hRunNext k]; exact hBudget (k+1)
    have caps : ¬componentComplete (source k) → ControllerCapacities g (source k) ell (capacity k) N := by
      intro hComp
      exact compiler_capacities_of_work m g s α ell N (source k) (hLive k hk) hDepth hStored hRegion hComp
        (hFinite k) hNextFinite (compiler_stored_work_run m g s α (rootThreshold ε ell) ell [] k) (hWideAt k) hNextBound
    have result := controller_source_step_exec m g ω (source k) s α ε ell length N rank Q (capacity k) a mem
      (hLive k hk) hDepth hα' hRegion hKeys hBoundary hParameters hStored hNumerical hm caps hCredit hCap hPow
    rw [←hRunNext k] at result
    obtain ⟨u,out,next,ex,hOut,hWork⟩ := result
    have hGrow : capacity k+controllerSourceGrowth g ell (source k) ≤ capacity (k+1) := by
      have h := compiler_heap_budget_step m g s α ell (source k) (hLive k hk) hDepth hStored hRegion (hFinite k) hNextFinite
      rw [←hRunNext k] at h
      exact h
    exact ⟨u,out,next,ex,hOut.trans hGrow,hWork⟩
  have hInitial : memory.mass ≤ capacity 0 := hM.trans (compiler_heap_budget_initial g s (rootThreshold ε ell) ell [])
  obtain ⟨u,out,next,ex,hOut,hWork⟩ := controller_loop_bounded_exec m g ω s α ε ell length source charge capacity φ
    (fun mem => mem.potential_payUnit P Q) terminal hDone hLive step terminal 0 (Nat.zero_add terminal) st memory hInitial
  have hCache : recursiveCacheMass (recursiveInit g s (rootThreshold ε ell) ell [])=0 := by
    simp [recursiveCacheMass,recursiveInit,freshFrame,emptyFrame]
  have hPhi : memory.potential P Q ≤ P := by
    rw [memory.potential_live (show (recursiveInit g s (rootThreshold ε ell) ell []).done=false from rfl),hCache,Nat.mul_zero,Nat.add_zero]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left P hM
  change out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+controllerChargeSum charge 0 terminal+1 at hWork
  rw [next.potential_done hDone P Q,Nat.cast_zero,add_zero] at hWork
  have hCast : (memory.potential P Q : ℝ≥0∞) ≤ (P : ℝ≥0∞) := by exact_mod_cast hPhi
  exact ⟨u,out,ex,next.output hDone,hWork.trans (add_le_add (add_le_add (add_le_add le_rfl hCast) le_rfl) le_rfl)⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerSourceRunWork

set_option autoImplicit false
set_option maxRecDepth 20000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 12000000 in
lemma controller_source_run_work_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε E : ℝ) (ell length N rank Q : ℕ) (F : ℝ≥0∞)
    (hα : 0<α ∧ α≤1/2) (hε : 0<ε ∧ ε≤1) (hs : 0<g.graph.degree s)
    (hBound : recursiveWork m g s α ε ell [] ≤ ENNReal.ofReal E)
    (hWide : ((8*(ell+1) : ℕ) : ℝ≥0∞)*ENNReal.ofReal E ≤ (N : ℝ≥0∞))
    (hTermination : ∃ t, (recursiveRun m g s α (rootThreshold ε ell) ell [] t).done=true)
    (hDom : ∀ k, (recursiveRun m g s α (rootThreshold ε ell) ell [] k).done=false →
      controllerBodyCharge m g (recursiveRun m g s α (rootThreshold ε ell) ell [] k) ell length rank Q+2 ≤
        F*(stepDebit m g α ell (recursiveRun m g s α (rootThreshold ε ell) ell [] k)).2)
    (hCredit : 4*(16*(ell+3))+17 ≤ Q) (hCap : rank<length) (hPow : N<2^rank)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length
      (recursiveInit g s (rootThreshold ε ell) ell []) st) (hM : memory.mass ≤ 1) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    ∃ steps out, MachineEval m g ω recursiveControllerCode st steps out ∧
      (∀ v : Fin n, 0 ≤ outputVector out.output v) ∧ ACL g.graph α ε s (outputVector out.output) ∧
      out.work ≤ st.work+(P : ℝ≥0∞)+F*recursiveWork m g s α ε ell []+1 := by
  classical
  dsimp only
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let source := fun k => recursiveRun m g s α (rootThreshold ε ell) ell [] k
  let work := fun k => (source k).work
  let debit := fun k => (stepDebit m g α ell (source k)).2
  let charge := fun k => controllerBodyCharge m g (source k) ell length rank Q
  let terminal := Nat.find hTermination
  have hDone : (source terminal).done=true := Nat.find_spec hTermination
  have hLive : ∀ k<terminal, (source k).done=false := by
    intro k hk
    exact Bool.eq_false_iff.mpr (Nat.find_min hTermination hk)
  obtain ⟨u,out,ex,hOutput,hWork⟩ := controller_source_run_exec m g ω s α ε E ell length N rank Q terminal hα hε hs hBound hWide hDone hLive hCredit hCap hPow st memory hM
  have hRecurrence (k : ℕ) : work (k+1)=work k+debit k := by
    simpa only [work,debit,source,recursiveRun,Function.iterate_succ_apply'] using
      compiler_cost_recursiveStep_work_debit m g s α ell [] (source k)
  have hSum := compiler_charge_sum_le work debit charge F terminal hRecurrence (fun k hk => hDom k (hLive k hk))
  have hSumBound : controllerChargeSum charge 0 terminal ≤ F*recursiveWork m g s α ε ell [] :=
    hSum.trans (mul_le_mul_of_nonneg_left (compiler_recursive_work_prefix m g s α ε ell [] terminal) (by positivity))
  have hAccuracy := compiler_source_done_accuracy m g s α ε hα hε hs ell [] terminal hDone
  rw [←hOutput] at hAccuracy
  exact ⟨u,out,ex,hAccuracy.1,hAccuracy.2,hWork.trans (add_le_add (add_le_add le_rfl hSumBound) le_rfl)⟩

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

lemma compiler_leaf_preparation_bound (ell length rank Q top : ℕ) (hTop : top≤ell) :
    leafPreparationFactor ell top length rank≤128*(compilerOverheadBase ell length rank Q)^2 := by
  let R := compilerOverheadBase ell length rank Q
  let w := 16*(ell+3)
  let P := cleanBodyBound w length rank+2
  obtain ⟨hR,hw,hL,hl,hr,hQ,hP⟩ := compiler_overhead_parameters ell length rank Q top hTop
  change 1000≤R at hR
  change w≤R at hw
  change top+1≤R at hL
  change rank≤R at hr
  change P≤R at hP
  have hSq : R≤R^2 := by nlinarith
  have hLinear : 42*rank+60*w+284≤103*R := by omega
  have hFirst : P+20*w+190≤22*R := by omega
  have hProduct : (top+1)*(42*rank+60*w+284)≤103*R^2 := by
    calc
      _≤R*(103*R) := Nat.mul_le_mul hL hLinear
      _=_ := by ring
  have hCredit : P*(2*(top+1))≤2*R^2 := by
    calc
      _≤R*(2*R) := Nat.mul_le_mul hP (by omega)
      _=_ := by ring
  change P+20*w+190+((top+1)*(42*rank+60*w+284)+21)+P*(2*(top+1))+21≤128*R^2
  nlinarith

lemma compiler_joint_iteration_bound (ell length rank Q top : ℕ) (hTop : top≤ell) :
    jointSolveIterationFactor ell top rank≤131*(compilerOverheadBase ell length rank Q)^2 := by
  let R := compilerOverheadBase ell length rank Q
  obtain ⟨hR,hw,hL,hl,hr,hQ,hP⟩ := compiler_overhead_parameters ell length rank Q top hTop
  change 1000≤R at hR
  change 16*(ell+3)≤R at hw
  change top+1≤R at hL
  change rank≤R at hr
  have hLinear : 42*rank+88*(16*(ell+3))+442≤131*R := by omega
  unfold jointSolveIterationFactor
  calc
    _≤R*(131*R) := Nat.mul_le_mul hL hLinear
    _=_ := by ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerSolveCoefficients

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_leaf_solve_bound (ell length rank Q top card size : ℕ) (hTop : top ≤ ell) (hCS : card ≤ size) :
    leafSolveUnitCost ell top rank card size ≤ 256*(compilerOverheadBase ell length rank Q)^2*(size+1) := by
  let R := compilerOverheadBase ell length rank Q
  let w := 16*(ell+3)
  let J := jointSolveIterationFactor ell top rank
  obtain ⟨hR,hw,hL,hl,hr,hQ,hP⟩ := compiler_overhead_parameters ell length rank Q top hTop
  change 1000 ≤ R at hR
  change w ≤ R at hw
  have hSq : R ≤ R^2 := by nlinarith
  have hJ : J ≤ 131*R^2 := compiler_joint_iteration_bound ell length rank Q top hTop
  have hc : 12*w+66 ≤ 13*R^2 := by
    have h : 12*w+66 ≤ 13*R := by omega
    exact h.trans (Nat.mul_le_mul_left 13 hSq)
  have hs : 24*w+100+J ≤ 156*R^2 := by nlinarith
  have h60 : 60 ≤ 60*R^2 := by nlinarith
  calc
    _ = (12*w+66)*card+(24*w+100+J)*size+60 := by unfold leafSolveUnitCost; dsimp only [w,J]; ring
    _  ≤  (13*R^2)*size+(156*R^2)*size+60*R^2 :=
      add_le_add (add_le_add (Nat.mul_le_mul hc hCS) (Nat.mul_le_mul_right size hs)) h60
    _  ≤  (256*R^2)*size+256*R^2 := by
      have h1 : (13*R^2)*size+(156*R^2)*size=(169*R^2)*size := by ring
      rw [h1]
      exact add_le_add (Nat.mul_le_mul_right size (Nat.mul_le_mul_right (R^2) (by norm_num : 169 ≤ 256)))
        (Nat.mul_le_mul_right (R^2) (by norm_num : 60 ≤ 256))
    _ = _ := by ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerLeafScalarBound

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 3000000 in
lemma compiler_leaf_core_scalar_bound (ell length rank Q top card size : ℕ) (hTop : top ≤ ell) (hCS : card ≤ size) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    let H := 2*P+(21*rank+20*(16*(ell+3))+70)+36
    let A := (card+1)*leafPreparationFactor ell top length rank
    let B := leafSolveUnitCost ell top rank card size
    let S := A+B+P*(2*(top+1)*size)
    H+S+12+Q*card ≤ 512*(compilerOverheadBase ell length rank Q)^2*(size+1) := by
  dsimp only
  let R := compilerOverheadBase ell length rank Q
  let w := 16*(ell+3)
  let P := cleanBodyBound w length rank+2
  let H := 2*P+(21*rank+20*w+70)+36
  let A := (card+1)*leafPreparationFactor ell top length rank
  let B := leafSolveUnitCost ell top rank card size
  obtain ⟨hR,hw,hL,hl,hr,hQ,hP⟩ := compiler_overhead_parameters ell length rank Q top hTop
  change 1000 ≤ R at hR
  change w ≤ R at hw
  change top+1 ≤ R at hL
  change rank ≤ R at hr
  change Q ≤ R at hQ
  change P ≤ R at hP
  have hSq : R ≤ R^2 := by nlinarith
  have hPrep : leafPreparationFactor ell top length rank ≤ 128*R^2 := compiler_leaf_preparation_bound ell length rank Q top hTop
  have hA : A ≤ 128*R^2*(size+1) := by
    simpa only [A,Nat.mul_comm] using Nat.mul_le_mul (Nat.succ_le_succ hCS) hPrep
  have hB : B ≤ 256*R^2*(size+1) := compiler_leaf_solve_bound ell length rank Q top card size hTop hCS
  have hP2 : P*(2*(top+1)) ≤ 2*R^2 := by
    calc
      _ ≤ R*(2*R) := Nat.mul_le_mul hP (by omega)
      _ = _ := by ring
  have hCredit : P*(2*(top+1)*size) ≤ 2*R^2*size := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right size hP2
  have hQSq : Q ≤ R^2 := hQ.trans hSq
  have hCache : Q*card ≤ R^2*size := Nat.mul_le_mul hQSq hCS
  have hH : H+12 ≤ 45*R^2 := by
    have hLinear : H+12 ≤ 44*R := by dsimp only [H]; omega
    nlinarith
  change H+(A+B+P*(2*(top+1)*size))+12+Q*card ≤ 512*R^2*(size+1)
  calc
    _ = (H+12)+A+B+P*(2*(top+1)*size)+Q*card := by ac_rfl
    _ ≤ 45*R^2+128*R^2*(size+1)+256*R^2*(size+1)+2*R^2*size+R^2*size :=
      add_le_add (add_le_add (add_le_add (add_le_add hH hA) hB) hCredit) hCache
    _ = 429*R^2+387*R^2*size := by ring
    _ ≤ 512*R^2+512*R^2*size := add_le_add (Nat.mul_le_mul_right (R^2) (by norm_num : 429 ≤ 512))
      (Nat.mul_le_mul_right size (Nat.mul_le_mul_right (R^2) (by norm_num : 387 ≤ 512)))
    _ = _ := by ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerQueueCoefficients

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma compiler_priority_scalar_bound (ell length rank Q top : ℕ) (hTop : top ≤ ell) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    (top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6 ≤ 45*(compilerOverheadBase ell length rank Q)^2 := by
  dsimp only
  let R := compilerOverheadBase ell length rank Q
  let w := 16*(ell+3)
  let P := cleanBodyBound w length rank+2
  obtain ⟨hR,hw,hL,hl,hr,hQ,hP⟩ := compiler_overhead_parameters ell length rank Q top hTop
  change 1000 ≤ R at hR
  change w ≤ R at hw
  change top+1 ≤ R at hL
  change rank ≤ R at hr
  change P ≤ R at hP
  have hLinear : 2*P+(21*rank+20*w+70)+50 ≤ 44*R := by omega
  have hProduct : (top+1)*(2*P+(21*rank+20*w+70)+50) ≤ 44*R^2 := by
    calc
      _ ≤ R*(44*R) := Nat.mul_le_mul hL hLinear
      _ = _ := by ring
  change (top+1)*(2*P+(21*rank+20*w+70)+50)+6 ≤ 45*R^2
  nlinarith

lemma compiler_high_peek_scalar_bound (ell length rank Q : ℕ) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    2*P+(21*rank+20*(16*(ell+3))+70)+36+12 ≤ 45*(compilerOverheadBase ell length rank Q)^2 := by
  dsimp only
  let R := compilerOverheadBase ell length rank Q
  obtain ⟨hR,hw,hL,hl,hr,hQ,hP⟩ := compiler_overhead_parameters ell length rank Q 0 (Nat.zero_le _)
  change 1000 ≤ R at hR
  change 16*(ell+3) ≤ R at hw
  change rank ≤ R at hr
  change cleanBodyBound (16*(ell+3)) length rank+2 ≤ R at hP
  have hLinear : 2*(cleanBodyBound (16*(ell+3)) length rank+2)+(21*rank+20*(16*(ell+3))+70)+36+12 ≤ 44*R := by omega
  nlinarith

lemma compiler_exterior_scalar_bound (ell length rank Q top degree : ℕ) (hTop : top ≤ ell) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    (top+1)*(degree+1)*(42*rank+168*(16*(ell+3))+910)+P*(2*(top+1)*(degree+1)) ≤
      256*(compilerOverheadBase ell length rank Q)^2*(degree+1) := by
  dsimp only
  let R := compilerOverheadBase ell length rank Q
  let w := 16*(ell+3)
  let P := cleanBodyBound w length rank+2
  obtain ⟨hR,hw,hL,hl,hr,hQ,hP⟩ := compiler_overhead_parameters ell length rank Q top hTop
  change 1000 ≤ R at hR
  change w ≤ R at hw
  change top+1 ≤ R at hL
  change rank ≤ R at hr
  change P ≤ R at hP
  have hLinear : 42*rank+168*w+910 ≤ 211*R := by omega
  have hProduct : (top+1)*(42*rank+168*w+910) ≤ 211*R^2 := by
    calc
      _ ≤ R*(211*R) := Nat.mul_le_mul hL hLinear
      _ = _ := by ring
  have hCredit : 2*P*(top+1) ≤ 2*R^2 := by
    calc
      _ ≤ (2*R)*R := Nat.mul_le_mul (by omega) hL
      _ = _ := by ring
  change (top+1)*(degree+1)*(42*rank+168*w+910)+P*(2*(top+1)*(degree+1)) ≤ 256*R^2*(degree+1)
  calc
    _ = ((top+1)*(42*rank+168*w+910)+2*P*(top+1))*(degree+1) := by ring
    _ ≤ (256*R^2)*(degree+1) := Nat.mul_le_mul_right _ (by nlinarith)
    _ = _ := rfl

lemma compiler_priority_extra_bound (ell length rank Q top extra : ℕ) (hTop : top ≤ ell) (hExtra : extra ≤ 1000) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    (top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6+extra ≤ 64*(compilerOverheadBase ell length rank Q)^2 := by
  dsimp only
  let R := compilerOverheadBase ell length rank Q
  have hR : 1000 ≤ R := (compiler_overhead_parameters ell length rank Q top hTop).1
  have hSq : R ≤ R^2 := by nlinarith
  have he : extra ≤ R^2 := hExtra.trans (hR.trans hSq)
  have hp := compiler_priority_scalar_bound ell length rank Q top hTop
  calc
    _ ≤ 45*R^2+R^2 := add_le_add hp he
    _ = 46*R^2 := by ring
    _ ≤ _ := Nat.mul_le_mul_right (R^2) (by norm_num)

lemma compiler_queue_total_scalar_bound (ell length rank Q top degree extra : ℕ) (hTop : top ≤ ell) (hExtra : extra ≤ 1000) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    let T := (top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
    let E := (top+1)*(degree+1)*(42*rank+168*(16*(ell+3))+910)
    T+E+P*(2*(top+1)*(degree+1))+extra ≤ 512*(compilerOverheadBase ell length rank Q)^2*(degree+1) := by
  dsimp only
  let R := compilerOverheadBase ell length rank Q
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let T := (top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
  let E := (top+1)*(degree+1)*(42*rank+168*(16*(ell+3))+910)
  have hOver : T+extra ≤ 64*R^2 := compiler_priority_extra_bound ell length rank Q top extra hTop hExtra
  have hExt : E+P*(2*(top+1)*(degree+1)) ≤ 256*R^2*(degree+1) := compiler_exterior_scalar_bound ell length rank Q top degree hTop
  change T+E+P*(2*(top+1)*(degree+1))+extra ≤ 512*R^2*(degree+1)
  calc
    _ = (T+extra)+(E+P*(2*(top+1)*(degree+1))) := by ac_rfl
    _ ≤ 64*R^2+256*R^2*(degree+1) := add_le_add hOver hExt
    _ ≤ 64*R^2*(degree+1)+256*R^2*(degree+1) := add_le_add (Nat.le_mul_of_pos_right _ (by omega)) le_rfl
    _ = 320*R^2*(degree+1) := by ring
    _ ≤ _ := Nat.mul_le_mul_right (degree+1) (Nat.mul_le_mul_right (R^2) (by norm_num))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerControlCoefficients

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma compiler_begin_scalar_bound (ell length rank Q top card : ℕ) (hTop : top ≤ ell) :
    let w := 16*(ell+3)
    let P := cleanBodyBound w length rank+2
    (((2*(4*w+17)+10)+((top+1)*(42*rank+60*w+284)+11))*card+188)+P*(2*(top+1)*card) ≤
      256*(compilerOverheadBase ell length rank Q)^2*(card+1) := by
  dsimp only
  let R := compilerOverheadBase ell length rank Q
  let w := 16*(ell+3)
  let P := cleanBodyBound w length rank+2
  obtain ⟨hR,hw,hL,hl,hr,hQ,hP⟩ := compiler_overhead_parameters ell length rank Q top hTop
  change 1000 ≤ R at hR
  change w ≤ R at hw
  change top+1 ≤ R at hL
  change rank ≤ R at hr
  change P ≤ R at hP
  have hSq : R ≤ R^2 := by nlinarith
  have hLinear : 42*rank+60*w+284 ≤ 103*R := by omega
  have hProduct : (top+1)*(42*rank+60*w+284) ≤ 103*R^2 := by
    calc
      _ ≤ R*(103*R) := Nat.mul_le_mul hL hLinear
      _ = _ := by ring
  have hCredit : 2*P*(top+1) ≤ 2*R^2 := by
    calc
      _ ≤ (2*R)*R := Nat.mul_le_mul (by omega) hL
      _ = _ := by ring
  have hCoeff : 8*w+55+(top+1)*(42*rank+60*w+284)+2*P*(top+1) ≤ 114*R^2 := by nlinarith
  have h188 : 188 ≤ 188*R^2 := by nlinarith
  change (((2*(4*w+17)+10)+((top+1)*(42*rank+60*w+284)+11))*card+188)+P*(2*(top+1)*card) ≤ 256*R^2*(card+1)
  calc
    _ = (8*w+55+(top+1)*(42*rank+60*w+284)+2*P*(top+1))*card+188 := by ring
    _ ≤ 114*R^2*card+188*R^2 := add_le_add (Nat.mul_le_mul_right card hCoeff) h188
    _ ≤ 256*R^2*card+256*R^2 := add_le_add
      (Nat.mul_le_mul_right card (Nat.mul_le_mul_right (R^2) (by norm_num : 114 ≤ 256)))
      (Nat.mul_le_mul_right (R^2) (by norm_num : 188 ≤ 256))
    _ = _ := by ring

lemma compiler_full_scalar_bound (ell length rank Q top card size : ℕ) (hTop : top ≤ ell) (hCS : card ≤ size) :
    let w := 16*(ell+3)
    let P := cleanBodyBound w length rank+2
    (10*card+5)+((24*w+100)*size+28)+(jointSolveIterationFactor ell top rank*size+5)+42+
      P*(2*(top+1)*size)+12 ≤ 256*(compilerOverheadBase ell length rank Q)^2*(size+1) := by
  dsimp only
  let R := compilerOverheadBase ell length rank Q
  let w := 16*(ell+3)
  let P := cleanBodyBound w length rank+2
  let J := jointSolveIterationFactor ell top rank
  obtain ⟨hR,hw,hL,hl,hr,hQ,hP⟩ := compiler_overhead_parameters ell length rank Q top hTop
  change 1000 ≤ R at hR
  change w ≤ R at hw
  change top+1 ≤ R at hL
  change P ≤ R at hP
  have hSq : R ≤ R^2 := by nlinarith
  have hJ : J ≤ 131*R^2 := compiler_joint_iteration_bound ell length rank Q top hTop
  have hCredit : 2*P*(top+1) ≤ 2*R^2 := by
    calc
      _ ≤ (2*R)*R := Nat.mul_le_mul (by omega) hL
      _ = _ := by ring
  have hCoeff : 24*w+100+J+2*P*(top+1) ≤ 158*R^2 := by nlinarith
  have h10 : 10 ≤ 10*R^2 := by nlinarith
  have h92 : 92 ≤ 92*R^2 := by nlinarith
  change (10*card+5)+((24*w+100)*size+28)+(J*size+5)+42+P*(2*(top+1)*size)+12 ≤ 256*R^2*(size+1)
  calc
    _ = 10*card+(24*w+100+J+2*P*(top+1))*size+92 := by ring
    _ ≤ 10*R^2*size+158*R^2*size+92*R^2 := add_le_add (add_le_add (Nat.mul_le_mul h10 hCS) (Nat.mul_le_mul_right size hCoeff)) h92
    _ = 168*R^2*size+92*R^2 := by ring
    _ ≤ 256*R^2*size+256*R^2 := add_le_add
      (Nat.mul_le_mul_right size (Nat.mul_le_mul_right (R^2) (by norm_num : 168 ≤ 256)))
      (Nat.mul_le_mul_right (R^2) (by norm_num : 92 ≤ 256))
    _ = _ := by ring

lemma compiler_component_scalar_bound (ell length rank Q card size : ℕ) (hCS : card ≤ size) :
    (10*card+5)+((24*(16*(ell+3))+100)*size+28)+((4*(16*(ell+3))+21)*card+6)+4 ≤
      256*(compilerOverheadBase ell length rank Q)^2*(size+1) := by
  let R := compilerOverheadBase ell length rank Q
  let w := 16*(ell+3)
  obtain ⟨hR,hw,hL,hl,hr,hQ,hP⟩ := compiler_overhead_parameters ell length rank Q 0 (Nat.zero_le _)
  change 1000 ≤ R at hR
  change w ≤ R at hw
  have hSq : R ≤ R^2 := by nlinarith
  have hCard : 4*w+31 ≤ 5*R^2 := by nlinarith
  have hSize : 24*w+100 ≤ 25*R^2 := by nlinarith
  have h43 : 43 ≤ 43*R^2 := by nlinarith
  change (10*card+5)+((24*w+100)*size+28)+((4*w+21)*card+6)+4 ≤ 256*R^2*(size+1)
  calc
    _ = (4*w+31)*card+(24*w+100)*size+43 := by ring
    _ ≤ 5*R^2*size+25*R^2*size+43*R^2 := add_le_add (add_le_add (Nat.mul_le_mul hCard hCS) (Nat.mul_le_mul_right size hSize)) h43
    _ = 30*R^2*size+43*R^2 := by ring
    _ ≤ 256*R^2*size+256*R^2 := add_le_add
      (Nat.mul_le_mul_right size (Nat.mul_le_mul_right (R^2) (by norm_num : 30 ≤ 256)))
      (Nat.mul_le_mul_right (R^2) (by norm_num : 43 ≤ 256))
    _ = _ := by ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerSolveChargeDom

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_joint_nat_covers_size {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (T : Finset (Fin n)) :
    volumeNat g T+T.card+1 ≤ 32*(logical.top+1)*(volumeNat g T+T.card+1)*keyCost logical := by
  have h := compiler_nat_scaled_bound (volumeNat g T+T.card+1) (volumeNat g T+T.card+1)
    (32*(logical.top+1)) (keyCost logical) le_rfl (by positivity) (by unfold keyCost; positivity)
  simpa only [Nat.mul_assoc] using h

lemma compiler_solve_charge_dom (m : SolveModel) {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (T : Finset (Fin n)) (F scalar : ℕ) (hF : 1 ≤ F)
    (hScalar : scalar ≤ F*(volumeNat g T+T.card+1)) :
    (scalar : ℝ≥0∞)+solveCharge m T.card (volumeNat g T+T.card) ≤ (F : ℝ≥0∞)*jointCost m g logical T := by
  have hN := hScalar.trans (Nat.mul_le_mul_left F (compiler_joint_nat_covers_size g logical T))
  have hCast : (scalar : ℝ≥0∞) ≤ (F : ℝ≥0∞)*((32*(logical.top+1)*(volumeNat g T+T.card+1)*keyCost logical : ℕ) : ℝ≥0∞) := by exact_mod_cast hN
  have hFCast : (1 : ℝ≥0∞) ≤ (F : ℝ≥0∞) := by exact_mod_cast hF
  have hSolve : solveCharge m T.card (volumeNat g T+T.card) ≤ (F : ℝ≥0∞)*solveCharge m T.card (volumeNat g T+T.card) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hFCast (by positivity : (0 : ℝ≥0∞) ≤ solveCharge m T.card (volumeNat g T+T.card))
  calc
    _ ≤ (F : ℝ≥0∞)*((32*(logical.top+1)*(volumeNat g T+T.card+1)*keyCost logical : ℕ) : ℝ≥0∞)+(F : ℝ≥0∞)*solveCharge m T.card (volumeNat g T+T.card) := add_le_add hCast hSolve
    _=_ := by unfold jointCost; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerControlChargeAdd

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation

lemma compiler_constant_factor_bound (R k A : ℕ) (hR : 1000 ≤ R) (hk : k ≤ 1000) (hA : 1 ≤ A) : k ≤ A*R^2 := by
  have hSq : R ≤ R^2 := by nlinarith
  exact (hk.trans hR).trans (hSq.trans (Nat.le_mul_of_pos_left _ (by omega)))

lemma compiler_control_charge_add (body cost : ℝ≥0∞) (overhead M G : ℕ)
    (hOne : 1 ≤ cost) (hOverhead : overhead ≤ M) (hBody : body ≤ (G : ℝ≥0∞)*cost) :
    (overhead : ℝ≥0∞)+body ≤ ((M+G : ℕ) : ℝ≥0∞)*cost := by
  have hCast : (overhead : ℝ≥0∞) ≤ (M : ℝ≥0∞) := by exact_mod_cast hOverhead
  have hControl : (overhead : ℝ≥0∞) ≤ (M : ℝ≥0∞)*cost := hCast.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hOne (by positivity : (0 : ℝ≥0∞) ≤ (M : ℝ≥0∞)))
  calc
    _ ≤ (M : ℝ≥0∞)*cost+(G : ℝ≥0∞)*cost := add_le_add hControl hBody
    _ = _ := by push_cast; ring

lemma compiler_charge_factor_mono (body cost : ℝ≥0∞) (F G : ℕ) (hFG : F ≤ G)
    (h : body ≤ (F : ℝ≥0∞)*cost) : body ≤ (G : ℝ≥0∞)*cost :=
  h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hFG) (by positivity))

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerBranchChargeBounds

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_full_time_charge {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n)
    (ell length rank Q : ℕ) (hDepth : logical.top ≤ ell) :
    let C := (logical.frames logical.top).active
    let size := volumeNat g C+C.card
    let P := SparseQueue.cleanBodyBound (16*(ell+3)) length rank+2
    let A := (10*C.card+5)+((24*(16*(ell+3))+100)*size+28)+(jointSolveIterationFactor ell logical.top rank*size+5)+42
    (((A+P*(2*(logical.top+1)*size)+12 : ℕ) : ℝ≥0∞)+solveCharge m C.card size) ≤
      ((256*(compilerOverheadBase ell length rank Q)^2 : ℕ) : ℝ≥0∞)*jointCost m g logical C := by
  dsimp only
  apply compiler_solve_charge_dom
  · apply Nat.succ_le_of_lt
    unfold compilerOverheadBase
    positivity
  · exact compiler_full_scalar_bound ell length rank Q logical.top _ _ hDepth (by omega)

lemma compiler_leaf_time_charge {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n)
    (ell length rank Q : ℕ) (hDepth : logical.top ≤ ell) :
    leafTightCharge m g logical ell length rank Q ≤
      ((512*(compilerOverheadBase ell length rank Q)^2 : ℕ) : ℝ≥0∞)*
        (if (logical.frames logical.top).high=∅ then 1 else jointCost m g logical ((logical.frames logical.top).cache ∪ (logical.frames logical.top).high)) := by
  by_cases hEmpty : (logical.frames logical.top).high=∅
  · simp only [leafTightCharge,if_pos hEmpty,mul_one]
    have h := compiler_high_peek_scalar_bound ell length rank Q
    exact_mod_cast h.trans (Nat.mul_le_mul_right ((compilerOverheadBase ell length rank Q)^2) (by norm_num : 45 ≤ 512))
  · let C := (logical.frames logical.top).cache ∪ (logical.frames logical.top).high
    have h := compiler_solve_charge_dom m g logical C (512*(compilerOverheadBase ell length rank Q)^2) _ (by
      apply Nat.succ_le_of_lt
      unfold compilerOverheadBase
      positivity) (compiler_leaf_core_scalar_bound ell length rank Q logical.top C.card (volumeNat g C+C.card) hDepth (by omega))
    simpa only [leafTightCharge,if_neg hEmpty] using h

lemma compiler_component_time_charge {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n)
    (ell length rank Q : ℕ) :
    controllerComponentCharge m g logical ell ≤
      ((256*(compilerOverheadBase ell length rank Q)^2 : ℕ) : ℝ≥0∞)*jointCost m g logical (logical.frames 0).active := by
  unfold controllerComponentCharge
  dsimp only
  apply compiler_solve_charge_dom
  · apply Nat.succ_le_of_lt
    unfold compilerOverheadBase
    positivity
  · exact compiler_component_scalar_bound ell length rank Q _ _ (by omega)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerMinorCoefficients

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_return_scalar_bound (ell length rank Q card : ℕ) :
    (8*(16*(ell+3))+31)*card+12 ≤ 16*(compilerOverheadBase ell length rank Q)^2*(card+1) := by
  let R := compilerOverheadBase ell length rank Q
  obtain ⟨hR,hw,hL,hl,hr,hQ,hP⟩ := compiler_overhead_parameters ell length rank Q 0 (Nat.zero_le _)
  change 1000 ≤ R at hR
  change 16*(ell+3) ≤ R at hw
  have hSq : R ≤ R^2 := by nlinarith
  have hC : 8*(16*(ell+3))+31 ≤ 9*R^2 := by nlinarith
  have h12 : 12 ≤ R^2 := by nlinarith
  calc
    _ ≤ 9*R^2*card+R^2 := add_le_add (Nat.mul_le_mul_right card hC) h12
    _ ≤ 16*R^2*card+16*R^2 := add_le_add
      (Nat.mul_le_mul_right card (Nat.mul_le_mul_right (R^2) (by norm_num : 9 ≤ 16))) (by nlinarith)
    _ = _ := by ring

lemma compiler_finish_scalar_bound (ell length rank Q card : ℕ) :
    (4*(16*(ell+3))+17)*card+144 ≤ 16*(compilerOverheadBase ell length rank Q)^2*(card+1) := by
  let R := compilerOverheadBase ell length rank Q
  obtain ⟨hR,hw,hL,hl,hr,hQ,hP⟩ := compiler_overhead_parameters ell length rank Q 0 (Nat.zero_le _)
  change 1000 ≤ R at hR
  change 16*(ell+3) ≤ R at hw
  have hSq : R ≤ R^2 := by nlinarith
  have hC : 4*(16*(ell+3))+17 ≤ 5*R^2 := by nlinarith
  have h144 : 144 ≤ R^2 := by nlinarith
  calc
    _ ≤ 5*R^2*card+R^2 := add_le_add (Nat.mul_le_mul_right card hC) h144
    _ ≤ 16*R^2*card+16*R^2 := add_le_add
      (Nat.mul_le_mul_right card (Nat.mul_le_mul_right (R^2) (by norm_num : 5 ≤ 16))) (by nlinarith)
    _ = _ := by ring

lemma compiler_child_scalar_bound (ell length rank Q top card block : ℕ) (hTop : top ≤ ell) :
    (block+2)*(4*(ell-(top+1))+22)+10*length+324+card*(21*rank+60*(16*(ell+3))+190)+
      (SparseQueue.cleanBodyBound (16*(ell+3)) length rank+2)*card+8 ≤
      128*(compilerOverheadBase ell length rank Q)^2*((block+2)+(card+1)) := by
  let R := compilerOverheadBase ell length rank Q
  let w := 16*(ell+3)
  let P := SparseQueue.cleanBodyBound w length rank+2
  obtain ⟨hR,hw,hL,hl,hr,hQ,hP⟩ := compiler_overhead_parameters ell length rank Q top hTop
  change 1000 ≤ R at hR
  change w ≤ R at hw
  change length ≤ R at hl
  change rank ≤ R at hr
  change P ≤ R at hP
  have hEll : ell ≤ R := by unfold R compilerOverheadBase; omega
  have hSq : R ≤ R^2 := by nlinarith
  have hBlock : 4*(ell-(top+1))+22 ≤ 128*R^2 := by nlinarith [show ell-(top+1) ≤ ell from Nat.sub_le _ _]
  have hCard : 21*rank+60*w+190+P ≤ 128*R^2 := by nlinarith
  have hConst : 10*length+332 ≤ 128*R^2 := by nlinarith
  change (block+2)*(4*(ell-(top+1))+22)+10*length+324+card*(21*rank+60*w+190)+P*card+8 ≤ 128*R^2*((block+2)+(card+1))
  calc
    _ = (4*(ell-(top+1))+22)*(block+2)+(21*rank+60*w+190+P)*card+(10*length+332) := by ring
    _ ≤ 128*R^2*(block+2)+128*R^2*card+128*R^2 := add_le_add
      (add_le_add (Nat.mul_le_mul_right (block+2) hBlock) (Nat.mul_le_mul_right card hCard)) hConst
    _ = _ := by ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerElementaryPCDom

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_begin_pc_dom (m : SolveModel) {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (ell length rank Q : ℕ) (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hDepth : logical.top ≤ ell) (hStored : StoredInvariant g logical)
    (hPC : (logical.frames logical.top).pc=.beginEpisode) :
    controllerPCCharge m g logical ell length rank Q ≤ ((1024*(compilerOverheadBase ell length rank Q)^2 : ℕ) : ℝ≥0∞)*(stepDebit m g α ell logical).2 := by
  let R := compilerOverheadBase ell length rank Q
  have hActive := compiler_stored_active_domain g logical hStored logical.top le_rfl
  have hCard := compiler_card_le_volume g _ hActive.2
  have hCost : (stepDebit m g α ell logical).2=((16*(volumeNat g (logical.frames logical.top).active+1)*keyCost logical : ℕ) : ℝ≥0∞) := by
    simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC]
  rw [hCost]
  have hScalar := compiler_begin_scalar_bound ell length rank Q logical.top (logical.frames logical.top).active.card hDepth
  have hPlus : (logical.frames logical.top).active.card+1 ≤ 16*(volumeNat g (logical.frames logical.top).active+1)*keyCost logical :=
    compiler_nat_scaled_bound _ _ 16 _ (by omega) (by norm_num) (by unfold keyCost; positivity)
  have hN := hScalar.trans (Nat.mul_le_mul_left (256*R^2) hPlus)
  have hCast : controllerPCCharge m g logical ell length rank Q ≤ ((256*R^2 : ℕ) : ℝ≥0∞)*((16*(volumeNat g (logical.frames logical.top).active+1)*keyCost logical : ℕ) : ℝ≥0∞) := by
    simp only [controllerPCCharge,hPC]
    exact_mod_cast hN
  exact compiler_charge_factor_mono _ _ (256*R^2) (1024*R^2) (Nat.mul_le_mul_right (R^2) (by norm_num)) hCast

lemma compiler_full_pc_dom (m : SolveModel) {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (ell length rank Q : ℕ) (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hDepth : logical.top ≤ ell) (hStored : StoredInvariant g logical)
    (hPC : (logical.frames logical.top).pc=.fullSolve) :
    controllerPCCharge m g logical ell length rank Q ≤ ((1024*(compilerOverheadBase ell length rank Q)^2 : ℕ) : ℝ≥0∞)*(stepDebit m g α ell logical).2 := by
  let R := compilerOverheadBase ell length rank Q
  have hActive := compiler_stored_active_domain g logical hStored logical.top le_rfl
  have hR : 1000 ≤ R := (compiler_overhead_parameters ell length rank Q 0 (Nat.zero_le _)).1
  by_cases hAny : anyExhausted logical
  · simp only [controllerPCCharge,stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hAny,if_true,mul_one]
    exact_mod_cast (compiler_constant_factor_bound R 12 1024 hR (by norm_num) (by norm_num))
  · have hCost : (stepDebit m g α ell logical).2=jointCost m g logical (logical.frames logical.top).active := by
      simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hAny,if_pos hActive]
    rw [hCost]
    have h := compiler_full_time_charge m g logical ell length rank Q hDepth
    have h' := compiler_charge_factor_mono _ _ (256*R^2) (1024*R^2) (Nat.mul_le_mul_right (R^2) (by norm_num)) h
    simpa only [controllerPCCharge,hPC,if_neg hAny] using h'

lemma compiler_return_pc_dom (m : SolveModel) {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (ell length rank Q : ℕ) (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hPC : (logical.frames logical.top).pc=.normal ∨ (logical.frames logical.top).pc=.interrupted) :
    controllerPCCharge m g logical ell length rank Q ≤ ((1024*(compilerOverheadBase ell length rank Q)^2 : ℕ) : ℝ≥0∞)*(stepDebit m g α ell logical).2 := by
  let R := compilerOverheadBase ell length rank Q
  have hR : 1000 ≤ R := (compiler_overhead_parameters ell length rank Q 0 (Nat.zero_le _)).1
  have hCost : (stepDebit m g α ell logical).2=((if logical.top=0 then 8*(logical.frames logical.top).active.card+2 else 1 : ℕ) : ℝ≥0∞) := by
    rcases hPC with hPC|hPC <;>
      simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC] <;> split_ifs <;> norm_num
  rw [hCost]
  by_cases hTop : logical.top=0
  · have hScalar := compiler_return_scalar_bound ell length rank Q (logical.frames 0).active.card
    have hPlus : (logical.frames 0).active.card+1 ≤ 8*(logical.frames 0).active.card+2 := by omega
    have hN := hScalar.trans (Nat.mul_le_mul_left (16*R^2) hPlus)
    have hCast : controllerPCCharge m g logical ell length rank Q ≤ ((16*R^2 : ℕ) : ℝ≥0∞)*((8*(logical.frames logical.top).active.card+2 : ℕ) : ℝ≥0∞) := by
      rcases hPC with hPC|hPC <;> simp only [controllerPCCharge,hPC,if_pos hTop] <;>
        simpa only [hTop,Nat.cast_mul] using (show (((8*(16*(ell+3))+31)*(logical.frames 0).active.card+12 : ℕ) : ℝ≥0∞) ≤ ((16*R^2*(8*(logical.frames 0).active.card+2) : ℕ) : ℝ≥0∞) from by exact_mod_cast hN)
    simpa only [if_pos hTop] using compiler_charge_factor_mono _ _ (16*R^2) (1024*R^2) (Nat.mul_le_mul_right (R^2) (by norm_num)) hCast
  · rcases hPC with hPC|hPC <;> simp only [controllerPCCharge,hPC,if_neg hTop,Nat.cast_one,mul_one] <;>
      exact_mod_cast (compiler_constant_factor_bound R 3 1024 hR (by norm_num) (by norm_num))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerNormalizePCDom

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_normalize_pc_dom (m : SolveModel) {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (ell length rank Q : ℕ) (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hDepth : logical.top ≤ ell) (hStored : StoredInvariant g logical)
    (hPC : (logical.frames logical.top).pc=.normalize) :
    controllerPCCharge m g logical ell length rank Q ≤ ((1024*(compilerOverheadBase ell length rank Q)^2 : ℕ) : ℝ≥0∞)*(stepDebit m g α ell logical).2 := by
  let R := compilerOverheadBase ell length rank Q
  have hR : 1000 ≤ R := (compiler_overhead_parameters ell length rank Q 0 (Nat.zero_le _)).1
  by_cases hAny : anyExhausted logical
  · simp only [controllerPCCharge,stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hAny,not_true_eq_false,if_true,mul_one]
    have h := compiler_constant_factor_bound R 12 1024 hR (by norm_num) (by norm_num)
    have hc : (12 : ℝ≥0∞) ≤ ((1024*R^2 : ℕ) : ℝ≥0∞) := by exact_mod_cast h
    norm_num at hc ⊢
    exact hc
  · by_cases hEq : logical.top=ell
    · simp only [controllerPCCharge,stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hAny,not_false_eq_true,if_true,if_pos hEq,mul_one]
      have h := compiler_constant_factor_bound R 18 1024 hR (by norm_num) (by norm_num)
      have hc : (18 : ℝ≥0∞) ≤ ((1024*R^2 : ℕ) : ℝ≥0∞) := by exact_mod_cast h
      norm_num at hc ⊢
      exact hc
    · have hActive := compiler_stored_active_domain g logical hStored logical.top le_rfl
      have hCard := compiler_card_le_volume g _ hActive.2
      have hCardPlus : (logical.frames logical.top).active.card+1 ≤ 16*(volumeNat g (logical.frames logical.top).active+1)*keyCost logical :=
        compiler_nat_scaled_bound _ _ 16 _ (by omega) (by norm_num) (by unfold keyCost; positivity)
      have hBlock : (logical.frames logical.top).block+2 ≤ 8*(ell+2)*((logical.frames logical.top).block+2) := Nat.le_mul_of_pos_left _ (by positivity)
      have hAllowance : ((logical.frames logical.top).block+2)+((logical.frames logical.top).active.card+1) ≤
          16*(volumeNat g (logical.frames logical.top).active+1)*keyCost logical+8*(ell+2)*((logical.frames logical.top).block+2) := by
        simpa only [Nat.add_comm] using add_le_add hCardPlus hBlock
      have hScalar := compiler_child_scalar_bound ell length rank Q logical.top (logical.frames logical.top).active.card (logical.frames logical.top).block hDepth
      have hN := hScalar.trans (Nat.mul_le_mul_left (128*R^2) hAllowance)
      have hCost : (stepDebit m g α ell logical).2=
          ((16*(volumeNat g (logical.frames logical.top).active+1)*keyCost logical+8*(ell+2)*((logical.frames logical.top).block+2) : ℕ) : ℝ≥0∞) := by
        simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hAny,if_neg hEq]
      rw [hCost]
      have hc : controllerPCCharge m g logical ell length rank Q ≤ ((128*R^2 : ℕ) : ℝ≥0∞)*
          ((16*(volumeNat g (logical.frames logical.top).active+1)*keyCost logical+8*(ell+2)*((logical.frames logical.top).block+2) : ℕ) : ℝ≥0∞) := by
        simp only [controllerPCCharge,hPC,if_pos hAny,if_neg hEq,controllerChildCharge]
        have hCast : ((((logical.frames logical.top).block+2)*(4*(ell-(logical.top+1))+22)+10*length+324+(logical.frames logical.top).active.card*(21*rank+60*(16*(ell+3))+190)+(SparseQueue.cleanBodyBound (16*(ell+3)) length rank+2)*(logical.frames logical.top).active.card+8 : ℕ) : ℝ≥0∞) ≤
            ((128*R^2 : ℕ) : ℝ≥0∞)*((16*(volumeNat g (logical.frames logical.top).active+1)*keyCost logical+8*(ell+2)*((logical.frames logical.top).block+2) : ℕ) : ℝ≥0∞) := by exact_mod_cast hN
        simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc,show (6 : ℝ≥0∞)+2=8 by norm_num] using hCast
      exact compiler_charge_factor_mono _ _ (128*R^2) (1024*R^2) (Nat.mul_le_mul_right (R^2) (by norm_num)) hc

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerFinishPCDom

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_finish_pc_dom (m : SolveModel) {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (ell length rank Q : ℕ) (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hStored : StoredInvariant g logical) (hPC : (logical.frames logical.top).pc=.finishEpisode) :
    controllerPCCharge m g logical ell length rank Q ≤ ((1024*(compilerOverheadBase ell length rank Q)^2 : ℕ) : ℝ≥0∞)*(stepDebit m g α ell logical).2 := by
  let R := compilerOverheadBase ell length rank Q
  have hR : 1000 ≤ R := (compiler_overhead_parameters ell length rank Q 0 (Nat.zero_le _)).1
  by_cases hA : ancestorExhausted logical
  · simp only [controllerPCCharge,controllerFinishCharge,stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hA,not_true_eq_false,if_true,mul_one]
    have hc : (72 : ℝ≥0∞) ≤ ((1024*R^2 : ℕ) : ℝ≥0∞) := by
      exact_mod_cast compiler_constant_factor_bound R 72 1024 hR (by norm_num) (by norm_num)
    norm_num at hc ⊢
    exact hc
  · by_cases hCurrent : exhausted logical logical.top
    · have hAny : anyExhausted logical := ⟨logical.top,le_rfl,hCurrent⟩
      simp only [controllerPCCharge,controllerFinishCharge,stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hA,hCurrent,hAny,not_false_eq_true,not_true_eq_false,if_true,mul_one]
      have hc : (74 : ℝ≥0∞) ≤ ((1024*R^2 : ℕ) : ℝ≥0∞) := by
        exact_mod_cast compiler_constant_factor_bound R 74 1024 hR (by norm_num) (by norm_num)
      norm_num at hc ⊢
      exact hc
    · have hAny : ¬anyExhausted logical := fun h => hCurrent ((any_exhausted_of_no_ancestor logical hA).mp h)
      have hActive := compiler_stored_active_domain g logical hStored logical.top le_rfl
      have hCard := compiler_card_le_volume g _ hActive.2
      have hPlus : (logical.frames logical.top).active.card+1 ≤ 16*(volumeNat g (logical.frames logical.top).active+1) :=
        (Nat.succ_le_succ hCard).trans (Nat.le_mul_of_pos_left _ (by norm_num))
      have hScalar := compiler_finish_scalar_bound ell length rank Q (logical.frames logical.top).active.card
      have hN := hScalar.trans (Nat.mul_le_mul_left (16*R^2) hPlus)
      have hCost : (stepDebit m g α ell logical).2=((16*(volumeNat g (logical.frames logical.top).active+1) : ℕ) : ℝ≥0∞) := by
        simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hA,hCurrent]
      rw [hCost]
      have hc : controllerPCCharge m g logical ell length rank Q ≤ ((16*R^2 : ℕ) : ℝ≥0∞)*((16*(volumeNat g (logical.frames logical.top).active+1) : ℕ) : ℝ≥0∞) := by
        calc
          _ = ((((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+144 : ℕ) : ℝ≥0∞)) := by
            simp only [controllerPCCharge,hPC,controllerFinishCharge,if_pos hA,if_pos hAny]
            push_cast
            ring
          _ ≤ _ := by exact_mod_cast hN
      exact compiler_charge_factor_mono _ _ (16*R^2) (1024*R^2) (Nat.mul_le_mul_right (R^2) (by norm_num)) hc

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerPendingChargeDom

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def compilerPendingDebit {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) : ℝ≥0∞ :=
  match pendingPush logical with
  | none => 1
  | some (t,v) => ((32*(logical.top+1)*((g.neighbors v).length+1)*keyCost (exteriorPush g α logical t v) : ℕ) : ℝ≥0∞)

lemma compiler_pending_time_charge {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (ell length rank Q extra : ℕ) (hDepth : logical.top ≤ ell) (hExtra : extra ≤ 1000) :
    let P := SparseQueue.cleanBodyBound (16*(ell+3)) length rank+2
    let T := (logical.top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
    let degree := drainDegree g logical
    let E := (logical.top+1)*(degree+1)*(42*rank+168*(16*(ell+3))+910)
    (((T+E+P*(2*(logical.top+1)*(degree+1))+extra : ℕ) : ℝ≥0∞)) ≤
      ((1024*(compilerOverheadBase ell length rank Q)^2 : ℕ) : ℝ≥0∞)*compilerPendingDebit g α logical := by
  dsimp only
  let R := compilerOverheadBase ell length rank Q
  cases hp : pendingPush logical with
  | none =>
    simp only [compilerPendingDebit,drainDegree,hp,Nat.zero_add,mul_one]
    have hScalar := compiler_queue_total_scalar_bound ell length rank Q logical.top 0 extra hDepth hExtra
    have hN := hScalar.trans (show 512*R^2*(0+1) ≤ 1024*R^2 from by
      simpa only [Nat.zero_add,Nat.mul_one] using Nat.mul_le_mul_right (R^2) (by norm_num : 512 ≤ 1024))
    simpa only [Nat.zero_add,Nat.mul_one] using (Nat.cast_le (α:=ℝ≥0∞)).mpr hN
  | some pair =>
    obtain ⟨t,v⟩ := pair
    simp only [compilerPendingDebit,drainDegree,hp]
    have hScalar := compiler_queue_total_scalar_bound ell length rank Q logical.top (g.neighbors v).length extra hDepth hExtra
    have hRow : (g.neighbors v).length+1 ≤ 32*(logical.top+1)*((g.neighbors v).length+1)*keyCost (exteriorPush g α logical t v) := by
      exact compiler_nat_scaled_bound _ _ (32*(logical.top+1)) _ le_rfl (by positivity) (by unfold keyCost; positivity)
    have hN := hScalar.trans (Nat.mul_le_mul_left (512*R^2) hRow)
    have hFinal := hN.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right (R^2) (by norm_num : 512 ≤ 1024)))
    have hc := (Nat.cast_le (α:=ℝ≥0∞)).mpr hFinal
    rw [Nat.cast_mul] at hc
    exact hc

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerAfterPCDom

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_after_pc_dom (m : SolveModel) {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (ell length rank Q : ℕ) (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hDepth : logical.top ≤ ell) (hPC : (logical.frames logical.top).pc=.afterChild) :
    controllerPCCharge m g logical ell length rank Q ≤ ((1024*(compilerOverheadBase ell length rank Q)^2 : ℕ) : ℝ≥0∞)*(stepDebit m g α ell logical).2 := by
  let R := compilerOverheadBase ell length rank Q
  have hR : 1000 ≤ R := (compiler_overhead_parameters ell length rank Q 0 (Nat.zero_le _)).1
  by_cases hA : ancestorExhausted logical
  · simp only [controllerPCCharge,controllerAfterCharge,stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hA,not_true_eq_false,if_true,mul_one]
    have hc : (72 : ℝ≥0∞) ≤ ((1024*R^2 : ℕ) : ℝ≥0∞) := by
      exact_mod_cast compiler_constant_factor_bound R 72 1024 hR (by norm_num) (by norm_num)
    norm_num at hc ⊢
    exact hc
  · by_cases hCurrent : exhausted logical logical.top
    · have hAny : anyExhausted logical := ⟨logical.top,le_rfl,hCurrent⟩
      simp only [controllerPCCharge,controllerAfterCharge,stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hA,hCurrent,hAny,not_false_eq_true,not_true_eq_false,if_true,mul_one]
      have hc : (74 : ℝ≥0∞) ≤ ((1024*R^2 : ℕ) : ℝ≥0∞) := by
        exact_mod_cast compiler_constant_factor_bound R 74 1024 hR (by norm_num) (by norm_num)
      norm_num at hc ⊢
      exact hc
    · have hAny : ¬anyExhausted logical := fun h => hCurrent ((any_exhausted_of_no_ancestor logical hA).mp h)
      have hCost : (stepDebit m g α ell logical).2=compilerPendingDebit g α logical := by
        cases hp : pendingPush logical with
        | none => simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hA,hCurrent,hAny,hp,compilerPendingDebit]
        | some pair =>
          obtain ⟨t,v⟩ := pair
          simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hA,hCurrent,hAny,hp,compilerPendingDebit]
      rw [hCost]
      let P := SparseQueue.cleanBodyBound (16*(ell+3)) length rank+2
      let T := (logical.top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
      let degree := drainDegree g logical
      let E := (logical.top+1)*(degree+1)*(42*rank+168*(16*(ell+3))+910)
      calc
        _ = (((T+E+P*(2*(logical.top+1)*(degree+1))+16 : ℕ) : ℝ≥0∞)) := by
          simp only [controllerPCCharge,hPC,controllerAfterCharge,if_pos hA,if_pos hAny,controllerDrainCharge]
          dsimp only [P,T,degree,E]
          push_cast
          ring
        _ ≤ _ := compiler_pending_time_charge g α logical ell length rank Q 16 hDepth (by norm_num)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerChargePositive

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_joint_charge_one (m : SolveModel) {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (T : Finset (Fin n)) :
    (1 : ℝ≥0∞)≤jointCost m g logical T := by
  have hN : 1≤32*(logical.top+1)*(volumeNat g T+T.card+1)*keyCost logical := by
    apply Nat.succ_le_of_lt
    unfold keyCost
    positivity
  have hc : (1 : ℝ≥0∞)≤((32*(logical.top+1)*(volumeNat g T+T.card+1)*keyCost logical : ℕ) : ℝ≥0∞) := by exact_mod_cast hN
  unfold jointCost
  exact hc.trans (le_add_of_nonneg_left (by positivity))

set_option maxHeartbeats 6000000 in
lemma compiler_step_charge_one (m : SolveModel) {n : ℕ} (g : InputGraph n) (α : ℝ) (ell : ℕ)
    (logical : RecursiveState n) (hDone : logical.done=false) : (1 : ℝ≥0∞)≤(stepDebit m g α ell logical).2 := by
  have hJ (T : Finset (Fin n)) := compiler_joint_charge_one m g logical T
  cases hp : pendingPush logical with
  | none =>
    cases hPC : (logical.frames logical.top).pc <;> simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hPC,hp,Option.isSome_none] <;>
      split_ifs <;> dsimp only
    all_goals first
      | exact le_rfl
      | exact hJ _
      | exact (hJ _).trans (le_add_of_nonneg_right (by positivity))
      | norm_cast; apply Nat.succ_le_of_lt; try unfold keyCost
        all_goals positivity
  | some pair =>
    obtain ⟨t,v⟩ := pair
    cases hPC : (logical.frames logical.top).pc <;> simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hPC,hp,Option.isSome_some] <;>
      split_ifs <;> dsimp only
    all_goals first
      | exact le_rfl
      | exact hJ _
      | exact (hJ _).trans (le_add_of_nonneg_right (by positivity))
      | norm_cast; apply Nat.succ_le_of_lt; try unfold keyCost
        all_goals positivity

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerLeafPCDom

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_leaf_pc_dom (m : SolveModel) {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (ell length rank Q : ℕ) (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hDepth : logical.top ≤ ell) (hStored : StoredInvariant g logical) (hRegion : RegionInvariant logical)
    (hPC : (logical.frames logical.top).pc=.leafDrain) :
    controllerPCCharge m g logical ell length rank Q ≤ ((1024*(compilerOverheadBase ell length rank Q)^2 : ℕ) : ℝ≥0∞)*(stepDebit m g α ell logical).2 := by
  let R := compilerOverheadBase ell length rank Q
  let P := SparseQueue.cleanBodyBound (16*(ell+3)) length rank+2
  let T := (logical.top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
  have hR : 1000 ≤ R := (compiler_overhead_parameters ell length rank Q 0 (Nat.zero_le _)).1
  have hCache := compiler_stored_cache_high_domain g logical hStored hRegion logical.top le_rfl
  by_cases hAny : anyExhausted logical
  · simp only [controllerPCCharge,stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hAny,not_true_eq_false,if_true,mul_one]
    have hc : (12 : ℝ≥0∞) ≤ ((1024*R^2 : ℕ) : ℝ≥0∞) := by
      exact_mod_cast compiler_constant_factor_bound R 12 1024 hR (by norm_num) (by norm_num)
    norm_num at hc ⊢
    exact hc
  · cases hp : pendingPush logical with
    | none =>
      have hCost : (stepDebit m g α ell logical).2=
          (if (logical.frames logical.top).high=∅ then 1 else jointCost m g logical ((logical.frames logical.top).cache ∪ (logical.frames logical.top).high)) := by
        by_cases hEmpty : (logical.frames logical.top).high=∅
        · simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hAny,hp,Option.isSome_none,if_pos hEmpty]
        · simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hAny,hp,Option.isSome_none,if_neg hEmpty,if_pos hCache]
      have hBody := compiler_leaf_time_charge m g logical ell length rank Q hDepth
      rw [←hCost] at hBody
      have hOver : T+4 ≤ 64*R^2 := compiler_priority_extra_bound ell length rank Q logical.top 4 hDepth (by norm_num)
      have hOne := compiler_step_charge_one m g α ell logical hDone
      have h := compiler_control_charge_add (leafTightCharge m g logical ell length rank Q) ((stepDebit m g α ell logical).2)
        (T+4) (64*R^2) (512*R^2) hOne hOver hBody
      have h' := compiler_charge_factor_mono _ _ (64*R^2+512*R^2) (1024*R^2) (by
        calc
          _ = 576*R^2 := by ring
          _ ≤ _ := Nat.mul_le_mul_right (R^2) (by norm_num)) h
      calc
        _ = (((T+4 : ℕ) : ℝ≥0∞))+leafTightCharge m g logical ell length rank Q := by
          simp only [controllerPCCharge,hPC,if_pos hAny,controllerPendingCharge,hp,leafControllerCharge]
          dsimp only [P,T]
          push_cast
          ring
        _ ≤ _ := h'
    | some pair =>
      obtain ⟨t,v⟩ := pair
      have hCost : (stepDebit m g α ell logical).2=compilerPendingDebit g α logical := by
        simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hAny,hp,Option.isSome_some,if_true,compilerPendingDebit]
      rw [hCost]
      let degree := drainDegree g logical
      let E := (logical.top+1)*(degree+1)*(42*rank+168*(16*(ell+3))+910)
      calc
        _ = (((T+E+P*(2*(logical.top+1)*(degree+1))+4 : ℕ) : ℝ≥0∞)) := by
          simp only [controllerPCCharge,hPC,if_pos hAny,controllerPendingCharge,hp]
          dsimp only [P,T,degree,E]
          simp only [drainDegree,hp]
          push_cast
          ring
        _ ≤ _ := compiler_pending_time_charge g α logical ell length rank Q 4 hDepth (by norm_num)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerInitialRestartPCDom

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_initial_restart_time_charge (m : SolveModel) {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (ell length rank Q noCharge : ℕ) (hNo : noCharge ≤ 22)
    (hDone : logical.done=false) (hComp : ¬componentComplete logical) (hDepth : logical.top ≤ ell)
    (hPC : (logical.frames logical.top).pc=.initialDrain ∨ (logical.frames logical.top).pc=.restartDrain) :
    initialRestartCharge g logical ell length rank (noCharge : ℝ≥0∞) ≤
      ((1024*(compilerOverheadBase ell length rank Q)^2 : ℕ) : ℝ≥0∞)*(stepDebit m g α ell logical).2 := by
  let R := compilerOverheadBase ell length rank Q
  let P := SparseQueue.cleanBodyBound (16*(ell+3)) length rank+2
  let T := (logical.top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
  have hR : 1000 ≤ R := (compiler_overhead_parameters ell length rank Q 0 (Nat.zero_le _)).1
  by_cases hA : ancestorExhausted logical
  · have hCost : (stepDebit m g α ell logical).2=1 := by
      rcases hPC with hPC|hPC <;> simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hA,if_true]
    rw [hCost,mul_one]
    simp only [initialRestartCharge,hA,not_true_eq_false,if_false]
    have hc : (12 : ℝ≥0∞) ≤ ((1024*R^2 : ℕ) : ℝ≥0∞) :=
      (Nat.cast_le (α:=ℝ≥0∞)).mpr (compiler_constant_factor_bound R 12 1024 hR (by norm_num) (by norm_num))
    norm_num at hc ⊢
    exact hc
  · cases hp : pendingPush logical with
    | none =>
      have hCost : (stepDebit m g α ell logical).2=1 := by
        rcases hPC with hPC|hPC <;> simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hA,hp,Option.isSome_none]
      rw [hCost,mul_one]
      have hOver : T+(noCharge+4) ≤ 64*R^2 := compiler_priority_extra_bound ell length rank Q logical.top (noCharge+4) hDepth (by omega)
      have hN := hOver.trans (Nat.mul_le_mul_right (R^2) (by norm_num : 64 ≤ 1024))
      calc
        _ = (((T+(noCharge+4) : ℕ) : ℝ≥0∞)) := by
          simp only [initialRestartCharge,if_pos hA,controllerPriorityCharge,hp,Option.isSome_none,Bool.false_eq_true,if_false]
          dsimp only [P,T]
          push_cast
          ring
        _ ≤ _ := (Nat.cast_le (α:=ℝ≥0∞)).mpr hN
    | some pair =>
      obtain ⟨t,v⟩ := pair
      by_cases hAny : anyExhausted logical
      · have hCost : (stepDebit m g α ell logical).2=1 := by
          rcases hPC with hPC|hPC <;> simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hA,hp,Option.isSome_some,if_true,hAny]
        rw [hCost,mul_one]
        have hOver : T+16 ≤ 64*R^2 := compiler_priority_extra_bound ell length rank Q logical.top 16 hDepth (by norm_num)
        have hN := hOver.trans (Nat.mul_le_mul_right (R^2) (by norm_num : 64 ≤ 1024))
        calc
          _ = (((T+16 : ℕ) : ℝ≥0∞)) := by
            simp only [initialRestartCharge,if_pos hA,controllerPriorityCharge,hp,Option.isSome_some,if_true,hAny,not_true_eq_false,if_false]
            dsimp only [P,T]
            push_cast
            ring
          _ ≤ _ := (Nat.cast_le (α:=ℝ≥0∞)).mpr hN
      · have hCost : (stepDebit m g α ell logical).2=compilerPendingDebit g α logical := by
          rcases hPC with hPC|hPC <;> simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hComp,hPC,hA,hp,Option.isSome_some,if_true,hAny,compilerPendingDebit]
        rw [hCost]
        let degree := drainDegree g logical
        let E := (logical.top+1)*(degree+1)*(42*rank+168*(16*(ell+3))+910)
        calc
          _ = (((T+E+P*(2*(logical.top+1)*(degree+1))+6 : ℕ) : ℝ≥0∞)) := by
            simp only [initialRestartCharge,if_pos hA,controllerPriorityCharge,hp,Option.isSome_some,if_true,if_pos hAny,selectedExteriorCharge]
            dsimp only [P,T,E,degree]
            simp only [drainDegree,hp]
            push_cast
            ring
          _ ≤ _ := compiler_pending_time_charge g α logical ell length rank Q 6 hDepth (by norm_num)

lemma compiler_initial_restart_pc_dom (m : SolveModel) {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (ell length rank Q : ℕ) (hDone : logical.done=false) (hComp : ¬componentComplete logical) (hDepth : logical.top ≤ ell)
    (hPC : (logical.frames logical.top).pc=.initialDrain ∨ (logical.frames logical.top).pc=.restartDrain) :
    controllerPCCharge m g logical ell length rank Q ≤ ((1024*(compilerOverheadBase ell length rank Q)^2 : ℕ) : ℝ≥0∞)*(stepDebit m g α ell logical).2 := by
  rcases hPC with hPC|hPC
  · simp only [controllerPCCharge,hPC]
    exact compiler_initial_restart_time_charge m g α logical ell length rank Q 22 (by norm_num) hDone hComp hDepth (Or.inl hPC)
  · simp only [controllerPCCharge,hPC]
    exact compiler_initial_restart_time_charge m g α logical ell length rank Q 20 (by norm_num) hDone hComp hDepth (Or.inr hPC)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerOverallChargeBound

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma compiler_dispatch_overhead_bound (ell length rank Q top : ℕ) (pc : NormalizePC) (hTop : top ≤ ell) :
    76*(top+1)+25+(3*normalizePCNumber pc+2)+10 ≤ 128*(compilerOverheadBase ell length rank Q)^2 := by
  let R := compilerOverheadBase ell length rank Q
  obtain ⟨hR,hw,hL,hl,hr,hQ,hP⟩ := compiler_overhead_parameters ell length rank Q top hTop
  change 1000 ≤ R at hR
  change top+1 ≤ R at hL
  have hPC : normalizePCNumber pc ≤ 9 := by cases pc <;> decide
  have hSq : R ≤ R^2 := by nlinarith
  nlinarith

lemma compiler_body_charge_bound (m : SolveModel) {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (ell length rank Q : ℕ) (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hPC : ¬componentComplete logical → controllerPCCharge m g logical ell length rank Q ≤
      ((1024*(compilerOverheadBase ell length rank Q)^2 : ℕ) : ℝ≥0∞)*(stepDebit m g α ell logical).2) :
    controllerBodyCharge m g logical ell length rank Q+2 ≤
      ((compilerOverheadFactor ell length rank Q : ℕ) : ℝ≥0∞)*(stepDebit m g α ell logical).2 := by
  let R := compilerOverheadBase ell length rank Q
  let cost := (stepDebit m g α ell logical).2
  have hR : 1000 ≤ R := (compiler_overhead_parameters ell length rank Q 0 (Nat.zero_le _)).1
  have hOne : 1 ≤ cost := compiler_step_charge_one m g α ell logical hDone
  by_cases hComp : componentComplete logical
  · have hCost : jointCost m g logical (logical.frames 0).active ≤ cost := by
      change _ ≤ (stepDebit m g α ell logical).2
      simp only [stepDebit,hDone,Bool.false_eq_true,if_false,hComp,if_true]
      exact le_add_of_nonneg_right (by positivity)
    have hBody : controllerComponentCharge m g logical ell ≤ ((256*R^2 : ℕ) : ℝ≥0∞)*cost :=
      (compiler_component_time_charge m g logical ell length rank Q).trans (mul_le_mul_of_nonneg_left hCost (by positivity))
    have h := compiler_control_charge_add (controllerComponentCharge m g logical ell) cost 10 (128*R^2) (256*R^2) hOne (compiler_constant_factor_bound R 10 128 hR (by norm_num) (by norm_num)) hBody
    have h' := compiler_charge_factor_mono _ cost (128*R^2+256*R^2) (4096*R^2) (by
      calc
        _ = (128+256)*R^2 := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)) h
    calc
      _ = (10 : ℝ≥0∞)+controllerComponentCharge m g logical ell := by simp only [controllerBodyCharge,if_pos hComp]; ring
      _ ≤ _ := h'
  · let extra := 76*(logical.top+1)+25+(3*normalizePCNumber (logical.frames logical.top).pc+2)+10
    have hOver : extra ≤ 128*R^2 := compiler_dispatch_overhead_bound ell length rank Q logical.top (logical.frames logical.top).pc hDepth
    have h := compiler_control_charge_add (controllerPCCharge m g logical ell length rank Q) cost extra (128*R^2) (1024*R^2) hOne hOver (hPC hComp)
    have h' := compiler_charge_factor_mono _ cost (128*R^2+1024*R^2) (4096*R^2) (by
      calc
        _ = (128+1024)*R^2 := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)) h
    calc
      _ = (extra : ℝ≥0∞)+controllerPCCharge m g logical ell length rank Q := by
        simp only [controllerBodyCharge,if_neg hComp,controllerOrdinaryCharge,extra]
        push_cast
        ring
      _ ≤ _ := h'

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerPCChargeBound

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_pc_charge_bound (m : SolveModel) {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (ell length rank Q : ℕ) (hDone : logical.done=false) (hComp : ¬componentComplete logical)
    (hDepth : logical.top ≤ ell) (hStored : StoredInvariant g logical) (hRegion : RegionInvariant logical) :
    controllerPCCharge m g logical ell length rank Q ≤ ((1024*(compilerOverheadBase ell length rank Q)^2 : ℕ) : ℝ≥0∞)*(stepDebit m g α ell logical).2 := by
  cases hPC : (logical.frames logical.top).pc
  · exact compiler_initial_restart_pc_dom m g α logical ell length rank Q hDone hComp hDepth (Or.inl hPC)
  · exact compiler_begin_pc_dom m g α logical ell length rank Q hDone hComp hDepth hStored hPC
  · exact compiler_full_pc_dom m g α logical ell length rank Q hDone hComp hDepth hStored hPC
  · exact compiler_normalize_pc_dom m g α logical ell length rank Q hDone hComp hDepth hStored hPC
  · exact compiler_leaf_pc_dom m g α logical ell length rank Q hDone hComp hDepth hStored hRegion hPC
  · exact compiler_after_pc_dom m g α logical ell length rank Q hDone hComp hDepth hPC
  · exact compiler_finish_pc_dom m g α logical ell length rank Q hDone hComp hStored hPC
  · exact compiler_initial_restart_pc_dom m g α logical ell length rank Q hDone hComp hDepth (Or.inr hPC)
  · exact compiler_return_pc_dom m g α logical ell length rank Q hDone hComp (Or.inl hPC)
  · exact compiler_return_pc_dom m g α logical ell length rank Q hDone hComp (Or.inr hPC)

lemma compiler_body_charge_comparison (m : SolveModel) {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (ell length rank Q : ℕ) (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hStored : StoredInvariant g logical) (hRegion : RegionInvariant logical) :
    controllerBodyCharge m g logical ell length rank Q+2 ≤
      ((compilerOverheadFactor ell length rank Q : ℕ) : ℝ≥0∞)*(stepDebit m g α ell logical).2 :=
  compiler_body_charge_bound m g α logical ell length rank Q hDone hDepth
    (fun hComp => compiler_pc_charge_bound m g α logical ell length rank Q hDone hComp hDepth hStored hRegion)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerSourceRunCertified

set_option autoImplicit false
set_option maxRecDepth 20000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 12000000 in
lemma controller_source_run_certified (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε E : ℝ) (ell length N rank Q : ℕ)
    (hα : 0<α ∧ α≤1/2) (hε : 0<ε ∧ ε≤1) (hs : 0<g.graph.degree s)
    (hBound : recursiveWork m g s α ε ell [] ≤ ENNReal.ofReal E)
    (hWide : ((8*(ell+1) : ℕ) : ℝ≥0∞)*ENNReal.ofReal E ≤ (N : ℝ≥0∞))
    (hTermination : ∃ t, (recursiveRun m g s α (rootThreshold ε ell) ell [] t).done=true)
    (hCredit : 4*(16*(ell+3))+17 ≤ Q) (hCap : rank<length) (hPow : N<2^rank)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length
      (recursiveInit g s (rootThreshold ε ell) ell []) st) (hM : memory.mass ≤ 1) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    let F := compilerOverheadFactor ell length rank Q
    ∃ steps out, MachineEval m g ω recursiveControllerCode st steps out ∧
      (∀ v : Fin n, 0 ≤ outputVector out.output v) ∧ ACL g.graph α ε s (outputVector out.output) ∧
      out.work ≤ st.work+(P : ℝ≥0∞)+(F : ℝ≥0∞)*ENNReal.ofReal E+1 := by
  dsimp only
  let F := compilerOverheadFactor ell length rank Q
  have he : 0<ε := hε.1
  have hq : 0<rootThreshold ε ell := by unfold rootThreshold kappa; positivity
  have hα' : 0<α ∧ α<1 := ⟨hα.1,by linarith [hα.2]⟩
  have hDom : ∀ k, (recursiveRun m g s α (rootThreshold ε ell) ell [] k).done=false →
      controllerBodyCharge m g (recursiveRun m g s α (rootThreshold ε ell) ell [] k) ell length rank Q+2 ≤
        (F : ℝ≥0∞)*(stepDebit m g α ell (recursiveRun m g s α (rootThreshold ε ell) ell [] k)).2 := by
    intro k hDone
    obtain ⟨hRegion,hDepth,hKeys,hParameters,hStored,hBudget,hNumerical,hBoundary⟩ := compiler_run_invariants m g s α (rootThreshold ε ell) hα' hq hs ell [] k
    exact compiler_body_charge_comparison m g α _ ell length rank Q hDone hDepth hStored hRegion
  obtain ⟨u,out,ex,hNonnegative,hACL,hWork⟩ := controller_source_run_work_exec m g ω s α ε E ell length N rank Q (F : ℝ≥0∞)
    hα hε hs hBound hWide hTermination hDom hCredit hCap hPow st memory hM
  exact ⟨u,out,ex,hNonnegative,hACL,hWork.trans (add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hBound (by positivity : (0 : ℝ≥0∞) ≤ (F : ℝ≥0∞)))) le_rfl)⟩

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution : ∀ (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε E : ℝ) (ell length N rank Q : ℕ)
    (hα : 0<α ∧ α≤1/2) (hε : 0<ε ∧ ε≤1) (hs : 0<g.graph.degree s)
    (hBound : recursiveWork m g s α ε ell [] ≤ ENNReal.ofReal E)
    (hWide : ((8*(ell+1) : ℕ) : ℝ≥0∞)*ENNReal.ofReal E ≤ (N : ℝ≥0∞))
    (hTermination : ∃ t, (recursiveRun m g s α (rootThreshold ε ell) ell [] t).done=true)
    (hCredit : 4*(16*(ell+3))+17 ≤ Q) (hCap : rank<length) (hPow : N<2^rank)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length
      (recursiveInit g s (rootThreshold ε ell) ell []) st) (hM : memory.mass ≤ 1),
let P := cleanBodyBound (16*(ell+3)) length rank+2
    let F := compilerOverheadFactor ell length rank Q
    ∃ steps out, MachineEval m g ω recursiveControllerCode st steps out ∧
      (∀ v : Fin n, 0 ≤ outputVector out.output v) ∧ ACL g.graph α ε s (outputVector out.output) ∧
      out.work ≤ st.work+(P : ℝ≥0∞)+(F : ℝ≥0∞)*ENNReal.ofReal E+1 := by
  exact @NearlyOptimalPPR.Computation.controller_source_run_certified
