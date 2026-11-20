-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.controller_pc_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:30:47.365178+00:00
-- url     : https://prove2.me/submissions/b757d119-ed70-4ef0-9611-f3479e348e11

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
import Theorems.Thm_NearlyOptimalPPR_Computation_begin_episode_exec
import Theorems.Thm_NearlyOptimalPPR_Computation_exterior_push_exec
import Theorems.Thm_NearlyOptimalPPR_Computation_finish_episode_exec
import Theorems.Thm_NearlyOptimalPPR_Computation_fresh_child_simulation
import Theorems.Thm_NearlyOptimalPPR_Computation_leaf_joint_solve_exec
import Theorems.Thm_NearlyOptimalPPR_Computation_list_joint_solve_exec
import Theorems.Thm_NearlyOptimalPPR_Computation_normalization_composes
import Theorems.Thm_NearlyOptimalPPR_Computation_priority_exec
import Theorems.Thm_NearlyOptimalPPR_Computation_push_correctness_work
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_level_work
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_residual_error
import Theorems.Thm_NearlyOptimalPPR_Computation_root_sparse_output_exec
set_option linter.all false
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

lemma compiler_raw_active {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) (δ : ℝ) (i : ℕ) :
    ((rawExterior g α st t v δ).frames i).active=(st.frames i).active := by
  classical
  by_cases hi : i ≤ st.top <;> simp [rawExterior,hi]

lemma compiler_raw_domain {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) (δ : ℝ) (i : ℕ) :
    parentDomain (rawExterior g α st t v δ) i=parentDomain st i := by
  unfold parentDomain
  split_ifs
  · rfl
  · exact compiler_raw_active g α st t v δ (i-1)

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

def compilerStaticFields {n : ℕ} (f : NormalizeFrame n) :=
  (f.N,f.q,f.Q,f.theta,f.block,f.pc,f.openBudget,f.needFull,f.childrenThisEpisode,f.cache)

lemma compiler_raw_static {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) (δ : ℝ) (i : ℕ) :
    compilerStaticFields ((rawExterior g α st t v δ).frames i)=compilerStaticFields (st.frames i) := by
  classical
  by_cases hi : i ≤ st.top <;> simp [compilerStaticFields,rawExterior,hi]

lemma compiler_admit_static {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) (i : ℕ) :
    compilerStaticFields ((admitStage g st t v).frames i)=compilerStaticFields (st.frames i) := by
  classical
  let a := changeFrame st t (fun fi =>
    {fi with
      active := insert v fi.active
      residual := Function.update fi.residual v (fi.residual v+(st.frames t).q*LocalPush.deg g.graph v/2)
      W := fi.W + if fi.openBudget then (t+3 : ℕ)*(st.frames t).q*LocalPush.deg g.graph v/2 else 0})
  let b := if t < st.top then changeFrame a (t+1) (fun fc =>
    {fc with
      reference := Function.update fc.reference v (a.x v)
      residual := Function.update fc.residual v ((a.frames t).residual v)}) else a
  let c := if t = 0 then {b with boundaryEdges := st.boundaryEdges+(g.neighbors v).length-
    2*((g.neighbors v).filter (fun w => w ∈ (st.frames t).active)).length} else b
  have hdef : admitStage g st t v = c := rfl
  have hbtop : b.top = st.top := by unfold b; split <;> rfl
  have hbx : b.x = st.x := by unfold b; split <;> rfl
  have hframes : (admitStage g st t v).frames = b.frames := by
    rw [hdef]
    unfold c
    split <;> rfl
  rw [hframes]
  by_cases hc : t < st.top <;> by_cases hit : i = t <;> by_cases hic : i = t+1 <;>
    simp [b,hc,a,changeFrame,hit,hic,compilerStaticFields]

lemma compiler_refresh_static {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (i : ℕ) :
    compilerStaticFields ((refreshKeys g st T).frames i)=compilerStaticFields (st.frames i) := by
  classical
  by_cases hi : i ≤ st.top <;> simp [compilerStaticFields,refreshKeys,hi]

lemma compiler_admit_top {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    (admitStage g st t v).top=st.top := by
  unfold admitStage
  split_ifs <;> rfl

lemma compiler_exterior_static {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) (i : ℕ) :
    compilerStaticFields ((exteriorPush g α st t v).frames i)=compilerStaticFields (st.frames i) := by
  classical
  rw [compiler_exterior_stages]
  change compilerStaticFields ((refreshKeys g _ _).frames i)=_
  rw [compiler_refresh_static]
  split_ifs
  · rw [compiler_admit_static,compiler_raw_static]
  · exact compiler_raw_static g α st t v _ i

lemma compiler_exterior_top {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    (exteriorPush g α st t v).top=st.top := by
  classical
  rw [compiler_exterior_stages]
  change RecursiveState.top ((if _ then _ else _) : RecursiveState n)=_
  split_ifs
  · rw [compiler_admit_top]
    rfl
  · rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerAdmissionViews

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma compiler_admit_stage_fields (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    let u := admitStage g st t v
    u.top = st.top ∧ u.x = st.x ∧
      (∀ i, (u.frames i).q = (st.frames i).q) ∧
      (∀ i, (u.frames i).theta = (st.frames i).theta) ∧
      (∀ i, (u.frames i).cache = (st.frames i).cache) ∧
      (∀ i, (u.frames i).active = if i = t then insert v (st.frames i).active else (st.frames i).active) ∧
      (∀ i w, (u.frames i).reference w =
        if t < st.top ∧ i = t+1 ∧ w = v then st.x v else (st.frames i).reference w) ∧
      (∀ i w, (u.frames i).residual w =
        if t < st.top ∧ i = t+1 ∧ w = v then
          (st.frames t).residual v+(st.frames t).q*LocalPush.deg g.graph v/2
        else (st.frames i).residual w+
          if i = t ∧ w = v then (st.frames t).q*LocalPush.deg g.graph v/2 else 0) := by
  classical
  dsimp only
  let a := changeFrame st t (fun fi =>
    {fi with
      active := insert v fi.active
      residual := Function.update fi.residual v (fi.residual v+(st.frames t).q*LocalPush.deg g.graph v/2)
      W := fi.W + if fi.openBudget then (t+3 : ℕ)*(st.frames t).q*LocalPush.deg g.graph v/2 else 0})
  let b := if t < st.top then changeFrame a (t+1) (fun fc =>
    {fc with
      reference := Function.update fc.reference v (a.x v)
      residual := Function.update fc.residual v ((a.frames t).residual v)}) else a
  let c := if t = 0 then {b with boundaryEdges := st.boundaryEdges+(g.neighbors v).length-
    2*((g.neighbors v).filter (fun w => w ∈ (st.frames t).active)).length} else b
  have hdef : admitStage g st t v = c := rfl
  have hbtop : b.top = st.top := by unfold b; split <;> rfl
  have hbx : b.x = st.x := by unfold b; split <;> rfl
  have hframes : (admitStage g st t v).frames = b.frames := by
    rw [hdef]
    unfold c
    split <;> rfl
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hdef]
    unfold c
    split <;> exact hbtop
  · rw [hdef]
    unfold c
    split <;> exact hbx
  · intro i
    rw [hframes]
    by_cases hc : t < st.top <;> by_cases hit : i = t <;> by_cases hic : i = t+1 <;>
      simp [b,hc,a,changeFrame,hit,hic]
  · intro i
    rw [hframes]
    by_cases hc : t < st.top <;> by_cases hit : i = t <;> by_cases hic : i = t+1 <;>
      simp [b,hc,a,changeFrame,hit,hic]
  · intro i
    rw [hframes]
    by_cases hc : t < st.top <;> by_cases hit : i = t <;> by_cases hic : i = t+1 <;>
      simp [b,hc,a,changeFrame,hit,hic]
  · intro i
    rw [hframes]
    by_cases hc : t < st.top <;> by_cases hit : i = t <;> by_cases hic : i = t+1 <;>
      simp [b,hc,a,changeFrame,hit,hic]
  · intro i w
    rw [hframes]
    by_cases hc : t < st.top <;> by_cases hit : i = t <;>
      by_cases hic : i = t+1 <;> by_cases hw : w = v <;>
      simp [b,hc,a,changeFrame,Function.update_apply,hit,hic,hw]
  · intro i w
    rw [hframes]
    by_cases hc : t < st.top <;> by_cases hit : i = t <;>
      by_cases hic : i = t+1 <;> by_cases hw : w = v <;>
      simp [b,hc,a,changeFrame,Function.update_apply,hit,hic,hw]

lemma compiler_admit_domain (g : InputGraph n) (st : RecursiveState n) (t i : ℕ) (v w : Fin n) :
    w ∈ parentDomain (admitStage g st t v) i ↔
      w ∈ parentDomain st i ∨ i = t+1 ∧ w = v := by
  classical
  have hA := (compiler_admit_stage_fields g st t v).2.2.2.2.2.1
  unfold parentDomain
  by_cases hz : i = 0
  · subst i
    simp
  · simp only [hz,ite_false]
    rw [hA]
    by_cases he : i = t+1
    · subst i
      simp [or_comm]
    · have hn : i-1 ≠ t := by omega
      simp [hn,he]


end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerExteriorQueueViews

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def compilerQueueFields {n : ℕ} (f : NormalizeFrame n) := (f.exterior,f.high)

lemma compiler_admit_queues {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) (i : ℕ) :
    compilerQueueFields ((admitStage g st t v).frames i)=compilerQueueFields (st.frames i) := by
  classical
  let a := changeFrame st t (fun fi =>
    {fi with
      active := insert v fi.active
      residual := Function.update fi.residual v (fi.residual v+(st.frames t).q*LocalPush.deg g.graph v/2)
      W := fi.W + if fi.openBudget then (t+3 : ℕ)*(st.frames t).q*LocalPush.deg g.graph v/2 else 0})
  let b := if t < st.top then changeFrame a (t+1) (fun fc =>
    {fc with
      reference := Function.update fc.reference v (a.x v)
      residual := Function.update fc.residual v ((a.frames t).residual v)}) else a
  let c := if t = 0 then {b with boundaryEdges := st.boundaryEdges+(g.neighbors v).length-
    2*((g.neighbors v).filter (fun w => w ∈ (st.frames t).active)).length} else b
  have hdef : admitStage g st t v = c := rfl
  have hbtop : b.top = st.top := by unfold b; split <;> rfl
  have hbx : b.x = st.x := by unfold b; split <;> rfl
  have hframes : (admitStage g st t v).frames = b.frames := by
    rw [hdef]
    unfold c
    split <;> rfl
  rw [hframes]
  by_cases hc : t < st.top <;> by_cases hit : i = t <;> by_cases hic : i = t+1 <;>
    simp [b,hc,a,changeFrame,hit,hic,compilerQueueFields]

lemma compiler_raw_queues {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) (δ : ℝ) (i : ℕ) :
    compilerQueueFields ((rawExterior g α st t v δ).frames i)=compilerQueueFields (st.frames i) := by
  classical
  by_cases hi : i ≤ st.top <;> simp [rawExterior,compilerQueueFields,hi]

lemma compiler_refresh_queues_outside {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (i : ℕ) (v : Fin n) (hv : v ∉ T) :
    (v ∈ ((refreshKeys g st T).frames i).exterior ↔ v ∈ (st.frames i).exterior) ∧
    (v ∈ ((refreshKeys g st T).frames i).high ↔ v ∈ (st.frames i).high) := by
  classical
  by_cases hi : i ≤ st.top <;> simp [refreshKeys,hi,hv]

lemma compiler_exterior_queues_outside {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v w : Fin n)
    (hw : w ∉ insert v (g.neighbors v).toFinset) (i : ℕ) :
    (w ∈ ((exteriorPush g α st t v).frames i).exterior ↔ w ∈ (st.frames i).exterior) ∧
    (w ∈ ((exteriorPush g α st t v).frames i).high ↔ w ∈ (st.frames i).high) := by
  classical
  rw [compiler_exterior_stages]
  change (w ∈ ((refreshKeys g _ _).frames i).exterior ↔ _) ∧ (w ∈ ((refreshKeys g _ _).frames i).high ↔ _)
  rw [(compiler_refresh_queues_outside g _ _ i w hw).1,(compiler_refresh_queues_outside g _ _ i w hw).2]
  split_ifs
  · let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v)) (3*(st.frames t).q/8-relative st t v)
    have ha := compiler_admit_queues g (rawExterior g α st t v δ) t v i
    have hr := compiler_raw_queues g α st t v δ i
    have h := ha.trans hr
    have he := congrArg Prod.fst h
    have hh := congrArg Prod.snd h
    exact ⟨by rw [show ((admitStage g _ t v).frames i).exterior=(st.frames i).exterior from he],
      by rw [show ((admitStage g _ t v).frames i).high=(st.frames i).high from hh]⟩
  · let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v)) (3*(st.frames t).q/8-relative st t v)
    have h := compiler_raw_queues g α st t v δ i
    have he := congrArg Prod.fst h
    have hh := congrArg Prod.snd h
    exact ⟨by rw [show ((rawExterior g α st t v _).frames i).exterior=(st.frames i).exterior from he],
      by rw [show ((rawExterior g α st t v _).frames i).high=(st.frames i).high from hh]⟩

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

lemma compiler_raw_outside {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ)
    (v w : Fin n) (δ : ℝ) (hw : w ∉ insert v (g.neighbors v).toFinset) (i : ℕ) :
    ((rawExterior g α st t v δ).frames i).residual w=(st.frames i).residual w ∧
      ((rawExterior g α st t v δ).frames i).reference w=(st.frames i).reference w := by
  classical
  have hne : w ≠ v := by intro h; subst w; simp at hw
  have hn : ¬g.graph.Adj w v := by
    intro h
    have hm : w ∈ g.neighbors v := (g.correct v w).mpr (g.graph.adj_symm h)
    exact hw (Finset.mem_insert_of_mem (List.mem_toFinset.mpr hm))
  by_cases hi : i ≤ st.top <;> simp [rawExterior,hi,hne,hn]

lemma compiler_admit_outside {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (t : ℕ)
    (v w : Fin n) (hw : w ≠ v) (i : ℕ) :
    (w ∈ parentDomain (admitStage g st t v) i ↔ w ∈ parentDomain st i) ∧
      (w ∈ ((admitStage g st t v).frames i).active ↔ w ∈ (st.frames i).active) ∧
      ((admitStage g st t v).frames i).residual w=(st.frames i).residual w ∧
      ((admitStage g st t v).frames i).reference w=(st.frames i).reference w := by
  classical
  obtain ⟨_,_,_,_,_,ha,href,hr⟩ := compiler_admit_stage_fields g st t v
  refine ⟨?_,?_,?_,?_⟩
  · simp only [compiler_admit_domain,hw,and_false,or_false]
  · rw [ha]
    split_ifs <;> simp [hw]
  · rw [hr]
    simp [hw]
  · rw [href]
    simp [hw]

lemma compiler_exterior_outside {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ)
    (v w : Fin n) (hw : w ∉ insert v (g.neighbors v).toFinset) (i : ℕ) :
    (w ∈ parentDomain (exteriorPush g α st t v) i ↔ w ∈ parentDomain st i) ∧
      (w ∈ ((exteriorPush g α st t v).frames i).active ↔ w ∈ (st.frames i).active) ∧
      ((exteriorPush g α st t v).frames i).residual w=(st.frames i).residual w ∧
      ((exteriorPush g α st t v).frames i).reference w=(st.frames i).reference w := by
  classical
  let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v)) (3*(st.frames t).q/8-relative st t v)
  let base := rawExterior g α st t v δ
  have hne : w ≠ v := by intro h; subst w; simp at hw
  have hb := compiler_raw_outside g α st t v w δ hw i
  rw [compiler_exterior_stages]
  change (w ∈ parentDomain (refreshKeys g _ _) i ↔ _) ∧
    (w ∈ ((refreshKeys g _ _).frames i).active ↔ _) ∧
    ((refreshKeys g _ _).frames i).residual w=_ ∧ ((refreshKeys g _ _).frames i).reference w=_
  rw [compiler_refresh_domain,(compiler_refresh_numeric g _ _ i).2.2.2.1,
    (compiler_refresh_numeric g _ _ i).1,(compiler_refresh_numeric g _ _ i).2.2.1]
  split_ifs
  · obtain ⟨hd,ha,hr,href⟩ := compiler_admit_outside g base t v w hne i
    rw [hd,ha,hr,href,compiler_raw_domain,compiler_raw_active]
    exact ⟨Iff.rfl,Iff.rfl,hb.1,hb.2⟩
  · rw [compiler_raw_domain,compiler_raw_active]
    exact ⟨Iff.rfl,Iff.rfl,hb.1,hb.2⟩

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
lemma levelHeaderRealLoadCode_wellFormed (slot : ℕ) : (levelHeaderRealLoadCode slot).wellFormed := by
  refine ⟨levelHeaderAddressCode_wellFormed slot,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma levelHeaderRealStoreCode_wellFormed (slot : ℕ) : (levelHeaderRealStoreCode slot).wellFormed := by
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

lemma heapDrainBodyCode_wellFormed : heapDrainBodyCode.wellFormed := by
  simp only [heapDrainBodyCode,sequenceCode,List.foldr,MachineCode.wellFormed]
  exact ⟨heapDrainPrefixCode_wellFormed,heapDetachCode_wellFormed,heapCarryCode_wellFormed,trivial⟩

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

lemma heapDeletePrepareCode_wellFormed : heapDeletePrepareCode.wellFormed := by
  simp [heapDeletePrepareCode,heapDeletePrefixRoutine,PointerRoutine.sequence,PointerRoutine.code,
    PointerOp.instruction,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma heapDeleteOccupiedCode_wellFormed : heapDeleteOccupiedCode.wellFormed :=
  ⟨heapDeletePrepareCode_wellFormed,heapDrainBodyCode_wellFormed⟩

lemma heapPopCode_wellFormed : heapPopCode.wellFormed :=
  ⟨heapMinScanCode_wellFormed,trivial,heapDeleteOccupiedCode_wellFormed⟩

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

lemma vertexFlagClearCode_wellFormed : vertexFlagClearCode.wellFormed := by
  simp [vertexFlagClearCode,vertexIntegerStoreCode,vertexAddressCode_wellFormed,
    coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

-- Proof module: Solutions.HighQueueMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section


lemma highBoolean_positive {n : ℕ} {I : ℤ → ℤ} {R : ℤ → ℝ} {width levelBase : ℕ}
    {theta : ℝ} {domain : Finset (Fin n)} (h : HighBooleanRecords I R width levelBase theta domain)
    {v : Fin n} (hv : v ∈ domain) :
    0 < R (vertexRecordAddress width v.val (levelBase+4)) ↔
      I (vertexRecordAddress width v.val (levelBase+2)) ≠ 0 ∧
      3*theta*(I (vertexRecordAddress width v.val 0) : ℝ) ≤ R (vertexRecordAddress width v.val (levelBase+1)) := by
  rw [h v hv]
  split_ifs <;> simp_all

lemma high_queue_as_exterior {n : ℕ} {I : ℤ → ℤ} {R : ℤ → ℝ} {width levelBase : ℕ}
    {theta : ℝ} {domain : Finset (Fin n)} {valid queued : Finset ℕ}
    (hBool : HighBooleanRecords I R width levelBase theta domain)
    (hZero : ∀ v ∈ domain, I (vertexRecordAddress width v.val (levelBase+5))=0)
    (hQueued : queued ⊆ domain.image Fin.val) (hFlags : QueuedFlags I width (levelBase+6) domain queued)
    (hValid : ∀ v ∈ domain, v.val ∈ valid ↔ I (vertexRecordAddress width v.val (levelBase+2)) ≠ 0 ∧
      3*theta*(I (vertexRecordAddress width v.val 0) : ℝ) ≤ R (vertexRecordAddress width v.val (levelBase+1))) :
    ExteriorQueueMemory I R width (levelBase+3) (levelBase+6) 0 domain valid queued := by
  refine ⟨hQueued,hFlags,?_,?_⟩
  · intro v hv
    change 0 ≤ I (vertexRecordAddress width v.val (levelBase+5))
    rw [hZero v hv]
  · intro v hv
    change v.val ∈ valid ↔ I (vertexRecordAddress width v.val (levelBase+5))=0 ∧
      (0 : ℝ)*(I (vertexRecordAddress width v.val 0) : ℝ) < R (vertexRecordAddress width v.val (levelBase+4))
    rw [hZero v hv,zero_mul]
    simp only [true_and]
    exact (hValid v hv).trans (highBoolean_positive hBool hv).symm

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerExteriorNonactivation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_exterior_scalar_parameters {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (i : ℕ) :
    ((exteriorPush g α st t v).frames i).q=(st.frames i).q ∧
      ((exteriorPush g α st t v).frames i).theta=(st.frames i).theta := by
  have h := compiler_exterior_static g α st t v i
  exact ⟨congrArg (fun x => x.2.1) h,congrArg (fun x => x.2.2.2.1) h⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerExteriorKeys

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma refresh_keys_inside {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (i : ℕ) (hi : i ≤ st.top) (v : Fin n) (hv : v ∈ T) :
    (v ∈ ((refreshKeys g st T).frames i).exterior ↔ exteriorKey g (refreshKeys g st T) i v) ∧
    (v ∈ ((refreshKeys g st T).frames i).high ↔ highKey g (refreshKeys g st T) i v) := by
  rw [(refresh_key_predicates g st T i v).1,(refresh_key_predicates g st T i v).2]
  simp [refreshKeys,hi,hv,exteriorKey,highKey]

set_option maxHeartbeats 7000000 in
lemma compiler_exterior_keys {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (t : ℕ) (v : Fin n) (hKeys : KeysInvariant g logical) : KeysInvariant g (exteriorPush g α logical t v) := by
  classical
  let δ := min ((logical.frames t).residual v/(5*LocalPush.deg g.graph v))
    (3*(logical.frames t).q/8-relative logical t v)
  let raw := rawExterior g α logical t v δ
  let prepared := if relative logical t v+δ=3*(logical.frames t).q/8 then admitStage g raw t v else raw
  let T := insert v (g.neighbors v).toFinset
  have hFinal := compiler_exterior_stages g α logical t v
  change exteriorPush g α logical t v=debit (refreshKeys g prepared T) t _ at hFinal
  have hTop := compiler_exterior_top g α logical t v
  have hPrepTop : prepared.top=logical.top := by rw [hFinal] at hTop; exact hTop
  intro i hi
  have hi' : i ≤ logical.top := by rw [hTop] at hi; exact hi
  have parameters := compiler_exterior_scalar_parameters g α logical t v i
  constructor
  · intro w
    by_cases hw : w ∈ T
    · rw [hFinal]
      exact (refresh_keys_inside g prepared T i (by rw [hPrepTop]; exact hi') w hw).1
    · have outside := compiler_exterior_outside g α logical t v w hw i
      rw [(compiler_exterior_queues_outside g α logical t v w hw i).1,(hKeys i hi').1 w]
      simp only [exteriorKey,outside.1,outside.2.1,outside.2.2.1,parameters.1]
  · intro w
    by_cases hw : w ∈ T
    · rw [hFinal]
      exact (refresh_keys_inside g prepared T i (by rw [hPrepTop]; exact hi') w hw).2
    · have outside := compiler_exterior_outside g α logical t v w hw i
      rw [(compiler_exterior_queues_outside g α logical t v w hw i).2,(hKeys i hi').2 w]
      simp only [highKey,outside.2.1,outside.2.2.1,parameters.2]

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

lemma compiler_pending_boundary_nonnegative {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hRegion : RegionInvariant st) (hBoundary : BoundaryIdentity g st)
    (t : ℕ) (v : Fin n) (hp : pendingPush st=some (t,v)) :
    0 ≤ (exteriorPush g α st t v).boundaryEdges := by
  have hNext := compiler_source_boundary_pending g α st t v hRegion hBoundary hp
  rw [show (exteriorPush g α st t v).boundaryEdges=graphCut g ((exteriorPush g α st t v).frames 0).active from hNext]
  exact compiler_source_graphCut_nonneg g _

lemma compiler_prune_outside {n : ℕ} (g : InputGraph n) (st : RecursiveState n)
    (hNumerical : NumericalInvariant g st) :
    ∀ v ∉ (st.frames 0).active, prune (st.frames 0).q st.x v=0 := by
  intro v hv
  have h := ((hNumerical 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).2.2.2 hv
  have hX : st.x v < 3*(st.frames 0).q/8 := by simpa [relative] using h
  exact max_eq_right (sub_nonpos.mpr hX.le)

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

lemma spawnChild_child {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n) :
    (spawnChildState g ell logical).frames (logical.top+1)=
      freshFrame g [] ell (logical.top+1) logical.nextId (logical.frames logical.top).block
        (logical.frames logical.top).theta (logical.frames logical.top).active logical.x
        (logical.frames logical.top).residual := by simp [spawnChildState]

lemma spawnChild_parent {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n) :
    (spawnChildState g ell logical).frames logical.top={logical.frames logical.top with
      pc := .afterChild,childrenThisEpisode := (logical.frames logical.top).childrenThisEpisode+1} := by
  simp [spawnChildState,changeFrame,debit]

lemma spawnChild_other {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n)
    (i : ℕ) (hi : i ≠ logical.top) (hc : i ≠ logical.top+1) :
    (spawnChildState g ell logical).frames i=logical.frames i := by
  simp [spawnChildState,changeFrame,debit,Function.update_of_ne hi,Function.update_of_ne hc]

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

lemma exteriorCleanObjectCode_wellFormed : exteriorCleanObjectCode.wellFormed := by
  refine ⟨exteriorQueueCleanCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

lemma vertexFlagSetCode_wellFormed : vertexFlagSetCode.wellFormed := by
  simp [vertexFlagSetCode,vertexIntegerStoreCode,vertexAddressCode_wellFormed,
    coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

lemma flaggedHeapInsertCode_wellFormed : flaggedHeapInsertCode.wellFormed := by
  refine ⟨?_,heapInsertCode_wellFormed,?_,vertexFlagSetCode_wellFormed⟩
  all_goals simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

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

lemma exteriorPeekObjectCode_wellFormed : exteriorPeekObjectCode.wellFormed :=
  ⟨exteriorCleanObjectCode_wellFormed,trivial,exteriorQueueRefreshCode_wellFormed⟩

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

-- Proof module: Solutions.ControllerBudgetFlags

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma ControllerBudgetFlags.payUnit {n : ℕ} {logical : RecursiveState n} {st : MachineState}
    (h : ControllerBudgetFlags logical st) : ControllerBudgetFlags logical (payUnit st) := h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerPriorityExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 14000000 in
lemma controller_priority_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) (hMass : memory.mass ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    let T := (logical.top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length logical out,
      MachineEval m g ω priorityCode st steps out ∧ PendingSelectionSpec logical out ∧
      next.mass ≤ memory.mass ∧ steps+next.potential P Q ≤ memory.potential P Q+T ∧
      out.work=st.work+steps ∧ out.scalar.core.ptrs 160=st.scalar.core.ptrs 160 ∧ out.scalar.core.ptrs 170=st.scalar.core.ptrs 170 := by
  dsimp only
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let T := (logical.top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
  let pm := memory.live hDone
  have oldMass : memory.mass=pm.queueMass := memory.mass_live hDone
  obtain ⟨u,out,om,ex,hSpec,oMass,oAmort,oQ,oW,oO,oH,oMarks⟩ := priority_exec m g ω logical s α ε ell length N rank st memory.halted pm hDepth (by rw [←oldMass]; exact hMass) hCap hPow
  let next := memory.nextLive hDone om hDone ex (by decide) (by decide) oH (memory.indexInvariant hDone ex (by decide) oMarks)
  have newMass : next.mass=om.queueMass := ControllerMemory.nextLive_mass _ _ _ _ _ _ _ _ _
  have hAmort : u+P*next.mass ≤ P*memory.mass+T := by
    rw [newMass,oldMass]
    simpa only [P,T,Nat.add_assoc] using oAmort
  refine ⟨u,out,next,ex,hSpec,?_,?_,oW,ex.pointer_frame 160 (by decide),ex.pointer_frame 170 (by decide)⟩
  · rw [newMass,oldMass]
    exact oMass
  · rw [next.potential_live hDone,memory.potential_live hDone]
    change u + (P * next.mass + Q * recursiveCacheMass logical) ≤
      (P * memory.mass + Q * recursiveCacheMass logical) + T
    omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolveAmortizedWork

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation

lemma solve_amortized_work (before middle after charge : ℝ≥0∞)
    (u v P mass0 mass1 mass2 A D : ℕ)
    (hMiddle : middle=before+(u : ℝ≥0∞))
    (hPrefix : u+P*mass1 ≤ P*mass0+A)
    (hSolve : after ≤ middle+(v : ℝ≥0∞)+charge)
    (hMass : mass2 ≤ mass1+D) :
    after+((P*mass2 : ℕ) : ℝ≥0∞) ≤
      before+((P*mass0+A+v+P*D : ℕ) : ℝ≥0∞)+charge := by
  have hMul := Nat.mul_le_mul_left P hMass
  simp only [Nat.mul_add] at hMul
  have hNat : u+v+P*mass2 ≤ P*mass0+A+v+P*D := by omega
  have hCast : ((u+v+P*mass2 : ℕ) : ℝ≥0∞) ≤
      ((P*mass0+A+v+P*D : ℕ) : ℝ≥0∞) := by exact_mod_cast hNat
  calc
    after+((P*mass2 : ℕ) : ℝ≥0∞) ≤
        (middle+(v : ℝ≥0∞)+charge)+((P*mass2 : ℕ) : ℝ≥0∞) := add_le_add hSolve le_rfl
    _ = before+((u+v+P*mass2 : ℕ) : ℝ≥0∞)+charge := by
      rw [hMiddle]
      simp only [Nat.cast_add]
      ac_rfl
    _ ≤ before+((P*mass0+A+v+P*D : ℕ) : ℝ≥0∞)+charge :=
      add_le_add (add_le_add le_rfl hCast) le_rfl

lemma amortized_unit_prefix (before middle after charge : ℝ≥0∞)
    (u P mass0 mass1 mass2 A B : ℕ)
    (hMiddle : middle=before+(u : ℝ≥0∞))
    (hPrefix : u+P*mass1 ≤ P*mass0+A)
    (hNext : after+((P*mass2 : ℕ) : ℝ≥0∞) ≤ middle+((P*mass1+B : ℕ) : ℝ≥0∞)+charge) :
    after+((P*mass2 : ℕ) : ℝ≥0∞) ≤ before+((P*mass0+A+B : ℕ) : ℝ≥0∞)+charge := by
  have hNat : u+(P*mass1+B) ≤ P*mass0+A+B := by omega
  have hCast : ((u+(P*mass1+B) : ℕ) : ℝ≥0∞) ≤ ((P*mass0+A+B : ℕ) : ℝ≥0∞) := by exact_mod_cast hNat
  calc
    _ ≤ middle+((P*mass1+B : ℕ) : ℝ≥0∞)+charge := hNext
    _ = before+((u+(P*mass1+B) : ℕ) : ℝ≥0∞)+charge := by rw [hMiddle]; simp only [Nat.cast_add]; ac_rfl
    _ ≤ _ := add_le_add (add_le_add le_rfl hCast) le_rfl

lemma unit_amortized_work (before after : ℝ≥0∞) (u P mass0 mass1 A D : ℕ)
    (hWork : after=before+(u : ℝ≥0∞)) (hSteps : u ≤ A) (hMass : mass1 ≤ mass0+D) :
    after+((P*mass1 : ℕ) : ℝ≥0∞) ≤ before+((P*mass0+A+P*D : ℕ) : ℝ≥0∞) := by
  have hMul := Nat.mul_le_mul_left P hMass
  rw [Nat.mul_add] at hMul
  have hNat : u+P*mass1 ≤ P*mass0+A+P*D := by omega
  have hCast : ((u+P*mass1 : ℕ) : ℝ≥0∞) ≤ ((P*mass0+A+P*D : ℕ) : ℝ≥0∞) := by exact_mod_cast hNat
  rw [hWork]
  calc
    _ = before+((u+P*mass1 : ℕ) : ℝ≥0∞) := by simp only [Nat.cast_add]; ac_rfl
    _ ≤ _ := add_le_add le_rfl hCast

lemma cache_credit_work (before after : ℝ≥0∞) (heap0 heap1 cache0 cache1 card coefficient Q rest : ℕ)
    (hWork : after+(heap1 : ℝ≥0∞) ≤ before+((heap0+coefficient*card+rest : ℕ) : ℝ≥0∞))
    (hDrop : cache1+card=cache0) (hCoefficient : coefficient ≤ Q) :
    after+((heap1+Q*cache1 : ℕ) : ℝ≥0∞) ≤ before+((heap0+Q*cache0+rest : ℕ) : ℝ≥0∞) := by
  have hMul := Nat.mul_le_mul_right card hCoefficient
  have hCredit := congrArg (fun z : ℕ => Q*z) hDrop
  simp only [Nat.mul_add] at hCredit
  have hNat : heap0+coefficient*card+rest+Q*cache1 ≤ heap0+Q*cache0+rest := by omega
  have hCast : ((heap0+coefficient*card+rest+Q*cache1 : ℕ) : ℝ≥0∞) ≤ ((heap0+Q*cache0+rest : ℕ) : ℝ≥0∞) := by exact_mod_cast hNat
  calc
    _ = (after+(heap1 : ℝ≥0∞))+((Q*cache1 : ℕ) : ℝ≥0∞) := by simp only [Nat.cast_add]; ac_rfl
    _ ≤ (before+((heap0+coefficient*card+rest : ℕ) : ℝ≥0∞))+((Q*cache1 : ℕ) : ℝ≥0∞) := add_le_add hWork le_rfl
    _ = before+((heap0+coefficient*card+rest+Q*cache1 : ℕ) : ℝ≥0∞) := by simp only [Nat.cast_add]; ac_rfl
    _ ≤ _ := add_le_add le_rfl hCast

lemma cache_growth_work (before after charge : ℝ≥0∞) (heap0 heap1 cache0 cache1 A Q D : ℕ)
    (hWork : after+(heap1 : ℝ≥0∞) ≤ before+((heap0+A : ℕ) : ℝ≥0∞)+charge)
    (hCache : cache1 ≤ cache0+D) :
    after+((heap1+Q*cache1 : ℕ) : ℝ≥0∞) ≤
      before+((heap0+Q*cache0 : ℕ) : ℝ≥0∞)+((A+Q*D : ℕ) : ℝ≥0∞)+charge := by
  have hMul := Nat.mul_le_mul_left Q hCache
  have hCast : ((Q*cache1 : ℕ) : ℝ≥0∞) ≤ ((Q*cache0+Q*D : ℕ) : ℝ≥0∞) := by
    exact_mod_cast (by simpa only [Nat.mul_add] using hMul)
  calc
    _ = (after+(heap1 : ℝ≥0∞))+((Q*cache1 : ℕ) : ℝ≥0∞) := by simp only [Nat.cast_add]; ac_rfl
    _ ≤ (before+((heap0+A : ℕ) : ℝ≥0∞)+charge)+((Q*cache0+Q*D : ℕ) : ℝ≥0∞) := add_le_add hWork hCast
    _ = _ := by simp only [Nat.cast_add]; ac_rfl

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PotentialPrefixWork

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation

lemma potential_prefix_work (before middle after charge : ℝ≥0∞) (u phi0 phi1 phi2 A : ℕ)
    (hMiddle : middle=before+(u : ℝ≥0∞)) (hPrefix : u+phi1 ≤ phi0+A)
    (hNext : after+(phi2 : ℝ≥0∞) ≤ middle+(phi1 : ℝ≥0∞)+charge) :
    after+(phi2 : ℝ≥0∞) ≤ before+(phi0 : ℝ≥0∞)+(A : ℝ≥0∞)+charge := by
  have hCast : ((u+phi1 : ℕ) : ℝ≥0∞) ≤ ((phi0+A : ℕ) : ℝ≥0∞) := by exact_mod_cast hPrefix
  calc
    _ ≤ middle+(phi1 : ℝ≥0∞)+charge := hNext
    _ = before+((u+phi1 : ℕ) : ℝ≥0∞)+charge := by rw [hMiddle]; push_cast; ac_rfl
    _ ≤ before+((phi0+A : ℕ) : ℝ≥0∞)+charge := add_le_add (add_le_add le_rfl hCast) le_rfl
    _ = _ := by push_cast; ac_rfl

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerPriorityChoice

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 18000000 in
lemma controller_priority_choice_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical no yes : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank Q M : ℕ)
    (noCode yesCode : MachineCode) (noGrowth yesGrowth : ℕ) (noCharge yesCharge : ℝ≥0∞)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hFlags : ControllerBudgetFlags logical st) (hM : memory.mass ≤ M) (hMN : M ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank)
    (noExec : pendingPush logical=none → ∀ a, ∀ mem : ControllerMemory g s α ε ell length logical a,
      mem.mass ≤ M → ControllerBudgetFlags logical a → PendingSelectionSpec logical a →
      ∃ u out, ∃ next : ControllerMemory g s α ε ell length no out,
        MachineEval m g ω noCode a u out ∧ next.mass ≤ mem.mass+noGrowth ∧
        out.work+(next.potential (cleanBodyBound (16*(ell+3)) length rank+2) Q : ℝ≥0∞) ≤
          a.work+(mem.potential (cleanBodyBound (16*(ell+3)) length rank+2) Q : ℝ≥0∞)+noCharge)
    (yesExec : (pendingPush logical).isSome=true → ∀ a, ∀ mem : ControllerMemory g s α ε ell length logical a,
      mem.mass ≤ M → ControllerBudgetFlags logical a → PendingSelectionSpec logical a →
      ∃ u out, ∃ next : ControllerMemory g s α ε ell length yes out,
        MachineEval m g ω yesCode a u out ∧ next.mass ≤ mem.mass+yesGrowth ∧
        out.work+(next.potential (cleanBodyBound (16*(ell+3)) length rank+2) Q : ℝ≥0∞) ≤
          a.work+(mem.potential (cleanBodyBound (16*(ell+3)) length rank+2) Q : ℝ≥0∞)+yesCharge) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerPriorityChoice logical no yes) out,
      MachineEval m g ω (.seq priorityCode (.branchPointer 97 0 noCode yesCode)) st steps out ∧
      next.mass ≤ memory.mass+(if (pendingPush logical).isSome then yesGrowth else noGrowth) ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+controllerPriorityCharge logical ell length rank noCharge yesCharge := by
  dsimp only
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let T := (logical.top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
  obtain ⟨u,a,am,ea,aSpec,aMass,aAmort,aW,a160,a170⟩ := controller_priority_exec m g ω logical s α ε ell length N rank Q st memory hDone hDepth (hM.trans hMN) hCap hPow
  have hM' : am.payUnit.mass ≤ M := by rw [ControllerMemory.payUnit_mass]; exact aMass.trans hM
  have aFlags : ControllerBudgetFlags logical a := ⟨a160.trans hFlags.1,a170.trans hFlags.2⟩
  cases hp : pendingPush logical with
  | none =>
    rw [compilerPriorityChoice,hp]
    simp only [Option.isSome_none,Bool.false_eq_true,if_false]
    obtain ⟨v,out,next,eb,bMass,bW⟩ := noExec hp (payUnit a) am.payUnit hM' aFlags.payUnit aSpec
    have noneSpec : a.scalar.core.ptrs 97=0 ∧ a.scalar.core.ptrs 112=(-1) := by
      simpa only [PendingSelectionSpec,hp] using aSpec
    have ec : MachineEval m g ω (.branchPointer 97 0 noCode yesCode) a (1+v) out :=
      MachineEval.pointerLe am.halted (by rw [noneSpec.1,(am.live hDone).zero]) eb
    refine ⟨u+(1+v),out,next,MachineEval.seq ea ec,?_,?_⟩
    · rw [ControllerMemory.payUnit_mass] at bMass
      exact bMass.trans (add_le_add aMass le_rfl)
    · rw [payUnit_work,ControllerMemory.potential_payUnit] at bW
      have hb : out.work+(next.potential P Q : ℝ≥0∞) ≤ a.work+(am.potential P Q : ℝ≥0∞)+(noCharge+2) := by
        have h12 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
        exact bW.trans (by simpa only [P,add_assoc,add_left_comm,add_comm] using add_le_add (le_refl (a.work+(am.potential P Q : ℝ≥0∞)+noCharge)) h12)
      have h := potential_prefix_work st.work a.work out.work (noCharge+2) u (memory.potential P Q) (am.potential P Q) (next.potential P Q) T aW aAmort hb
      simpa only [controllerPriorityCharge,hp,Option.isSome_none,Bool.false_eq_true,if_false,P,T,add_assoc] using h
  | some pair =>
    obtain ⟨t,v⟩ := pair
    rw [compilerPriorityChoice,hp]
    simp only [Option.isSome_some,if_true]
    obtain ⟨w,out,next,eb,bMass,bW⟩ := yesExec (by simp [hp]) (payUnit a) am.payUnit hM' aFlags.payUnit aSpec
    have spec : a.scalar.core.ptrs 97=1 ∧ a.scalar.core.ptrs 112=(t : ℤ) ∧ a.scalar.core.ptrs 40=(v.val : ℤ) := by simpa only [PendingSelectionSpec,hp] using aSpec
    have ec : MachineEval m g ω (.branchPointer 97 0 noCode yesCode) a (1+w+1) (payUnit out) :=
      MachineEval.pointerGt am.halted (by rw [spec.1,(am.live hDone).zero]; norm_num) eb
    refine ⟨u+(1+w+1),payUnit out,next.payUnit,MachineEval.seq ea ec,?_,?_⟩
    · rw [ControllerMemory.payUnit_mass] at bMass ⊢
      exact bMass.trans (add_le_add aMass le_rfl)
    · rw [payUnit_work,ControllerMemory.potential_payUnit] at bW
      rw [payUnit_work,ControllerMemory.potential_payUnit]
      have hb : out.work+(next.potential P Q : ℝ≥0∞) ≤ a.work+(am.potential P Q : ℝ≥0∞)+(yesCharge+1) := by
        simpa only [P,add_assoc,add_left_comm,add_comm] using bW
      have h := potential_prefix_work st.work a.work out.work (yesCharge+1) u (memory.potential P Q) (am.potential P Q) (next.potential P Q) T aW aAmort hb
      calc
        _ = (out.work+(next.potential P Q : ℝ≥0∞))+1 := by ac_rfl
        _ ≤ _ := add_le_add h le_rfl
        _ = _ := by simp only [controllerPriorityCharge,hp,Option.isSome_some,if_true,P,T]; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerRoutineLift

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma controller_lift_unit_run {m : SolveModel} {n : ℕ} {g : InputGraph n} {ω : ℕ → Bool}
    {s : Fin n} {α ε : ℝ} {ell length P A D : ℕ} {logical sourceNext : RecursiveState n}
    {st out : MachineState} {code : MachineCode} {steps : ℕ}
    (memory : ControllerMemory g s α ε ell length logical st) (hDone : logical.done=false)
    (pm : RecursiveMachineMemory g s α ε ell length sourceNext out) (hNext : sourceNext.done=false)
    (ex : MachineEval m g ω code st steps out) (h150 : 150 ∉ code.pointerTargets) (h151 : 151 ∉ code.pointerTargets)
    (h53 : 53 ∉ code.pointerTargets) (hh : out.scalar.halted=false)
    (hMarks : ∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
      st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7))
    (hWork : out.work=st.work+steps) (hSteps : steps ≤ A) (hMass : pm.queueMass ≤ (memory.live hDone).queueMass+D) :
    ∃ next : ControllerMemory g s α ε ell length sourceNext out,
      next.mass ≤ memory.mass+D ∧
      out.work+((P*next.mass : ℕ) : ℝ≥0∞) ≤ st.work+((P*memory.mass : ℕ) : ℝ≥0∞)+((A+P*D : ℕ) : ℝ≥0∞) := by
  let next := memory.nextLive hDone pm hNext ex h150 h151 hh (memory.indexInvariant hDone ex h53 hMarks)
  have massNext : next.mass=pm.queueMass := ControllerMemory.nextLive_mass _ _ _ _ _ _ _ _ _
  have massOld : memory.mass=(memory.live hDone).queueMass := memory.mass_live hDone
  refine ⟨next,?_,?_⟩
  · rw [massNext,massOld]
    exact hMass
  · have h := unit_amortized_work st.work out.work steps P (memory.live hDone).queueMass pm.queueMass A D hWork hSteps hMass
    rw [←massNext,←massOld] at h
    simpa only [Nat.cast_add,add_assoc] using h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerCacheWork

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma controller_cache_work {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length P Q : ℕ} {logical target : RecursiveState n} {st out : MachineState}
    (memory : ControllerMemory g s α ε ell length logical st)
    (next : ControllerMemory g s α ε ell length target out)
    (hOld : logical.done=false) (hNext : target.done=false) (charge : ℝ≥0∞)
    (hCache : recursiveCacheMass target ≤ recursiveCacheMass logical)
    (hWork : out.work+((P*next.mass : ℕ) : ℝ≥0∞) ≤
      st.work+((P*memory.mass : ℕ) : ℝ≥0∞)+charge) :
    out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+charge := by
  rw [next.potential_live hNext,memory.potential_live hOld]
  have hNat := Nat.mul_le_mul_left Q hCache
  have hCast : ((Q*recursiveCacheMass target : ℕ) : ℝ≥0∞) ≤ ((Q*recursiveCacheMass logical : ℕ) : ℝ≥0∞) := by exact_mod_cast hNat
  simpa only [Nat.cast_add,add_assoc,add_left_comm,add_comm] using add_le_add hWork hCast

lemma controller_cache_work_two {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length P Q : ℕ} {logical target : RecursiveState n} {st out : MachineState}
    (memory : ControllerMemory g s α ε ell length logical st)
    (next : ControllerMemory g s α ε ell length target out)
    (hOld : logical.done=false) (hNext : target.done=false) (a b : ℝ≥0∞)
    (hCache : recursiveCacheMass target ≤ recursiveCacheMass logical)
    (hWork : out.work+((P*next.mass : ℕ) : ℝ≥0∞) ≤
      st.work+((P*memory.mass : ℕ) : ℝ≥0∞)+a+b) :
    out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+a+b := by
  have h := controller_cache_work (P:=P) (Q:=Q) memory next hOld hNext (a+b) hCache
    (by simpa only [add_assoc] using hWork)
  simpa only [add_assoc] using h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerBeginEpisodeSource

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_begin_selected {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n) :
    let f := logical.frames logical.top
    let Q := max (∑ v ∈ f.active, f.residual v) (f.q*(f.block : ℝ))
    let theta := Q/(f.block : ℝ)
    (compilerBeginEpisode m g logical).frames logical.top={f with Q := Q,W := 0,theta := theta,openBudget := true,childrenThisEpisode := 0,cache := ∅,high := f.active.filter (fun v => 3*theta*LocalPush.deg g.graph v ≤ f.residual v),pc := if f.needFull then .fullSolve else .normalize} := by
  simp only [compilerBeginEpisode,changeFrame,debit,Function.update_self]

lemma compiler_begin_other {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n) (j : ℕ) (hj : j ≠ logical.top) :
    (compilerBeginEpisode m g logical).frames j=logical.frames j := by
  simp only [compilerBeginEpisode,changeFrame,debit,Function.update_of_ne hj]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FinishEpisodeSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma finish_episode_selected {n : ℕ} (logical : RecursiveState n) :
    (finishEpisode logical).frames logical.top=
      {logical.frames logical.top with openBudget := false,cache := ∅} := by
  simp only [finishEpisode,changeFrame,Function.update_self]

lemma finish_episode_other {n : ℕ} (logical : RecursiveState n) (j : ℕ) (hj : j ≠ logical.top) :
    (finishEpisode logical).frames j=logical.frames j := by
  simp only [finishEpisode,changeFrame,Function.update_of_ne hj]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveFrameControl

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def RecursiveFrameMemory.control_frame {n : ℕ} {g : InputGraph n} {a b : RecursiveState n}
    {j width length : ℕ} {st out : MachineState} {floor : ℤ}
    (f : RecursiveFrameMemory g a j width length st floor)
    (pc : NormalizePC) (budget need : Bool) (children : ℕ)
    (hFrame : b.frames j={a.frames j with pc := pc,openBudget := budget,needFull := need,childrenThisEpisode := children})
    (hDomain : parentDomain b j=parentDomain a j)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hHeaderI : ∀ slot < 32, slot ∉ ([0,9,10,11] : List ℕ) →
      out.scalar.integerMemory (levelHeaderAddress j slot)=st.scalar.integerMemory (levelHeaderAddress j slot))
    (hHeaderR : ∀ slot < 32, out.scalar.core.mem (levelHeaderAddress j slot)=st.scalar.core.mem (levelHeaderAddress j slot))
    (hPC : out.scalar.integerMemory (levelHeaderAddress j 0)=(normalizePCNumber pc : ℤ))
    (hBudget : out.scalar.integerMemory (levelHeaderAddress j 9)=if budget then 1 else 0)
    (hNeed : out.scalar.integerMemory (levelHeaderAddress j 10)=if need then 1 else 0)
    (hChildren : out.scalar.integerMemory (levelHeaderAddress j 11)=(children : ℤ))
    (hFieldsI : ∀ v ∈ parentDomain a j, ∀ field < 16*(j+1)+7,
      out.scalar.integerMemory (vertexRecordAddress width v.val field)=st.scalar.integerMemory (vertexRecordAddress width v.val field))
    (hFieldsR : ∀ v ∈ parentDomain a j, ∀ field < 16*(j+1)+7,
      out.scalar.core.mem (vertexRecordAddress width v.val field)=st.scalar.core.mem (vertexRecordAddress width v.val field))
    (hOwned : ∀ z ∈ f.owned, out.scalar.integerMemory z=st.scalar.integerMemory z) :
    RecursiveFrameMemory g b j width length out floor := by
  let ext := f.exteriorObject.frame
    (fun z hz => hOwned z (Finset.mem_union_left _ (Finset.mem_union_right _ hz))) hFree
  let high := f.highObject.frame (fun z hz => hOwned z (Finset.mem_union_right _ hz)) hFree
  refine {
    N := by simpa only [hFrame] using (hHeaderR 0 (by decide)).trans f.N
    q := by simpa only [hFrame] using (hHeaderR 1 (by decide)).trans f.q
    Q := by simpa only [hFrame] using (hHeaderR 3 (by decide)).trans f.Q
    W := by simpa only [hFrame] using (hHeaderR 4 (by decide)).trans f.W
    theta := by simpa only [hFrame] using (hHeaderR 5 (by decide)).trans f.theta
    block := by simpa only [hFrame] using (hHeaderI 14 (by decide) (by decide)).trans f.block
    pc := by simpa only [hFrame] using hPC
    openBudget := by simpa only [hFrame] using hBudget
    needFull := by simpa only [hFrame] using hNeed
    children := by simpa only [hFrame] using hChildren
    reference := by rw [hDomain,hFrame]; exact fun v hv => (hFieldsR v hv _ (by omega)).trans (f.reference v hv)
    residual := by rw [hDomain,hFrame]; exact fun v hv => (hFieldsR v hv _ (by omega)).trans (f.residual v hv)
    activeFlags := by rw [hDomain,hFrame]; exact fun v hv => (hFieldsI v hv _ (by omega)).trans (f.activeFlags v hv)
    cacheFlags := by rw [hDomain,hFrame]; exact fun v hv => (hFieldsI v hv _ (by omega)).trans (f.cacheFlags v hv)
    activeVertices := f.activeVertices
    activeFoot := f.activeFoot
    activeRep := ?_
    activeNodup := f.activeNodup
    activeSet := by rw [hFrame]; exact f.activeSet
    activeCount := by simpa only [hFrame] using (hHeaderI 3 (by decide) (by decide)).trans f.activeCount
    activeVolume := by simpa only [hFrame] using (hHeaderI 2 (by decide) (by decide)).trans f.activeVolume
    activeBelow := fun z hz => (f.activeBelow z hz).trans_le hFree
    activeAbove := f.activeAbove
    cacheVertices := f.cacheVertices
    cacheFoot := f.cacheFoot
    cacheRep := ?_
    cacheNodup := f.cacheNodup
    cacheSet := by rw [hFrame]; exact f.cacheSet
    cacheCount := by simpa only [hFrame] using (hHeaderI 5 (by decide) (by decide)).trans f.cacheCount
    cacheVolume := by simpa only [hFrame] using (hHeaderI 6 (by decide) (by decide)).trans f.cacheVolume
    cacheBelow := fun z hz => (f.cacheBelow z hz).trans_le hFree
    cacheAbove := f.cacheAbove
    exteriorBase := f.exteriorBase
    highBase := f.highBase
    exteriorPointer := (hHeaderI 7 (by decide) (by decide)).trans f.exteriorPointer
    highPointer := (hHeaderI 8 (by decide) (by decide)).trans f.highPointer
    exteriorObject := ext
    highObject := high
    exteriorData := ?_
    exteriorCover := by rw [hFrame]; exact f.exteriorCover
    highBoolean := ?_
    virtualExcluded := by rw [hDomain]; exact fun v hv => (hFieldsI v hv _ (by omega)).trans (f.virtualExcluded v hv)
    highFlags := ?_
    highDomain := by rw [hDomain]; exact f.highDomain
    highValid := ?_
    highCover := by rw [hFrame]; exact f.highCover
  }
  · rw [hHeaderI 1 (by decide) (by decide)]
    apply f.activeRep.frame
    intro z hz
    apply hOwned
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hz))
  · rw [hHeaderI 4 (by decide) (by decide)]
    apply f.cacheRep.frame
    intro z hz
    apply hOwned
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hz))
  · rw [hFrame,hDomain]
    refine ⟨f.exteriorData.queuedDomain,?_,?_,?_⟩
    · intro v hv
      rw [hFieldsI v hv _ (by omega)]
      exact f.exteriorData.flags v hv
    · intro v hv
      rw [hFieldsI v hv _ (by omega)]
      exact f.exteriorData.activeNonnegative v hv
    · intro v hv
      rw [hFieldsI v hv _ (by omega),hFieldsI v hv 0 (by omega),hFieldsR v hv _ (by omega)]
      exact f.exteriorData.eligibility v hv
  · rw [hFrame,hDomain]
    intro v hv
    rw [hFieldsR v hv _ (by omega),hFieldsI v hv _ (by omega),hFieldsI v hv 0 (by omega),hFieldsR v hv _ (by omega)]
    exact f.highBoolean v hv
  · rw [hDomain]
    intro v hv
    rw [hFieldsI v hv _ (by omega)]
    exact f.highFlags v hv
  · rw [hFrame,hDomain]
    intro v hv
    rw [hFieldsI v hv _ (by omega),hFieldsI v hv 0 (by omega),hFieldsR v hv _ (by omega)]
    exact f.highValid v hv

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

-- Proof module: Solutions.RecursiveMachineControlFrame

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section


def RecursiveMachineMemory.control_frame {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical next : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hTop : next.top=logical.top) (hStored : next.stored=logical.stored) (hX : next.x=logical.x)
    (hBoundary : next.boundaryEdges=logical.boundaryEdges)
    (hFrames : ∀ j ≤ logical.top, next.frames j={logical.frames j with pc := (next.frames j).pc,openBudget := (next.frames j).openBudget,needFull := (next.frames j).needFull,childrenThisEpisode := (next.frames j).childrenThisEpisode})
    (hDomains : ∀ j ≤ logical.top, parentDomain next j=parentDomain logical j)
    (hGlobals : ∀ z, 0 ≤ z → z < 128 → out.scalar.integerMemory z=st.scalar.integerMemory z)
    (hV : ∀ v : Fin n, ∀ field, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field)=
      st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val field))
    (hHeader : ∀ j ≤ logical.top, ∀ slot < 32, slot ∉ ([0,9,10,11] : List ℕ) →
      out.scalar.integerMemory (levelHeaderAddress j slot)=st.scalar.integerMemory (levelHeaderAddress j slot))
    (hPC : ∀ j ≤ logical.top, out.scalar.integerMemory (levelHeaderAddress j 0)=(normalizePCNumber (next.frames j).pc : ℤ))
    (hBudget : ∀ j ≤ logical.top, out.scalar.integerMemory (levelHeaderAddress j 9)=if (next.frames j).openBudget then 1 else 0)
    (hNeed : ∀ j ≤ logical.top, out.scalar.integerMemory (levelHeaderAddress j 10)=if (next.frames j).needFull then 1 else 0)
    (hChildren : ∀ j ≤ logical.top, out.scalar.integerMemory (levelHeaderAddress j 11)=((next.frames j).childrenThisEpisode : ℤ))
    (hOwned : ∀ j, ∀ hj : j ≤ logical.top, ∀ z ∈ (pm.frames j hj).owned, out.scalar.integerMemory z=st.scalar.integerMemory z)
    (hCache : ∀ z ∈ cachedRowCells g st.scalar.integerMemory (16*(ell+3)) logical.stored,
      out.scalar.integerMemory z=st.scalar.integerMemory z)
    (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : RecursiveMachineMemory g s α ε ell length next out := by
  have hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 := le_of_eq (hP 20 (by simp)).symm
  let frames := fun j hj => (pm.frames j (by rw [←hTop]; exact hj)).control_frame
    (next.frames j).pc (next.frames j).openBudget (next.frames j).needFull (next.frames j).childrenThisEpisode
    (hFrames j (by rw [←hTop]; exact hj)) (hDomains j (by rw [←hTop]; exact hj)) hFree
    (hHeader j (by rw [←hTop]; exact hj)) (fun slot hs => congrFun hR _)
    (hPC j (by rw [←hTop]; exact hj)) (hBudget j (by rw [←hTop]; exact hj))
    (hNeed j (by rw [←hTop]; exact hj)) (hChildren j (by rw [←hTop]; exact hj))
    (fun v hv field hf => hV v field) (fun v hv field hf => congrFun hR _)
    (hOwned j (by rw [←hTop]; exact hj))
  have hDegree : recursiveDegreeDomain g s next=recursiveDegreeDomain g s logical := by
    unfold recursiveDegreeDomain
    rw [hStored]
  have hGraphCache : GraphCache g out.scalar.integerMemory (16*(ell+3)) logical.stored (out.scalar.core.ptrs 20) := by
    rw [hP 20 (by simp)]
    apply pm.graphCache.frame g _ _ _ _ _
    · intro v field hf
      exact hV v field
    · intro v hv i hi
      exact hCache _ (Finset.mem_biUnion.mpr ⟨v,hv,(mem_arrayCells _ _ _).mpr ⟨i,hi,rfl⟩⟩)
  refine {
    zero := (hP 0 (by simp)).trans pm.zero
    top := by rw [hTop]; exact (hP 100 (by simp)).trans pm.top
    width := (hP 50 (by simp)).trans pm.width
    alphaRegister := (hG 30 (by simp)).trans pm.alphaRegister
    one := (hG 31 (by simp)).trans pm.one
    alphaMemory := by rw [hR]; exact pm.alphaMemory
    epsilonMemory := by rw [hR]; exact pm.epsilonMemory
    depthMemory := (hGlobals 2 (by omega) (by omega)).trans pm.depthMemory
    lengthMemory := (hGlobals 5 (by omega) (by omega)).trans pm.lengthMemory
    seedMemory := (hGlobals 0 (by omega) (by omega)).trans pm.seedMemory
    allocator := by rw [hP 20 (by simp)]; exact pm.allocator
    potential := by rw [hR,hX]; exact pm.potential
    seedMarker := by rw [hR]; exact pm.seedMarker
    boundary := by rw [hBoundary]; exact (hGlobals 7 (by omega) (by omega)).trans pm.boundary
    graphCache := by rw [hStored]; exact hGraphCache
    rowAbove := by rw [hStored]; intro v hv; rw [hV v 1]; exact pm.rowAbove v hv
    knownDegree := by rw [hDegree]; intro v hv; rw [hV v 0]; exact pm.knownDegree v hv
    unknownDegree := by rw [hDegree]; intro v hv; rw [hV v 0]; exact pm.unknownDegree v hv
    frames := frames
    pieceSeparation := ?_
    frameSeparation := ?_
    cacheSeparation := ?_
    output := hO.trans pm.output
  }
  · intro j hj
    exact pm.pieceSeparation j (by rw [←hTop]; exact hj)
  · intro i hi j hj hij
    exact pm.frameSeparation i (by rw [←hTop]; exact hi) j (by rw [←hTop]; exact hj) hij
  · intro j hj
    have ho : j ≤ logical.top := by rw [←hTop]; exact hj
    change Disjoint (pm.frames j ho).owned (cachedRowCells g out.scalar.integerMemory (16*(ell+3)) next.stored)
    rw [hStored,cached_row_cells_congr g logical.stored (16*(ell+3)) st.scalar.integerMemory out.scalar.integerMemory (fun v hv => hV v 1)]
    exact pm.cacheSeparation j ho

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SetNeedFullSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma set_need_full_active {n : ℕ} (logical : RecursiveState n) (need : Bool) (j : ℕ) :
    ((compilerSetNeedFull logical need).frames j).active=(logical.frames j).active := by
  classical
  by_cases hj : j=logical.top <;> simp [compilerSetNeedFull,changeFrame,hj]

lemma set_need_full_domain {n : ℕ} (logical : RecursiveState n) (need : Bool) (j : ℕ) :
    parentDomain (compilerSetNeedFull logical need) j=parentDomain logical j := by
  unfold parentDomain
  split_ifs
  · rfl
  · exact set_need_full_active logical need (j-1)

lemma set_need_full_frame_control {n : ℕ} (logical : RecursiveState n) (need : Bool) (j : ℕ) :
    (compilerSetNeedFull logical need).frames j={logical.frames j with pc := ((compilerSetNeedFull logical need).frames j).pc,openBudget := ((compilerSetNeedFull logical need).frames j).openBudget,needFull := ((compilerSetNeedFull logical need).frames j).needFull,childrenThisEpisode := ((compilerSetNeedFull logical need).frames j).childrenThisEpisode} := by
  classical
  by_cases hj : j=logical.top <;> simp [compilerSetNeedFull,changeFrame,hj]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerFinishRequestSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma set_need_full_selected {n : ℕ} (logical : RecursiveState n) (need : Bool) :
    (compilerSetNeedFull logical need).frames logical.top={logical.frames logical.top with needFull := need} := by
  simp only [compilerSetNeedFull,changeFrame,Function.update_self]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HighQueueFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

lemma HighBooleanRecords.frame {n : ℕ} {I J : ℤ → ℤ} {R S : ℤ → ℝ}
    {width levelBase : ℕ} {theta : ℝ} {domain : Finset (Fin n)}
    (h : HighBooleanRecords I R width levelBase theta domain)
    (hActive : ∀ v ∈ domain, J (vertexRecordAddress width v.val (levelBase+2))=I (vertexRecordAddress width v.val (levelBase+2)))
    (hDegree : ∀ v ∈ domain, J (vertexRecordAddress width v.val 0)=I (vertexRecordAddress width v.val 0))
    (hResidual : ∀ v ∈ domain, S (vertexRecordAddress width v.val (levelBase+1))=R (vertexRecordAddress width v.val (levelBase+1)))
    (hBoolean : ∀ v ∈ domain, S (vertexRecordAddress width v.val (levelBase+4))=R (vertexRecordAddress width v.val (levelBase+4))) :
    HighBooleanRecords J S width levelBase theta domain := by
  intro v hv
  rw [hBoolean v hv,hActive v hv,hDegree v hv,hResidual v hv]
  exact h v hv

end
end SparseQueue
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

lemma MachinePendingKeys.boolean_frame {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st out : MachineState}
    (old : MachinePendingKeys g s α ε ell length logical st)
    (next : MachinePendingKeys g s α ε ell length logical out) (j : ℕ) (hj : j ≤ logical.top)
    (processed : Finset (Fin n)) (hDomain : processed ⊆ parentDomain logical j)
    (hBool : HighBooleanRecords st.scalar.integerMemory st.scalar.core.mem (16*(ell+3)) (16*(j+1)) (logical.frames j).theta processed)
    (hBits : ∀ v ∈ processed, out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+4))=
      st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(j+1)+4))) :
    HighBooleanRecords out.scalar.integerMemory out.scalar.core.mem (16*(ell+3)) (16*(j+1)) (logical.frames j).theta processed := by
  apply hBool.frame
  · intro v hv
    exact old.active_frame next j hj v (hDomain hv)
  · intro v hv
    exact old.degree_frame next v
  · intro v hv
    exact ((next.frames j hj).residual v (hDomain hv)).trans ((old.frames j hj).residual v (hDomain hv)).symm
  · exact hBits

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

-- Proof module: Solutions.ChangePCSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma change_pc_active {n : ℕ} (logical : RecursiveState n) (pc : NormalizePC) (j : ℕ) :
    ((changePC logical pc).frames j).active=(logical.frames j).active := by
  classical
  by_cases hj : j=logical.top <;> simp [changePC,changeFrame,hj]

lemma change_pc_domain {n : ℕ} (logical : RecursiveState n) (pc : NormalizePC) (j : ℕ) :
    parentDomain (changePC logical pc) j=parentDomain logical j := by
  unfold parentDomain
  split_ifs
  · rfl
  · exact change_pc_active logical pc (j-1)

lemma change_pc_frame_control {n : ℕ} (logical : RecursiveState n) (pc : NormalizePC) (j : ℕ) :
    (changePC logical pc).frames j={logical.frames j with pc := ((changePC logical pc).frames j).pc,openBudget := ((changePC logical pc).frames j).openBudget,needFull := ((changePC logical pc).frames j).needFull,childrenThisEpisode := ((changePC logical pc).frames j).childrenThisEpisode} := by
  classical
  by_cases hj : j=logical.top <;> simp [changePC,changeFrame,hj]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveCacheMass

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma recursive_cache_mass_frame {n : ℕ} (a b : RecursiveState n) (hTop : b.top=a.top)
    (hCache : ∀ i ≤ a.top, (b.frames i).cache=(a.frames i).cache) : recursiveCacheMass b=recursiveCacheMass a := by
  unfold recursiveCacheMass
  rw [hTop]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hCache i (by have := Finset.mem_range.mp hi; omega)]

lemma recursive_cache_mass_single_change {n : ℕ} (a b : RecursiveState n) (hTop : b.top=a.top)
    (hOther : ∀ i < a.top, (b.frames i).cache=(a.frames i).cache) :
    recursiveCacheMass b+(a.frames a.top).cache.card=recursiveCacheMass a+(b.frames a.top).cache.card := by
  unfold recursiveCacheMass
  rw [hTop]
  rw [Finset.sum_range_succ,Finset.sum_range_succ]
  have hPrefix : (∑ i ∈ Finset.range a.top, (b.frames i).cache.card)=(∑ i ∈ Finset.range a.top, (a.frames i).cache.card) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hOther i (Finset.mem_range.mp hi)]
  rw [hPrefix]
  omega

lemma recursive_cache_mass_debit {n : ℕ} (logical : RecursiveState n) (j : ℕ) (cost : ℝ≥0∞) :
    recursiveCacheMass (debit logical j cost)=recursiveCacheMass logical := rfl

lemma recursive_cache_mass_pc {n : ℕ} (logical : RecursiveState n) (pc : NormalizePC) :
    recursiveCacheMass (changePC logical pc)=recursiveCacheMass logical := by
  apply recursive_cache_mass_frame logical (changePC logical pc) rfl
  intro i hi
  by_cases he : i=logical.top <;> simp [changePC,changeFrame,he]

lemma recursive_cache_mass_need_full {n : ℕ} (logical : RecursiveState n) (need : Bool) :
    recursiveCacheMass (compilerSetNeedFull logical need)=recursiveCacheMass logical := by
  apply recursive_cache_mass_frame logical (compilerSetNeedFull logical need) rfl
  intro i hi
  by_cases he : i=logical.top <;> simp [compilerSetNeedFull,changeFrame,he]

lemma recursive_cache_mass_finish {n : ℕ} (logical : RecursiveState n) :
    recursiveCacheMass (finishEpisode logical)+(logical.frames logical.top).cache.card=recursiveCacheMass logical := by
  have h := recursive_cache_mass_single_change logical (finishEpisode logical) rfl (by
    intro i hi
    rw [finish_episode_other logical i (by omega)])
  simpa only [finish_episode_selected,Finset.card_empty,Nat.add_zero] using h

lemma recursive_cache_mass_begin {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n) :
    recursiveCacheMass (compilerBeginEpisode m g logical)+(logical.frames logical.top).cache.card=recursiveCacheMass logical := by
  have h := recursive_cache_mass_single_change logical (compilerBeginEpisode m g logical) rfl (by
    intro i hi
    rw [compiler_begin_other m g logical i (by omega)])
  simpa only [compiler_begin_selected,Finset.card_empty,Nat.add_zero] using h

lemma recursive_cache_mass_finish_request {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) :
    recursiveCacheMass (compilerFinishRequest g logical)+(logical.frames logical.top).cache.card=recursiveCacheMass logical := by
  dsimp only [compilerFinishRequest]
  rw [recursive_cache_mass_pc,recursive_cache_mass_need_full]
  exact recursive_cache_mass_finish (debit logical logical.top (16*(volumeNat g (logical.frames logical.top).active+1) : ℕ))

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

set_option maxHeartbeats 1800000 in
lemma high_queue_context_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (levelBase : ℕ)
    (hbase : st.scalar.core.ptrs 89=(levelBase : ℤ)) :
    ∃ out, MachineEval m g ω highQueueContextCode st 9 out ∧
      out.scalar.core.ptrs 87=((levelBase+3 : ℕ) : ℤ) ∧
      out.scalar.core.ptrs 88=((levelBase+6 : ℕ) : ℤ) ∧ out.scalar.core.regs 20=0 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+9 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω highQueueContextInstructions
    (by simp [highQueueContextInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,?_,?_,ex.query_frame (by decide),hW,?_,hH⟩
  all_goals simp [linearRun,highQueueContextInstructions,atomState,machineStep,pcSet,
    LocalPush.step,scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,hh,hbase] <;> ring

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

set_option maxHeartbeats 10000000 in
lemma high_clean_prepare_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : MachinePendingKeys g s α ε ell length logical st) :
    ∃ out, ∃ memory : MachinePendingKeys g s α ε ell length logical out,
      MachineEval m g ω highCleanPrepareCode st 30 out ∧
      ExteriorQueueContext out (16*(ell+3)) (16*(logical.top+1)+3) (16*(logical.top+1)+6)
        length (memory.frames logical.top le_rfl).highBase (128+32*((ell+2 : ℕ) : ℤ)) 0 ∧
      memory.queueMass=pm.queueMass ∧
      (∀ j, ∀ hj : j ≤ logical.top,
        (memory.frames j hj).exteriorObject.keys=(pm.frames j hj).exteriorObject.keys ∧
        (memory.frames j hj).highObject.keys=(pm.frames j hj).highObject.keys) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+30 ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a13,aI,aR,aW,aO,aH⟩ := level_header_integer_to_exec m g ω st hh logical.top 8 13 pm.top
  have a100 := (ea.pointer_frame 100 (by decide)).trans pm.top
  have a50 := (ea.pointer_frame 50 (by decide)).trans pm.width
  obtain ⟨b,eb,b87,b89,b41,bI,bR,bQ,bW,bO,bH⟩ := level_context_exec m g ω a aH logical.top (16*(ell+3)) a100 a50
  have bLength : b.scalar.integerMemory 5=(length : ℤ) := by rw [bI,aI]; exact pm.lengthMemory
  obtain ⟨c,ec,c18,c25,cI,cR,cQ,cW,cO,cH⟩ := frame_rank_load_exec m g ω b bH length bLength
  have c89 := (ec.pointer_frame 89 (by decide)).trans b89
  obtain ⟨out,ed,d87,d88,d20,dI,dR,dQ,dW,dO,dH⟩ := high_queue_context_exec m g ω c cH (16*(logical.top+1)) c89
  have ex : MachineEval m g ω highCleanPrepareCode st 30 out := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  have hI := dI.trans (cI.trans (bI.trans aI))
  have hR := dR.trans (cR.trans (bR.trans aR))
  have hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ex.pointer_frame _ (by decide)
  have hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ex.real_register_frame _ (by decide)
  have hO := dO.trans (cO.trans (bO.trans aO))
  let memory := pm.frame hI hR hP hG hO
  refine ⟨out,memory,ex,?_,rfl,(by intros; exact ⟨rfl,rfl⟩),hI,hR,?_,ex.query_frame (by decide),hO,dH⟩
  · refine ⟨memory.zero,?_,?_,memory.width,d87,d88,d20,memory.allocator⟩
    · exact ((ed.pointer_frame 13 (by decide)).trans ((ec.pointer_frame 13 (by decide)).trans
        ((eb.pointer_frame 13 (by decide)).trans a13))).trans (pm.frames logical.top le_rfl).highPointer
    · exact (ed.pointer_frame 25 (by decide)).trans c25
  · rw [dW,cW,bW,aW]
    norm_num
    ring

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

-- Proof module: Solutions.HighPeekExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma highPeekCode_wellFormed : highPeekCode.wellFormed :=
  ⟨highCleanPrepareCode_wellFormed,exteriorPeekObjectCode_wellFormed⟩

set_option maxHeartbeats 24000000 in
lemma high_peek_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hMass : pm.queueMass ≤ N) (hCap : rank < length) (hPow : N < 2^rank) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out, ∃ key : Option ℕ,
      MachineEval m g ω highPeekCode st steps out ∧ memory.queueMass ≤ pm.queueMass ∧
      steps+(cleanBodyBound (16*(ell+3)) length rank+2)*memory.queueMass ≤
        (cleanBodyBound (16*(ell+3)) length rank+2)*pm.queueMass+
          2*(cleanBodyBound (16*(ell+3)) length rank+2)+(21*rank+20*(16*(ell+3))+70)+36 ∧
      ExteriorPeekSpec ((logical.frames logical.top).high.image Fin.val) out key ∧
      out.scalar.core.mem=st.scalar.core.mem ∧ out.work=st.work+steps ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ z : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) z.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) z.val 7)) := by
  let old := MachinePendingKeys.ofMemory pm
  obtain ⟨a,am,ea,aCtx,aMass,aKeys,aI,aR,aW,aQ,aO,aH⟩ := high_clean_prepare_exec m g ω logical s α ε ell length st hh old
  change am.queueMass=pm.queueMass at aMass
  let f := am.frames logical.top le_rfl
  let valid := (logical.frames logical.top).high.image Fin.val
  have aCover : valid ⊆ f.highObject.keys := by
    rw [(aKeys logical.top le_rfl).2]
    exact (pm.frames logical.top le_rfl).highCover
  have aData : ExteriorQueueMemory a.scalar.integerMemory a.scalar.core.mem (16*(ell+3))
      (16*(logical.top+1)+3) (16*(logical.top+1)+6) 0 (parentDomain logical logical.top) valid f.highObject.keys := by
    rw [(aKeys logical.top le_rfl).2,aI,aR]
    let oldf := pm.frames logical.top le_rfl
    exact high_queue_as_exterior oldf.highBoolean oldf.virtualExcluded oldf.highDomain oldf.highFlags oldf.highValid
  have aMassBound : f.highObject.mass ≤ N := by
    have h := am.frame_mass_le_total logical.top le_rfl
    change f.exteriorObject.mass+f.highObject.mass ≤ am.queueMass at h
    omega
  obtain ⟨u,out,next,key,eb,bCtx,bData,bCover,bSpec,bMass,bAmort,bFree,bFreeUp,bCells,bFields,bPos,bR,bQ,bW,bO,bH⟩ :=
    exterior_peek_object_exec m g ω a aH (16*(ell+3)) (16*(logical.top+1)+3) (16*(logical.top+1)+6)
      length N rank (by omega) (by omega) (by omega) (by omega)
      f.highBase (128+32*((ell+2 : ℕ) : ℤ)) (by omega) 0 (parentDomain logical logical.top) valid
      f.highObject aCtx aData aCover aMassBound hCap hPow
  have hPair : Disjoint f.exteriorObject.cells f.highObject.cells := by
    have hp : [f.activeFoot,f.cacheFoot,f.exteriorObject.cells,f.highObject.cells].Pairwise Disjoint := am.pieceSeparation logical.top le_rfl
    exact hp.rel_get_of_lt (a:=⟨2,by norm_num⟩) (b:=⟨3,by norm_num⟩) (by change (2 : ℕ)<3; omega)
  have hFree : a.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 := bFree
  let nextExt := f.exteriorObject.frame (J := out.scalar.integerMemory)
    (fun z hz => bPos z (by have := f.exteriorObject.above z hz; omega) (f.exteriorObject.below z hz)
      (fun hn => Finset.disjoint_left.mp hPair hz hn)) hFree
  have extData : ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem (16*(ell+3))
      (16*(logical.top+1)) (16*(logical.top+1)+3) (logical.frames logical.top).q
      (parentDomain logical logical.top) ((logical.frames logical.top).exterior.image Fin.val) nextExt.keys := by
    refine ⟨f.exteriorData.queuedDomain,?_,?_,?_⟩
    · intro w hw
      rw [bFields w _ (by omega) (by omega)]
      exact f.exteriorData.flags w hw
    · intro w hw
      rw [bFields w _ (by omega) (by omega)]
      exact f.exteriorData.activeNonnegative w hw
    · intro w hw
      rw [bFields w _ (by omega) (by omega),bFields w 0 (by omega) (by omega),bR]
      exact f.exteriorData.eligibility w hw
  obtain ⟨memory,hExchange,hExt,hHigh,hOther,hFrame⟩ := replace_pending_queue_pair_frame g logical s α ε ell length
    logical.top a out am le_rfl hDepth nextExt next extData bData.queuedDomain bData.flags
    (by
      apply Finset.disjoint_left.mpr
      intro z he hh
      rcases Finset.mem_union.mp (bCells hh) with hn|ho
      · have hN := (nodeCells_mem_iff (a.scalar.core.ptrs 20) z).mp hn
        have hE := f.exteriorObject.below z he
        omega
      · exact Finset.disjoint_left.mp hPair he ho) hFree
    (by
      intro z hz hlt
      rcases Finset.mem_union.mp hz with he|hh
      · exact Finset.mem_union_left _ he
      · rcases Finset.mem_union.mp (bCells hh) with hn|ho
        · have hN := (nodeCells_mem_iff (a.scalar.core.ptrs 20) z).mp hn
          omega
        · exact Finset.mem_union_right _ ho)
    (fun w field hf ha hb => bFields w field hf hb)
    (fun z hz hf hn => bPos z hz hf (fun hm => hn (Finset.mem_union_right _ hm)))
    (fun z hz => congrFun bR z) (fun w field hf hn => congrFun bR _)
    bCtx.zero ((eb.pointer_frame 100 (by decide)).trans am.top)
    ((eb.pointer_frame 50 (by decide)).trans am.width)
    ((eb.real_register_frame 30 (by decide)).trans am.alphaRegister)
    ((eb.real_register_frame 31 (by decide)).trans am.one) (bO.trans am.output)
  have massOut : memory.queueMass ≤ pm.queueMass := by
    change memory.queueMass+(f.exteriorObject.mass+f.highObject.mass)=am.queueMass+(f.exteriorObject.mass+next.mass) at hExchange
    omega
  have allExt : ∀ j, ∀ hj : j ≤ logical.top,
      (logical.frames j).exterior.image Fin.val ⊆ (memory.frames j hj).exteriorObject.keys := by
    intro j hj
    by_cases he : j=logical.top
    · subst j
      rw [hExt]
      change (logical.frames logical.top).exterior.image Fin.val ⊆ f.exteriorObject.keys
      rw [(aKeys logical.top le_rfl).1]
      exact (pm.frames logical.top le_rfl).exteriorCover
    · rw [(hOther j hj he).1,(aKeys j hj).1]
      exact (pm.frames j hj).exteriorCover
  have allHigh : ∀ j, ∀ hj : j ≤ logical.top,
      (logical.frames j).high.image Fin.val ⊆ (memory.frames j hj).highObject.keys := by
    intro j hj
    by_cases he : j=logical.top
    · subst j
      rw [hHigh]
      exact bCover
    · rw [(hOther j hj he).2,(aKeys j hj).2]
      exact (pm.frames j hj).highCover
  have allBool : ∀ j ≤ logical.top,
      HighBooleanRecords out.scalar.integerMemory out.scalar.core.mem (16*(ell+3)) (16*(j+1))
        (logical.frames j).theta (parentDomain logical j) := by
    intro j hj
    apply old.boolean_frame memory j hj (parentDomain logical j) (fun _ h => h)
      (pm.frames j hj).highBoolean
    intro v hv
    exact congrFun (bR.trans aR) _
  let finalMemory := memory.finish allExt allBool allHigh
  have ex : MachineEval m g ω highPeekCode st (30+u) out := MachineEval.seq ea eb
  refine ⟨_,out,finalMemory,key,ex,massOut,?_,bSpec,bR.trans aR,
    ex.unit_work highPeekCode_wellFormed (by decide) hh,bQ.trans aQ,bO.trans aO,bH,?_⟩
  · let P := cleanBodyBound (16*(ell+3)) length rank+2
    change memory.queueMass+(f.exteriorObject.mass+f.highObject.mass)=am.queueMass+(f.exteriorObject.mass+next.mass) at hExchange
    have hMul := congrArg (fun z : ℕ => P*z) hExchange
    change u+P*next.mass ≤ P*f.highObject.mass+2*P+(21*rank+20*(16*(ell+3))+70)+6 at bAmort
    change 30+u+P*memory.queueMass ≤ P*pm.queueMass+2*P+(21*rank+20*(16*(ell+3))+70)+36
    simp only [Nat.mul_add] at hMul
    rw [aMass] at hMul
    omega
  · intro z
    exact (bFields z 7 (by omega) (by omega)).trans (congrFun aI _)

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

-- Proof module: Solutions.RecursiveMachineLogicalFrame

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def RecursiveMachineMemory.logical_frame {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical next : RecursiveState n} {st : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hTop : next.top=logical.top) (hStored : next.stored=logical.stored) (hX : next.x=logical.x)
    (hBoundary : next.boundaryEdges=logical.boundaryEdges)
    (hFrames : ∀ j ≤ logical.top, next.frames j=logical.frames j)
    (hDomains : ∀ j ≤ logical.top, parentDomain next j=parentDomain logical j) :
    RecursiveMachineMemory g s α ε ell length next st := by
  have hDegree : recursiveDegreeDomain g s next=recursiveDegreeDomain g s logical := by
    unfold recursiveDegreeDomain
    rw [hStored]
  let frames := fun j hj => (pm.frames j (by rw [←hTop]; exact hj)).logical_frame
    (hFrames j (by rw [←hTop]; exact hj)) (hDomains j (by rw [←hTop]; exact hj))
  refine {
    zero := pm.zero
    top := by rw [hTop]; exact pm.top
    width := pm.width
    alphaRegister := pm.alphaRegister
    one := pm.one
    alphaMemory := pm.alphaMemory
    epsilonMemory := pm.epsilonMemory
    depthMemory := pm.depthMemory
    lengthMemory := pm.lengthMemory
    seedMemory := pm.seedMemory
    allocator := pm.allocator
    potential := by rw [hX]; exact pm.potential
    seedMarker := pm.seedMarker
    boundary := by rw [hBoundary]; exact pm.boundary
    graphCache := by rw [hStored]; exact pm.graphCache
    rowAbove := by rw [hStored]; exact pm.rowAbove
    knownDegree := by rw [hDegree]; exact pm.knownDegree
    unknownDegree := by rw [hDegree]; exact pm.unknownDegree
    frames := frames
    pieceSeparation := ?_
    frameSeparation := ?_
    cacheSeparation := ?_
    output := pm.output
  }
  · intro j hj
    have ho : j ≤ logical.top := by rw [←hTop]; exact hj
    exact pm.pieceSeparation j ho
  · intro i hi j hj hij
    have hi' : i ≤ logical.top := by rw [←hTop]; exact hi
    have hj' : j ≤ logical.top := by rw [←hTop]; exact hj
    exact pm.frameSeparation i hi' j hj' hij
  · intro j hj
    have ho : j ≤ logical.top := by rw [←hTop]; exact hj
    change Disjoint (pm.frames j ho).owned (cachedRowCells g st.scalar.integerMemory (16*(ell+3)) next.stored)
    rw [hStored]
    exact pm.cacheSeparation j ho

def RecursiveMachineMemory.debit {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (producer : ℕ) (cost : ℝ≥0∞) :
    RecursiveMachineMemory g s α ε ell length (NearlyOptimalPPR.Computation.debit logical producer cost) st :=
  pm.logical_frame rfl rfl rfl rfl (by intros; rfl) (by intros; rfl)

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

-- Proof module: Solutions.VertexEnumerationCreation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma vertexEnumeration_injective {n : ℕ} (vertices : List (Fin n)) (h : vertices.Nodup) :
    Function.Injective (vertexEnumeration vertices) := by
  exact List.nodup_iff_injective_getElem.mp h

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

-- Proof module: Solutions.PrincipalEntries

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section


lemma principalRowEntries_length_le {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) (i : Fin k) :
    (principalRowEntries g α e i).length ≤ (g.neighbors (e i)).length+1 := by
  simp only [principalRowEntries,List.length_cons]
  have h := List.length_filterMap_le (f:=fun v => (enumerationIndex e v).map fun j => (⟨i.val,j.val,α-1⟩ : SparseEntry)) (l:=g.neighbors (e i))
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PrincipalEntriesDecode

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

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

-- Proof module: Solutions.ChangePCMemory

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def RecursiveMachineMemory.changePC {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell) (pc : NormalizePC)
    (hI : out.scalar.integerMemory=Function.update st.scalar.integerMemory (levelHeaderAddress logical.top 0) (normalizePCNumber pc : ℤ))
    (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : RecursiveMachineMemory g s α ε ell length
      (NearlyOptimalPPR.Computation.changePC logical pc) out := by
  classical
  let H := levelHeaderAddress logical.top 0
  have hH : 128 ≤ H := levelHeaderAddress_positive _ _
  have hBelow : H < 128+32*((ell+2 : ℕ) : ℤ) := by
    dsimp only [H,levelHeaderAddress]
    omega
  have hOtherSlot : ∀ j slot, slot < 32 → slot ≠ 0 → levelHeaderAddress j slot ≠ H := by
    intro j slot hs hne he
    exact hne (levelHeaderAddress_injective j logical.top slot 0 hs (by decide) he).2
  refine pm.control_frame rfl rfl rfl rfl
    (fun j hj => change_pc_frame_control logical pc j) (fun j hj => change_pc_domain logical pc j)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hR hP hG hO
  · intro z hz hz128
    rw [hI]
    exact Function.update_of_ne (by omega : z ≠ H) _ _
  · intro v field
    rw [hI]
    apply Function.update_of_ne
    have hn := vertexRecordAddress_negative (16*(ell+3)) v.val field
    omega
  · intro j hj slot hs hExclude
    have hSlot : slot ≠ 0 := by intro he; subst slot; simp at hExclude
    rw [hI]
    exact Function.update_of_ne (hOtherSlot j slot hs hSlot) _ _
  · intro j hj
    by_cases he : j=logical.top
    · subst j
      simp [hI,NearlyOptimalPPR.Computation.changePC,changeFrame]
    · have hNe : levelHeaderAddress j 0 ≠ H := by
        intro h
        exact he (levelHeaderAddress_injective j logical.top 0 0 (by decide) (by decide) h).1
      rw [hI,Function.update_of_ne hNe]
      simpa [NearlyOptimalPPR.Computation.changePC,changeFrame,he] using (pm.frames j hj).pc
  · intro j hj
    rw [hI,Function.update_of_ne (hOtherSlot j 9 (by decide) (by decide))]
    by_cases he : j=logical.top <;>
      simpa [NearlyOptimalPPR.Computation.changePC,changeFrame,he] using (pm.frames j hj).openBudget
  · intro j hj
    rw [hI,Function.update_of_ne (hOtherSlot j 10 (by decide) (by decide))]
    by_cases he : j=logical.top <;>
      simpa [NearlyOptimalPPR.Computation.changePC,changeFrame,he] using (pm.frames j hj).needFull
  · intro j hj
    rw [hI,Function.update_of_ne (hOtherSlot j 11 (by decide) (by decide))]
    by_cases he : j=logical.top <;>
      simpa [NearlyOptimalPPR.Computation.changePC,changeFrame,he] using (pm.frames j hj).children
  · intro j hj z hz
    rw [hI]
    apply Function.update_of_ne
    have hAbove := (pm.frames j hj).owned_above z hz
    omega
  · intro z hz
    obtain ⟨v,hv,hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨i,hi,he⟩ := (mem_arrayCells _ z _).mp hz
    rw [hI]
    apply Function.update_of_ne
    have hAbove := pm.rowAbove v hv
    have hi0 := Int.natCast_nonneg i
    omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ChangePCExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma changePCCode_wellFormed (pc : NormalizePC) : (changePCCode pc).wellFormed := levelHeaderIntegerSetCode_wellFormed _ _

set_option maxHeartbeats 7000000 in
lemma change_pc_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ) (pc : NormalizePC)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length (changePC logical pc) out,
      MachineEval m g ω (changePCCode pc) st 10 out ∧ memory.queueMass=pm.queueMass ∧
      out.work=st.work+10 ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨out,ex,hI,hR,hW,hO,hH⟩ := level_header_integer_set_exec m g ω st hh logical.top 0 (normalizePCNumber pc : ℤ) pm.top
  have hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ex.pointer_frame _ (by cases pc <;> decide)
  have hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ex.real_register_frame _ (by cases pc <;> decide)
  let memory := pm.changePC hDepth pc hI hR hP hG hO
  refine ⟨out,memory,ex,rfl,hW,ex.query_frame (by cases pc <;> decide),hO,hH⟩

set_option maxHeartbeats 7000000 in
lemma cheap_change_pc_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ) (pc : NormalizePC)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length (changePC (debit logical logical.top 1) pc) out,
      MachineEval m g ω (changePCCode pc) st 10 out ∧ memory.queueMass=pm.queueMass ∧
      out.work=st.work+10 ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨out,memory,ex,hMass,hW,hQ,hO,hH⟩ := change_pc_exec m g ω logical s α ε ell length pc st hh pm hDepth
  let next := memory.logical_frame (next := changePC (debit logical logical.top 1) pc) rfl rfl rfl rfl (by intros; rfl) (by intros; rfl)
  exact ⟨out,next,ex,hMass,hW,hQ,hO,hH⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.HeaderSetIndexFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma header_set_index_frame (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (level slot width : ℕ) (value : ℤ) (st out : MachineState) (steps : ℕ)
    (hh : st.scalar.halted=false) (h100 : st.scalar.core.ptrs 100=(level : ℤ))
    (ex : MachineEval m g ω (levelHeaderIntegerSetCode slot value) st steps out) :
    ∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress width v.val 7)=
      st.scalar.integerMemory (vertexRecordAddress width v.val 7) := by
  obtain ⟨check,ey,hI,hR,hW,hO,hH⟩ := level_header_integer_set_exec m g ω st hh level slot value h100
  have hOut := (ex.deterministic ey).2
  intro v
  rw [hOut,hI]
  apply Function.update_of_ne
  have := vertexRecordAddress_negative width v.val 7
  have := levelHeaderAddress_positive level slot
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CheapPCExecution

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma cheap_pc_index_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ) (pc : NormalizePC)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length (changePC (debit logical logical.top 1) pc) out,
      MachineEval m g ω (changePCCode pc) st 10 out ∧ memory.queueMass=pm.queueMass ∧
      out.work=st.work+10 ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  obtain ⟨out,memory,ex,hMass,hW,hQ,hO,hH⟩ := cheap_change_pc_exec m g ω logical s α ε ell length pc st hh pm hDepth
  exact ⟨out,memory,ex,hMass,hW,hQ,hO,hH,
    header_set_index_frame m g ω logical.top 0 (16*(ell+3)) (normalizePCNumber pc : ℤ) st out 10 hh pm.top ex⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LeafDecisionExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 30000000 in
lemma leaf_decision_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hα : 0<α ∧ α<1) (hRegion : RegionInvariant logical) (hKeys : KeysInvariant g logical)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames logical.top).cache ∪ (logical.frames logical.top).high, 0<g.graph.degree v)
    (hEpoch : EpochInvariant (n:=n) (16*(ell+3)) st)
    (hMass : pm.queueMass+2*(logical.top+1)*
      (((logical.frames logical.top).cache ∪ (logical.frames logical.top).high).card+
        (volumeNat g ((logical.frames logical.top).cache ∪ (logical.frames logical.top).high)+
          ((logical.frames logical.top).cache ∪ (logical.frames logical.top).high).card)) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let C := (logical.frames logical.top).cache ∪ (logical.frames logical.top).high
    let size := volumeNat g C+C.card
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    let H := 2*P+(21*rank+20*(16*(ell+3))+70)+36
    let A := (C.card+1)*leafPreparationFactor ell logical.top length rank
    let B := leafSolveUnitCost ell logical.top rank C.card size
    let S := A+B+P*(2*(logical.top+1)*size)
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (compilerLeafDecision m g α logical) out,
      MachineEval m g ω leafDecisionCode st steps out ∧ steps ≤ P*pm.queueMass+H+A+B+12 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*(C.card+size) ∧
      out.work+((P*memory.queueMass : ℕ) : ℝ≥0∞) ≤
        st.work+((P*pm.queueMass+(H+S+12) : ℕ) : ℝ≥0∞)+solveCharge m C.card size ∧
      out.output=st.output ∧ out.scalar.halted=false ∧ EpochInvariant (n:=n) (16*(ell+3)) out := by
  dsimp only
  let C := (logical.frames logical.top).cache ∪ (logical.frames logical.top).high
  let size := volumeNat g C+C.card
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let H := 2*P+(21*rank+20*(16*(ell+3))+70)+36
  let A := (C.card+1)*leafPreparationFactor ell logical.top length rank
  let B := leafSolveUnitCost ell logical.top rank C.card size
  let S := A+B+P*(2*(logical.top+1)*size)
  obtain ⟨u,a,am,key,ea,aMass,aAmort,aSpec,aR,aW,aQ,aO,aH,aMarks⟩ := high_peek_exec m g ω logical s α ε ell length N rank st hh pm hDepth (by omega) hCap hPow
  have aAmort' : u+P*am.queueMass ≤ P*pm.queueMass+H := by simpa only [H,P,Nat.add_assoc] using aAmort
  clear aAmort
  have aAmort := aAmort'
  have a53 := ea.pointer_frame 53 (by decide)
  have aEpoch : EpochInvariant (n:=n) (16*(ell+3)) a := fun v => by rw [aMarks v,a53]; exact hEpoch v
  cases hKey : key with
  | none =>
    have hSpec : (logical.frames logical.top).high.image Fin.val=∅ ∧ a.scalar.core.ptrs 97=0 := by
      simpa only [ExteriorPeekSpec,hKey] using aSpec
    have hEmpty := Finset.image_eq_empty.mp hSpec.1
    rw [compilerLeafDecision,if_pos hEmpty]
    obtain ⟨out,memory,eb,bMass,bW,bQ,bO,bH,bMarks⟩ := cheap_pc_index_exec m g ω logical s α ε ell length .afterChild (payUnit a) aH am.payUnit hDepth
    have eBranch : MachineEval m g ω (.branchPointer 97 0 (changePCCode .afterChild) leafJointSolveCode) a 11 out :=
      MachineEval.pointerLe aH (by rw [hSpec.2,am.zero]) eb
    have ex : MachineEval m g ω leafDecisionCode st (u+11) out := MachineEval.seq ea eBranch
    have hMassOut : memory.queueMass=am.queueMass := bMass
    have hUnit : out.work=st.work+(u+11 : ℕ) := by
      rw [bW,payUnit_work,aW]
      push_cast
      ring
    refine ⟨u+11,out,memory,ex,?_,by rw [hMassOut]; omega,?_,bO.trans aO,bH,?_⟩
    · change u+11 ≤ P*pm.queueMass+H+A+B+12
      omega
    · have hNat : u+11+P*memory.queueMass ≤ P*pm.queueMass+(H+S+12) := by rw [hMassOut]; omega
      have hCast : ((u+11+P*memory.queueMass : ℕ) : ℝ≥0∞) ≤ ((P*pm.queueMass+(H+S+12) : ℕ) : ℝ≥0∞) := by exact_mod_cast hNat
      rw [hUnit]
      calc
        _ = st.work+((u+11+P*memory.queueMass : ℕ) : ℝ≥0∞) := by simp only [Nat.cast_add]; ac_rfl
        _ ≤ st.work+((P*pm.queueMass+(H+S+12) : ℕ) : ℝ≥0∞) := add_le_add le_rfl hCast
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · intro v
      rw [bMarks v,(eb.pointer_frame 53 (by decide))]
      exact aEpoch v
  | some k =>
    have hSpec : k ∈ (logical.frames logical.top).high.image Fin.val ∧
        (∀ z ∈ (logical.frames logical.top).high.image Fin.val, k ≤ z) ∧ a.scalar.core.ptrs 97=1 ∧ a.scalar.core.ptrs 40=(k : ℤ) := by
      simpa only [ExteriorPeekSpec,hKey] using aSpec
    obtain ⟨v,hv,hvk⟩ := Finset.mem_image.mp hSpec.1
    have hNonempty : C.Nonempty := ⟨v,Finset.mem_union_right _ hv⟩
    have hNe : (logical.frames logical.top).high ≠ ∅ := by intro he; simpa [he] using hv
    rw [compilerLeafDecision,if_neg hNe]
    obtain ⟨w,b,bm,eb,hSteps,bMass,bAmort,bO,bH,bIndex⟩ := leaf_joint_solve_exec m g ω logical s α ε ell length N rank (a.scalar.core.ptrs 53)
      (payUnit a) aH am.payUnit hDepth hα hRegion hKeys hStored hNonempty hDegree rfl aEpoch (by
        change am.queueMass+2*(logical.top+1)*(C.card+size) ≤ N
        change pm.queueMass+2*(logical.top+1)*(C.card+size) ≤ N at hMass
        omega) hCap hPow
    have eBranch : MachineEval m g ω (.branchPointer 97 0 (changePCCode .afterChild) leafJointSolveCode) a (1+w+1) (payUnit b) :=
      MachineEval.pointerGt aH (by rw [hSpec.2.2.1,am.zero]; norm_num) eb
    have ex : MachineEval m g ω leafDecisionCode st (u+(1+w+1)) (payUnit b) := MachineEval.seq ea eBranch
    change w ≤ P*am.queueMass+A+B+1 at hSteps
    have hNext : (payUnit b).work+((P*bm.payUnit.queueMass : ℕ) : ℝ≥0∞) ≤
        a.work+((P*am.queueMass+(S+2) : ℕ) : ℝ≥0∞)+solveCharge m C.card size := by
      change b.work+((P*bm.queueMass : ℕ) : ℝ≥0∞) ≤ (payUnit a).work+((P*am.queueMass+S : ℕ) : ℝ≥0∞)+solveCharge m C.card size at bAmort
      have h := add_le_add bAmort (le_refl (1 : ℝ≥0∞))
      change b.work+1+((P*bm.queueMass : ℕ) : ℝ≥0∞) ≤ a.work+((P*am.queueMass+(S+2) : ℕ) : ℝ≥0∞)+solveCharge m C.card size
      calc
        _ = (b.work+((P*bm.queueMass : ℕ) : ℝ≥0∞))+1 := by ac_rfl
        _ ≤ ((payUnit a).work+((P*am.queueMass+S : ℕ) : ℝ≥0∞)+solveCharge m C.card size)+1 := h
        _ = _ := by rw [payUnit_work]; simp only [Nat.cast_add,Nat.cast_ofNat]; ring
    have hAll := amortized_unit_prefix st.work a.work (payUnit b).work (solveCharge m C.card size)
      u P pm.queueMass am.queueMass bm.payUnit.queueMass H (S+2) aW aAmort hNext
    refine ⟨u+(1+w+1),payUnit b,bm.payUnit,ex,?_,?_,?_,bO.trans aO,bH,?_⟩
    · change u+(1+w+1) ≤ P*pm.queueMass+H+A+B+12
      omega
    · change bm.queueMass ≤ pm.queueMass+2*(logical.top+1)*(C.card+size)
      change bm.queueMass ≤ am.queueMass+2*(logical.top+1)*(C.card+size) at bMass
      omega
    · exact hAll.trans (add_le_add (add_le_add le_rfl (by exact_mod_cast (show P*pm.queueMass+H+(S+2) ≤ P*pm.queueMass+(H+S+12) by omega))) le_rfl)
    · intro z
      change b.scalar.integerMemory _ ≤ b.scalar.core.ptrs 53
      rw [bIndex.1]
      exact bIndex.2 z

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveCacheTransitions

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma recursive_cache_mass_joint {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) (z : Fin n → ℝ) :
    recursiveCacheMass (jointUpdate g α logical z)=recursiveCacheMass logical := by
  apply recursive_cache_mass_frame logical (jointUpdate g α logical z) rfl
  intro i hi
  simp [jointUpdate,hi]

lemma recursive_cache_mass_refresh {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (T : Finset (Fin n)) :
    recursiveCacheMass (refreshKeys g logical T)=recursiveCacheMass logical := by
  apply recursive_cache_mass_frame logical (refreshKeys g logical T) rfl
  intro i hi
  simp [refreshKeys,hi]

lemma recursive_cache_mass_full {n : ℕ} (m : SolveModel) (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) :
    recursiveCacheMass (compilerFullSolve m g α logical)=recursiveCacheMass logical := by
  unfold compilerFullSolve
  rw [recursive_cache_mass_pc]
  change recursiveCacheMass (compilerFullUpdate g α logical)=recursiveCacheMass logical
  dsimp only [compilerFullUpdate]
  rw [recursive_cache_mass_refresh,recursive_cache_mass_joint]

lemma recursive_cache_mass_cache_union {n : ℕ} (logical : RecursiveState n) :
    recursiveCacheMass (compilerCacheUnion logical)+(logical.frames logical.top).cache.card=
      recursiveCacheMass logical+((logical.frames logical.top).cache ∪ (logical.frames logical.top).high).card := by
  have h := recursive_cache_mass_single_change logical (compilerCacheUnion logical) rfl (by
    intro i hi
    simp [compilerCacheUnion,changeFrame,show i ≠ logical.top by omega])
  simpa only [compilerCacheUnion,changeFrame,Function.update_self] using h

lemma recursive_cache_mass_leaf {n : ℕ} (m : SolveModel) (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) :
    recursiveCacheMass (compilerLeafSolve m g α logical)=recursiveCacheMass (compilerCacheUnion logical) := by
  dsimp only [compilerLeafSolve]
  rw [recursive_cache_mass_debit]
  dsimp only [compilerLeafUpdate]
  rw [recursive_cache_mass_refresh,recursive_cache_mass_joint]

lemma recursive_cache_mass_leaf_growth {n : ℕ} (m : SolveModel) (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) :
    recursiveCacheMass (compilerLeafDecision m g α logical) ≤ recursiveCacheMass logical+
      ((logical.frames logical.top).cache ∪ (logical.frames logical.top).high).card := by
  unfold compilerLeafDecision
  split
  · rw [recursive_cache_mass_pc,recursive_cache_mass_debit]
    omega
  · rw [recursive_cache_mass_leaf]
    have h := recursive_cache_mass_cache_union logical
    omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.InitialEmptyExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma initialEmptyCode_wellFormed : initialEmptyCode.wellFormed :=
  ⟨levelHeaderIntegerToCode_wellFormed _ _,changePCCode_wellFormed _,changePCCode_wellFormed _⟩

set_option maxHeartbeats 9000000 in
lemma initial_empty_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (compilerInitialEmpty logical) out,
      MachineEval m g ω initialEmptyCode st steps out ∧ steps ≤ 22 ∧ memory.queueMass=pm.queueMass ∧
      out.work=st.work+steps ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  obtain ⟨a,ea,a175,aI,aR,aW,aO,aH⟩ := level_header_integer_to_exec m g ω st hh logical.top 3 175 pm.top
  let am := pm.frame aI aR (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ea.pointer_frame _ (by decide)) (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ea.real_register_frame _ (by decide)) aO
  have hCard : a.scalar.core.ptrs 175=((logical.frames logical.top).active.card : ℤ) := a175.trans (pm.frames logical.top le_rfl).activeCount
  by_cases hEmpty : (logical.frames logical.top).active=∅
  · rw [compilerInitialEmpty,if_pos hEmpty]
    obtain ⟨out,memory,eb,bMass,bW,bQ,bO,bH,bIndex⟩ := cheap_pc_index_exec m g ω logical s α ε ell length .normal (payUnit a) aH am.payUnit hDepth
    have eBranch : MachineEval m g ω (.branchPointer 175 0 (changePCCode .normal) (changePCCode .beginEpisode)) a 11 out :=
      MachineEval.pointerLe aH (by rw [hCard,hEmpty,am.zero]; simp) eb
    have ex : MachineEval m g ω initialEmptyCode st 21 out := MachineEval.seq ea eBranch
    exact ⟨21,out,memory,ex,by omega,bMass,
      ex.unit_work initialEmptyCode_wellFormed (by decide) hh,bQ.trans (ea.query_frame (by decide)),bO.trans aO,bH,
      fun v => (bIndex v).trans (congrFun aI _)⟩
  · rw [compilerInitialEmpty,if_neg hEmpty]
    obtain ⟨b,bm,eb,bMass,bW,bQ,bO,bH,bIndex⟩ := cheap_pc_index_exec m g ω logical s α ε ell length .beginEpisode (payUnit a) aH am.payUnit hDepth
    have eBranch : MachineEval m g ω (.branchPointer 175 0 (changePCCode .normal) (changePCCode .beginEpisode)) a 12 (payUnit b) :=
      MachineEval.pointerGt aH (by rw [hCard,am.zero]; exact_mod_cast (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEmpty)).not_ge) eb
    have ex : MachineEval m g ω initialEmptyCode st 22 (payUnit b) := MachineEval.seq ea eBranch
    exact ⟨22,payUnit b,bm.payUnit,ex,by omega,bMass,
      ex.unit_work initialEmptyCode_wellFormed (by decide) hh,bQ.trans (ea.query_frame (by decide)),bO.trans aO,bH,
      fun v => (bIndex v).trans (congrFun aI _)⟩

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

set_option maxHeartbeats 4000000 in
lemma frame_residual_sum_prelude_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (level width : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (h100 : st.scalar.core.ptrs 100=(level : ℤ)) (h50 : st.scalar.core.ptrs 50=(width : ℤ)) :
    ∃ out, MachineEval m g ω frameResidualSumPreludeCode st 19 out ∧
      out.scalar.core.ptrs 94=st.scalar.integerMemory (levelHeaderAddress level 1) ∧
      out.scalar.core.ptrs 83=((16*(level+1)+1 : ℕ) : ℤ) ∧ out.scalar.core.ptrs 41=(width : ℤ) ∧
      out.scalar.core.regs 70=0 ∧ out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+19 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a94,aI,aR,aW,aO,aH⟩ := level_header_integer_to_exec m g ω st hh level 1 94 h100
  have a100 := (ea.pointer_frame 100 (by decide)).trans h100
  have a50 := (ea.pointer_frame 50 (by decide)).trans h50
  obtain ⟨b,eb,bP,bI,bR,bW,bO,bH⟩ := frameResidualSumPointerRoutine.execute m g ω a aH
  have eb8 : MachineEval m g ω frameResidualSumPointerRoutine.code a 8 b := eb
  have b83 : b.scalar.core.ptrs 83=((16*(level+1)+1 : ℕ) : ℤ) := by
    rw [bP]
    simp [frameResidualSumPointerRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,a100]
    ring
  have b41 : b.scalar.core.ptrs 41=(width : ℤ) := by
    rw [bP]
    simp [frameResidualSumPointerRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result,a50]
  let out := payUnit (realWrite b 70 0)
  have ec : MachineEval m g ω (coreCode (.const 70 0)) b 1 out := const_eval m g ω b 70 0 bH
  have ex : MachineEval m g ω frameResidualSumPreludeCode st 19 out := MachineEval.seq ea (MachineEval.seq eb8 ec)
  refine ⟨out,ex,?_,b83,b41,?_,bI.trans aI,bR.trans aR,?_,bO.trans aO,bH⟩
  · exact (ec.pointer_frame 94 (by decide)).trans ((eb.pointer_frame 94 (by decide)).trans a94)
  · simp [out,payUnit,pcSet,realWrite]
  · change b.work+1= _
    rw [bW,aW]
    change st.work+10+8+1= _
    norm_num; ring

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

set_option maxHeartbeats 5000000 in
lemma vertex_residual_sum_body_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width offset : ℕ) (head next : ℤ) (v : Fin n) (r : ℝ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (h41 : st.scalar.core.ptrs 41=(width : ℤ))
    (h83 : st.scalar.core.ptrs 83=(offset : ℤ)) (h94 : st.scalar.core.ptrs 94=head)
    (hKey : st.scalar.integerMemory head=(v.val : ℤ)) (hNext : st.scalar.integerMemory (head+2)=next)
    (hValue : st.scalar.core.mem (vertexRecordAddress width v.val offset)=r) :
    ∃ out, MachineEval m g ω vertexResidualSumBodyCode st (4*width+15) out ∧
      out.scalar.core.ptrs 94=next ∧ out.scalar.core.regs 70=st.scalar.core.regs 70+r ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+(4*width+15 : ℕ) ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a40,a94,a44,aI,aR,aQ,aW,aO,aH⟩ := push_output_read_exec m g ω st hh head next v h94 hKey hNext
  have a83 := (ea.pointer_frame 83 (by decide)).trans h83
  let b := payUnit (pointerWrite a 44 (offset : ℤ))
  have eb : MachineEval m g ω (coreCode (.pcopy 44 83)) a 1 b := by
    simpa only [coreCode,a83,b] using pcopy_eval m g ω a 44 83 aH
  have b44 : b.scalar.core.ptrs 44=(offset : ℤ) := by simp [b,payUnit,pcSet,pointerWrite]
  have b0 := (eb.pointer_frame 0 (by decide)).trans ((ea.pointer_frame 0 (by decide)).trans h0)
  have b40 := (eb.pointer_frame 40 (by decide)).trans a40
  have b41 := (eb.pointer_frame 41 (by decide)).trans ((ea.pointer_frame 41 (by decide)).trans h41)
  obtain ⟨c,ec,c10,cI,cR,cW,cO,cH⟩ := vertex_real_load_exec m g ω b aH width v.val offset b0 b40 b41 b44
  have cValue : c.scalar.core.regs 10=r := by rw [c10]; change a.scalar.core.mem _=r; rw [aR]; exact hValue
  have c70 : c.scalar.core.regs 70=st.scalar.core.regs 70 :=
    (ec.real_register_frame 70 (by decide)).trans ((eb.real_register_frame 70 (by decide)).trans (ea.real_register_frame 70 (by decide)))
  let out := payUnit (realWrite c 70 (st.scalar.core.regs 70+r))
  have ed : MachineEval m g ω (coreCode (.add 70 70 10)) c 1 out := by
    simpa only [coreCode,RealOperation.instruction,RealOperation.value,cValue,c70,out] using binary_eval m g ω c .add 70 70 10 cH
  have ex : MachineEval m g ω vertexResidualSumBodyCode st (4*width+15) out := by
    have ee := MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
    convert ee using 1 <;> (first | rfl | ring)
  refine ⟨out,ex,?_,?_,cI.trans aI,cR.trans aR,ex.query_frame (by decide),?_,cO.trans aO,cH⟩
  · exact (ed.pointer_frame 94 (by decide)).trans ((ec.pointer_frame 94 (by decide)).trans ((eb.pointer_frame 94 (by decide)).trans a94))
  · simp [out,payUnit,pcSet,realWrite]
  · change c.work+1= _
    rw [cW]
    change a.work+1+(4*width+7 : ℕ)+1= _
    rw [aW]
    push_cast
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VertexResidualSumLoop

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 6500000 in
lemma vertex_residual_sum_loop_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (width offset : ℕ) (vertices : List (Fin n)) (head : ℤ) (F : Finset ℤ) (r : Fin n → ℝ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (h0 : st.scalar.core.ptrs 0=0) (h41 : st.scalar.core.ptrs 41=(width : ℤ))
    (h83 : st.scalar.core.ptrs 83=(offset : ℤ)) (h94 : st.scalar.core.ptrs 94=head)
    (hList : VertexListRep st.scalar.integerMemory head vertices F)
    (hValues : ∀ v ∈ vertices, st.scalar.core.mem (vertexRecordAddress width v.val offset)=r v) :
    ∃ out, MachineEval m g ω vertexResidualSumLoopCode st ((4*width+17)*vertices.length+1) out ∧
      out.scalar.core.regs 70=st.scalar.core.regs 70+(vertices.map r).sum ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+((4*width+17)*vertices.length+1 : ℕ) ∧
      out.output=st.output ∧ out.scalar.halted=false := by
  induction vertices generalizing st head F with
  | nil =>
    have hHead : st.scalar.core.ptrs 94=0 := h94.trans hList.nil.1
    refine ⟨payUnit st,MachineEval.pointerDone hh (by rw [hHead,h0]),?_,rfl,rfl,rfl,by simp,rfl,hh⟩
    simp [payUnit,pcSet]
  | cons v vertices ih =>
    obtain ⟨next,S,hPos,hKey,hChild,hNext,hTail,hF,hSep⟩ := hList.cons_view
    obtain ⟨mid,eb,hm94,hm70,hmI,hmR,hmQ,hmW,hmO,hmH⟩ := vertex_residual_sum_body_exec m g ω width offset head next v (r v)
      (payUnit st) hh h0 h41 h83 h94 hKey hNext (hValues v (by simp))
    have hm0 := (eb.pointer_frame 0 (by decide)).trans h0
    have hm41 := (eb.pointer_frame 41 (by decide)).trans h41
    have hm83 := (eb.pointer_frame 83 (by decide)).trans h83
    have hmList : VertexListRep mid.scalar.integerMemory next vertices S := by rw [hmI]; exact hTail
    have hmValues : ∀ u ∈ vertices, mid.scalar.core.mem (vertexRecordAddress width u.val offset)=r u := by
      intro u hu
      rw [hmR]
      exact hValues u (by simp [hu])
    obtain ⟨out,er,ho70,hoI,hoR,hoQ,hoW,hoO,hoH⟩ := ih next S (payUnit mid) hmH hm0 hm41 hm83 hm94 hmList hmValues
    have ex : MachineEval m g ω vertexResidualSumLoopCode st ((4*width+17)*(v::vertices).length+1) out := by
      have ee := MachineEval.pointerNext (r:=94) (s:=0) hh (by rw [h94,h0]; omega) eb er
      convert ee using 1 <;> (first | rfl | simp only [List.length_cons]; ring)
    refine ⟨out,ex,?_,hoI.trans hmI,hoR.trans hmR,hoQ.trans hmQ,?_,hoO.trans hmO,hoH⟩
    · rw [ho70]
      change mid.scalar.core.regs 70+_= _
      rw [hm70]
      simp only [payUnit_regs,List.map_cons,List.sum_cons]
      ring
    · rw [hoW,payUnit_work,hmW,payUnit_work]
      simp only [List.length_cons]
      push_cast
      ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameResidualSumExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma frameResidualSumCode_wellFormed : frameResidualSumCode.wellFormed :=
  ⟨frameResidualSumPreludeCode_wellFormed,vertexResidualSumBodyCode_wellFormed⟩

set_option maxHeartbeats 7000000 in
lemma frame_residual_sum_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hSubset : (logical.frames logical.top).active ⊆ parentDomain logical logical.top) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω frameResidualSumCode st
        ((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+20) out ∧
      out.scalar.core.regs 70=∑ v ∈ (logical.frames logical.top).active, (logical.frames logical.top).residual v ∧
      memory.queueMass=pm.queueMass ∧
      out.work=st.work+((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+20 : ℕ) ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let f := pm.frames logical.top le_rfl
  obtain ⟨pre,ep,h94,h83,h41,h70,hI,hR,hW,hO,hH⟩ := frame_residual_sum_prelude_exec m g ω logical.top (16*(ell+3)) st hh pm.top pm.width
  have h0 := (ep.pointer_frame 0 (by decide)).trans pm.zero
  have hList : VertexListRep pre.scalar.integerMemory (st.scalar.integerMemory (levelHeaderAddress logical.top 1)) f.activeVertices f.activeFoot := by
    rw [hI]
    exact f.activeRep
  have hValues : ∀ v ∈ f.activeVertices,
      pre.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val (16*(logical.top+1)+1))=(logical.frames logical.top).residual v := by
    intro v hv
    rw [hR]
    apply f.residual
    apply hSubset
    rw [←f.activeSet]
    exact List.mem_toFinset.mpr hv
  obtain ⟨out,el,ho70,hoI,hoR,hoQ,hoW,hoO,hoH⟩ := vertex_residual_sum_loop_exec m g ω (16*(ell+3)) (16*(logical.top+1)+1)
    f.activeVertices (st.scalar.integerMemory (levelHeaderAddress logical.top 1)) f.activeFoot (logical.frames logical.top).residual
    pre hH h0 h41 h83 h94 hList hValues
  have hLength : f.activeVertices.length=(logical.frames logical.top).active.card := by
    rw [←f.activeSet,List.toFinset_card_of_nodup f.activeNodup]
  have hSum : (f.activeVertices.map (logical.frames logical.top).residual).sum=
      ∑ v ∈ (logical.frames logical.top).active, (logical.frames logical.top).residual v := by
    rw [←f.activeSet]
    exact (List.sum_toFinset _ f.activeNodup).symm
  have ex : MachineEval m g ω frameResidualSumCode st
      ((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+20) out := by
    have ee := MachineEval.seq ep el
    rw [hLength] at ee
    convert ee using 1 <;> (first | rfl | omega)
  have hFinalI : out.scalar.integerMemory=st.scalar.integerMemory := hoI.trans hI
  have hFinalR : out.scalar.core.mem=st.scalar.core.mem := hoR.trans hR
  have hFinalO : out.output=st.output := hoO.trans hO
  let memory := pm.frame hFinalI hFinalR
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> exact ex.pointer_frame _ (by decide))
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl <;> exact ex.real_register_frame _ (by decide)) hFinalO
  refine ⟨out,memory,ex,?_,rfl,?_,ex.query_frame (by decide),hFinalO,hoH⟩
  · rw [ho70,h70,hSum,zero_add]
  · rw [hoW,hW,hLength]
    push_cast
    ring

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

lemma clear_vertex_field_set_other_field {n : ℕ} (width offset field : ℕ) (T : Finset (Fin n)) (I : ℤ → ℤ)
    (ho : offset < width) (hf : field < width) (hne : field ≠ offset) (v : Fin n) :
    clearVertexFieldSetRecords width offset T I (vertexRecordAddress width v.val field)=I (vertexRecordAddress width v.val field) := by
  apply if_neg
  intro hm
  obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hm
  exact hne (vertexRecordAddress_injective width v.val u.val field offset hf ho he.symm).2

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerFullEmpty

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_full_update_empty {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (hEmpty : (logical.frames logical.top).active=∅) : compilerFullUpdate g α logical=logical := by
  have hSolve : solveOn g α (logical.frames logical.top).active (logical.frames logical.top).residual=0 := by
    rw [hEmpty]
    funext v
    simp [solveOn]
  dsimp only [compilerFullUpdate]
  rw [hSolve,hEmpty]
  simp [jointUpdate,refreshKeys,touchedBy]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EmptyFullSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 8000000 in
lemma empty_full_solve_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hEmpty : (logical.frames logical.top).active=∅) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length (compilerFullSolve m g α logical) out,
      MachineEval m g ω (changePCCode .normalize) st 10 out ∧ memory.queueMass=pm.queueMass ∧
      out.work=st.work+10 ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      out.scalar.core.ptrs 53=st.scalar.core.ptrs 53 ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  have hUpdate := compiler_full_update_empty g α logical hEmpty
  have hFrames (j : ℕ) : (compilerFullCharged m g α logical).frames j=logical.frames j := by
    change (compilerFullUpdate g α logical).frames j=logical.frames j
    rw [hUpdate]
  let cm := pm.logical_frame (next:=compilerFullCharged m g α logical) rfl rfl
    (by change (compilerFullUpdate g α logical).x=logical.x; rw [hUpdate]) rfl (by intro j hj; exact hFrames j) (by
      intro j hj
      unfold parentDomain
      split_ifs
      · rfl
      · exact congrArg NormalizeFrame.active (hFrames (j-1)))
  obtain ⟨out,memory,ex,hMass,hW,hQ,hO,hH⟩ := change_pc_exec m g ω (compilerFullCharged m g α logical) s α ε ell length .normalize st hh cm hDepth
  exact ⟨out,memory,ex,hMass,hW,hQ,hO,hH,ex.pointer_frame 53 (by decide),
    header_set_index_frame m g ω logical.top 0 (16*(ell+3)) (normalizePCNumber .normalize : ℤ) st out 10 hh pm.top ex⟩

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

set_option maxHeartbeats 3000000 in
lemma active_joint_prelude_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (level width : ℕ)
    (hl : st.scalar.core.ptrs 100=(level : ℤ)) (hw : st.scalar.core.ptrs 50=(width : ℤ)) :
    ∃ out, MachineEval m g ω activeJointSolvePreludeCode st 20 out ∧
      out.scalar.core.ptrs 90=st.scalar.integerMemory (levelHeaderAddress level 1) ∧
      out.scalar.core.ptrs 83=((16*(level+1)+1 : ℕ) : ℤ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+20 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a90,aI,aR,aW,aO,aH⟩ := level_header_integer_to_exec m g ω st hh level 1 90 hl
  obtain ⟨b,eb,b87,b89,b41,bI,bR,bQ,bW,bO,bH⟩ := level_context_exec m g ω a aH level width
    ((ea.pointer_frame 100 (by decide)).trans hl) ((ea.pointer_frame 50 (by decide)).trans hw)
  obtain ⟨out,ec,cP,cI,cR,cW,cO,cH⟩ := activeJointOffsetRoutine.execute m g ω b bH
  have ex : MachineEval m g ω activeJointSolvePreludeCode st 20 out := MachineEval.seq ea (MachineEval.seq eb ec)
  refine ⟨out,ex,?_,?_,cI.trans (bI.trans aI),cR.trans (bR.trans aR),
    ex.unit_work activeJointSolvePreludeCode_wellFormed (by decide) hh,cO.trans (bO.trans aO),cH⟩
  · exact ((ec.pointer_frame 90 (by decide)).trans (eb.pointer_frame 90 (by decide))).trans a90
  · rw [cP]
    simp [activeJointOffsetRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,
      PointerOp.result,b87]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ActiveJointSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 20000000 in
lemma active_joint_solve_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ) (epoch : ℤ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hα : 0<α ∧ α<1) (hNonempty : (logical.frames logical.top).active.Nonempty)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames logical.top).active, 0<g.graph.degree v)
    (hRegion : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hEpoch : st.scalar.core.ptrs 53=epoch)
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch)
    (hKeys : KeysInvariant g logical)
    (hSubset : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (hMass : pm.queueMass+2*(logical.top+1)*
      (volumeNat g (logical.frames logical.top).active+(logical.frames logical.top).active.card) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let C := (logical.frames logical.top).active
    let size := volumeNat g C+C.card
    let cost := (10*C.card+5)+((24*(16*(ell+3))+100)*size+28)+
      (jointSolveIterationFactor ell logical.top rank*size+5)+20
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length
      (refreshKeys g (jointUpdate g α logical (solveOn g α C (logical.frames logical.top).residual)) (touchedBy g C)) out,
      MachineEval m g ω activeJointSolveCode st steps out ∧ steps ≤ cost+1 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*size ∧
      out.work ≤ st.work+(cost : ℕ)+solveCharge m C.card size ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (out.scalar.core.ptrs 53=epoch+1 ∧ ∀ v : Fin n,
        out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch+1) := by
  dsimp only
  let f := pm.frames logical.top le_rfl
  obtain ⟨pre,ep,h90,h83,hI,hR,hpWork,aO,aH⟩ := active_joint_prelude_exec m g ω st hh logical.top (16*(ell+3)) pm.top pm.width
  let preMemory := pm.frame hI hR
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> exact ep.pointer_frame _ (by decide))
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl <;> exact ep.real_register_frame _ (by decide)) (aO : pre.output=st.output)
  have hList : VertexListRep pre.scalar.integerMemory (st.scalar.integerMemory (levelHeaderAddress logical.top 1)) f.activeVertices f.activeFoot := by
    rw [hI]; exact f.activeRep
  have hBelow : ∀ z ∈ f.activeFoot, z < pre.scalar.core.ptrs 20 := by
    intro z hz
    rw [ep.pointer_frame 20 (by decide)]
    exact f.activeBelow z hz
  have hLength : f.activeVertices.length=(logical.frames logical.top).active.card := by
    rw [←f.activeSet,List.toFinset_card_of_nodup f.activeNodup]
  have hMembership : ∀ v ∈ f.activeVertices, v ∈ (logical.frames logical.top).active := by
    intro v hv
    rw [←f.activeSet]
    exact List.mem_toFinset.mpr hv
  have hBudget : preMemory.queueMass+2*(logical.top+1)*(volumeNat g f.activeVertices.toFinset+f.activeVertices.toFinset.card) ≤ N := by
    rw [f.activeSet]
    exact hMass
  have result := list_joint_solve_exec m g ω logical s α ε ell length N rank (16*(logical.top+1)+1)
    f.activeVertices (st.scalar.integerMemory (levelHeaderAddress logical.top 1)) epoch f.activeFoot f.activeNodup
      (by rw [hLength]; exact Finset.card_pos.mpr hNonempty) (fun v hv => hDegree v (hMembership v hv)) hα (logical.frames logical.top).residual pre aH preMemory hDepth
      (fun v hv => hStored (hMembership v hv)) h90 hList hBelow ((ep.pointer_frame 53 (by decide)).trans hEpoch) h83
      (fun v hv => (congrFun hR _).trans (f.residual v (hRegion (hMembership v hv)))) (by rw [hI]; exact hbound)
      hKeys hSubset hBudget hCap hPow
  rw [f.activeSet] at result
  obtain ⟨u,out,memory,ex,hu,hMassOut,hWork,hOutput,hHalt,hIndex⟩ := result
  have hCost : (10*f.activeVertices.length+5)+
      ((24*(16*(ell+3))+100)*(volumeNat g (logical.frames logical.top).active+(logical.frames logical.top).active.card)+28)+
      (jointSolveIterationFactor ell logical.top rank*(volumeNat g (logical.frames logical.top).active+(logical.frames logical.top).active.card)+5)=
      (10*(logical.frames logical.top).active.card+5)+
      ((24*(16*(ell+3))+100)*(volumeNat g (logical.frames logical.top).active+(logical.frames logical.top).active.card)+28)+
      (jointSolveIterationFactor ell logical.top rank*(volumeNat g (logical.frames logical.top).active+(logical.frames logical.top).active.card)+5) := by rw [hLength]
  rw [hCost] at hu hWork
  have hCapacity := vertex_list_capacity g f.activeVertices f.activeNodup
  rw [f.activeSet] at hCapacity
  have hEntries := principal_entries_length_le g α (vertexEnumeration f.activeVertices)
  have hCharge := solveCharge_mono m hLength.le (hEntries.trans_eq hCapacity)
  have eRun : MachineEval m g ω activeJointSolveCode st (20+u) out := MachineEval.seq ep ex
  refine ⟨_,out,memory,eRun,by omega,hMassOut,?_,hOutput.trans aO,hHalt,hIndex⟩
  rw [hpWork] at hWork
  have hh := hWork.trans (add_le_add le_rfl hCharge)
  have hAssoc (A : ℕ) (Z : ℝ≥0∞) :
      st.work+20+(A : ℝ≥0∞)+Z=st.work+((A+20 : ℕ) : ℝ≥0∞)+Z := by
    simp only [Nat.cast_add,Nat.cast_ofNat]
    ac_rfl
  rw [←hAssoc]
  exact hh

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FullJointSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 20000000 in
lemma full_joint_solve_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ) (epoch : ℤ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hα : 0<α ∧ α<1) (hNonempty : (logical.frames logical.top).active.Nonempty)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames logical.top).active, 0<g.graph.degree v)
    (hRegion : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hEpoch : st.scalar.core.ptrs 53=epoch)
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch)
    (hKeys : KeysInvariant g logical)
    (hSubset : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (hMass : pm.queueMass+2*(logical.top+1)*
      (volumeNat g (logical.frames logical.top).active+(logical.frames logical.top).active.card) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let C := (logical.frames logical.top).active
    let size := volumeNat g C+C.card
    let cost := (10*C.card+5)+((24*(16*(ell+3))+100)*size+28)+
      (jointSolveIterationFactor ell logical.top rank*size+5)+30
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length
      (compilerFullSolve m g α logical) out,
      MachineEval m g ω fullJointSolveCode st steps out ∧ steps ≤ cost+1 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*size ∧
      out.work ≤ st.work+(cost : ℕ)+solveCharge m C.card size ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (out.scalar.core.ptrs 53=epoch+1 ∧ ∀ v : Fin n,
        out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch+1) := by
  dsimp only
  let C := (logical.frames logical.top).active
  let size := volumeNat g C+C.card
  let A := (10*C.card+5)+((24*(16*(ell+3))+100)*size+28)+
    (jointSolveIterationFactor ell logical.top rank*size+5)+20
  obtain ⟨u,a,am,ea,hu,aMass,aW,aO,aH,aIndex⟩ := active_joint_solve_exec m g ω logical s α ε ell length N rank epoch st hh pm hDepth
    hα hNonempty hStored hDegree hRegion hEpoch hbound hKeys hSubset hMass hCap hPow
  let chargedMemory := am.logical_frame (next:=compilerFullCharged m g α logical) rfl rfl rfl rfl
    (by intros; rfl) (by intros; rfl)
  obtain ⟨out,memory,eb,bMass,bW,bQ,bO,bH⟩ := change_pc_exec m g ω (compilerFullCharged m g α logical)
    s α ε ell length .normalize a aH chargedMemory hDepth
  have ex : MachineEval m g ω fullJointSolveCode st (u+10) out := MachineEval.seq ea eb
  have bIndex := header_set_index_frame m g ω (compilerFullCharged m g α logical).top 0 (16*(ell+3))
    (normalizePCNumber .normalize : ℤ) a out 10 aH chargedMemory.top eb
  refine ⟨u+10,out,memory,ex,by omega,?_,?_,bO.trans aO,bH,?_,?_⟩
  · change memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*size
    change memory.queueMass=am.queueMass at bMass
    rw [bMass]
    exact aMass
  · change out.work ≤ st.work+((A+10 : ℕ) : ℝ≥0∞)+solveCharge m C.card size
    change a.work ≤ st.work+(A : ℕ)+solveCharge m C.card size at aW
    rw [bW]
    calc
      _ ≤ (st.work+(A : ℕ)+solveCharge m C.card size)+10 := add_le_add aW le_rfl
      _ = _ := by simp only [Nat.cast_add,Nat.cast_ofNat]; ac_rfl
  · exact (eb.pointer_frame 53 (by decide)).trans aIndex.1
  · intro v
    rw [bIndex v]
    exact aIndex.2 v

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FullSolveDecisionExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 20000000 in
lemma full_solve_decision_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hα : 0<α ∧ α<1)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames logical.top).active, 0<g.graph.degree v)
    (hRegion : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hEpoch : EpochInvariant (n:=n) (16*(ell+3)) st)
    (hKeys : KeysInvariant g logical)
    (hSubset : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (hMass : pm.queueMass+2*(logical.top+1)*
      (volumeNat g (logical.frames logical.top).active+(logical.frames logical.top).active.card) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let C := (logical.frames logical.top).active
    let size := volumeNat g C+C.card
    let cost := (10*C.card+5)+((24*(16*(ell+3))+100)*size+28)+
      (jointSolveIterationFactor ell logical.top rank*size+5)+42
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length
      (compilerFullSolve m g α logical) out,
      MachineEval m g ω fullSolveDecisionCode st steps out ∧ steps ≤ cost+1 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*size ∧
      out.work ≤ st.work+(cost : ℕ)+solveCharge m C.card size ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      EpochInvariant (n:=n) (16*(ell+3)) out := by
  dsimp only
  let C := (logical.frames logical.top).active
  let size := volumeNat g C+C.card
  let A := (10*C.card+5)+((24*(16*(ell+3))+100)*size+28)+
    (jointSolveIterationFactor ell logical.top rank*size+5)+30
  obtain ⟨a,ea,a175,aI,aR,aW,aO,aH⟩ := level_header_integer_to_exec m g ω st hh logical.top 3 175 pm.top
  let am := pm.frame aI aR (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ea.pointer_frame _ (by decide)) (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ea.real_register_frame _ (by decide)) aO
  have hCard : a.scalar.core.ptrs 175=(C.card : ℤ) := a175.trans (pm.frames logical.top le_rfl).activeCount
  have aEpoch : EpochInvariant (n:=n) (16*(ell+3)) a := by
    intro v
    rw [congrFun aI _,ea.pointer_frame 53 (by decide)]
    exact hEpoch v
  by_cases hEmpty : C=∅
  · obtain ⟨out,memory,eb,bMass,bW,bQ,bO,bH,b53,bMarks⟩ := empty_full_solve_exec m g ω logical s α ε ell length
      (payUnit a) aH am.payUnit hDepth hEmpty
    have eBranch : MachineEval m g ω (.branchPointer 175 0 (changePCCode .normalize) fullJointSolveCode) a 11 out :=
      MachineEval.pointerLe aH (by rw [hCard,hEmpty,am.zero]; simp) eb
    have ex : MachineEval m g ω fullSolveDecisionCode st 21 out := MachineEval.seq ea eBranch
    refine ⟨21,out,memory,ex,by omega,?_,?_,bO.trans aO,bH,?_⟩
    · change memory.queueMass=pm.queueMass at bMass
      rw [bMass]
      omega
    · have work : out.work=st.work+21 := by rw [bW,payUnit_work,aW]; norm_num; ring
      rw [work]
      have hBound : (21 : ℝ≥0∞) ≤ ((10*C.card+5)+((24*(16*(ell+3))+100)*size+28)+(jointSolveIterationFactor ell logical.top rank*size+5)+42 : ℕ) := by exact_mod_cast (show 21 ≤ (10*C.card+5)+((24*(16*(ell+3))+100)*size+28)+(jointSolveIterationFactor ell logical.top rank*size+5)+42 by omega)
      exact (add_le_add le_rfl hBound).trans (le_add_of_nonneg_right (by positivity))
    · intro v
      rw [bMarks v,b53]
      exact aEpoch v
  · obtain ⟨u,b,bm,eb,hu,bMass,bW,bO,bH,bIndex⟩ := full_joint_solve_exec m g ω logical s α ε ell length N rank (a.scalar.core.ptrs 53)
      (payUnit a) aH am.payUnit hDepth hα (Finset.nonempty_iff_ne_empty.mpr hEmpty) hStored hDegree hRegion rfl aEpoch hKeys hSubset hMass hCap hPow
    have eBranch : MachineEval m g ω (.branchPointer 175 0 (changePCCode .normalize) fullJointSolveCode) a (1+u+1) (payUnit b) :=
      MachineEval.pointerGt aH (by rw [hCard,am.zero]; exact_mod_cast (show ¬C.card ≤ 0 by have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEmpty); omega)) eb
    have ex : MachineEval m g ω fullSolveDecisionCode st (10+(1+u+1)) (payUnit b) := MachineEval.seq ea eBranch
    refine ⟨_,payUnit b,bm.payUnit,ex,by omega,bMass,?_,bO.trans aO,bH,?_⟩
    · change b.work ≤ (payUnit a).work+(A : ℕ)+solveCharge m C.card size at bW
      change b.work+1 ≤ st.work+((A+12 : ℕ) : ℝ≥0∞)+solveCharge m C.card size
      calc
        _ ≤ ((payUnit a).work+(A : ℕ)+solveCharge m C.card size)+1 := add_le_add bW le_rfl
        _ = _ := by rw [payUnit_work,aW]; push_cast; ring
    · intro v
      change b.scalar.integerMemory _ ≤ b.scalar.core.ptrs 53
      rw [bIndex.1]
      exact bIndex.2 v

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

lemma finish_raw_integer_field {n : ℕ} (I : ℤ → ℤ) (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (v : Fin n) (field : ℕ) (hf : field < 16*(ell+3))
    (hNe : field ≠ 16*(logical.top+1)+4) :
    finishEpisodeIntegerMemory I logical ell (vertexRecordAddress (16*(ell+3)) v.val field)=
      I (vertexRecordAddress (16*(ell+3)) v.val field) := by
  rw [finish_raw_integer_below _ _ _ _ (by have := vertexRecordAddress_negative (16*(ell+3)) v.val field; omega)]
  exact clear_vertex_field_set_other_field _ _ _ _ _ (by omega) hf hNe v

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FinishEpisodeIndexFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma finish_episode_index_frame (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st out : MachineState) (steps : ℕ) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (ex : MachineEval m g ω finishEpisodeCode st steps out) :
    ∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
      st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) := by
  obtain ⟨check,ey,hI,hCache,hR,hW,hQ,hO,hH⟩ := finish_episode_raw_exec m g ω logical s α ε ell length st hh pm hDepth
  have hOut := (ex.deterministic ey).2
  intro v
  rw [hOut,hI]
  exact finish_raw_integer_field _ _ _ hDepth v 7 (by omega) (by omega)

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

set_option maxHeartbeats 3000000 in
lemma need_full_arithmetic_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) :
    ∃ out, MachineEval m g ω needFullArithmeticCode st 3 out ∧
      out.scalar.core.regs 76=st.scalar.core.regs 75/2-st.scalar.core.regs 70 ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+3 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨ex,hW,hH⟩ := linear_execute m g ω needFullArithmeticInstructions
    (by simp [needFullArithmeticInstructions,unitInstruction,straightInstruction]) st hh
  refine ⟨_,ex,?_,?_,?_,hW,?_,hH⟩
  all_goals simp [linearRun,needFullArithmeticInstructions,atomState,machineStep,pcSet,hh,LocalPush.step,
    scalarProgram,LocalPush.coreProgram,SmaleNinth.RAMStep,div_eq_mul_inv]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SetNeedFullMemory

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def RecursiveMachineMemory.setNeedFull {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell) (need : Bool)
    (hI : out.scalar.integerMemory=Function.update st.scalar.integerMemory (levelHeaderAddress logical.top 10) (if need then 1 else 0))
    (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : RecursiveMachineMemory g s α ε ell length
      (compilerSetNeedFull logical need) out := by
  classical
  let H := levelHeaderAddress logical.top 10
  have hH : 128 ≤ H := levelHeaderAddress_positive _ _
  have hBelow : H < 128+32*((ell+2 : ℕ) : ℤ) := by
    dsimp only [H,levelHeaderAddress]
    omega
  have hOtherSlot : ∀ j slot, slot < 32 → slot ≠ 10 → levelHeaderAddress j slot ≠ H := by
    intro j slot hs hne he
    exact hne (levelHeaderAddress_injective j logical.top slot 10 hs (by decide) he).2
  refine pm.control_frame rfl rfl rfl rfl
    (fun j hj => set_need_full_frame_control logical need j) (fun j hj => set_need_full_domain logical need j)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hR hP hG hO
  · intro z hz hz128
    rw [hI]
    exact Function.update_of_ne (by omega : z ≠ H) _ _
  · intro v field
    rw [hI]
    apply Function.update_of_ne
    have hn := vertexRecordAddress_negative (16*(ell+3)) v.val field
    omega
  · intro j hj slot hs hExclude
    have hSlot : slot ≠ 10 := by intro he; subst slot; simp at hExclude
    rw [hI]
    exact Function.update_of_ne (hOtherSlot j slot hs hSlot) _ _
  · intro j hj
    rw [hI,Function.update_of_ne (hOtherSlot j 0 (by decide) (by decide))]
    by_cases he : j=logical.top <;>
      simpa [compilerSetNeedFull,changeFrame,he] using (pm.frames j hj).pc
  · intro j hj
    rw [hI,Function.update_of_ne (hOtherSlot j 9 (by decide) (by decide))]
    by_cases he : j=logical.top <;>
      simpa [compilerSetNeedFull,changeFrame,he] using (pm.frames j hj).openBudget
  · intro j hj
    by_cases he : j=logical.top
    · subst j
      simp [hI,compilerSetNeedFull,changeFrame]
    · have hNe : levelHeaderAddress j 10 ≠ H := by
        intro h
        exact he (levelHeaderAddress_injective j logical.top 10 10 (by decide) (by decide) h).1
      rw [hI,Function.update_of_ne hNe]
      simpa [compilerSetNeedFull,changeFrame,he] using (pm.frames j hj).needFull
  · intro j hj
    rw [hI,Function.update_of_ne (hOtherSlot j 11 (by decide) (by decide))]
    by_cases he : j=logical.top <;>
      simpa [compilerSetNeedFull,changeFrame,he] using (pm.frames j hj).children
  · intro j hj z hz
    rw [hI]
    apply Function.update_of_ne
    have hAbove := (pm.frames j hj).owned_above z hz
    omega
  · intro z hz
    obtain ⟨v,hv,hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨i,hi,he⟩ := (mem_arrayCells _ z _).mp hz
    rw [hI]
    apply Function.update_of_ne
    have hAbove := pm.rowAbove v hv
    have hi0 := Int.natCast_nonneg i
    omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SetNeedFullExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma setNeedFullCode_wellFormed (need : Bool) : (setNeedFullCode need).wellFormed := levelHeaderIntegerSetCode_wellFormed _ _

set_option maxHeartbeats 7000000 in
lemma set_need_full_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ) (need : Bool)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length (compilerSetNeedFull logical need) out,
      MachineEval m g ω (setNeedFullCode need) st 10 out ∧ memory.queueMass=pm.queueMass ∧
      out.work=st.work+10 ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  obtain ⟨out,ex,hI,hR,hW,hO,hH⟩ := level_header_integer_set_exec m g ω st hh logical.top 10 (if need then 1 else 0) pm.top
  have hP : ∀ r ∈ ([0,20,50,100] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ex.pointer_frame _ (by cases need <;> decide)
  have hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ex.real_register_frame _ (by cases need <;> decide)
  let memory := pm.setNeedFull hDepth need hI hR hP hG hO
  refine ⟨out,memory,ex,rfl,hW,ex.query_frame (by cases need <;> decide),hO,hH,?_⟩
  intro v
  rw [hI]
  apply Function.update_of_ne
  have := vertexRecordAddress_negative (16*(ell+3)) v.val 7
  have := levelHeaderAddress_positive logical.top 10
  omega

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

set_option maxHeartbeats 16000000 in
lemma need_full_decision_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε mu : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (h70 : st.scalar.core.regs 70=mu) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length
      (compilerSetNeedFull logical (decide ((logical.frames logical.top).Q/2 ≤ mu))) out,
      MachineEval m g ω needFullDecisionCode st steps out ∧ steps ≤ 25 ∧
      memory.queueMass=pm.queueMass ∧ out.work=st.work+steps ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  classical
  obtain ⟨a,ea,a75,aI,aR,aW,aO,aH⟩ := level_header_real_to_exec m g ω st hh logical.top 3 75 pm.top pm.one
  obtain ⟨b,eb,b76,bI,bR,bW,bO,bH⟩ := need_full_arithmetic_exec m g ω a aH
  have ep : MachineEval m g ω needFullPrepareCode st 13 b := MachineEval.seq ea eb
  have hI := bI.trans aI
  have hR := bR.trans aR
  have hO := bO.trans aO
  have hP : ∀ r ∈ ([0,20,50,100] : List ℕ), b.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ep.pointer_frame _ (by decide)
  have hG : ∀ r ∈ ([30,31] : List ℕ), b.scalar.core.regs r=st.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ep.real_register_frame _ (by decide)
  let bm := pm.frame hI hR hP hG hO
  have h76 : b.scalar.core.regs 76=(logical.frames logical.top).Q/2-mu := by
    rw [b76,a75,(ea.real_register_frame 70 (by decide)).trans h70,(pm.frames logical.top le_rfl).Q]
  by_cases hTest : (logical.frames logical.top).Q/2 ≤ mu
  · have hBool : decide ((logical.frames logical.top).Q/2 ≤ mu)=true := by simp [hTest]
    rw [hBool]
    obtain ⟨out,memory,ec,hMass,hWork,hQuery,hOutput,hHalt,hIndex⟩ :=
      set_need_full_exec m g ω logical s α ε ell length true (payUnit b) bH bm.payUnit hDepth
    have ec' : MachineEval m g ω (.branchReal 76 (setNeedFullCode true) (setNeedFullCode false)) b 11 out :=
      MachineEval.realNonpos bH (by rw [h76]; exact sub_nonpos.mpr hTest) ec
    have ex : MachineEval m g ω needFullDecisionCode st 24 out := MachineEval.seq ep ec'
    exact ⟨_,out,memory,ex,by omega,hMass,ex.unit_work needFullDecisionCode_wellFormed (by decide) hh,
      hQuery.trans (ep.query_frame (by decide)),hOutput.trans hO,hHalt,fun v => (hIndex v).trans (congrFun hI _)⟩
  · have hBool : decide ((logical.frames logical.top).Q/2 ≤ mu)=false := by simp [hTest]
    rw [hBool]
    obtain ⟨out,memory,ec,hMass,hWork,hQuery,hOutput,hHalt,hIndex⟩ :=
      set_need_full_exec m g ω logical s α ε ell length false (payUnit b) bH bm.payUnit hDepth
    have ec' : MachineEval m g ω (.branchReal 76 (setNeedFullCode true) (setNeedFullCode false)) b 12 (payUnit out) :=
      MachineEval.realPos bH (by rw [h76]; exact fun h => hTest (sub_nonpos.mp h)) ec
    have ex : MachineEval m g ω needFullDecisionCode st 25 (payUnit out) := MachineEval.seq ep ec'
    exact ⟨_,payUnit out,memory.payUnit,ex,by omega,hMass,ex.unit_work needFullDecisionCode_wellFormed (by decide) hh,
      hQuery.trans (ep.query_frame (by decide)),hOutput.trans hO,hHalt,fun v => (hIndex v).trans (congrFun hI _)⟩

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

set_option maxHeartbeats 8000000 in
lemma return_pc_prepare_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (level : ℕ) (st : MachineState) (hh : st.scalar.halted=false)
    (h100 : st.scalar.core.ptrs 100=(level : ℤ)) (h31 : st.scalar.core.regs 31=1) :
    ∃ out, MachineEval m g ω returnPCPrepareCode st 21 out ∧
      out.scalar.core.regs 77=st.scalar.core.mem (levelHeaderAddress level 5) ∧
      out.scalar.core.regs 78=st.scalar.core.mem (levelHeaderAddress level 1) ∧
      out.scalar.core.regs 79=st.scalar.core.mem (levelHeaderAddress level 5)-st.scalar.core.mem (levelHeaderAddress level 1) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.work=st.work+21 ∧ out.output=st.output ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,a77,aI,aR,aW,aO,aH⟩ := level_header_real_to_exec m g ω st hh level 5 77 h100 h31
  obtain ⟨b,eb,b78,bI,bR,bW,bO,bH⟩ := level_header_real_to_exec m g ω a aH level 1 78
    ((ea.pointer_frame 100 (by decide)).trans h100) ((ea.real_register_frame 31 (by decide)).trans h31)
  let out := payUnit (realWrite b 79 (b.scalar.core.regs 77-b.scalar.core.regs 78))
  have ec : MachineEval m g ω (coreCode (.sub 79 77 78)) b 1 out := binary_eval m g ω b .sub 79 77 78 bH
  have ex : MachineEval m g ω returnPCPrepareCode st 21 out := MachineEval.seq ea (MachineEval.seq eb ec)
  have b77 := (eb.real_register_frame 77 (by decide)).trans a77
  have b78' : b.scalar.core.regs 78=st.scalar.core.mem (levelHeaderAddress level 1) := by rw [b78,aR]
  refine ⟨out,ex,(ec.real_register_frame 77 (by decide)).trans b77,
    (ec.real_register_frame 78 (by decide)).trans b78',?_,
    ex.integer_memory_frame (by decide),ex.real_memory_frame (by decide),
    ex.unit_work returnPCPrepareCode_wellFormed (by decide) hh,bO.trans aO,bH⟩
  change b.scalar.core.regs 77-b.scalar.core.regs 78= _
  rw [b77,b78']

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ScalarRegisterMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def RecursiveMachineMemory.realWrite {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {st : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (r : ℕ) (value : ℝ) (hr : r ∉ ([30,31] : List ℕ)) :
    RecursiveMachineMemory g s α ε ell length logical (NearlyOptimalPPR.Computation.realWrite st r value) :=
  pm.frame rfl rfl (by intros; rfl) (by
    intro i hi
    apply Function.update_of_ne
    intro he
    subst i
    exact hr hi) rfl

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

set_option maxHeartbeats 16000000 in
lemma return_pc_guard_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε theta q : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (h77 : st.scalar.core.regs 77=theta) (h78 : st.scalar.core.regs 78=q)
    (h79 : st.scalar.core.regs 79=theta-q) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length
      (changePC logical (if theta=q then .normal else .beginEpisode)) out,
      MachineEval m g ω returnPCGuardCode st steps out ∧ steps ≤ 14 ∧
      memory.queueMass=pm.queueMass ∧ out.work=st.work+steps ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  classical
  by_cases hOuter : theta-q ≤ 0
  · let mid := payUnit (realWrite (payUnit st) 80 (q-theta))
    let mm := (pm.payUnit.realWrite 80 (q-theta) (by simp)).payUnit
    have er : MachineEval m g ω (coreCode (.sub 80 78 77)) (payUnit st) 1 mid := by
      have h77' : (payUnit st).scalar.core.regs 77=theta := h77
      have h78' : (payUnit st).scalar.core.regs 78=q := h78
      simpa only [mid,coreCode,RealOperation.instruction,RealOperation.value,h78',h77'] using binary_eval m g ω (payUnit st) .sub 80 78 77 hh
    have m80 : mid.scalar.core.regs 80=q-theta := by simp [mid,payUnit,pcSet,realWrite]
    by_cases hInner : q-theta ≤ 0
    · have hEq : theta=q := le_antisymm (sub_nonpos.mp hOuter) (sub_nonpos.mp hInner)
      rw [if_pos hEq]
      obtain ⟨out,memory,ec,hMass,hWork,hQuery,hOutput,hHalt⟩ :=
        change_pc_exec m g ω logical s α ε ell length .normal (payUnit mid) hh mm.payUnit hDepth
      have ei : MachineEval m g ω (.branchReal 80 (changePCCode .normal) (changePCCode .beginEpisode)) mid 11 out :=
        MachineEval.realNonpos (st := mid) (r := 80) hh (by rw [m80]; exact hInner) ec
      have ex : MachineEval m g ω returnPCGuardCode st 13 out :=
        MachineEval.realNonpos (st := st) (r := 79) hh (by rw [h79]; exact hOuter) (MachineEval.seq er ei)
      exact ⟨_,out,memory,ex,by omega,hMass,ex.unit_work returnPCGuardCode_wellFormed (by decide) hh,
        hQuery,hOutput,hHalt,header_set_index_frame m g ω logical.top 0 (16*(ell+3))
          (normalizePCNumber .normal : ℤ) (payUnit mid) out 10 hh mm.top ec⟩
    · have hNe : theta ≠ q := by intro he; apply hInner; rw [←he]; simp
      rw [if_neg hNe]
      obtain ⟨out,memory,ec,hMass,hWork,hQuery,hOutput,hHalt⟩ :=
        change_pc_exec m g ω logical s α ε ell length .beginEpisode (payUnit mid) hh mm.payUnit hDepth
      have ei : MachineEval m g ω (.branchReal 80 (changePCCode .normal) (changePCCode .beginEpisode)) mid 12 (payUnit out) :=
        MachineEval.realPos (st := mid) (r := 80) hh (by rw [m80]; exact hInner) ec
      have ex : MachineEval m g ω returnPCGuardCode st 14 (payUnit out) :=
        MachineEval.realNonpos (st := st) (r := 79) hh (by rw [h79]; exact hOuter) (MachineEval.seq er ei)
      exact ⟨_,payUnit out,memory.payUnit,ex,by omega,hMass,ex.unit_work returnPCGuardCode_wellFormed (by decide) hh,
        hQuery,hOutput,hHalt,header_set_index_frame m g ω logical.top 0 (16*(ell+3))
          (normalizePCNumber .beginEpisode : ℤ) (payUnit mid) out 10 hh mm.top ec⟩
  · have hNe : theta ≠ q := by intro he; apply hOuter; rw [he]; simp
    rw [if_neg hNe]
    obtain ⟨out,memory,ec,hMass,hWork,hQuery,hOutput,hHalt⟩ :=
      change_pc_exec m g ω logical s α ε ell length .beginEpisode (payUnit st) hh pm.payUnit hDepth
    have ex : MachineEval m g ω returnPCGuardCode st 12 (payUnit out) :=
      MachineEval.realPos (st := st) (r := 79) hh (by rw [h79]; exact hOuter) ec
    exact ⟨_,payUnit out,memory.payUnit,ex,by omega,hMass,ex.unit_work returnPCGuardCode_wellFormed (by decide) hh,
      hQuery,hOutput,hHalt,header_set_index_frame m g ω logical.top 0 (16*(ell+3))
        (normalizePCNumber .beginEpisode : ℤ) (payUnit st) out 10 hh pm.top ec⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ReturnPCExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma returnPCCode_wellFormed : returnPCCode.wellFormed :=
  ⟨returnPCPrepareCode_wellFormed,returnPCGuardCode_wellFormed⟩

set_option maxHeartbeats 14000000 in
lemma return_pc_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length
      (changePC logical (if (logical.frames logical.top).theta=(logical.frames logical.top).q then .normal else .beginEpisode)) out,
      MachineEval m g ω returnPCCode st steps out ∧ steps ≤ 35 ∧
      memory.queueMass=pm.queueMass ∧ out.work=st.work+steps ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  obtain ⟨a,ea,a77,a78,a79,aI,aR,aW,aO,aH⟩ := return_pc_prepare_exec m g ω logical.top st hh pm.top pm.one
  have aP : ∀ r ∈ ([0,20,50,100] : List ℕ), a.scalar.core.ptrs r=st.scalar.core.ptrs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ea.pointer_frame _ (by decide)
  have aG : ∀ r ∈ ([30,31] : List ℕ), a.scalar.core.regs r=st.scalar.core.regs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ea.real_register_frame _ (by decide)
  let am := pm.frame aI aR aP aG aO
  have aTheta := a77.trans (pm.frames logical.top le_rfl).theta
  have aQ := a78.trans (pm.frames logical.top le_rfl).q
  have aDiff : a.scalar.core.regs 79=(logical.frames logical.top).theta-(logical.frames logical.top).q := by
    rw [a79,(pm.frames logical.top le_rfl).theta,(pm.frames logical.top le_rfl).q]
  obtain ⟨u,out,memory,eb,hu,hMass,hWork,hQuery,hOutput,hHalt,hIndex⟩ :=
    return_pc_guard_exec m g ω logical s α ε (logical.frames logical.top).theta (logical.frames logical.top).q
      ell length a aH am hDepth aTheta aQ aDiff
  have ex : MachineEval m g ω returnPCCode st (21+u) out := MachineEval.seq ea eb
  exact ⟨_,out,memory,ex,by omega,hMass,ex.unit_work returnPCCode_wellFormed (by decide) hh,
    hQuery.trans (ea.query_frame (by decide)),hOutput.trans aO,hHalt,fun v => (hIndex v).trans (congrFun aI _)⟩

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

set_option maxHeartbeats 24000000 in
lemma finish_request_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hDomain : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (compilerFinishRequest g logical) out,
      MachineEval m g ω finishRequestCode st steps out ∧
      steps ≤ (4*(16*(ell+3))+17)*
        ((logical.frames logical.top).active.card+(logical.frames logical.top).cache.card)+140 ∧
      memory.queueMass=pm.queueMass ∧ out.work=st.work+steps ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  classical
  let mu := ∑ v ∈ (logical.frames logical.top).active, (logical.frames logical.top).residual v
  let charged := debit logical logical.top (16*(volumeNat g (logical.frames logical.top).active+1) : ℕ)
  let finished := finishEpisode charged
  let afterNeed := compilerSetNeedFull finished (decide ((logical.frames logical.top).Q/2 ≤ mu))
  obtain ⟨a,am,ea,a70,aMass,aW,aQ,aO,aH⟩ := frame_residual_sum_exec m g ω logical s α ε ell length st hh pm hDomain
  let chargedMemory := am.debit logical.top (16*(volumeNat g (logical.frames logical.top).active+1) : ℕ)
  obtain ⟨b,bm,eb,bMass,bW,bQ,bO,bH⟩ := finish_episode_exec m g ω charged s α ε ell length a aH chargedMemory hDepth hStored hKeys
  have b70 := (eb.real_register_frame 70 (by decide)).trans a70
  have hFinishedQ : (finished.frames finished.top).Q=(logical.frames logical.top).Q := by
    change ((finishEpisode charged).frames charged.top).Q= _
    rw [finish_episode_selected]
    rfl
  have needResult := need_full_decision_exec m g ω finished s α ε mu ell length b bH bm hDepth b70
  rw [hFinishedQ] at needResult
  obtain ⟨u,c,cm,ec,hu,cMass,cW,cQ,cO,cH,cIndex⟩ := needResult
  have hTheta : (afterNeed.frames afterNeed.top).theta=(logical.frames logical.top).theta := by
    change ((compilerSetNeedFull finished _).frames finished.top).theta= _
    rw [set_need_full_selected]
    change ((finishEpisode charged).frames charged.top).theta= _
    rw [finish_episode_selected]
    rfl
  have hRate : (afterNeed.frames afterNeed.top).q=(logical.frames logical.top).q := by
    change ((compilerSetNeedFull finished _).frames finished.top).q= _
    rw [set_need_full_selected]
    change ((finishEpisode charged).frames charged.top).q= _
    rw [finish_episode_selected]
    rfl
  have pcResult := return_pc_exec m g ω afterNeed s α ε ell length c cH cm hDepth
  rw [hTheta,hRate] at pcResult
  obtain ⟨v,out,memory,ed,hv,dMass,dW,dQ,dO,dH,dIndex⟩ := pcResult
  have ex : MachineEval m g ω finishRequestCode st
      (((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+20)+
        (((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+60)+(u+v))) out :=
    MachineEval.seq ea (MachineEval.seq eb (MachineEval.seq ec ed))
  have bIndex := finish_episode_index_frame m g ω charged s α ε ell length a b _ aH chargedMemory hDepth eb
  have aI := ea.integer_memory_frame (by decide)
  refine ⟨_,out,memory,ex,?_,dMass.trans (cMass.trans (bMass.trans aMass)),
    ex.unit_work finishRequestCode_wellFormed (by decide) hh,dQ.trans (cQ.trans (bQ.trans aQ)),
    dO.trans (cO.trans (bO.trans aO)),dH,fun z => (dIndex z).trans ((cIndex z).trans ((bIndex z).trans (congrFun aI _)))⟩
  let F := 4*(16*(ell+3))+17
  change (F*(logical.frames logical.top).active.card+20)+
    ((F*(logical.frames logical.top).cache.card+60)+(u+v)) ≤
      F*((logical.frames logical.top).active.card+(logical.frames logical.top).cache.card)+140
  rw [Nat.mul_add]
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.InterruptEpisodeExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma interruptEpisodeCode_wellFormed (pc : NormalizePC) : (interruptEpisodeCode pc).wellFormed :=
  ⟨finishEpisodeCode_wellFormed,changePCCode_wellFormed pc⟩

set_option maxHeartbeats 18000000 in
lemma interrupt_episode_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ) (pc : NormalizePC)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length
      (changePC (finishEpisode (debit logical logical.top 1)) pc) out,
      MachineEval m g ω (interruptEpisodeCode pc) st
        ((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+70) out ∧
      memory.queueMass=pm.queueMass ∧
      out.work=st.work+((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+70 : ℕ) ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  let charged := debit logical logical.top 1
  let cm := pm.debit logical.top 1
  obtain ⟨a,am,ea,aMass,aW,aQ,aO,aH⟩ := finish_episode_exec m g ω charged s α ε ell length st hh cm hDepth hStored hKeys
  obtain ⟨out,memory,eb,bMass,bW,bQ,bO,bH⟩ := change_pc_exec m g ω (finishEpisode charged) s α ε ell length pc a aH am hDepth
  have ex : MachineEval m g ω (interruptEpisodeCode pc) st
      ((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+70) out := by
    convert MachineEval.seq ea eb using 1 <;> (first | rfl | omega)
  have aIndex := finish_episode_index_frame m g ω charged s α ε ell length st a _ hh cm hDepth ea
  have bIndex := header_set_index_frame m g ω (finishEpisode charged).top 0 (16*(ell+3))
    (normalizePCNumber pc : ℤ) a out 10 aH am.top eb
  exact ⟨out,memory,ex,bMass.trans aMass,
    ex.unit_work (interruptEpisodeCode_wellFormed pc) (by cases pc <;> decide) hh,
    bQ.trans aQ,bO.trans aO,bH,fun v => (bIndex v).trans (aIndex v)⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RestartRequestExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma restartRequestCode_wellFormed : restartRequestCode.wellFormed :=
  ⟨setNeedFullCode_wellFormed _,changePCCode_wellFormed _⟩

set_option maxHeartbeats 7000000 in
lemma restart_request_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length (compilerRestartRequest logical) out,
      MachineEval m g ω restartRequestCode st 20 out ∧ memory.queueMass=pm.queueMass ∧
      out.work=st.work+20 ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  let charged := debit logical logical.top 1
  let cm := pm.debit logical.top 1
  obtain ⟨a,am,ea,aMass,aW,aQ,aO,aH,aIndex⟩ := set_need_full_exec m g ω charged s α ε ell length true st hh cm hDepth
  obtain ⟨out,memory,eb,bMass,bW,bQ,bO,bH⟩ := change_pc_exec m g ω (compilerSetNeedFull charged true) s α ε ell length .beginEpisode a aH am hDepth
  have bIndex := header_set_index_frame m g ω (compilerSetNeedFull charged true).top 0 (16*(ell+3))
    (normalizePCNumber .beginEpisode : ℤ) a out 10 aH am.top eb
  have ex : MachineEval m g ω restartRequestCode st 20 out := MachineEval.seq ea eb
  exact ⟨out,memory,ex,bMass.trans aMass,ex.unit_work restartRequestCode_wellFormed (by decide) hh,
    bQ.trans aQ,bO.trans aO,bH,fun v => (bIndex v).trans (aIndex v)⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorPushBound

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma exteriorPushBound_le (ell top rank degree : ℕ) :
    exteriorPushBound ell top rank degree ≤
      (top+1)*(degree+1)*(42*rank+168*(16*(ell+3))+910) := by
  let w := 16*(ell+3)
  have hD : degree ≤ degree+1 := by omega
  have hL : 1 ≤ top+1 := by omega
  have hConst : 84*w+452 ≤ (degree+1)*(84*w+452) := by
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hLevel : (top+1)*(4*w+60) ≤ (degree+1)*((top+1)*(4*w+60)) := by
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hDeg : degree*((top+1)*(8*w+39)+8*w+50) ≤
      (degree+1)*((top+1)*(8*w+39)+8*w+50) := Nat.mul_le_mul_right _ hD
  have hLift : (degree+1)*(96*w+527) ≤ (top+1)*((degree+1)*(96*w+527)) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hFirst : exteriorPushBound ell top rank degree ≤
      (degree+1)*((top+1)*(42*rank+72*w+383)+96*w+527) := by
    unfold exteriorPushBound
    change 84*w+452+(top+1)*(4*w+60)+degree*((top+1)*(8*w+39)+8*w+50)+
      (degree+1)*((top+1)*(42*rank+60*w+284)+4*w+25) ≤ _
    calc
      _ ≤ (degree+1)*(84*w+452)+(degree+1)*((top+1)*(4*w+60))+
          (degree+1)*((top+1)*(8*w+39)+8*w+50)+
          (degree+1)*((top+1)*(42*rank+60*w+284)+4*w+25) := by omega
      _ = _ := by ring
  calc
    _ ≤ (degree+1)*((top+1)*(42*rank+72*w+383)+96*w+527) := hFirst
    _ ≤ (top+1)*(degree+1)*(42*rank+168*w+910) := by
      have hEq : (degree+1)*((top+1)*(42*rank+72*w+383)+96*w+527)=
          (top+1)*(degree+1)*(42*rank+72*w+383)+(degree+1)*(96*w+527) := by ring
      rw [hEq]
      calc
        _ ≤ (top+1)*(degree+1)*(42*rank+72*w+383)+(top+1)*((degree+1)*(96*w+527)) := by omega
        _ = _ := by ring


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

set_option maxHeartbeats 22000000 in
lemma drain_decision_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank boundary : ℕ) (pc : NormalizePC)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hKeys : KeysInvariant g logical)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hCacheDomain : ∀ i ≤ logical.top, (logical.frames i).cache ⊆ parentDomain logical i)
    (hBoundary : logical.boundaryEdges=(boundary : ℤ))
    (hNextBoundary : ∀ t v, pendingPush logical=some (t,v) → 0 ≤ (exteriorPush g α logical t v).boundaryEdges)
    (hNextKeys : ∀ t v, pendingPush logical=some (t,v) → KeysInvariant g (exteriorPush g α logical t v))
    (hMass : pm.queueMass+2*(logical.top+1)*(drainDegree g logical+1) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    let T := (logical.top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
    let D := drainDegree g logical+1
    let E := (logical.top+1)*D*(42*rank+168*(16*(ell+3))+910)
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (compilerDrain g α logical pc) out,
      MachineEval m g ω (drainDecisionCode pc) st steps out ∧
      steps+P*memory.queueMass ≤ P*pm.queueMass+(T+E+P*(2*(logical.top+1)*D)+12) ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*D ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  dsimp only
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let T := (logical.top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
  let D := drainDegree g logical+1
  let E := (logical.top+1)*D*(42*rank+168*(16*(ell+3))+910)
  obtain ⟨u,a,am,ea,aSpec,aMass,aAmort,aQ,aW,aO,aH,aIndex⟩ := priority_exec m g ω logical s α ε ell length N rank st hh pm hDepth (by omega) hCap hPow
  have aAmort' : u+P*am.queueMass ≤ P*pm.queueMass+T := by simpa only [P,T,Nat.add_assoc] using aAmort
  cases hp : pendingPush logical with
  | none =>
    rw [compilerDrain,hp]
    have aSpec' : a.scalar.core.ptrs 97=0 ∧ a.scalar.core.ptrs 112=(-1) := by simpa only [PendingSelectionSpec,hp] using aSpec
    have aFlag : a.scalar.core.ptrs 97=0 := aSpec'.1
    obtain ⟨out,memory,eb,bMass,bW,bQ,bO,bH,bIndex⟩ := cheap_pc_index_exec m g ω logical s α ε ell length pc (payUnit a) aH am.payUnit hDepth
    have eBranch : MachineEval m g ω (.branchPointer 97 0 (changePCCode pc) exteriorPushProgramCode) a 11 out :=
      MachineEval.pointerLe aH (by rw [aFlag,am.zero]) eb
    have ex : MachineEval m g ω (drainDecisionCode pc) st (u+11) out := MachineEval.seq ea eBranch
    refine ⟨u+11,out,memory,ex,?_,?_,ex.unit_work (drainDecisionCode_wellFormed pc) (by cases pc <;> decide) hh,
      bO.trans aO,bH,fun v => (bIndex v).trans (aIndex v)⟩
    · change memory.queueMass=am.queueMass at bMass
      change u+11+P*memory.queueMass ≤ P*pm.queueMass+(T+E+P*(2*(logical.top+1)*D)+12)
      rw [bMass]
      omega
    · change memory.queueMass=am.queueMass at bMass
      rw [bMass]
      omega
  | some pair =>
    obtain ⟨t,v⟩ := pair
    rw [compilerDrain,hp]
    have spec : a.scalar.core.ptrs 97=1 ∧ a.scalar.core.ptrs 112=(t : ℤ) ∧ a.scalar.core.ptrs 40=(v.val : ℤ) := by
      simpa only [PendingSelectionSpec,hp] using aSpec
    have hMember := pending_push_member logical t v hp
    have hEligible := ((hKeys t hMember.1).1 v).mp hMember.2
    have hD : D=(g.neighbors v).length+1 := by simp [D,drainDegree,hp]
    obtain ⟨w,b,bm,eb,hSteps,bMass,b40,bW,bO,bH,bIndex⟩ := exterior_push_exec m g ω logical s α ε ell length N rank t boundary v
      (payUnit a) aH am.payUnit hDepth hMember.1 hEligible.1 hEligible.2.1 hSubset hCacheDomain spec.2.1 spec.2.2
      hBoundary (hNextBoundary t v hp) (hNextKeys t v hp) (by
        change am.queueMass+2*(logical.top+1)*((g.neighbors v).length+1) ≤ N
        rw [←hD]
        change pm.queueMass+2*(logical.top+1)*D ≤ N at hMass
        omega) hCap hPow
    have eBranch : MachineEval m g ω (.branchPointer 97 0 (changePCCode pc) exteriorPushProgramCode) a (1+w+1) (payUnit b) :=
      MachineEval.pointerGt aH (by rw [spec.1,am.zero]; norm_num) eb
    have ex : MachineEval m g ω (drainDecisionCode pc) st (u+(1+w+1)) (payUnit b) := MachineEval.seq ea eBranch
    have hStepBound : w ≤ E := by
      apply hSteps.trans
      dsimp only [E]
      rw [hD]
      exact exteriorPushBound_le ell logical.top rank (g.neighbors v).length
    have hM : bm.queueMass ≤ am.queueMass+2*(logical.top+1)*D := by
      change bm.queueMass ≤ am.queueMass+2*(logical.top+1)*((g.neighbors v).length+1) at bMass
      simpa only [hD] using bMass
    have hMul := Nat.mul_le_mul_left P hM
    rw [Nat.mul_add] at hMul
    refine ⟨u+(1+w+1),payUnit b,bm.payUnit,ex,?_,?_,ex.unit_work (drainDecisionCode_wellFormed pc) (by cases pc <;> decide) hh,
      bO.trans aO,bH,fun z => (bIndex z).trans (aIndex z)⟩
    · change u+(1+w+1)+P*bm.queueMass ≤ P*pm.queueMass+(T+E+P*(2*(logical.top+1)*D)+12)
      omega
    · change bm.queueMass ≤ pm.queueMass+2*(logical.top+1)*D
      omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveMachineReturnFrame

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section


def RecursiveMachineMemory.return_frame {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical next : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hTop : next.top ≤ logical.top) (hStored : next.stored=logical.stored) (hX : next.x=logical.x)
    (hBoundary : next.boundaryEdges=logical.boundaryEdges)
    (hFrames : ∀ j ≤ next.top, next.frames j=logical.frames j)
    (hDomains : ∀ j ≤ next.top, parentDomain next j=parentDomain logical j)
    (hI : out.scalar.integerMemory=st.scalar.integerMemory) (hR : out.scalar.core.mem=st.scalar.core.mem)
    (hP : ∀ r ∈ ([0,20,50] : List ℕ), out.scalar.core.ptrs r=st.scalar.core.ptrs r)
    (hTopPointer : out.scalar.core.ptrs 100=(next.top : ℤ))
    (hG : ∀ r ∈ ([30,31] : List ℕ), out.scalar.core.regs r=st.scalar.core.regs r)
    (hO : out.output=st.output) : RecursiveMachineMemory g s α ε ell length next out := by
  have hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 := le_of_eq (hP 20 (by simp)).symm
  have hDegree : recursiveDegreeDomain g s next=recursiveDegreeDomain g s logical := by
    unfold recursiveDegreeDomain
    rw [hStored]
  let frames := fun j hj => ((pm.frames j (hj.trans hTop)).logical_frame (hFrames j hj) (hDomains j hj)).memory_frame
    hFree (fun slot hs => congrFun hI _) (fun slot hs => congrFun hR _)
    (fun v hv field hf => congrFun hI _) (fun v hv field hf => congrFun hR _) (fun z hz => congrFun hI _)
  refine {
    zero := (hP 0 (by simp)).trans pm.zero
    top := hTopPointer
    width := (hP 50 (by simp)).trans pm.width
    alphaRegister := (hG 30 (by simp)).trans pm.alphaRegister
    one := (hG 31 (by simp)).trans pm.one
    alphaMemory := by rw [hR]; exact pm.alphaMemory
    epsilonMemory := by rw [hR]; exact pm.epsilonMemory
    depthMemory := by rw [hI]; exact pm.depthMemory
    lengthMemory := by rw [hI]; exact pm.lengthMemory
    seedMemory := by rw [hI]; exact pm.seedMemory
    allocator := by rw [hP 20 (by simp)]; exact pm.allocator
    potential := by rw [hR,hX]; exact pm.potential
    seedMarker := by rw [hR]; exact pm.seedMarker
    boundary := by rw [hI,hBoundary]; exact pm.boundary
    graphCache := by rw [hI,hStored,hP 20 (by simp)]; exact pm.graphCache
    rowAbove := by rw [hI,hStored]; exact pm.rowAbove
    knownDegree := by rw [hI,hDegree]; exact pm.knownDegree
    unknownDegree := by rw [hI,hDegree]; exact pm.unknownDegree
    frames := frames
    pieceSeparation := fun j hj => pm.pieceSeparation j (hj.trans hTop)
    frameSeparation := fun i hi j hj hij => pm.frameSeparation i (hi.trans hTop) j (hj.trans hTop) hij
    cacheSeparation := ?_
    output := hO.trans pm.output
  }
  intro j hj
  change Disjoint (pm.frames j (hj.trans hTop)).owned (cachedRowCells g out.scalar.integerMemory (16*(ell+3)) next.stored)
  rw [hI,hStored]
  exact pm.cacheSeparation j (hj.trans hTop)

lemma queue_mass_return {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical next : RecursiveState n} {st out : MachineState}
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (memory : RecursiveMachineMemory g s α ε ell length next out) (hTop : next.top ≤ logical.top)
    (hMasses : ∀ j, ∀ hj : j ≤ next.top, (memory.frames j hj).queueMass=(pm.frames j (hj.trans hTop)).queueMass) :
    memory.queueMass ≤ pm.queueMass := by
  unfold RecursiveMachineMemory.queueMass
  calc
    (∑ j ∈ Finset.range (next.top+1), if hj : j ≤ next.top then (memory.frames j hj).queueMass else 0)=
        ∑ j ∈ Finset.range (next.top+1), if hj : j ≤ logical.top then (pm.frames j hj).queueMass else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hNew : j ≤ next.top := by have := Finset.mem_range.mp hj; omega
      simp only [dif_pos hNew,dif_pos (hNew.trans hTop)]
      exact hMasses j hNew
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hTop)) (by intros; omega)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ChildReturnExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma child_end_call_top {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) (hNonzero : logical.top ≠ 0) :
    (endCall g α logical).top=logical.top-1 := by simp [endCall,hNonzero]

set_option maxHeartbeats 8000000 in
lemma child_return_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hNonzero : logical.top ≠ 0) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length (endCall g α logical) out,
      MachineEval m g ω (coreCode (.pdec 100)) st 1 out ∧ memory.queueMass ≤ pm.queueMass ∧
      out.work=st.work+1 ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  let out := payUnit (pointerWrite st 100 ((logical.top : ℤ)-1))
  have ex : MachineEval m g ω (coreCode (.pdec 100)) st 1 out := by
    simpa only [coreCode,pm.top,out] using pdec_eval m g ω st 100 hh
  have hTopLe : (endCall g α logical).top ≤ logical.top := by rw [child_end_call_top g α logical hNonzero]; omega
  have hFrames : ∀ j ≤ (endCall g α logical).top, (endCall g α logical).frames j=logical.frames j := by
    intros
    simp [endCall,hNonzero]
  have hDomains : ∀ j ≤ (endCall g α logical).top, parentDomain (endCall g α logical) j=parentDomain logical j := by
    intros
    simp [endCall,hNonzero,parentDomain]
  have hTopP : out.scalar.core.ptrs 100=((endCall g α logical).top : ℤ) := by
    simp only [out,payUnit,pcSet,pointerWrite,Function.update_self,child_end_call_top g α logical hNonzero]
    rw [Nat.cast_sub (by omega : 1 ≤ logical.top)]
    rfl
  let memory := pm.return_frame (out := out) hTopLe
    (by simp [endCall,hNonzero]) (by simp [endCall,hNonzero]) (by simp [endCall,hNonzero]) hFrames hDomains rfl rfl
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl <;> exact ex.pointer_frame _ (by decide)) hTopP
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl <;> exact ex.real_register_frame _ (by decide)) rfl
  refine ⟨out,memory,ex,?_,rfl,rfl,rfl,hh⟩
  exact queue_mass_return pm memory hTopLe (by intros; rfl)

set_option maxHeartbeats 8000000 in
lemma cheap_child_return_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hNonzero : logical.top ≠ 0) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length (endCall g α (debit logical logical.top 1)) out,
      MachineEval m g ω (coreCode (.pdec 100)) st 1 out ∧ memory.queueMass ≤ pm.queueMass ∧
      out.work=st.work+1 ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by
  exact child_return_exec m g ω (debit logical logical.top 1) s α ε ell length st hh (pm.debit logical.top 1) hNonzero

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

-- Proof module: Solutions.RecursiveControllerCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma stopControllerCode_wellFormed : stopControllerCode.wellFormed := by
  simp [stopControllerCode,coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]

lemma controllerRootReturnCode_wellFormed : controllerRootReturnCode.wellFormed :=
  ⟨rootSparseOutputCode_wellFormed,stopControllerCode_wellFormed⟩
lemma controllerReturnCode_wellFormed : controllerReturnCode.wellFormed := by
  refine ⟨controllerRootReturnCode_wellFormed,?_⟩
  simp [coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
lemma controllerDepthCode_wellFormed : controllerDepthCode.wellFormed := by
  simp [controllerDepthCode,controllerDepthRoutine,PointerRoutine.sequence,PointerRoutine.code,PointerOp.instruction,
    coreCode,MachineCode.wellFormed,straightInstruction,admissible,scalarProgram,LocalPush.Admissible]
end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerCheapPCExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 9000000 in
lemma controller_cheap_pc_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P : ℕ) (pc : NormalizePC)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) :
    ∃ out, ∃ next : ControllerMemory g s α ε ell length (changePC (debit logical logical.top 1) pc) out,
      MachineEval m g ω (changePCCode pc) st 10 out ∧ next.mass=memory.mass ∧
      out.work+((P*next.mass : ℕ) : ℝ≥0∞)=st.work+((P*memory.mass : ℕ) : ℝ≥0∞)+10 := by
  let pm := memory.live hDone
  obtain ⟨out,om,ex,hMass,hW,hQ,hO,hH,hMarks⟩ := cheap_pc_index_exec m g ω logical s α ε ell length pc st memory.halted pm hDepth
  have hNextDone : (changePC (debit logical logical.top 1) pc).done=false := hDone
  have h150 : out.scalar.core.ptrs 150=0 := by
    rw [ex.pointer_frame 150 (by cases pc <;> decide),memory.doneFlag,hDone]
    rfl
  have h151 : out.scalar.core.ptrs 151=1 := (ex.pointer_frame 151 (by cases pc <;> decide)).trans memory.one
  have hE : EpochInvariant (n:=n) (16*(ell+3)) out := by
    intro v
    rw [hMarks v,ex.pointer_frame 53 (by cases pc <;> decide)]
    exact memory.epoch hDone v
  let next := ControllerMemory.ofLive om hNextDone h150 h151 hH hE
  have hNewMass : next.mass=memory.mass := by
    rw [ControllerMemory.ofLive_mass,hMass,memory.mass_live hDone]
  exact ⟨out,next,ex,hNewMass,by rw [hW,hNewMass]; ring⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerFullExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 20000000 in
lemma controller_full_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank P : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hFlags : ControllerBudgetFlags logical st) (hα : 0<α ∧ α<1)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames logical.top).active, 0<g.graph.degree v)
    (hRegion : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (hKeys : KeysInvariant g logical)
    (hMass : (memory.live hDone).queueMass+2*(logical.top+1)*
      (volumeNat g (logical.frames logical.top).active+(logical.frames logical.top).active.card) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let C := (logical.frames logical.top).active
    let size := volumeNat g C+C.card
    let A := (10*C.card+5)+((24*(16*(ell+3))+100)*size+28)+(jointSolveIterationFactor ell logical.top rank*size+5)+42
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerFullDecision m g α logical) out,
      MachineEval m g ω controllerFullCode st steps out ∧
      next.mass ≤ memory.mass+2*(logical.top+1)*size ∧
      out.work+((P*next.mass : ℕ) : ℝ≥0∞) ≤ st.work+((P*memory.mass : ℕ) : ℝ≥0∞)+
        ((A+P*(2*(logical.top+1)*size)+12 : ℕ) : ℝ≥0∞)+solveCharge m C.card size := by
  dsimp only
  let pm := memory.live hDone
  let C := (logical.frames logical.top).active
  let size := volumeNat g C+C.card
  let A := (10*C.card+5)+((24*(16*(ell+3))+100)*size+28)+(jointSolveIterationFactor ell logical.top rank*size+5)+42
  have oldMass : memory.mass=pm.queueMass := memory.mass_live hDone
  by_cases hAny : anyExhausted logical
  · rw [compilerFullDecision,if_pos hAny]
    obtain ⟨out,next,eb,nMass,hWork⟩ := controller_cheap_pc_exec m g ω logical s α ε ell length P .afterChild
      (payUnit st) memory.payUnit hDone hDepth
    have ex : MachineEval m g ω controllerFullCode st 12 (payUnit out) :=
      MachineEval.pointerGt memory.halted (by rw [hFlags.1,if_pos hAny,pm.zero]; norm_num) eb
    have hNewMass : next.payUnit.mass=memory.mass := by rw [ControllerMemory.payUnit_mass,nMass,ControllerMemory.payUnit_mass]
    refine ⟨12,payUnit out,next.payUnit,ex,by rw [hNewMass]; omega,?_⟩
    have hEq : (payUnit out).work+((P*next.payUnit.mass : ℕ) : ℝ≥0∞)=st.work+((P*memory.mass : ℕ) : ℝ≥0∞)+12 := by
      rw [ControllerMemory.payUnit_mass,payUnit_work]
      calc
        _ = (out.work+((P*next.mass : ℕ) : ℝ≥0∞))+1 := by ac_rfl
        _ = ((payUnit st).work+((P*memory.payUnit.mass : ℕ) : ℝ≥0∞)+10)+1 := by rw [hWork]
        _ = _ := by rw [payUnit_work,ControllerMemory.payUnit_mass]; ring
    rw [hEq]
    have hNat : (12 : ℕ) ≤ A+P*(2*(logical.top+1)*size)+12 := by omega
    have hCast : (12 : ℝ≥0∞) ≤ ((A+P*(2*(logical.top+1)*size)+12 : ℕ) : ℝ≥0∞) := by exact_mod_cast hNat
    exact (add_le_add le_rfl hCast).trans (le_add_of_nonneg_right (by positivity))
  · rw [compilerFullDecision,if_neg hAny]
    obtain ⟨u,out,om,eb,hu,oMass,oW,oO,oH,oEpoch⟩ := full_solve_decision_exec m g ω logical s α ε ell length N rank
      (payUnit st) memory.halted pm.payUnit hDepth hα hStored hDegree (hRegion logical.top le_rfl)
      (memory.epoch hDone) hKeys hRegion hMass hCap hPow
    have ex : MachineEval m g ω controllerFullCode st (1+u) out :=
      MachineEval.pointerLe memory.halted (by rw [hFlags.1,if_neg hAny,pm.zero]) eb
    have hNDone : (compilerFullSolve m g α logical).done=false := hDone
    have h150 : out.scalar.core.ptrs 150=0 := by
      rw [eb.pointer_frame 150 (by decide)]
      change st.scalar.core.ptrs 150=0
      rw [memory.doneFlag,hDone]
      rfl
    have h151 : out.scalar.core.ptrs 151=1 := (eb.pointer_frame 151 (by decide)).trans memory.one
    let next := ControllerMemory.ofLive om hNDone h150 h151 oH oEpoch
    have nMass : next.mass=om.queueMass := ControllerMemory.ofLive_mass _ _ _ _ _ _
    refine ⟨1+u,out,next,ex,?_,?_⟩
    · rw [nMass,oldMass]
      exact oMass
    · change out.work ≤ (payUnit st).work+(A : ℕ)+solveCharge m C.card size at oW
      have hM : next.mass ≤ memory.mass+2*(logical.top+1)*size := by rw [nMass,oldMass]; exact oMass
      have h := solve_amortized_work st.work (payUnit st).work out.work (solveCharge m C.card size)
        1 A P memory.mass memory.mass next.mass 1 (2*(logical.top+1)*size)
        (by simp [payUnit_work]) (by omega) oW hM
      exact h.trans (by
        apply add_le_add
        · change st.work+((P*memory.mass+1+A+P*(2*(logical.top+1)*size) : ℕ) : ℝ≥0∞) ≤
            st.work+((P*memory.mass : ℕ) : ℝ≥0∞)+((A+P*(2*(logical.top+1)*size)+12 : ℕ) : ℝ≥0∞)
          have hNat : P*memory.mass+1+A+P*(2*(logical.top+1)*size) ≤ P*memory.mass+(A+P*(2*(logical.top+1)*size)+12) := by omega
          have hCast : ((P*memory.mass+1+A+P*(2*(logical.top+1)*size) : ℕ) : ℝ≥0∞) ≤ ((P*memory.mass+(A+P*(2*(logical.top+1)*size)+12) : ℕ) : ℝ≥0∞) := by exact_mod_cast hNat
          simpa only [Nat.cast_add,add_assoc] using add_le_add (le_refl st.work) hCast
        · rfl)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveCacheControl

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma recursive_cache_mass_full_decision {n : ℕ} (m : SolveModel) (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) :
    recursiveCacheMass (compilerFullDecision m g α logical)=recursiveCacheMass logical := by
  unfold compilerFullDecision
  split
  · rw [recursive_cache_mass_pc,recursive_cache_mass_debit]
  · exact recursive_cache_mass_full m g α logical

lemma recursive_cache_mass_restart {n : ℕ} (logical : RecursiveState n) :
    recursiveCacheMass (compilerRestartRequest logical)=recursiveCacheMass logical := by
  unfold compilerRestartRequest
  rw [recursive_cache_mass_pc,recursive_cache_mass_need_full,recursive_cache_mass_debit]

lemma recursive_cache_mass_initial_empty {n : ℕ} (logical : RecursiveState n) :
    recursiveCacheMass (compilerInitialEmpty logical)=recursiveCacheMass logical := by
  unfold compilerInitialEmpty
  rw [recursive_cache_mass_pc,recursive_cache_mass_debit]

lemma recursive_cache_mass_end_call {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) :
    recursiveCacheMass (endCall g α logical) ≤ recursiveCacheMass logical := by
  unfold endCall
  dsimp only
  split
  · rfl
  · unfold recursiveCacheMass
    dsimp only
    have hTop : logical.top-1+1=logical.top := by omega
    rw [hTop]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (by intros; positivity)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveCacheLocal

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma recursive_cache_mass_exterior {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) (t : ℕ) (v : Fin n) :
    recursiveCacheMass (exteriorPush g α logical t v)=recursiveCacheMass logical := by
  apply recursive_cache_mass_frame logical (exteriorPush g α logical t v) (compiler_exterior_top g α logical t v)
  intro i hi
  exact congrArg (fun x => x.2.2.2.2.2.2.2.2.2) (compiler_exterior_static g α logical t v i)

lemma recursive_cache_mass_drain {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) (pc : NormalizePC) :
    recursiveCacheMass (compilerDrain g α logical pc)=recursiveCacheMass logical := by
  unfold compilerDrain
  split
  · rw [recursive_cache_mass_pc,recursive_cache_mass_debit]
  · exact recursive_cache_mass_exterior g α logical _ _

lemma recursive_cache_mass_child {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n) :
    recursiveCacheMass (spawnChildState g ell logical)=recursiveCacheMass logical := by
  unfold recursiveCacheMass
  rw [spawnChild_top,Finset.sum_range_succ,spawnChild_child]
  simp only [freshFrame,Finset.card_empty,Nat.add_zero,emptyFrame]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ logical.top := by have := Finset.mem_range.mp hi; omega
  by_cases he : i=logical.top
  · subst i
    rw [spawnChild_parent]
  · rw [spawnChild_other g ell logical i he (by omega)]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerExteriorExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 18000000 in
lemma controller_exterior_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank P Q t : ℕ) (v : Fin n)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hKeys : KeysInvariant g logical) (hRegion : RegionInvariant logical) (hBoundary : BoundaryIdentity g logical)
    (hPending : pendingPush logical=some (t,v)) (hSelected : PendingSelectionSpec logical st)
    (hMass : (memory.live hDone).queueMass+2*(logical.top+1)*((g.neighbors v).length+1) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let D := 2*(logical.top+1)*((g.neighbors v).length+1)
    let A := (logical.top+1)*((g.neighbors v).length+1)*(42*rank+168*(16*(ell+3))+910)
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (exteriorPush g α logical t v) out,
      MachineEval m g ω exteriorPushProgramCode st steps out ∧ next.mass ≤ memory.mass+D ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+((A+P*D : ℕ) : ℝ≥0∞) := by
  dsimp only
  obtain ⟨boundary,hB⟩ := compiler_boundary_nat g logical hBoundary
  have hMember := pending_push_member logical t v hPending
  have hEligible := ((hKeys t hMember.1).1 v).mp hMember.2
  have hSpec : st.scalar.core.ptrs 97=1 ∧ st.scalar.core.ptrs 112=(t : ℤ) ∧ st.scalar.core.ptrs 40=(v.val : ℤ) := by
    simpa only [PendingSelectionSpec,hPending] using hSelected
  obtain ⟨u,out,om,ex,hu,oMass,o40,oW,oO,oH,oMarks⟩ := exterior_push_exec m g ω logical s α ε ell length N rank t boundary v st memory.halted
    (memory.live hDone) hDepth hMember.1 hEligible.1 hEligible.2.1
    (fun i hi => (hRegion i hi).1) (fun i hi => (hRegion i hi).2.2.2.trans (hRegion i hi).1)
    hSpec.2.1 hSpec.2.2 hB (compiler_pending_boundary_nonnegative g α logical hRegion hBoundary t v hPending)
    (compiler_exterior_keys g α logical t v hKeys) hMass hCap hPow
  have hTarget : (exteriorPush g α logical t v).done=false := by
    rw [compiler_exterior_stages]
    change RecursiveState.done ((if _ then _ else _) : RecursiveState n)=false
    split_ifs
    · unfold admitStage
      split_ifs <;> exact hDone
    · exact hDone
  have hSteps := hu.trans (exteriorPushBound_le ell logical.top rank (g.neighbors v).length)
  obtain ⟨next,nMass,nWork⟩ := controller_lift_unit_run (P:=P) memory hDone om hTarget ex (by decide) (by decide) (by decide) oH oMarks oW hSteps oMass
  refine ⟨u,out,next,ex,nMass,?_⟩
  exact controller_cache_work memory next hDone hTarget _ (le_of_eq (recursive_cache_mass_exterior g α logical t v)) nWork

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerEpisodeCoreExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 10000000 in
lemma controller_finish_core_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hDomain : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical) :
    let A := (4*(16*(ell+3))+17)*((logical.frames logical.top).active.card+(logical.frames logical.top).cache.card)+140
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerFinishRequest g logical) out,
      MachineEval m g ω finishRequestCode st steps out ∧ next.mass ≤ memory.mass ∧
      out.work+((P*next.mass : ℕ) : ℝ≥0∞) ≤ st.work+((P*memory.mass : ℕ) : ℝ≥0∞)+(A : ℕ) := by
  dsimp only
  obtain ⟨u,out,pm,ex,hu,hMass,hWork,hQ,hO,hH,hMarks⟩ := finish_request_exec m g ω logical s α ε ell length st memory.halted (memory.live hDone) hDepth hDomain hStored hKeys
  obtain ⟨next,nMass,nWork⟩ := controller_lift_unit_run (P:=P) (D:=0) memory hDone pm hDone ex (by decide) (by decide) (by decide) hH hMarks hWork hu (by rw [hMass]; omega)
  exact ⟨u,out,next,ex,by simpa using nMass,by simpa using nWork⟩

set_option maxHeartbeats 10000000 in
lemma controller_restart_core_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) :
    ∃ out, ∃ next : ControllerMemory g s α ε ell length (compilerRestartRequest logical) out,
      MachineEval m g ω restartRequestCode st 20 out ∧ next.mass ≤ memory.mass ∧
      out.work+((P*next.mass : ℕ) : ℝ≥0∞) ≤ st.work+((P*memory.mass : ℕ) : ℝ≥0∞)+20 := by
  obtain ⟨out,pm,ex,hMass,hWork,hQ,hO,hH,hMarks⟩ := restart_request_exec m g ω logical s α ε ell length st memory.halted (memory.live hDone) hDepth
  obtain ⟨next,nMass,nWork⟩ := controller_lift_unit_run (P:=P) (A:=20) (D:=0) memory hDone pm hDone ex (by decide) (by decide) (by decide) hH hMarks hWork le_rfl (by rw [hMass]; omega)
  exact ⟨out,next,ex,by simpa using nMass,by simpa using nWork⟩

set_option maxHeartbeats 10000000 in
lemma controller_interrupt_core_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P : ℕ) (pc : NormalizePC)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical) :
    let A := (4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+70
    ∃ out, ∃ next : ControllerMemory g s α ε ell length (changePC (finishEpisode (debit logical logical.top 1)) pc) out,
      MachineEval m g ω (interruptEpisodeCode pc) st A out ∧ next.mass ≤ memory.mass ∧
      out.work+((P*next.mass : ℕ) : ℝ≥0∞) ≤ st.work+((P*memory.mass : ℕ) : ℝ≥0∞)+(A : ℕ) := by
  dsimp only
  obtain ⟨out,pm,ex,hMass,hWork,hQ,hO,hH,hMarks⟩ := interrupt_episode_exec m g ω logical s α ε ell length pc st memory.halted (memory.live hDone) hDepth hStored hKeys
  obtain ⟨next,nMass,nWork⟩ := controller_lift_unit_run (P:=P) (D:=0) memory hDone pm hDone ex (by cases pc <;> decide) (by cases pc <;> decide) (by cases pc <;> decide) hH hMarks hWork le_rfl (by rw [hMass]; omega)
  exact ⟨out,next,ex,by simpa using nMass,by simpa using nWork⟩

set_option maxHeartbeats 10000000 in
lemma controller_initial_empty_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) :
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerInitialEmpty logical) out,
      MachineEval m g ω initialEmptyCode st steps out ∧ next.mass ≤ memory.mass ∧
      out.work+((P*next.mass : ℕ) : ℝ≥0∞) ≤ st.work+((P*memory.mass : ℕ) : ℝ≥0∞)+22 := by
  obtain ⟨u,out,pm,ex,hu,hMass,hWork,hQ,hO,hH,hMarks⟩ := initial_empty_exec m g ω logical s α ε ell length st memory.halted (memory.live hDone) hDepth
  obtain ⟨next,nMass,nWork⟩ := controller_lift_unit_run (P:=P) (A:=22) (D:=0) memory hDone pm hDone ex (by decide) (by decide) (by decide) hH hMarks hWork hu (by rw [hMass]; omega)
  exact ⟨u,out,next,ex,by simpa using nMass,by simpa using nWork⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerSimplePotential

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma controller_cheap_potential_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P Q : ℕ) (pc : NormalizePC)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) :
    ∃ out, ∃ next : ControllerMemory g s α ε ell length (changePC (debit logical logical.top 1) pc) out,
      MachineEval m g ω (changePCCode pc) st 10 out ∧ next.mass ≤ memory.mass ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+10 := by
  obtain ⟨out,next,ex,hMass,hWork⟩ := controller_cheap_pc_exec m g ω logical s α ε ell length P pc st memory hDone hDepth
  refine ⟨out,next,ex,le_of_eq hMass,?_⟩
  apply controller_cache_work memory next hDone hDone _ _ (le_of_eq hWork)
  rw [recursive_cache_mass_pc,recursive_cache_mass_debit]

lemma controller_restart_potential_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) :
    ∃ out, ∃ next : ControllerMemory g s α ε ell length (compilerRestartRequest logical) out,
      MachineEval m g ω restartRequestCode st 20 out ∧ next.mass ≤ memory.mass ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+20 := by
  obtain ⟨out,next,ex,hMass,hWork⟩ := controller_restart_core_exec m g ω logical s α ε ell length P st memory hDone hDepth
  exact ⟨out,next,ex,hMass,controller_cache_work memory next hDone hDone _
    (le_of_eq (recursive_cache_mass_restart logical)) hWork⟩

lemma controller_initial_empty_potential_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) :
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerInitialEmpty logical) out,
      MachineEval m g ω initialEmptyCode st steps out ∧ next.mass ≤ memory.mass ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+22 := by
  obtain ⟨u,out,next,ex,hMass,hWork⟩ := controller_initial_empty_exec m g ω logical s α ε ell length P st memory hDone hDepth
  exact ⟨u,out,next,ex,hMass,controller_cache_work memory next hDone hDone _
    (le_of_eq (recursive_cache_mass_initial_empty logical)) hWork⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerBudgetGuards

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma ControllerBudgetFlags.ancestor_guard {n : ℕ} {logical : RecursiveState n} {st : MachineState}
    (flags : ControllerBudgetFlags logical st) (hZero : st.scalar.core.ptrs 0=0) :
    (st.scalar.core.ptrs 170 ≤ st.scalar.core.ptrs 0 ↔ ¬ancestorExhausted logical) := by
  rw [flags.2,hZero]
  by_cases h : ancestorExhausted logical <;> simp [h]

lemma ControllerBudgetFlags.any_guard {n : ℕ} {logical : RecursiveState n} {st : MachineState}
    (flags : ControllerBudgetFlags logical st) (hZero : st.scalar.core.ptrs 0=0) :
    (st.scalar.core.ptrs 160 ≤ st.scalar.core.ptrs 0 ↔ ¬anyExhausted logical) := by
  rw [flags.1,hZero]
  by_cases h : anyExhausted logical <;> simp [h]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerBranchBounded

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 12000000 in
lemma controller_pointer_branch_bounded_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (logical yes no : RecursiveState n)
    (condition : Prop) [Decidable condition] (r t : ℕ) (yesCode noCode : MachineCode)
    (yesCharge noCharge : ℝ≥0∞) (yesGrowth noGrowth M : ℕ) (context : MachineState → Prop)
    (potential : ∀ {logical : RecursiveState n} {st : MachineState}, ControllerMemory g s α ε ell length logical st → ℕ)
    (hPay : ∀ {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st),
      potential memory.payUnit=potential memory)
    (hContext : ∀ st, context st → context (payUnit st))
    (execYes : condition → ∀ st, ∀ memory : ControllerMemory g s α ε ell length logical st, context st → memory.mass ≤ M →
      ∃ steps out, ∃ next : ControllerMemory g s α ε ell length yes out,
        MachineEval m g ω yesCode st steps out ∧ next.mass ≤ memory.mass+yesGrowth ∧
        out.work+(potential next : ℝ≥0∞) ≤ st.work+(potential memory : ℝ≥0∞)+yesCharge)
    (execNo : ¬condition → ∀ st, ∀ memory : ControllerMemory g s α ε ell length logical st, context st → memory.mass ≤ M →
      ∃ steps out, ∃ next : ControllerMemory g s α ε ell length no out,
        MachineEval m g ω noCode st steps out ∧ next.mass ≤ memory.mass+noGrowth ∧
        out.work+(potential next : ℝ≥0∞) ≤ st.work+(potential memory : ℝ≥0∞)+noCharge)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st) (hc : context st) (hMass : memory.mass ≤ M)
    (hGuard : st.scalar.core.ptrs r ≤ st.scalar.core.ptrs t ↔ condition) :
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (if condition then yes else no) out,
      MachineEval m g ω (.branchPointer r t yesCode noCode) st steps out ∧
      next.mass ≤ memory.mass+(if condition then yesGrowth else noGrowth) ∧
      out.work+(potential next : ℝ≥0∞) ≤ st.work+(potential memory : ℝ≥0∞)+(if condition then yesCharge else noCharge)+2 := by
  by_cases h : condition
  · rw [if_pos h,if_pos h,if_pos h]
    obtain ⟨u,out,next,ex,hMass,hWork⟩ := execYes h (payUnit st) memory.payUnit (hContext st hc) (by simpa only [ControllerMemory.payUnit_mass] using hMass)
    have eBranch : MachineEval m g ω (.branchPointer r t yesCode noCode) st (1+u) out :=
      MachineEval.pointerLe memory.halted (hGuard.mpr h) ex
    refine ⟨1+u,out,next,eBranch,?_,?_⟩
    · simpa only [ControllerMemory.payUnit_mass] using hMass
    · rw [payUnit_work,hPay] at hWork
      calc
        _ ≤ (st.work+1)+(potential memory : ℝ≥0∞)+yesCharge := hWork
        _ ≤ _ := by
          have hOne : (1 : ℝ≥0∞) ≤ 2 := by norm_num
          simpa only [add_assoc,add_left_comm,add_comm] using add_le_add (le_refl (st.work+(potential memory : ℝ≥0∞)+yesCharge)) hOne
  · rw [if_neg h,if_neg h,if_neg h]
    obtain ⟨u,out,next,ex,hMass,hWork⟩ := execNo h (payUnit st) memory.payUnit (hContext st hc) (by simpa only [ControllerMemory.payUnit_mass] using hMass)
    have eBranch : MachineEval m g ω (.branchPointer r t yesCode noCode) st (1+u+1) (payUnit out) :=
      MachineEval.pointerGt memory.halted (by intro he; exact h (hGuard.mp he)) ex
    refine ⟨1+u+1,payUnit out,next.payUnit,eBranch,?_,?_⟩
    · simpa only [ControllerMemory.payUnit_mass] using hMass
    · rw [payUnit_work,hPay] at hWork
      rw [payUnit_work,hPay]
      calc
        _ = (out.work+(potential next : ℝ≥0∞))+1 := by ac_rfl
        _ ≤ ((st.work+1)+(potential memory : ℝ≥0∞)+noCharge)+1 := add_le_add hWork le_rfl
        _ = _ := by ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerSelectedDrain

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 18000000 in
lemma controller_selected_drain_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank P Q : ℕ) (pc : NormalizePC)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hKeys : KeysInvariant g logical) (hRegion : RegionInvariant logical) (hBoundary : BoundaryIdentity g logical)
    (hSome : (pendingPush logical).isSome=true) (hSelected : PendingSelectionSpec logical st)
    (hFlags : ControllerBudgetFlags logical st)
    (hMass : ¬anyExhausted logical → memory.mass+2*(logical.top+1)*(drainDegree g logical+1) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerSelectedDrain g α logical pc) out,
      MachineEval m g ω (.branchPointer 160 0 exteriorPushProgramCode (changePCCode pc)) st steps out ∧
      next.mass ≤ memory.mass+(if ¬anyExhausted logical then 2*(logical.top+1)*(drainDegree g logical+1) else 0) ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+
        (if ¬anyExhausted logical then selectedExteriorCharge g logical ell rank P else 10)+2 := by
  let context := fun a => ControllerBudgetFlags logical a ∧ PendingSelectionSpec logical a
  let φ := fun {logical : RecursiveState n} {st : MachineState} (mem : ControllerMemory g s α ε ell length logical st) => mem.potential P Q
  have result := controller_pointer_branch_bounded_exec m g ω s α ε ell length logical
    (compilerDrain g α logical pc) (changePC (debit logical logical.top 1) pc) (¬anyExhausted logical) 160 0
    exteriorPushProgramCode (changePCCode pc) (selectedExteriorCharge g logical ell rank P) 10
    (2*(logical.top+1)*(drainDegree g logical+1)) 0 memory.mass context φ
    (fun mem => mem.potential_payUnit P Q) (fun _ h => ⟨h.1.payUnit,h.2⟩) (by
      intro hAny a mem hc hm
      cases hp : pendingPush logical with
      | none => simp [hp] at hSome
      | some pair =>
        obtain ⟨t,v⟩ := pair
        rw [compilerDrain,hp]
        obtain ⟨u,out,next,ex,hM,hW⟩ := controller_exterior_exec m g ω logical s α ε ell length N rank P Q t v a mem hDone hDepth hKeys hRegion hBoundary hp hc.2 (by
          rw [←mem.mass_live hDone]
          have h := (add_le_add hm le_rfl).trans (hMass hAny)
          simpa only [drainDegree,hp] using h) hCap hPow
        exact ⟨u,out,next,ex,by simpa only [drainDegree,hp] using hM,by simpa only [selectedExteriorCharge,drainDegree,hp] using hW⟩) (by
      intro hAny a mem hc hm
      obtain ⟨out,next,ex,hM,hW⟩ := controller_cheap_potential_exec m g ω logical s α ε ell length P Q pc a mem hDone hDepth
      exact ⟨10,out,next,ex,by simpa using hM,hW⟩)
    st memory ⟨hFlags,hSelected⟩ le_rfl (hFlags.any_guard (memory.live hDone).zero)
  exact result

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

def initialRestartCode (pc : NormalizePC) (noCode : MachineCode) : MachineCode :=
  .branchPointer 170 0 (.seq priorityCode (.branchPointer 97 0 noCode
    (.branchPointer 160 0 exteriorPushProgramCode (changePCCode pc)))) (changePCCode .interrupted)

set_option maxHeartbeats 18000000 in
lemma controller_initial_restart_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical noPending : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank Q : ℕ)
    (pc : NormalizePC) (noCode : MachineCode) (noCharge : ℝ≥0∞)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hKeys : KeysInvariant g logical) (hRegion : RegionInvariant logical) (hBoundary : BoundaryIdentity g logical)
    (hFlags : ControllerBudgetFlags logical st) (hM : memory.mass ≤ N)
    (hMass : ¬ancestorExhausted logical → ¬anyExhausted logical →
      (pendingPush logical).isSome=true → memory.mass+2*(logical.top+1)*(drainDegree g logical+1) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank)
    (noExec : ∀ a, ∀ mem : ControllerMemory g s α ε ell length logical a,
      ∃ u out, ∃ next : ControllerMemory g s α ε ell length noPending out,
        MachineEval m g ω noCode a u out ∧ next.mass ≤ mem.mass ∧
        out.work+(next.potential (cleanBodyBound (16*(ell+3)) length rank+2) Q : ℝ≥0∞) ≤
          a.work+(mem.potential (cleanBodyBound (16*(ell+3)) length rank+2) Q : ℝ≥0∞)+noCharge) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerInitialRestart g α logical pc noPending) out,
      MachineEval m g ω (initialRestartCode pc noCode) st steps out ∧
      next.mass ≤ memory.mass+initialRestartGrowth g logical ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+
        initialRestartCharge g logical ell length rank noCharge := by
  dsimp only
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let φ := fun {logical : RecursiveState n} {st : MachineState} (mem : ControllerMemory g s α ε ell length logical st) => mem.potential P Q
  have result := controller_pointer_branch_bounded_exec m g ω s α ε ell length logical
    (compilerPriorityChoice logical noPending (compilerSelectedDrain g α logical pc)) (changePC (debit logical logical.top 1) .interrupted)
    (¬ancestorExhausted logical) 170 0
    (.seq priorityCode (.branchPointer 97 0 noCode (.branchPointer 160 0 exteriorPushProgramCode (changePCCode pc)))) (changePCCode .interrupted)
    (controllerPriorityCharge logical ell length rank noCharge ((if ¬anyExhausted logical then selectedExteriorCharge g logical ell rank P else 10)+2)) 10
    (if (pendingPush logical).isSome then (if ¬anyExhausted logical then 2*(logical.top+1)*(drainDegree g logical+1) else 0) else 0) 0
    memory.mass (ControllerBudgetFlags logical) φ (fun mem => mem.potential_payUnit P Q) (fun _ h => h.payUnit) (by
      intro hA a mem flags hm
      exact controller_priority_choice_exec m g ω logical noPending (compilerSelectedDrain g α logical pc) s α ε ell length N rank Q memory.mass
        noCode (.branchPointer 160 0 exteriorPushProgramCode (changePCCode pc)) 0
        (if ¬anyExhausted logical then 2*(logical.top+1)*(drainDegree g logical+1) else 0) noCharge
        ((if ¬anyExhausted logical then selectedExteriorCharge g logical ell rank P else 10)+2)
        a mem hDone hDepth flags hm hM hCap hPow (by
          intro hp a mem hm flags spec
          obtain ⟨u,out,next,ex,hM,hW⟩ := noExec a mem
          exact ⟨u,out,next,ex,by simpa using hM,hW⟩) (by
          intro hSome a mem hm flags spec
          simpa only [P,add_assoc] using (controller_selected_drain_exec m g ω logical s α ε ell length N rank P Q pc a mem hDone hDepth hKeys hRegion hBoundary hSome spec flags
            (fun hAny => (add_le_add hm le_rfl).trans (hMass hA hAny hSome)) hCap hPow))) (by
      intro hA a mem flags hm
      obtain ⟨out,next,ex,hM,hW⟩ := controller_cheap_potential_exec m g ω logical s α ε ell length P Q .interrupted a mem hDone hDepth
      exact ⟨10,out,next,ex,by simpa using hM,hW⟩)
    st memory hFlags le_rfl (hFlags.ancestor_guard (memory.live hDone).zero)
  simpa only [compilerInitialRestart,initialRestartCode,initialRestartGrowth,initialRestartCharge,φ,P,add_assoc] using result

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerDepthExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 10000000 in
lemma controller_depth_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) :
    ∃ out, ∃ next : ControllerMemory g s α ε ell length logical out,
      MachineEval m g ω controllerDepthCode st 4 out ∧
      out.scalar.core.ptrs 171=(ell : ℤ) ∧ next.mass=memory.mass ∧
      next.potential P Q=memory.potential P Q ∧ out.work=st.work+4 := by
  let pm := memory.live hDone
  obtain ⟨a,ea,aP,aI,aR,aW,aO,aH⟩ := controllerDepthRoutine.execute m g ω st memory.halted
  let b := payUnit (pointerWrite a 171 (a.scalar.core.ptrs 171-1))
  have eb : MachineEval m g ω (coreCode (.pdec 171)) a 1 b := pdec_eval m g ω a 171 aH
  let out := payUnit (pointerWrite b 171 (b.scalar.core.ptrs 171-1))
  have ec : MachineEval m g ω (coreCode (.pdec 171)) b 1 out := pdec_eval m g ω b 171 aH
  have ex : MachineEval m g ω controllerDepthCode st 4 out := MachineEval.seq ea (MachineEval.seq eb ec)
  have oI : out.scalar.integerMemory=st.scalar.integerMemory := aI
  have oR : out.scalar.core.mem=st.scalar.core.mem := aR
  let om := pm.frame oI oR (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact ex.pointer_frame _ (by decide)) (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact ex.real_register_frame _ (by decide)) aO
  let next := memory.nextLive hDone om hDone ex (by decide) (by decide) aH
    (memory.indexInvariant hDone ex (by decide) (fun v => congrFun oI _))
  have oMass : next.mass=memory.mass := by
    have hn : next.mass=om.queueMass := ControllerMemory.nextLive_mass _ _ _ _ _ _ _ _ _
    exact hn.trans (memory.mass_live hDone).symm
  refine ⟨out,next,ex,?_,oMass,?_,ex.unit_work controllerDepthCode_wellFormed (by decide) memory.halted⟩
  · have a171 : a.scalar.core.ptrs 171=st.scalar.integerMemory 2 := by
      rw [aP]
      simp [controllerDepthRoutine,PointerRoutine.sequence,PointerRoutine.run,PointerOp.update,PointerOp.destination,PointerOp.result]
    change a.scalar.core.ptrs 171-1-1=(ell : ℤ)
    rw [a171,pm.depthMemory]
    push_cast
    ring
  · simp only [ControllerMemory.potential,oMass]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerChildExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 16000000 in
lemma controller_child_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank P Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top < ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hDomain : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hBlock : 1 ≤ (logical.frames logical.top).block)
    (hMass : memory.mass+(logical.frames logical.top).active.card ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let A := ((logical.frames logical.top).block+2)*(4*(ell-(logical.top+1))+22)+10*length+324+
      (logical.frames logical.top).active.card*(21*rank+60*(16*(ell+3))+190)
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (spawnChildState g ell logical) out,
      MachineEval m g ω freshChildCode st steps out ∧
      next.mass ≤ memory.mass+(logical.frames logical.top).active.card ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+
        ((A+P*(logical.frames logical.top).active.card : ℕ) : ℝ≥0∞) := by
  dsimp only
  let pm := memory.live hDone
  let f := pm.frames logical.top le_rfl
  have hLength : f.activeVertices.length=(logical.frames logical.top).active.card := by
    rw [←f.activeSet,List.toFinset_card_of_nodup f.activeNodup]
  obtain ⟨u,out,om,ex,oMass,hu,oQ,oW,oO,oH,oMarks⟩ := fresh_child_simulation m g ω logical s α ε ell length N rank st memory.halted pm hDepth hStored hDomain hBlock (by
    change f.activeVertices.length ≤ N
    rw [hLength]
    omega) hCap hPow
  change om.queueMass ≤ pm.queueMass+f.activeVertices.length at oMass
  change u ≤ ((logical.frames logical.top).block+2)*(4*(ell-(logical.top+1))+22)+10*length+324+
    f.activeVertices.length*(21*rank+60*(16*(ell+3))+190) at hu
  rw [hLength] at oMass hu
  have hTarget : (spawnChildState g ell logical).done=false := hDone
  obtain ⟨next,nMass,nWork⟩ := controller_lift_unit_run (P:=P) memory hDone om hTarget ex (by decide) (by decide) (by decide) oH oMarks oW hu oMass
  exact ⟨u,out,next,ex,nMass,controller_cache_work memory next hDone hTarget _
    (le_of_eq (recursive_cache_mass_child g ell logical)) nWork⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerNormalizeDecision

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 18000000 in
lemma controller_normalize_inner_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank P Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hDomain : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hBlock : 1 ≤ (logical.frames logical.top).block)
    (hMass : logical.top≠ell → memory.mass+(logical.frames logical.top).active.card ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerNormalizeInner g ell logical) out,
      MachineEval m g ω (.seq controllerDepthCode (.branchPointer 171 100 (changePCCode .leafDrain) freshChildCode)) st steps out ∧
      next.mass ≤ memory.mass+(if logical.top=ell then 0 else (logical.frames logical.top).active.card) ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+
        ((if logical.top=ell then 10 else controllerChildCharge logical ell length rank P)+6) := by
  obtain ⟨a,am,ea,a171,aMass,aPhi,aW⟩ := controller_depth_exec m g ω logical s α ε ell length P Q st memory hDone
  let φ := fun {logical : RecursiveState n} {st : MachineState} (mem : ControllerMemory g s α ε ell length logical st) => mem.potential P Q
  let context := fun a : MachineState => a.scalar.core.ptrs 171=(ell : ℤ)
  have hPay : ∀ {l : RecursiveState n} {a : MachineState} (mem : ControllerMemory g s α ε ell length l a), φ mem.payUnit=φ mem := fun mem => mem.potential_payUnit P Q
  have result := controller_pointer_branch_bounded_exec m g ω s α ε ell length logical
    (changePC (debit logical logical.top 1) .leafDrain) (spawnChildState g ell logical) (logical.top=ell)
    171 100 (changePCCode .leafDrain) freshChildCode 10 (controllerChildCharge logical ell length rank P)
    0 (logical.frames logical.top).active.card memory.mass context φ hPay (fun _ h => h) (by
      intro hEq a mem hc hm
      obtain ⟨out,next,ex,hM,hW⟩ := controller_cheap_potential_exec m g ω logical s α ε ell length P Q .leafDrain a mem hDone hDepth
      exact ⟨10,out,next,ex,by simpa using hM,hW⟩) (by
      intro hEq a mem hc hm
      exact controller_child_exec m g ω logical s α ε ell length N rank P Q a mem hDone (by omega) hStored hDomain hBlock
        ((add_le_add hm le_rfl).trans (hMass hEq)) hCap hPow)
    a am a171 (by rw [aMass]) (by rw [a171,(am.live hDone).top]; constructor <;> intro h <;> exact_mod_cast (by omega : _))
  obtain ⟨u,out,next,ex,hM,hW⟩ := result
  refine ⟨4+u,out,next,MachineEval.seq ea ex,?_,?_⟩
  · rw [aMass] at hM
    exact hM
  · change out.work+(next.potential P Q : ℝ≥0∞) ≤ a.work+(am.potential P Q : ℝ≥0∞)+_+2 at hW
    rw [aW,aPhi] at hW
    calc
      _ ≤ _ := hW
      _ = _ := by ring

set_option maxHeartbeats 18000000 in
lemma controller_normalize_decision_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank P Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hDomain : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hBlock : 1 ≤ (logical.frames logical.top).block) (hFlags : ControllerBudgetFlags logical st)
    (hMass : ¬anyExhausted logical → logical.top≠ell → memory.mass+(logical.frames logical.top).active.card ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let growth := if ¬anyExhausted logical then (if logical.top=ell then 0 else (logical.frames logical.top).active.card) else 0
    let charge := (if ¬anyExhausted logical then (if logical.top=ell then 10 else controllerChildCharge logical ell length rank P)+6 else 10)+2
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerNormalizeDecision g ell logical) out,
      MachineEval m g ω controllerNormalizeCode st steps out ∧ next.mass ≤ memory.mass+growth ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+charge := by
  dsimp only
  let φ := fun {logical : RecursiveState n} {st : MachineState} (mem : ControllerMemory g s α ε ell length logical st) => mem.potential P Q
  have hPay : ∀ {l : RecursiveState n} {a : MachineState} (mem : ControllerMemory g s α ε ell length l a), φ mem.payUnit=φ mem := fun mem => mem.potential_payUnit P Q
  have result := controller_pointer_branch_bounded_exec m g ω s α ε ell length logical
    (compilerNormalizeInner g ell logical) (changePC (debit logical logical.top 1) .afterChild) (¬anyExhausted logical)
    160 0 (.seq controllerDepthCode (.branchPointer 171 100 (changePCCode .leafDrain) freshChildCode)) (changePCCode .afterChild)
    ((if logical.top=ell then 10 else controllerChildCharge logical ell length rank P)+6) 10
    (if logical.top=ell then 0 else (logical.frames logical.top).active.card) 0 memory.mass (ControllerBudgetFlags logical) φ hPay
    (fun _ h => h.payUnit) (by
      intro hAny a mem flags hm
      exact controller_normalize_inner_exec m g ω logical s α ε ell length N rank P Q a mem hDone hDepth hStored hDomain hBlock
        (fun hEq => (add_le_add hm le_rfl).trans (hMass hAny hEq)) hCap hPow) (by
      intro hAny a mem flags hm
      obtain ⟨out,next,ex,hM,hW⟩ := controller_cheap_potential_exec m g ω logical s α ε ell length P Q .afterChild a mem hDone hDepth
      exact ⟨10,out,next,ex,by simpa using hM,hW⟩)
    st memory hFlags le_rfl (hFlags.any_guard (memory.live hDone).zero)
  simpa only [compilerNormalizeDecision,controllerNormalizeCode,φ,add_assoc] using result

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerPendingExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 18000000 in
lemma controller_pending_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical noPending : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank Q M : ℕ)
    (noneCode : MachineCode) (noneGrowth : ℕ) (noneCharge : ℝ≥0∞)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hKeys : KeysInvariant g logical) (hRegion : RegionInvariant logical) (hBoundary : BoundaryIdentity g logical)
    (hM : memory.mass ≤ M) (hMN : M ≤ N)
    (hMass : ∀ t v, pendingPush logical=some (t,v) → M+2*(logical.top+1)*((g.neighbors v).length+1) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank)
    (noneExec : pendingPush logical=none → ∀ a, ∀ mem : ControllerMemory g s α ε ell length logical a,
      mem.mass ≤ M →
      ∃ u out, ∃ next : ControllerMemory g s α ε ell length noPending out,
        MachineEval m g ω noneCode a u out ∧ next.mass ≤ mem.mass+noneGrowth ∧
        out.work+(next.potential (cleanBodyBound (16*(ell+3)) length rank+2) Q : ℝ≥0∞) ≤
          a.work+(mem.potential (cleanBodyBound (16*(ell+3)) length rank+2) Q : ℝ≥0∞)+noneCharge) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerPendingDecision g α logical noPending) out,
      MachineEval m g ω (.seq priorityCode (.branchPointer 97 0 noneCode exteriorPushProgramCode)) st steps out ∧
      next.mass ≤ memory.mass+controllerPendingGrowth g logical noneGrowth ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+controllerPendingCharge g logical ell length rank noneCharge := by
  dsimp only
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let T := (logical.top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
  obtain ⟨u,a,am,ea,aSpec,aMass,aAmort,aW,a160,a170⟩ := controller_priority_exec m g ω logical s α ε ell length N rank Q st memory hDone hDepth (hM.trans hMN) hCap hPow
  have hM' : am.payUnit.mass ≤ M := by rw [ControllerMemory.payUnit_mass]; exact aMass.trans hM
  cases hp : pendingPush logical with
  | none =>
    rw [compilerPendingDecision,hp,controllerPendingGrowth,hp]
    obtain ⟨v,out,next,eb,bMass,bW⟩ := noneExec hp (payUnit a) am.payUnit hM'
    have noneSpec : a.scalar.core.ptrs 97=0 ∧ a.scalar.core.ptrs 112=(-1) := by
      simpa only [PendingSelectionSpec,hp] using aSpec
    have h97 : a.scalar.core.ptrs 97=0 := noneSpec.1
    have ec : MachineEval m g ω (.branchPointer 97 0 noneCode exteriorPushProgramCode) a (1+v) out :=
      MachineEval.pointerLe am.halted (by rw [h97,(am.live hDone).zero]) eb
    refine ⟨u+(1+v),out,next,MachineEval.seq ea ec,?_,?_⟩
    · rw [ControllerMemory.payUnit_mass] at bMass
      exact bMass.trans (add_le_add aMass le_rfl)
    · rw [payUnit_work,ControllerMemory.potential_payUnit] at bW
      have hb : out.work+(next.potential P Q : ℝ≥0∞) ≤ a.work+(am.potential P Q : ℝ≥0∞)+(noneCharge+2) := by
        have h12 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
        exact bW.trans (by simpa only [P,add_assoc,add_left_comm,add_comm] using add_le_add (le_refl (a.work+(am.potential P Q : ℝ≥0∞)+noneCharge)) h12)
      have h := potential_prefix_work st.work a.work out.work (noneCharge+2) u (memory.potential P Q) (am.potential P Q) (next.potential P Q) T aW aAmort hb
      simpa only [controllerPendingCharge,hp,P,T,add_assoc] using h
  | some pair =>
    obtain ⟨t,v⟩ := pair
    rw [compilerPendingDecision,hp,controllerPendingGrowth,hp]
    have hSelected : PendingSelectionSpec logical (payUnit a) := aSpec
    obtain ⟨w,out,next,eb,bMass,bW⟩ := controller_exterior_exec m g ω logical s α ε ell length N rank P Q t v (payUnit a) am.payUnit hDone hDepth hKeys hRegion hBoundary hp hSelected (by
      rw [←am.payUnit.mass_live hDone]
      exact (add_le_add hM' le_rfl).trans (hMass t v hp)) hCap hPow
    have spec : a.scalar.core.ptrs 97=1 ∧ a.scalar.core.ptrs 112=(t : ℤ) ∧ a.scalar.core.ptrs 40=(v.val : ℤ) := by simpa only [PendingSelectionSpec,hp] using aSpec
    have ec : MachineEval m g ω (.branchPointer 97 0 noneCode exteriorPushProgramCode) a (1+w+1) (payUnit out) :=
      MachineEval.pointerGt am.halted (by rw [spec.1,(am.live hDone).zero]; norm_num) eb
    refine ⟨u+(1+w+1),payUnit out,next.payUnit,MachineEval.seq ea ec,?_,?_⟩
    · rw [ControllerMemory.payUnit_mass] at bMass ⊢
      exact bMass.trans (add_le_add aMass le_rfl)
    · rw [payUnit_work,ControllerMemory.potential_payUnit] at bW
      rw [payUnit_work,ControllerMemory.potential_payUnit]
      let B := (logical.top+1)*((g.neighbors v).length+1)*(42*rank+168*(16*(ell+3))+910)+P*(2*(logical.top+1)*((g.neighbors v).length+1))
      have hb : out.work+(next.potential P Q : ℝ≥0∞) ≤ a.work+(am.potential P Q : ℝ≥0∞)+((B : ℕ)+1) := by
        simpa only [B,P,add_assoc,add_left_comm,add_comm] using bW
      have h := potential_prefix_work st.work a.work out.work ((B : ℕ)+1) u (memory.potential P Q) (am.potential P Q) (next.potential P Q) T aW aAmort hb
      calc
        _ = (out.work+(next.potential P Q : ℝ≥0∞))+1 := by ac_rfl
        _ ≤ _ := add_le_add h le_rfl
        _ = _ := by simp only [controllerPendingCharge,hp,P,T,B,Nat.cast_add]; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerLeafCoreExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 18000000 in
lemma controller_leaf_core_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hα : 0<α ∧ α<1) (hRegion : RegionInvariant logical) (hKeys : KeysInvariant g logical)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames logical.top).cache ∪ (logical.frames logical.top).high, 0<g.graph.degree v)
    (hMass : (memory.live hDone).queueMass+2*(logical.top+1)*
      (((logical.frames logical.top).cache ∪ (logical.frames logical.top).high).card+
        (volumeNat g ((logical.frames logical.top).cache ∪ (logical.frames logical.top).high)+
          ((logical.frames logical.top).cache ∪ (logical.frames logical.top).high).card)) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let C := (logical.frames logical.top).cache ∪ (logical.frames logical.top).high
    let size := volumeNat g C+C.card
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    let H := 2*P+(21*rank+20*(16*(ell+3))+70)+36
    let A := (C.card+1)*leafPreparationFactor ell logical.top length rank
    let B := leafSolveUnitCost ell logical.top rank C.card size
    let S := A+B+P*(2*(logical.top+1)*size)
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerLeafDecision m g α logical) out,
      MachineEval m g ω leafDecisionCode st steps out ∧
      next.mass ≤ memory.mass+2*(logical.top+1)*(C.card+size) ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+
        ((H+S+12+Q*C.card : ℕ) : ℝ≥0∞)+solveCharge m C.card size := by
  dsimp only
  let pm := memory.live hDone
  let C := (logical.frames logical.top).cache ∪ (logical.frames logical.top).high
  let size := volumeNat g C+C.card
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let H := 2*P+(21*rank+20*(16*(ell+3))+70)+36
  let A := (C.card+1)*leafPreparationFactor ell logical.top length rank
  let B := leafSolveUnitCost ell logical.top rank C.card size
  let S := A+B+P*(2*(logical.top+1)*size)
  obtain ⟨u,out,om,ex,hu,oMass,oWork,oO,oH,oEpoch⟩ := leaf_decision_exec m g ω logical s α ε ell length N rank st memory.halted pm hDepth hα hRegion hKeys hStored hDegree (memory.epoch hDone) hMass hCap hPow
  have hNDone : (compilerLeafDecision m g α logical).done=false := by
    unfold compilerLeafDecision
    split <;> exact hDone
  let next := memory.nextLive hDone om hNDone ex (by decide) (by decide) oH oEpoch
  have newMass : next.mass=om.queueMass := ControllerMemory.nextLive_mass _ _ _ _ _ _ _ _ _
  have oldMass : memory.mass=pm.queueMass := memory.mass_live hDone
  have hInput : out.work+((P*next.mass : ℕ) : ℝ≥0∞) ≤ st.work+((P*memory.mass+(H+S+12) : ℕ) : ℝ≥0∞)+solveCharge m C.card size := by
    rw [newMass,oldMass]
    exact oWork
  have hWork := cache_growth_work st.work out.work (solveCharge m C.card size) (P*memory.mass) (P*next.mass)
    (recursiveCacheMass logical) (recursiveCacheMass (compilerLeafDecision m g α logical)) (H+S+12) Q C.card hInput
    (recursive_cache_mass_leaf_growth m g α logical)
  refine ⟨u,out,next,ex,?_,?_⟩
  · rw [newMass,oldMass]
    exact oMass
  · rw [next.potential_live hNDone,memory.potential_live hDone]
    exact hWork

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerLeafEmpty

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 18000000 in
lemma controller_leaf_empty_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) (hEmpty : (logical.frames logical.top).high=∅)
    (hMass : memory.mass ≤ N) (hCap : rank < length) (hPow : N < 2^rank) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    let H := 2*P+(21*rank+20*(16*(ell+3))+70)+36
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerLeafDecision m g α logical) out,
      MachineEval m g ω leafDecisionCode st steps out ∧ next.mass ≤ memory.mass ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+((H+12 : ℕ) : ℝ≥0∞) := by
  dsimp only
  rw [compilerLeafDecision,if_pos hEmpty]
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let H := 2*P+(21*rank+20*(16*(ell+3))+70)+36
  let pm := memory.live hDone
  obtain ⟨u,a,am,key,ea,aMass,aAmort,aSpec,aR,aW,aQ,aO,aH,aMarks⟩ := high_peek_exec m g ω logical s α ε ell length N rank st memory.halted pm hDepth (by rw [←memory.mass_live hDone]; exact hMass) hCap hPow
  have aAmort' : u+P*am.queueMass ≤ P*pm.queueMass+H := by simpa only [H,P,Nat.add_assoc] using aAmort
  have hk : key=none := by
    cases he : key with
    | none => rfl
    | some k =>
      have spec : k ∈ (logical.frames logical.top).high.image Fin.val ∧
          (∀ z ∈ (logical.frames logical.top).high.image Fin.val, k≤z) ∧ a.scalar.core.ptrs 97=1 ∧ a.scalar.core.ptrs 40=(k : ℤ) := by
        simpa only [ExteriorPeekSpec,he] using aSpec
      simpa [hEmpty] using spec.1
  have spec : (logical.frames logical.top).high.image Fin.val=∅ ∧ a.scalar.core.ptrs 97=0 := by simpa only [ExteriorPeekSpec,hk] using aSpec
  obtain ⟨out,om,eb,bMass,bW,bQ,bO,bH,bMarks⟩ := cheap_pc_index_exec m g ω logical s α ε ell length .afterChild (payUnit a) aH am.payUnit hDepth
  have ec : MachineEval m g ω (.branchPointer 97 0 (changePCCode .afterChild) leafJointSolveCode) a 11 out := MachineEval.pointerLe aH (by rw [spec.2,am.zero]) eb
  have ex : MachineEval m g ω leafDecisionCode st (u+11) out := MachineEval.seq ea ec
  have hMarks : ∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) := fun v => (bMarks v).trans (aMarks v)
  have h53 : out.scalar.core.ptrs 53=st.scalar.core.ptrs 53 :=
    (eb.pointer_frame 53 (by decide)).trans (ea.pointer_frame 53 (by decide))
  have hEpoch : EpochInvariant (n:=n) (16*(ell+3)) out := by
    intro v
    rw [hMarks v,h53]
    exact memory.epoch hDone v
  let next := memory.nextLive hDone om hDone ex (by decide) (by decide) bH hEpoch
  have nMass : next.mass=om.queueMass := ControllerMemory.nextLive_mass _ _ _ _ _ _ _ _ _
  have oldMass : memory.mass=pm.queueMass := memory.mass_live hDone
  have hm : next.mass ≤ memory.mass := by
    rw [nMass,oldMass]
    change om.queueMass=am.queueMass at bMass
    rw [bMass]
    exact aMass
  have hWork : out.work+((P*next.mass : ℕ) : ℝ≥0∞) ≤ st.work+((P*memory.mass : ℕ) : ℝ≥0∞)+((H+12 : ℕ) : ℝ≥0∞) := by
    have hNat : u+11+P*next.mass ≤ P*memory.mass+(H+12) := by
      rw [nMass,oldMass]
      change om.queueMass=am.queueMass at bMass
      rw [bMass]
      omega
    have hc : ((u+11+P*next.mass : ℕ) : ℝ≥0∞) ≤ ((P*memory.mass+(H+12) : ℕ) : ℝ≥0∞) := by exact_mod_cast hNat
    have hUnit : out.work=st.work+(u+11 : ℕ) := by
      rw [bW,payUnit_work,aW]
      push_cast
      ring
    rw [hUnit]
    simpa only [Nat.cast_add,add_assoc] using add_le_add (le_refl st.work) hc
  exact ⟨u+11,out,next,ex,hm,controller_cache_work memory next hDone hDone _ (by rw [recursive_cache_mass_pc,recursive_cache_mass_debit]) hWork⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerLeafTight

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 18000000 in
lemma controller_leaf_tight_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hα : 0<α ∧ α<1) (hRegion : RegionInvariant logical) (hKeys : KeysInvariant g logical)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames logical.top).cache ∪ (logical.frames logical.top).high, 0<g.graph.degree v)
    (hM : memory.mass ≤ N)
    (hMass : (logical.frames logical.top).high≠∅ →
      (memory.live hDone).queueMass+2*(logical.top+1)*
      (((logical.frames logical.top).cache ∪ (logical.frames logical.top).high).card+
        (volumeNat g ((logical.frames logical.top).cache ∪ (logical.frames logical.top).high)+
          ((logical.frames logical.top).cache ∪ (logical.frames logical.top).high).card)) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerLeafDecision m g α logical) out,
      MachineEval m g ω leafDecisionCode st steps out ∧ next.mass ≤ memory.mass+leafTightGrowth g logical ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+leafTightCharge m g logical ell length rank Q := by
  dsimp only
  by_cases hEmpty : (logical.frames logical.top).high=∅
  · have result := controller_leaf_empty_exec m g ω logical s α ε ell length N rank Q st memory hDone hDepth hEmpty hM hCap hPow
    simpa only [leafTightGrowth,leafTightCharge,if_pos hEmpty,Nat.add_zero] using result
  · have result := controller_leaf_core_exec m g ω logical s α ε ell length N rank Q st memory hDone hDepth hα hRegion hKeys hStored hDegree (hMass hEmpty) hCap hPow
    simpa only [leafTightGrowth,leafTightCharge,if_neg hEmpty,add_assoc] using result

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

set_option maxHeartbeats 18000000 in
lemma controller_leaf_decision_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) (hα : 0<α ∧ α<1)
    (hKeys : KeysInvariant g logical) (hRegion : RegionInvariant logical) (hBoundary : BoundaryIdentity g logical)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames logical.top).cache ∪ (logical.frames logical.top).high, 0<g.graph.degree v)
    (hFlags : ControllerBudgetFlags logical st) (hM : memory.mass ≤ N)
    (hLeafMass : ¬anyExhausted logical → memory.mass+leafControllerGrowth g logical ≤ N)
    (hPushMass : ¬anyExhausted logical → ∀ t v, pendingPush logical=some (t,v) → memory.mass+2*(logical.top+1)*((g.neighbors v).length+1) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    let growth := if ¬anyExhausted logical then controllerPendingGrowth g logical (leafControllerGrowth g logical) else 0
    let charge := (if ¬anyExhausted logical then controllerPendingCharge g logical ell length rank (leafControllerCharge m g logical ell length rank Q) else 10)+2
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerLeafController m g α logical) out,
      MachineEval m g ω controllerLeafCode st steps out ∧ next.mass ≤ memory.mass+growth ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+charge := by
  dsimp only
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let φ := fun {logical : RecursiveState n} {st : MachineState} (mem : ControllerMemory g s α ε ell length logical st) => mem.potential P Q
  have hPay : ∀ {l : RecursiveState n} {a : MachineState} (mem : ControllerMemory g s α ε ell length l a), φ mem.payUnit=φ mem := fun mem => mem.potential_payUnit P Q
  have result := controller_pointer_branch_bounded_exec m g ω s α ε ell length logical
    (compilerPendingDecision g α logical (compilerLeafDecision m g α logical)) (changePC (debit logical logical.top 1) .afterChild)
    (¬anyExhausted logical) 160 0 (.seq priorityCode (.branchPointer 97 0 leafDecisionCode exteriorPushProgramCode)) (changePCCode .afterChild)
    (controllerPendingCharge g logical ell length rank (leafControllerCharge m g logical ell length rank Q)) 10
    (controllerPendingGrowth g logical (leafControllerGrowth g logical)) 0 memory.mass
    (ControllerBudgetFlags logical) φ hPay (fun _ h => h.payUnit) (by
      intro hAny a mem flags hm
      exact controller_pending_exec m g ω logical (compilerLeafDecision m g α logical) s α ε ell length N rank Q memory.mass
        leafDecisionCode (leafControllerGrowth g logical) (leafControllerCharge m g logical ell length rank Q)
        a mem hDone hDepth hKeys hRegion hBoundary hm hM (hPushMass hAny) hCap hPow (by
          intro hp a mem hm
          obtain ⟨u,out,next,ex,hM,hW⟩ := controller_leaf_tight_exec m g ω logical s α ε ell length N rank Q a mem hDone hDepth hα hRegion hKeys hStored hDegree (hm.trans hM) (by
            intro hNonempty
            rw [←mem.mass_live hDone]
            exact (add_le_add hm le_rfl).trans (by
              simpa only [leafControllerGrowth,leafTightGrowth,if_neg hNonempty] using hLeafMass hAny)) hCap hPow
          exact ⟨u,out,next,ex,by simpa only [leafControllerGrowth] using hM,by simpa only [leafControllerCharge,add_assoc] using hW⟩)) (by
      intro hAny a mem flags hm
      obtain ⟨out,next,ex,hM,hW⟩ := controller_cheap_potential_exec m g ω logical s α ε ell length P Q .afterChild a mem hDone hDepth
      exact ⟨10,out,next,ex,by simpa using hM,hW⟩)
    st memory hFlags le_rfl (hFlags.any_guard (memory.live hDone).zero)
  simpa only [compilerLeafController,controllerLeafCode,φ,add_assoc] using result

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerBranchPotential

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 12000000 in
lemma controller_pointer_branch_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (logical yes no : RecursiveState n)
    (condition : Prop) [Decidable condition] (r t : ℕ) (yesCode noCode : MachineCode)
    (yesCharge noCharge : ℝ≥0∞) (yesGrowth noGrowth : ℕ) (context : MachineState → Prop)
    (potential : ∀ {logical : RecursiveState n} {st : MachineState}, ControllerMemory g s α ε ell length logical st → ℕ)
    (hPay : ∀ {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st),
      potential memory.payUnit=potential memory)
    (hContext : ∀ st, context st → context (payUnit st))
    (execYes : condition → ∀ st, ∀ memory : ControllerMemory g s α ε ell length logical st, context st →
      ∃ steps out, ∃ next : ControllerMemory g s α ε ell length yes out,
        MachineEval m g ω yesCode st steps out ∧ next.mass ≤ memory.mass+yesGrowth ∧
        out.work+(potential next : ℝ≥0∞) ≤ st.work+(potential memory : ℝ≥0∞)+yesCharge)
    (execNo : ¬condition → ∀ st, ∀ memory : ControllerMemory g s α ε ell length logical st, context st →
      ∃ steps out, ∃ next : ControllerMemory g s α ε ell length no out,
        MachineEval m g ω noCode st steps out ∧ next.mass ≤ memory.mass+noGrowth ∧
        out.work+(potential next : ℝ≥0∞) ≤ st.work+(potential memory : ℝ≥0∞)+noCharge)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st) (hc : context st)
    (hGuard : st.scalar.core.ptrs r ≤ st.scalar.core.ptrs t ↔ condition) :
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (if condition then yes else no) out,
      MachineEval m g ω (.branchPointer r t yesCode noCode) st steps out ∧
      next.mass ≤ memory.mass+(if condition then yesGrowth else noGrowth) ∧
      out.work+(potential next : ℝ≥0∞) ≤ st.work+(potential memory : ℝ≥0∞)+(if condition then yesCharge else noCharge)+2 := by
  by_cases h : condition
  · rw [if_pos h,if_pos h,if_pos h]
    obtain ⟨u,out,next,ex,hMass,hWork⟩ := execYes h (payUnit st) memory.payUnit (hContext st hc)
    have eBranch : MachineEval m g ω (.branchPointer r t yesCode noCode) st (1+u) out :=
      MachineEval.pointerLe memory.halted (hGuard.mpr h) ex
    refine ⟨1+u,out,next,eBranch,?_,?_⟩
    · simpa only [ControllerMemory.payUnit_mass] using hMass
    · rw [payUnit_work,hPay] at hWork
      calc
        _ ≤ (st.work+1)+(potential memory : ℝ≥0∞)+yesCharge := hWork
        _ ≤ _ := by
          have hOne : (1 : ℝ≥0∞) ≤ 2 := by norm_num
          simpa only [add_assoc,add_left_comm,add_comm] using add_le_add (le_refl (st.work+(potential memory : ℝ≥0∞)+yesCharge)) hOne
  · rw [if_neg h,if_neg h,if_neg h]
    obtain ⟨u,out,next,ex,hMass,hWork⟩ := execNo h (payUnit st) memory.payUnit (hContext st hc)
    have eBranch : MachineEval m g ω (.branchPointer r t yesCode noCode) st (1+u+1) (payUnit out) :=
      MachineEval.pointerGt memory.halted (by intro he; exact h (hGuard.mp he)) ex
    refine ⟨1+u+1,payUnit out,next.payUnit,eBranch,?_,?_⟩
    · simpa only [ControllerMemory.payUnit_mass] using hMass
    · rw [payUnit_work,hPay] at hWork
      rw [payUnit_work,hPay]
      calc
        _ = (out.work+(potential next : ℝ≥0∞))+1 := by ac_rfl
        _ ≤ ((st.work+1)+(potential memory : ℝ≥0∞)+noCharge)+1 := add_le_add hWork le_rfl
        _ = _ := by ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerEpisodePotential

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 12000000 in
lemma controller_interrupt_potential_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P Q : ℕ) (pc : NormalizePC)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical)
    (hCredit : 4*(16*(ell+3))+17 ≤ Q) :
    ∃ out, ∃ next : ControllerMemory g s α ε ell length (changePC (finishEpisode (debit logical logical.top 1)) pc) out,
      MachineEval m g ω (interruptEpisodeCode pc) st ((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+70) out ∧
      next.mass ≤ memory.mass ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+70 := by
  obtain ⟨out,next,ex,hMass,hWork⟩ := controller_interrupt_core_exec m g ω logical s α ε ell length P pc st memory hDone hDepth hStored hKeys
  have hNDone : (changePC (finishEpisode (debit logical logical.top 1)) pc).done=false := hDone
  have hDrop : recursiveCacheMass (changePC (finishEpisode (debit logical logical.top 1)) pc)+
      (logical.frames logical.top).cache.card=recursiveCacheMass logical := by
    rw [recursive_cache_mass_pc]
    exact recursive_cache_mass_finish (debit logical logical.top 1)
  have hInput : out.work+((P*next.mass : ℕ) : ℝ≥0∞) ≤ st.work+((P*memory.mass+(4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+70 : ℕ) : ℝ≥0∞) := by
    simpa only [Nat.cast_add,add_assoc] using hWork
  have h := cache_credit_work st.work out.work (P*memory.mass) (P*next.mass) (recursiveCacheMass logical)
    (recursiveCacheMass (changePC (finishEpisode (debit logical logical.top 1)) pc)) (logical.frames logical.top).cache.card
    (4*(16*(ell+3))+17) Q 70 hInput hDrop hCredit
  refine ⟨out,next,ex,hMass,?_⟩
  rw [next.potential_live hNDone,memory.potential_live hDone]
  simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using h

set_option maxHeartbeats 12000000 in
lemma controller_finish_potential_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hDomain : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical)
    (hCredit : 4*(16*(ell+3))+17 ≤ Q) :
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerFinishRequest g logical) out,
      MachineEval m g ω finishRequestCode st steps out ∧ next.mass ≤ memory.mass ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+
        ((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+140 : ℕ) := by
  obtain ⟨u,out,next,ex,hMass,hWork⟩ := controller_finish_core_exec m g ω logical s α ε ell length P st memory hDone hDepth hDomain hStored hKeys
  have hNDone : (compilerFinishRequest g logical).done=false := hDone
  have hCost : (4*(16*(ell+3))+17)*((logical.frames logical.top).active.card+(logical.frames logical.top).cache.card)+140=
      (4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+140) := by ring
  rw [hCost] at hWork
  have hInput : out.work+((P*next.mass : ℕ) : ℝ≥0∞) ≤ st.work+((P*memory.mass+
      (4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+140) : ℕ) : ℝ≥0∞) := by
    simpa only [Nat.cast_add,add_assoc] using hWork
  have h := cache_credit_work st.work out.work (P*memory.mass) (P*next.mass) (recursiveCacheMass logical)
    (recursiveCacheMass (compilerFinishRequest g logical)) (logical.frames logical.top).cache.card
    (4*(16*(ell+3))+17) Q ((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+140)
    hInput (recursive_cache_mass_finish_request g logical) hCredit
  refine ⟨u,out,next,ex,hMass,?_⟩
  rw [next.potential_live hNDone,memory.potential_live hDone]
  simpa only [Nat.cast_add,add_assoc] using h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerFinishDecision

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 18000000 in
lemma controller_finish_decision_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hDomain : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical)
    (hFlags : ControllerBudgetFlags logical st) (hCredit : 4*(16*(ell+3))+17 ≤ Q) :
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerFinishDecision g logical) out,
      MachineEval m g ω controllerFinishCode st steps out ∧ next.mass ≤ memory.mass ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+controllerFinishCharge logical ell := by
  let φ := fun {logical : RecursiveState n} {st : MachineState} (mem : ControllerMemory g s α ε ell length logical st) => mem.potential P Q
  let context := ControllerBudgetFlags logical
  have hPay : ∀ {l : RecursiveState n} {a : MachineState} (mem : ControllerMemory g s α ε ell length l a), φ mem.payUnit=φ mem := fun mem => mem.potential_payUnit P Q
  have hContext : ∀ a, context a → context (payUnit a) := fun _ h => h.payUnit
  have inner : ∀ a, ∀ mem : ControllerMemory g s α ε ell length logical a, context a →
      ∃ u out, ∃ next : ControllerMemory g s α ε ell length
        (if ¬anyExhausted logical then compilerFinishRequest g logical else changePC (finishEpisode (debit logical logical.top 1)) .restartDrain) out,
        MachineEval m g ω (.branchPointer 160 0 finishRequestCode (interruptEpisodeCode .restartDrain)) a u out ∧
        next.mass ≤ mem.mass+(if ¬anyExhausted logical then 0 else 0) ∧
        out.work+(φ next : ℝ≥0∞) ≤ a.work+(φ mem : ℝ≥0∞)+
          (if ¬anyExhausted logical then (((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+140 : ℕ) : ℝ≥0∞) else 70)+2 := by
    intro a mem flags
    apply controller_pointer_branch_exec m g ω s α ε ell length logical _ _ (¬anyExhausted logical) 160 0 _ _ _ _ 0 0 context φ hPay hContext
    · intro h a mem flags
      obtain ⟨u,out,next,ex,hM,hW⟩ := controller_finish_potential_exec m g ω logical s α ε ell length P Q a mem hDone hDepth hDomain hStored hKeys hCredit
      exact ⟨u,out,next,ex,by simpa using hM,hW⟩
    · intro h a mem flags
      obtain ⟨out,next,ex,hM,hW⟩ := controller_interrupt_potential_exec m g ω logical s α ε ell length P Q .restartDrain a mem hDone hDepth hStored hKeys hCredit
      exact ⟨_,out,next,ex,by simpa using hM,hW⟩
    · exact flags
    · exact flags.any_guard (mem.live hDone).zero
  have result := controller_pointer_branch_exec m g ω s α ε ell length logical
    (if ¬anyExhausted logical then compilerFinishRequest g logical else changePC (finishEpisode (debit logical logical.top 1)) .restartDrain)
    (changePC (finishEpisode (debit logical logical.top 1)) .interrupted) (¬ancestorExhausted logical) 170 0
    (.branchPointer 160 0 finishRequestCode (interruptEpisodeCode .restartDrain)) (interruptEpisodeCode .interrupted)
    ((if ¬anyExhausted logical then (((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+140 : ℕ) : ℝ≥0∞) else 70)+2) 70
    0 0 context φ hPay hContext (fun _ a mem flags => by simpa only [add_assoc,ite_self] using inner a mem flags) (by
      intro h a mem flags
      obtain ⟨out,next,ex,hM,hW⟩ := controller_interrupt_potential_exec m g ω logical s α ε ell length P Q .interrupted a mem hDone hDepth hStored hKeys hCredit
      exact ⟨_,out,next,ex,by simpa using hM,hW⟩)
    st memory hFlags (hFlags.ancestor_guard (memory.live hDone).zero)
  simpa only [compilerFinishDecision,controllerFinishCode,controllerFinishCharge,φ,Nat.add_zero,ite_self,add_assoc] using result

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerDrainExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 18000000 in
lemma controller_drain_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank Q : ℕ) (pc : NormalizePC)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hKeys : KeysInvariant g logical) (hRegion : RegionInvariant logical) (hBoundary : BoundaryIdentity g logical)
    (hMass : (memory.live hDone).queueMass+2*(logical.top+1)*(drainDegree g logical+1) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    let T := (logical.top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
    let D := drainDegree g logical+1
    let E := (logical.top+1)*D*(42*rank+168*(16*(ell+3))+910)
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerDrain g α logical pc) out,
      MachineEval m g ω (drainDecisionCode pc) st steps out ∧
      next.mass ≤ memory.mass+2*(logical.top+1)*D ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+
        ((T+E+P*(2*(logical.top+1)*D)+12 : ℕ) : ℝ≥0∞) := by
  dsimp only
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let T := (logical.top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
  let D := drainDegree g logical+1
  let E := (logical.top+1)*D*(42*rank+168*(16*(ell+3))+910)
  let pm := memory.live hDone
  obtain ⟨boundary,hB⟩ := compiler_boundary_nat g logical hBoundary
  obtain ⟨u,out,om,ex,oAmort,oMass,oW,oO,oH,oMarks⟩ := drain_decision_exec m g ω logical s α ε ell length N rank boundary pc st memory.halted pm hDepth hKeys
    (fun i hi => (hRegion i hi).1) (fun i hi => (hRegion i hi).2.2.2.trans (hRegion i hi).1) hB
    (fun t v hp => compiler_pending_boundary_nonnegative g α logical hRegion hBoundary t v hp)
    (fun t v hp => compiler_exterior_keys g α logical t v hKeys) hMass hCap hPow
  have hTarget : (compilerDrain g α logical pc).done=false := by
    unfold compilerDrain
    split
    · exact hDone
    · rw [compiler_exterior_stages]
      change RecursiveState.done ((if _ then _ else _) : RecursiveState n)=false
      split_ifs
      · unfold admitStage
        split_ifs <;> exact hDone
      · exact hDone
  let next := memory.nextLive hDone om hTarget ex (by cases pc <;> decide) (by cases pc <;> decide) oH
    (memory.indexInvariant hDone ex (by cases pc <;> decide) oMarks)
  have oldMass : memory.mass=pm.queueMass := memory.mass_live hDone
  have newMass : next.mass=om.queueMass := ControllerMemory.nextLive_mass _ _ _ _ _ _ _ _ _
  have hWork : out.work+((P*next.mass : ℕ) : ℝ≥0∞) ≤ st.work+((P*memory.mass : ℕ) : ℝ≥0∞)+
      ((T+E+P*(2*(logical.top+1)*D)+12 : ℕ) : ℝ≥0∞) := by
    rw [oW,newMass,oldMass]
    have hc : ((u+P*om.queueMass : ℕ) : ℝ≥0∞) ≤ ((P*pm.queueMass+(T+E+P*(2*(logical.top+1)*D)+12) : ℕ) : ℝ≥0∞) := by
      exact_mod_cast oAmort
    simpa only [Nat.cast_add,add_assoc] using add_le_add (le_refl st.work) hc
  refine ⟨u,out,next,ex,?_,?_⟩
  · rw [newMass,oldMass]
    exact oMass
  · exact controller_cache_work memory next hDone hTarget _ (le_of_eq (recursive_cache_mass_drain g α logical pc)) hWork

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

set_option maxHeartbeats 18000000 in
lemma controller_after_decision_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hRegion : RegionInvariant logical) (hKeys : KeysInvariant g logical) (hBoundary : BoundaryIdentity g logical)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hFlags : ControllerBudgetFlags logical st) (hCredit : 4*(16*(ell+3))+17 ≤ Q)
    (hMass : ¬ancestorExhausted logical → ¬anyExhausted logical → memory.mass+2*(logical.top+1)*(drainDegree g logical+1) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerAfterDecision g α logical) out,
      MachineEval m g ω controllerAfterChildCode st steps out ∧
      next.mass ≤ memory.mass+controllerAfterGrowth g logical ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+controllerAfterCharge g logical ell length rank := by
  dsimp only
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let φ := fun {logical : RecursiveState n} {st : MachineState} (mem : ControllerMemory g s α ε ell length logical st) => mem.potential P Q
  let context := ControllerBudgetFlags logical
  have hPay : ∀ {l : RecursiveState n} {a : MachineState} (mem : ControllerMemory g s α ε ell length l a), φ mem.payUnit=φ mem := fun mem => mem.potential_payUnit P Q
  have hContext : ∀ a, context a → context (payUnit a) := fun _ h => h.payUnit
  have inner : ¬ancestorExhausted logical → ∀ a, ∀ mem : ControllerMemory g s α ε ell length logical a,
      context a → mem.mass ≤ memory.mass →
      ∃ u out, ∃ next : ControllerMemory g s α ε ell length
        (if ¬anyExhausted logical then compilerDrain g α logical .finishEpisode else changePC (finishEpisode (debit logical logical.top 1)) .restartDrain) out,
        MachineEval m g ω (.branchPointer 160 0 (drainDecisionCode .finishEpisode) (interruptEpisodeCode .restartDrain)) a u out ∧
        next.mass ≤ mem.mass+(if ¬anyExhausted logical then 2*(logical.top+1)*(drainDegree g logical+1) else 0) ∧
        out.work+(φ next : ℝ≥0∞) ≤ a.work+(φ mem : ℝ≥0∞)+
          (if ¬anyExhausted logical then controllerDrainCharge g logical ell length rank else 70)+2 := by
    intro hA a mem flags hm
    apply controller_pointer_branch_bounded_exec m g ω s α ε ell length logical _ _ (¬anyExhausted logical) 160 0 _ _ _ _ _ 0 memory.mass context φ hPay hContext
    · intro h a mem flags hmWithin
      obtain ⟨u,out,next,ex,hM,hW⟩ := controller_drain_exec m g ω logical s α ε ell length N rank Q .finishEpisode a mem hDone hDepth hKeys hRegion hBoundary (by
        rw [←mem.mass_live hDone]
        exact (add_le_add hmWithin le_rfl).trans (hMass hA h)) hCap hPow
      exact ⟨u,out,next,ex,hM,hW⟩
    · intro h a mem flags hmWithin
      obtain ⟨out,next,ex,hM,hW⟩ := controller_interrupt_potential_exec m g ω logical s α ε ell length P Q .restartDrain a mem hDone hDepth hStored hKeys hCredit
      exact ⟨_,out,next,ex,by simpa using hM,hW⟩
    · exact flags
    · exact hm
    · exact flags.any_guard (mem.live hDone).zero
  have result := controller_pointer_branch_bounded_exec m g ω s α ε ell length logical
    (if ¬anyExhausted logical then compilerDrain g α logical .finishEpisode else changePC (finishEpisode (debit logical logical.top 1)) .restartDrain)
    (changePC (finishEpisode (debit logical logical.top 1)) .interrupted) (¬ancestorExhausted logical) 170 0
    (.branchPointer 160 0 (drainDecisionCode .finishEpisode) (interruptEpisodeCode .restartDrain)) (interruptEpisodeCode .interrupted)
    ((if ¬anyExhausted logical then controllerDrainCharge g logical ell length rank else 70)+2) 70
    (if ¬anyExhausted logical then 2*(logical.top+1)*(drainDegree g logical+1) else 0) 0 memory.mass context φ hPay hContext (by
      intro hA a mem flags hmWithin
      simpa only [add_assoc] using inner hA a mem flags hmWithin) (by
      intro h a mem flags hmWithin
      obtain ⟨out,next,ex,hM,hW⟩ := controller_interrupt_potential_exec m g ω logical s α ε ell length P Q .interrupted a mem hDone hDepth hStored hKeys hCredit
      exact ⟨_,out,next,ex,by simpa using hM,hW⟩)
    st memory hFlags le_rfl (hFlags.ancestor_guard (memory.live hDone).zero)
  simpa only [compilerAfterDecision,controllerAfterChildCode,controllerAfterCharge,controllerAfterGrowth,φ,Nat.add_zero,ite_self,add_assoc] using result

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerBeginExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 14000000 in
lemma controller_begin_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank P : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) (hRegion : RegionInvariant logical)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hMass : (memory.live hDone).queueMass+2*(logical.top+1)*(logical.frames logical.top).active.card ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let D := 2*(logical.top+1)*(logical.frames logical.top).active.card
    let A := ((2*(4*(16*(ell+3))+17)+10)+((logical.top+1)*(42*rank+60*(16*(ell+3))+284)+11))*
      (logical.frames logical.top).active.card+188
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerBeginEpisode m g logical) out,
      MachineEval m g ω beginEpisodeCode st steps out ∧ next.mass ≤ memory.mass+D ∧
      out.work+((P*next.mass : ℕ) : ℝ≥0∞) ≤ st.work+((P*memory.mass : ℕ) : ℝ≥0∞)+((A+P*D : ℕ) : ℝ≥0∞) := by
  dsimp only
  let pm := memory.live hDone
  obtain ⟨u,out,om,ex,hu,hMassOut,hWork,hQ,hO,hH,hIndex⟩ := begin_episode_exec m g ω logical s α ε ell length N rank st memory.halted pm hDepth hRegion hStored hMass hCap hPow
  have hNextDone : (compilerBeginEpisode m g logical).done=false := hDone
  have hE := memory.indexInvariant hDone ex (by decide) hIndex
  let next := memory.nextLive hDone om hNextDone ex (by decide) (by decide) hH hE
  have newMass : next.mass=om.queueMass := ControllerMemory.nextLive_mass _ _ _ _ _ _ _ _ _
  have oldMass : memory.mass=pm.queueMass := memory.mass_live hDone
  refine ⟨u,out,next,ex,?_,?_⟩
  · rw [newMass,oldMass]
    exact hMassOut
  · have h := unit_amortized_work st.work out.work u P pm.queueMass om.queueMass _ _ hWork hu hMassOut
    rw [←newMass,←oldMass] at h
    simpa only [Nat.cast_add,add_assoc] using h

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerSolvePotential

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 16000000 in
lemma controller_begin_potential_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank P Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) (hRegion : RegionInvariant logical)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hMass : (memory.live hDone).queueMass+2*(logical.top+1)*(logical.frames logical.top).active.card ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let D := 2*(logical.top+1)*(logical.frames logical.top).active.card
    let A := ((2*(4*(16*(ell+3))+17)+10)+((logical.top+1)*(42*rank+60*(16*(ell+3))+284)+11))*
      (logical.frames logical.top).active.card+188
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerBeginEpisode m g logical) out,
      MachineEval m g ω beginEpisodeCode st steps out ∧ next.mass ≤ memory.mass+D ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+((A+P*D : ℕ) : ℝ≥0∞) := by
  dsimp only
  obtain ⟨u,out,next,ex,hMassOut,hWork⟩ := controller_begin_exec m g ω logical s α ε ell length N rank P st memory hDone hDepth hRegion hStored hMass hCap hPow
  refine ⟨u,out,next,ex,hMassOut,?_⟩
  exact controller_cache_work memory next hDone (by exact hDone) _ (by have := recursive_cache_mass_begin m g logical; omega) hWork

set_option maxHeartbeats 16000000 in
lemma controller_full_potential_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank P Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hFlags : ControllerBudgetFlags logical st) (hα : 0<α ∧ α<1)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames logical.top).active, 0<g.graph.degree v)
    (hRegion : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (hKeys : KeysInvariant g logical)
    (hMass : (memory.live hDone).queueMass+2*(logical.top+1)*
      (volumeNat g (logical.frames logical.top).active+(logical.frames logical.top).active.card) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let C := (logical.frames logical.top).active
    let size := volumeNat g C+C.card
    let A := (10*C.card+5)+((24*(16*(ell+3))+100)*size+28)+(jointSolveIterationFactor ell logical.top rank*size+5)+42
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerFullDecision m g α logical) out,
      MachineEval m g ω controllerFullCode st steps out ∧
      next.mass ≤ memory.mass+2*(logical.top+1)*size ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+
        ((A+P*(2*(logical.top+1)*size)+12 : ℕ) : ℝ≥0∞)+solveCharge m C.card size := by
  dsimp only
  obtain ⟨u,out,next,ex,hMassOut,hWork⟩ := controller_full_exec m g ω logical s α ε ell length N rank P st memory hDone hDepth hFlags hα hStored hDegree hRegion hKeys hMass hCap hPow
  refine ⟨u,out,next,ex,hMassOut,?_⟩
  exact controller_cache_work_two (P:=P) (Q:=Q) memory next hDone (by unfold compilerFullDecision; split <;> exact hDone) _ _ (le_of_eq (recursive_cache_mass_full_decision m g α logical)) hWork

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerFullTight

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 18000000 in
lemma controller_full_tight_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank P Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell)
    (hFlags : ControllerBudgetFlags logical st) (hα : 0<α ∧ α<1)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hDegree : ∀ v ∈ (logical.frames logical.top).active, 0<g.graph.degree v)
    (hRegion : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (hKeys : KeysInvariant g logical)
    (hMass : ¬anyExhausted logical → (memory.live hDone).queueMass+2*(logical.top+1)*
      (volumeNat g (logical.frames logical.top).active+(logical.frames logical.top).active.card) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let C := (logical.frames logical.top).active
    let size := volumeNat g C+C.card
    let A := (10*C.card+5)+((24*(16*(ell+3))+100)*size+28)+(jointSolveIterationFactor ell logical.top rank*size+5)+42
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (compilerFullDecision m g α logical) out,
      MachineEval m g ω controllerFullCode st steps out ∧
      next.mass ≤ memory.mass+(if anyExhausted logical then 0 else 2*(logical.top+1)*size) ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+
        (if anyExhausted logical then 12 else ((A+P*(2*(logical.top+1)*size)+12 : ℕ) : ℝ≥0∞)+solveCharge m C.card size) := by
  dsimp only
  by_cases hAny : anyExhausted logical
  · rw [compilerFullDecision,if_pos hAny,if_pos hAny,if_pos hAny]
    obtain ⟨out,next,eb,hM,hW⟩ := controller_cheap_potential_exec m g ω logical s α ε ell length P Q .afterChild (payUnit st) memory.payUnit hDone hDepth
    have ex : MachineEval m g ω controllerFullCode st 12 (payUnit out) :=
      MachineEval.pointerGt memory.halted (by rw [hFlags.1,if_pos hAny,(memory.live hDone).zero]; norm_num) eb
    refine ⟨12,payUnit out,next.payUnit,ex,?_,?_⟩
    · simpa only [ControllerMemory.payUnit_mass,Nat.add_zero] using hM
    · rw [ControllerMemory.potential_payUnit,payUnit_work] at hW
      rw [ControllerMemory.potential_payUnit,payUnit_work]
      calc
        _ = (out.work+(next.potential P Q : ℝ≥0∞))+1 := by ac_rfl
        _ ≤ ((st.work+1)+(memory.potential P Q : ℝ≥0∞)+10)+1 := add_le_add hW le_rfl
        _ = _ := by ring
  · obtain ⟨u,out,next,ex,hM,hW⟩ := controller_full_potential_exec m g ω logical s α ε ell length N rank P Q st memory hDone hDepth hFlags hα hStored hDegree hRegion hKeys (hMass hAny) hCap hPow
    exact ⟨u,out,next,ex,by simpa only [if_neg hAny] using hM,by simpa only [if_neg hAny,add_assoc] using hW⟩

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

-- Proof module: Solutions.ControllerReturnExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 10000000 in
lemma controller_child_return_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hNonzero : logical.top ≠ 0) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length (endCall g α (debit logical logical.top 1)) out,
      MachineEval m g ω controllerReturnCode st 3 out ∧ memory.queueMass ≤ pm.queueMass ∧
      out.work=st.work+3 ∧ out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.ptrs 53=st.scalar.core.ptrs 53 ∧
      out.scalar.core.ptrs 150=st.scalar.core.ptrs 150 ∧ out.scalar.core.ptrs 151=st.scalar.core.ptrs 151 := by
  obtain ⟨b,bm,eb,bMass,bW,bQ,bO,bH⟩ := cheap_child_return_exec m g ω logical s α ε ell length (payUnit st) hh pm.payUnit hNonzero
  have ex : MachineEval m g ω controllerReturnCode st 3 (payUnit b) :=
    MachineEval.pointerGt hh (by rw [pm.top,pm.zero]; exact_mod_cast (show ¬logical.top ≤ 0 by omega)) eb
  exact ⟨payUnit b,bm.payUnit,ex,bMass,by rw [payUnit_work,bW,payUnit_work]; norm_num; ring,
    bQ,bO,bH,eb.integer_memory_frame (by decide),eb.pointer_frame 53 (by decide),
    eb.pointer_frame 150 (by decide),eb.pointer_frame 151 (by decide)⟩

set_option maxHeartbeats 10000000 in
lemma controller_root_return_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hTop : logical.top=0)
    (hStored : (logical.frames 0).active ⊆ logical.stored)
    (hOutside : ∀ v ∉ (logical.frames 0).active, prune (logical.frames 0).q logical.x v=0) :
    ∃ out, MachineEval m g ω controllerReturnCode st
      ((8*(16*(ell+3))+31)*(logical.frames 0).active.card+12) out ∧
      outputVector out.output=potentialOutput g.graph α (prune (logical.frames 0).q logical.x) ∧
      out.work=st.work+((8*(16*(ell+3))+31)*(logical.frames 0).active.card+12 : ℕ) ∧
      out.scalar.core.ptrs 150=1 ∧ out.scalar.core.ptrs 151=st.scalar.core.ptrs 151 ∧ out.scalar.halted=false := by
  obtain ⟨a,ea,aVector,aW,aI,aR,aQ,aH⟩ := root_sparse_output_exec m g ω logical s α ε ell length (payUnit st) hh pm.payUnit hStored hOutside
  let out := payUnit (pointerWrite a 150 1)
  have eb : MachineEval m g ω stopControllerCode a 1 out := pset_eval m g ω a 150 1 aH
  have eBranch : MachineEval m g ω controllerRootReturnCode (payUnit st)
      ((8*(16*(ell+3))+31)*(logical.frames 0).active.card+11) out := by
    convert MachineEval.seq ea eb using 1 <;> (first | rfl | omega)
  have ex : MachineEval m g ω controllerReturnCode st
      ((8*(16*(ell+3))+31)*(logical.frames 0).active.card+12) out := by
    convert MachineEval.pointerLe (r:=100) (s:=0) (b:=coreCode (.pdec 100)) hh
      (by rw [pm.top,hTop,pm.zero]; simp) eBranch using 1 <;> (first | rfl | omega)
  exact ⟨out,ex,aVector,ex.unit_work controllerReturnCode_wellFormed (by decide) hh,
    by simp [out,payUnit,pcSet,pointerWrite],ex.pointer_frame 151 (by decide),aH⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerReturnPotential

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

set_option maxHeartbeats 18000000 in
lemma controller_return_potential_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length P Q : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hStored : (logical.frames 0).active ⊆ logical.stored)
    (hOutside : ∀ v ∉ (logical.frames 0).active, prune (logical.frames 0).q logical.x v=0) :
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (endCall g α (debit logical logical.top 1)) out,
      MachineEval m g ω controllerReturnCode st steps out ∧ next.mass ≤ memory.mass ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+
        ((if logical.top=0 then (8*(16*(ell+3))+31)*(logical.frames 0).active.card+12 else 3 : ℕ) : ℝ≥0∞) := by
  classical
  let pm := memory.live hDone
  by_cases hTop : logical.top=0
  · obtain ⟨out,ex,hVector,hWork,h150,h151,hH⟩ := controller_root_return_exec m g ω logical s α ε ell length st memory.halted pm hTop hStored hOutside
    have hTarget : (endCall g α (debit logical logical.top 1)).done=true := by simp [endCall,hTop,debit]
    have hOutput : outputVector (n:=n) out.output=outputVector (n:=n) (endCall g α (debit logical logical.top 1)).output := by
      rw [hVector]
      simp only [endCall,debit,hTop,if_pos rfl]
      symm
      apply compiler_sparse_vector_eq
      intro v hv
      simp only [potentialOutput,hOutside v hv,mul_zero]
    let next : ControllerMemory g s α ε ell length (endCall g α (debit logical logical.top 1)) out := ControllerMemory.ofDone hTarget h150 (h151.trans memory.one) hH hOutput
    refine ⟨_,out,next,ex,?_,?_⟩
    · rw [next.mass_done hTarget]
      exact Nat.zero_le _
    · rw [next.potential_done hTarget P Q,if_pos hTop,Nat.cast_zero,add_zero,hWork]
      simpa only [add_assoc,add_left_comm,add_comm,add_zero,zero_add] using add_le_add (le_refl (st.work+(((8*(16*(ell+3))+31)*(logical.frames 0).active.card+12 : ℕ) : ℝ≥0∞))) (show (0 : ℝ≥0∞) ≤ (memory.potential P Q : ℝ≥0∞) by positivity)
  · obtain ⟨out,om,ex,oMass,oW,oQ,oO,oH,oI,o53,o150,o151⟩ := controller_child_return_exec m g ω logical s α ε ell length st memory.halted pm hTop
    have hTarget : (endCall g α (debit logical logical.top 1)).done=false := by simp [endCall,hTop,debit,hDone]
    have hEpoch : EpochInvariant (n:=n) (16*(ell+3)) out := by
      intro v
      rw [oI,o53]
      exact memory.epoch hDone v
    let next := ControllerMemory.ofLive om hTarget (by rw [o150,memory.doneFlag,hDone]; rfl) (o151.trans memory.one) oH hEpoch
    have nMass : next.mass ≤ memory.mass := by
      rw [ControllerMemory.ofLive_mass,memory.mass_live hDone]
      exact oMass
    have hWork : out.work+((P*next.mass : ℕ) : ℝ≥0∞) ≤ st.work+((P*memory.mass : ℕ) : ℝ≥0∞)+3 := by
      rw [oW]
      have hCast : ((P*next.mass : ℕ) : ℝ≥0∞) ≤ ((P*memory.mass : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.mul_le_mul_left P nMass
      simpa only [add_assoc,add_left_comm,add_comm] using add_le_add (le_refl (st.work+3)) hCast
    refine ⟨3,out,next,ex,nMass,?_⟩
    rw [if_neg hTop]
    exact controller_cache_work memory next hDone hTarget _ (by
      rw [← recursive_cache_mass_debit logical logical.top 1]
      exact recursive_cache_mass_end_call g α (debit logical logical.top 1)) hWork

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControllerPCExecution

set_option autoImplicit false
set_option maxRecDepth 20000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 24000000 in
lemma controller_pc_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank Q M : ℕ)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length logical st)
    (hDone : logical.done=false) (hDepth : logical.top ≤ ell) (hα : 0<α ∧ α<1)
    (hRegion : RegionInvariant logical) (hKeys : KeysInvariant g logical) (hBoundary : BoundaryIdentity g logical)
    (hParameters : ParameterInvariant logical) (hStored : StoredInvariant g logical) (hNumerical : NumericalInvariant g logical)
    (hFlags : ControllerBudgetFlags logical st) (hm : memory.mass ≤ M)
    (capacities : ControllerCapacities g logical ell M N)
    (hCredit : 4*(16*(ell+3))+17 ≤ Q) (hCap : rank < length) (hPow : N < 2^rank) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (controllerNext m g α ell logical) out,
      MachineEval m g ω (controllerPCCode (logical.frames logical.top).pc) st steps out ∧
      next.mass ≤ M+controllerStepGrowth g ell logical ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+controllerPCCharge m g logical ell length rank Q := by
  dsimp only
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  have hActive := compiler_stored_active_domain g logical hStored logical.top le_rfl
  have hCache := compiler_stored_cache_high_domain g logical hStored hRegion logical.top le_rfl
  have hDomain := (hRegion logical.top le_rfl).1
  have hBlock := (hParameters logical.top le_rfl).2.1
  have hmN : memory.mass ≤ N := hm.trans capacities.base
  cases hPC : (logical.frames logical.top).pc
  all_goals unfold controllerNext controllerStepGrowth controllerPCCharge controllerPCCode
  all_goals rw [hPC]
  all_goals dsimp only
  · obtain ⟨u,out,next,ex,hOut,hWork⟩ := controller_initial_restart_exec m g ω logical (compilerInitialEmpty logical) s α ε ell length N rank Q
      .initialDrain initialEmptyCode 22 st memory hDone hDepth hKeys hRegion hBoundary hFlags hmN (by
        intro hA hAny hSome
        exact (add_le_add hm le_rfl).trans (capacities.push (by rw [hPC]; simp) hAny hSome)) hCap hPow (by
        intro a mem
        exact controller_initial_empty_potential_exec m g ω logical s α ε ell length P Q a mem hDone hDepth)
    exact ⟨u,out,next,ex,hOut.trans (add_le_add hm le_rfl),hWork⟩
  · obtain ⟨u,out,next,ex,hOut,hWork⟩ := controller_begin_potential_exec m g ω logical s α ε ell length N rank P Q st memory hDone hDepth hRegion hActive.1 (by
      rw [←memory.mass_live hDone]
      exact (add_le_add hm le_rfl).trans (capacities.begin hPC)) hCap hPow
    exact ⟨u,out,next,ex,hOut.trans (add_le_add hm le_rfl),hWork⟩
  · obtain ⟨u,out,next,ex,hOut,hWork⟩ := controller_full_tight_exec m g ω logical s α ε ell length N rank P Q st memory hDone hDepth hFlags hα hActive.1 hActive.2
      (fun i hi => (hRegion i hi).1) hKeys (by
        intro hAny
        rw [←memory.mass_live hDone]
        exact (add_le_add hm le_rfl).trans (capacities.full hPC hAny)) hCap hPow
    exact ⟨u,out,next,ex,hOut.trans (add_le_add hm le_rfl),hWork⟩
  · obtain ⟨u,out,next,ex,hOut,hWork⟩ := controller_normalize_decision_exec m g ω logical s α ε ell length N rank P Q st memory hDone hDepth hActive.1 hDomain hBlock hFlags
      (fun hAny hEq => (add_le_add hm le_rfl).trans (capacities.child hPC hAny hEq)) hCap hPow
    exact ⟨u,out,next,ex,hOut.trans (add_le_add hm le_rfl),hWork⟩
  · obtain ⟨u,out,next,ex,hOut,hWork⟩ := controller_leaf_decision_exec m g ω logical s α ε ell length N rank Q st memory hDone hDepth hα hKeys hRegion hBoundary hActive.1 hCache.2 hFlags hmN
      (fun hAny => (add_le_add hm le_rfl).trans (capacities.leaf hPC hAny)) (by
        intro hAny t v hp
        have h := (add_le_add hm le_rfl).trans (capacities.push (by rw [hPC]; simp) hAny (by simp [hp]))
        simpa only [drainDegree,hp] using h) hCap hPow
    exact ⟨u,out,next,ex,hOut.trans (add_le_add hm le_rfl),hWork⟩
  · obtain ⟨u,out,next,ex,hOut,hWork⟩ := controller_after_decision_exec m g ω logical s α ε ell length N rank Q st memory hDone hDepth hRegion hKeys hBoundary hActive.1 hFlags hCredit
      (fun hA hAny => (add_le_add hm le_rfl).trans (capacities.drain hPC hAny)) hCap hPow
    exact ⟨u,out,next,ex,hOut.trans (add_le_add hm le_rfl),hWork⟩
  · obtain ⟨u,out,next,ex,hOut,hWork⟩ := controller_finish_decision_exec m g ω logical s α ε ell length P Q st memory hDone hDepth hDomain hActive.1 hKeys hFlags hCredit
    exact ⟨u,out,next,ex,by simpa only [Nat.add_zero] using hOut.trans hm,hWork⟩
  · obtain ⟨u,out,next,ex,hOut,hWork⟩ := controller_initial_restart_exec m g ω logical (compilerRestartRequest logical) s α ε ell length N rank Q
      .restartDrain restartRequestCode 20 st memory hDone hDepth hKeys hRegion hBoundary hFlags hmN (by
        intro hA hAny hSome
        exact (add_le_add hm le_rfl).trans (capacities.push (by rw [hPC]; simp) hAny hSome)) hCap hPow (by
        intro a mem
        obtain ⟨out,next,ex,hOut,hWork⟩ := controller_restart_potential_exec m g ω logical s α ε ell length P Q a mem hDone hDepth
        exact ⟨20,out,next,ex,hOut,hWork⟩)
    exact ⟨u,out,next,ex,hOut.trans (add_le_add hm le_rfl),hWork⟩
  · obtain ⟨u,out,next,ex,hOut,hWork⟩ := controller_return_potential_exec m g ω logical s α ε ell length P Q st memory hDone (hStored.1 0 (Nat.zero_le _)) (compiler_prune_outside g logical hNumerical)
    exact ⟨u,out,next,ex,by simpa only [Nat.add_zero] using hOut.trans hm,hWork⟩
  · obtain ⟨u,out,next,ex,hOut,hWork⟩ := controller_return_potential_exec m g ω logical s α ε ell length P Q st memory hDone (hStored.1 0 (Nat.zero_le _)) (compiler_prune_outside g logical hNumerical)
    exact ⟨u,out,next,ex,by simpa only [Nat.add_zero] using hOut.trans hm,hWork⟩

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
    (hFlags : ControllerBudgetFlags logical st) (hm : memory.mass ≤ M)
    (capacities : ControllerCapacities g logical ell M N)
    (hCredit : 4*(16*(ell+3))+17 ≤ Q) (hCap : rank < length) (hPow : N < 2^rank),
let P := cleanBodyBound (16*(ell+3)) length rank+2
    ∃ steps out, ∃ next : ControllerMemory g s α ε ell length (controllerNext m g α ell logical) out,
      MachineEval m g ω (controllerPCCode (logical.frames logical.top).pc) st steps out ∧
      next.mass ≤ M+controllerStepGrowth g ell logical ∧
      out.work+(next.potential P Q : ℝ≥0∞) ≤ st.work+(memory.potential P Q : ℝ≥0∞)+controllerPCCharge m g logical ell length rank Q := by
  exact @NearlyOptimalPPR.Computation.controller_pc_exec
