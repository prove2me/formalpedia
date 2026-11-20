-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.exterior_push_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T06:46:21.005143+00:00
-- url     : https://prove2.me/submissions/fa1693fd-4002-4971-802d-38bf8cfd78bb

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
import Theorems.Thm_NearlyOptimalPPR_Computation_exterior_activation_raw_exec
import Theorems.Thm_NearlyOptimalPPR_Computation_exterior_numeric_prefix_exec
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

lemma compiler_raw_residual {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) (δ : ℝ)
    (i : ℕ) (hi : i ≤ st.top) (w : Fin n) :
    ((rawExterior g α st t v δ).frames i).residual w=(st.frames i).residual w+
      (if w=v then if i < t then -LocalPush.deg g.graph v*δ else if i=t then -5*LocalPush.deg g.graph v*δ else 0 else 0)+
      (if w ∈ parentDomain st i ∧ g.graph.Adj w v then (1-α)*δ else 0) := by
  simp only [rawExterior,if_pos hi]

lemma compiler_raw_budget {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) (δ : ℝ)
    (i : ℕ) (hi : i ≤ st.top) :
    ((rawExterior g α st t v δ).frames i).W=(st.frames i).W+
      (if (st.frames i).openBudget=true ∧ t ≤ i then (1-α)*LocalPush.deg g.graph v*δ else 0) := by
  simp only [rawExterior,if_pos hi]

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

lemma compiler_admit_stored {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    (admitStage g st t v).stored=st.stored := by
  unfold admitStage
  split_ifs <;> rfl

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

lemma compiler_exterior_stored {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    (exteriorPush g α st t v).stored=insert v st.stored := by
  classical
  rw [compiler_exterior_stages]
  change RecursiveState.stored ((if _ then _ else _) : RecursiveState n)=_
  split_ifs
  · rw [compiler_admit_stored]
    rfl
  · rfl

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

-- Proof module: Solutions.HeapMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section


lemma nodeCells_mem_iff (p a : ℤ) : a ∈ nodeCells p ↔ p ≤ a ∧ a ≤ p+2 := by
  simp only [nodeCells,Finset.mem_insert,Finset.mem_singleton]
  omega

end
end SparseQueue
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

lemma levelHeaderAddress_injective (level level' slot slot' : ℕ) (hs : slot < 32) (hs' : slot' < 32)
    (he : levelHeaderAddress level slot=levelHeaderAddress level' slot') : level=level' ∧ slot=slot' := by
  unfold levelHeaderAddress at he
  omega

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

lemma frameRankLoadCode_wellFormed : frameRankLoadCode.wellFormed := by
  simp [frameRankLoadCode,frameRankLoadInstructions,linearCode,sequenceCode,MachineCode.wellFormed,
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

lemma exterior_transition_eligibility {n : ℕ} (g : InputGraph n) (α : ℝ)
    (logical : RecursiveState n) (t : ℕ) (source : Fin n) (j width length : ℕ)
    (old out : MachineState) (floor : ℤ)
    (f : RecursiveFrameMemory g logical j width length old floor)
    (hKeys : KeysInvariant g (exteriorPush g α logical t source))
    (hj : j ≤ logical.top)
    (hQ : ((exteriorPush g α logical t source).frames j).q=(logical.frames j).q)
    (hFlags : ∀ u ∈ parentDomain (exteriorPush g α logical t source) j,
      out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+2))=
        if u ∈ ((exteriorPush g α logical t source).frames j).active then 1 else 0)
    (hResidual : ∀ u ∈ parentDomain (exteriorPush g α logical t source) j,
      out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+1))=
        ((exteriorPush g α logical t source).frames j).residual u)
    (hDegree : ∀ u ∈ insert source (g.neighbors source).toFinset,
      out.scalar.integerMemory (vertexRecordAddress width u.val 0)=((g.neighbors u).length : ℤ))
    (hOtherDegree : ∀ u ∉ insert source (g.neighbors source).toFinset,
      out.scalar.integerMemory (vertexRecordAddress width u.val 0)=old.scalar.integerMemory (vertexRecordAddress width u.val 0)) :
    ∀ u ∈ parentDomain (exteriorPush g α logical t source) j,
      u.val ∈ ((exteriorPush g α logical t source).frames j).exterior.image Fin.val ↔
        out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+2))=0 ∧
        ((exteriorPush g α logical t source).frames j).q*(out.scalar.integerMemory (vertexRecordAddress width u.val 0) : ℝ) <
          out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+1)) := by
  classical
  intro u hu
  rw [hFlags u hu,hResidual u hu,compiler_fin_val_image]
  by_cases hT : u ∈ insert source (g.neighbors source).toFinset
  · rw [(hKeys j (by rw [compiler_exterior_top]; exact hj)).1 u,hDegree u hT,compiler_neighbor_degree]
    simp [exteriorKey,hu,LocalPush.deg]
  · obtain ⟨hD,hA,hR,_⟩ := compiler_exterior_outside g α logical t source u hT j
    have huOld := hD.mp hu
    rw [(compiler_exterior_queues_outside g α logical t source u hT j).1,hOtherDegree u hT,hQ,hR]
    have hOld := f.exteriorData.eligibility u huOld
    rw [compiler_fin_val_image,f.activeFlags u huOld,f.residual u huOld] at hOld
    simpa only [hA] using hOld

lemma exterior_transition_high_eligibility {n : ℕ} (g : InputGraph n) (α : ℝ)
    (logical : RecursiveState n) (t : ℕ) (source : Fin n) (j width length : ℕ)
    (old out : MachineState) (floor : ℤ)
    (f : RecursiveFrameMemory g logical j width length old floor)
    (hKeys : KeysInvariant g (exteriorPush g α logical t source))
    (hj : j ≤ logical.top)
    (hTheta : ((exteriorPush g α logical t source).frames j).theta=(logical.frames j).theta)
    (hFlags : ∀ u ∈ parentDomain (exteriorPush g α logical t source) j,
      out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+2))=
        if u ∈ ((exteriorPush g α logical t source).frames j).active then 1 else 0)
    (hResidual : ∀ u ∈ parentDomain (exteriorPush g α logical t source) j,
      out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+1))=
        ((exteriorPush g α logical t source).frames j).residual u)
    (hDegree : ∀ u ∈ insert source (g.neighbors source).toFinset,
      out.scalar.integerMemory (vertexRecordAddress width u.val 0)=((g.neighbors u).length : ℤ))
    (hOtherDegree : ∀ u ∉ insert source (g.neighbors source).toFinset,
      out.scalar.integerMemory (vertexRecordAddress width u.val 0)=old.scalar.integerMemory (vertexRecordAddress width u.val 0)) :
    ∀ u ∈ parentDomain (exteriorPush g α logical t source) j,
      u.val ∈ ((exteriorPush g α logical t source).frames j).high.image Fin.val ↔
        out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+2)) ≠ 0 ∧
        3*((exteriorPush g α logical t source).frames j).theta*(out.scalar.integerMemory (vertexRecordAddress width u.val 0) : ℝ) ≤
          out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+1)) := by
  classical
  intro u hu
  rw [hFlags u hu,hResidual u hu,compiler_fin_val_image]
  by_cases hT : u ∈ insert source (g.neighbors source).toFinset
  · rw [(hKeys j (by rw [compiler_exterior_top]; exact hj)).2 u,hDegree u hT,compiler_neighbor_degree]
    simp [highKey,LocalPush.deg]
  · obtain ⟨hD,hA,hR,_⟩ := compiler_exterior_outside g α logical t source u hT j
    have huOld := hD.mp hu
    rw [(compiler_exterior_queues_outside g α logical t source u hT j).2,hOtherDegree u hT,hTheta,hR]
    have hOld := f.highValid u huOld
    rw [compiler_fin_val_image,f.activeFlags u huOld,f.residual u huOld] at hOld
    simpa only [hA] using hOld

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerExteriorNonactivation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_exterior_nonactivation {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hn : relative st t v+compilerExteriorDelta g α st t v ≠ 3*(st.frames t).q/8) :
    let base := rawExterior g α st t v (compilerExteriorDelta g α st t v)
    (exteriorPush g α st t v).x=base.x ∧
      (exteriorPush g α st t v).boundaryEdges=st.boundaryEdges ∧
      (∀ i, parentDomain (exteriorPush g α st t v) i=parentDomain st i ∧
        ((exteriorPush g α st t v).frames i).active=(st.frames i).active ∧
        ((exteriorPush g α st t v).frames i).reference=(st.frames i).reference ∧
        ((exteriorPush g α st t v).frames i).residual=(base.frames i).residual ∧
        ((exteriorPush g α st t v).frames i).W=(base.frames i).W) := by
  classical
  dsimp only [compilerExteriorDelta] at hn ⊢
  rw [compiler_exterior_stages]
  change (debit (refreshKeys g (if _ then _ else _) _) _ _).x=_ ∧ _
  rw [if_neg hn]
  refine ⟨rfl,rfl,?_⟩
  intro i
  change parentDomain (refreshKeys g _ _) i=_ ∧ _
  rw [compiler_refresh_domain,compiler_raw_domain]
  change _ ∧ ((refreshKeys g _ _).frames i).active=_ ∧ ((refreshKeys g _ _).frames i).reference=_ ∧
    ((refreshKeys g _ _).frames i).residual=_ ∧ ((refreshKeys g _ _).frames i).W=_
  rw [(compiler_refresh_numeric g _ _ i).2.2.2.1,compiler_raw_active,
    (compiler_refresh_numeric g _ _ i).2.2.1,(compiler_refresh_numeric g _ _ i).1,
    (compiler_refresh_numeric g _ _ i).2.1]
  refine ⟨rfl,rfl,?_,rfl,rfl⟩
  funext w
  by_cases hi : i ≤ st.top <;> simp [rawExterior,hi]

lemma compiler_exterior_scalar_parameters {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (i : ℕ) :
    ((exteriorPush g α st t v).frames i).q=(st.frames i).q ∧
      ((exteriorPush g α st t v).frames i).theta=(st.frames i).theta := by
  have h := compiler_exterior_static g α st t v i
  exact ⟨congrArg (fun x => x.2.1) h,congrArg (fun x => x.2.2.2.1) h⟩

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

-- Proof module: Solutions.CacheWriteOtherVertex

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma cache_write_cells_other_vertex (width vertex other field : ℕ) (free : ℤ) (degree : ℕ)
    (hFree : 0 ≤ free) (hWidth : 3 ≤ width) (hf : field < width) (hOther : other ≠ vertex) :
    vertexRecordAddress width other field ∉ cacheWriteCells width vertex free degree := by
  intro h
  rcases Finset.mem_union.mp h with hArray|hMeta
  · obtain ⟨i,hi,he⟩ := (mem_arrayCells free (vertexRecordAddress width other field) degree).mp hArray
    have hn := vertexRecordAddress_negative width other field
    have hi0 := Int.natCast_nonneg i
    omega
  · have hNe (k : ℕ) (hk : k < 3) : vertexRecordAddress width other field ≠ vertexRecordAddress width vertex k := by
      intro he
      exact hOther (vertexRecordAddress_injective width other vertex field k hf (by omega) he).1
    simpa only [Finset.mem_insert,Finset.mem_singleton,hNe 0 (by omega),hNe 1 (by omega),hNe 2 (by omega),or_self] using hMeta

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheRowExtension

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma cache_extension_old_base {n : ℕ} (g : InputGraph n) (stored : Finset (Fin n))
    (width : ℕ) (v : Fin n) (I J : ℤ → ℤ) (free : ℤ) (hFree : 0 ≤ free) (hw : 3 ≤ width)
    (hJ : ∀ z, z ∉ cacheWriteCells width v.val free (g.neighbors v).length → J z=I z)
    (hBase : J (vertexRecordAddress width v.val 1)=if v ∈ stored then I (vertexRecordAddress width v.val 1) else free) :
    ∀ u ∈ stored, J (vertexRecordAddress width u.val 1)=I (vertexRecordAddress width u.val 1) := by
  classical
  intro u hu
  by_cases he : u=v
  · subst u
    simpa only [if_pos hu] using hBase
  · exact hJ _ (cache_write_cells_other_vertex width v.val u.val 1 free (g.neighbors v).length hFree hw (by omega)
      (fun h => he (Fin.ext h)))

lemma cached_row_cells_extension {n : ℕ} (g : InputGraph n) (stored : Finset (Fin n))
    (width : ℕ) (v : Fin n) (I J : ℤ → ℤ) (free : ℤ)
    (hOld : ∀ u ∈ stored, J (vertexRecordAddress width u.val 1)=I (vertexRecordAddress width u.val 1))
    (hBase : J (vertexRecordAddress width v.val 1)=if v ∈ stored then I (vertexRecordAddress width v.val 1) else free) :
    cachedRowCells g J width (insert v stored) ⊆ cachedRowCells g I width stored ∪ arrayCells free (g.neighbors v).length := by
  classical
  intro z hz
  obtain ⟨u,hu,hz⟩ := Finset.mem_biUnion.mp hz
  rcases Finset.mem_insert.mp hu with hu|hu
  · subst u
    rw [hBase] at hz
    by_cases hv : v ∈ stored
    · rw [if_pos hv] at hz
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨v,hv,hz⟩)
    · rw [if_neg hv] at hz
      exact Finset.mem_union_right _ hz
  · rw [hOld u hu] at hz
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨u,hu,hz⟩)

lemma cached_row_extension_disjoint {n : ℕ} (g : InputGraph n) (stored : Finset (Fin n))
    (width : ℕ) (v : Fin n) (I J : ℤ → ℤ) (free : ℤ) (F : Finset ℤ)
    (hOld : ∀ u ∈ stored, J (vertexRecordAddress width u.val 1)=I (vertexRecordAddress width u.val 1))
    (hBase : J (vertexRecordAddress width v.val 1)=if v ∈ stored then I (vertexRecordAddress width v.val 1) else free)
    (hDisjoint : Disjoint F (cachedRowCells g I width stored)) (hBelow : ∀ z ∈ F, z < free) :
    Disjoint F (cachedRowCells g J width (insert v stored)) := by
  apply Finset.disjoint_left.mpr
  intro z hzF hzCache
  rcases Finset.mem_union.mp (cached_row_cells_extension g stored width v I J free hOld hBase hzCache) with hOldZ|hNewZ
  · exact Finset.disjoint_left.mp hDisjoint hzF hOldZ
  · obtain ⟨i,hi,he⟩ := (mem_arrayCells free z (g.neighbors v).length).mp hNewZ
    have hBelowZ := hBelow z hzF
    have hi0 := Int.natCast_nonneg i
    omega

lemma cached_row_cells_congr {n : ℕ} (g : InputGraph n) (stored : Finset (Fin n)) (width : ℕ) (I J : ℤ → ℤ)
    (h : ∀ u ∈ stored, J (vertexRecordAddress width u.val 1)=I (vertexRecordAddress width u.val 1)) :
    cachedRowCells g J width stored=cachedRowCells g I width stored := by
  unfold cachedRowCells
  apply Finset.biUnion_congr rfl
  intro u hu
  rw [h u hu]

lemma cached_row_cells_below {n : ℕ} (g : InputGraph n) (stored : Finset (Fin n)) (width : ℕ) (I : ℤ → ℤ) (free : ℤ)
    (cache : GraphCache g I width stored free) : ∀ z ∈ cachedRowCells g I width stored, z < free := by
  intro z hz
  obtain ⟨u,hu,hz⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨i,hi,he⟩ := (mem_arrayCells _ z _).mp hz
  rw [he]
  exact cache.belowFree u hu i hi

lemma cache_extension_rows_above {n : ℕ} (g : InputGraph n) (stored : Finset (Fin n))
    (width : ℕ) (v : Fin n) (I J : ℤ → ℤ) (free floor : ℤ) (hFree : 0 ≤ free) (hw : 3 ≤ width)
    (hJ : ∀ z, z ∉ cacheWriteCells width v.val free (g.neighbors v).length → J z=I z)
    (hBase : J (vertexRecordAddress width v.val 1)=if v ∈ stored then I (vertexRecordAddress width v.val 1) else free)
    (hFloor : floor ≤ free) (hOld : ∀ u ∈ stored, floor ≤ I (vertexRecordAddress width u.val 1)) :
    ∀ u ∈ insert v stored, floor ≤ J (vertexRecordAddress width u.val 1) := by
  classical
  intro u hu
  rcases Finset.mem_insert.mp hu with hu|hu
  · subst u
    rw [hBase]
    split_ifs with hv
    · exact hOld v hv
    · exact hFloor
  · rw [cache_extension_old_base g stored width v I J free hFree hw hJ hBase u hu]
    exact hOld u hu

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

-- Proof module: Solutions.KeyListPrependMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section

lemma listPrependMemory_outside (I : ℤ → ℤ) (free : ℤ) (key : ℕ) (head z : ℤ)
    (hz : z ∉ nodeCells free) : listPrependMemory I free key head z=I z := by
  have hne : z ≠ free+2 := by intro he; subst z; exact hz (by simp [nodeCells])
  rw [listPrependMemory,Function.update_of_ne hne]
  exact node_alloc_frame _ _ _ _ hz

lemma listPrependMemory_below (I : ℤ → ℤ) (free : ℤ) (key : ℕ) (head z : ℤ)
    (hz : z < free) : listPrependMemory I free key head z=I z := by
  apply listPrependMemory_outside
  intro hm
  have he := (nodeCells_mem_iff free z).mp hm
  omega

end
end SparseQueue
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

lemma frame_list_prepend_below (I : ℤ → ℤ) (free : ℤ) (vertex level headSlot : ℕ) (z : ℤ)
    (hz : z < free) (hHead : z ≠ levelHeaderAddress level headSlot) :
    frameListPrependMemory I free vertex level headSlot z=I z := by
  rw [frameListPrependMemory,Function.update_of_ne hHead,listPrependMemory_below _ _ _ _ _ hz]

lemma frame_list_metadata_other (I : ℤ → ℤ) (level cardSlot volumeSlot width vertex field : ℕ) (degree z : ℤ)
    (hCard : z ≠ levelHeaderAddress level cardSlot) (hVol : z ≠ levelHeaderAddress level volumeSlot)
    (hFlag : z ≠ vertexRecordAddress width vertex (16*(level+1)+field)) :
    frameListMetadataMemory I level cardSlot volumeSlot width vertex field degree z=I z := by
  simp only [frameListMetadataMemory,Function.update_of_ne hFlag,Function.update_of_ne hVol,Function.update_of_ne hCard]

lemma level_header_below_end (level slot : ℕ) (hs : slot < 32) :
    levelHeaderAddress level slot < 128+32*((level+1 : ℕ) : ℤ) := by
  unfold levelHeaderAddress
  push_cast
  omega

lemma frame_list_metadata_on_positive (I : ℤ → ℤ) (level cardSlot volumeSlot width vertex field : ℕ)
    (degree z : ℤ) (hz : 0 ≤ z) (hCard : z ≠ levelHeaderAddress level cardSlot)
    (hVol : z ≠ levelHeaderAddress level volumeSlot) :
    frameListMetadataMemory I level cardSlot volumeSlot width vertex field degree z=I z := by
  apply frame_list_metadata_other I level cardSlot volumeSlot width vertex field degree z hCard hVol
  have := vertexRecordAddress_negative width vertex (16*(level+1)+field)
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

-- Proof module: Solutions.FrameListInsertMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma frame_list_insert_field_frame (I : ℤ → ℤ) (free : ℤ) (hf : 0 ≤ free)
    (vertex other level headSlot cardSlot volumeSlot width field otherField : ℕ)
    (hField : 16*(level+1)+field < width) (ho : otherField < width)
    (hNe : otherField ≠ 16*(level+1)+field) (degree : ℤ) :
    frameListInsertMemory I free vertex level headSlot cardSlot volumeSlot width field degree
      (vertexRecordAddress width other otherField)=I (vertexRecordAddress width other otherField) := by
  have hn := vertexRecordAddress_negative width other otherField
  have hHeader (slot : ℕ) : vertexRecordAddress width other otherField ≠ levelHeaderAddress level slot := by
    have := levelHeaderAddress_positive level slot
    omega
  unfold frameListInsertMemory frameListMetadataMemory
  rw [vertex_integer_update_other_field _ width vertex other (16*(level+1)+field) otherField 1 hField ho hNe,
    Function.update_of_ne (hHeader volumeSlot),Function.update_of_ne (hHeader cardSlot)]
  exact frame_list_prepend_below I free vertex level headSlot _ (by omega) (hHeader headSlot)

lemma frame_list_insert_other_vertex (I : ℤ → ℤ) (free : ℤ) (hf : 0 ≤ free)
    (vertex other level headSlot cardSlot volumeSlot width field otherField : ℕ)
    (hField : 16*(level+1)+field < width) (ho : otherField < width)
    (hNe : other ≠ vertex) (degree : ℤ) :
    frameListInsertMemory I free vertex level headSlot cardSlot volumeSlot width field degree
      (vertexRecordAddress width other otherField)=I (vertexRecordAddress width other otherField) := by
  have hn := vertexRecordAddress_negative width other otherField
  have hHeader (slot : ℕ) : vertexRecordAddress width other otherField ≠ levelHeaderAddress level slot := by
    have := levelHeaderAddress_positive level slot
    omega
  unfold frameListInsertMemory frameListMetadataMemory
  rw [vertex_integer_update_other_vertex _ width vertex other (16*(level+1)+field) otherField 1 hField ho hNe,
    Function.update_of_ne (hHeader volumeSlot),Function.update_of_ne (hHeader cardSlot)]
  exact frame_list_prepend_below I free vertex level headSlot _ (by omega) (hHeader headSlot)

lemma frame_list_insert_flag (I : ℤ → ℤ) (free : ℤ)
    (vertex level headSlot cardSlot volumeSlot width field : ℕ) (degree : ℤ) :
    frameListInsertMemory I free vertex level headSlot cardSlot volumeSlot width field degree
      (vertexRecordAddress width vertex (16*(level+1)+field))=1 := by
  simp only [frameListInsertMemory,frameListMetadataMemory,Function.update_self]

lemma frame_list_insert_old_heap (I : ℤ → ℤ) (free : ℤ)
    (vertex level headSlot cardSlot volumeSlot width field : ℕ) (degree z : ℤ)
    (hz : 128+32*((level+1 : ℕ) : ℤ) ≤ z) (hBelow : z < free)
    (hh : headSlot < 32) (hc : cardSlot < 32) (hv : volumeSlot < 32) :
    frameListInsertMemory I free vertex level headSlot cardSlot volumeSlot width field degree z=I z := by
  have hHeader (slot : ℕ) (hs : slot < 32) : z ≠ levelHeaderAddress level slot := by
    have := level_header_below_end level slot hs
    omega
  rw [frameListInsertMemory,frame_list_metadata_on_positive _ level cardSlot volumeSlot width vertex field degree z
    (by have := Int.natCast_nonneg (level+1); omega) (hHeader cardSlot hc) (hHeader volumeSlot hv)]
  exact frame_list_prepend_below I free vertex level headSlot z hBelow (hHeader headSlot hh)

lemma frame_list_insert_card (I : ℤ → ℤ) (free : ℤ)
    (vertex level headSlot cardSlot volumeSlot width field : ℕ) (degree : ℤ)
    (hfree : 128+32*((level+1 : ℕ) : ℤ) ≤ free)
    (hh : headSlot < 32) (hc : cardSlot < 32) (hv : volumeSlot < 32)
    (hch : cardSlot ≠ headSlot) (hvc : volumeSlot ≠ cardSlot) :
    frameListInsertMemory I free vertex level headSlot cardSlot volumeSlot width field degree
      (levelHeaderAddress level cardSlot)=I (levelHeaderAddress level cardSlot)+1 := by
  have hNeg : levelHeaderAddress level cardSlot ≠ vertexRecordAddress width vertex (16*(level+1)+field) := by
    have := levelHeaderAddress_positive level cardSlot
    have := vertexRecordAddress_negative width vertex (16*(level+1)+field)
    omega
  have hNe (slot : ℕ) (hs : slot < 32) (hne : slot ≠ cardSlot) :
      levelHeaderAddress level cardSlot ≠ levelHeaderAddress level slot := by
    intro he
    exact hne (levelHeaderAddress_injective level level cardSlot slot hc hs he).2.symm
  unfold frameListInsertMemory frameListMetadataMemory
  rw [Function.update_of_ne hNeg,Function.update_of_ne (hNe volumeSlot hv hvc),Function.update_self]
  rw [frame_list_prepend_below _ free vertex level headSlot _
    (lt_of_lt_of_le (level_header_below_end level cardSlot hc) hfree) (hNe headSlot hh hch.symm)]

lemma frame_list_insert_volume (I : ℤ → ℤ) (free : ℤ)
    (vertex level headSlot cardSlot volumeSlot width field : ℕ) (degree : ℤ)
    (hfree : 128+32*((level+1 : ℕ) : ℤ) ≤ free)
    (hh : headSlot < 32) (hv : volumeSlot < 32) (hvh : volumeSlot ≠ headSlot) :
    frameListInsertMemory I free vertex level headSlot cardSlot volumeSlot width field degree
      (levelHeaderAddress level volumeSlot)=I (levelHeaderAddress level volumeSlot)+degree := by
  have hNeg : levelHeaderAddress level volumeSlot ≠ vertexRecordAddress width vertex (16*(level+1)+field) := by
    have := levelHeaderAddress_positive level volumeSlot
    have := vertexRecordAddress_negative width vertex (16*(level+1)+field)
    omega
  have hHead : levelHeaderAddress level volumeSlot ≠ levelHeaderAddress level headSlot := by
    intro he
    exact hvh (levelHeaderAddress_injective level level volumeSlot headSlot hv hh he).2
  unfold frameListInsertMemory frameListMetadataMemory
  rw [Function.update_of_ne hNeg,Function.update_self,frame_list_prepend_below _ free vertex level headSlot _
    (lt_of_lt_of_le (level_header_below_end level volumeSlot hv) hfree) hHead]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ActiveNodeSeparation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma fresh_active_pieces (F A C E H : Finset ℤ)
    (hOld : ([A,C,E,H] : List (Finset ℤ)).Pairwise Disjoint)
    (hF : Disjoint F (A ∪ C ∪ E ∪ H)) :
    ([F ∪ A,C,E,H] : List (Finset ℤ)).Pairwise Disjoint := by
  rw [List.pairwise_cons] at hOld ⊢
  refine ⟨?_,hOld.2⟩
  intro G hG
  apply Finset.disjoint_union_left.mpr
  refine ⟨?_,hOld.1 G hG⟩
  apply hF.mono_right
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hG
  rcases hG with rfl|rfl|rfl
  · intro z hz; exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hz))
  · intro z hz; exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
  · exact Finset.subset_union_right

lemma nodeCells_disjoint_below (free : ℤ) (F : Finset ℤ) (hBelow : ∀ z ∈ F, z < free) :
    Disjoint (nodeCells free) F := by
  apply Finset.disjoint_left.mpr
  intro z hzNode hzF
  have hn := (nodeCells_mem_iff free z).mp hzNode
  have hf := hBelow z hzF
  omega

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

-- Proof module: Solutions.GraphCacheDegreeUpdate

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma GraphCache.degree_update {n : ℕ} (g : InputGraph n) (I : ℤ → ℤ) (width : ℕ)
    (stored : Finset (Fin n)) (free : ℤ) (cache : GraphCache g I width stored free) (v : Fin n) :
    GraphCache g (Function.update I (vertexRecordAddress width v.val 0) ((g.neighbors v).length : ℤ)) width stored free := by
  let J := Function.update I (vertexRecordAddress width v.val 0) ((g.neighbors v).length : ℤ)
  have hField (u : Fin n) (field : ℕ) (hf : field < width) (hn : field ≠ 0) :
      J (vertexRecordAddress width u.val field)=I (vertexRecordAddress width u.val field) :=
    vertex_integer_update_other_field I width v.val u.val 0 field _ (by have := cache.widthBound; omega) hf hn
  refine ⟨cache.widthBound,cache.freeBound,?_,?_,?_,?_,?_⟩
  · intro u
    change J (vertexRecordAddress width u.val 2)=_
    rw [hField u 2 (by have := cache.widthBound; omega) (by decide)]
    exact cache.flag u
  · intro u hu
    by_cases he : u=v
    · subst u
      exact Function.update_self _ _ _
    · have hAddr : vertexRecordAddress width u.val 0 ≠ vertexRecordAddress width v.val 0 := by
        intro h
        exact he (Fin.ext (vertexRecordAddress_injective width u.val v.val 0 0
          (by have := cache.widthBound; omega) (by have := cache.widthBound; omega) h).1)
      change J (vertexRecordAddress width u.val 0)= _
      rw [show J (vertexRecordAddress width u.val 0)=I (vertexRecordAddress width u.val 0) from Function.update_of_ne hAddr _ _]
      exact cache.degree u hu
  · intro u hu
    change 128 ≤ J (vertexRecordAddress width u.val 1)
    rw [hField u 1 (by have := cache.widthBound; omega) (by decide)]
    exact cache.basePositive u hu
  · intro u hu i hi hi'
    change J (J (vertexRecordAddress width u.val 1)+(i : ℤ))=_
    rw [hField u 1 (by have := cache.widthBound; omega) (by decide)]
    have hAddr : I (vertexRecordAddress width u.val 1)+(i : ℤ) ≠ vertexRecordAddress width v.val 0 := by
      have hp := cache.basePositive u hu
      have hn := vertexRecordAddress_negative width v.val 0
      have hi0 := Int.natCast_nonneg i
      omega
    change Function.update I _ _ _ = _
    rw [Function.update_of_ne hAddr]
    exact cache.adjacency u hu i hi hi'
  · intro u hu i hi
    change J (vertexRecordAddress width u.val 1)+(i : ℤ)<free
    rw [hField u 1 (by have := cache.widthBound; omega) (by decide)]
    exact cache.belowFree u hu i hi

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

lemma stored_neighbor_fold_graph_cache {n : ℕ} (g : InputGraph n) (source : Fin n)
    (logical : RecursiveState n) (ell : ℕ) (delta : ℝ) (stored : Finset (Fin n)) (free : ℤ)
    (payload : (ℤ → ℤ) × (ℤ → ℝ)) (cache : GraphCache g payload.1 (16*(ell+3)) stored free) :
    GraphCache g (levelPayloadFold (storedNeighborMemoryUpdate g source logical ell delta) 0
      (g.neighbors source).length payload).1 (16*(ell+3)) stored free := by
  apply level_payload_invariant (storedNeighborMemoryUpdate g source logical ell delta) (limit:=(g.neighbors source).length)
    (P:=fun p => GraphCache g p.1 (16*(ell+3)) stored free)
  · intro i hi p hp
    exact GraphCache.degree_update g p.1 (16*(ell+3)) stored free hp (storedNeighborVertex g source i)
  · omega
  · exact cache

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

lemma stored_neighbor_fold_degree {n : ℕ} (g : InputGraph n) (source u : Fin n)
    (logical : RecursiveState n) (ell : ℕ) (delta : ℝ) (payload : (ℤ → ℤ) × (ℤ → ℝ)) :
    (levelPayloadFold (storedNeighborMemoryUpdate g source logical ell delta) 0
      (g.neighbors source).length payload).1 (vertexRecordAddress (16*(ell+3)) u.val 0)=
        (if g.graph.Adj source u then ((g.neighbors u).length : ℤ) else
          payload.1 (vertexRecordAddress (16*(ell+3)) u.val 0)) := by
  classical
  have h := level_payload_overwrite (storedNeighborMemoryUpdate g source logical ell delta)
    (fun i => u=storedNeighborVertex g source i) (g.neighbors source).length
    (fun p => p.1 (vertexRecordAddress (16*(ell+3)) u.val 0)) ((g.neighbors u).length : ℤ)
    (by
      intro i hi p
      by_cases he : u=storedNeighborVertex g source i
      · simp [storedNeighborMemoryUpdate,←he]
      · rw [if_neg he]
        exact vertex_integer_update_other_vertex p.1 (16*(ell+3)) (storedNeighborVertex g source i).val u.val 0 0 _
          (by omega) (by omega) (by intro hval; exact he (Fin.ext hval)))
    (g.neighbors source).length 0 payload (by omega)
  have hExist : (∃ j, 0 ≤ j ∧ j < 0+(g.neighbors source).length ∧ u=storedNeighborVertex g source j) ↔
      g.graph.Adj source u := by
    rw [←g.correct source u]
    constructor
    · rintro ⟨j,hj0,hj,he⟩
      exact he ▸ storedNeighborVertex_mem g source j (by omega)
    · intro hu
      obtain ⟨j,hj,he⟩ := List.getElem_of_mem hu
      exact ⟨j,Nat.zero_le _,by omega,((storedNeighborVertex_eq g source j hj).trans he).symm⟩
  simpa only [hExist] using h

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

-- Proof module: Solutions.ClearVertexFlagsMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma clear_level_flags_frame (I : ℤ → ℤ) (width vertex base : ℕ) (offsets : List ℕ) (z : ℤ)
    (hz : ∀ k ∈ offsets, z ≠ vertexRecordAddress width vertex (base+k)) :
    clearLevelVertexFlagsMemory I width vertex base offsets z=I z := by
  induction offsets generalizing I with
  | nil => rfl
  | cons offset rest ih =>
    change clearLevelVertexFlagsMemory (Function.update I (vertexRecordAddress width vertex (base+offset)) 0) width vertex base rest z=I z
    rw [ih _ (fun k hk => hz k (by simp [hk]))]
    simp only [Function.update_of_ne (hz offset (by simp))]


lemma clear_level_flags_at (I : ℤ → ℤ) (width vertex base : ℕ) (offsets : List ℕ)
    (hw : ∀ k ∈ offsets, base+k < width) (k : ℕ) (hk : k ∈ offsets) :
    clearLevelVertexFlagsMemory I width vertex base offsets (vertexRecordAddress width vertex (base+k))=0 := by
  classical
  induction offsets generalizing I with
  | nil => simp at hk
  | cons offset rest ih =>
    change clearLevelVertexFlagsMemory (Function.update I (vertexRecordAddress width vertex (base+offset)) 0) width vertex base rest _= _
    by_cases hr : k ∈ rest
    · exact ih _ (fun j hj => hw j (by simp [hj])) hr
    · have he : k=offset := (List.mem_cons.mp hk).resolve_right hr
      subst k
      rw [clear_level_flags_frame]
      · simp
      · intro j hj he
        have hp := hw offset (by simp)
        have hp' := hw j (by simp [hj])
        have he' := (vertexRecordAddress_injective width vertex vertex (base+offset) (base+j) hp hp' he).2
        have hj' : offset=j := by omega
        exact hr (hj' ▸ hj)


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

lemma pending_touched_refresh_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
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
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by
  obtain ⟨steps,out,memory,ex,hSteps,hMass,h40,hQuery,hWork,hOutput,hHalt,hPositive,hFrame⟩ :=
    pending_touched_refresh_foreign_exec m g ω s α ε ell length N R logical st hh pm hDepth hActiveDomain hExtDomain hHighDomain source hs hSource hVertex hDegree hMass hCap hPow hExtOutside hHighOutside hBoolOutside
  exact ⟨steps,out,memory,ex,hSteps,hMass,h40,hQuery,hWork,hOutput,hHalt,hFrame.indexFrame⟩

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

-- Proof module: Solutions.ExteriorSelfBudgetMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma exterior_self_budget_at_residual (I : ℤ → ℤ) (ell top t : ℕ) (hDepth : top ≤ ell)
    (v u : ℕ) (z flow : ℝ) (i j : ℕ) (hi : i ≤ top) (hj : j ≤ top) (R : ℤ → ℝ) :
    exteriorSelfBudgetMemoryUpdate I (16*(ell+3)) v t z flow i R
        (vertexRecordAddress (16*(ell+3)) u (16*(j+1)+1))=
      R (vertexRecordAddress (16*(ell+3)) u (16*(j+1)+1))+
        (if i=j ∧ u=v ∧ i ≤ t then (if i < t then -z else -5*z) else 0) := by
  classical
  have hHead : vertexRecordAddress (16*(ell+3)) u (16*(j+1)+1) ≠ levelHeaderAddress i 4 := by
    have := vertexRecordAddress_negative (16*(ell+3)) u (16*(j+1)+1)
    have := levelHeaderAddress_positive i 4
    omega
  have hSelf :
      (if i ≤ t then Function.update R (vertexRecordAddress (16*(ell+3)) v (16*(i+1)+1))
        (R (vertexRecordAddress (16*(ell+3)) v (16*(i+1)+1))+(if i < t then -z else -5*z)) else R)
        (vertexRecordAddress (16*(ell+3)) u (16*(j+1)+1))=
      R (vertexRecordAddress (16*(ell+3)) u (16*(j+1)+1))+
        (if i=j ∧ u=v ∧ i ≤ t then (if i < t then -z else -5*z) else 0) := by
    by_cases he : i=j ∧ u=v
    · obtain ⟨rfl,rfl⟩ := he
      by_cases ht : i ≤ t <;> simp [ht]
    · have hn : vertexRecordAddress (16*(ell+3)) u (16*(j+1)+1) ≠
          vertexRecordAddress (16*(ell+3)) v (16*(i+1)+1) := by
        intro h
        have hh := vertexRecordAddress_injective (16*(ell+3)) u v (16*(j+1)+1) (16*(i+1)+1) (by omega) (by omega) h
        exact he ⟨by omega,hh.1⟩
      have hNot : ¬(i=j ∧ u=v ∧ i ≤ t) := fun h => he ⟨h.1,h.2.1⟩
      rw [if_neg hNot]
      by_cases ht : i ≤ t
      · rw [if_pos ht,Function.update_of_ne hn,add_zero]
      · rw [if_neg ht,add_zero]
  unfold exteriorSelfBudgetMemoryUpdate
  by_cases hBudget : t ≤ i ∧ 0 < I (levelHeaderAddress i 9)
  · rw [if_pos hBudget,Function.update_of_ne hHead]
    exact hSelf
  · rw [if_neg hBudget]
    exact hSelf

lemma exterior_self_budget_fold_residual (I : ℤ → ℤ) (ell top t : ℕ) (hDepth : top ≤ ell)
    (v u : ℕ) (z flow : ℝ) (j : ℕ) (hj : j ≤ top) (R : ℤ → ℝ) :
    levelRealMemoryFold (exteriorSelfBudgetMemoryUpdate I (16*(ell+3)) v t z flow) 0 (top+1) R
        (vertexRecordAddress (16*(ell+3)) u (16*(j+1)+1))=
      R (vertexRecordAddress (16*(ell+3)) u (16*(j+1)+1))+
        (if u=v ∧ j ≤ t then (if j < t then -z else -5*z) else 0) := by
  classical
  have h := level_memory_additive (exteriorSelfBudgetMemoryUpdate I (16*(ell+3)) v t z flow)
    (fun i => if i=j ∧ u=v ∧ i ≤ t then (if i < t then -z else -5*z) else 0)
    (top+1) (vertexRecordAddress (16*(ell+3)) u (16*(j+1)+1))
    (fun i hi R' => exterior_self_budget_at_residual I ell top t hDepth v u z flow i j (by omega) hj R')
    (top+1) 0 R (by omega)
  simp only [Nat.zero_add] at h
  have hSum : (∑ i ∈ Finset.range (top+1), if i=j ∧ u=v ∧ i ≤ t then (if i < t then -z else -5*z) else 0)=
      (if u=v ∧ j ≤ t then (if j < t then -z else -5*z) else 0) := by
    calc
      _ = (if j=j ∧ u=v ∧ j ≤ t then (if j < t then -z else -5*z) else 0) := by
        apply Finset.sum_eq_single j
        · intro i hi hij
          simp only [hij,false_and,if_false]
        · intro hNot
          exact False.elim (hNot (Finset.mem_range.mpr (by omega)))
      _ = _ := by simp only [true_and]
  rw [hSum] at h
  exact h

lemma exterior_self_budget_at_budget (I : ℤ → ℤ) (width v t : ℕ) (z flow : ℝ) (i j : ℕ) (R : ℤ → ℝ) :
    exteriorSelfBudgetMemoryUpdate I width v t z flow i R (levelHeaderAddress j 4)=
      R (levelHeaderAddress j 4)+(if i=j ∧ t ≤ i ∧ 0 < I (levelHeaderAddress i 9) then flow else 0) := by
  classical
  have hn : levelHeaderAddress j 4 ≠ vertexRecordAddress width v (16*(i+1)+1) := by
    have := levelHeaderAddress_positive j 4
    have := vertexRecordAddress_negative width v (16*(i+1)+1)
    omega
  have hSelf : (if i ≤ t then Function.update R (vertexRecordAddress width v (16*(i+1)+1))
      (R (vertexRecordAddress width v (16*(i+1)+1))+(if i < t then -z else -5*z)) else R) (levelHeaderAddress j 4)=
      R (levelHeaderAddress j 4) := by
    by_cases ht : i ≤ t <;> simp only [ht,if_true,if_false,Function.update_of_ne hn]
  by_cases he : i=j
  · subst i
    unfold exteriorSelfBudgetMemoryUpdate
    by_cases hb : t ≤ j ∧ 0 < I (levelHeaderAddress j 9) <;> simp only [hb,if_true,if_false,Function.update_self,hSelf,true_and]
    all_goals simp_all
  · have hHeader : levelHeaderAddress j 4 ≠ levelHeaderAddress i 4 := by
      intro hh
      exact he (levelHeaderAddress_injective j i 4 4 (by decide) (by decide) hh).1.symm
    have hNever : ¬(i=j ∧ t ≤ i ∧ 0 < I (levelHeaderAddress i 9)) := fun h => he h.1
    unfold exteriorSelfBudgetMemoryUpdate
    rw [if_neg hNever]
    by_cases hb : t ≤ i ∧ 0 < I (levelHeaderAddress i 9)
    · rw [if_pos hb,Function.update_of_ne hHeader,hSelf,add_zero]
    · rw [if_neg hb,hSelf,add_zero]

lemma exterior_self_budget_fold_budget (I : ℤ → ℤ) (width top v t : ℕ) (z flow : ℝ)
    (j : ℕ) (hj : j ≤ top) (R : ℤ → ℝ) :
    levelRealMemoryFold (exteriorSelfBudgetMemoryUpdate I width v t z flow) 0 (top+1) R (levelHeaderAddress j 4)=
      R (levelHeaderAddress j 4)+(if t ≤ j ∧ 0 < I (levelHeaderAddress j 9) then flow else 0) := by
  classical
  have h := level_memory_additive (exteriorSelfBudgetMemoryUpdate I width v t z flow)
    (fun i => if i=j ∧ t ≤ i ∧ 0 < I (levelHeaderAddress i 9) then flow else 0) (top+1) (levelHeaderAddress j 4)
    (fun i hi R' => exterior_self_budget_at_budget I width v t z flow i j R') (top+1) 0 R (by omega)
  simp only [Nat.zero_add] at h
  have hSum : (∑ i ∈ Finset.range (top+1), if i=j ∧ t ≤ i ∧ 0 < I (levelHeaderAddress i 9) then flow else 0)=
      (if t ≤ j ∧ 0 < I (levelHeaderAddress j 9) then flow else 0) := by
    calc
      _ = (if j=j ∧ t ≤ j ∧ 0 < I (levelHeaderAddress j 9) then flow else 0) := by
        apply Finset.sum_eq_single j
        · intro i hi hij
          simp only [hij,false_and,if_false]
        · intro hNot
          exact False.elim (hNot (Finset.mem_range.mpr (by omega)))
      _ = _ := by simp only [true_and]
  rw [hSum] at h
  exact h

lemma exterior_self_budget_fold_frame (I : ℤ → ℤ) (width top v t : ℕ) (z flow : ℝ) (R : ℤ → ℝ) (a : ℤ)
    (hResidual : ∀ i ≤ top, a ≠ vertexRecordAddress width v (16*(i+1)+1))
    (hBudget : ∀ i ≤ top, a ≠ levelHeaderAddress i 4) :
    levelRealMemoryFold (exteriorSelfBudgetMemoryUpdate I width v t z flow) 0 (top+1) R a=R a := by
  apply level_memory_frame (limit:=top+1)
  · intro i hi R'
    unfold exteriorSelfBudgetMemoryUpdate
    split_ifs <;> simp_all only [Function.update_of_ne (hResidual i (by omega)),Function.update_of_ne (hBudget i (by omega))]
  · omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorNumericMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma exterior_self_correction {n : ℕ} (u v : Fin n) (j t : ℕ) (d δ : ℝ) :
    (if u.val=v.val ∧ j ≤ t then (if j < t then -(d*δ) else -5*(d*δ)) else 0)=
      (if u=v then if j < t then -d*δ else if j=t then -5*d*δ else 0 else 0) := by
  classical
  by_cases he : u=v
  · subst u
    by_cases hlt : j<t
    · simp [hlt,show j ≤ t by omega]
    · by_cases hjt : j=t
      · subst j
        simp
        ring
      · simp [hlt,hjt,show ¬j ≤ t by omega]
  · have hval : u.val ≠ v.val := fun h => he (Fin.ext h)
    simp [he,hval]

lemma exterior_numeric_payload_residual {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (α : ℝ) (t : ℕ) (v u : Fin n) (δ : ℝ) (I : ℤ → ℤ) (R : ℤ → ℝ)
    (j : ℕ) (hj : j ≤ logical.top) :
    (exteriorNumericPayload g logical ell α t v δ I R).2 (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))=
      R (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))+
        (if u=v then if j<t then -LocalPush.deg g.graph v*δ else if j=t then -5*LocalPush.deg g.graph v*δ else 0 else 0)+
        (if u ∈ parentDomain logical j ∧ g.graph.Adj u v then (1-α)*δ else 0) := by
  classical
  unfold exteriorNumericPayload
  rw [stored_neighbor_fold_residual g v u logical ell hDepth _ j hj]
  dsimp only [Prod.snd]
  rw [exterior_self_budget_fold_residual I ell logical.top t hDepth v.val u.val _ _ j hj,
    vertex_memory_update_other_field R (16*(ell+3)) v.val u.val 0 (16*(j+1)+1) _ (by omega) (by omega) (by omega),
    exterior_self_correction]
  have hN : (g.graph.Adj v u ∧ u ∈ parentDomain logical j) ↔ (u ∈ parentDomain logical j ∧ g.graph.Adj u v) := by
    constructor
    · intro h
      exact ⟨h.2,g.graph.adj_symm h.1⟩
    · intro h
      exact ⟨g.graph.adj_symm h.2,h.1⟩
  simp only [hN]

lemma exterior_numeric_payload_potential {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (α : ℝ) (t : ℕ) (v u : Fin n) (δ : ℝ) (I : ℤ → ℤ) (R : ℤ → ℝ) :
    (exteriorNumericPayload g logical ell α t v δ I R).2 (vertexRecordAddress (16*(ell+3)) u.val 0)=
      R (vertexRecordAddress (16*(ell+3)) u.val 0)+(if u=v then δ else 0) := by
  classical
  unfold exteriorNumericPayload
  rw [stored_neighbor_fold_real_field g v u logical ell hDepth _ _ 0 (by omega) (by intros; omega)]
  dsimp only [Prod.snd]
  rw [exterior_self_budget_fold_frame]
  · by_cases he : u=v
    · subst u
      simp
    · rw [vertex_memory_update_other_vertex R (16*(ell+3)) v.val u.val 0 0 _ (by omega) (by omega) (fun h => he (Fin.ext h)),if_neg he,add_zero]
  · intro i hi
    intro h
    have := (vertexRecordAddress_injective (16*(ell+3)) u.val v.val 0 (16*(i+1)+1) (by omega) (by omega) h).2
    omega
  · intro i hi
    have := vertexRecordAddress_negative (16*(ell+3)) u.val 0
    have := levelHeaderAddress_positive i 4
    omega

lemma exterior_numeric_payload_budget {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (t : ℕ) (v : Fin n) (δ : ℝ) (I : ℤ → ℤ) (R : ℤ → ℝ)
    (j : ℕ) (hj : j ≤ logical.top) :
    (exteriorNumericPayload g logical ell α t v δ I R).2 (levelHeaderAddress j 4)=
      R (levelHeaderAddress j 4)+(if t ≤ j ∧ 0 < I (levelHeaderAddress j 9) then (1-α)*LocalPush.deg g.graph v*δ else 0) := by
  unfold exteriorNumericPayload
  rw [stored_neighbor_fold_real_positive g v logical ell _ _ _ (by have := levelHeaderAddress_positive j 4; omega)]
  dsimp only [Prod.snd]
  rw [exterior_self_budget_fold_budget I (16*(ell+3)) logical.top v.val t _ _ j hj]
  have hn : levelHeaderAddress j 4 ≠ vertexRecordAddress (16*(ell+3)) v.val 0 := by
    have := levelHeaderAddress_positive j 4
    have := vertexRecordAddress_negative (16*(ell+3)) v.val 0
    omega
  rw [Function.update_of_ne hn]

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

lemma exterior_numeric_payload_degree {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (t : ℕ) (v u : Fin n) (δ : ℝ) (I : ℤ → ℤ) (R : ℤ → ℝ) :
    (exteriorNumericPayload g logical ell α t v δ I R).1 (vertexRecordAddress (16*(ell+3)) u.val 0)=
      (if g.graph.Adj v u then ((g.neighbors u).length : ℤ) else I (vertexRecordAddress (16*(ell+3)) u.val 0)) := by
  unfold exteriorNumericPayload
  exact stored_neighbor_fold_degree g v u logical ell _ _

lemma exterior_numeric_payload_real_field {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (hDepth : logical.top ≤ ell) (α : ℝ) (t : ℕ) (v u : Fin n) (δ : ℝ) (I : ℤ → ℤ) (R : ℤ → ℝ) (field : ℕ)
    (hf : field < 16*(ell+3)) (h0 : field ≠ 0) (hSafe : ∀ i ≤ logical.top, field ≠ 16*(i+1)+1) :
    (exteriorNumericPayload g logical ell α t v δ I R).2 (vertexRecordAddress (16*(ell+3)) u.val field)=
      R (vertexRecordAddress (16*(ell+3)) u.val field) := by
  unfold exteriorNumericPayload
  rw [stored_neighbor_fold_real_field g v u logical ell hDepth _ _ field hf hSafe]
  dsimp only [Prod.snd]
  rw [exterior_self_budget_fold_frame]
  · exact vertex_memory_update_other_field R (16*(ell+3)) v.val u.val 0 field _ (by omega) hf h0
  · intro i hi he
    exact hSafe i hi (vertexRecordAddress_injective (16*(ell+3)) u.val v.val field (16*(i+1)+1) hf (by omega) he).2
  · intro i hi
    have := vertexRecordAddress_negative (16*(ell+3)) u.val field
    have := levelHeaderAddress_positive i 4
    omega

lemma exterior_numeric_payload_real_positive {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (t : ℕ) (v : Fin n) (δ : ℝ) (I : ℤ → ℤ) (R : ℤ → ℝ) (z : ℤ) (hz : 0 ≤ z)
    (hSafe : ∀ i ≤ logical.top, z ≠ levelHeaderAddress i 4) :
    (exteriorNumericPayload g logical ell α t v δ I R).2 z=R z := by
  unfold exteriorNumericPayload
  rw [stored_neighbor_fold_real_positive g v logical ell _ _ z hz]
  dsimp only [Prod.snd]
  rw [exterior_self_budget_fold_frame]
  · apply Function.update_of_ne
    have := vertexRecordAddress_negative (16*(ell+3)) v.val 0
    omega
  · intro i hi
    have := vertexRecordAddress_negative (16*(ell+3)) v.val (16*(i+1)+1)
    omega
  · exact hSafe

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

-- Proof module: Solutions.FreshVertexMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma fresh_vertex_real_frame (R : ℤ → ℝ) (width vertex parent : ℕ) (z : ℤ)
    (h0 : z ≠ vertexRecordAddress width vertex (parent+16))
    (h1 : z ≠ vertexRecordAddress width vertex (parent+17))
    (h4 : z ≠ vertexRecordAddress width vertex (parent+20)) :
    freshVertexRealMemory R width vertex parent z=R z := by
  simp only [freshVertexRealMemory,Function.update_of_ne h0,Function.update_of_ne h1,Function.update_of_ne h4]

lemma fresh_vertex_real_positive (R : ℤ → ℝ) (width vertex parent : ℕ) (z : ℤ) (hz : 0 ≤ z) :
    freshVertexRealMemory R width vertex parent z=R z := by
  have hneg (offset : ℕ) : z ≠ vertexRecordAddress width vertex offset := by
    have hn := vertexRecordAddress_negative width vertex offset
    omega
  exact fresh_vertex_real_frame R width vertex parent z (hneg _) (hneg _) (hneg _)

lemma fresh_vertex_integer_positive (I : ℤ → ℤ) (width vertex parent : ℕ) (z : ℤ) (hz : 0 ≤ z) :
    clearLevelVertexFlagsMemory I width vertex (parent+16) [2,3,4,5,6] z=I z := by
  apply clear_level_flags_frame
  intro k hk
  have hn := vertexRecordAddress_negative width vertex (parent+16+k)
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorNumericSourceRecords

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma exterior_numeric_source_residual {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (machine : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical machine)
    (hDepth : logical.top ≤ ell) (t : ℕ) (v u : Fin n) (δ : ℝ) (J : ℤ → ℤ)
    (j : ℕ) (hj : j ≤ logical.top) (hu : u ∈ parentDomain logical j) :
    (exteriorNumericPayload g logical ell α t v δ J machine.scalar.core.mem).2
      (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))=
        ((rawExterior g α logical t v δ).frames j).residual u := by
  rw [exterior_numeric_payload_residual g logical ell hDepth α t v u δ J _ j hj,
    (pm.frames j hj).residual u hu,compiler_raw_residual g α logical t v δ j hj u]

lemma exterior_numeric_source_reference {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (machine : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical machine)
    (hDepth : logical.top ≤ ell) (t : ℕ) (v u : Fin n) (δ : ℝ) (J : ℤ → ℤ)
    (j : ℕ) (hj : j ≤ logical.top) (hu : u ∈ parentDomain logical j) :
    (exteriorNumericPayload g logical ell α t v δ J machine.scalar.core.mem).2
      (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)))=
        ((rawExterior g α logical t v δ).frames j).reference u := by
  rw [exterior_numeric_payload_real_field g logical ell hDepth α t v u δ J _ (16*(j+1))
    (by omega) (by omega) (by intros; omega),(pm.frames j hj).reference u hu]
  simp [rawExterior,hj]

lemma exterior_numeric_source_budget {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (machine : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical machine)
    (t : ℕ) (v : Fin n) (δ : ℝ) (J : ℤ → ℤ)
    (j : ℕ) (hj : j ≤ logical.top)
    (hOpen : J (levelHeaderAddress j 9)=machine.scalar.integerMemory (levelHeaderAddress j 9)) :
    (exteriorNumericPayload g logical ell α t v δ J machine.scalar.core.mem).2 (levelHeaderAddress j 4)=
        ((rawExterior g α logical t v δ).frames j).W := by
  rw [exterior_numeric_payload_budget g logical ell α t v δ J _ j hj,
    (pm.frames j hj).W,hOpen,(pm.frames j hj).openBudget,compiler_raw_budget g α logical t v δ j hj]
  cases (logical.frames j).openBudget <;> simp [and_comm]

lemma exterior_numeric_source_potential {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (machine : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical machine)
    (hDepth : logical.top ≤ ell) (t : ℕ) (v u : Fin n) (δ : ℝ) (J : ℤ → ℤ) :
    (exteriorNumericPayload g logical ell α t v δ J machine.scalar.core.mem).2
      (vertexRecordAddress (16*(ell+3)) u.val 0)=(rawExterior g α logical t v δ).x u := by
  rw [exterior_numeric_payload_potential g logical ell hDepth α t v u δ J _,pm.potential u]
  by_cases h : u=v <;> simp [rawExterior,h]

lemma exterior_numeric_source_seed_marker {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (machine : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical machine)
    (hDepth : logical.top ≤ ell) (t : ℕ) (v u : Fin n) (δ : ℝ) (J : ℤ → ℤ) :
    (exteriorNumericPayload g logical ell α t v δ J machine.scalar.core.mem).2
      (vertexRecordAddress (16*(ell+3)) u.val 2)=LocalPush.e s u := by
  rw [exterior_numeric_payload_real_field g logical ell hDepth α t v u δ J _ 2
    (by omega) (by omega) (by intros; omega)]
  exact pm.seedMarker u

lemma exterior_numeric_source_header {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (ell : ℕ) (α : ℝ) (t : ℕ) (v : Fin n) (δ : ℝ) (J : ℤ → ℤ) (R : ℤ → ℝ)
    (j slot : ℕ) (hs : slot < 32) (h4 : slot ≠ 4) :
    (exteriorNumericPayload g logical ell α t v δ J R).2 (levelHeaderAddress j slot)=R (levelHeaderAddress j slot) := by
  apply exterior_numeric_payload_real_positive
  · have := levelHeaderAddress_positive j slot
    omega
  · intro i hi he
    exact h4 (levelHeaderAddress_injective j i slot 4 hs (by decide) he).2

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorNumericDegreeRecords

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma exterior_numeric_touched_degrees {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (t : ℕ) (v : Fin n) (δ : ℝ) (J : ℤ → ℤ) (R : ℤ → ℝ) (free : ℤ)
    (hCache : GraphCache g J (16*(ell+3)) (insert v logical.stored) free) :
    ∀ u ∈ insert v (g.neighbors v).toFinset,
      (exteriorNumericPayload g logical ell α t v δ J R).1 (vertexRecordAddress (16*(ell+3)) u.val 0)=
        ((g.neighbors u).length : ℤ) := by
  classical
  intro u hu
  rw [exterior_numeric_payload_degree]
  rcases Finset.mem_insert.mp hu with hself|hu
  · subst u
    simp only [g.graph.loopless.irrefl,if_false]
    exact hCache.degree v (Finset.mem_insert_self _ _)
  · have hAdj : g.graph.Adj v u := (g.correct v u).mp (List.mem_toFinset.mp hu)
    rw [if_pos hAdj]

lemma exterior_numeric_other_degrees {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (t : ℕ) (v : Fin n) (δ : ℝ) (J I : ℤ → ℤ) (R : ℤ → ℝ) (free : ℤ)
    (hFree : 0 ≤ free)
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val free (g.neighbors v).length → J z=I z) :
    ∀ u ∉ insert v (g.neighbors v).toFinset,
      (exteriorNumericPayload g logical ell α t v δ J R).1 (vertexRecordAddress (16*(ell+3)) u.val 0)=
        I (vertexRecordAddress (16*(ell+3)) u.val 0) := by
  classical
  intro u hu
  have hne : u ≠ v := by intro he; subst u; simp at hu
  have hn : ¬g.graph.Adj v u := by
    intro h
    exact hu (Finset.mem_insert_of_mem (List.mem_toFinset.mpr ((g.correct v u).mpr h)))
  rw [exterior_numeric_payload_degree,if_neg hn]
  apply hJ
  exact cache_write_cells_other_vertex (16*(ell+3)) v.val u.val 0 free (g.neighbors v).length hFree
    (by omega) (by omega) (fun h => hne (Fin.ext h))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorBooleanOutside

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma exterior_transition_boolean_outside {n : ℕ} (g : InputGraph n) (α : ℝ)
    (logical : RecursiveState n) (t : ℕ) (source : Fin n) (j width length : ℕ)
    (old out : MachineState) (floor : ℤ)
    (f : RecursiveFrameMemory g logical j width length old floor)
    (hTheta : ((exteriorPush g α logical t source).frames j).theta=(logical.frames j).theta)
    (hFlags : ∀ u ∈ parentDomain (exteriorPush g α logical t source) j,
      out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+2))=
        if u ∈ ((exteriorPush g α logical t source).frames j).active then 1 else 0)
    (hResidual : ∀ u ∈ parentDomain (exteriorPush g α logical t source) j,
      out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+1))=
        ((exteriorPush g α logical t source).frames j).residual u)
    (hOtherDegree : ∀ u ∉ insert source (g.neighbors source).toFinset,
      out.scalar.integerMemory (vertexRecordAddress width u.val 0)=old.scalar.integerMemory (vertexRecordAddress width u.val 0))
    (hBits : ∀ u ∉ insert source (g.neighbors source).toFinset,
      out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+4))=
        old.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+4))) :
    HighBooleanRecords out.scalar.integerMemory out.scalar.core.mem width (16*(j+1))
      ((exteriorPush g α logical t source).frames j).theta
      (parentDomain (exteriorPush g α logical t source) j \ insert source (g.neighbors source).toFinset) := by
  intro u hu
  obtain ⟨hD,hT⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨hd,ha,hr,_⟩ := compiler_exterior_outside g α logical t source u hT j
  have oldD := hd.mp hD
  change out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+4))=_
  rw [hBits u hT,hFlags u hD,hOtherDegree u hT,hResidual u hD,hTheta,hr]
  have hOld := f.highBoolean u oldD
  rw [f.activeFlags u oldD,f.residual u oldD] at hOld
  simpa only [ha] using hOld

lemma exterior_transition_queue_cover {n : ℕ} (g : InputGraph n) (α : ℝ)
    (logical : RecursiveState n) (t : ℕ) (source : Fin n) (j : ℕ) (ext high : Finset ℕ)
    (hExt : (logical.frames j).exterior.image Fin.val ⊆ ext)
    (hHigh : (logical.frames j).high.image Fin.val ⊆ high) :
    ((exteriorPush g α logical t source).frames j).exterior.image Fin.val \
      (insert source (g.neighbors source).toFinset).image Fin.val ⊆ ext ∧
    ((exteriorPush g α logical t source).frames j).high.image Fin.val \
      (insert source (g.neighbors source).toFinset).image Fin.val ⊆ high := by
  constructor
  · intro k hk
    obtain ⟨hK,hT⟩ := Finset.mem_sdiff.mp hk
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hK
    have huT : u ∉ insert source (g.neighbors source).toFinset := by
      simpa only [compiler_fin_val_image] using hT
    apply hExt
    exact Finset.mem_image.mpr ⟨u,(compiler_exterior_queues_outside g α logical t source u huT j).1.mp hu,rfl⟩
  · intro k hk
    obtain ⟨hK,hT⟩ := Finset.mem_sdiff.mp hk
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hK
    have huT : u ∉ insert source (g.neighbors source).toFinset := by
      simpa only [compiler_fin_val_image] using hT
    apply hHigh
    exact Finset.mem_image.mpr ⟨u,(compiler_exterior_queues_outside g α logical t source u huT j).2.mp hu,rfl⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorNumericPendingFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 2500000 in
def exterior_numeric_pending_frame {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (old out : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (t : ℕ) (v : Fin n) (J : ℤ → ℤ)
    (hNoAdmit : relative logical t v+compilerExteriorDelta g α logical t v ≠ 3*(logical.frames t).q/8)
    (hKeys : KeysInvariant g (exteriorPush g α logical t v))
    (hCache : GraphCache g J (16*(ell+3)) (insert v logical.stored) (out.scalar.core.ptrs 20))
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val (old.scalar.core.ptrs 20) (g.neighbors v).length → J z=old.scalar.integerMemory z)
    (hPayload : (out.scalar.integerMemory,out.scalar.core.mem)=
      exteriorNumericPayload g logical ell α t v (compilerExteriorDelta g α logical t v) J old.scalar.core.mem)
    (hFree : old.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20) (j : ℕ) (hj : j ≤ logical.top) :
    FramePendingKeys g (exteriorPush g α logical t v) j (16*(ell+3)) length out (128+32*((ell+2 : ℕ) : ℤ)) := by
  classical
  let δ := compilerExteriorDelta g α logical t v
  let width := 16*(ell+3)
  let f := pm.frames j hj
  have hNon := (compiler_exterior_nonactivation g α logical t v hNoAdmit).2.2 j
  have hDomain := hNon.1
  have hActive := hNon.2.1
  have hReference := hNon.2.2.1
  have hResidual := hNon.2.2.2.1
  have hBudget := hNon.2.2.2.2
  have hI : out.scalar.integerMemory=(exteriorNumericPayload g logical ell α t v δ J old.scalar.core.mem).1 := congrArg Prod.fst hPayload
  have hR : out.scalar.core.mem=(exteriorNumericPayload g logical ell α t v δ J old.scalar.core.mem).2 := congrArg Prod.snd hPayload
  have hOldFree : 0 ≤ old.scalar.core.ptrs 20 := by have := pm.allocator; omega
  have hHeaderI (slot : ℕ) (hs : slot < 32) :
      out.scalar.integerMemory (levelHeaderAddress j slot)=old.scalar.integerMemory (levelHeaderAddress j slot) := by
    rw [hI,exterior_numeric_payload_integer_positive g logical ell α t v δ J _ _ (by have := levelHeaderAddress_positive j slot; omega)]
    apply hJ
    apply cache_write_cells_below_positive
    · have := levelHeaderAddress_positive j slot; omega
    · have := level_header_below_end j slot hs
      have := pm.allocator
      omega
  have hJOpen : J (levelHeaderAddress j 9)=old.scalar.integerMemory (levelHeaderAddress j 9) := by
    rw [←hHeaderI 9 (by decide),hI,exterior_numeric_payload_integer_positive g logical ell α t v δ J _ _
      (by have := levelHeaderAddress_positive j 9; omega)]
  have hHeaderR (slot : ℕ) (hs : slot < 32) (hn : slot ≠ 4) :
      out.scalar.core.mem (levelHeaderAddress j slot)=old.scalar.core.mem (levelHeaderAddress j slot) := by
    rw [hR]
    exact exterior_numeric_source_header g logical ell α t v δ J _ j slot hs hn
  have hRef : ∀ u ∈ parentDomain (exteriorPush g α logical t v) j,
      out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)))=((exteriorPush g α logical t v).frames j).reference u := by
    intro u hu
    rw [hDomain] at hu
    rw [hR,hReference]
    have he := exterior_numeric_source_reference g logical s α ε ell length old pm hDepth t v u δ J j hj hu
    simpa only [rawExterior,if_pos hj] using he
  have hRes : ∀ u ∈ parentDomain (exteriorPush g α logical t v) j,
      out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+1))=((exteriorPush g α logical t v).frames j).residual u := by
    intro u hu
    rw [hDomain] at hu
    rw [hR,hResidual]
    exact exterior_numeric_source_residual g logical s α ε ell length old pm hDepth t v u δ J j hj hu
  have hFields : ∀ u ∈ parentDomain logical j, ∀ offset, 2 ≤ offset → offset ≤ 6 →
      out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+offset))=
        old.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+offset)) := by
    intro u hu offset hlo hhi
    rw [hI,exterior_numeric_payload_integer_field g logical ell α t v u δ J _ _ (by omega) (by omega)]
    apply hJ
    exact cache_write_cells_negative_field width v.val u.val _ _ _ hOldFree (by omega)
      (by omega) (by omega)
  have hFlags : ∀ u ∈ parentDomain (exteriorPush g α logical t v) j,
      out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+2))=
        if u ∈ ((exteriorPush g α logical t v).frames j).active then 1 else 0 := by
    intro u hu
    rw [hDomain] at hu
    rw [hFields u hu 2 (by decide) (by decide),hActive]
    exact f.activeFlags u hu
  have hDeg := exterior_numeric_touched_degrees g logical ell α t v δ J old.scalar.core.mem _ hCache
  have hOtherDeg := exterior_numeric_other_degrees g logical ell α t v δ J old.scalar.integerMemory old.scalar.core.mem _ hOldFree hJ
  have hDeg' : ∀ u ∈ insert v (g.neighbors v).toFinset,
      out.scalar.integerMemory (vertexRecordAddress width u.val 0)=((g.neighbors u).length : ℤ) := by
    intro u hu
    rw [hI]
    exact hDeg u hu
  have hOtherDeg' : ∀ u ∉ insert v (g.neighbors v).toFinset,
      out.scalar.integerMemory (vertexRecordAddress width u.val 0)=old.scalar.integerMemory (vertexRecordAddress width u.val 0) := by
    intro u hu
    rw [hI]
    exact hOtherDeg u hu
  apply (FramePendingKeys.ofMemory f).numeric_frame hFree hDomain hActive
    (compiler_exterior_static g α logical t v j) hHeaderI hHeaderR
  · rw [hR,hBudget]
    exact exterior_numeric_source_budget g logical s α ε ell length old pm t v δ J j hj hJOpen
  · exact hRef
  · exact hRes
  · exact hFields
  · intro z hz
    have hAbove := f.owned_above z hz
    have hBelow := f.owned_below z hz
    rw [hI,exterior_numeric_payload_integer_positive g logical ell α t v δ J _ z (by omega)]
    exact hJ z (cache_write_cells_below_positive width v.val _ z _ (by omega) hBelow)
  · exact exterior_transition_eligibility g α logical t v j width length old out _ f hKeys hj
      (compiler_exterior_scalar_parameters g α logical t v j).1 hFlags hRes hDeg' hOtherDeg'
  · exact exterior_transition_high_eligibility g α logical t v j width length old out _ f hKeys hj
      (compiler_exterior_scalar_parameters g α logical t v j).2 hFlags hRes hDeg' hOtherDeg'

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveDegreeDomainInsert

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma recursive_degree_domain_exterior {n : ℕ} (g : InputGraph n) (α : ℝ) (s : Fin n) (logical : RecursiveState n)
    (t : ℕ) (v : Fin n) :
    recursiveDegreeDomain g s (exteriorPush g α logical t v)=
      recursiveDegreeDomain g s logical ∪ insert v (g.neighbors v).toFinset := by
  classical
  rw [recursiveDegreeDomain,compiler_exterior_stored]
  change insert s (touchedBy g (insert v logical.stored))=_
  change insert s (touchedBy g (insert v logical.stored))=insert s (touchedBy g logical.stored) ∪ _
  simp only [touchedBy,Finset.biUnion_insert]
  ext u
  simp only [Finset.mem_insert,Finset.mem_union]
  tauto

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorNumericPendingMemory

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 6000000 in
def exterior_numeric_pending_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ) (old out : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (t : ℕ) (v : Fin n) (J : ℤ → ℤ) (steps : ℕ)
    (ex : MachineEval m g ω exteriorNumericPrefixCode old steps out)
    (hNoAdmit : relative logical t v+compilerExteriorDelta g α logical t v ≠ 3*(logical.frames t).q/8)
    (hKeys : KeysInvariant g (exteriorPush g α logical t v))
    (hCache : GraphCache g J (16*(ell+3)) (insert v logical.stored) (out.scalar.core.ptrs 20))
    (hOutCache : GraphCache g out.scalar.integerMemory (16*(ell+3)) (insert v logical.stored) (out.scalar.core.ptrs 20))
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val (old.scalar.core.ptrs 20) (g.neighbors v).length → J z=old.scalar.integerMemory z)
    (hBase : J (vertexRecordAddress (16*(ell+3)) v.val 1)=if v ∈ logical.stored then old.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 1) else old.scalar.core.ptrs 20)
    (hPayload : (out.scalar.integerMemory,out.scalar.core.mem)=
      exteriorNumericPayload g logical ell α t v (compilerExteriorDelta g α logical t v) J old.scalar.core.mem)
    (hFree : old.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hTop : out.scalar.core.ptrs 100=(logical.top : ℤ)) (hOutput : out.output=old.output) :
    MachinePendingKeys g s α ε ell length (exteriorPush g α logical t v) out := by
  classical
  let next := exteriorPush g α logical t v
  let δ := compilerExteriorDelta g α logical t v
  let width := 16*(ell+3)
  have hNextTop : next.top=logical.top := compiler_exterior_top g α logical t v
  have hStored : next.stored=insert v logical.stored := compiler_exterior_stored g α logical t v
  have hOldFree : 0 ≤ old.scalar.core.ptrs 20 := by have := pm.allocator; omega
  have hI : out.scalar.integerMemory=(exteriorNumericPayload g logical ell α t v δ J old.scalar.core.mem).1 := congrArg Prod.fst hPayload
  have hR : out.scalar.core.mem=(exteriorNumericPayload g logical ell α t v δ J old.scalar.core.mem).2 := congrArg Prod.snd hPayload
  have hPositiveI (z : ℤ) (hz : 0 ≤ z) (hBelow : z < old.scalar.core.ptrs 20) : out.scalar.integerMemory z=old.scalar.integerMemory z := by
    rw [hI,exterior_numeric_payload_integer_positive g logical ell α t v δ J _ z hz]
    exact hJ z (cache_write_cells_below_positive width v.val _ z _ hz hBelow)
  have hPositiveR (z : ℤ) (hz : 0 ≤ z) (hSmall : z < 128) : out.scalar.core.mem z=old.scalar.core.mem z := by
    rw [hR]
    apply exterior_numeric_payload_real_positive g logical ell α t v δ J _ z hz
    intro i hi he
    have := levelHeaderAddress_positive i 4
    simp only [levelHeaderAddress] at he
    omega
  have hRowBase (u : Fin n) : out.scalar.integerMemory (vertexRecordAddress width u.val 1)=J (vertexRecordAddress width u.val 1) := by
    rw [hI]
    exact exterior_numeric_payload_integer_field g logical ell α t v u δ J _ 1 (by omega) (by decide)
  have hOldBases : ∀ u ∈ logical.stored,
      out.scalar.integerMemory (vertexRecordAddress width u.val 1)=old.scalar.integerMemory (vertexRecordAddress width u.val 1) := by
    intro u hu
    rw [hRowBase]
    exact cache_extension_old_base g logical.stored width v old.scalar.integerMemory J _ hOldFree (by omega) hJ hBase u hu
  have hNewBase : out.scalar.integerMemory (vertexRecordAddress width v.val 1)=
      if v ∈ logical.stored then old.scalar.integerMemory (vertexRecordAddress width v.val 1) else old.scalar.core.ptrs 20 := by
    rw [hRowBase,hBase]
  have hDegrees := exterior_numeric_touched_degrees g logical ell α t v δ J old.scalar.core.mem _ hCache
  have hOther := exterior_numeric_other_degrees g logical ell α t v δ J old.scalar.integerMemory old.scalar.core.mem _ hOldFree hJ
  let frames : ∀ j ≤ next.top, FramePendingKeys g next j width length out (128+32*((ell+2 : ℕ) : ℤ)) :=
    fun j hj => exterior_numeric_pending_frame g logical s α ε ell length old out pm hDepth t v J hNoAdmit hKeys hCache hJ hPayload hFree j (by rw [hNextTop] at hj; exact hj)
  refine {
    zero := (ex.pointer_frame 0 (by decide)).trans pm.zero
    top := by rw [hNextTop]; exact hTop
    width := (ex.pointer_frame 50 (by decide)).trans pm.width
    alphaRegister := (ex.real_register_frame 30 (by decide)).trans pm.alphaRegister
    one := (ex.real_register_frame 31 (by decide)).trans pm.one
    alphaMemory := (hPositiveR 0 (by decide) (by decide)).trans pm.alphaMemory
    epsilonMemory := (hPositiveR 1 (by decide) (by decide)).trans pm.epsilonMemory
    depthMemory := (hPositiveI 2 (by decide) (by have := pm.allocator; omega)).trans pm.depthMemory
    lengthMemory := (hPositiveI 5 (by decide) (by have := pm.allocator; omega)).trans pm.lengthMemory
    seedMemory := (hPositiveI 0 (by decide) (by have := pm.allocator; omega)).trans pm.seedMemory
    allocator := pm.allocator.trans hFree
    potential := ?_
    seedMarker := ?_
    boundary := ?_
    graphCache := by rw [hStored]; exact hOutCache
    rowAbove := ?_
    knownDegree := ?_
    unknownDegree := ?_
    frames := frames
    pieceSeparation := ?_
    frameSeparation := ?_
    cacheSeparation := ?_
    output := hOutput.trans pm.output
  }
  · intro u
    rw [hR,(compiler_exterior_nonactivation g α logical t v hNoAdmit).1]
    exact exterior_numeric_source_potential g logical s α ε ell length old pm hDepth t v u δ J
  · intro u
    rw [hR]
    exact exterior_numeric_source_seed_marker g logical s α ε ell length old pm hDepth t v u δ J
  · rw [hPositiveI 7 (by decide) (by have := pm.allocator; omega),pm.boundary]
    exact (compiler_exterior_nonactivation g α logical t v hNoAdmit).2.1.symm
  · intro u hu
    rw [hStored] at hu
    rcases Finset.mem_insert.mp hu with hu|hu
    · subst u
      rw [hNewBase]
      split_ifs with hv
      · exact pm.rowAbove v hv
      · exact pm.allocator
    · rw [hOldBases u hu]
      exact pm.rowAbove u hu
  · intro u hu
    rw [recursive_degree_domain_exterior] at hu
    rw [hI]
    by_cases hT : u ∈ insert v (g.neighbors v).toFinset
    · exact hDegrees u hT
    · rw [hOther u hT]
      exact pm.knownDegree u ((Finset.mem_union.mp hu).resolve_right hT)
  · intro u hu
    rw [recursive_degree_domain_exterior] at hu
    have hOld : u ∉ recursiveDegreeDomain g s logical := fun h => hu (Finset.mem_union_left _ h)
    have hT : u ∉ insert v (g.neighbors v).toFinset := fun h => hu (Finset.mem_union_right _ h)
    rw [hI,hOther u hT]
    exact pm.unknownDegree u hOld
  · intro j hj
    have hj' : j ≤ logical.top := by rw [←hNextTop]; exact hj
    change ((pm.frames j hj').pieces).Pairwise Disjoint
    exact pm.pieceSeparation j hj'
  · intro i hi j hj hij
    have hi' : i ≤ logical.top := by rw [←hNextTop]; exact hi
    have hj' : j ≤ logical.top := by rw [←hNextTop]; exact hj
    change Disjoint (pm.frames i hi').owned (pm.frames j hj').owned
    exact pm.frameSeparation i hi' j hj' hij
  · intro j hj
    have hj' : j ≤ logical.top := by rw [←hNextTop]; exact hj
    change Disjoint (pm.frames j hj').owned (cachedRowCells g out.scalar.integerMemory width next.stored)
    rw [hStored]
    exact cached_row_extension_disjoint g logical.stored width v old.scalar.integerMemory out.scalar.integerMemory
      (old.scalar.core.ptrs 20) (pm.frames j hj').owned hOldBases hNewBase (pm.cacheSeparation j hj') (pm.frames j hj').owned_below

lemma exterior_numeric_pending_memory_mass (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ) (old out : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (t : ℕ) (v : Fin n) (J : ℤ → ℤ) (steps : ℕ)
    (ex : MachineEval m g ω exteriorNumericPrefixCode old steps out)
    (hNoAdmit : relative logical t v+compilerExteriorDelta g α logical t v ≠ 3*(logical.frames t).q/8)
    (hKeys : KeysInvariant g (exteriorPush g α logical t v))
    (hCache : GraphCache g J (16*(ell+3)) (insert v logical.stored) (out.scalar.core.ptrs 20))
    (hOutCache : GraphCache g out.scalar.integerMemory (16*(ell+3)) (insert v logical.stored) (out.scalar.core.ptrs 20))
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val (old.scalar.core.ptrs 20) (g.neighbors v).length → J z=old.scalar.integerMemory z)
    (hBase : J (vertexRecordAddress (16*(ell+3)) v.val 1)=if v ∈ logical.stored then old.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 1) else old.scalar.core.ptrs 20)
    (hPayload : (out.scalar.integerMemory,out.scalar.core.mem)=
      exteriorNumericPayload g logical ell α t v (compilerExteriorDelta g α logical t v) J old.scalar.core.mem)
    (hFree : old.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hTop : out.scalar.core.ptrs 100=(logical.top : ℤ)) (hOutput : out.output=old.output) :
    (exterior_numeric_pending_memory m g ω logical s α ε ell length old out pm hDepth t v J steps ex hNoAdmit hKeys hCache hOutCache hJ hBase hPayload hFree hTop hOutput).queueMass=pm.queueMass := by
  unfold MachinePendingKeys.queueMass RecursiveMachineMemory.queueMass
  simp only [compiler_exterior_top]
  apply Finset.sum_congr rfl
  intro i hi
  have hLive : i ≤ logical.top := by have := Finset.mem_range.mp hi; omega
  simp only [dif_pos hLive]
  rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorNonactivationExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 12000000 in
lemma exterior_nonactivation_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank t : ℕ) (v : Fin n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (ht : t ≤ logical.top) (hvDomain : v ∈ parentDomain logical t)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hSelected : st.scalar.core.ptrs 112=(t : ℤ)) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hNoAdmit : relative logical t v+compilerExteriorDelta g α logical t v ≠ 3*(logical.frames t).q/8)
    (hKeys : KeysInvariant g (exteriorPush g α logical t v))
    (hMass : pm.queueMass+2*(logical.top+1)*((g.neighbors v).length+1) ≤ N) (hCap : rank < length) (hPow : N < 2^rank) :
    let width := 16*(ell+3)
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (exteriorPush g α logical t v) out,
      MachineEval m g ω exteriorPushProgramCode st steps out ∧
      steps ≤ 36*width+173+(logical.top+1)*(4*width+60)+
        (g.neighbors v).length*((logical.top+1)*(8*width+39)+4*width+31)+
        ((g.neighbors v).length+1)*((logical.top+1)*(42*rank+60*width+284)+4*width+25) ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*((g.neighbors v).length+1) ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ w : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) w.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) w.val 7)) := by
  intro width
  let next := exteriorPush g α logical t v
  have hNextTop : next.top=logical.top := compiler_exterior_top g α logical t v
  obtain ⟨u,a,J,ea,hu,jCache,jFrame,aPayload,aCache,aFree,a40,a100,a120,a121,a108,a112,a116,a114,
    aR40,aR41,aR42,aR43,aR46,aQ,aW,aO,aH,jBase⟩ :=
    exterior_numeric_prefix_exec m g ω logical s α ε ell length t v st hh pm hDepth ht hvDomain hSubset hSelected hv
  have hFree : st.scalar.core.ptrs 20 ≤ a.scalar.core.ptrs 20 := by rw [aFree]; split_ifs <;> omega
  have jCache' : GraphCache g J width (insert v logical.stored) (a.scalar.core.ptrs 20) := by rw [aFree]; exact jCache
  have aCache' : GraphCache g a.scalar.integerMemory width (insert v logical.stored) (a.scalar.core.ptrs 20) := by rw [aFree]; exact aCache
  let memA := exterior_numeric_pending_memory m g ω logical s α ε ell length st a pm hDepth t v J u ea hNoAdmit hKeys
    jCache' aCache' jFrame jBase aPayload hFree a100 aO
  have aMass : memA.queueMass=pm.queueMass := exterior_numeric_pending_memory_mass m g ω logical s α ε ell length st a pm hDepth t v J u ea hNoAdmit hKeys
    jCache' aCache' jFrame jBase aPayload hFree a100 aO
  let b := payUnit a
  let memB := memA.payUnit
  have eb : MachineEval m g ω exteriorActivationCode a 1 b := by
    have hp : a.scalar.core.ptrs 114 ≤ a.scalar.core.ptrs 0 := by
      rw [a114]
      have hn : relative logical t v+min ((logical.frames t).residual v/(5*LocalPush.deg g.graph v))
        (3*(logical.frames t).q/8-relative logical t v) ≠ 3*(logical.frames t).q/8 := hNoAdmit
      rw [if_neg hn,memA.zero]
    exact MachineEval.pointerLe aH hp (MachineEval.skip _)
  have eRaw : MachineEval m g ω exteriorNumericRawCode st (u+1) b := MachineEval.seq ea eb
  have activeD : ∀ i ≤ next.top, (next.frames i).active ⊆ parentDomain next i := by
    intro i hi
    rw [hNextTop] at hi
    have hN := (compiler_exterior_nonactivation g α logical t v hNoAdmit).2.2 i
    rw [hN.1,hN.2.1]
    exact hSubset i hi
  have extD : ∀ i ≤ next.top, (next.frames i).exterior ⊆ parentDomain next i := by
    intro i hi w hw
    exact ((hKeys i hi).1 w).mp hw |>.1
  have highD : ∀ i ≤ next.top, (next.frames i).high ⊆ parentDomain next i := by
    intro i hi w hw
    exact activeD i hi (((hKeys i hi).2 w).mp hw).1
  have extOutside : ∀ i, ∀ hi : i ≤ next.top,
      (next.frames i).exterior.image Fin.val \ (insert v (g.neighbors v).toFinset).image Fin.val ⊆ (memB.frames i hi).exteriorObject.keys := by
    intro i hi
    have hi' : i ≤ logical.top := by rw [←hNextTop]; exact hi
    change (next.frames i).exterior.image Fin.val \ (insert v (g.neighbors v).toFinset).image Fin.val ⊆ (pm.frames i hi').exteriorObject.keys
    exact (exterior_transition_queue_cover g α logical t v i _ _ (pm.frames i hi').exteriorCover (pm.frames i hi').highCover).1
  have highOutside : ∀ i, ∀ hi : i ≤ next.top,
      (next.frames i).high.image Fin.val \ (insert v (g.neighbors v).toFinset).image Fin.val ⊆ (memB.frames i hi).highObject.keys := by
    intro i hi
    have hi' : i ≤ logical.top := by rw [←hNextTop]; exact hi
    change (next.frames i).high.image Fin.val \ (insert v (g.neighbors v).toFinset).image Fin.val ⊆ (pm.frames i hi').highObject.keys
    exact (exterior_transition_queue_cover g α logical t v i _ _ (pm.frames i hi').exteriorCover (pm.frames i hi').highCover).2
  have boolOutside : ∀ i ≤ next.top,
      HighBooleanRecords b.scalar.integerMemory b.scalar.core.mem width (16*(i+1)) (next.frames i).theta
        (parentDomain next i \ insert v (g.neighbors v).toFinset) := by
    intro i hi
    have hi' : i ≤ logical.top := by rw [←hNextTop]; exact hi
    apply exterior_transition_boolean_outside g α logical t v i width length st b _ (pm.frames i hi')
      (compiler_exterior_scalar_parameters g α logical t v i).2 (memB.frames i hi).activeFlags (memB.frames i hi).residual
    · intro w hw
      change a.scalar.integerMemory _=_
      rw [show a.scalar.integerMemory=(exteriorNumericPayload g logical ell α t v (compilerExteriorDelta g α logical t v) J st.scalar.core.mem).1 from congrArg Prod.fst aPayload]
      exact exterior_numeric_other_degrees g logical ell α t v _ J st.scalar.integerMemory st.scalar.core.mem _
        (by have := pm.allocator; omega) jFrame w hw
    · intro w hw
      change a.scalar.core.mem _=_
      rw [show a.scalar.core.mem=(exteriorNumericPayload g logical ell α t v (compilerExteriorDelta g α logical t v) J st.scalar.core.mem).2 from congrArg Prod.snd aPayload]
      exact exterior_numeric_payload_real_field g logical ell hDepth α t v w _ J _ (16*(i+1)+4) (by omega) (by omega) (by intros; omega)
  have budget : memB.queueMass+2*(next.top+1)*((g.neighbors v).length+1) ≤ N := by
    change memA.queueMass+2*(next.top+1)*((g.neighbors v).length+1) ≤ N
    rw [aMass,hNextTop]
    exact hMass
  obtain ⟨r,out,memory,er,hr,rMass,r40,rQ,rW,rO,rH,rMarks⟩ := pending_touched_refresh_exec m g ω s α ε ell length N rank next
    b aH memB (by rw [hNextTop]; exact hDepth) activeD extD highD v
    (by rw [compiler_exterior_stored]; exact Finset.mem_insert_self _ _) a116 a40 a120 budget hCap hPow extOutside highOutside boolOutside
  have ex : MachineEval m g ω exteriorPushProgramCode st ((u+1)+r) out := MachineEval.seq eRaw er
  refine ⟨_,out,memory,ex,?_,?_,r40,ex.unit_work exteriorPushProgramCode_wellFormed (by decide) hh,rO.trans aO,rH,?_⟩
  · rw [hNextTop] at hr
    dsimp only [width]
    omega
  · change memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*((g.neighbors v).length+1)
    change memory.queueMass ≤ memA.queueMass+2*(next.top+1)*((g.neighbors v).length+1) at rMass
    simpa only [aMass,hNextTop] using rMass

  · intro w
    rw [rMarks w]
    change a.scalar.integerMemory _=_
    rw [show a.scalar.integerMemory=(exteriorNumericPayload g logical ell α t v (compilerExteriorDelta g α logical t v) J st.scalar.core.mem).1 from congrArg Prod.fst aPayload]
    exact exterior_numeric_integer_field_frame g logical ell α t v w _ J st.scalar.integerMemory st.scalar.core.mem _ jFrame
      (by have := pm.allocator; omega) 7 (by decide) (by omega)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ActivationBoundaryMemory
set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
lemma activation_boundary_memory_other {n : ℕ} (g : InputGraph n) (source : Fin n) (active : Finset (Fin n))
    (boundary level : ℕ) (I : ℤ → ℤ) (z : ℤ) (hz : z ≠ 7) :
    activationBoundaryMemory g source active boundary level I z=I z := by
  unfold activationBoundaryMemory
  split_ifs <;> simp only [Function.update_of_ne hz]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorActivationIntegerRecords

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma exterior_activation_integer_vertex {n : ℕ} (g : InputGraph n) (source : Fin n) (rootActive : Finset (Fin n))
    (boundary ell level top : ℕ) (free : ℤ) (I : ℤ → ℤ) (u field : ℕ)
    (hl : level ≤ ell) (hFree : 0 ≤ free) (hf : field < 16*(ell+3)) :
    exteriorActivationIntegerMemory g source rootActive boundary level top (16*(ell+3)) free I
      (vertexRecordAddress (16*(ell+3)) u field)=
      if level<top ∧ u=source.val ∧ 16*(level+1)+18 ≤ field ∧ field ≤ 16*(level+1)+22 then 0
      else if u=source.val ∧ field=16*(level+1)+2 then 1
      else I (vertexRecordAddress (16*(ell+3)) u field) := by
  classical
  let width := 16*(ell+3)
  let B := activationBoundaryMemory g source rootActive boundary level I
  let A := frameListInsertMemory B free source.val level 1 3 2 width 2 ((g.neighbors source).length : ℤ)
  have hBase : A (vertexRecordAddress width u field)=if u=source.val ∧ field=16*(level+1)+2 then 1 else I (vertexRecordAddress width u field) := by
    dsimp only [A]
    by_cases h : u=source.val ∧ field=16*(level+1)+2
    · obtain ⟨rfl,rfl⟩ := h
      simpa only [and_self,if_true] using frame_list_insert_flag B free source.val level 1 3 2 width 2 ((g.neighbors source).length : ℤ)
    · rw [if_neg h]
      by_cases hField : field=16*(level+1)+2
      · have hOther : u ≠ source.val := by tauto
        rw [frame_list_insert_other_vertex B free hFree source.val u level 1 3 2 width 2 field (by dsimp [width]; omega) hf hOther]
        exact activation_boundary_memory_other g source rootActive boundary level I _ (by have := vertexRecordAddress_negative width u field; omega)
      · rw [frame_list_insert_field_frame B free hFree source.val u level 1 3 2 width 2 field (by dsimp [width]; omega) hf hField]
        exact activation_boundary_memory_other g source rootActive boundary level I _ (by have := vertexRecordAddress_negative width u field; omega)
  change (if level<top then clearLevelVertexFlagsMemory A width source.val (16*(level+1)+16) [2,3,4,5,6] else A) _=_
  by_cases hc : level<top
  · rw [if_pos hc]
    by_cases hHit : u=source.val ∧ 16*(level+1)+18 ≤ field ∧ field ≤ 16*(level+1)+22
    · obtain ⟨hu,hLo,hHi⟩ := hHit
      have hPoint : field=16*(level+1)+16+(field-(16*(level+1)+16)) := by omega
      have hOffset : field-(16*(level+1)+16) ∈ ([2,3,4,5,6] : List ℕ) := by
        simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
        omega
      have hClear : clearLevelVertexFlagsMemory A width source.val (16*(level+1)+16) [2,3,4,5,6]
          (vertexRecordAddress width u field)=0 := by
        rw [hu,hPoint]
        exact clear_level_flags_at A width source.val (16*(level+1)+16) [2,3,4,5,6]
          (by intro k hk; simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk; dsimp [width]; omega)
          (field-(16*(level+1)+16)) hOffset
      rw [hClear,if_pos ⟨hc,hu,hLo,hHi⟩]
    · rw [clear_level_flags_frame]
      · rw [hBase]
        simp only [hc,true_and,if_neg hHit]
        rfl
      · intro k hk he
        have hkRange : 2 ≤ k ∧ k ≤ 6 := by
          simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk
          omega
        have he' := vertexRecordAddress_injective width u source.val field (16*(level+1)+16+k) hf (by dsimp [width]; omega) he
        exact hHit ⟨he'.1,by omega,by omega⟩
  · rw [if_neg hc,hBase]
    simp only [hc,false_and,if_false]
    rfl

lemma exterior_activation_integer_old_heap {n : ℕ} (g : InputGraph n) (source : Fin n) (rootActive : Finset (Fin n))
    (boundary ell level top : ℕ) (free z : ℤ) (I : ℤ → ℤ)
    (hl : level ≤ ell) (hz : 128+32*((ell+2 : ℕ) : ℤ) ≤ z) (hBelow : z < free) :
    exteriorActivationIntegerMemory g source rootActive boundary level top (16*(ell+3)) free I z=I z := by
  unfold exteriorActivationIntegerMemory
  split_ifs
  · rw [fresh_vertex_integer_positive _ (16*(ell+3)) source.val (16*(level+1)) z (by omega)]
    rw [frame_list_insert_old_heap _ free source.val level 1 3 2 (16*(ell+3)) 2 _ z (by omega) hBelow (by decide) (by decide) (by decide)]
    exact activation_boundary_memory_other g source rootActive boundary level I z (by omega)
  · rw [frame_list_insert_old_heap _ free source.val level 1 3 2 (16*(ell+3)) 2 _ z (by omega) hBelow (by decide) (by decide) (by decide)]
    exact activation_boundary_memory_other g source rootActive boundary level I z (by omega)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorActivationScopedFlags

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma exterior_activation_scoped_flag {n : ℕ} (g : InputGraph n) (source : Fin n) (rootActive : Finset (Fin n))
    (boundary ell level top j : ℕ) (free : ℤ) (I : ℤ → ℤ) (u offset : ℕ)
    (hl : level ≤ ell) (hj : j ≤ ell) (hFree : 0 ≤ free) (hOffset : 2 ≤ offset ∧ offset ≤ 6) :
    exteriorActivationIntegerMemory g source rootActive boundary level top (16*(ell+3)) free I
      (vertexRecordAddress (16*(ell+3)) u (16*(j+1)+offset))=
      if level<top ∧ u=source.val ∧ j=level+1 then 0
      else if u=source.val ∧ j=level ∧ offset=2 then 1
      else I (vertexRecordAddress (16*(ell+3)) u (16*(j+1)+offset)) := by
  rw [exterior_activation_integer_vertex g source rootActive boundary ell level top free I u (16*(j+1)+offset) hl hFree (by omega)]
  have hRange : (16*(level+1)+18 ≤ 16*(j+1)+offset ∧ 16*(j+1)+offset ≤ 16*(level+1)+22) ↔ j=level+1 := by omega
  have hSelf : 16*(j+1)+offset=16*(level+1)+2 ↔ j=level ∧ offset=2 := by omega
  simp only [←and_assoc,hRange,hSelf,and_assoc]

lemma exterior_activation_global_field {n : ℕ} (g : InputGraph n) (source : Fin n) (rootActive : Finset (Fin n))
    (boundary ell level top : ℕ) (free : ℤ) (I : ℤ → ℤ) (u field : ℕ)
    (hl : level ≤ ell) (hFree : 0 ≤ free) (hf : field < 16) :
    exteriorActivationIntegerMemory g source rootActive boundary level top (16*(ell+3)) free I
      (vertexRecordAddress (16*(ell+3)) u field)=I (vertexRecordAddress (16*(ell+3)) u field) := by
  rw [exterior_activation_integer_vertex g source rootActive boundary ell level top free I u field hl hFree (by omega)]
  have hLo : ¬16*(level+1)+18 ≤ field := by omega
  have hEq : field ≠ 16*(level+1)+2 := by omega
  simp only [hLo,hEq,false_and,and_false,if_false]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerAdmissionAccounting

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_admit_budget {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) (i : ℕ) :
    ((admitStage g st t v).frames i).W=(st.frames i).W+
      (if i=t ∧ (st.frames i).openBudget=true then ((t+3 : ℕ) : ℝ)*(st.frames t).q*LocalPush.deg g.graph v/2 else 0) := by
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
    simp [b,hc,a,changeFrame,hit,hic]

lemma compiler_admit_boundary {n : ℕ} (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    (admitStage g st t v).boundaryEdges=if t=0 then
      st.boundaryEdges+(g.neighbors v).length-2*((g.neighbors v).filter (fun w => w ∈ (st.frames t).active)).length
      else st.boundaryEdges := by
  unfold admitStage
  split_ifs <;> rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CompilerExteriorAdmission

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma compiler_exterior_admission {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (ha : relative st t v+compilerExteriorDelta g α st t v=3*(st.frames t).q/8) :
    let base := rawExterior g α st t v (compilerExteriorDelta g α st t v)
    let admitted := admitStage g base t v
    (exteriorPush g α st t v).x=admitted.x ∧
      (exteriorPush g α st t v).boundaryEdges=admitted.boundaryEdges ∧
      (∀ i, parentDomain (exteriorPush g α st t v) i=parentDomain admitted i ∧
        ((exteriorPush g α st t v).frames i).active=(admitted.frames i).active ∧
        ((exteriorPush g α st t v).frames i).reference=(admitted.frames i).reference ∧
        ((exteriorPush g α st t v).frames i).residual=(admitted.frames i).residual ∧
        ((exteriorPush g α st t v).frames i).W=(admitted.frames i).W) := by
  classical
  dsimp only [compilerExteriorDelta] at ha ⊢
  rw [compiler_exterior_stages]
  change (debit (refreshKeys g (if _ then _ else _) _) _ _).x=_ ∧ _
  rw [if_pos ha]
  refine ⟨rfl,rfl,?_⟩
  intro i
  change parentDomain (refreshKeys g _ _) i=_ ∧ _
  rw [compiler_refresh_domain]
  change _ ∧ ((refreshKeys g _ _).frames i).active=_ ∧ ((refreshKeys g _ _).frames i).reference=_ ∧
    ((refreshKeys g _ _).frames i).residual=_ ∧ ((refreshKeys g _ _).frames i).W=_
  rw [(compiler_refresh_numeric g _ _ i).2.2.2.1,(compiler_refresh_numeric g _ _ i).2.2.1,
    (compiler_refresh_numeric g _ _ i).1,(compiler_refresh_numeric g _ _ i).2.1]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

lemma compiler_exterior_admission_domain {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (ha : relative st t v+compilerExteriorDelta g α st t v=3*(st.frames t).q/8) (i : ℕ) (w : Fin n) :
    w ∈ parentDomain (exteriorPush g α st t v) i ↔ w ∈ parentDomain st i ∨ i=t+1 ∧ w=v := by
  rw [((compiler_exterior_admission g α st t v ha).2.2 i).1,compiler_admit_domain,compiler_raw_domain]

lemma compiler_exterior_admission_active {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (ha : relative st t v+compilerExteriorDelta g α st t v=3*(st.frames t).q/8) (i : ℕ) :
    ((exteriorPush g α st t v).frames i).active=if i=t then insert v (st.frames i).active else (st.frames i).active := by
  rw [((compiler_exterior_admission g α st t v ha).2.2 i).2.1,
    (compiler_admit_stage_fields g _ t v).2.2.2.2.2.1 i]
  simp only [compiler_raw_active]

lemma compiler_exterior_admission_active_domain {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (ha : relative st t v+compilerExteriorDelta g α st t v=3*(st.frames t).q/8)
    (hv : v ∈ parentDomain st t)
    (hSubset : ∀ i ≤ st.top, (st.frames i).active ⊆ parentDomain st i) :
    ∀ i ≤ (exteriorPush g α st t v).top,
      ((exteriorPush g α st t v).frames i).active ⊆ parentDomain (exteriorPush g α st t v) i := by
  intro i hi w hw
  rw [compiler_exterior_top] at hi
  apply (compiler_exterior_admission_domain g α st t v ha i w).mpr
  apply Or.inl
  rw [compiler_exterior_admission_active g α st t v ha i] at hw
  by_cases hit : i=t
  · subst i
    rw [if_pos rfl] at hw
    rcases Finset.mem_insert.mp hw with rfl|hw
    · exact hv
    · exact hSubset t hi hw
  · rw [if_neg hit] at hw
    exact hSubset i hi hw

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorAdmittedActiveFlags

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def exteriorAdmittedIntegerPayload {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell boundary : ℕ)
    (α : ℝ) (t : ℕ) (v : Fin n) (free : ℤ) (J : ℤ → ℤ) (R : ℤ → ℝ) : ℤ → ℤ :=
  exteriorActivationIntegerMemory g v (logical.frames 0).active boundary t logical.top (16*(ell+3)) free
    (exteriorNumericPayload g logical ell α t v (compilerExteriorDelta g α logical t v) J R).1

lemma exterior_admitted_active_flags {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length boundary : ℕ) (old : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (t j : ℕ) (ht : t ≤ logical.top) (hj : j ≤ logical.top) (v u : Fin n) (J : ℤ → ℤ) (free : ℤ)
    (hFree : 0 ≤ free)
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val (old.scalar.core.ptrs 20) (g.neighbors v).length → J z=old.scalar.integerMemory z)
    (hv : v ∉ (logical.frames t).active)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8)
    (hu : u ∈ parentDomain (exteriorPush g α logical t v) j) :
    exteriorAdmittedIntegerPayload g logical ell boundary α t v free J old.scalar.core.mem
      (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+2))=
      if u ∈ ((exteriorPush g α logical t v).frames j).active then 1 else 0 := by
  classical
  unfold exteriorAdmittedIntegerPayload
  rw [exterior_activation_scoped_flag g v (logical.frames 0).active boundary ell t logical.top j free _ u.val 2
    (by omega) (by omega) hFree (by omega)]
  simp only [show u.val=v.val ↔ u=v from Fin.val_inj,and_true]
  rw [exterior_numeric_integer_field_frame g logical ell α t v u _ J old.scalar.integerMemory old.scalar.core.mem _ hJ
    (by have := pm.allocator; omega) (16*(j+1)+2) (by omega) (by omega),compiler_exterior_admission_active g α logical t v ha j]
  by_cases hChild : t<logical.top ∧ u=v ∧ j=t+1
  · obtain ⟨hc,huv,hjv⟩ := hChild
    subst u
    subst j
    have hNot : v ∉ (logical.frames (t+1)).active := by
      intro h
      have hm := hSubset (t+1) hj h
      have hd : parentDomain logical (t+1)=(logical.frames t).active := by simp [parentDomain]
      rw [hd] at hm
      exact hv hm
    simp [hc,hNot]
  · rw [if_neg hChild]
    have hOld : u ∈ parentDomain logical j := by
      rcases (compiler_exterior_admission_domain g α logical t v ha j u).mp hu with hd|⟨hjt,huv⟩
      · exact hd
      · exact (hChild ⟨by omega,huv,hjt⟩).elim
    rw [(pm.frames j hj).activeFlags u hOld]
    by_cases hjt : j=t
    · subst j
      by_cases he : u=v <;> simp [Finset.mem_insert,he]
    · simp [hjt]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorAdmittedOtherFlags

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma exterior_admitted_other_scoped_flag {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (ell boundary : ℕ) (α : ℝ) (t j : ℕ) (v u : Fin n) (J I : ℤ → ℤ) (R : ℤ → ℝ) (free oldFree : ℤ)
    (ht : t ≤ ell) (hj : j ≤ ell) (hFree : 0 ≤ free) (hOldFree : 0 ≤ oldFree)
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val oldFree (g.neighbors v).length → J z=I z)
    (offset : ℕ) (hOffset : 3 ≤ offset ∧ offset ≤ 6) :
    exteriorAdmittedIntegerPayload g logical ell boundary α t v free J R
      (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+offset))=
      if t<logical.top ∧ u=v ∧ j=t+1 then 0
      else I (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+offset)) := by
  unfold exteriorAdmittedIntegerPayload
  rw [exterior_activation_scoped_flag g v (logical.frames 0).active boundary ell t logical.top j free _ u.val offset
    ht hj hFree (by omega)]
  simp only [show u.val=v.val ↔ u=v from Fin.val_inj,show offset ≠ 2 by omega,and_false,if_false]
  rw [exterior_numeric_integer_field_frame g logical ell α t v u _ J I R oldFree hJ hOldFree (16*(j+1)+offset) (by omega) (by omega)]

lemma exterior_admitted_queued_flags {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (ell boundary : ℕ) (α : ℝ) (t j : ℕ) (v : Fin n) (J I : ℤ → ℤ) (R : ℤ → ℝ) (free oldFree : ℤ)
    (hDepth : logical.top ≤ ell) (ht : t ≤ logical.top) (hj : j ≤ logical.top) (hFree : 0 ≤ free) (hOldFree : 0 ≤ oldFree)
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val oldFree (g.neighbors v).length → J z=I z)
    (offset : ℕ) (hOffset : 3 ≤ offset ∧ offset ≤ 6) (queued : Finset ℕ)
    (hQueuedDomain : queued ⊆ (parentDomain logical j).image Fin.val)
    (hFlags : QueuedFlags I (16*(ell+3)) (16*(j+1)+offset) (parentDomain logical j) queued)
    (hv : v ∉ (logical.frames t).active)
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8) :
    QueuedFlags (exteriorAdmittedIntegerPayload g logical ell boundary α t v free J R)
      (16*(ell+3)) (16*(j+1)+offset) (parentDomain (exteriorPush g α logical t v) j) queued := by
  classical
  intro u hu
  rw [exterior_admitted_other_scoped_flag g logical ell boundary α t j v u J I R free oldFree
    (by omega) (by omega) hFree hOldFree hJ offset hOffset]
  by_cases hChild : t<logical.top ∧ u=v ∧ j=t+1
  · obtain ⟨hc,huv,hjv⟩ := hChild
    subst u
    subst j
    have hNot : v.val ∉ queued := by
      intro h
      have hm : v ∈ parentDomain logical (t+1) := (compiler_fin_val_image _ v).mp (hQueuedDomain h)
      have hd : parentDomain logical (t+1)=(logical.frames t).active := by simp [parentDomain]
      exact hv (hd ▸ hm)
    simp only [hc,and_self,true_and,if_true,if_neg hNot]
  · rw [if_neg hChild]
    apply hFlags
    rcases (compiler_exterior_admission_domain g α logical t v ha j u).mp hu with hD|⟨hjv,huv⟩
    · exact hD
    · exact (hChild ⟨by omega,huv,hjv⟩).elim

lemma exterior_admitted_cache_flags {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length boundary : ℕ) (old : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (t j : ℕ) (ht : t ≤ logical.top) (hj : j ≤ logical.top) (v : Fin n) (J : ℤ → ℤ) (free : ℤ)
    (hFree : 0 ≤ free)
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val (old.scalar.core.ptrs 20) (g.neighbors v).length → J z=old.scalar.integerMemory z)
    (hv : v ∉ (logical.frames t).active) (hCacheDomain : (logical.frames j).cache ⊆ parentDomain logical j)
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8) :
    ∀ u ∈ parentDomain (exteriorPush g α logical t v) j,
      exteriorAdmittedIntegerPayload g logical ell boundary α t v free J old.scalar.core.mem
        (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+4))=
        if u ∈ ((exteriorPush g α logical t v).frames j).cache then 1 else 0 := by
  have hOldFlags : QueuedFlags old.scalar.integerMemory (16*(ell+3)) (16*(j+1)+4) (parentDomain logical j)
      ((logical.frames j).cache.image Fin.val) := by
    intro u hu
    simpa only [compiler_fin_val_image] using (pm.frames j hj).cacheFlags u hu
  have hf := exterior_admitted_queued_flags g logical ell boundary α t j v J old.scalar.integerMemory old.scalar.core.mem free
    (old.scalar.core.ptrs 20) hDepth ht hj hFree (by have := pm.allocator; omega) hJ 4 (by omega)
    ((logical.frames j).cache.image Fin.val) (Finset.image_subset_image hCacheDomain) hOldFlags hv ha
  have hc : ((exteriorPush g α logical t v).frames j).cache=(logical.frames j).cache :=
    congrArg (fun x => x.2.2.2.2.2.2.2.2.2) (compiler_exterior_static g α logical t v j)
  intro u hu
  rw [hc]
  simpa only [compiler_fin_val_image] using hf u hu

lemma exterior_admitted_virtual_excluded {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length boundary : ℕ) (old : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (t j : ℕ) (ht : t ≤ logical.top) (hj : j ≤ logical.top) (v : Fin n) (J : ℤ → ℤ) (free : ℤ)
    (hFree : 0 ≤ free)
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val (old.scalar.core.ptrs 20) (g.neighbors v).length → J z=old.scalar.integerMemory z)
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8) :
    ∀ u ∈ parentDomain (exteriorPush g α logical t v) j,
      exteriorAdmittedIntegerPayload g logical ell boundary α t v free J old.scalar.core.mem
        (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+5))=0 := by
  intro u hu
  rw [exterior_admitted_other_scoped_flag g logical ell boundary α t j v u J old.scalar.integerMemory old.scalar.core.mem free
    (old.scalar.core.ptrs 20) (by omega) (by omega) hFree (by have := pm.allocator; omega) hJ 5 (by omega)]
  split_ifs with hChild
  · rfl
  · apply (pm.frames j hj).virtualExcluded
    rcases (compiler_exterior_admission_domain g α logical t v ha j u).mp hu with hd|⟨hjv,huv⟩
    · exact hd
    · exact (hChild ⟨by omega,huv,hjv⟩).elim

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorActivationRealRecords

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma compiler_vertex_address_eq (width u v a b : ℕ) (ha : a < width) (hb : b < width) :
    vertexRecordAddress width u a=vertexRecordAddress width v b ↔ u=v ∧ a=b := by
  constructor
  · exact vertexRecordAddress_injective width u v a b ha hb
  · rintro ⟨rfl,rfl⟩; rfl

lemma activation_scalars_vertex (R : ℤ → ℝ) (width source level u field : ℕ) (half : ℝ) (opened : Bool)
    (hw : 16*(level+1)+1 < width) (hf : field < width) :
    activationScalarsMemory R width source level half opened (vertexRecordAddress width u field)=
      R (vertexRecordAddress width u field)+(if u=source ∧ field=16*(level+1)+1 then half else 0) := by
  have hn : vertexRecordAddress width u field ≠ levelHeaderAddress level 4 := by
    have := vertexRecordAddress_negative width u field
    have := levelHeaderAddress_positive level 4
    omega
  unfold activationScalarsMemory
  rw [Function.update_of_ne hn]
  by_cases h : u=source ∧ field=16*(level+1)+1
  · obtain ⟨rfl,rfl⟩ := h
    simp
  · rw [Function.update_of_ne ((compiler_vertex_address_eq width u source field (16*(level+1)+1) hf hw).not.mpr h),if_neg h,add_zero]

lemma exterior_activation_real_vertex (R : ℤ → ℝ) (width source level top u field : ℕ)
    (half : ℝ) (opened : Bool) (hw : 16*(level+1)+22 < width) (hf : field < width) :
    exteriorActivationRealMemory R source level top width half opened (vertexRecordAddress width u field)=
      if level<top ∧ u=source ∧ field=16*(level+1)+16 then R (vertexRecordAddress width source 0)
      else if level<top ∧ u=source ∧ field=16*(level+1)+17 then R (vertexRecordAddress width source (16*(level+1)+1))+half
      else if level<top ∧ u=source ∧ field=16*(level+1)+20 then 0
      else R (vertexRecordAddress width u field)+(if u=source ∧ field=16*(level+1)+1 then half else 0) := by
  unfold exteriorActivationRealMemory
  by_cases hc : level<top
  · rw [if_pos hc]
    unfold freshVertexRealMemory
    simp only [Function.update_apply,
      compiler_vertex_address_eq width u source field (16*(level+1)+16) hf (by omega),
      compiler_vertex_address_eq width u source field (16*(level+1)+17) hf (by omega),
      compiler_vertex_address_eq width u source field (16*(level+1)+20) hf (by omega)]
    rw [activation_scalars_vertex R width source level source 0 half opened (by omega) (by omega),
      activation_scalars_vertex R width source level source (16*(level+1)+1) half opened (by omega) (by omega),
      activation_scalars_vertex R width source level u field half opened (by omega) hf]
    by_cases h16 : u=source ∧ field=16*(level+1)+16
    · obtain ⟨rfl,rfl⟩ := h16
      simp [hc]
    · by_cases h17 : u=source ∧ field=16*(level+1)+17
      · obtain ⟨rfl,rfl⟩ := h17
        simp [hc]
      · by_cases h20 : u=source ∧ field=16*(level+1)+20
        · obtain ⟨rfl,rfl⟩ := h20
          simp [hc]
        · simp [hc,h16,h17,h20]
  · rw [if_neg hc,activation_scalars_vertex R width source level u field half opened (by omega) hf]
    simp [hc]

lemma exterior_activation_real_header (R : ℤ → ℝ) (width source level top j slot : ℕ)
    (half : ℝ) (opened : Bool) (hs : slot < 32) :
    exteriorActivationRealMemory R source level top width half opened (levelHeaderAddress j slot)=
      R (levelHeaderAddress j slot)+(if j=level ∧ slot=4 then (if opened then ((level+3 : ℕ) : ℝ)*half else 0) else 0) := by
  have hz : 0 ≤ levelHeaderAddress j slot := by have := levelHeaderAddress_positive j slot; omega
  have hn : levelHeaderAddress j slot ≠ vertexRecordAddress width source (16*(level+1)+1) := by
    have := vertexRecordAddress_negative width source (16*(level+1)+1)
    omega
  unfold exteriorActivationRealMemory
  by_cases hc : level<top
  · rw [if_pos hc,fresh_vertex_real_positive _ width source (16*(level+1)) _ hz]
    unfold activationScalarsMemory
    by_cases he : j=level ∧ slot=4
    · obtain ⟨rfl,rfl⟩ := he
      simp
    · have hnH : levelHeaderAddress j slot ≠ levelHeaderAddress level 4 := by
        intro h
        exact he (levelHeaderAddress_injective j level slot 4 hs (by decide) h)
      rw [Function.update_of_ne hnH,Function.update_of_ne hn,if_neg he,add_zero]
  · rw [if_neg hc]
    unfold activationScalarsMemory
    by_cases he : j=level ∧ slot=4
    · obtain ⟨rfl,rfl⟩ := he
      simp
    · have hnH : levelHeaderAddress j slot ≠ levelHeaderAddress level 4 := by
        intro h
        exact he (levelHeaderAddress_injective j level slot 4 hs (by decide) h)
      rw [Function.update_of_ne hnH,Function.update_of_ne hn,if_neg he,add_zero]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorActivationSourceRecords

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma exterior_activation_reference_readback (R : ℤ → ℝ) (ell source level top j : ℕ)
    (half : ℝ) (opened : Bool) (hl : level ≤ ell) (hj : j ≤ ell) (u : ℕ) :
    exteriorActivationRealMemory R source level top (16*(ell+3)) half opened
      (vertexRecordAddress (16*(ell+3)) u (16*(j+1)))=
      if level<top ∧ u=source ∧ j=level+1 then R (vertexRecordAddress (16*(ell+3)) source 0)
      else R (vertexRecordAddress (16*(ell+3)) u (16*(j+1))) := by
  rw [exterior_activation_real_vertex R (16*(ell+3)) source level top u (16*(j+1)) half opened (by omega) (by omega)]
  have h16 : 16*(j+1)=16*(level+1)+16 ↔ j=level+1 := by omega
  have h17 : 16*(j+1) ≠ 16*(level+1)+17 := by omega
  have h20 : 16*(j+1) ≠ 16*(level+1)+20 := by omega
  have h1 : 16*(j+1) ≠ 16*(level+1)+1 := by omega
  simp only [h16,h17,h20,h1,and_false,if_false,add_zero]

lemma exterior_activation_residual_readback (R : ℤ → ℝ) (ell source level top j : ℕ)
    (half : ℝ) (opened : Bool) (hl : level ≤ ell) (hj : j ≤ ell) (u : ℕ) :
    exteriorActivationRealMemory R source level top (16*(ell+3)) half opened
      (vertexRecordAddress (16*(ell+3)) u (16*(j+1)+1))=
      if level<top ∧ u=source ∧ j=level+1 then
        R (vertexRecordAddress (16*(ell+3)) source (16*(level+1)+1))+half
      else R (vertexRecordAddress (16*(ell+3)) u (16*(j+1)+1))+(if u=source ∧ j=level then half else 0) := by
  rw [exterior_activation_real_vertex R (16*(ell+3)) source level top u (16*(j+1)+1) half opened (by omega) (by omega)]
  have h16 : 16*(j+1)+1 ≠ 16*(level+1)+16 := by omega
  have h17 : 16*(j+1)+1=16*(level+1)+17 ↔ j=level+1 := by omega
  have h20 : 16*(j+1)+1 ≠ 16*(level+1)+20 := by omega
  have h1 : 16*(j+1)+1=16*(level+1)+1 ↔ j=level := by omega
  simp only [h16,h17,h20,h1,and_false,if_false]

lemma exterior_activation_source_reference {n : ℕ} (g : InputGraph n) (st : RecursiveState n)
    (R : ℤ → ℝ) (ell level j : ℕ) (v u : Fin n)
    (hl : level ≤ ell) (hj : j ≤ ell) (hLive : j ≤ st.top)
    (hPotential : R (vertexRecordAddress (16*(ell+3)) v.val 0)=st.x v)
    (hReference : ∀ u ∈ parentDomain st j,
      R (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)))=(st.frames j).reference u)
    (hu : u ∈ parentDomain (admitStage g st level v) j) :
    exteriorActivationRealMemory R v.val level st.top (16*(ell+3))
      ((st.frames level).q*LocalPush.deg g.graph v/2) (st.frames level).openBudget
      (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)))=
        ((admitStage g st level v).frames j).reference u := by
  rw [exterior_activation_reference_readback R ell v.val level st.top j _ _ hl hj u.val,
    (compiler_admit_stage_fields g st level v).2.2.2.2.2.2.1]
  have hVal : u.val=v.val ↔ u=v := Fin.val_inj
  simp only [hVal]
  by_cases h : level<st.top ∧ j=level+1 ∧ u=v
  · obtain ⟨hc,rfl,rfl⟩ := h
    simp [hc,hPotential]
  · have h' : ¬(level<st.top ∧ u=v ∧ j=level+1) := by tauto
    rw [if_neg h',if_neg h]
    have hD := (compiler_admit_domain g st level j v u).mp hu
    rcases hD with hD|hD
    · exact hReference u hD
    · obtain ⟨hjv,huv⟩ := hD
      by_cases hc : level<st.top
      · exact (h ⟨hc,hjv,huv⟩).elim
      · omega


lemma exterior_activation_source_residual {n : ℕ} (g : InputGraph n) (st : RecursiveState n)
    (R : ℤ → ℝ) (ell level j : ℕ) (v u : Fin n)
    (hl : level ≤ ell) (hj : j ≤ ell) (hLive : j ≤ st.top) (hLevel : level ≤ st.top)
    (hv : v ∈ parentDomain st level)
    (hResidual : ∀ i ≤ st.top, ∀ u ∈ parentDomain st i,
      R (vertexRecordAddress (16*(ell+3)) u.val (16*(i+1)+1))=(st.frames i).residual u)
    (hu : u ∈ parentDomain (admitStage g st level v) j) :
    exteriorActivationRealMemory R v.val level st.top (16*(ell+3))
      ((st.frames level).q*LocalPush.deg g.graph v/2) (st.frames level).openBudget
      (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))=
        ((admitStage g st level v).frames j).residual u := by
  rw [exterior_activation_residual_readback R ell v.val level st.top j _ _ hl hj u.val,
    (compiler_admit_stage_fields g st level v).2.2.2.2.2.2.2]
  have hVal : u.val=v.val ↔ u=v := Fin.val_inj
  simp only [hVal]
  by_cases h : level<st.top ∧ j=level+1 ∧ u=v
  · obtain ⟨hc,hjv,huv⟩ := h
    subst j
    subst u
    simp only [hc,true_and,and_self,if_true]
    exact congrArg (fun r => r+(st.frames level).q*LocalPush.deg g.graph v/2) (hResidual level hLevel v hv)
  · have h' : ¬(level<st.top ∧ u=v ∧ j=level+1) := by tauto
    rw [if_neg h',if_neg h]
    have hD : u ∈ parentDomain st j := by
      rcases (compiler_admit_domain g st level j v u).mp hu with hD|⟨hjv,huv⟩
      · exact hD
      · exact (h ⟨by omega,hjv,huv⟩).elim
    rw [hResidual j hLive u hD]
    simp only [and_comm]

lemma exterior_activation_potential_frame (R : ℤ → ℝ) (ell source level top u : ℕ)
    (half : ℝ) (opened : Bool) (hl : level ≤ ell) :
    exteriorActivationRealMemory R source level top (16*(ell+3)) half opened
      (vertexRecordAddress (16*(ell+3)) u 0)=R (vertexRecordAddress (16*(ell+3)) u 0) := by
  rw [exterior_activation_real_vertex R (16*(ell+3)) source level top u 0 half opened (by omega) (by omega)]
  simp only [show (0:ℕ) ≠ 16*(level+1)+16 by omega,
    show (0:ℕ) ≠ 16*(level+1)+17 by omega,show (0:ℕ) ≠ 16*(level+1)+20 by omega,
    show (0:ℕ) ≠ 16*(level+1)+1 by omega,and_false,if_false,add_zero]

lemma exterior_activation_seed_marker_frame (R : ℤ → ℝ) (ell source level top u : ℕ)
    (half : ℝ) (opened : Bool) (hl : level ≤ ell) :
    exteriorActivationRealMemory R source level top (16*(ell+3)) half opened
      (vertexRecordAddress (16*(ell+3)) u 2)=R (vertexRecordAddress (16*(ell+3)) u 2) := by
  rw [exterior_activation_real_vertex R (16*(ell+3)) source level top u 2 half opened (by omega) (by omega)]
  simp only [show (2:ℕ) ≠ 16*(level+1)+16 by omega,
    show (2:ℕ) ≠ 16*(level+1)+17 by omega,show (2:ℕ) ≠ 16*(level+1)+20 by omega,
    show (2:ℕ) ≠ 16*(level+1)+1 by omega,and_false,if_false,add_zero]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorAdmittedRealPayload

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def exteriorAdmittedRealPayload {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (t : ℕ) (v : Fin n) (J : ℤ → ℤ) (R : ℤ → ℝ) : ℤ → ℝ :=
  exteriorActivationRealMemory
    (exteriorNumericPayload g logical ell α t v (compilerExteriorDelta g α logical t v) J R).2
    v.val t logical.top (16*(ell+3)) ((logical.frames t).q*LocalPush.deg g.graph v/2) (logical.frames t).openBudget

lemma exterior_admitted_reference {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (machine : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical machine) (hDepth : logical.top ≤ ell)
    (t j : ℕ) (ht : t ≤ logical.top) (hj : j ≤ logical.top) (v u : Fin n) (J : ℤ → ℤ)
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8)
    (hu : u ∈ parentDomain (exteriorPush g α logical t v) j) :
    exteriorAdmittedRealPayload g logical ell α t v J machine.scalar.core.mem
      (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)))=
      ((exteriorPush g α logical t v).frames j).reference u := by
  let δ := compilerExteriorDelta g α logical t v
  let base := rawExterior g α logical t v δ
  let R := (exteriorNumericPayload g logical ell α t v δ J machine.scalar.core.mem).2
  have hD := ((compiler_exterior_admission g α logical t v ha).2.2 j).1
  rw [hD] at hu
  have hPot : R (vertexRecordAddress (16*(ell+3)) v.val 0)=base.x v :=
    exterior_numeric_source_potential g logical s α ε ell length machine pm hDepth t v v δ J
  have hRef : ∀ w ∈ parentDomain base j,
      R (vertexRecordAddress (16*(ell+3)) w.val (16*(j+1)))=(base.frames j).reference w := by
    intro w hw
    rw [compiler_raw_domain] at hw
    exact exterior_numeric_source_reference g logical s α ε ell length machine pm hDepth t v w δ J j hj hw
  have he := exterior_activation_source_reference g base R ell t j v u (by omega) (by omega) hj hPot hRef hu
  rw [((compiler_exterior_admission g α logical t v ha).2.2 j).2.2.1]
  simpa only [base,rawExterior,if_pos ht,exteriorAdmittedRealPayload] using he

lemma exterior_admitted_residual {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (machine : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical machine) (hDepth : logical.top ≤ ell)
    (t j : ℕ) (ht : t ≤ logical.top) (hj : j ≤ logical.top) (v u : Fin n) (J : ℤ → ℤ)
    (hv : v ∈ parentDomain logical t)
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8)
    (hu : u ∈ parentDomain (exteriorPush g α logical t v) j) :
    exteriorAdmittedRealPayload g logical ell α t v J machine.scalar.core.mem
      (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))=
      ((exteriorPush g α logical t v).frames j).residual u := by
  let δ := compilerExteriorDelta g α logical t v
  let base := rawExterior g α logical t v δ
  let R := (exteriorNumericPayload g logical ell α t v δ J machine.scalar.core.mem).2
  have hD := ((compiler_exterior_admission g α logical t v ha).2.2 j).1
  rw [hD] at hu
  have hRes : ∀ i ≤ base.top, ∀ w ∈ parentDomain base i,
      R (vertexRecordAddress (16*(ell+3)) w.val (16*(i+1)+1))=(base.frames i).residual w := by
    intro i hi w hw
    rw [compiler_raw_domain] at hw
    exact exterior_numeric_source_residual g logical s α ε ell length machine pm hDepth t v w δ J i hi hw
  have hV : v ∈ parentDomain base t := by rw [compiler_raw_domain]; exact hv
  have he := exterior_activation_source_residual g base R ell t j v u (by omega) (by omega) hj ht hV hRes hu
  rw [((compiler_exterior_admission g α logical t v ha).2.2 j).2.2.2.1]
  simpa only [base,rawExterior,if_pos ht,exteriorAdmittedRealPayload] using he

lemma exterior_admitted_header {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (t : ℕ) (v : Fin n) (J : ℤ → ℤ) (R : ℤ → ℝ) (j slot : ℕ)
    (hs : slot < 32) (h4 : slot ≠ 4) :
    exteriorAdmittedRealPayload g logical ell α t v J R (levelHeaderAddress j slot)=R (levelHeaderAddress j slot) := by
  unfold exteriorAdmittedRealPayload
  rw [exterior_activation_real_header _ (16*(ell+3)) v.val t logical.top j slot _ _ hs]
  simp only [h4,and_false,if_false,add_zero]
  exact exterior_numeric_source_header g logical ell α t v _ J R j slot hs h4

lemma exterior_admitted_budget {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (machine : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical machine)
    (t j : ℕ) (ht : t ≤ logical.top) (hj : j ≤ logical.top) (v : Fin n) (J : ℤ → ℤ)
    (hOpen : J (levelHeaderAddress j 9)=machine.scalar.integerMemory (levelHeaderAddress j 9))
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8) :
    exteriorAdmittedRealPayload g logical ell α t v J machine.scalar.core.mem (levelHeaderAddress j 4)=
      ((exteriorPush g α logical t v).frames j).W := by
  unfold exteriorAdmittedRealPayload
  rw [exterior_activation_real_header _ (16*(ell+3)) v.val t logical.top j 4 _ _ (by decide)]
  rw [exterior_numeric_source_budget g logical s α ε ell length machine pm t v _ J j hj hOpen,
    ((compiler_exterior_admission g α logical t v ha).2.2 j).2.2.2.2,compiler_admit_budget]
  by_cases hjt : j=t
  · subst j
    simp only [rawExterior,if_pos ht,true_and,if_true,and_self]
    split_ifs <;> ring
  · simp only [hjt,false_and,and_true,if_false,add_zero]

lemma exterior_admitted_potential {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (machine : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical machine) (hDepth : logical.top ≤ ell)
    (t : ℕ) (ht : t ≤ logical.top) (v u : Fin n) (J : ℤ → ℤ)
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8) :
    exteriorAdmittedRealPayload g logical ell α t v J machine.scalar.core.mem (vertexRecordAddress (16*(ell+3)) u.val 0)=
      (exteriorPush g α logical t v).x u := by
  unfold exteriorAdmittedRealPayload
  rw [exterior_activation_potential_frame _ ell v.val t logical.top u.val _ _ (by omega),
    (compiler_exterior_admission g α logical t v ha).1,(compiler_admit_stage_fields g _ t v).2.1]
  exact exterior_numeric_source_potential g logical s α ε ell length machine pm hDepth t v u _ J

lemma exterior_admitted_seed_marker {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length : ℕ) (machine : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical machine) (hDepth : logical.top ≤ ell)
    (t : ℕ) (ht : t ≤ logical.top) (v u : Fin n) (J : ℤ → ℤ) :
    exteriorAdmittedRealPayload g logical ell α t v J machine.scalar.core.mem (vertexRecordAddress (16*(ell+3)) u.val 2)=LocalPush.e s u := by
  unfold exteriorAdmittedRealPayload
  rw [exterior_activation_seed_marker_frame _ ell v.val t logical.top u.val _ _ (by omega)]
  exact exterior_numeric_source_seed_marker g logical s α ε ell length machine pm hDepth t v u _ J

lemma exterior_admitted_small_real {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (t : ℕ) (v : Fin n) (J : ℤ → ℤ) (R : ℤ → ℝ) (z : ℤ) (hz : 0 ≤ z) (hSmall : z < 128) :
    exteriorAdmittedRealPayload g logical ell α t v J R z=R z := by
  have hnV : z ≠ vertexRecordAddress (16*(ell+3)) v.val (16*(t+1)+1) := by
    have := vertexRecordAddress_negative (16*(ell+3)) v.val (16*(t+1)+1); omega
  have hnH (i : ℕ) : z ≠ levelHeaderAddress i 4 := by
    unfold levelHeaderAddress
    have := Int.natCast_nonneg i
    omega
  unfold exteriorAdmittedRealPayload exteriorActivationRealMemory
  by_cases hc : t<logical.top
  · rw [if_pos hc,fresh_vertex_real_positive _ (16*(ell+3)) v.val (16*(t+1)) z hz]
    unfold activationScalarsMemory
    rw [Function.update_of_ne (hnH t),Function.update_of_ne hnV]
    exact exterior_numeric_payload_real_positive g logical ell α t v _ J R z hz (fun i hi => hnH i)
  · rw [if_neg hc]
    unfold activationScalarsMemory
    rw [Function.update_of_ne (hnH t),Function.update_of_ne hnV]
    exact exterior_numeric_payload_real_positive g logical ell α t v _ J R z hz (fun i hi => hnH i)

lemma exterior_admitted_other_boolean {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ)
    (α : ℝ) (t j : ℕ) (v u : Fin n) (J : ℤ → ℤ) (R : ℤ → ℝ)
    (hDepth : logical.top ≤ ell) (ht : t ≤ logical.top) (hj : j ≤ logical.top) (hu : u ≠ v) :
    exteriorAdmittedRealPayload g logical ell α t v J R (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+4))=
      R (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+4)) := by
  have hVal : u.val ≠ v.val := fun h => hu (Fin.ext h)
  unfold exteriorAdmittedRealPayload
  rw [exterior_activation_real_vertex _ (16*(ell+3)) v.val t logical.top u.val (16*(j+1)+4) _ _ (by omega) (by omega)]
  simp only [hVal,and_false,false_and,if_false,add_zero]
  exact exterior_numeric_payload_real_field g logical ell hDepth α t v u _ J R (16*(j+1)+4) (by omega) (by omega) (by intros; omega)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorAdmittedFrameRecords

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

structure ExteriorAdmittedFrameRecords {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (α : ℝ)
    (t : ℕ) (v : Fin n) (j width length : ℕ) (old out : MachineState) (floor : ℤ)
    (f : RecursiveFrameMemory g logical j width length old floor) : Prop where
  W : out.scalar.core.mem (levelHeaderAddress j 4)=((exteriorPush g α logical t v).frames j).W
  reference : ∀ u ∈ parentDomain (exteriorPush g α logical t v) j,
    out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)))=((exteriorPush g α logical t v).frames j).reference u
  residual : ∀ u ∈ parentDomain (exteriorPush g α logical t v) j,
    out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+1))=((exteriorPush g α logical t v).frames j).residual u
  activeFlags : ∀ u ∈ parentDomain (exteriorPush g α logical t v) j,
    out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+2))=if u ∈ ((exteriorPush g α logical t v).frames j).active then 1 else 0
  cacheFlags : ∀ u ∈ parentDomain (exteriorPush g α logical t v) j,
    out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+4))=if u ∈ ((exteriorPush g α logical t v).frames j).cache then 1 else 0
  virtualExcluded : ∀ u ∈ parentDomain (exteriorPush g α logical t v) j,
    out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+5))=0
  extFlags : QueuedFlags out.scalar.integerMemory width (16*(j+1)+3) (parentDomain (exteriorPush g α logical t v) j) f.exteriorObject.keys
  highFlags : QueuedFlags out.scalar.integerMemory width (16*(j+1)+6) (parentDomain (exteriorPush g α logical t v) j) f.highObject.keys
  eligibility : ∀ u ∈ parentDomain (exteriorPush g α logical t v) j,
    u.val ∈ ((exteriorPush g α logical t v).frames j).exterior.image Fin.val ↔
    out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+2))=0 ∧
      ((exteriorPush g α logical t v).frames j).q*(out.scalar.integerMemory (vertexRecordAddress width u.val 0) : ℝ) <
        out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+1))
  highValid : ∀ u ∈ parentDomain (exteriorPush g α logical t v) j,
    u.val ∈ ((exteriorPush g α logical t v).frames j).high.image Fin.val ↔
    out.scalar.integerMemory (vertexRecordAddress width u.val (16*(j+1)+2)) ≠ 0 ∧
      3*((exteriorPush g α logical t v).frames j).theta*(out.scalar.integerMemory (vertexRecordAddress width u.val 0) : ℝ) ≤
        out.scalar.core.mem (vertexRecordAddress width u.val (16*(j+1)+1))

set_option maxHeartbeats 4000000 in
lemma exterior_admitted_frame_records {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length boundary : ℕ) (old out : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (t j : ℕ) (ht : t ≤ logical.top) (hj : j ≤ logical.top) (v : Fin n) (J : ℤ → ℤ) (free : ℤ)
    (hFree : 128+32*((ell+2 : ℕ) : ℤ) ≤ free)
    (hCache : GraphCache g J (16*(ell+3)) (insert v logical.stored) free)
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val (old.scalar.core.ptrs 20) (g.neighbors v).length → J z=old.scalar.integerMemory z)
    (hI : out.scalar.integerMemory=exteriorAdmittedIntegerPayload g logical ell boundary α t v free J old.scalar.core.mem)
    (hR : out.scalar.core.mem=exteriorAdmittedRealPayload g logical ell α t v J old.scalar.core.mem)
    (hv : v ∉ (logical.frames t).active) (hvD : v ∈ parentDomain logical t)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hCacheDomain : ∀ i ≤ logical.top, (logical.frames i).cache ⊆ parentDomain logical i)
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8)
    (hKeys : KeysInvariant g (exteriorPush g α logical t v)) :
    ExteriorAdmittedFrameRecords g logical α t v j (16*(ell+3)) length old out
      (128+32*((ell+2 : ℕ) : ℤ)) (pm.frames j hj) := by
  have oldFree : 0 ≤ old.scalar.core.ptrs 20 := by have := pm.allocator; omega
  have hJOpen : J (levelHeaderAddress j 9)=old.scalar.integerMemory (levelHeaderAddress j 9) := by
    apply hJ
    apply cache_write_cells_below_positive
    · have := levelHeaderAddress_positive j 9; omega
    · have := level_header_below_end j 9 (by decide); have := pm.allocator; omega
  have hRes : ∀ u ∈ parentDomain (exteriorPush g α logical t v) j,
      out.scalar.core.mem (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+1))=
        ((exteriorPush g α logical t v).frames j).residual u := by
    intro u hu
    rw [hR]
    exact exterior_admitted_residual g logical s α ε ell length old pm hDepth t j ht hj v u J hvD ha hu
  have hFlags : ∀ u ∈ parentDomain (exteriorPush g α logical t v) j,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) u.val (16*(j+1)+2))=
        if u ∈ ((exteriorPush g α logical t v).frames j).active then 1 else 0 := by
    intro u hu
    rw [hI]
    exact exterior_admitted_active_flags g logical s α ε ell length boundary old pm hDepth t j ht hj v u J free (by omega) hJ hv hSubset ha hu
  have hDegrees : ∀ u ∈ insert v (g.neighbors v).toFinset,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) u.val 0)=((g.neighbors u).length : ℤ) := by
    intro u hu
    rw [hI,exteriorAdmittedIntegerPayload,exterior_activation_global_field g v (logical.frames 0).active boundary ell t logical.top free _ u.val 0 (by omega) (by omega) (by decide)]
    exact exterior_numeric_touched_degrees g logical ell α t v _ J old.scalar.core.mem free hCache u hu
  have hOther : ∀ u ∉ insert v (g.neighbors v).toFinset,
      out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) u.val 0)=old.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) u.val 0) := by
    intro u hu
    rw [hI,exteriorAdmittedIntegerPayload,exterior_activation_global_field g v (logical.frames 0).active boundary ell t logical.top free _ u.val 0 (by omega) (by omega) (by decide)]
    exact exterior_numeric_other_degrees g logical ell α t v _ J old.scalar.integerMemory old.scalar.core.mem _ oldFree hJ u hu
  refine ⟨?_,?_,hRes,hFlags,?_,?_,?_,?_,?_,?_⟩
  · rw [hR]
    exact exterior_admitted_budget g logical s α ε ell length old pm t j ht hj v J hJOpen ha
  · intro u hu
    rw [hR]
    exact exterior_admitted_reference g logical s α ε ell length old pm hDepth t j ht hj v u J ha hu
  · intro u hu
    rw [hI]
    exact exterior_admitted_cache_flags g logical s α ε ell length boundary old pm hDepth t j ht hj v J free (by omega) hJ hv (hCacheDomain j hj) ha u hu
  · intro u hu
    rw [hI]
    exact exterior_admitted_virtual_excluded g logical s α ε ell length boundary old pm hDepth t j ht hj v J free (by omega) hJ ha u hu
  · rw [hI]
    exact exterior_admitted_queued_flags g logical ell boundary α t j v J old.scalar.integerMemory old.scalar.core.mem free
      (old.scalar.core.ptrs 20) hDepth ht hj (by omega) oldFree hJ 3 (by omega) _
      (pm.frames j hj).exteriorData.queuedDomain (pm.frames j hj).exteriorData.flags hv ha
  · rw [hI]
    exact exterior_admitted_queued_flags g logical ell boundary α t j v J old.scalar.integerMemory old.scalar.core.mem free
      (old.scalar.core.ptrs 20) hDepth ht hj (by omega) oldFree hJ 6 (by omega) _
      (pm.frames j hj).highDomain (pm.frames j hj).highFlags hv ha
  · exact exterior_transition_eligibility g α logical t v j (16*(ell+3)) length old out _ (pm.frames j hj)
      hKeys hj (compiler_exterior_scalar_parameters g α logical t v j).1 hFlags hRes hDegrees hOther
  · exact exterior_transition_high_eligibility g α logical t v j (16*(ell+3)) length old out _ (pm.frames j hj)
      hKeys hj (compiler_exterior_scalar_parameters g α logical t v j).2 hFlags hRes hDegrees hOther

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FramePendingDomainNumericTransport

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def FramePendingKeys.domain_numeric_frame {n : ℕ} {g : InputGraph n} {logical next : RecursiveState n}
    {j width length : ℕ} {st out : MachineState} {floor : ℤ}
    (f : FramePendingKeys g logical j width length st floor)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hDomain : parentDomain logical j ⊆ parentDomain next j)
    (hActive : (next.frames j).active=(logical.frames j).active)
    (hStatic : compilerStaticFields (next.frames j)=compilerStaticFields (logical.frames j))
    (hHeaderI : ∀ slot < 32, out.scalar.integerMemory (levelHeaderAddress j slot)=st.scalar.integerMemory (levelHeaderAddress j slot))
    (hHeaderR : ∀ slot < 32, slot ≠ 4 → out.scalar.core.mem (levelHeaderAddress j slot)=st.scalar.core.mem (levelHeaderAddress j slot))
    (hW : out.scalar.core.mem (levelHeaderAddress j 4)=(next.frames j).W)
    (hReference : ∀ v ∈ parentDomain next j,
      out.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)))=(next.frames j).reference v)
    (hResidual : ∀ v ∈ parentDomain next j,
      out.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)+1))=(next.frames j).residual v)
    (hActiveFlags : ∀ v ∈ parentDomain next j,
      out.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+2))=if v ∈ (next.frames j).active then 1 else 0)
    (hCacheFlags : ∀ v ∈ parentDomain next j,
      out.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+4))=if v ∈ (next.frames j).cache then 1 else 0)
    (hVirtual : ∀ v ∈ parentDomain next j,
      out.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+5))=0)
    (hExtFlags : QueuedFlags out.scalar.integerMemory width (16*(j+1)+3) (parentDomain next j) f.exteriorObject.keys)
    (hHighFlags : QueuedFlags out.scalar.integerMemory width (16*(j+1)+6) (parentDomain next j) f.highObject.keys)
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
    activeFlags := hActiveFlags
    cacheFlags := hCacheFlags
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
    virtualExcluded := hVirtual
    highFlags := hHighFlags
    highDomain := f.highDomain.trans (Finset.image_subset_image hDomain)
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
  · refine ⟨f.exteriorData.queuedDomain.trans (Finset.image_subset_image hDomain),hExtFlags,?_,hEligibility⟩
    intro v hv
    rw [hActiveFlags v hv]
    split_ifs <;> norm_num

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorActivationPositiveFrames

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma exterior_activation_integer_small {n : ℕ} (g : InputGraph n) (source : Fin n) (rootActive : Finset (Fin n))
    (boundary ell level top : ℕ) (free z : ℤ) (I : ℤ → ℤ) (hFree : 128 ≤ free) (hz : 0 ≤ z) (hSmall : z < 128) :
    exteriorActivationIntegerMemory g source rootActive boundary level top (16*(ell+3)) free I z=
      activationBoundaryMemory g source rootActive boundary level I z := by
  have hH (slot : ℕ) : z ≠ levelHeaderAddress level slot := by
    unfold levelHeaderAddress
    have := Int.natCast_nonneg level
    have := Int.natCast_nonneg slot
    omega
  have hV : z ≠ vertexRecordAddress (16*(ell+3)) source.val (16*(level+1)+2) := by
    have := vertexRecordAddress_negative (16*(ell+3)) source.val (16*(level+1)+2)
    omega
  unfold exteriorActivationIntegerMemory
  by_cases hc : level<top
  · rw [if_pos hc,fresh_vertex_integer_positive _ (16*(ell+3)) source.val (16*(level+1)) z hz]
    rw [frameListInsertMemory,frame_list_metadata_other _ level 3 2 (16*(ell+3)) source.val 2 _ z (hH 3) (hH 2) hV]
    exact frame_list_prepend_below _ free source.val level 1 z (by omega) (hH 1)
  · rw [if_neg hc,frameListInsertMemory,frame_list_metadata_other _ level 3 2 (16*(ell+3)) source.val 2 _ z (hH 3) (hH 2) hV]
    exact frame_list_prepend_below _ free source.val level 1 z (by omega) (hH 1)

lemma exterior_activation_integer_header_other {n : ℕ} (g : InputGraph n) (source : Fin n) (rootActive : Finset (Fin n))
    (boundary ell level top j slot : ℕ) (free : ℤ) (I : ℤ → ℤ) (hl : level ≤ ell) (hj : j ≤ ell+1) (hs : slot < 32)
    (hFree : 128+32*((ell+2 : ℕ) : ℤ) ≤ free)
    (hOther : j ≠ level ∨ slot ∉ ([1,2,3] : List ℕ)) :
    exteriorActivationIntegerMemory g source rootActive boundary level top (16*(ell+3)) free I (levelHeaderAddress j slot)=
      I (levelHeaderAddress j slot) := by
  have hNe (k : ℕ) (hk : k ∈ ([1,2,3] : List ℕ)) : levelHeaderAddress j slot ≠ levelHeaderAddress level k := by
    have hk32 : k < 32 := by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk; omega
    intro he
    obtain ⟨hjEq,hsEq⟩ := levelHeaderAddress_injective j level slot k hs hk32 he
    rcases hOther with hn|hn
    · exact hn hjEq
    · exact hn (hsEq ▸ hk)
  have hz : 0 ≤ levelHeaderAddress j slot := by have := levelHeaderAddress_positive j slot; omega
  have hBelow : levelHeaderAddress j slot < free := by
    have := level_header_below_end j slot hs
    omega
  have hV : levelHeaderAddress j slot ≠ vertexRecordAddress (16*(ell+3)) source.val (16*(level+1)+2) := by
    have := vertexRecordAddress_negative (16*(ell+3)) source.val (16*(level+1)+2)
    omega
  unfold exteriorActivationIntegerMemory
  by_cases hc : level<top
  · rw [if_pos hc,fresh_vertex_integer_positive _ (16*(ell+3)) source.val (16*(level+1)) _ hz]
    rw [frameListInsertMemory,frame_list_metadata_other _ level 3 2 (16*(ell+3)) source.val 2 _ _ (hNe 3 (by simp)) (hNe 2 (by simp)) hV,
      frame_list_prepend_below _ free source.val level 1 _ hBelow (hNe 1 (by simp))]
    exact activation_boundary_memory_other g source rootActive boundary level I _ (by have := levelHeaderAddress_positive j slot; omega)
  · rw [if_neg hc,frameListInsertMemory,frame_list_metadata_other _ level 3 2 (16*(ell+3)) source.val 2 _ _ (hNe 3 (by simp)) (hNe 2 (by simp)) hV,
      frame_list_prepend_below _ free source.val level 1 _ hBelow (hNe 1 (by simp))]
    exact activation_boundary_memory_other g source rootActive boundary level I _ (by have := levelHeaderAddress_positive j slot; omega)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorAdmittedOtherFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 2500000 in
def exterior_admitted_other_frame {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length boundary : ℕ) (old out : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (t j : ℕ) (ht : t ≤ logical.top) (hj : j ≤ logical.top) (hjt : j ≠ t) (v : Fin n) (J : ℤ → ℤ) (free : ℤ)
    (hFree : 128+32*((ell+2 : ℕ) : ℤ) ≤ free) (hOldFree : old.scalar.core.ptrs 20 ≤ free)
    (hOutFree : out.scalar.core.ptrs 20=free+3)
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val (old.scalar.core.ptrs 20) (g.neighbors v).length → J z=old.scalar.integerMemory z)
    (hI : out.scalar.integerMemory=exteriorAdmittedIntegerPayload g logical ell boundary α t v free J old.scalar.core.mem)
    (hR : out.scalar.core.mem=exteriorAdmittedRealPayload g logical ell α t v J old.scalar.core.mem)
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8)
    (recs : ExteriorAdmittedFrameRecords g logical α t v j (16*(ell+3)) length old out
      (128+32*((ell+2 : ℕ) : ℤ)) (pm.frames j hj)) :
    FramePendingKeys g (exteriorPush g α logical t v) j (16*(ell+3)) length out (128+32*((ell+2 : ℕ) : ℤ)) := by
  have hF : old.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 := by rw [hOutFree]; omega
  have hD : parentDomain logical j ⊆ parentDomain (exteriorPush g α logical t v) j := by
    intro u hu
    exact (compiler_exterior_admission_domain g α logical t v ha j u).mpr (Or.inl hu)
  have hA : ((exteriorPush g α logical t v).frames j).active=(logical.frames j).active := by
    rw [compiler_exterior_admission_active g α logical t v ha j,if_neg hjt]
  apply (FramePendingKeys.ofMemory (pm.frames j hj)).domain_numeric_frame hF hD hA
    (compiler_exterior_static g α logical t v j) _ _ recs.W recs.reference recs.residual
    recs.activeFlags recs.cacheFlags recs.virtualExcluded recs.extFlags recs.highFlags _ recs.eligibility recs.highValid
  · intro slot hs
    rw [hI,exteriorAdmittedIntegerPayload,exterior_activation_integer_header_other g v (logical.frames 0).active boundary ell t logical.top j slot free _
      (by omega) (by omega) hs hFree (Or.inl hjt)]
    exact exterior_numeric_old_heap g logical ell α t v _ J old.scalar.integerMemory old.scalar.core.mem _ _ hJ
      (by have := levelHeaderAddress_positive j slot; omega)
      (by have := level_header_below_end j slot hs; have := pm.allocator; omega)
  · intro slot hs hn
    rw [hR]
    exact exterior_admitted_header g logical ell α t v J old.scalar.core.mem j slot hs hn
  · intro z hz
    have hAbove := (pm.frames j hj).owned_above z hz
    have hBelow := (pm.frames j hj).owned_below z hz
    rw [hI,exteriorAdmittedIntegerPayload,exterior_activation_integer_old_heap g v (logical.frames 0).active boundary ell t logical.top free z _
      (by omega) hAbove (by omega)]
    exact exterior_numeric_old_heap g logical ell α t v _ J old.scalar.integerMemory old.scalar.core.mem _ z hJ (by omega) hBelow

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FramePendingActiveNumericTransport

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def FramePendingKeys.active_numeric_frame {n : ℕ} {g : InputGraph n} {logical next : RecursiveState n}
    {j width length : ℕ} {st out : MachineState} {floor : ℤ}
    (f : FramePendingKeys g logical j width length st floor)
    (hFree : st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20)
    (hDomain : parentDomain logical j ⊆ parentDomain next j)
    (hStatic : compilerStaticFields (next.frames j)=compilerStaticFields (logical.frames j))
    (hHeaderI : ∀ slot < 32, slot ∉ ([1,2,3] : List ℕ) → out.scalar.integerMemory (levelHeaderAddress j slot)=st.scalar.integerMemory (levelHeaderAddress j slot))
    (hHeaderR : ∀ slot < 32, slot ≠ 4 → out.scalar.core.mem (levelHeaderAddress j slot)=st.scalar.core.mem (levelHeaderAddress j slot))
    (hW : out.scalar.core.mem (levelHeaderAddress j 4)=(next.frames j).W)
    (hReference : ∀ v ∈ parentDomain next j,
      out.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)))=(next.frames j).reference v)
    (hResidual : ∀ v ∈ parentDomain next j,
      out.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)+1))=(next.frames j).residual v)
    (hActiveFlags : ∀ v ∈ parentDomain next j,
      out.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+2))=if v ∈ (next.frames j).active then 1 else 0)
    (hCacheFlags : ∀ v ∈ parentDomain next j,
      out.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+4))=if v ∈ (next.frames j).cache then 1 else 0)
    (hVirtual : ∀ v ∈ parentDomain next j,
      out.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+5))=0)
    (hExtFlags : QueuedFlags out.scalar.integerMemory width (16*(j+1)+3) (parentDomain next j) f.exteriorObject.keys)
    (hHighFlags : QueuedFlags out.scalar.integerMemory width (16*(j+1)+6) (parentDomain next j) f.highObject.keys)
    (vertices : List (Fin n)) (F : Finset ℤ)
    (hActiveRep : VertexListRep out.scalar.integerMemory (out.scalar.integerMemory (levelHeaderAddress j 1)) vertices F)
    (hActiveNodup : vertices.Nodup) (hActiveSet : vertices.toFinset=(next.frames j).active)
    (hActiveCount : out.scalar.integerMemory (levelHeaderAddress j 3)=((next.frames j).active.card : ℤ))
    (hActiveVolume : out.scalar.integerMemory (levelHeaderAddress j 2)=(volumeNat g (next.frames j).active : ℤ))
    (hActiveBelow : ∀ z ∈ F, z < out.scalar.core.ptrs 20) (hActiveAbove : ∀ z ∈ F, floor ≤ z)
    (hOwned : ∀ z ∈ f.cacheFoot ∪ f.exteriorObject.cells ∪ f.highObject.cells,
      out.scalar.integerMemory z=st.scalar.integerMemory z)
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
    block := by rw [hBlock]; exact (hHeaderI 14 (by decide) (by decide)).trans f.block
    pc := by rw [hPC]; exact (hHeaderI 0 (by decide) (by decide)).trans f.pc
    openBudget := by rw [hOpen]; exact (hHeaderI 9 (by decide) (by decide)).trans f.openBudget
    needFull := by rw [hNeed]; exact (hHeaderI 10 (by decide) (by decide)).trans f.needFull
    children := by rw [hChildren]; exact (hHeaderI 11 (by decide) (by decide)).trans f.children
    reference := hReference
    residual := hResidual
    activeFlags := hActiveFlags
    cacheFlags := hCacheFlags
    activeVertices := vertices
    activeFoot := F
    activeRep := hActiveRep
    activeNodup := hActiveNodup
    activeSet := hActiveSet
    activeCount := hActiveCount
    activeVolume := hActiveVolume
    activeBelow := hActiveBelow
    activeAbove := hActiveAbove
    cacheVertices := f.cacheVertices
    cacheFoot := f.cacheFoot
    cacheRep := ?_
    cacheNodup := f.cacheNodup
    cacheSet := f.cacheSet.trans hCache.symm
    cacheCount := by rw [hCache]; exact (hHeaderI 5 (by decide) (by decide)).trans f.cacheCount
    cacheVolume := by rw [hCache]; exact (hHeaderI 6 (by decide) (by decide)).trans f.cacheVolume
    cacheBelow := fun z hz => (f.cacheBelow z hz).trans_le hFree
    cacheAbove := f.cacheAbove
    exteriorBase := f.exteriorBase
    highBase := f.highBase
    exteriorPointer := (hHeaderI 7 (by decide) (by decide)).trans f.exteriorPointer
    highPointer := (hHeaderI 8 (by decide) (by decide)).trans f.highPointer
    exteriorObject := ext
    highObject := high
    exteriorData := ?_
    virtualExcluded := hVirtual
    highFlags := hHighFlags
    highDomain := f.highDomain.trans (Finset.image_subset_image hDomain)
    highValid := hHighValid
  }
  · rw [hHeaderI 4 (by decide) (by decide)]
    apply f.cacheRep.frame
    intro z hz
    exact hOwned z (Finset.mem_union_left _ (Finset.mem_union_left _ hz))
  · refine ⟨f.exteriorData.queuedDomain.trans (Finset.image_subset_image hDomain),hExtFlags,?_,hEligibility⟩
    intro v hv
    rw [hActiveFlags v hv]
    split_ifs <;> norm_num

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorActivationSelectedMetadata

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma exterior_activation_card {n : ℕ} (g : InputGraph n) (source : Fin n) (rootActive : Finset (Fin n))
    (boundary ell level top : ℕ) (free : ℤ) (I : ℤ → ℤ)
    (hFree : 128+32*((level+1 : ℕ) : ℤ) ≤ free) :
    exteriorActivationIntegerMemory g source rootActive boundary level top (16*(ell+3)) free I (levelHeaderAddress level 3)=
      I (levelHeaderAddress level 3)+1 := by
  have hz : 0 ≤ levelHeaderAddress level 3 := by have := levelHeaderAddress_positive level 3; omega
  have hn : levelHeaderAddress level 3 ≠ 7 := by have := levelHeaderAddress_positive level 3; omega
  unfold exteriorActivationIntegerMemory
  by_cases hc : level<top
  · rw [if_pos hc,fresh_vertex_integer_positive _ (16*(ell+3)) source.val (16*(level+1)) _ hz]
    rw [frame_list_insert_card _ free source.val level 1 3 2 (16*(ell+3)) 2 _ hFree
      (by decide) (by decide) (by decide) (by decide) (by decide),activation_boundary_memory_other g source rootActive boundary level I _ hn]
  · rw [if_neg hc,frame_list_insert_card _ free source.val level 1 3 2 (16*(ell+3)) 2 _ hFree
      (by decide) (by decide) (by decide) (by decide) (by decide),activation_boundary_memory_other g source rootActive boundary level I _ hn]

lemma exterior_activation_volume {n : ℕ} (g : InputGraph n) (source : Fin n) (rootActive : Finset (Fin n))
    (boundary ell level top : ℕ) (free : ℤ) (I : ℤ → ℤ)
    (hFree : 128+32*((level+1 : ℕ) : ℤ) ≤ free) :
    exteriorActivationIntegerMemory g source rootActive boundary level top (16*(ell+3)) free I (levelHeaderAddress level 2)=
      I (levelHeaderAddress level 2)+((g.neighbors source).length : ℤ) := by
  have hz : 0 ≤ levelHeaderAddress level 2 := by have := levelHeaderAddress_positive level 2; omega
  have hn : levelHeaderAddress level 2 ≠ 7 := by have := levelHeaderAddress_positive level 2; omega
  unfold exteriorActivationIntegerMemory
  by_cases hc : level<top
  · rw [if_pos hc,fresh_vertex_integer_positive _ (16*(ell+3)) source.val (16*(level+1)) _ hz]
    rw [frame_list_insert_volume _ free source.val level 1 3 2 (16*(ell+3)) 2 _ hFree
      (by decide) (by decide) (by decide),activation_boundary_memory_other g source rootActive boundary level I _ hn]
  · rw [if_neg hc,frame_list_insert_volume _ free source.val level 1 3 2 (16*(ell+3)) 2 _ hFree
      (by decide) (by decide) (by decide),activation_boundary_memory_other g source rootActive boundary level I _ hn]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorAdmittedSelectedFrame

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 4000000 in
def exterior_admitted_selected_frame {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length boundary : ℕ) (old out : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (t : ℕ) (ht : t ≤ logical.top) (v : Fin n) (J : ℤ → ℤ) (free : ℤ)
    (hFree : 128+32*((ell+2 : ℕ) : ℤ) ≤ free) (hOldFree : old.scalar.core.ptrs 20 ≤ free)
    (hOutFree : out.scalar.core.ptrs 20=free+3)
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val (old.scalar.core.ptrs 20) (g.neighbors v).length → J z=old.scalar.integerMemory z)
    (hI : out.scalar.integerMemory=exteriorAdmittedIntegerPayload g logical ell boundary α t v free J old.scalar.core.mem)
    (hR : out.scalar.core.mem=exteriorAdmittedRealPayload g logical ell α t v J old.scalar.core.mem)
    (hv : v ∉ (logical.frames t).active)
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8)
    (hRep : VertexListRep out.scalar.integerMemory (out.scalar.integerMemory (levelHeaderAddress t 1))
      (v::(pm.frames t ht).activeVertices) (nodeCells free ∪ (pm.frames t ht).activeFoot))
    (hBelow : ∀ z ∈ nodeCells free ∪ (pm.frames t ht).activeFoot, z < free+3)
    (recs : ExteriorAdmittedFrameRecords g logical α t v t (16*(ell+3)) length old out
      (128+32*((ell+2 : ℕ) : ℤ)) (pm.frames t ht)) :
    FramePendingKeys g (exteriorPush g α logical t v) t (16*(ell+3)) length out (128+32*((ell+2 : ℕ) : ℤ)) := by
  classical
  let f := pm.frames t ht
  have hD : parentDomain logical t ⊆ parentDomain (exteriorPush g α logical t v) t := by
    intro u hu
    exact (compiler_exterior_admission_domain g α logical t v ha t u).mpr (Or.inl hu)
  have hF : old.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 := by rw [hOutFree]; omega
  have hActive : ((exteriorPush g α logical t v).frames t).active=insert v (logical.frames t).active := by
    rw [compiler_exterior_admission_active g α logical t v ha t,if_pos rfl]
  have hMeta (slot : ℕ) (hs : slot < 32) :
      (exteriorNumericPayload g logical ell α t v (compilerExteriorDelta g α logical t v) J old.scalar.core.mem).1 (levelHeaderAddress t slot)=
        old.scalar.integerMemory (levelHeaderAddress t slot) :=
    exterior_numeric_old_heap g logical ell α t v _ J old.scalar.integerMemory old.scalar.core.mem _ _ hJ
      (by have := levelHeaderAddress_positive t slot; omega)
      (by have := level_header_below_end t slot hs; have := pm.allocator; omega)
  apply (FramePendingKeys.ofMemory f).active_numeric_frame hF hD
    (compiler_exterior_static g α logical t v t) _ _ recs.W recs.reference recs.residual
    recs.activeFlags recs.cacheFlags recs.virtualExcluded recs.extFlags recs.highFlags
    (v::f.activeVertices) (nodeCells free ∪ f.activeFoot) hRep _ _ _ _ _ _ _ recs.eligibility recs.highValid
  · intro slot hs hn
    rw [hI,exteriorAdmittedIntegerPayload,exterior_activation_integer_header_other g v (logical.frames 0).active boundary ell t logical.top t slot free _
      (by omega) (by omega) hs hFree (Or.inr hn)]
    exact hMeta slot hs
  · intro slot hs hn
    rw [hR]
    exact exterior_admitted_header g logical ell α t v J old.scalar.core.mem t slot hs hn
  · apply List.nodup_cons.mpr
    refine ⟨?_,f.activeNodup⟩
    intro hm
    exact hv (f.activeSet ▸ List.mem_toFinset.mpr hm)
  · rw [List.toFinset_cons,f.activeSet,hActive]
  · rw [hI,exteriorAdmittedIntegerPayload,exterior_activation_card g v (logical.frames 0).active boundary ell t logical.top free _ (by omega),hMeta 3 (by decide),f.activeCount,hActive,
      Finset.card_insert_of_notMem hv,Nat.cast_add,Nat.cast_one]
  · rw [hI,exteriorAdmittedIntegerPayload,exterior_activation_volume g v (logical.frames 0).active boundary ell t logical.top free _ (by omega),hMeta 2 (by decide),f.activeVolume,hActive]
    have hVol : volumeNat g (insert v (logical.frames t).active)=(g.neighbors v).length+volumeNat g (logical.frames t).active := by
      simp only [volumeNat,Finset.sum_insert hv]
    rw [hVol,Nat.cast_add]
    exact add_comm _ _
  · intro z hz
    rw [hOutFree]
    exact hBelow z hz
  · intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · exact hFree.trans (nodeCells_mem_iff free z |>.mp hz).1
    · exact f.activeAbove z hz
  · intro z hz
    have hzOwned : z ∈ f.owned := by
      rcases Finset.mem_union.mp hz with hz|hz
      · rcases Finset.mem_union.mp hz with hz|hz
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hz))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
      · exact Finset.mem_union_right _ hz
    have hAbove := f.owned_above z hzOwned
    have hOldBelow := f.owned_below z hzOwned
    rw [hI,exteriorAdmittedIntegerPayload,exterior_activation_integer_old_heap g v (logical.frames 0).active boundary ell t logical.top free z _ (by omega) hAbove (by omega)]
    exact exterior_numeric_old_heap g logical ell α t v _ J old.scalar.integerMemory old.scalar.core.mem _ z hJ (by omega) hOldBelow

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorAdmittedCache

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma exterior_admitted_row_base {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell boundary : ℕ)
    (α : ℝ) (t : ℕ) (v : Fin n) (free : ℤ) (J : ℤ → ℤ) (R : ℤ → ℝ)
    (ht : t ≤ ell) (hFree : 0 ≤ free) (u : Fin n) :
    exteriorAdmittedIntegerPayload g logical ell boundary α t v free J R (vertexRecordAddress (16*(ell+3)) u.val 1)=
      J (vertexRecordAddress (16*(ell+3)) u.val 1) := by
  unfold exteriorAdmittedIntegerPayload
  rw [exterior_activation_global_field g v (logical.frames 0).active boundary ell t logical.top free _ u.val 1 ht hFree (by decide)]
  exact exterior_numeric_payload_integer_field g logical ell α t v u _ J R 1 (by omega) (by decide)

lemma exterior_admitted_graph_cache {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell boundary : ℕ)
    (α : ℝ) (t : ℕ) (v : Fin n) (free : ℤ) (J : ℤ → ℤ) (R : ℤ → ℝ)
    (ht : t ≤ ell) (hFree : 128+32*((ell+2 : ℕ) : ℤ) ≤ free)
    (hCache : GraphCache g J (16*(ell+3)) (insert v logical.stored) free)
    (hRows : ∀ u ∈ insert v logical.stored,
      128+32*((ell+2 : ℕ) : ℤ) ≤ J (vertexRecordAddress (16*(ell+3)) u.val 1)) :
    GraphCache g (exteriorAdmittedIntegerPayload g logical ell boundary α t v free J R)
      (16*(ell+3)) (insert v logical.stored) (free+3) := by
  let δ := compilerExteriorDelta g α logical t v
  let P := exteriorNumericPayload g logical ell α t v δ J R
  have hp : GraphCache g P.1 (16*(ell+3)) (insert v logical.stored) free := by
    unfold P exteriorNumericPayload
    exact stored_neighbor_fold_graph_cache g v logical ell _ _ free _ hCache
  have hBase (u : Fin n) : P.1 (vertexRecordAddress (16*(ell+3)) u.val 1)=J (vertexRecordAddress (16*(ell+3)) u.val 1) :=
    exterior_numeric_payload_integer_field g logical ell α t v u δ J R 1 (by omega) (by decide)
  apply GraphCache.frame g P.1 (exteriorAdmittedIntegerPayload g logical ell boundary α t v free J R)
    (16*(ell+3)) (insert v logical.stored) (free+3) (hp.mono_free (by omega))
  · intro u field hf
    exact exterior_activation_global_field g v (logical.frames 0).active boundary ell t logical.top free P.1 u.val field ht (by omega) (by omega)
  · intro u hu i hi
    have hBelow := hp.belowFree u hu i hi
    have hAbove : 128+32*((ell+2 : ℕ) : ℤ) ≤ P.1 (vertexRecordAddress (16*(ell+3)) u.val 1)+(i : ℤ) := by
      rw [hBase]
      have := hRows u hu
      have := Int.natCast_nonneg i
      omega
    exact exterior_activation_integer_old_heap g v (logical.frames 0).active boundary ell t logical.top free _ P.1 ht hAbove hBelow

lemma exterior_admitted_cached_cells_below {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell boundary : ℕ)
    (α : ℝ) (t : ℕ) (v : Fin n) (free : ℤ) (J : ℤ → ℤ) (R : ℤ → ℝ)
    (ht : t ≤ ell) (hFree : 0 ≤ free)
    (hCache : GraphCache g J (16*(ell+3)) (insert v logical.stored) free) :
    ∀ z ∈ cachedRowCells g (exteriorAdmittedIntegerPayload g logical ell boundary α t v free J R) (16*(ell+3)) (insert v logical.stored), z < free := by
  rw [cached_row_cells_congr g (insert v logical.stored) (16*(ell+3)) J _
    (fun u hu => exterior_admitted_row_base g logical ell boundary α t v free J R ht hFree u)]
  exact cached_row_cells_below g (insert v logical.stored) (16*(ell+3)) J free hCache

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorAdmittedBoundary

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

lemma exterior_admitted_boundary {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (s : Fin n) (α ε : ℝ) (ell length boundary : ℕ) (old : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (t : ℕ) (ht : t ≤ logical.top) (v : Fin n) (J : ℤ → ℤ) (free : ℤ)
    (hFree : 128+32*((ell+2 : ℕ) : ℤ) ≤ free)
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val (old.scalar.core.ptrs 20) (g.neighbors v).length → J z=old.scalar.integerMemory z)
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8)
    (hBoundary : logical.boundaryEdges=(boundary : ℤ))
    (hNext : 0 ≤ (exteriorPush g α logical t v).boundaryEdges) :
    exteriorAdmittedIntegerPayload g logical ell boundary α t v free J old.scalar.core.mem 7=
      (exteriorPush g α logical t v).boundaryEdges := by
  have hSource := (compiler_exterior_admission g α logical t v ha).2.1
  rw [compiler_admit_boundary] at hSource
  have hRawB : (rawExterior g α logical t v (compilerExteriorDelta g α logical t v)).boundaryEdges=logical.boundaryEdges := rfl
  rw [hRawB,compiler_raw_active] at hSource
  unfold exteriorAdmittedIntegerPayload
  rw [exterior_activation_integer_small g v (logical.frames 0).active boundary ell t logical.top free 7 _ (by omega) (by decide) (by decide)]
  unfold activationBoundaryMemory
  by_cases hRoot : t=0
  · rw [if_pos hRoot,Function.update_self]
    rw [if_pos hRoot] at hSource
    have hActive : (logical.frames t).active=(logical.frames 0).active := by rw [hRoot]
    rw [hActive,hBoundary] at hSource
    omega
  · rw [if_neg hRoot]
    rw [if_neg hRoot] at hSource
    rw [exterior_numeric_old_heap g logical ell α t v _ J old.scalar.integerMemory old.scalar.core.mem _ 7 hJ
      (by decide) (by have := pm.allocator; omega),pm.boundary]
    exact hSource.symm

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorAdmittedPendingMemory

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 12000000 in
def exterior_admitted_pending_memory (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length boundary : ℕ) (old out : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (t : ℕ) (ht : t ≤ logical.top) (v : Fin n) (J : ℤ → ℤ) (free : ℤ) (steps : ℕ)
    (ex : MachineEval m g ω exteriorNumericRawCode old steps out)
    (hFree : 128+32*((ell+2 : ℕ) : ℤ) ≤ free) (hOldFree : old.scalar.core.ptrs 20 ≤ free)
    (hOutFree : out.scalar.core.ptrs 20=free+3)
    (hTop : out.scalar.core.ptrs 100=(logical.top : ℤ)) (hZero : out.scalar.core.ptrs 0=0)
    (hCache : GraphCache g J (16*(ell+3)) (insert v logical.stored) free)
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val (old.scalar.core.ptrs 20) (g.neighbors v).length → J z=old.scalar.integerMemory z)
    (hBase : J (vertexRecordAddress (16*(ell+3)) v.val 1)=if v ∈ logical.stored then old.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 1) else old.scalar.core.ptrs 20)
    (hI : out.scalar.integerMemory=exteriorAdmittedIntegerPayload g logical ell boundary α t v free J old.scalar.core.mem)
    (hR : out.scalar.core.mem=exteriorAdmittedRealPayload g logical ell α t v J old.scalar.core.mem)
    (hv : v ∉ (logical.frames t).active) (hvD : v ∈ parentDomain logical t)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hCacheDomain : ∀ i ≤ logical.top, (logical.frames i).cache ⊆ parentDomain logical i)
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8)
    (hKeys : KeysInvariant g (exteriorPush g α logical t v))
    (hBoundary : logical.boundaryEdges=(boundary : ℤ)) (hBoundaryNext : 0 ≤ (exteriorPush g α logical t v).boundaryEdges)
    (hRep : VertexListRep out.scalar.integerMemory (out.scalar.integerMemory (levelHeaderAddress t 1))
      (v::(pm.frames t ht).activeVertices) (nodeCells free ∪ (pm.frames t ht).activeFoot))
    (hBelow : ∀ z ∈ nodeCells free ∪ (pm.frames t ht).activeFoot, z < free+3)
    (hOutput : out.output=old.output) :
    MachinePendingKeys g s α ε ell length (exteriorPush g α logical t v) out := by
  classical
  let next := exteriorPush g α logical t v
  let width := 16*(ell+3)
  have hNextTop : next.top=logical.top := compiler_exterior_top g α logical t v
  have hStored : next.stored=insert v logical.stored := compiler_exterior_stored g α logical t v
  have hOldZero : 0 ≤ old.scalar.core.ptrs 20 := by have := pm.allocator; omega
  let recs := fun j hj => exterior_admitted_frame_records g logical s α ε ell length boundary old out pm hDepth
    t j ht hj v J free hFree hCache hJ hI hR hv hvD hSubset hCacheDomain ha hKeys
  let selected := exterior_admitted_selected_frame g logical s α ε ell length boundary old out pm hDepth
    t ht v J free hFree hOldFree hOutFree hJ hI hR hv ha hRep hBelow (recs t ht)
  let other := fun j hj hjt => exterior_admitted_other_frame g logical s α ε ell length boundary old out pm hDepth
    t j ht hj hjt v J free hFree hOldFree hOutFree hJ hI hR ha (recs j hj)
  let frames : ∀ j ≤ next.top, FramePendingKeys g next j width length out (128+32*((ell+2 : ℕ) : ℤ)) := fun j hj =>
    if hjt : j=t then hjt.symm ▸ selected else other j (by rw [hNextTop] at hj; exact hj) hjt
  have hFrameOwned (j : ℕ) (hj : j ≤ next.top) :
      (frames j hj).owned=if j=t then nodeCells free ∪ (pm.frames j (by rw [←hNextTop]; exact hj)).owned
        else (pm.frames j (by rw [←hNextTop]; exact hj)).owned := by
    by_cases hjt : j=t
    · subst j
      simp only [frames,dif_pos rfl,if_pos rfl]
      change (nodeCells free ∪ (pm.frames t ht).activeFoot) ∪ (pm.frames t ht).cacheFoot ∪
        (pm.frames t ht).exteriorObject.cells ∪ (pm.frames t ht).highObject.cells=nodeCells free ∪ (pm.frames t ht).owned
      simp only [RecursiveFrameMemory.owned,Finset.union_assoc]
    · simp only [frames,dif_neg hjt,if_neg hjt]
      rfl
  have hRows : ∀ u ∈ insert v logical.stored,
      128+32*((ell+2 : ℕ) : ℤ) ≤ J (vertexRecordAddress width u.val 1) :=
    cache_extension_rows_above g logical.stored width v old.scalar.integerMemory J _ _ hOldZero (by dsimp [width]; omega)
      hJ hBase pm.allocator pm.rowAbove
  have hBaseOut (u : Fin n) : out.scalar.integerMemory (vertexRecordAddress width u.val 1)=J (vertexRecordAddress width u.val 1) := by
    rw [hI]
    exact exterior_admitted_row_base g logical ell boundary α t v free J old.scalar.core.mem (by omega) (by omega) u
  have hOldBases : ∀ u ∈ logical.stored,
      out.scalar.integerMemory (vertexRecordAddress width u.val 1)=old.scalar.integerMemory (vertexRecordAddress width u.val 1) := by
    intro u hu
    rw [hBaseOut]
    exact cache_extension_old_base g logical.stored width v old.scalar.integerMemory J _ hOldZero (by dsimp [width]; omega) hJ hBase u hu
  have hNewBase : out.scalar.integerMemory (vertexRecordAddress width v.val 1)=
      if v ∈ logical.stored then old.scalar.integerMemory (vertexRecordAddress width v.val 1) else old.scalar.core.ptrs 20 := by rw [hBaseOut,hBase]
  have hSmallI (z : ℤ) (hz : 0 ≤ z) (hSmall : z < 128) (hn : z ≠ 7) : out.scalar.integerMemory z=old.scalar.integerMemory z := by
    rw [hI,exteriorAdmittedIntegerPayload,exterior_activation_integer_small g v (logical.frames 0).active boundary ell t logical.top free z _ (by omega) hz hSmall,
      activation_boundary_memory_other g v (logical.frames 0).active boundary t _ z hn]
    exact exterior_numeric_old_heap g logical ell α t v _ J old.scalar.integerMemory old.scalar.core.mem _ z hJ hz (by have := pm.allocator; omega)
  have hDegreeTouched : ∀ u ∈ insert v (g.neighbors v).toFinset,
      out.scalar.integerMemory (vertexRecordAddress width u.val 0)=((g.neighbors u).length : ℤ) := by
    intro u hu
    rw [hI,exteriorAdmittedIntegerPayload,exterior_activation_global_field g v (logical.frames 0).active boundary ell t logical.top free _ u.val 0 (by omega) (by omega) (by decide)]
    exact exterior_numeric_touched_degrees g logical ell α t v _ J old.scalar.core.mem free hCache u hu
  have hDegreeOther : ∀ u ∉ insert v (g.neighbors v).toFinset,
      out.scalar.integerMemory (vertexRecordAddress width u.val 0)=old.scalar.integerMemory (vertexRecordAddress width u.val 0) := by
    intro u hu
    rw [hI,exteriorAdmittedIntegerPayload,exterior_activation_global_field g v (logical.frames 0).active boundary ell t logical.top free _ u.val 0 (by omega) (by omega) (by decide)]
    exact exterior_numeric_other_degrees g logical ell α t v _ J old.scalar.integerMemory old.scalar.core.mem _ hOldZero hJ u hu
  have hNodeOld (j : ℕ) (hj : j ≤ logical.top) : Disjoint (nodeCells free) (pm.frames j hj).owned :=
    nodeCells_disjoint_below free _ (fun z hz => ((pm.frames j hj).owned_below z hz).trans_le hOldFree)
  have hOldCacheSep (j : ℕ) (hj : j ≤ logical.top) :
      Disjoint (pm.frames j hj).owned (cachedRowCells g out.scalar.integerMemory width (insert v logical.stored)) :=
    cached_row_extension_disjoint g logical.stored width v old.scalar.integerMemory out.scalar.integerMemory _ _
      hOldBases hNewBase (pm.cacheSeparation j hj) (pm.frames j hj).owned_below
  refine {
    zero := hZero
    top := by rw [hNextTop]; exact hTop
    width := (ex.pointer_frame 50 (by decide)).trans pm.width
    alphaRegister := (ex.real_register_frame 30 (by decide)).trans pm.alphaRegister
    one := (ex.real_register_frame 31 (by decide)).trans pm.one
    alphaMemory := by rw [hR,exterior_admitted_small_real g logical ell α t v J _ 0 (by decide) (by decide)]; exact pm.alphaMemory
    epsilonMemory := by rw [hR,exterior_admitted_small_real g logical ell α t v J _ 1 (by decide) (by decide)]; exact pm.epsilonMemory
    depthMemory := (hSmallI 2 (by decide) (by decide) (by decide)).trans pm.depthMemory
    lengthMemory := (hSmallI 5 (by decide) (by decide) (by decide)).trans pm.lengthMemory
    seedMemory := (hSmallI 0 (by decide) (by decide) (by decide)).trans pm.seedMemory
    allocator := by rw [hOutFree]; omega
    potential := ?_
    seedMarker := ?_
    boundary := by rw [hI]; exact exterior_admitted_boundary g logical s α ε ell length boundary old pm hDepth t ht v J free hFree hJ ha hBoundary hBoundaryNext
    graphCache := by rw [hI,hStored,hOutFree]; exact exterior_admitted_graph_cache g logical ell boundary α t v free J old.scalar.core.mem (by omega) hFree hCache hRows
    rowAbove := ?_
    knownDegree := ?_
    unknownDegree := ?_
    frames := frames
    pieceSeparation := ?_
    frameSeparation := ?_
    cacheSeparation := ?_
    output := hOutput.trans pm.output
  }
  · intro u
    rw [hR]
    exact exterior_admitted_potential g logical s α ε ell length old pm hDepth t ht v u J ha
  · intro u
    rw [hR]
    exact exterior_admitted_seed_marker g logical s α ε ell length old pm hDepth t ht v u J
  · intro u hu
    rw [hStored] at hu
    rw [hBaseOut]
    exact hRows u hu
  · intro u hu
    rw [recursive_degree_domain_exterior] at hu
    by_cases hT : u ∈ insert v (g.neighbors v).toFinset
    · exact hDegreeTouched u hT
    · rw [hDegreeOther u hT]
      exact pm.knownDegree u ((Finset.mem_union.mp hu).resolve_right hT)
  · intro u hu
    rw [recursive_degree_domain_exterior] at hu
    have hT : u ∉ insert v (g.neighbors v).toFinset := fun h => hu (Finset.mem_union_right _ h)
    rw [hDegreeOther u hT]
    exact pm.unknownDegree u (fun h => hu (Finset.mem_union_left _ h))
  · intro j hj
    have hj' : j ≤ logical.top := by rw [←hNextTop]; exact hj
    by_cases hjt : j=t
    · subst j
      simp only [frames,dif_pos rfl]
      change ([nodeCells free ∪ (pm.frames t ht).activeFoot,(pm.frames t ht).cacheFoot,
        (pm.frames t ht).exteriorObject.cells,(pm.frames t ht).highObject.cells] : List (Finset ℤ)).Pairwise Disjoint
      exact fresh_active_pieces _ _ _ _ _ (pm.pieceSeparation t ht) (hNodeOld t ht)
    · simp only [frames,dif_neg hjt]
      change (pm.frames j hj').pieces.Pairwise Disjoint
      exact pm.pieceSeparation j hj'
  · intro i hi j hj hij
    have hi' : i ≤ logical.top := by rw [←hNextTop]; exact hi
    have hj' : j ≤ logical.top := by rw [←hNextTop]; exact hj
    rw [hFrameOwned i hi,hFrameOwned j hj]
    by_cases hit : i=t <;> by_cases hjt : j=t
    · exact (hij (hit.trans hjt.symm)).elim
    · rw [if_pos hit,if_neg hjt]
      exact Finset.disjoint_union_left.mpr ⟨hNodeOld j hj',pm.frameSeparation i hi' j hj' hij⟩
    · rw [if_neg hit,if_pos hjt]
      exact Finset.disjoint_union_right.mpr ⟨(hNodeOld i hi').symm,pm.frameSeparation i hi' j hj' hij⟩
    · rw [if_neg hit,if_neg hjt]
      exact pm.frameSeparation i hi' j hj' hij
  · intro j hj
    have hj' : j ≤ logical.top := by rw [←hNextTop]; exact hj
    rw [hFrameOwned j hj,hStored]
    by_cases hjt : j=t
    · rw [if_pos hjt]
      apply Finset.disjoint_union_left.mpr
      refine ⟨?_,hOldCacheSep j hj'⟩
      apply nodeCells_disjoint_below
      rw [hI]
      exact exterior_admitted_cached_cells_below g logical ell boundary α t v free J old.scalar.core.mem (by omega) (by omega) hCache
    · rw [if_neg hjt]
      exact hOldCacheSep j hj'

lemma exterior_admitted_pending_memory_mass (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length boundary : ℕ) (old out : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (t : ℕ) (ht : t ≤ logical.top) (v : Fin n) (J : ℤ → ℤ) (free : ℤ) (steps : ℕ)
    (ex : MachineEval m g ω exteriorNumericRawCode old steps out)
    (hFree : 128+32*((ell+2 : ℕ) : ℤ) ≤ free) (hOldFree : old.scalar.core.ptrs 20 ≤ free)
    (hOutFree : out.scalar.core.ptrs 20=free+3)
    (hTop : out.scalar.core.ptrs 100=(logical.top : ℤ)) (hZero : out.scalar.core.ptrs 0=0)
    (hCache : GraphCache g J (16*(ell+3)) (insert v logical.stored) free)
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val (old.scalar.core.ptrs 20) (g.neighbors v).length → J z=old.scalar.integerMemory z)
    (hBase : J (vertexRecordAddress (16*(ell+3)) v.val 1)=if v ∈ logical.stored then old.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 1) else old.scalar.core.ptrs 20)
    (hI : out.scalar.integerMemory=exteriorAdmittedIntegerPayload g logical ell boundary α t v free J old.scalar.core.mem)
    (hR : out.scalar.core.mem=exteriorAdmittedRealPayload g logical ell α t v J old.scalar.core.mem)
    (hv : v ∉ (logical.frames t).active) (hvD : v ∈ parentDomain logical t)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hCacheDomain : ∀ i ≤ logical.top, (logical.frames i).cache ⊆ parentDomain logical i)
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8)
    (hKeys : KeysInvariant g (exteriorPush g α logical t v))
    (hBoundary : logical.boundaryEdges=(boundary : ℤ)) (hBoundaryNext : 0 ≤ (exteriorPush g α logical t v).boundaryEdges)
    (hRep : VertexListRep out.scalar.integerMemory (out.scalar.integerMemory (levelHeaderAddress t 1))
      (v::(pm.frames t ht).activeVertices) (nodeCells free ∪ (pm.frames t ht).activeFoot))
    (hBelow : ∀ z ∈ nodeCells free ∪ (pm.frames t ht).activeFoot, z < free+3)
    (hOutput : out.output=old.output) :
    (exterior_admitted_pending_memory m g ω logical s α ε ell length boundary old out pm hDepth t ht v J free steps ex hFree hOldFree hOutFree hTop hZero hCache hJ hBase hI hR hv hvD hSubset hCacheDomain ha hKeys hBoundary hBoundaryNext hRep hBelow hOutput).queueMass=pm.queueMass := by
  unfold MachinePendingKeys.queueMass RecursiveMachineMemory.queueMass
  simp only [compiler_exterior_top]
  apply Finset.sum_congr rfl
  intro i hi
  have hLive : i ≤ logical.top := by have := Finset.mem_range.mp hi; omega
  simp only [dif_pos hLive]
  by_cases hit : i=t
  · subst i
    simp only [exterior_admitted_pending_memory,dif_pos rfl]
    rfl
  · simp only [exterior_admitted_pending_memory,dif_neg hit]
    rfl

set_option pp.notation false in
lemma exterior_admitted_pending_memory_keys (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length boundary : ℕ) (old out : MachineState)
    (pm : RecursiveMachineMemory g s α ε ell length logical old) (hDepth : logical.top ≤ ell)
    (t : ℕ) (ht : t ≤ logical.top) (v : Fin n) (J : ℤ → ℤ) (free : ℤ) (steps : ℕ)
    (ex : MachineEval m g ω exteriorNumericRawCode old steps out)
    (hFree : 128+32*((ell+2 : ℕ) : ℤ) ≤ free) (hOldFree : old.scalar.core.ptrs 20 ≤ free)
    (hOutFree : out.scalar.core.ptrs 20=free+3)
    (hTop : out.scalar.core.ptrs 100=(logical.top : ℤ)) (hZero : out.scalar.core.ptrs 0=0)
    (hCache : GraphCache g J (16*(ell+3)) (insert v logical.stored) free)
    (hJ : ∀ z, z ∉ cacheWriteCells (16*(ell+3)) v.val (old.scalar.core.ptrs 20) (g.neighbors v).length → J z=old.scalar.integerMemory z)
    (hBase : J (vertexRecordAddress (16*(ell+3)) v.val 1)=if v ∈ logical.stored then old.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 1) else old.scalar.core.ptrs 20)
    (hI : out.scalar.integerMemory=exteriorAdmittedIntegerPayload g logical ell boundary α t v free J old.scalar.core.mem)
    (hR : out.scalar.core.mem=exteriorAdmittedRealPayload g logical ell α t v J old.scalar.core.mem)
    (hv : v ∉ (logical.frames t).active) (hvD : v ∈ parentDomain logical t)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hCacheDomain : ∀ i ≤ logical.top, (logical.frames i).cache ⊆ parentDomain logical i)
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8)
    (hKeys : KeysInvariant g (exteriorPush g α logical t v))
    (hBoundary : logical.boundaryEdges=(boundary : ℤ)) (hBoundaryNext : 0 ≤ (exteriorPush g α logical t v).boundaryEdges)
    (hRep : VertexListRep out.scalar.integerMemory (out.scalar.integerMemory (levelHeaderAddress t 1))
      (v::(pm.frames t ht).activeVertices) (nodeCells free ∪ (pm.frames t ht).activeFoot))
    (hBelow : ∀ z ∈ nodeCells free ∪ (pm.frames t ht).activeFoot, z < free+3)
    (hOutput : out.output=old.output) (j : ℕ) (hj : j ≤ logical.top) :
    let memory := exterior_admitted_pending_memory m g ω logical s α ε ell length boundary old out pm hDepth t ht v J free steps ex hFree hOldFree hOutFree hTop hZero hCache hJ hBase hI hR hv hvD hSubset hCacheDomain ha hKeys hBoundary hBoundaryNext hRep hBelow hOutput
    (memory.frames j (by rw [compiler_exterior_top]; exact hj)).exteriorObject.keys=(pm.frames j hj).exteriorObject.keys ∧
      (memory.frames j (by rw [compiler_exterior_top]; exact hj)).highObject.keys=(pm.frames j hj).highObject.keys := by
  dsimp only
  constructor
  all_goals
    unfold RankQueueObject.keys
    dsimp only [exterior_admitted_pending_memory]
    split_ifs with hit
    · subst j
      rw [dif_pos rfl]
      rfl
    · rw [dif_neg hit]
      rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorActivationExecutionComplete

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 15000000 in
lemma exterior_activation_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank t boundary : ℕ) (v : Fin n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (ht : t ≤ logical.top) (hvDomain : v ∈ parentDomain logical t) (hvNot : v ∉ (logical.frames t).active)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hCacheDomain : ∀ i ≤ logical.top, (logical.frames i).cache ⊆ parentDomain logical i)
    (hSelected : st.scalar.core.ptrs 112=(t : ℤ)) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hBoundary : logical.boundaryEdges=(boundary : ℤ)) (hBoundaryNext : 0 ≤ (exteriorPush g α logical t v).boundaryEdges)
    (ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8)
    (hKeys : KeysInvariant g (exteriorPush g α logical t v))
    (hMass : pm.queueMass+2*(logical.top+1)*((g.neighbors v).length+1) ≤ N) (hCap : rank < length) (hPow : N < 2^rank) :
    let width := 16*(ell+3)
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (exteriorPush g α logical t v) out,
      MachineEval m g ω exteriorPushProgramCode st steps out ∧
      steps ≤ 84*width+452+(logical.top+1)*(4*width+60)+
        (g.neighbors v).length*((logical.top+1)*(8*width+39)+8*width+50)+
        ((g.neighbors v).length+1)*((logical.top+1)*(42*rank+60*width+284)+4*width+25) ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*((g.neighbors v).length+1) ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ w : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) w.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) w.val 7)) := by
  intro width
  let next := exteriorPush g α logical t v
  let free := if v ∈ logical.stored then st.scalar.core.ptrs 20 else st.scalar.core.ptrs 20+((g.neighbors v).length : ℤ)
  have hNextTop : next.top=logical.top := compiler_exterior_top g α logical t v
  obtain ⟨u,a,J,ea,hu,jCache,jFrame,jBase,aI,aR,aRep,aBelow,aFree,a100,a0,a40,a116,a120,aQ,aW,aO,aH⟩ :=
    exterior_activation_raw_exec m g ω logical s α ε ell length t boundary v st hh pm hDepth ht hvDomain hSubset hSelected hv hBoundary ha
  have hOldFree : st.scalar.core.ptrs 20 ≤ free := by dsimp [free]; split_ifs <;> omega
  have hFree : 128+32*((ell+2 : ℕ) : ℤ) ≤ free := pm.allocator.trans hOldFree
  have aI' : a.scalar.integerMemory=exteriorAdmittedIntegerPayload g logical ell boundary α t v free J st.scalar.core.mem := aI
  have aR' : a.scalar.core.mem=exteriorAdmittedRealPayload g logical ell α t v J st.scalar.core.mem := aR
  let memA := exterior_admitted_pending_memory m g ω logical s α ε ell length boundary st a pm hDepth t ht v J free u ea
    hFree hOldFree aFree a100 a0 jCache jFrame jBase aI' aR' hvNot hvDomain hSubset hCacheDomain ha hKeys hBoundary hBoundaryNext aRep aBelow aO
  have aMass : memA.queueMass=pm.queueMass := exterior_admitted_pending_memory_mass m g ω logical s α ε ell length boundary st a pm hDepth t ht v J free u ea
    hFree hOldFree aFree a100 a0 jCache jFrame jBase aI' aR' hvNot hvDomain hSubset hCacheDomain ha hKeys hBoundary hBoundaryNext aRep aBelow aO
  have keys (i : ℕ) (hi : i ≤ logical.top) :
      (memA.frames i (by rw [hNextTop]; exact hi)).exteriorObject.keys=(pm.frames i hi).exteriorObject.keys ∧
      (memA.frames i (by rw [hNextTop]; exact hi)).highObject.keys=(pm.frames i hi).highObject.keys :=
    exterior_admitted_pending_memory_keys m g ω logical s α ε ell length boundary st a pm hDepth t ht v J free u ea
      hFree hOldFree aFree a100 a0 jCache jFrame jBase aI' aR' hvNot hvDomain hSubset hCacheDomain ha hKeys hBoundary hBoundaryNext aRep aBelow aO i hi
  have activeD : ∀ i ≤ next.top, (next.frames i).active ⊆ parentDomain next i :=
    compiler_exterior_admission_active_domain g α logical t v ha hvDomain hSubset
  have extD : ∀ i ≤ next.top, (next.frames i).exterior ⊆ parentDomain next i := by
    intro i hi w hw
    exact ((hKeys i hi).1 w).mp hw |>.1
  have highD : ∀ i ≤ next.top, (next.frames i).high ⊆ parentDomain next i := by
    intro i hi w hw
    exact activeD i hi (((hKeys i hi).2 w).mp hw).1
  have extOutside : ∀ i, ∀ hi : i ≤ next.top,
      (next.frames i).exterior.image Fin.val \ (insert v (g.neighbors v).toFinset).image Fin.val ⊆ (memA.frames i hi).exteriorObject.keys := by
    intro i hi
    have hi' : i ≤ logical.top := by rw [←hNextTop]; exact hi
    rw [(keys i hi').1]
    exact (exterior_transition_queue_cover g α logical t v i _ _ (pm.frames i hi').exteriorCover (pm.frames i hi').highCover).1
  have highOutside : ∀ i, ∀ hi : i ≤ next.top,
      (next.frames i).high.image Fin.val \ (insert v (g.neighbors v).toFinset).image Fin.val ⊆ (memA.frames i hi).highObject.keys := by
    intro i hi
    have hi' : i ≤ logical.top := by rw [←hNextTop]; exact hi
    rw [(keys i hi').2]
    exact (exterior_transition_queue_cover g α logical t v i _ _ (pm.frames i hi').exteriorCover (pm.frames i hi').highCover).2
  have boolOutside : ∀ i ≤ next.top,
      HighBooleanRecords a.scalar.integerMemory a.scalar.core.mem width (16*(i+1)) (next.frames i).theta
        (parentDomain next i \ insert v (g.neighbors v).toFinset) := by
    intro i hi
    have hi' : i ≤ logical.top := by rw [←hNextTop]; exact hi
    apply exterior_transition_boolean_outside g α logical t v i width length st a _ (pm.frames i hi')
      (compiler_exterior_scalar_parameters g α logical t v i).2 (memA.frames i hi).activeFlags (memA.frames i hi).residual
    · intro w hw
      rw [aI',exteriorAdmittedIntegerPayload,exterior_activation_global_field g v (logical.frames 0).active boundary ell t logical.top free _ w.val 0 (by omega) (by omega) (by decide)]
      exact exterior_numeric_other_degrees g logical ell α t v _ J st.scalar.integerMemory st.scalar.core.mem _
        (by have := pm.allocator; omega) jFrame w hw
    · intro w hw
      rw [aR']
      apply exterior_admitted_other_boolean g logical ell α t i v w J st.scalar.core.mem hDepth ht hi'
      intro he
      subst w
      exact hw (Finset.mem_insert_self _ _)
  have budget : memA.queueMass+2*(next.top+1)*((g.neighbors v).length+1) ≤ N := by
    rw [aMass,hNextTop]
    exact hMass
  obtain ⟨r,out,memory,er,hr,rMass,r40,rQ,rW,rO,rH,rMarks⟩ := pending_touched_refresh_exec m g ω s α ε ell length N rank next
    a aH memA (by rw [hNextTop]; exact hDepth) activeD extD highD v
    (by rw [compiler_exterior_stored]; exact Finset.mem_insert_self _ _) a116 a40 a120 budget hCap hPow extOutside highOutside boolOutside
  have ex : MachineEval m g ω exteriorPushProgramCode st (u+r) out := MachineEval.seq ea er
  refine ⟨_,out,memory,ex,?_,?_,r40,ex.unit_work exteriorPushProgramCode_wellFormed (by decide) hh,rO.trans aO,rH,?_⟩
  · rw [hNextTop] at hr
    dsimp only [width]
    omega
  · simpa only [aMass,hNextTop] using rMass

  · intro w
    rw [rMarks w]
    rw [aI',exteriorAdmittedIntegerPayload,
      exterior_activation_global_field g v (logical.frames 0).active boundary ell t logical.top free _ w.val 7 (by omega) (by omega) (by decide)]
    exact exterior_numeric_integer_field_frame g logical ell α t v w _ J st.scalar.integerMemory st.scalar.core.mem _ jFrame
      (by have := pm.allocator; omega) 7 (by decide) (by omega)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorPushSimulation

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

set_option maxHeartbeats 15000000 in
lemma exterior_push_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank t boundary : ℕ) (v : Fin n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (ht : t ≤ logical.top) (hvDomain : v ∈ parentDomain logical t) (hvNot : v ∉ (logical.frames t).active)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hCacheDomain : ∀ i ≤ logical.top, (logical.frames i).cache ⊆ parentDomain logical i)
    (hSelected : st.scalar.core.ptrs 112=(t : ℤ)) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hBoundary : logical.boundaryEdges=(boundary : ℤ)) (hBoundaryNext : 0 ≤ (exteriorPush g α logical t v).boundaryEdges)
    (hKeys : KeysInvariant g (exteriorPush g α logical t v))
    (hMass : pm.queueMass+2*(logical.top+1)*((g.neighbors v).length+1) ≤ N) (hCap : rank < length) (hPow : N < 2^rank) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (exteriorPush g α logical t v) out,
      MachineEval m g ω exteriorPushProgramCode st steps out ∧
      steps ≤ exteriorPushBound ell logical.top rank (g.neighbors v).length ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*((g.neighbors v).length+1) ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ w : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) w.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) w.val 7)) := by
  classical
  by_cases ha : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8
  · exact exterior_activation_exec m g ω logical s α ε ell length N rank t boundary v st hh pm hDepth ht hvDomain hvNot
      hSubset hCacheDomain hSelected hv hBoundary hBoundaryNext ha hKeys hMass hCap hPow
  · obtain ⟨steps,out,memory,ex,hSteps,hQueue,h40,hWork,hOut,hHalt,hMarks⟩ :=
      exterior_nonactivation_exec m g ω logical s α ε ell length N rank t v st hh pm hDepth ht hvDomain hSubset hSelected hv ha hKeys hMass hCap hPow
    refine ⟨steps,out,memory,ex,?_,hQueue,h40,hWork,hOut,hHalt,hMarks⟩
    dsimp only [exteriorPushBound]
    have hProd : (g.neighbors v).length*((logical.top+1)*(8*(16*(ell+3))+39)+4*(16*(ell+3))+31) ≤
        (g.neighbors v).length*((logical.top+1)*(8*(16*(ell+3))+39)+8*(16*(ell+3))+50) :=
      Nat.mul_le_mul_left _ (by omega)
    omega


end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open NearlyOptimalPPR.Computation.SparseQueue
open scoped ENNReal
theorem solution : ∀ (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank t boundary : ℕ) (v : Fin n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (ht : t ≤ logical.top) (hvDomain : v ∈ parentDomain logical t) (hvNot : v ∉ (logical.frames t).active)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hCacheDomain : ∀ i ≤ logical.top, (logical.frames i).cache ⊆ parentDomain logical i)
    (hSelected : st.scalar.core.ptrs 112=(t : ℤ)) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hBoundary : logical.boundaryEdges=(boundary : ℤ)) (hBoundaryNext : 0 ≤ (exteriorPush g α logical t v).boundaryEdges)
    (hKeys : KeysInvariant g (exteriorPush g α logical t v))
    (hMass : pm.queueMass+2*(logical.top+1)*((g.neighbors v).length+1) ≤ N) (hCap : rank < length) (hPow : N < 2^rank),
∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (exteriorPush g α logical t v) out,
      MachineEval m g ω exteriorPushProgramCode st steps out ∧
      steps ≤ exteriorPushBound ell logical.top rank (g.neighbors v).length ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*((g.neighbors v).length+1) ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ w : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) w.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) w.val 7)) := by
  exact @NearlyOptimalPPR.Computation.exterior_push_exec
