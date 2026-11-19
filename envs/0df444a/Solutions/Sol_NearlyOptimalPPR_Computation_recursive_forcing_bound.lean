-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_forcing_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:01:17.023311+00:00
-- url     : https://prove2.me/submissions/3c5153e7-309a-4688-9d2b-5a6d2025e496

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}
lemma region_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    RegionInvariant (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).1

theorem root_identity_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    RootIdentity g s α (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).2.1

lemma layer_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    LayerIdentity g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).2.2.1

lemma root_threshold_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ((recursiveRun m g s α q ℓ schedule t).frames 0).q = q := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).2.2.2

lemma depth_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    (recursiveRun m g s α q ℓ schedule t).top ≤ ℓ := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).1

lemma budget_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    BudgetInvariant (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).2.1

lemma cache_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    CacheControlInvariant ℓ (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).2.2.1

lemma parameters_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ParameterInvariant (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).2.2.2 hq

lemma keys_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    KeysInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_queue_domains m n g s α q ℓ schedule t).1 hq

lemma isolate_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    IsolateResidual g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_queue_domains m n g s α q ℓ schedule t).2.1 hs

lemma stored_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    StoredInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_queue_domains m n g s α q ℓ schedule t).2.2 hq hs

lemma numerical_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    NumericalInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  exact recursive_numerical_invariants m n g s α q hα hq hs ℓ schedule t

end
end NearlyOptimalPPR.Computation


-- Proof module: Solutions.RegionInvariants

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

@[simp] lemma refresh_active (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).active = (st.frames i).active := by
  by_cases hi : i ≤ st.top <;> simp [refreshKeys,hi]

@[simp] lemma refresh_parentDomain (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    parentDomain (refreshKeys g st T) i = parentDomain st i := by
  unfold parentDomain
  split <;> simp

lemma parentDomain_same (st st' : RecursiveState n)
    (ha : ∀ i, (st'.frames i).active = (st.frames i).active) :
    ∀ i, parentDomain st' i = parentDomain st i := by
  intro i
  unfold parentDomain
  split <;> simp [ha]

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

-- Proof module: Solutions.LayerIdentity

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}


lemma raw_relative (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (δ : ℝ) (i : ℕ) (w : Fin n) :
    relative (rawExterior g α st t v δ) i w =
      relative st i w+(if w = v then δ else 0) := by
  classical
  by_cases hi : i = 0 <;> by_cases hw : w = v <;> by_cases ht : i ≤ st.top <;>
    simp [relative,rawExterior,hi,hw,ht] <;> ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VirtualRecords

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma virtual_actual (g : InputGraph n) (st : RecursiveState n) (j : ℕ) (v : Fin n)
    (hv : v ∈ parentDomain st j) :
    virtualPotential st j v = relative st j v ∧ virtualResidual g st j v = (st.frames j).residual v := by
  cases j with
  | zero => simp [virtualPotential,virtualReference,virtualResidual,relative]
  | succ j =>
    have hh : v ∈ (st.frames j).active := by simpa [parentDomain] using hv
    simp [virtualPotential,virtualReference,virtualResidual,relative,hh]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueueExterior

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma observe_changeFrame {β : Type*} (F : NormalizeFrame n → β) (st : RecursiveState n)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hf : F (f (st.frames j)) = F (st.frames j)) (i : ℕ) :
    F ((changeFrame st j f).frames i) = F (st.frames i) := by
  by_cases he : i = j
  · subst i
    simpa [changeFrame] using hf
  · simp [changeFrame,he]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameParameters

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
lemma exterior_parameters (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (i : ℕ) :
    frameParameters ((exteriorPush g α st t v).frames i) = frameParameters (st.frames i) := by
  classical
  let f := st.frames t
  let d := LocalPush.deg g.graph v
  let δ := min (f.residual v/(5*d)) (3*f.q/8-relative st t v)
  let base := rawExterior g α st t v δ
  let admitted := changeFrame base t (fun fi =>
    {fi with
      active := insert v fi.active
      residual := Function.update fi.residual v (fi.residual v+f.q*d/2)
      W := fi.W + if fi.openBudget then (t+3 : ℕ)*f.q*d/2 else 0})
  let child := if t < st.top then changeFrame admitted (t+1) (fun fc =>
    {fc with
      reference := Function.update fc.reference v (admitted.x v)
      residual := Function.update fc.residual v ((admitted.frames t).residual v)}) else admitted
  let final := if t = 0 then {child with boundaryEdges := st.boundaryEdges+
    (g.neighbors v).length-2*((g.neighbors v).filter (fun w => w ∈ f.active)).length} else child
  let prepared := if relative st t v+δ = 3*f.q/8 then final else base
  have hprepared (i : ℕ) : frameParameters (prepared.frames i) = frameParameters (st.frames i) := by
    have hb (i : ℕ) : frameParameters (base.frames i) = frameParameters (st.frames i) := by
      by_cases hh : i ≤ st.top <;> simp [base,rawExterior,hh,frameParameters]
    have ha (i : ℕ) : frameParameters (admitted.frames i) = frameParameters (st.frames i) := by
      exact (observe_changeFrame frameParameters base t _ rfl i).trans (hb i)
    have hc (i : ℕ) : frameParameters (child.frames i) = frameParameters (st.frames i) := by
      unfold child
      split
      · exact (observe_changeFrame frameParameters admitted (t+1) _ rfl i).trans (ha i)
      · exact ha i
    have hf (i : ℕ) : frameParameters (final.frames i) = frameParameters (st.frames i) := by
      unfold final
      split <;> exact hc i
    unfold prepared
    split
    · exact hf i
    · exact hb i
  have hrefresh : frameParameters ((refreshKeys g prepared (insert v (g.neighbors v).toFinset)).frames i) =
      frameParameters (prepared.frames i) := by
    by_cases hh : i ≤ prepared.top <;> simp [refreshKeys,hh,frameParameters]
  unfold exteriorPush frameParameters
  change frameParameters ((refreshKeys g prepared (insert v (g.neighbors v).toFinset)).frames i) = _
  exact hrefresh.trans (hprepared i)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorStages

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}


lemma admit_stage_fields (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
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

lemma raw_q (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ)
    (v : Fin n) (δ : ℝ) (i : ℕ) :
    ((rawExterior g α st t v δ).frames i).q = (st.frames i).q := by
  by_cases hi : i ≤ st.top <;> simp [rawExterior,hi]

lemma raw_active (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ)
    (v : Fin n) (δ : ℝ) (i : ℕ) :
    ((rawExterior g α st t v δ).frames i).active = (st.frames i).active := by
  by_cases hi : i ≤ st.top <;> simp [rawExterior,hi]

lemma exterior_stages (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)
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

-- Proof module: Solutions.VirtualReferenceTransport

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma virtualReference_transport (st u : RecursiveState n) (j : ℕ)
    (hq : ∀ i ≤ j, (u.frames i).q = (st.frames i).q)
    (hH : ∀ i ≤ j, (u.frames i).active = (st.frames i).active)
    (href : ∀ i ≤ j, (u.frames i).reference = (st.frames i).reference) :
    virtualReference u j = virtualReference st j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext v
    simp only [virtualReference]
    rw [hH j (by omega),href (j+1) le_rfl,hq j (by omega),
      ih (fun i hi => hq i (by omega)) (fun i hi => hH i (by omega)) (fun i hi => href i (by omega))]

lemma virtualReference_raw (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t j : ℕ) (v : Fin n) (δ : ℝ) :
    virtualReference (rawExterior g α st t v δ) j = virtualReference st j := by
  apply virtualReference_transport st (rawExterior g α st t v δ) j
  · intro i _; exact raw_q g α st t v δ i
  · intro i _; exact raw_active g α st t v δ i
  · intro i _; by_cases he : i ≤ st.top <;> simp [rawExterior,he]

lemma virtualReference_admit (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hvt : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active)
    (hcap : relative st t v = 3*(st.frames t).q/8) :
    ∀ j ≤ st.top, virtualReference (admitStage g st t v) j = virtualReference st j := by
  obtain ⟨htop,hx,hq,hθ,hC,hA,href,hr⟩ := admit_stage_fields g st t v
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hjs : j ≤ st.top := by omega
    funext w
    simp only [virtualReference]
    rw [hA j,hq j,ih hjs]
    by_cases hje : j = t
    · subst j
      simp only [ite_true]
      by_cases hw : w = v
      · subst w
        simp only [Finset.mem_insert_self,ite_true]
        rw [href]
        have htl : t < st.top := by omega
        simp only [htl,true_and,and_self,ite_true]
        simp only [hout,ite_false]
        have hh := (virtual_actual g st t v hvt).1
        unfold virtualPotential at hh
        linarith
      · have hcond : ¬(t < st.top ∧ t+1 = t+1 ∧ w = v) := by simp [hw]
        rw [href]
        simp [Finset.mem_insert,hw]
    · simp only [hje,ite_false]
      rw [href]
      have hcond : ¬(t < st.top ∧ j+1 = t+1 ∧ w = v) := by omega
      simp only [hcond,ite_false]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DepthInvariant

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma top_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).top = if P then a.top else b.top := by split <;> rfl
@[simp] lemma top_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) : (debit st j w).top = st.top := rfl
@[simp] lemma top_changeFrame (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).top = st.top := rfl
@[simp] lemma top_changePC (st : RecursiveState n) (pc : NormalizePC) : (changePC st pc).top = st.top := rfl
@[simp] lemma top_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).top = st.top := rfl
@[simp] lemma top_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    (jointUpdate g α st h).top = st.top := rfl
@[simp] lemma top_finish (st : RecursiveState n) : (finishEpisode st).top = st.top := rfl
@[simp] lemma top_complete (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α : ℝ) (st : RecursiveState n) : (completeComponent m g s α st).top = st.top := rfl
@[simp] lemma top_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    (endCall g α st).top = if st.top = 0 then st.top else st.top-1 := by
  unfold endCall
  dsimp only
  split <;> rfl
@[simp] lemma top_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) : (exteriorPush g α st t v).top = st.top := by
  simp [exteriorPush]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.PPRLinearAlgebra

set_option autoImplicit false
open Finset Matrix
open NearlyOptimalPPR.Computation

namespace NearlyOptimalPPR.Computation
variable {V : Type*} [Fintype V] [DecidableEq V]
local instance positive_adjacency (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (positiveGraph G).Adj :=
  inferInstanceAs (DecidableRel (G.induce {v | 0 < G.degree v}).Adj)

lemma lap_mul_apply (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (x : V → ℝ) (v : V) :
    (LocalPush.Lα G α *ᵥ x) v =
      LocalPush.deg G v * x v - (1 - α) * ∑ u ∈ G.neighborFinset v, x u := by
  simp [LocalPush.Lα, LocalPush.degM, LocalPush.adjM, sub_mulVec,
    smul_mulVec, SimpleGraph.adjMatrix_mulVec_apply, mulVec_diagonal]

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootControl

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma frame_pc_debit (st : RecursiveState n) (j i : ℕ) (w : ℝ≥0∞) :
    ((debit st j w).frames i).pc = (st.frames i).pc := by simp [debit]
@[simp] lemma frame_pc_refresh (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).pc = (st.frames i).pc := by
  by_cases he : i ≤ st.top <;> simp [refreshKeys,he]
@[simp] lemma frame_pc_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (i : ℕ) :
    ((jointUpdate g α st h).frames i).pc = (st.frames i).pc := by
  by_cases he : i ≤ st.top <;> simp [jointUpdate,he]
@[simp] lemma frame_pc_ite (P : Prop) [Decidable P] (a b : RecursiveState n) (i : ℕ) :
    ((if P then a else b).frames i).pc = if P then (a.frames i).pc else (b.frames i).pc := by
  split <;> rfl
@[simp] lemma frame_pc_changeFrame (st : RecursiveState n) (j i : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) :
    ((changeFrame st j f).frames i).pc =
      if i = j then (f (st.frames j)).pc else (st.frames i).pc := by
  by_cases he : i = j <;> simp [changeFrame,he]

@[simp] lemma frame_pc_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
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
    simp only [admitted,frame_pc_changeFrame]
    split <;> simp_all [hb]
  have hc (i : ℕ) : (child.frames i).pc = (st.frames i).pc := by
    unfold child
    split
    · simp only [frame_pc_changeFrame]
      split <;> simp_all [ha]
    · exact ha i
  have hf (i : ℕ) : (final.frames i).pc = (st.frames i).pc := by
    unfold final
    split <;> exact hc i
  unfold exteriorPush
  simp only [frame_pc_debit,frame_pc_refresh]
  change ((if relative st t v+h = 3*f.q/8 then final else base).frames i).pc = _
  split
  · exact hf i
  · exact hb i

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.MaximumBarrier

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma lap_max_left (g : InputGraph n) (α : ℝ) (hα : α ≤ 1) (x y : Fin n → ℝ)
    (v : Fin n) (hv : y v ≤ x v) :
    (LocalPush.Lα g.graph α *ᵥ (fun w => max (x w) (y w))) v ≤ (LocalPush.Lα g.graph α *ᵥ x) v := by
  rw [lap_mul_apply,lap_mul_apply,max_eq_left hv]
  have hs : (∑ w ∈ g.graph.neighborFinset v, x w) ≤
      ∑ w ∈ g.graph.neighborFinset v, max (x w) (y w) :=
    Finset.sum_le_sum (fun w _ => le_max_left _ _)
  have hh := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hα)
  linarith

lemma lap_max_upper (g : InputGraph n) (α : ℝ) (hα : α ≤ 1) (x y b : Fin n → ℝ)
    (hx : ∀ v, (LocalPush.Lα g.graph α *ᵥ x) v ≤ b v)
    (hy : ∀ v, (LocalPush.Lα g.graph α *ᵥ y) v ≤ b v) :
    ∀ v, (LocalPush.Lα g.graph α *ᵥ (fun w => max (x w) (y w))) v ≤ b v := by
  intro v
  by_cases hv : y v ≤ x v
  · exact (lap_max_left g α hα x y v hv).trans (hx v)
  · have hh := (lap_max_left g α hα y x v (le_of_not_ge hv)).trans (hy v)
    simpa only [max_comm] using hh

lemma lap_add_constant (g : InputGraph n) (α c : ℝ) (x : Fin n → ℝ) (v : Fin n) :
    (LocalPush.Lα g.graph α *ᵥ (fun w => x w+c)) v =
      (LocalPush.Lα g.graph α *ᵥ x) v+α*c*LocalPush.deg g.graph v := by
  rw [lap_mul_apply,lap_mul_apply,Finset.sum_add_distrib]
  simp only [Finset.sum_const,SimpleGraph.card_neighborFinset_eq_degree,nsmul_eq_mul]
  unfold LocalPush.deg
  ring

lemma potential_subsolution (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hroot : RootIdentity g s α st) (hnum : NumericalInvariant g st) (hq : 0 ≤ (st.frames 0).q) :
    ∀ v, (LocalPush.Lα g.graph α *ᵥ st.x) v ≤ LocalPush.e s v := by
  intro v
  have hn := (hnum 0 (Nat.zero_le _)).1 v (by simp [parentDomain])
  have hx : 0 ≤ st.x v := by simpa [relative] using hn.2.1
  have hh := hroot v
  have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
  have hc : 0 ≤ LocalPush.deg g.graph v*(if v ∈ (st.frames 0).active then (st.frames 0).q else 4*st.x v) := by
    apply mul_nonneg hd
    split <;> positivity
  unfold residual at hh
  simp only [Pi.sub_apply] at hh
  linarith [hn.1]

lemma forcing_max_lift (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α ∧ α ≤ 1)
    (x ξ : Fin n → ℝ) (S q : ℝ) (hS : 0 ≤ S) (hq : 0 ≤ q)
    (hx : ∀ v, (LocalPush.Lα g.graph α *ᵥ x) v ≤ LocalPush.e s v)
    (hξ : ∀ v, (LocalPush.Lα g.graph α *ᵥ ξ) v ≤ LocalPush.e s v+(3*α/8)*S*LocalPush.deg g.graph v) :
    ∀ v, (LocalPush.Lα g.graph α *ᵥ (fun w => max (x w) (ξ w+3*q/8))) v ≤
      LocalPush.e s v+(3*α/8)*(S+q)*LocalPush.deg g.graph v := by
  have ha0 : 0 ≤ α := hα.1
  apply lap_max_upper g α hα.2
  · intro v
    have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
    have hh : 0 ≤ (3*α/8)*(S+q)*LocalPush.deg g.graph v := by positivity
    exact (hx v).trans (le_add_of_nonneg_right hh)
  · intro v
    rw [lap_add_constant]
    have hh := hξ v
    nlinarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VirtualCaps

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma virtual_inactive_cap (g : InputGraph n) (st : RecursiveState n)
    (hnum : NumericalInvariant g st) (hp : ParameterInvariant st) :
    ∀ j ≤ st.top, ∀ v ∉ (st.frames j).active, virtualPotential st j v ≤ 3*(st.frames j).q/8 := by
  intro j
  induction j with
  | zero =>
    intro hj v hv
    have hdom : v ∈ parentDomain st 0 := by simp [parentDomain]
    rw [(virtual_actual g st 0 v hdom).1]
    exact (((hnum 0 hj).1 v hdom).2.2.2 hv).le
  | succ j ih =>
    intro hj v hv
    by_cases hdom : v ∈ parentDomain st (j+1)
    · rw [(virtual_actual g st (j+1) v hdom).1]
      exact (((hnum (j+1) hj).1 v hdom).2.2.2 hv).le
    · have hout : v ∉ (st.frames j).active := by simpa [parentDomain] using hdom
      have hh := ih (by omega) v hout
      have hq := (hp (j+1) hj).1.le
      unfold virtualPotential virtualReference
      simp only [hout,ite_false]
      unfold virtualPotential at hh
      linarith

lemma virtual_active_floor (g : InputGraph n) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hnum : NumericalInvariant g st)
    (j : ℕ) (hj : j ≤ st.top) (v : Fin n) (hv : v ∈ (st.frames j).active) :
    3*(st.frames j).q/8 ≤ virtualPotential st j v := by
  rw [(virtual_actual g st j v ((hreg j hj).1 hv)).1]
  exact ((hnum j hj).1 v ((hreg j hj).1 hv)).2.2.1 hv

lemma virtualReference_child_max (g : InputGraph n) (st u : RecursiveState n)
    (hreg : RegionInvariant st) (hnum : NumericalInvariant g st) (hp : ParameterInvariant st)
    (j : ℕ) (hj : j ≤ st.top)
    (hξ : virtualReference u j = virtualReference st j)
    (hq : (u.frames j).q = (st.frames j).q)
    (hH : (u.frames j).active = (st.frames j).active)
    (href : (u.frames (j+1)).reference = st.x) :
    virtualReference u (j+1) = fun v => max (st.x v) (virtualReference st j v+3*(st.frames j).q/8) := by
  funext v
  simp only [virtualReference]
  rw [hξ,hq,hH,href]
  by_cases hv : v ∈ (st.frames j).active
  · simp only [hv,ite_true]
    apply (max_eq_left _).symm
    have hh := virtual_active_floor g st hreg hnum j hj v hv
    unfold virtualPotential at hh
    linarith
  · simp only [hv,ite_false]
    apply (max_eq_right _).symm
    have hh := virtual_inactive_cap g st hnum hp j hj v hv
    unfold virtualPotential at hh
    linarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ReferenceData

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma referenceData_transport (st u : RecursiveState n) (j : ℕ)
    (hq : ∀ i ≤ j, (u.frames i).q = (st.frames i).q)
    (hH : ∀ i ≤ j, (u.frames i).active = (st.frames i).active)
    (href : ∀ i ≤ j, (u.frames i).reference = (st.frames i).reference) :
    referenceData u j = referenceData st j := by
  simp only [referenceData]
  apply Prod.ext
  · change thresholdSum u j = thresholdSum st j
    unfold thresholdSum
    apply Finset.sum_congr rfl
    intro i hi
    exact hq i (Nat.le_of_lt (Finset.mem_range.mp hi))
  · exact virtualReference_transport st u j hq hH href

lemma referenceData_frames (st u : RecursiveState n) (j : ℕ) (hf : u.frames = st.frames) :
    referenceData u j = referenceData st j := by
  apply referenceData_transport
  all_goals intro i _; rw [hf]

lemma referenceData_metadata (st : RecursiveState n) (k j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hq : (f (st.frames k)).q = (st.frames k).q)
    (hH : (f (st.frames k)).active = (st.frames k).active)
    (href : (f (st.frames k)).reference = (st.frames k).reference) :
    referenceData (changeFrame st k f) j = referenceData st j := by
  apply referenceData_transport
  · intro i _; exact observe_changeFrame (fun f => f.q) st k f hq i
  · intro i _; exact observe_changeFrame (fun f => f.active) st k f hH i
  · intro i _; exact observe_changeFrame (fun f => f.reference) st k f href i

lemma referenceData_metadata_trans (st u : RecursiveState n) (k j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hq : (f (u.frames k)).q = (u.frames k).q)
    (hH : (f (u.frames k)).active = (u.frames k).active)
    (href : (f (u.frames k)).reference = (u.frames k).reference)
    (hbase : referenceData u j = referenceData st j) :
    referenceData (changeFrame u k f) j = referenceData st j :=
  (referenceData_metadata u k j f hq hH href).trans hbase

lemma referenceData_episodes (st : RecursiveState n) (episodes : ℕ → ℕ) (j : ℕ) :
    referenceData {st with episodes := episodes} j = referenceData st j :=
  referenceData_frames st {st with episodes := episodes} j rfl
lemma referenceData_fullSolves (st : RecursiveState n) (fullSolves : ℕ → ℕ) (j : ℕ) :
    referenceData {st with fullSolves := fullSolves} j = referenceData st j :=
  referenceData_frames st {st with fullSolves := fullSolves} j rfl

lemma referenceData_PC (st : RecursiveState n) (pc : NormalizePC) (j : ℕ) :
    referenceData (changePC st pc) j = referenceData st j := referenceData_metadata st st.top j _ rfl rfl rfl
lemma referenceData_debit (st : RecursiveState n) (k j : ℕ) (w : ℝ≥0∞) :
    referenceData (debit st k w) j = referenceData st j := referenceData_frames st (debit st k w) j rfl

lemma referenceData_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) (j : ℕ) :
    referenceData (jointUpdate g α st h) j = referenceData st j := by
  apply referenceData_transport
  all_goals intro i _; by_cases hi : i ≤ st.top <;> simp [jointUpdate,hi]

lemma referenceData_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (j : ℕ) :
    referenceData (refreshKeys g st T) j = referenceData st j := by
  apply referenceData_transport
  all_goals intro i _; by_cases hi : i ≤ st.top <;> simp [refreshKeys,hi]

lemma referenceData_finish (st : RecursiveState n) (j : ℕ) :
    referenceData (finishEpisode st) j = referenceData st j := by
  apply referenceData_transport
  all_goals intro i _; by_cases hi : i = st.top <;> simp [finishEpisode,changeFrame,hi]

lemma referenceData_new (st : RecursiveState n) (c : NormalizeFrame n) (j : ℕ) (hj : j ≤ st.top) :
    referenceData {st with top := st.top+1,frames := Function.update st.frames (st.top+1) c} j = referenceData st j := by
  apply referenceData_transport
  all_goals intro i hi; have hn : i ≠ st.top+1 := by omega
  all_goals simp [hn]

lemma referenceData_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ) :
    referenceData (endCall g α st) j = referenceData st j := by
  unfold endCall
  dsimp only
  split <;> apply referenceData_frames <;> rfl

lemma virtualReference_debit (st : RecursiveState n) (k j : ℕ) (w : ℝ≥0∞) :
    virtualReference (debit st k w) j = virtualReference st j := by
  simpa only [referenceData] using congrArg Prod.snd (referenceData_debit st k j w)
lemma virtualReference_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (j : ℕ) :
    virtualReference (refreshKeys g st T) j = virtualReference st j := by
  simpa only [referenceData] using congrArg Prod.snd (referenceData_refresh g st T j)

lemma referenceData_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t j : ℕ) (hj : j ≤ st.top) (v : Fin n) (hvt : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active) :
    referenceData (exteriorPush g α st t v) j = referenceData st j := by
  classical
  simp only [referenceData]
  apply Prod.ext
  · change thresholdSum (exteriorPush g α st t v) j = thresholdSum st j
    unfold thresholdSum
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun z => z.1) (exterior_parameters g α st t v i)
  · let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
        (3*(st.frames t).q/8-relative st t v)
    let base := rawExterior g α st t v δ
    have hA (i : ℕ) := raw_active g α st t v δ i
    have hU := parentDomain_same st base hA
    have hvt' : v ∈ parentDomain base t := by simpa [hU t] using hvt
    have hout' : v ∉ (base.frames t).active := by
      change v ∉ ((rawExterior g α st t v δ).frames t).active
      rw [raw_active]
      exact hout
    have hq := raw_q g α st t v δ t
    rw [exterior_stages,virtualReference_debit,virtualReference_refresh]
    simp only [←show δ = min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v) from rfl]
    by_cases ha : relative st t v+δ = 3*(st.frames t).q/8
    · rw [if_pos ha]
      have hcap : relative base t v = 3*(base.frames t).q/8 := by rw [raw_relative,hq]; simpa using ha
      rw [virtualReference_admit g base t v hvt' hout' hcap j hj]
      exact virtualReference_raw g α st t j v δ
    · rw [if_neg ha]
      exact virtualReference_raw g α st t j v δ

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ReferenceDataStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma referenceData_pending (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hreg : RegionInvariant st)
    (j : ℕ) (hj : j ≤ st.top) (t : ℕ) (v : Fin n) (hp : pendingPush st = some (t,v)) :
    referenceData (exteriorPush g α st t v) j = referenceData st j := by
  obtain ⟨ht,hm⟩ := pending_push_member st t v hp
  obtain ⟨hv,hout⟩ := Finset.mem_sdiff.mp ((hreg t ht).2.1 hm)
  exact referenceData_exterior g α st t j hj v hv hout

lemma referenceData_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hreg : RegionInvariant st)
    (j : ℕ) (hj : j ≤ st.top) (pc : NormalizePC) :
    referenceData (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) j = referenceData st j := by
  split
  · rw [referenceData_PC,referenceData_debit]
  · cases hp : pendingPush st with
    | none => rw [referenceData_PC,referenceData_debit]
    | some p => obtain ⟨t,v⟩ := p; exact referenceData_pending g α st hreg j hj t v hp

set_option maxHeartbeats 1500000 in
lemma referenceData_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hreg : RegionInvariant st)
    (j : ℕ) (hj : j ≤ st.top) :
    referenceData (recursiveStep m g s α ℓ schedule st) j = referenceData st j := by
  classical
  by_cases hd : st.done = true
  · simp only [recursiveStep,hd,ite_true]
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hcomp : componentComplete st
  · simp only [hcomp,ite_true]
    apply referenceData_frames
    rfl
  simp only [hcomp,ite_false]
  have hdrain := referenceData_drain g α st hreg j hj
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · rw [referenceData_PC,referenceData_debit]
    · split
      · exact hdrain _
      · split <;> rw [referenceData_PC,referenceData_debit]
  | beginEpisode =>
    simp only [hpc]
    apply referenceData_metadata_trans st
    · rfl
    · rfl
    · rfl
    · rw [referenceData_episodes,referenceData_debit]
  | fullSolve =>
    simp only [hpc]
    split
    · rw [referenceData_PC,referenceData_debit]
    · split
      · rw [referenceData_PC,referenceData_fullSolves,referenceData_debit,referenceData_refresh,referenceData_joint]
      · exact referenceData_debit st st.top j 1
  | normalize =>
    simp only [hpc]
    split
    · rw [referenceData_PC,referenceData_debit]
    · split
      · rw [referenceData_PC,referenceData_debit]
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild,childrenThisEpisode := fc.childrenThisEpisode+1})
        trans referenceData {up with top := st.top+1,frames := Function.update up.frames (st.top+1) c} j
        · apply referenceData_frames
          rfl
        · have hh : j ≤ up.top := hj
          change referenceData {up with top := up.top+1,frames := Function.update up.frames (up.top+1) c} j = referenceData st j
          rw [referenceData_new up c j hh]
          apply referenceData_metadata_trans st
          · rfl
          · rfl
          · rfl
          · exact referenceData_debit st st.top j _
  | leafDrain =>
    simp only [hpc]
    split
    · rw [referenceData_PC,referenceData_debit]
    · split
      · cases hp : pendingPush st with
        | none => rw [referenceData_PC,referenceData_debit]
        | some p => obtain ⟨t,v⟩ := p; exact referenceData_pending g α st hreg j hj t v hp
      · split
        · rw [referenceData_PC,referenceData_debit]
        · split
          · rw [referenceData_debit,referenceData_refresh,referenceData_joint]
            apply referenceData_metadata
            · rfl
            · rfl
            · rfl
          · exact referenceData_debit st st.top j 1
  | afterChild =>
    simp only [hpc]
    split
    · rw [referenceData_PC,referenceData_finish,referenceData_debit]
    · split
      · rw [referenceData_PC,referenceData_finish,referenceData_debit]
      · exact hdrain _
  | finishEpisode =>
    simp only [hpc]
    split
    · rw [referenceData_PC,referenceData_finish,referenceData_debit]
    · split
      · rw [referenceData_PC,referenceData_finish,referenceData_debit]
      · apply referenceData_metadata_trans st
        · rfl
        · rfl
        · rfl
        · rw [referenceData_finish,referenceData_debit]
  | restartDrain =>
    simp only [hpc]
    split
    · rw [referenceData_PC,referenceData_debit]
    · split
      · exact hdrain _
      · apply referenceData_metadata_trans st
        · rfl
        · rfl
        · rfl
        · exact referenceData_debit st st.top j 1
  | normal => simp only [hpc]; rw [referenceData_end,referenceData_debit]
  | interrupted => simp only [hpc]; rw [referenceData_end,referenceData_debit]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.GrowingStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
lemma growing_step_pc (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hg : st.top < (recursiveStep m g s α ℓ schedule st).top) :
    (st.frames st.top).pc = .normalize := by
  classical
  by_contra hn
  cases hp : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hp,hn] at hg <;> (try split_ifs at hg) <;> simp_all <;> omega
  | some p =>
    obtain ⟨t,v⟩ := p
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hp,hn] at hg <;> (try split_ifs at hg) <;> simp_all <;> omega

lemma growing_step_guards (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hg : st.top < (recursiveStep m g s α ℓ schedule st).top) :
    st.done = false ∧ ¬componentComplete st ∧ (st.frames st.top).pc = .normalize ∧
      ¬anyExhausted st ∧ st.top ≠ ℓ := by
  classical
  have hd : st.done = false := by
    cases h : st.done
    · rfl
    · simp [recursiveStep,h] at hg
  have hc : ¬componentComplete st := by
    intro hh
    simp [recursiveStep,hd,hh] at hg
  have hp := growing_step_pc m g s α ℓ schedule st hg
  have he : ¬anyExhausted st := by
    intro hh
    simp [recursiveStep,hd,hc,hp,hh] at hg
  have hl : st.top ≠ ℓ := by
    intro hh
    subst ℓ
    simp [recursiveStep,hd,hc,hp,he] at hg
  exact ⟨hd,hc,hp,he,hl⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ForcingInvariant

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma thresholdSum_nonnegative (st : RecursiveState n) (hp : ParameterInvariant st) (j : ℕ) (hj : j ≤ st.top) :
    0 ≤ thresholdSum st j := by
  apply Finset.sum_nonneg
  intro i hi
  exact (hp i ((Nat.le_of_lt (Finset.mem_range.mp hi)).trans hj)).1.le

lemma forcing_transport (g : InputGraph n) (s : Fin n) (α : ℝ) (st u : RecursiveState n)
    (hi : ForcingInvariant g s α st) (ht : u.top ≤ st.top)
    (hdata : ∀ j ≤ u.top, referenceData u j = referenceData st j) : ForcingInvariant g s α u := by
  intro j hj v
  have hS : thresholdSum u j = thresholdSum st j := congrArg Prod.fst (hdata j hj)
  have hξ : virtualReference u j = virtualReference st j := congrArg Prod.snd (hdata j hj)
  rw [hS,hξ]
  exact hi j (hj.trans ht) v

lemma forcing_new_level (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α ∧ α ≤ 1)
    (st u : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hnum : NumericalInvariant g st) (hp : ParameterInvariant st) (hi : ForcingInvariant g s α st)
    (hξ : virtualReference u st.top = virtualReference st st.top)
    (hq : (u.frames st.top).q = (st.frames st.top).q)
    (hH : (u.frames st.top).active = (st.frames st.top).active)
    (href : (u.frames (st.top+1)).reference = st.x)
    (hS : thresholdSum u (st.top+1) = thresholdSum st st.top+(st.frames st.top).q) :
    ∀ v, (LocalPush.Lα g.graph α *ᵥ virtualReference u (st.top+1)) v ≤
      LocalPush.e s v+(3*α/8)*thresholdSum u (st.top+1)*LocalPush.deg g.graph v := by
  rw [virtualReference_child_max g st u hreg hnum hp st.top le_rfl hξ hq hH href,hS]
  exact forcing_max_lift g s α hα st.x (virtualReference st st.top) (thresholdSum st st.top) (st.frames st.top).q
    (thresholdSum_nonnegative st hp st.top le_rfl) (hp st.top le_rfl).1.le
    (potential_subsolution g s α st hroot hnum (hp 0 (Nat.zero_le _)).1.le) (hi st.top le_rfl)

lemma forcing_init (g : InputGraph n) (s : Fin n) (α q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    ForcingInvariant g s α (recursiveInit g s q ℓ schedule) := by
  intro j hj v
  have hz : j = 0 := by change j ≤ 0 at hj; omega
  subst j
  simp [virtualReference,thresholdSum,LocalPush.e,Pi.single_apply,
    show (fun _ : Fin n => (0 : ℝ)) = 0 from rfl] <;> split_ifs <;> norm_num

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ForcingStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
lemma forcing_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α ∧ α ≤ 1)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hroot : RootIdentity g s α st) (hnum : NumericalInvariant g st)
    (hp : ParameterInvariant st) (hi : ForcingInvariant g s α st) :
    ForcingInvariant g s α (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hle : (recursiveStep m g s α ℓ schedule st).top ≤ st.top
  · apply forcing_transport g s α st _ hi hle
    intro j hj
    exact referenceData_step m g s α ℓ schedule st hreg j (hj.trans hle)
  · have hg : st.top < (recursiveStep m g s α ℓ schedule st).top := Nat.lt_of_not_ge hle
    obtain ⟨hd,hcomp,hpc,hex,hlevel⟩ := growing_step_guards m g s α ℓ schedule st hg
    let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
      (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
    let pre := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
      8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
    let up := changeFrame pre st.top (fun f => {f with pc := .afterChild,childrenThisEpisode := f.childrenThisEpisode+1})
    let next : RecursiveState n :=
      { up with
        top := st.top+1
        nextId := st.nextId+1
        frames := Function.update up.frames (st.top+1) c
        information := Function.update up.information c.id (some ⟨st.top+1,(st.frames st.top).block,c.block⟩) }
    have hnext : recursiveStep m g s α ℓ schedule st = next := by
      simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hcomp,hpc,hex,hlevel]
      rfl
    have hdata (j : ℕ) (hj : j ≤ st.top) : referenceData next j = referenceData st j := by
      rw [←hnext]
      exact referenceData_step m g s α ℓ schedule st hreg j hj
    have hξ : virtualReference next st.top = virtualReference st st.top := congrArg Prod.snd (hdata st.top le_rfl)
    have hS : thresholdSum next st.top = thresholdSum st st.top := congrArg Prod.fst (hdata st.top le_rfl)
    have hq : (next.frames st.top).q = (st.frames st.top).q := by
      simp [next,up,pre,changeFrame,debit]
    have hH : (next.frames st.top).active = (st.frames st.top).active := by
      simp [next,up,pre,changeFrame,debit]
    have href : (next.frames (st.top+1)).reference = st.x := by simp [next,c,freshFrame]
    have hsum : thresholdSum next (st.top+1) = thresholdSum st st.top+(st.frames st.top).q := by
      have hh : thresholdSum next (st.top+1) = thresholdSum next st.top+(next.frames st.top).q := by
        simp [thresholdSum,Finset.sum_range_succ]
      rw [hh,hS,hq]
    rw [hnext]
    intro j hj v
    by_cases hjs : j ≤ st.top
    · have hSj : thresholdSum next j = thresholdSum st j := congrArg Prod.fst (hdata j hjs)
      have hξj : virtualReference next j = virtualReference st j := congrArg Prod.snd (hdata j hjs)
      rw [hSj,hξj]
      exact hi j hjs v
    · have hje : j = st.top+1 := by change j ≤ st.top+1 at hj; omega
      subst j
      exact forcing_new_level g s α hα st next hreg hroot hnum hp hi hξ hq hH href hsum v

lemma forcing_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ForcingInvariant g s α (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using forcing_init g s α q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using forcing_step m g s α ⟨hα.1.le,hα.2.le⟩ ℓ schedule _
      (region_run m g s α q ℓ schedule t) (root_identity_run m g s α q ℓ schedule t)
      (numerical_run m g s α q hα hq hs ℓ schedule t) (parameters_run m g s α q hq ℓ schedule t) ih

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open NearlyOptimalPPR.Computation

theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ForcingInvariant g s α (recursiveRun m g s α q ℓ schedule t) := by
  exact forcing_run m g s α q hα hq hs ℓ schedule t


