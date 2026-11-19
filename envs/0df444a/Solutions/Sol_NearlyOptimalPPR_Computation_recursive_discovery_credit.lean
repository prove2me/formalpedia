-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_discovery_credit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T10:58:05.273502+00:00
-- url     : https://prove2.me/submissions/87afb86e-b24c-4eac-bbc3-8a9d6703436a

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

lemma active_subset_root (st : RecursiveState n) (hi : RegionInvariant st)
    (j : ℕ) (hj : j ≤ st.top) : (st.frames j).active ⊆ (st.frames 0).active := by
  induction j with
  | zero => exact Finset.Subset.refl _
  | succ j ih =>
    have hh := (hi (j+1) hj).1
    have hp : parentDomain st (j+1) = (st.frames j).active := by simp [parentDomain]
    rw [hp] at hh
    exact hh.trans (ih (Nat.le_of_succ_le hj))

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

lemma region_same (st st' : RecursiveState n) (ht : st'.top = st.top)
    (ha : ∀ i, (st'.frames i).active = (st.frames i).active)
    (he : ∀ i, (st'.frames i).exterior = (st.frames i).exterior)
    (hh : ∀ i, (st'.frames i).high = (st.frames i).high)
    (hc : ∀ i, (st'.frames i).cache ⊆ (st.frames i).cache)
    (hi : RegionInvariant st) : RegionInvariant st' := by
  intro i hle
  rw [ht] at hle
  have h := hi i hle
  rw [ha, he, hh, parentDomain_same st st' ha]
  exact ⟨h.1,h.2.1,h.2.2.1,(hc i).trans h.2.2.2⟩

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

-- Proof module: Solutions.RootIdentityControl

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma solveOn_outside (g : InputGraph n) (α : ℝ) (T : Finset (Fin n))
    (b : Fin n → ℝ) (v : Fin n) (hv : v ∉ T) : solveOn g α T b v = 0 := by
  classical
  simp [solveOn,hv]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LayerIdentity

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}


lemma active_subset_between (st : RecursiveState n) (hr : RegionInvariant st)
    (a b : ℕ) (hab : a ≤ b) (hbt : b ≤ st.top) :
    (st.frames b).active ⊆ (st.frames a).active := by
  induction b with
  | zero =>
    have he : a = 0 := by omega
    subst a
    exact Finset.Subset.refl _
  | succ b ih =>
    by_cases he : a = b+1
    · subst a; exact Finset.Subset.refl _
    · have hh := (hr (b+1) hbt).1
      have hp : parentDomain st (b+1) = (st.frames b).active := by simp [parentDomain]
      rw [hp] at hh
      exact hh.trans (ih (by omega) (by omega))


lemma raw_relative (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (δ : ℝ) (i : ℕ) (w : Fin n) :
    relative (rawExterior g α st t v δ) i w =
      relative st i w+(if w = v then δ else 0) := by
  classical
  by_cases hi : i = 0 <;> by_cases hw : w = v <;> by_cases ht : i ≤ st.top <;>
    simp [relative,rawExterior,hi,hw,ht] <;> ring

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

-- Proof module: Solutions.GraphCut

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma neighbor_degree (g : InputGraph n) (v : Fin n) :
    (g.neighbors v).length = g.graph.degree v := by
  have he : (g.neighbors v).toFinset = g.graph.neighborFinset v := by
    ext u
    simp [g.correct]
  rw [← List.toFinset_card_of_nodup (g.nodup v),he,SimpleGraph.card_neighborFinset_eq_degree]

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

@[simp] lemma boundary_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    (debit st j w).boundaryEdges = st.boundaryEdges := rfl
@[simp] lemma boundary_changeFrame (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).boundaryEdges = st.boundaryEdges := rfl
@[simp] lemma boundary_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).boundaryEdges = st.boundaryEdges := rfl
@[simp] lemma active_debit (st : RecursiveState n) (j i : ℕ) (w : ℝ≥0∞) :
    ((debit st j w).frames i).active = (st.frames i).active := by
  classical
  simp [debit]
@[simp] lemma active_changeFrame (st : RecursiveState n) (j i : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) :
    ((changeFrame st j f).frames i).active =
      if i = j then (f (st.frames j)).active else (st.frames i).active := by
  classical
  by_cases h : i = j <;> simp [changeFrame,h]
@[simp] lemma active_refresh (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).active = (st.frames i).active := by
  classical
  by_cases h : i ≤ st.top <;> simp [refreshKeys,h]

@[simp] lemma boundary_id_debit (g : InputGraph n) (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    BoundaryIdentity g (debit st j w) ↔ BoundaryIdentity g st := by
  simp [BoundaryIdentity]

@[simp] lemma boundary_id_changeFrame (g : InputGraph n) (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hf : (f (st.frames j)).active = (st.frames j).active) :
    BoundaryIdentity g (changeFrame st j f) ↔ BoundaryIdentity g st := by
  by_cases he : (0 : ℕ) = j <;> simp_all (config := {maxSteps := 500000}) [BoundaryIdentity]

@[simp] lemma boundary_id_changePC (g : InputGraph n) (st : RecursiveState n) (pc : NormalizePC) :
    BoundaryIdentity g (changePC st pc) ↔ BoundaryIdentity g st :=
  boundary_id_changeFrame g st st.top _ rfl

@[simp] lemma boundary_id_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    BoundaryIdentity g (refreshKeys g st T) ↔ BoundaryIdentity g st := by simp [BoundaryIdentity]

@[simp] lemma boundary_id_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    BoundaryIdentity g (jointUpdate g α st h) ↔ BoundaryIdentity g st := by
  simp [BoundaryIdentity,jointUpdate]

@[simp] lemma boundary_id_finish (g : InputGraph n) (st : RecursiveState n) :
    BoundaryIdentity g (finishEpisode st) ↔ BoundaryIdentity g st := by
  by_cases he : (0 : ℕ) = st.top <;> simp [finishEpisode,BoundaryIdentity,he]

@[simp] lemma boundary_id_complete (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α : ℝ) (st : RecursiveState n) :
    BoundaryIdentity g (completeComponent m g s α st) ↔ BoundaryIdentity g st := Iff.rfl

@[simp] lemma boundary_id_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    BoundaryIdentity g (endCall g α st) ↔ BoundaryIdentity g st := by
  unfold endCall
  dsimp only
  split <;> rfl

@[simp] lemma active_ite (P : Prop) [Decidable P] (a b : RecursiveState n) (i : ℕ) :
    ((if P then a else b).frames i).active =
      if P then (a.frames i).active else (b.frames i).active := by split <;> rfl
@[simp] lemma boundary_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).boundaryEdges = if P then a.boundaryEdges else b.boundaryEdges := by split <;> rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredInvariant

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

@[simp] lemma stored_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).stored = if P then a.stored else b.stored := by split <;> rfl

lemma exterior_stored (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) : (exteriorPush g α st t v).stored = insert v st.stored := by
  simp [exteriorPush,refreshKeys,debit,changeFrame]

set_option maxHeartbeats 1000000 in
lemma exterior_active (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (i : ℕ) :
    let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)
    ((exteriorPush g α st t v).frames i).active =
      if relative st t v+δ = 3*(st.frames t).q/8 ∧ i = t then insert v (st.frames i).active
      else (st.frames i).active := by
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
  have hb (i : ℕ) : (base.frames i).active = (st.frames i).active := by
    by_cases hh : i ≤ st.top <;> simp [base,rawExterior,hh]
  have ha (i : ℕ) : (admitted.frames i).active =
      if i = t then insert v (st.frames i).active else (st.frames i).active := by
    simp only [admitted,active_changeFrame]
    by_cases hh : i = t <;> simp [hh,hb]
  have hc (i : ℕ) : (child.frames i).active = (admitted.frames i).active := by
    unfold child
    split
    · exact observe_changeFrame (fun f => f.active) admitted (t+1) _ rfl i
    · rfl
  have hf (i : ℕ) : (final.frames i).active = (admitted.frames i).active := by
    unfold final
    split <;> exact hc i
  have hp (i : ℕ) : (prepared.frames i).active =
      if relative st t v+δ = 3*f.q/8 ∧ i = t then insert v (st.frames i).active
      else (st.frames i).active := by
    unfold prepared
    split
    · rename_i hh
      rw [hf,ha]
      simp [hh]
    · rename_i hh
      rw [hb]
      simp [hh]
  dsimp only
  unfold exteriorPush
  simp only [active_debit,active_refresh]
  change (prepared.frames i).active = _
  exact hp i

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IsolateResidual

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma isolate_pending_positive (g : InputGraph n) (st : RecursiveState n)
    (hi : IsolateResidual g st) (hk : KeysInvariant g st)
    (t : ℕ) (v : Fin n) (hp : pendingPush st = some (t,v)) : 0 < g.graph.degree v := by
  obtain ⟨ht,hm⟩ := pending_push_member st t v hp
  have hh := ((hk t ht).1 v).mp hm
  by_contra hn
  have hz : g.graph.degree v = 0 := by omega
  have hr := hi t ht v hz
  have hf := hh.2.2
  rw [hr] at hf
  simp [LocalPush.deg,hz] at hf

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CrossingPush

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma crossing_push_bounds (d q r y : ℝ) (hd : 0 < d) (hq : 0 < q)
    (hr : 0 ≤ r) (hy : 0 ≤ y ∧ y ≤ 3*q/8) :
    let δ := min (r/(5*d)) (3*q/8-y)
    0 ≤ δ ∧ 0 ≤ r-5*d*δ ∧ 0 ≤ y+δ ∧ y+δ ≤ 3*q/8 := by
  dsimp only
  have hden : 0 < 5*d := by positivity
  have hδ : 0 ≤ min (r/(5*d)) (3*q/8-y) :=
    le_min (div_nonneg hr hden.le) (sub_nonneg.mpr hy.2)
  have hres := (le_div_iff₀ hden).mp (min_le_left (r/(5*d)) (3*q/8-y))
  have hcap := min_le_right (r/(5*d)) (3*q/8-y)
  refine ⟨hδ,?_,by linarith,by linarith⟩
  nlinarith

lemma nonactivating_push_clears (d q r y : ℝ)
    (hn : y+min (r/(5*d)) (3*q/8-y) ≠ 3*q/8) :
    min (r/(5*d)) (3*q/8-y) = r/(5*d) := by
  by_cases hh : r/(5*d) ≤ 3*q/8-y
  · exact min_eq_left hh
  · have he := min_eq_right (le_of_not_ge hh)
    exfalso
    apply hn
    rw [he]
    ring

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NumericalRaw

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma parent_domain_nested (st : RecursiveState n) (hreg : RegionInvariant st)
    (a b : ℕ) (hab : a < b) (hbt : b ≤ st.top) : parentDomain st b ⊆ (st.frames a).active := by
  have hb : b ≠ 0 := by omega
  rw [parentDomain,if_neg hb]
  exact active_subset_between st hreg a (b-1) (by omega) (by omega)

lemma inactive_push_level (st : RecursiveState n) (hreg : RegionInvariant st)
    (t i : ℕ) (ht : t ≤ st.top) (hi : i ≤ st.top) (v : Fin n)
    (hvt : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active)
    (hvi : v ∈ parentDomain st i) (hoi : v ∉ (st.frames i).active) : i = t := by
  by_contra he
  by_cases hlt : i < t
  · exact hoi (parent_domain_nested st hreg i t hlt ht hvt)
  · exact hout (parent_domain_nested st hreg t i (by omega) hi hvi)

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

lemma admit_domain (g : InputGraph n) (st : RecursiveState n) (t i : ℕ) (v w : Fin n) :
    w ∈ parentDomain (admitStage g st t v) i ↔
      w ∈ parentDomain st i ∨ i = t+1 ∧ w = v := by
  classical
  have hA := (admit_stage_fields g st t v).2.2.2.2.2.1
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

lemma admit_relative (g : InputGraph n) (st : RecursiveState n) (t i : ℕ) (v w : Fin n) :
    relative (admitStage g st t v) i w =
      if t < st.top ∧ i = t+1 ∧ w = v then 0 else relative st i w := by
  classical
  obtain ⟨ht,hx,hq,hθ,hC,hA,href,hr⟩ := admit_stage_fields g st t v
  by_cases hz : i = 0
  · subst i
    simp [relative,hx]
  · unfold relative
    simp only [hz,ite_false,hx]
    rw [href]
    split
    · rename_i hh
      obtain ⟨_,_,he⟩ := hh
      subst w
      simp
    · rfl

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

-- Proof module: Solutions.RootMass

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma volume_real (g : InputGraph n) (H : Finset (Fin n)) :
    (volumeNat g H : ℝ) = ∑ v ∈ H, LocalPush.deg g.graph v := by
  simp [volumeNat,LocalPush.deg,neighbor_degree]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DiscoveryCredit

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma discoveryCredit_as_sum_of_subset (g : InputGraph n) (st : RecursiveState n)
    (j : ℕ) (hsub : (st.frames j).active ⊆ parentDomain st j) :
    discoveryCredit g st j = ∑ v ∈ parentDomain st j,
      if v ∈ (st.frames j).active then 3*(st.frames j).q/8*LocalPush.deg g.graph v
      else LocalPush.deg g.graph v*relative st j v := by
  classical
  let f := fun v => if v ∈ (st.frames j).active then 3*(st.frames j).q/8*LocalPush.deg g.graph v
      else LocalPush.deg g.graph v*relative st j v
  have hactive : (∑ v ∈ (st.frames j).active, f v) =
      3*(st.frames j).q/8*(volumeNat g (st.frames j).active : ℝ) := by
    rw [volume_real,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    simp [f,hv]
  have houtside : (∑ v ∈ parentDomain st j \ (st.frames j).active, f v) =
      ∑ v ∈ parentDomain st j \ (st.frames j).active, LocalPush.deg g.graph v*relative st j v := by
    apply Finset.sum_congr rfl
    intro v hv
    simp [f,(Finset.mem_sdiff.mp hv).2]
  have he := Finset.sum_sdiff (f := f) hsub
  rw [hactive,houtside] at he
  unfold discoveryCredit
  change _ = ∑ v ∈ parentDomain st j, f v
  linarith

lemma discoveryCredit_as_sum (g : InputGraph n) (st : RecursiveState n)
    (hreg : RegionInvariant st) (j : ℕ) (hj : j ≤ st.top) :
    discoveryCredit g st j = ∑ v ∈ parentDomain st j,
      if v ∈ (st.frames j).active then 3*(st.frames j).q/8*LocalPush.deg g.graph v
      else LocalPush.deg g.graph v*relative st j v :=
  discoveryCredit_as_sum_of_subset g st j ((hreg j hj).1)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DiscoveryRaw

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma discoveryCredit_raw (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (t j : ℕ) (ht : t ≤ st.top) (hj : j ≤ st.top)
    (v : Fin n) (hvt : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active) (δ : ℝ) :
    discoveryCredit g (rawExterior g α st t v δ) j = discoveryCredit g st j+
      (if j = t then LocalPush.deg g.graph v*δ else 0) := by
  classical
  have hA (i : ℕ) : ((rawExterior g α st t v δ).frames i).active = (st.frames i).active := raw_active g α st t v δ i
  have hU := parentDomain_same st (rawExterior g α st t v δ) hA
  have hm : v ∈ parentDomain st j \ (st.frames j).active ↔ j = t := by
    constructor
    · intro hv
      obtain ⟨hdom,houtj⟩ := Finset.mem_sdiff.mp hv
      exact inactive_push_level st hreg t j ht hj v hvt hout hdom houtj
    · intro he
      subst j
      exact Finset.mem_sdiff.mpr ⟨hvt,hout⟩
  unfold discoveryCredit
  rw [raw_q,hA j,hU j]
  simp only [raw_relative,mul_add,mul_ite,mul_zero]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq']
  simp only [hm]
  ring

lemma discoveryCredit_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ)
    (j : ℕ) (hs : ∀ v ∈ parentDomain st j \ (st.frames j).active, h v = 0) :
    discoveryCredit g (jointUpdate g α st h) j = discoveryCredit g st j := by
  classical
  have hq (i : ℕ) : ((jointUpdate g α st h).frames i).q = (st.frames i).q := by
    by_cases hi : i ≤ st.top <;> simp [jointUpdate,hi]
  have hA (i : ℕ) : ((jointUpdate g α st h).frames i).active = (st.frames i).active := by
    by_cases hi : i ≤ st.top <;> simp [jointUpdate,hi]
  have hU := parentDomain_same st (jointUpdate g α st h) hA
  unfold discoveryCredit
  rw [hq,hA j,hU j]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  have hh := hs v hv
  have href : ((jointUpdate g α st h).frames j).reference = (st.frames j).reference := by
    by_cases hi : j ≤ st.top <;> simp [jointUpdate,hi]
  unfold relative
  rw [href]
  by_cases hz : j = 0 <;> simp [hz,jointUpdate,Pi.add_apply,hh]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DiscoveryAdmission

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma discoveryCredit_admit (g : InputGraph n) (st : RecursiveState n) (hreg : RegionInvariant st)
    (t j : ℕ) (ht : t ≤ st.top) (hj : j ≤ st.top) (v : Fin n)
    (hvt : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active)
    (hcap : relative st t v = 3*(st.frames t).q/8) :
    discoveryCredit g (admitStage g st t v) j = discoveryCredit g st j := by
  classical
  obtain ⟨htop,hx,hq,hθ,hC,hA,hrest⟩ := admit_stage_fields g st t v
  have hU : parentDomain (admitStage g st t v) j =
      if j = t+1 then insert v (parentDomain st j) else parentDomain st j := by
    ext w
    by_cases he : j = t+1 <;> simp [admit_domain,he,or_comm]
  have hsub : ((admitStage g st t v).frames j).active ⊆ parentDomain (admitStage g st t v) j := by
    intro w hw
    rw [hA j] at hw
    apply (admit_domain g st t j v w).mpr
    left
    by_cases he : j = t
    · subst j
      simp only [ite_true] at hw
      obtain rfl|hw := Finset.mem_insert.mp hw
      · exact hvt
      · exact (hreg t ht).1 hw
    · exact (hreg j hj).1 (by simpa [he] using hw)
  rw [discoveryCredit_as_sum_of_subset g _ j hsub,discoveryCredit_as_sum g st hreg j hj]
  rw [hq j,hA j,hU]
  by_cases he : j = t
  · subst j
    have hnt : t ≠ t+1 := by omega
    simp only [ite_true,hnt,ite_false]
    apply Finset.sum_congr rfl
    intro w _
    rw [admit_relative]
    have hfalse : ¬(t < st.top ∧ t = t+1 ∧ w = v) := by omega
    simp only [hfalse,ite_false]
    by_cases hw : w = v
    · subst w
      simp [hout,hcap]
      ring
    · simp [Finset.mem_insert,hw]
  · simp only [he,ite_false]
    by_cases hchild : j = t+1
    · have ht' : t < st.top := by omega
      have hnotdom : v ∉ parentDomain st j := by simpa [hchild,parentDomain] using hout
      have hnotactive : v ∉ (st.frames j).active := fun hv => hnotdom ((hreg j hj).1 hv)
      rw [if_pos hchild,Finset.sum_insert hnotdom]
      have hzero : (if v ∈ (st.frames j).active then 3*(st.frames j).q/8*LocalPush.deg g.graph v
          else LocalPush.deg g.graph v*relative (admitStage g st t v) j v) = 0 := by
        rw [if_neg hnotactive,admit_relative]
        simp [ht',hchild]
      rw [hzero,zero_add]
      apply Finset.sum_congr rfl
      intro w hw
      have hne : w ≠ v := by intro he; subst w; exact hnotdom hw
      rw [admit_relative]
      simp [hne]
    · rw [if_neg hchild]
      apply Finset.sum_congr rfl
      intro w _
      rw [admit_relative]
      simp [hchild]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DiscoveryExterior

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma region_raw (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) (δ : ℝ)
    (hi : RegionInvariant st) : RegionInvariant (rawExterior g α st t v δ) := by
  apply region_same st (rawExterior g α st t v δ) rfl
  · intro i; exact raw_active g α st t v δ i
  · intro i; by_cases he : i ≤ st.top <;> simp [rawExterior,he]
  · intro i; by_cases he : i ≤ st.top <;> simp [rawExterior,he]
  · intro i; by_cases he : i ≤ st.top <;> simp [rawExterior,he]
  · exact hi

lemma discoveryCredit_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (j : ℕ) :
    discoveryCredit g (refreshKeys g st T) j = discoveryCredit g st j := by
  classical
  have hA (i : ℕ) : ((refreshKeys g st T).frames i).active = (st.frames i).active := by
    by_cases hi : i ≤ st.top <;> simp [refreshKeys,hi]
  have hq : ((refreshKeys g st T).frames j).q = (st.frames j).q := by
    by_cases hi : j ≤ st.top <;> simp [refreshKeys,hi]
  have href : ((refreshKeys g st T).frames j).reference = (st.frames j).reference := by
    by_cases hi : j ≤ st.top <;> simp [refreshKeys,hi]
  have hU := parentDomain_same st (refreshKeys g st T) hA
  unfold discoveryCredit
  rw [hq,hA j,hU j]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  unfold relative
  rw [href]
  rfl

lemma discoveryCredit_debit (g : InputGraph n) (st : RecursiveState n) (j t : ℕ) (w : ℝ≥0∞) :
    discoveryCredit g (debit st t w) j = discoveryCredit g st j := rfl

lemma discoveryCredit_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (t j : ℕ) (ht : t ≤ st.top) (hj : j ≤ st.top)
    (v : Fin n) (hvt : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active) :
    let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)
    discoveryCredit g (exteriorPush g α st t v) j = discoveryCredit g st j+
      (if j = t then LocalPush.deg g.graph v*δ else 0) := by
  classical
  dsimp only
  let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)
  let base := rawExterior g α st t v δ
  have hr : RegionInvariant base := region_raw g α st t v δ hreg
  have hA (i : ℕ) := raw_active g α st t v δ i
  have hU := parentDomain_same st base hA
  have hvt' : v ∈ parentDomain base t := by simpa [hU t] using hvt
  have hout' : v ∉ (base.frames t).active := by
    change v ∉ ((rawExterior g α st t v δ).frames t).active
    rw [raw_active]
    exact hout
  have hq := raw_q g α st t v δ t
  rw [exterior_stages,discoveryCredit_debit,discoveryCredit_refresh]
  simp only [←show δ = min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
    (3*(st.frames t).q/8-relative st t v) from rfl]
  by_cases ha : relative st t v+δ = 3*(st.frames t).q/8
  · rw [if_pos ha]
    have hcap : relative base t v = 3*(base.frames t).q/8 := by
      rw [raw_relative,hq]
      simpa using ha
    rw [discoveryCredit_admit g base hr t j ht hj v hvt' hout' hcap]
    exact discoveryCredit_raw g α st hreg t j ht hj v hvt hout δ
  · rw [if_neg ha]
    exact discoveryCredit_raw g α st hreg t j ht hj v hvt hout δ

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredCredit

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma volume_insert_real (g : InputGraph n) (H : Finset (Fin n)) (v : Fin n) (hv : v ∉ H) :
    (volumeNat g (insert v H) : ℝ) = (volumeNat g H : ℝ)+LocalPush.deg g.graph v := by
  classical
  rw [volume_real,Finset.sum_insert hv,←volume_real]
  ring

lemma volume_insert_real_le (g : InputGraph n) (H : Finset (Fin n)) (v : Fin n) :
    (volumeNat g (insert v H) : ℝ) ≤ (volumeNat g H : ℝ)+LocalPush.deg g.graph v := by
  classical
  by_cases hv : v ∈ H
  · rw [Finset.insert_eq_of_mem hv]
    have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
    linarith
  · exact (volume_insert_real g H v hv).le

lemma stored_credit_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hnum : NumericalInvariant g st) (hparam : ParameterInvariant st)
    (hkeys : KeysInvariant g st) (hstore : StoredInvariant g st) (hi : StoredCreditInvariant g st)
    (t : ℕ) (ht : t ≤ st.top) (v : Fin n) (hvt : v ∈ parentDomain st t)
    (hout : v ∉ (st.frames t).active) (hr : (st.frames t).q*LocalPush.deg g.graph v < (st.frames t).residual v)
    (hd : 0 < g.graph.degree v) : StoredCreditInvariant g (exteriorPush g α st t v) := by
  classical
  let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)
  have hq0 := (hparam 0 (Nat.zero_le _)).1
  have hd' : 0 < LocalPush.deg g.graph v := by unfold LocalPush.deg; exact_mod_cast hd
  have hn := (hnum t ht).1 v hvt
  have hδ : 0 ≤ δ := (crossing_push_bounds (LocalPush.deg g.graph v) (st.frames t).q
    ((st.frames t).residual v) (relative st t v) hd' (hparam t ht).1 hn.1
    ⟨hn.2.1,(hn.2.2.2 hout).le⟩).1
  have hq : ((exteriorPush g α st t v).frames 0).q = (st.frames 0).q :=
    congrArg (fun z => z.1) (exterior_parameters g α st t v 0)
  have hC := discoveryCredit_exterior g α st hreg t 0 ht (Nat.zero_le _) v hvt hout
  have hA := exterior_active g α st t v 0
  have hS := exterior_stored g α st t v
  dsimp only at hC hA
  by_cases ht0 : t = 0
  · subst t
    change 0 ≤ min ((st.frames 0).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames 0).q/8-relative st 0 v) at hδ
    have hvol := volume_insert_real_le g st.stored v
    unfold StoredCreditInvariant rootScanPotential at hi ⊢
    rw [hS,hq,hC,hA]
    simp only [le_refl,ite_true,and_true]
    by_cases ha : relative st 0 v+min ((st.frames 0).residual v/(5*LocalPush.deg g.graph v))
        (3*(st.frames 0).q/8-relative st 0 v) = 3*(st.frames 0).q/8
    · rw [if_pos ha,volume_insert_real g (st.frames 0).active v hout]
      have hpos : 0 ≤ 5/(st.frames 0).q*(LocalPush.deg g.graph v*
          min ((st.frames 0).residual v/(5*LocalPush.deg g.graph v))
            (3*(st.frames 0).q/8-relative st 0 v)) := by positivity
      nlinarith
    · rw [if_neg ha]
      have hclear := nonactivating_push_clears (LocalPush.deg g.graph v) (st.frames 0).q
        ((st.frames 0).residual v) (relative st 0 v) ha
      have hmin : (st.frames 0).q/5 < min ((st.frames 0).residual v/(5*LocalPush.deg g.graph v))
          (3*(st.frames 0).q/8-relative st 0 v) := by
        rw [hclear]
        apply (lt_div_iff₀ (by positivity : 0 < 5*LocalPush.deg g.graph v)).mpr
        nlinarith
      have hcost : LocalPush.deg g.graph v ≤ 5/(st.frames 0).q*(LocalPush.deg g.graph v*
          min ((st.frames 0).residual v/(5*LocalPush.deg g.graph v))
            (3*(st.frames 0).q/8-relative st 0 v)) := by
        rw [show 5/(st.frames 0).q*(LocalPush.deg g.graph v*min
          ((st.frames 0).residual v/(5*LocalPush.deg g.graph v)) (3*(st.frames 0).q/8-relative st 0 v)) =
          (5*LocalPush.deg g.graph v*min ((st.frames 0).residual v/(5*LocalPush.deg g.graph v))
            (3*(st.frames 0).q/8-relative st 0 v))/(st.frames 0).q by ring]
        apply (le_div_iff₀ hq0).mpr
        nlinarith [mul_le_mul_of_nonneg_left hmin.le hd'.le]
      nlinarith
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
    have hvr : v ∈ (st.frames 0).active := parent_domain_nested st hreg 0 t htpos ht hvt
    have hvs : v ∈ st.stored := hstore.1 0 (Nat.zero_le _) hvr
    unfold StoredCreditInvariant rootScanPotential at hi ⊢
    rw [hS,Finset.insert_eq_of_mem hvs,hq,hC,hA]
    have hz : (0 : ℕ) ≠ t := Ne.symm ht0
    simpa [hz] using hi

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredCreditControl

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_discoveryCredit_same (g : InputGraph n) (st u : RecursiveState n) (hx : u.x = st.x)
    (hq : (u.frames 0).q = (st.frames 0).q) (hH : (u.frames 0).active = (st.frames 0).active) :
    discoveryCredit g u 0 = discoveryCredit g st 0 := by
  unfold discoveryCredit
  simp only [parentDomain,ite_true,relative]
  rw [hx,hq,hH]

lemma stored_credit_transport (g : InputGraph n) (st u : RecursiveState n) (hi : StoredCreditInvariant g st)
    (hS : u.stored = st.stored) (hq : (u.frames 0).q = (st.frames 0).q)
    (hH : (u.frames 0).active = (st.frames 0).active) (hC : discoveryCredit g u 0 = discoveryCredit g st 0) :
    StoredCreditInvariant g u := by
  unfold StoredCreditInvariant rootScanPotential at hi ⊢
  rw [hS,hq,hH,hC]
  exact hi

lemma stored_credit_metadata (g : InputGraph n) (st : RecursiveState n) (hi : StoredCreditInvariant g st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hq : (f (st.frames j)).q = (st.frames j).q)
    (hH : (f (st.frames j)).active = (st.frames j).active) :
    StoredCreditInvariant g (changeFrame st j f) := by
  have hq0 := observe_changeFrame (fun f => f.q) st j f hq 0
  have hH0 := observe_changeFrame (fun f => f.active) st j f hH 0
  exact stored_credit_transport g st _ hi rfl hq0 hH0 (root_discoveryCredit_same g st _ rfl hq0 hH0)

lemma stored_credit_PC (g : InputGraph n) (st : RecursiveState n) (pc : NormalizePC)
    (hi : StoredCreditInvariant g st) : StoredCreditInvariant g (changePC st pc) :=
  stored_credit_metadata g st hi st.top _ rfl rfl

lemma stored_credit_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : StoredCreditInvariant g st) : StoredCreditInvariant g (refreshKeys g st T) := by
  apply stored_credit_transport g st (refreshKeys g st T) hi rfl
  · simp [refreshKeys]
  · simp [refreshKeys]
  · exact discoveryCredit_refresh g st T 0

lemma stored_credit_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ)
    (hs : ∀ v ∉ (st.frames 0).active, h v = 0) (hi : StoredCreditInvariant g st) :
    StoredCreditInvariant g (jointUpdate g α st h) := by
  apply stored_credit_transport g st (jointUpdate g α st h) hi rfl
  · simp [jointUpdate]
  · simp [jointUpdate]
  · exact discoveryCredit_joint g α st h 0 (fun v hv => hs v ((Finset.mem_sdiff.mp hv).2))

lemma stored_credit_solve (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (T : Finset (Fin n))
    (hT : T ⊆ (st.frames 0).active) (b : Fin n → ℝ) (hi : StoredCreditInvariant g st) :
    StoredCreditInvariant g (jointUpdate g α st (solveOn g α T b)) := by
  apply stored_credit_joint g α st _ _ hi
  intro v hv
  apply solveOn_outside
  intro hvt
  exact hv (hT hvt)

lemma stored_credit_finish (g : InputGraph n) (st : RecursiveState n) (hi : StoredCreditInvariant g st) :
    StoredCreditInvariant g (finishEpisode st) := by
  unfold finishEpisode
  apply stored_credit_metadata
  · exact hi
  · rfl
  · rfl

lemma stored_credit_new (g : InputGraph n) (st : RecursiveState n) (c : NormalizeFrame n)
    (hi : StoredCreditInvariant g st) :
    StoredCreditInvariant g {st with top := st.top+1,frames := Function.update st.frames (st.top+1) c} := by
  have hn : 0 ≠ st.top+1 := by omega
  apply stored_credit_transport g st
    {st with top := st.top+1,frames := Function.update st.frames (st.top+1) c} hi rfl
  · simp [hn]
  · simp [hn]
  · apply root_discoveryCredit_same g st _ rfl <;> simp [hn]

lemma stored_credit_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hi : StoredCreditInvariant g st) :
    StoredCreditInvariant g (endCall g α st) := by
  unfold endCall
  dsimp only
  split <;> exact hi

lemma stored_credit_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    StoredCreditInvariant g (recursiveInit g s q ℓ schedule) := by
  simp [StoredCreditInvariant,rootScanPotential,discoveryCredit,recursiveInit,freshFrame,emptyFrame,
    volumeNat,parentDomain,relative]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredCreditStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma stored_credit_pending (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hnum : NumericalInvariant g st) (hparam : ParameterInvariant st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st) (hstore : StoredInvariant g st)
    (hi : StoredCreditInvariant g st) (t : ℕ) (v : Fin n) (hp : pendingPush st = some (t,v)) :
    StoredCreditInvariant g (exteriorPush g α st t v) := by
  obtain ⟨ht,hm⟩ := pending_push_member st t v hp
  obtain ⟨hvt,hout⟩ := Finset.mem_sdiff.mp ((hreg t ht).2.1 hm)
  have hr := (((hkeys t ht).1 v).mp hm).2.2
  exact stored_credit_exterior g α st hreg hnum hparam hkeys hstore hi t ht v hvt hout hr
    (isolate_pending_positive g st hiso hkeys t v hp)

lemma stored_credit_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hnum : NumericalInvariant g st) (hparam : ParameterInvariant st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st) (hstore : StoredInvariant g st)
    (hi : StoredCreditInvariant g st) (pc : NormalizePC) :
    StoredCreditInvariant g (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact stored_credit_PC g _ pc hi
  · cases hp : pendingPush st with
    | none => exact stored_credit_PC g _ pc hi
    | some p => obtain ⟨t,v⟩ := p; exact stored_credit_pending g α st hreg hnum hparam hkeys hiso hstore hi t v hp

set_option maxHeartbeats 1500000 in
lemma stored_credit_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hnum : NumericalInvariant g st) (hparam : ParameterInvariant st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st) (hstore : StoredInvariant g st)
    (hi : StoredCreditInvariant g st) : StoredCreditInvariant g (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hcomp : componentComplete st
  · simp only [hcomp,ite_true]; exact hi
  simp only [hcomp,ite_false]
  have hdrain := stored_credit_drain g α st hreg hnum hparam hkeys hiso hstore hi
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact stored_credit_PC g _ _ hi
    · split
      · exact hdrain _
      · split <;> exact stored_credit_PC g _ _ hi
  | beginEpisode =>
    simp only [hpc]
    apply stored_credit_metadata
    · exact hi
    · rfl
    · rfl
  | fullSolve =>
    simp only [hpc]
    split
    · exact stored_credit_PC g _ _ hi
    · split
      · apply stored_credit_PC
        exact stored_credit_refresh g
          (jointUpdate g α st (solveOn g α (st.frames st.top).active (st.frames st.top).residual))
          (touchedBy g (st.frames st.top).active)
          (stored_credit_solve g α st (st.frames st.top).active (active_subset_root st hreg st.top le_rfl)
            (st.frames st.top).residual hi)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact stored_credit_PC g _ _ hi
    · split
      · exact stored_credit_PC g _ _ hi
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild,childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : StoredCreditInvariant g up := stored_credit_metadata g u hi st.top _ rfl rfl
        exact stored_credit_new g up c hup
  | leafDrain =>
    simp only [hpc]
    split
    · exact stored_credit_PC g _ _ hi
    · split
      · cases hp : pendingPush st with
        | none => exact stored_credit_PC g _ _ hi
        | some p => obtain ⟨t,v⟩ := p; exact stored_credit_pending g α st hreg hnum hparam hkeys hiso hstore hi t v hp
      · split
        · exact stored_credit_PC g _ _ hi
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun f => {f with cache := C})
            have hu : StoredCreditInvariant g u := stored_credit_metadata g st hi st.top _ rfl rfl
            have hC : C ⊆ (st.frames 0).active :=
              (Finset.union_subset_iff.mpr ⟨(hreg st.top le_rfl).2.2.2,(hreg st.top le_rfl).2.2.1⟩).trans
                (active_subset_root st hreg st.top le_rfl)
            have hCu : C ⊆ (u.frames 0).active := by
              have he := observe_changeFrame (fun f => f.active) st st.top (fun f => {f with cache := C}) rfl 0
              change C ⊆ ((changeFrame st st.top (fun f => {f with cache := C})).frames 0).active
              rw [he]
              exact hC
            exact stored_credit_refresh g
              (jointUpdate g α u (solveOn g α C
                (fun v => (st.frames st.top).residual v-(st.frames st.top).theta*LocalPush.deg g.graph v)))
              (touchedBy g C) (stored_credit_solve g α u C hCu
                (fun v => (st.frames st.top).residual v-(st.frames st.top).theta*LocalPush.deg g.graph v) hu)
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact stored_credit_PC g _ _ (stored_credit_finish g _ hi)
    · split
      · exact stored_credit_PC g _ _ (stored_credit_finish g _ hi)
      · exact hdrain _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact stored_credit_PC g _ _ (stored_credit_finish g _ hi)
    · split
      · exact stored_credit_PC g _ _ (stored_credit_finish g _ hi)
      · apply stored_credit_metadata
        · exact stored_credit_finish g _ hi
        · rfl
        · rfl
  | restartDrain =>
    simp only [hpc]
    split
    · exact stored_credit_PC g _ _ hi
    · split
      · exact hdrain _
      · apply stored_credit_metadata
        · exact hi
        · rfl
        · rfl
  | normal => simp only [hpc]; exact stored_credit_end g α _ hi
  | interrupted => simp only [hpc]; exact stored_credit_end g α _ hi

lemma stored_credit_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    StoredCreditInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using stored_credit_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using stored_credit_step m g s α ℓ schedule _
      (region_run m g s α q ℓ schedule t) (numerical_run m g s α q hα hq hs ℓ schedule t)
      (parameters_run m g s α q hq ℓ schedule t) (keys_run m g s α q hq.le ℓ schedule t)
      (isolate_run m g s α q hs ℓ schedule t) (stored_run m g s α q hq.le hs ℓ schedule t) ih

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open NearlyOptimalPPR.Computation

theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    StoredCreditInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  exact stored_credit_run m g s α q hα hq hs ℓ schedule t

