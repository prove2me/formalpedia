-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_nonhalving_full_solve
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:00:10.83118+00:00
-- url     : https://prove2.me/submissions/c24456b2-3973-4cf4-a28d-e327240f956e

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_successful_request_bounds
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_full_solve_comparison
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_stack_scales
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_call_metadata

set_option linter.all false
set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

abbrev region_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_residual_identities m n g s α q ℓ schedule t).1

abbrev parameters_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_control_parameters m n g s α q ℓ schedule t).2.2.2 hq

abbrev keys_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_queue_domains m n g s α q ℓ schedule t).1 hq

abbrev isolate_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_queue_domains m n g s α q ℓ schedule t).2.1 hs

abbrev numerical_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  recursive_numerical_invariants m n g s α q hα hq hs ℓ schedule t

abbrev successful_full_event_bounds (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (he : fullSolveEvent g (recursiveRun m g s α q ℓ schedule t) id)
    (hfinish : currentPC (recursiveRun m g s α q ℓ schedule (t-2))=.finishEpisode) :=
  NearlyOptimalPPR.Computation.recursive_successful_request_bounds m n g s α q hα hq hs ℓ schedule t id he hfinish

abbrev actual_full_solve_comparison (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b : ℕ) (hab : a+1 ≤ b) :=
  NearlyOptimalPPR.Computation.recursive_full_solve_comparison m n g s α q hα hq hs ℓ schedule a b hab

abbrev stack_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_stack_scales m n g s α q ℓ schedule t).2.1

abbrev call_locations_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_call_metadata m n g s α q ℓ schedule t).1

abbrev information_id_bound_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_call_metadata m n g s α q ℓ schedule t).2.1

abbrev open_frame_information_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_call_metadata m n g s α q ℓ schedule t).2.2.2.2.1

abbrev running_open_not_closed_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_call_metadata m n g s α q ℓ schedule t).2.2.2.2.2

end
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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ReturnDrainedControl

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma pending_same (st u : RecursiveState n) (ht : u.top = st.top)
    (hE : ∀ i, (u.frames i).exterior = (st.frames i).exterior) : pendingPush u = pendingPush st := by
  classical
  simp only [pendingPush,ht,hE]

lemma pending_metadata (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hE : (f (st.frames j)).exterior = (st.frames j).exterior) :
    pendingPush (changeFrame st j f) = pendingPush st := by
  apply pending_same st (changeFrame st j f) rfl
  intro i
  exact observe_changeFrame (fun f => f.exterior) st j f hE i

lemma pending_PC (st : RecursiveState n) (pc : NormalizePC) : pendingPush (changePC st pc) = pendingPush st :=
  pending_metadata st st.top _ rfl

lemma pending_finish (st : RecursiveState n) : pendingPush (finishEpisode st) = pendingPush st := by
  apply pending_same st (finishEpisode st) rfl
  intro i
  by_cases he : i = st.top <;> simp [finishEpisode,changeFrame,he]

lemma any_exhausted_iff (st : RecursiveState n) :
    anyExhausted st ↔ ancestorExhausted st ∨ exhausted st st.top := by
  constructor
  · rintro ⟨i,hi,he⟩
    by_cases hit : i = st.top
    · right; simpa [hit] using he
    · exact Or.inl ⟨i,lt_of_le_of_ne hi hit,he⟩
  · rintro (⟨i,hi,he⟩|he)
    · exact ⟨i,hi.le,he⟩
    · exact ⟨st.top,le_rfl,he⟩

lemma return_drained_none (st : RecursiveState n) (hp : pendingPush st = none) : ReturnDrained st := fun _ => hp

lemma return_drained_excluded (st : RecursiveState n)
    (hn : (st.frames st.top).pc ≠ .normal) (hf : (st.frames st.top).pc ≠ .finishEpisode) : ReturnDrained st := by
  rintro (h|h)
  · exact False.elim (hn h)
  · exact False.elim (hf h)

lemma return_drained_PC_safe (st : RecursiveState n) (pc : NormalizePC)
    (hn : pc ≠ .normal) (hf : pc ≠ .finishEpisode) : ReturnDrained (changePC st pc) := by
  apply return_drained_excluded
  · simpa [changePC,changeFrame] using hn
  · simpa [changePC,changeFrame] using hf

lemma return_drained_PC_none (st : RecursiveState n) (pc : NormalizePC) (hp : pendingPush st = none) :
    ReturnDrained (changePC st pc) := return_drained_none _ ((pending_PC st pc).trans hp)

lemma return_drained_exterior_safe (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hn : (st.frames st.top).pc ≠ .normal)
    (hf : (st.frames st.top).pc ≠ .finishEpisode) : ReturnDrained (exteriorPush g α st t v) := by
  apply return_drained_excluded
  · simpa only [top_exterior,frame_pc_exterior] using hn
  · simpa only [top_exterior,frame_pc_exterior] using hf

lemma return_drained_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hstack : StackInvariant st) (hi : ReturnDrained st) : ReturnDrained (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · rename_i ht
    have hp := hstack (st.top-1) (by omega)
    apply return_drained_excluded <;> simpa [hp]

lemma return_drained_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    ReturnDrained (recursiveInit g s q ℓ schedule) := by
  apply return_drained_excluded <;> simp [recursiveInit,freshFrame,emptyFrame]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ReturnDrainedStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma return_drained_drain_safe (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (pc : NormalizePC)
    (hn : (st.frames st.top).pc ≠ .normal) (hf : (st.frames st.top).pc ≠ .finishEpisode)
    (hpn : pc ≠ .normal) (hpf : pc ≠ .finishEpisode) :
    ReturnDrained (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact return_drained_PC_safe _ pc hpn hpf
  · cases hp : pendingPush st with
    | none => exact return_drained_PC_safe _ pc hpn hpf
    | some p => obtain ⟨t,v⟩ := p; exact return_drained_exterior_safe g α st t v hn hf

lemma return_drained_afterChild_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hpc : (st.frames st.top).pc = .afterChild)
    (ha : ¬ancestorExhausted st) (he : ¬exhausted st st.top) :
    ReturnDrained (if anyExhausted st then changePC (debit st st.top 1) .finishEpisode else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) .finishEpisode) := by
  have hn : ¬anyExhausted st := by simp [any_exhausted_iff,ha,he]
  rw [if_neg hn]
  cases hp : pendingPush st with
  | none => exact return_drained_PC_none _ _ hp
  | some p =>
    obtain ⟨t,v⟩ := p
    exact return_drained_exterior_safe g α st t v (by simp [hpc]) (by simp [hpc])

lemma return_drained_newFrame (st : RecursiveState n) (f : NormalizeFrame n) (hp : f.pc = .initialDrain) :
    ReturnDrained {st with top := st.top+1, frames := Function.update st.frames (st.top+1) f} := by
  apply return_drained_excluded <;> simp [hp]

set_option maxHeartbeats 1000000 in
lemma return_drained_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hstack : StackInvariant st) (hi : ReturnDrained st) :
    ReturnDrained (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]
    exact hi
  simp only [hc,ite_false]
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact return_drained_PC_safe _ _ (by simp) (by simp)
    · split
      · exact return_drained_drain_safe g α st _ (by simp [hpc]) (by simp [hpc]) (by simp) (by simp)
      · rename_i hp
        have hn : pendingPush st = none := by cases h : pendingPush st <;> simp_all
        split
        · exact return_drained_PC_none _ _ hn
        · exact return_drained_PC_safe _ _ (by simp) (by simp)
  | beginEpisode =>
    simp only [hpc]
    apply return_drained_excluded <;>
      simp [changeFrame,debit] <;> (try split_ifs) <;> simp
  | fullSolve =>
    simp only [hpc]
    split
    · exact return_drained_PC_safe _ _ (by simp) (by simp)
    · split
      · exact return_drained_PC_safe _ _ (by simp) (by simp)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact return_drained_PC_safe _ _ (by simp) (by simp)
    · split
      · exact return_drained_PC_safe _ _ (by simp) (by simp)
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        exact return_drained_newFrame up c rfl
  | leafDrain =>
    simp only [hpc]
    split
    · exact return_drained_PC_safe _ _ (by simp) (by simp)
    · split
      · cases hp : pendingPush st with
        | none => exact return_drained_PC_safe _ _ (by simp) (by simp)
        | some p =>
          obtain ⟨t,v⟩ := p
          exact return_drained_exterior_safe g α st t v (by simp [hpc]) (by simp [hpc])
      · split
        · exact return_drained_PC_safe _ _ (by simp) (by simp)
        · split
          · apply return_drained_excluded <;>
              simp [changeFrame,refreshKeys,jointUpdate,debit,hpc]
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact return_drained_PC_safe _ _ (by simp) (by simp)
    · rename_i ha
      split
      · exact return_drained_PC_safe _ _ (by simp) (by simp)
      · rename_i he
        exact return_drained_afterChild_drain g α st hpc ha he
  | finishEpisode =>
    have hn : pendingPush st = none := hi (Or.inr hpc)
    simp only [hpc]
    split
    · exact return_drained_PC_safe _ _ (by simp) (by simp)
    · split
      · exact return_drained_PC_safe _ _ (by simp) (by simp)
      · apply return_drained_none
        rw [pending_metadata _ st.top _ rfl,pending_finish]
        exact hn
  | restartDrain =>
    simp only [hpc]
    split
    · exact return_drained_PC_safe _ _ (by simp) (by simp)
    · split
      · exact return_drained_drain_safe g α st _ (by simp [hpc]) (by simp [hpc]) (by simp) (by simp)
      · apply return_drained_excluded <;> simp [changeFrame,debit]
  | normal =>
    simp only [hpc]
    exact return_drained_end g α _ hstack hi
  | interrupted =>
    simp only [hpc]
    exact return_drained_end g α _ hstack hi

lemma return_drained_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ReturnDrained (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using return_drained_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      return_drained_step m g s α ℓ schedule _ (stack_run m g s α q ℓ schedule t) ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EntryDrained

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma entry_safe (st : RecursiveState n) (hpc : (st.frames st.top).pc ≠ .beginEpisode) : EntryDrained st :=
  fun h => False.elim (hpc h)
lemma entry_none (st : RecursiveState n) (hp : pendingPush st = none) : EntryDrained st := fun _ => hp
lemma entry_PC_safe (st : RecursiveState n) (pc : NormalizePC) (hp : pc ≠ .beginEpisode) : EntryDrained (changePC st pc) := by
  apply entry_safe
  simpa [changePC,changeFrame] using hp
lemma entry_PC_none (st : RecursiveState n) (pc : NormalizePC) (hp : pendingPush st = none) : EntryDrained (changePC st pc) :=
  entry_none _ ((pending_PC st pc).trans hp)
lemma entry_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hp : (st.frames st.top).pc ≠ .beginEpisode) : EntryDrained (exteriorPush g α st t v) := by
  apply entry_safe
  simpa only [top_exterior,frame_pc_exterior] using hp
lemma entry_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (pc : NormalizePC)
    (hp : (st.frames st.top).pc ≠ .beginEpisode) (hn : pc ≠ .beginEpisode) :
    EntryDrained (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact entry_PC_safe _ pc hn
  · cases he : pendingPush st with
    | none => exact entry_PC_safe _ pc hn
    | some p => obtain ⟨t,v⟩ := p; exact entry_exterior g α st t v hp
lemma entry_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hs : StackInvariant st) (hi : EntryDrained st) : EntryDrained (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · rename_i ht
    apply entry_safe
    simpa [hs (st.top-1) (by omega)]

set_option maxHeartbeats 1000000 in
lemma entry_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hs : StackInvariant st) (hr : ReturnDrained st) (hi : EntryDrained st) :
    EntryDrained (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]; exact hi
  simp only [hc,ite_false]
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact entry_PC_safe _ _ (by simp)
    · split
      · exact entry_drain g α st _ (by simp [hpc]) (by simp)
      · rename_i hp
        have hn : pendingPush st = none := by cases h : pendingPush st <;> simp_all
        split <;> exact entry_PC_none _ _ hn
  | beginEpisode =>
    simp only [hpc]
    apply entry_safe
    simp [changeFrame,debit] <;> (try split_ifs) <;> simp
  | fullSolve =>
    simp only [hpc]
    split
    · exact entry_PC_safe _ _ (by simp)
    · split
      · exact entry_PC_safe _ _ (by simp)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact entry_PC_safe _ _ (by simp)
    · split
      · exact entry_PC_safe _ _ (by simp)
      · apply entry_safe; simp [freshFrame,emptyFrame]
  | leafDrain =>
    simp only [hpc]
    split
    · exact entry_PC_safe _ _ (by simp)
    · split
      · cases hp : pendingPush st with
        | none => exact entry_PC_safe _ _ (by simp)
        | some p => obtain ⟨t,v⟩ := p; exact entry_exterior g α st t v (by simp [hpc])
      · split
        · exact entry_PC_safe _ _ (by simp)
        · split
          · apply entry_safe; simp [changeFrame,refreshKeys,jointUpdate,debit,hpc]
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact entry_PC_safe _ _ (by simp)
    · split
      · exact entry_PC_safe _ _ (by simp)
      · exact entry_drain g α st _ (by simp [hpc]) (by simp)
  | finishEpisode =>
    have hp := hr (Or.inr hpc)
    simp only [hpc]
    split
    · exact entry_PC_safe _ _ (by simp)
    · split
      · exact entry_PC_safe _ _ (by simp)
      · apply entry_none
        rw [pending_metadata _ st.top _ rfl,pending_finish]
        exact hp
  | restartDrain =>
    simp only [hpc]
    split
    · exact entry_PC_safe _ _ (by simp)
    · split
      · exact entry_drain g α st _ (by simp [hpc]) (by simp)
      · rename_i hp
        have hn : pendingPush st = none := by cases h : pendingPush st <;> simp_all
        apply entry_none
        rw [pending_metadata _ st.top _ rfl]
        exact hn
  | normal => simp only [hpc]; exact entry_end g α _ hs hi
  | interrupted => simp only [hpc]; exact entry_end g α _ hs hi

lemma entry_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    EntryDrained (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => apply entry_safe; simp [recursiveRun,recursiveInit,freshFrame,emptyFrame]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      entry_step m g s α ℓ schedule _ (stack_run m g s α q ℓ schedule t)
        (return_drained_run m g s α q ℓ schedule t) ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FullSolveDrained

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma full_drained_safe (st : RecursiveState n) (hpc : (st.frames st.top).pc ≠ .fullSolve) : FullSolveDrained st :=
  fun h => False.elim (hpc h)
lemma full_drained_none (st : RecursiveState n) (hp : pendingPush st = none) : FullSolveDrained st := fun _ => hp
lemma full_drained_PC_safe (st : RecursiveState n) (pc : NormalizePC) (hp : pc ≠ .fullSolve) : FullSolveDrained (changePC st pc) := by
  apply full_drained_safe
  simpa [changePC,changeFrame] using hp
lemma full_drained_PC_none (st : RecursiveState n) (pc : NormalizePC) (hp : pendingPush st = none) : FullSolveDrained (changePC st pc) :=
  full_drained_none _ ((pending_PC st pc).trans hp)
lemma full_drained_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hp : (st.frames st.top).pc ≠ .fullSolve) : FullSolveDrained (exteriorPush g α st t v) := by
  apply full_drained_safe
  simpa only [top_exterior,frame_pc_exterior] using hp
lemma full_drained_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (pc : NormalizePC)
    (hp : (st.frames st.top).pc ≠ .fullSolve) (hn : pc ≠ .fullSolve) :
    FullSolveDrained (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact full_drained_PC_safe _ pc hn
  · cases he : pendingPush st with
    | none => exact full_drained_PC_safe _ pc hn
    | some p => obtain ⟨t,v⟩ := p; exact full_drained_exterior g α st t v hp
lemma full_drained_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hs : StackInvariant st) (hi : FullSolveDrained st) : FullSolveDrained (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · rename_i ht
    apply full_drained_safe
    simpa [hs (st.top-1) (by omega)]

set_option maxHeartbeats 1000000 in
lemma full_drained_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hs : StackInvariant st) (hr : ReturnDrained st) (he : EntryDrained st) (hi : FullSolveDrained st) :
    FullSolveDrained (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]; exact hi
  simp only [hc,ite_false]
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact full_drained_PC_safe _ _ (by simp)
    · split
      · exact full_drained_drain g α st _ (by simp [hpc]) (by simp)
      · rename_i hp
        have hn : pendingPush st = none := by cases h : pendingPush st <;> simp_all
        split <;> exact full_drained_PC_none _ _ hn
  | beginEpisode =>
    simp only [hpc]
    apply full_drained_none
    rw [pending_metadata _ st.top _ rfl]
    exact he hpc
  | fullSolve =>
    simp only [hpc]
    split
    · exact full_drained_PC_safe _ _ (by simp)
    · split
      · exact full_drained_PC_safe _ _ (by simp)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact full_drained_PC_safe _ _ (by simp)
    · split
      · exact full_drained_PC_safe _ _ (by simp)
      · apply full_drained_safe; simp [freshFrame,emptyFrame]
  | leafDrain =>
    simp only [hpc]
    split
    · exact full_drained_PC_safe _ _ (by simp)
    · split
      · cases hp : pendingPush st with
        | none => exact full_drained_PC_safe _ _ (by simp)
        | some p => obtain ⟨t,v⟩ := p; exact full_drained_exterior g α st t v (by simp [hpc])
      · split
        · exact full_drained_PC_safe _ _ (by simp)
        · split
          · apply full_drained_safe; simp [changeFrame,refreshKeys,jointUpdate,debit,hpc]
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact full_drained_PC_safe _ _ (by simp)
    · split
      · exact full_drained_PC_safe _ _ (by simp)
      · exact full_drained_drain g α st _ (by simp [hpc]) (by simp)
  | finishEpisode =>
    have hp := hr (Or.inr hpc)
    simp only [hpc]
    split
    · exact full_drained_PC_safe _ _ (by simp)
    · split
      · exact full_drained_PC_safe _ _ (by simp)
      · apply full_drained_none
        rw [pending_metadata _ st.top _ rfl,pending_finish]
        exact hp
  | restartDrain =>
    simp only [hpc]
    split
    · exact full_drained_PC_safe _ _ (by simp)
    · split
      · exact full_drained_drain g α st _ (by simp [hpc]) (by simp)
      · rename_i hp
        have hn : pendingPush st = none := by cases h : pendingPush st <;> simp_all
        apply full_drained_none
        rw [pending_metadata _ st.top _ rfl]
        exact hn
  | normal => simp only [hpc]; exact full_drained_end g α _ hs hi
  | interrupted => simp only [hpc]; exact full_drained_end g α _ hs hi

lemma full_drained_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    FullSolveDrained (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => apply full_drained_safe; simp [recursiveRun,recursiveInit,freshFrame,emptyFrame]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using full_drained_step m g s α ℓ schedule _
      (stack_run m g s α q ℓ schedule t) (return_drained_run m g s α q ℓ schedule t)
      (entry_run m g s α q ℓ schedule t) ih

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

-- Proof module: Solutions.SharedMonotone

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma exterior_x (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    (exteriorPush g α st t v).x = Function.update st.x v (st.x v+
      min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
        (3*(st.frames t).q/8-relative st t v)) := by
  classical
  simp only [exteriorPush]
  split_ifs <;> rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ProductionEvents

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma production_pending (st : RecursiveState n) (t : ℕ) (v : Fin n) (hp : stepProduction st = some (t,v)) :
    pendingPush st = some (t,v) := by
  unfold stepProduction drainProduction at hp
  split_ifs at hp <;> try cases hp
  all_goals
    cases hpc : (st.frames st.top).pc <;> simp [hpc] at hp <;>
      (try split_ifs at hp) <;> simp_all

lemma production_push (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hp : stepProduction st = some (t,v)) :
    recursiveStep m g s α ℓ schedule st = exteriorPush g α st t v := by
  have hpend := production_pending st t v hp
  cases hpc : (st.frames st.top).pc <;>
    simp [stepProduction,drainProduction,hpc,hpend] at hp <;>
    (try split_ifs at hp) <;> simp_all [recursiveStep,hpc,hpend]

lemma production_increment_nonnegative (g : InputGraph n) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hp : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st)
    (t : ℕ) (v : Fin n) (hprod : stepProduction st = some (t,v)) :
    0 ≤ pushIncrement g st t v := by
  have hpend := production_pending st t v hprod
  obtain ⟨ht,hm⟩ := pending_push_member st t v hpend
  obtain ⟨hv,hout⟩ := Finset.mem_sdiff.mp ((hreg t ht).2.1 hm)
  have hd : 0 < LocalPush.deg g.graph v := by
    unfold LocalPush.deg
    exact_mod_cast isolate_pending_positive g st hiso hkeys t v hpend
  have hn := (hnum t ht).1 v hv
  exact (crossing_push_bounds _ _ _ _ hd (hp t ht).1 hn.1 ⟨hn.2.1,(hn.2.2.2 hout).le⟩).1

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OutsideFlowStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma outsideMass_update (g : InputGraph n) (F : Finset (Fin n)) (x : Fin n → ℝ)
    (v : Fin n) (δ : ℝ) : outsideMass g F (Function.update x v (x v+δ)) =
      outsideMass g F x+if v ∉ F then LocalPush.deg g.graph v*δ else 0 := by
  classical
  have hrow (w : Fin n) : LocalPush.deg g.graph w*Function.update x v (x v+δ) w =
      LocalPush.deg g.graph w*x w+if w=v then LocalPush.deg g.graph v*δ else 0 := by
    by_cases hw : w=v
    · subst w; simp; ring
    · simp [Function.update_of_ne hw,hw]
  unfold outsideMass
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]
  simp

set_option maxHeartbeats 2000000 in
lemma x_step_none_outside (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hreg : RegionInvariant st)
    (j : ℕ) (hj : j ≤ st.top) (F : Finset (Fin n)) (hF : (st.frames j).active ⊆ F)
    (v : Fin n) (hv : v ∉ F) (hp : stepProduction st = none) :
    (recursiveStep m g s α ℓ schedule st).x v = st.x v := by
  have htop : v ∉ (st.frames st.top).active := fun hh =>
    hv (hF (active_subset_between st hreg j st.top hj le_rfl hh))
  have hcache : v ∉ (st.frames st.top).cache ∪ (st.frames st.top).high := by
    intro hh
    obtain hh|hh := Finset.mem_union.mp hh
    · exact htop ((hreg st.top le_rfl).2.2.2 hh)
    · exact htop ((hreg st.top le_rfl).2.2.1 hh)
  have hfull := solveOn_outside g α (st.frames st.top).active (st.frames st.top).residual v htop
  have hcached := solveOn_outside g α ((st.frames st.top).cache ∪ (st.frames st.top).high)
    (fun w => (st.frames st.top).residual w-(st.frames st.top).theta*LocalPush.deg g.graph w) v hcache
  clear hreg
  cases hpend : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,stepProduction,drainProduction,hpc,hpend] at hp ⊢ <;>
      (try split_ifs at hp ⊢) <;>
      simp_all (config := {maxSteps := 1000000}) [changePC,changeFrame,debit,refreshKeys,jointUpdate,finishEpisode,endCall,completeComponent,Pi.add_apply] <;> (try split_ifs) <;> simp_all
  | some p =>
    obtain ⟨t,w⟩ := p
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,stepProduction,drainProduction,hpc,hpend] at hp ⊢ <;>
      (try split_ifs at hp ⊢) <;>
      simp_all (config := {maxSteps := 1000000}) [changePC,changeFrame,debit,refreshKeys,jointUpdate,finishEpisode,endCall,completeComponent,Pi.add_apply] <;> (try split_ifs) <;> simp_all

lemma outsideMass_step_flow (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : α ≤ 1)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hp : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st)
    (j : ℕ) (hj : j ≤ st.top) (F : Finset (Fin n)) (hF : (st.frames j).active ⊆ F) :
    (1-α)*(outsideMass g F (recursiveStep m g s α ℓ schedule st).x-outsideMass g F st.x) ≤
      incomingProduction g α st j := by
  classical
  cases hh : stepProduction st with
  | none =>
    have heq : outsideMass g F (recursiveStep m g s α ℓ schedule st).x = outsideMass g F st.x := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [x_step_none_outside m g s α ℓ schedule st hreg j hj F hF v (Finset.mem_compl.mp hv) hh]
    rw [heq]
    simp [incomingProduction,hh]
  | some p =>
    obtain ⟨t,v⟩ := p
    have hδ := production_increment_nonnegative g st hreg hp hnum hkeys hiso t v hh
    have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
    have hm : 0 ≤ LocalPush.deg g.graph v*pushIncrement g st t v := mul_nonneg hd hδ
    rw [production_push m g s α ℓ schedule st t v hh,exterior_x,outsideMass_update]
    change (1-α)*(outsideMass g F st.x+(if v ∉ F then LocalPush.deg g.graph v*pushIncrement g st t v else 0)-
      outsideMass g F st.x) ≤ incomingProduction g α st j
    unfold incomingProduction
    rw [hh]
    dsimp only
    by_cases htj : t ≤ j
    · rw [if_pos htj]
      split_ifs <;> nlinarith [mul_nonneg (sub_nonneg.mpr hα) hm]
    · have hpend := production_pending st t v hh
      obtain ⟨ht,hmem⟩ := pending_push_member st t v hpend
      have hdom := (Finset.mem_sdiff.mp ((hreg t ht).2.1 hmem)).1
      have hvF : v ∈ F := hF (parent_domain_nested st hreg j t (by omega) ht hdom)
      simp [htj,hvF]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolveHalving

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma full_solve_halving_criterion (κ q b Q μ J d R f μnext : ℝ)
    (hκ : 0 < κ) (hq : 0 < q) (hb : 0 < b) (hfloor : q*b < Q) (hQ : Q ≤ 2*μ)
    (hd : 0 ≤ d) (hvol : d ≤ b/(64*κ)) (hR : R ≤ κ*(Q/b)*d)
    (hJ : J < μ/4) (hf : f ≤ q*b/2048)
    (hcompare : μnext ≤ J+2*κ*q*d+2*R+f) : μnext < μ/2 := by
  have hQ0 : 0 < Q := (mul_pos hq hb).trans hfloor
  have hμ : 0 < μ := by linarith
  have hkd : κ*d ≤ b/64 := by
    have hh := (le_div_iff₀ (show 0 < 64*κ by positivity)).mp hvol
    nlinarith
  have hqd : κ*q*d ≤ μ/32 := by
    calc
      _ = q*(κ*d) := by ring
      _ ≤ q*(b/64) := mul_le_mul_of_nonneg_left hkd hq.le
      _ = q*b/64 := by ring
      _ ≤ μ/32 := by linarith
  have hrd : R ≤ μ/32 := by
    calc
      _ ≤ κ*(Q/b)*d := hR
      _ = (Q/b)*(κ*d) := by ring
      _ ≤ (Q/b)*(b/64) := mul_le_mul_of_nonneg_left hkd (div_nonneg hQ0.le hb.le)
      _ = Q/64 := by field_simp
      _ ≤ μ/32 := by linarith
  have hfd : f ≤ μ/1024 := by linarith
  linarith

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SuccessfulRequestBounds

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma weighted_density_bound (g : InputGraph n) (D H : Finset (Fin n)) (r : Fin n → ℝ)
    (hD : D ⊆ H) (κ Q b : ℝ) (hr : ∀ v ∈ H, r v ≤ κ*(Q/b)*LocalPush.deg g.graph v) :
    (∑ v ∈ D, r v) ≤ κ*(Q/b)*(volumeNat g D : ℝ) := by
  rw [volume_real,Finset.mul_sum]
  exact Finset.sum_le_sum (fun v hv => hr v (hD hv))

lemma nonhalving_exception (κ q b μ J d R μnext : ℝ)
    (hκ : 0 < κ) (hq : 0 < q) (hb : 0 < b) (hfloor : q*b < 2*μ)
    (hd : 0 ≤ d) (hR : R ≤ κ*(2*μ/b)*d)
    (hcompare : μnext ≤ J+2*κ*q*d+2*R) (hnonhalf : μ/2 ≤ μnext) :
    μ/4 ≤ J ∨ b/(64*κ) < d := by
  by_contra hn
  push_neg at hn
  have hf : (0 : ℝ) ≤ q*b/2048 := by positivity
  have hh := full_solve_halving_criterion κ q b (2*μ) μ J d R 0 μnext hκ hq hb hfloor le_rfl hd
    hn.2 hR hn.1 hf (by simpa using hcompare)
  linarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ActiveGrowth

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma frame_active_metadata (st : RecursiveState n) (k j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) (hH : (f (st.frames k)).active = (st.frames k).active) :
    ((changeFrame st k f).frames j).active = (st.frames j).active :=
  observe_changeFrame (fun f => f.active) st k f hH j

lemma active_exterior_growth (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t j : ℕ) (v : Fin n) : (st.frames j).active ⊆ ((exteriorPush g α st t v).frames j).active := by
  classical
  rw [exterior_active]
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

lemma active_drain_growth (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ) (pc : NormalizePC) :
    (st.frames j).active ⊆ ((if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc).frames j).active := by
  split
  · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
  · cases hp : pendingPush st with
    | none => simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
    | some p => obtain ⟨t,v⟩ := p; exact active_exterior_growth g α st t j v

set_option maxHeartbeats 1000000 in
lemma active_step_growth (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top) :
    (st.frames j).active ⊆ ((recursiveStep m g s α ℓ schedule st).frames j).active := by
  classical
  have hnew : j ≠ st.top+1 := by omega
  by_cases hd : st.done = true
  · simp [recursiveStep,hd] <;> (try split_ifs) <;> simp_all
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp [hc,completeComponent,debit] <;> (try split_ifs) <;> simp_all
  simp only [hc,ite_false]
  have hdrain := active_drain_growth g α st j
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
    · split
      · exact hdrain _
      · split <;> simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
  | beginEpisode => simp only [hpc]; simp [changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
  | fullSolve =>
    simp only [hpc]
    split
    · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
    · split
      · simp [changePC,changeFrame,Function.update_apply,debit,refreshKeys,jointUpdate] <;> (try split_ifs) <;> simp_all
      · simp [debit] <;> (try split_ifs) <;> simp_all
  | normalize =>
    simp only [hpc]
    split
    · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
    · split
      · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
      · simp [changeFrame,Function.update_apply,debit,hnew] <;> (try split_ifs) <;> simp_all
  | leafDrain =>
    simp only [hpc]
    split
    · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
    · split
      · cases hh : pendingPush st with
        | none => simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
        | some p => obtain ⟨t,v⟩ := p; exact active_exterior_growth g α st t j v
      · split
        · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
        · split
          · simp [debit,refreshKeys,jointUpdate,changeFrame,Function.update_apply] <;> (try split_ifs) <;> simp_all
          · simp [debit] <;> (try split_ifs) <;> simp_all
  | afterChild =>
    simp only [hpc]
    split
    · simp [changePC,changeFrame,Function.update_apply,debit,finishEpisode] <;> (try split_ifs) <;> simp_all
    · split
      · simp [changePC,changeFrame,Function.update_apply,debit,finishEpisode] <;> (try split_ifs) <;> simp_all
      · exact hdrain _
  | finishEpisode =>
    simp only [hpc]
    split
    · simp [changePC,changeFrame,Function.update_apply,debit,finishEpisode] <;> (try split_ifs) <;> simp_all
    · split <;> simp [changePC,changeFrame,Function.update_apply,debit,finishEpisode] <;> (try split_ifs) <;> simp_all
  | restartDrain =>
    simp only [hpc]
    split
    · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
    · split
      · exact hdrain _
      · simp [changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
  | normal => simp only [hpc]; simp [endCall,debit] <;> (try split_ifs) <;> simp_all
  | interrupted => simp only [hpc]; simp [endCall,debit] <;> (try split_ifs) <;> simp_all

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SnapshotIntervals

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma active_interval_growth (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top) :
    ((recursiveRun m g s α q ℓ schedule a).frames j).active ⊆
      ((recursiveRun m g s α q ℓ schedule b).frames j).active := by
  have aux : ∀ d, a+d ≤ b → ((recursiveRun m g s α q ℓ schedule a).frames j).active ⊆
      ((recursiveRun m g s α q ℓ schedule (a+d)).frames j).active := by
    intro d
    induction d with
    | zero => intro _; exact Finset.Subset.refl _
    | succ d ih =>
      intro hd
      have hstep := active_step_growth m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+d))
        j (hopen (a+d) (by omega) (by omega))
      have heq : recursiveRun m g s α q ℓ schedule (a+(d+1)) =
          recursiveStep m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+d)) := by
        rw [show a+(d+1) = (a+d)+1 by omega]
        simp only [recursiveRun,Function.iterate_succ_apply']
      rw [heq]
      exact (ih (by omega)).trans hstep
  simpa [Nat.add_sub_of_le hab] using aux (b-a) (by omega)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CallLifecycleSteps

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma exterior_lifecycle (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    (exteriorPush g α st t v).nextId = st.nextId ∧
      (exteriorPush g α st t v).information = st.information ∧ (exteriorPush g α st t v).closed = st.closed := by
  simp [exteriorPush,changeFrame,refreshKeys,debit] <;> (try split_ifs) <;>
    (first | rfl | exact ⟨rfl,rfl,rfl⟩)

@[simp] lemma nextId_changeFrame (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).nextId = st.nextId := rfl

@[simp] lemma nextId_PC (st : RecursiveState n) (pc : NormalizePC) :
    (changePC st pc).nextId = st.nextId := rfl

@[simp] lemma nextId_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    (debit st j w).nextId = st.nextId := rfl

@[simp] lemma nextId_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).nextId = st.nextId := rfl

@[simp] lemma nextId_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    (jointUpdate g α st h).nextId = st.nextId := rfl

@[simp] lemma nextId_finish (st : RecursiveState n) :
    (finishEpisode st).nextId = st.nextId := rfl

@[simp] lemma nextId_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    (endCall g α st).nextId = st.nextId := by unfold endCall; dsimp only; split <;> rfl

@[simp] lemma nextId_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) :
    (completeComponent m g s α st).nextId = st.nextId := rfl

@[simp] lemma information_changeFrame (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).information = st.information := rfl

@[simp] lemma information_PC (st : RecursiveState n) (pc : NormalizePC) :
    (changePC st pc).information = st.information := rfl

@[simp] lemma information_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    (debit st j w).information = st.information := rfl

@[simp] lemma information_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).information = st.information := rfl

@[simp] lemma information_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    (jointUpdate g α st h).information = st.information := rfl

@[simp] lemma information_finish (st : RecursiveState n) :
    (finishEpisode st).information = st.information := rfl

@[simp] lemma information_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    (endCall g α st).information = st.information := by unfold endCall; dsimp only; split <;> rfl

@[simp] lemma information_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) :
    (completeComponent m g s α st).information = st.information := rfl

@[simp] lemma closed_changeFrame (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).closed = st.closed := rfl

@[simp] lemma closed_PC (st : RecursiveState n) (pc : NormalizePC) :
    (changePC st pc).closed = st.closed := rfl

@[simp] lemma closed_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    (debit st j w).closed = st.closed := rfl

@[simp] lemma closed_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).closed = st.closed := rfl

@[simp] lemma closed_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    (jointUpdate g α st h).closed = st.closed := rfl

@[simp] lemma closed_finish (st : RecursiveState n) :
    (finishEpisode st).closed = st.closed := rfl

@[simp] lemma closed_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    (endCall g α st).closed = insert (st.frames st.top).id st.closed := by
  unfold endCall
  dsimp only
  split <;> rfl

@[simp] lemma closed_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) :
    (completeComponent m g s α st).closed = st.closed ∪ (Finset.range (st.top+1)).image (fun i => (st.frames i).id) := rfl

set_option maxHeartbeats 2000000 in
lemma closed_step_monotone (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) :
    st.closed ⊆ (recursiveStep m g s α ℓ schedule st).closed := by
  cases hpend : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hpend] <;>
      (try split_ifs) <;> simp_all
  | some p =>
    obtain ⟨t,v⟩ := p
    have hh := (exterior_lifecycle g α st t v).2.2
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hpend,hh] <;>
      (try split_ifs) <;> simp_all

set_option maxHeartbeats 2000000 in
lemma information_step_old (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (id : ℕ) (hid : id < st.nextId) :
    (recursiveStep m g s α ℓ schedule st).information id = st.information id := by
  have hne : id ≠ st.nextId := Nat.ne_of_lt hid
  cases hpend : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hpend,
        Function.update_apply,hne] <;> (try split_ifs) <;> simp_all [freshFrame,Function.update_apply]
  | some p =>
    obtain ⟨t,v⟩ := p
    have hh := (exterior_lifecycle g α st t v).2.1
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hpend,
        Function.update_apply,hne,hh] <;> (try split_ifs) <;> simp_all [freshFrame,Function.update_apply]

lemma closed_run_monotone (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) : Monotone (fun t => (recursiveRun m g s α q ℓ schedule t).closed) := by
  apply monotone_nat_of_le_succ
  intro t
  simpa only [recursiveRun,Function.iterate_succ_apply'] using
    closed_step_monotone m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule t)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CallLocations

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma information_run_persistent (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (info : CallInformation) (hab : a ≤ b)
    (hinfo : (recursiveRun m g s α q ℓ schedule a).information id=some info) :
    (recursiveRun m g s α q ℓ schedule b).information id=some info := by
  have aux : ∀ d, (recursiveRun m g s α q ℓ schedule (a+d)).information id=some info := by
    intro d
    induction d with
    | zero => simpa using hinfo
    | succ d ih =>
      have hi := information_id_bound_run m g s α q ℓ schedule (a+d) id info ih
      have hs := information_step_old m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+d)) id hi
      have hstep : recursiveRun m g s α q ℓ schedule (a+(d+1)) =
          recursiveStep m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+d)) := by
        rw [show a+(d+1)=(a+d)+1 by omega]
        simp only [recursiveRun,Function.iterate_succ_apply']
      rw [hstep,hs]
      exact ih
  simpa [Nat.add_sub_of_le hab] using aux (b-a)

lemma unclosed_call_interval (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (info : CallInformation)
    (hinfo : (recursiveRun m g s α q ℓ schedule a).information id=some info)
    (hclosed : id ∉ (recursiveRun m g s α q ℓ schedule b).closed) :
    ∀ k, a ≤ k → k ≤ b →
      info.level ≤ (recursiveRun m g s α q ℓ schedule k).top ∧
      ((recursiveRun m g s α q ℓ schedule k).frames info.level).id=id ∧
      ((recursiveRun m g s α q ℓ schedule k).frames info.level).N=info.scale ∧
      ((recursiveRun m g s α q ℓ schedule k).frames info.level).block=info.block := by
  intro k hak hkb
  have hi := information_run_persistent m g s α q ℓ schedule a k id info hak hinfo
  rcases call_locations_run m g s α q ℓ schedule k id info hi with hc|hc
  · exact False.elim (hclosed (closed_run_monotone m g s α q ℓ schedule hkb hc))
  · exact hc

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EventCallIntervals

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma running_call_information (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (hd : (recursiveRun m g s α q ℓ schedule t).done=false)
    (hid : ((recursiveRun m g s α q ℓ schedule t).frames (recursiveRun m g s α q ℓ schedule t).top).id=id) :
    let st := recursiveRun m g s α q ℓ schedule t
    st.information id=some ⟨st.top,(st.frames st.top).N,(st.frames st.top).block⟩ ∧ id ∉ st.closed := by
  intro st
  have hi := open_frame_information_run m g s α q ℓ schedule t st.top le_rfl
  have hn := running_open_not_closed_run m g s α q ℓ schedule t hd st.top le_rfl
  rw [hid] at hi hn
  exact ⟨hi,hn⟩

lemma full_solve_event_span (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a ≤ b)
    (ha : fullSolveEvent g (recursiveRun m g s α q ℓ schedule a) id)
    (hb : fullSolveEvent g (recursiveRun m g s α q ℓ schedule b) id) :
    let run := recursiveRun m g s α q ℓ schedule
    let st := run a
    ∀ k, a ≤ k → k ≤ b → st.top ≤ (run k).top ∧
      ((run k).frames st.top).id=id ∧ ((run k).frames st.top).N=(st.frames st.top).N ∧
      ((run k).frames st.top).block=(st.frames st.top).block := by
  intro run st
  rcases ha with ⟨hda,hcompa,hpca,hexa,hvala,hida⟩
  rcases hb with ⟨hdb,hcompb,hpcb,hexb,hvalb,hidb⟩
  have hia := (running_call_information m g s α q ℓ schedule a id hda hida).1
  have hnb := (running_call_information m g s α q ℓ schedule b id hdb hidb).2
  exact unclosed_call_interval m g s α q ℓ schedule a b id
    ⟨st.top,(st.frames st.top).N,(st.frames st.top).block⟩ hia hnb

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ProductionIntervals

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma offset_sum_difference (f : ℕ → ℝ) (a d : ℕ) :
    (∑ k ∈ Finset.range d, (f (a+k+1)-f (a+k))) = f (a+d)-f a := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ,ih]
    rw [show a+(d+1)=a+d+1 by omega]
    ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OutsideFlowIntervals

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma outsideMass_sub (g : InputGraph n) (F : Finset (Fin n)) (x y : Fin n → ℝ) :
    outsideMass g F (x-y) = outsideMass g F x-outsideMass g F y := by
  simp [outsideMass,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]

lemma outsideMass_interval_flow (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b) (F : Finset (Fin n))
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top ∧
      ((recursiveRun m g s α q ℓ schedule k).frames j).active ⊆ F) :
    (1-α)*outsideMass g F ((recursiveRun m g s α q ℓ schedule b).x-(recursiveRun m g s α q ℓ schedule a).x) ≤
      ∑ k ∈ Finset.range (b-a), incomingProduction g α (recursiveRun m g s α q ℓ schedule (a+k)) j := by
  have hh : (∑ k ∈ Finset.range (b-a), (1-α)*(outsideMass g F (recursiveRun m g s α q ℓ schedule (a+k+1)).x-
      outsideMass g F (recursiveRun m g s α q ℓ schedule (a+k)).x)) ≤
      ∑ k ∈ Finset.range (b-a), incomingProduction g α (recursiveRun m g s α q ℓ schedule (a+k)) j := by
    apply Finset.sum_le_sum
    intro k hk
    have hkt : a+k < b := by have := Finset.mem_range.mp hk; omega
    obtain ⟨hj,hF⟩ := hopen (a+k) (by omega) hkt
    have hh := outsideMass_step_flow m g s α hα.2.le ℓ schedule (recursiveRun m g s α q ℓ schedule (a+k))
      (region_run m g s α q ℓ schedule (a+k)) (parameters_run m g s α q hq ℓ schedule (a+k))
      (numerical_run m g s α q hα hq hs ℓ schedule (a+k)) (keys_run m g s α q hq.le ℓ schedule (a+k))
      (isolate_run m g s α q hs ℓ schedule (a+k)) j hj F hF
    simpa only [recursiveRun,Function.iterate_succ_apply'] using hh
  rw [←Finset.mul_sum,offset_sum_difference (fun t => outsideMass g F (recursiveRun m g s α q ℓ schedule t).x) a (b-a),
    Nat.add_sub_of_le hab] at hh
  rwa [outsideMass_sub]

lemma final_active_outside_flow (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top) :
    (1-α)*outsideMass g ((recursiveRun m g s α q ℓ schedule b).frames j).active
      ((recursiveRun m g s α q ℓ schedule b).x-(recursiveRun m g s α q ℓ schedule a).x) ≤
      ∑ k ∈ Finset.range (b-a), incomingProduction g α (recursiveRun m g s α q ℓ schedule (a+k)) j := by
  apply outsideMass_interval_flow m g s α q hα hq hs ℓ schedule a b j hab _
  intro k hak hkb
  exact ⟨hopen k hak hkb,active_interval_growth m g s α q ℓ schedule k b j hkb.le
    (fun t hkt htb => hopen t (hak.trans hkt) htb)⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ChargedSolveComparison

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma charged_full_solve_comparison (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b : ℕ) (hab : a+1 ≤ b) :
    let run := recursiveRun m g s α q ℓ schedule
    let st := run a
    let next := run b
    let j := st.top
    let H := (st.frames j).active
    let F := (next.frames j).active
    let Z := F \ H
    let h := solveOn g α H (st.frames j).residual
    let D := doubledSet H h (virtualPotential st j)
    (∀ k, a ≤ k → k < b → j ≤ (run k).top) → j ≤ next.top →
    st.done = false → ¬componentComplete st → (st.frames j).pc = .fullSolve →
      ¬anyExhausted st → pendingPush st = none →
      (∑ v ∈ F, (next.frames j).residual v) ≤
        (∑ k ∈ Finset.range (b-(a+1)), incomingProduction g α (run (a+1+k)) j)+
        4*(kappa ℓ 0 : ℝ)*(st.frames j).q*(volumeNat g Z : ℝ)+
        2*(kappa ℓ 0 : ℝ)*(st.frames j).q*(volumeNat g D : ℝ)+
        2*∑ v ∈ D, (st.frames j).residual v := by
  intro run st next j H F Z h D hopen hjnext hd hc hpc he hn
  have hcomp := actual_full_solve_comparison m g s α q hα hq hs ℓ schedule a b hab hopen hjnext hd hc hpc he hn
  have hflow := final_active_outside_flow m g s α q hα hq hs ℓ schedule (a+1) b j hab
    (fun k hak hkb => hopen k (by omega) hkb)
  change (1-α)*outsideMass g F (next.x-(run (a+1)).x) ≤ _ at hflow
  change (∑ v ∈ F, (next.frames j).residual v) ≤
    (1-α)*outsideMass g F (next.x-(run (a+1)).x)+
    4*(kappa ℓ 0 : ℝ)*(st.frames j).q*(volumeNat g Z : ℝ)+
    2*(kappa ℓ 0 : ℝ)*(st.frames j).q*(volumeNat g D : ℝ)+
    2*∑ v ∈ D, (st.frames j).residual v at hcomp
  linarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FullSolveHalving

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma successful_full_solve_nonhalving (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a < b)
    (ha : fullSolveEvent g (recursiveRun m g s α q ℓ schedule a) id)
    (hb : fullSolveEvent g (recursiveRun m g s α q ℓ schedule b) id)
    (hf : currentPC (recursiveRun m g s α q ℓ schedule (a-2))=.finishEpisode) :
    let run := recursiveRun m g s α q ℓ schedule
    let j := (run a).top
    let H := ((run a).frames j).active
    let F := ((run b).frames j).active
    let μ := ∑ v ∈ H, ((run a).frames j).residual v
    let μnext := ∑ v ∈ F, ((run b).frames j).residual v
    let J := (∑ k ∈ Finset.range (b-(a+1)), incomingProduction g α (run (a+1+k)) j)+
      4*(kappa ℓ 0 : ℝ)*((run a).frames j).q*(volumeNat g (F \ H) : ℝ)
    μ/2 ≤ μnext → μ/4 ≤ J ∨
      (((run a).frames j).block : ℝ)/(64*(kappa ℓ 0 : ℝ)) <
        (volumeNat g (fullSolveDoubles g α (run a) j) : ℝ) := by
  intro run j H F μ μnext J hnonhalf
  have hspan := full_solve_event_span m g s α q ℓ schedule a b id hab.le ha hb
  have hsuccess := successful_full_event_bounds m g s α q hα hq hs ℓ schedule a id ha hf
  have hparams := parameters_run m g s α q hq ℓ schedule a j le_rfl
  have hblock : (0 : ℝ) < ((run a).frames j).block := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hparams.2.1
  have hcompare := charged_full_solve_comparison m g s α q hα hq hs ℓ schedule a b (by omega)
    (fun k hak hkb => (hspan k hak hkb.le).1) (hspan b hab.le le_rfl).1
    ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1
    (full_drained_run m g s α q ℓ schedule a ha.2.2.1)
  have hR := weighted_density_bound g (fullSolveDoubles g α (run a) j) H
    ((run a).frames j).residual (Finset.filter_subset _ _) (kappa ℓ 0 : ℝ) (2*μ)
    ((run a).frames j).block hsuccess.2
  have hh := nonhalving_exception (kappa ℓ 0 : ℝ) ((run a).frames j).q ((run a).frames j).block
    μ J (volumeNat g (fullSolveDoubles g α (run a) j) : ℝ)
    (∑ v ∈ fullSolveDoubles g α (run a) j, ((run a).frames j).residual v) μnext
    (by unfold kappa; positivity) hparams.1 hblock hsuccess.1 (by positivity) hR
    (by simpa only [run,j,H,F,μ,μnext,J,fullSolveDoubles,add_assoc] using hcompare) hnonhalf
  exact hh

end
end NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal

theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a < b)
    (ha : fullSolveEvent g (recursiveRun m g s α q ℓ schedule a) id)
    (hb : fullSolveEvent g (recursiveRun m g s α q ℓ schedule b) id)
    (hf : currentPC (recursiveRun m g s α q ℓ schedule (a-2))=.finishEpisode) :
    let run := recursiveRun m g s α q ℓ schedule
    let j := (run a).top
    let H := ((run a).frames j).active
    let F := ((run b).frames j).active
    let μ := ∑ v ∈ H, ((run a).frames j).residual v
    let μnext := ∑ v ∈ F, ((run b).frames j).residual v
    let J := (∑ k ∈ Finset.range (b-(a+1)), incomingProduction g α (run (a+1+k)) j)+
      4*(kappa ℓ 0 : ℝ)*((run a).frames j).q*(volumeNat g (F \ H) : ℝ)
    μ/2 ≤ μnext → μ/4 ≤ J ∨
      (((run a).frames j).block : ℝ)/(64*(kappa ℓ 0 : ℝ)) <
        (volumeNat g (fullSolveDoubles g α (run a) j) : ℝ) := by
  exact successful_full_solve_nonhalving m g s α q hα hq hs ℓ schedule a b id hab ha hb hf
