-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_own_work_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:06:30.765944+00:00
-- url     : https://prove2.me/submissions/434519ac-c542-454f-88b7-4e9e00760626

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_budget_energy
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_discovery_credit
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_episode_count
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_cached_solve_count
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_stack_scales
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_call_metadata
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_discovery_effort
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_event_count
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_joint_solve_overhead

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

abbrev root_identity_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_residual_identities m n g s α q ℓ schedule t).2.1

abbrev layer_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_residual_identities m n g s α q ℓ schedule t).2.2.1

abbrev root_threshold_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_residual_identities m n g s α q ℓ schedule t).2.2.2

abbrev depth_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_control_parameters m n g s α q ℓ schedule t).1

abbrev budget_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_control_parameters m n g s α q ℓ schedule t).2.1

abbrev cache_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_control_parameters m n g s α q ℓ schedule t).2.2.1

abbrev parameters_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_control_parameters m n g s α q ℓ schedule t).2.2.2 hq

abbrev keys_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_queue_domains m n g s α q ℓ schedule t).1 hq

abbrev isolate_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_queue_domains m n g s α q ℓ schedule t).2.1 hs

abbrev stored_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_queue_domains m n g s α q ℓ schedule t).2.2 hq hs

abbrev numerical_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  recursive_numerical_invariants m n g s α q hα hq hs ℓ schedule t

abbrev budget_energy_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  recursive_budget_energy m n g s α q hα hq hs ℓ schedule t

abbrev stored_credit_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  recursive_discovery_credit m n g s α q hα hq hs ℓ schedule t

abbrev uniform_episode_count :=
  recursive_episode_count

abbrev uniform_cached_solve_count :=
  recursive_cached_solve_count

abbrev threshold_relation_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_stack_scales m n g s α q ℓ schedule t).1

abbrev stack_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_stack_scales m n g s α q ℓ schedule t).2.1

abbrev scale_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ) (hq : 0 < q)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_stack_scales m n g s α q ℓ schedule t).2.2 hq

abbrev information_id_bound_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_call_metadata m n g s α q ℓ schedule t).2.1

abbrev open_frame_information_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_call_metadata m n g s α q ℓ schedule t).2.2.2.2.1

abbrev call_discovery_effort_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) (info : CallInformation)
    (hinfo : (recursiveRun m g s α q ℓ schedule T).information id=some info) :=
  recursive_discovery_effort m n g s α q hα hq hs ℓ schedule T id info hinfo

abbrev control_prefix_count (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) :=
  recursive_control_event_count m n g s α q hq hs ℓ schedule T id

abbrev uniform_jointCost_overhead (m : SolveModel) :=
  recursive_joint_solve_overhead m

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

lemma virtual_state_identity (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hroot : RootIdentity g s α st) (hlayer : LayerIdentity g st)
    (j : ℕ) (hj : j ≤ st.top) (v : Fin n) :
    residual g.graph α s st.x v = thresholdSum st j*LocalPush.deg g.graph v+
      LocalPush.deg g.graph v*(if v ∈ (st.frames j).active then (st.frames j).q
        else 4*virtualPotential st j v)+virtualResidual g st j v := by
  induction j with
  | zero => simpa [thresholdSum,virtualPotential,virtualReference,virtualResidual,add_comm] using hroot v
  | succ j ih =>
    have hjj : j < st.top := by omega
    have he := ih (by omega)
    have hsum : thresholdSum st (j+1) = thresholdSum st j+(st.frames j).q := by
      simp [thresholdSum,Finset.sum_range_succ]
    rw [hsum]
    by_cases hv : v ∈ (st.frames j).active
    · have hlink := hlayer j hjj v hv
      have hactual := virtual_actual g st (j+1) v (by simpa [parentDomain] using hv)
      rw [hactual.1,hactual.2]
      simp only [hv,ite_true] at he
      rw [(virtual_actual g st j v ((hreg j hjj.le).1 hv)).2] at he
      rw [he,hlink]
      split_ifs <;> ring
    · have hout : v ∉ (st.frames (j+1)).active := by
        intro hh
        have hp := (hreg (j+1) hj).1 hh
        exact hv (by simpa [parentDomain] using hp)
      simp only [virtualResidual,virtualPotential,virtualReference,hv,hout,ite_false] at he ⊢
      rw [he]
      ring

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

-- Proof module: Solutions.StoredStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma run_active_domain_valid (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t i : ℕ)
    (hi : i ≤ (recursiveRun m g s α q ℓ schedule t).top) :
    let st := recursiveRun m g s α q ℓ schedule t
    (st.frames i).active ⊆ st.stored ∧ ∀ v ∈ (st.frames i).active, 0 < g.graph.degree v := by
  have hh := stored_run m g s α q hq hs ℓ schedule t
  exact ⟨hh.1 i hi,fun v hv => hh.2 v (hh.1 i hi hv)⟩

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

-- Proof module: Solutions.RootMass

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma lap_sum (g : InputGraph n) (α : ℝ) (x : Fin n → ℝ) :
    (∑ v, (LocalPush.Lα g.graph α *ᵥ x) v) = α*∑ v, LocalPush.deg g.graph v*x v := by
  classical
  have hadj (u : Fin n) : (∑ v, LocalPush.adjM g.graph v u) = LocalPush.deg g.graph u := by
    have he : (fun v => if g.graph.Adj v u then (1 : ℝ) else 0) =
        (fun v => if g.graph.Adj u v then (1 : ℝ) else 0) := by
      funext v
      simp only [g.graph.adj_comm]
    change (∑ v, if g.graph.Adj v u then (1 : ℝ) else 0) = _
    rw [he]
    exact (g.graph.degree_eq_sum_if_adj (R := ℝ) u).symm
  have hcol (u : Fin n) : (∑ v, LocalPush.Lα g.graph α v u) = α*LocalPush.deg g.graph u := by
    simp only [LocalPush.Lα,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      Finset.sum_sub_distrib,← Finset.mul_sum]
    rw [hadj]
    simp [LocalPush.degM,Matrix.diagonal]
    ring
  simp only [Matrix.mulVec,dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,hcol]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

lemma residual_sum (g : InputGraph n) (s : Fin n) (α : ℝ) (x : Fin n → ℝ) :
    (∑ v, residual g.graph α s x v) = 1-α*∑ v, LocalPush.deg g.graph v*x v := by
  simp [residual,Pi.sub_apply,Finset.sum_sub_distrib,lap_sum,LocalPush.e,Pi.single_apply]

lemma volume_real (g : InputGraph n) (H : Finset (Fin n)) :
    (volumeNat g H : ℝ) = ∑ v ∈ H, LocalPush.deg g.graph v := by
  simp [volumeNat,LocalPush.deg,neighbor_degree]

lemma root_volume_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hi : RootIdentity g s α st) (hn : NumericalInvariant g st) :
    (st.frames 0).q*(volumeNat g (st.frames 0).active : ℝ) ≤ 1 := by
  classical
  have hr (v : Fin n) : 0 ≤ (st.frames 0).residual v := by
    exact ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).1
  have hx (v : Fin n) : 0 ≤ st.x v := by
    simpa [relative] using ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).2.1
  have hd (v : Fin n) : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
  have hs : 0 ≤ ∑ v, LocalPush.deg g.graph v*st.x v :=
    Finset.sum_nonneg fun v _ => mul_nonneg (hd v) (hx v)
  have hb : (∑ v, if v ∈ (st.frames 0).active then
      (st.frames 0).q*LocalPush.deg g.graph v else 0) ≤ ∑ v, residual g.graph α s st.x v := by
    apply Finset.sum_le_sum
    intro v _
    rw [hi v]
    by_cases hv : v ∈ (st.frames 0).active
    · simp only [hv,ite_true]
      nlinarith [hr v]
    · simp only [hv,ite_false]
      nlinarith [hr v,mul_nonneg (hd v) (hx v)]
  have hsum : (∑ v, if v ∈ (st.frames 0).active then
      (st.frames 0).q*LocalPush.deg g.graph v else 0) =
      (st.frames 0).q*(volumeNat g (st.frames 0).active : ℝ) := by
    rw [volume_real,Finset.mul_sum,← Finset.sum_filter]
    congr 1
    ext v
    simp
  rw [hsum,residual_sum] at hb
  nlinarith [mul_nonneg hα hs]

lemma card_le_volume (g : InputGraph n) (H : Finset (Fin n))
    (hH : ∀ v ∈ H, 0 < g.graph.degree v) : H.card ≤ volumeNat g H := by
  calc
    H.card = ∑ v ∈ H, (1 : ℕ) := by simp
    _ ≤ ∑ v ∈ H, (g.neighbors v).length := by
      apply Finset.sum_le_sum
      intro v hv
      rw [neighbor_degree]
      exact hH v hv

lemma run_root_volume_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    (volumeNat g (st.frames 0).active : ℝ) ≤ 1/q ∧ ((st.frames 0).active.card : ℝ) ≤ 1/q := by
  let st := recursiveRun m g s α q ℓ schedule t
  have hv := root_volume_bound g s α hα.1.le st (root_identity_run m g s α q ℓ schedule t)
    (numerical_run m g s α q hα hq hs ℓ schedule t)
  have hq' : (st.frames 0).q = q := root_threshold_run m g s α q ℓ schedule t
  rw [hq'] at hv
  have hvol : (volumeNat g (st.frames 0).active : ℝ) ≤ 1/q := by
    apply (le_div_iff₀ hq).mpr
    nlinarith
  have hdom := run_active_domain_valid m g s α q hq.le hs ℓ schedule t 0 (Nat.zero_le _)
  have hcard : ((st.frames 0).active.card : ℝ) ≤ (volumeNat g (st.frames 0).active : ℝ) := by
    exact_mod_cast card_le_volume g (st.frames 0).active hdom.2
  exact ⟨hvol,hcard.trans hvol⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ChildVolume

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma child_volume_mass (g : InputGraph n) (st : RecursiveState n) (j : ℕ)
    (hj : j < st.top) (hreg : RegionInvariant st) (hnum : NumericalInvariant g st)
    (hlayer : LayerIdentity g st) :
    (st.frames (j+1)).q*(volumeNat g (st.frames (j+1)).active : ℝ) ≤
      ∑ v ∈ (st.frames j).active, (st.frames j).residual v := by
  classical
  have hsub : (st.frames (j+1)).active ⊆ (st.frames j).active := by
    simpa [parentDomain] using (hreg (j+1) hj).1
  rw [volume_real,Finset.mul_sum]
  calc
    _ ≤ ∑ v ∈ (st.frames (j+1)).active, (st.frames j).residual v := by
      apply Finset.sum_le_sum
      intro v hv
      have hpar : v ∈ parentDomain st (j+1) := (hreg (j+1) hj).1 hv
      have hr := ((hnum (j+1) hj).1 v hpar).1
      have he := hlayer j hj v (hsub hv)
      simp only [hv,ite_true] at he
      nlinarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro v hv _
      exact ((hnum j hj.le).1 v ((hreg j hj.le).1 hv)).1)

lemma child_volume_bound (g : InputGraph n) (st : RecursiveState n) (j : ℕ) (N : ℝ)
    (hj : j < st.top) (hreg : RegionInvariant st) (hnum : NumericalInvariant g st)
    (hlayer : LayerIdentity g st) (hq : 0 < (st.frames (j+1)).q)
    (hm : (∑ v ∈ (st.frames j).active, (st.frames j).residual v) <
      2*(st.frames (j+1)).q*N) :
    (volumeNat g (st.frames (j+1)).active : ℝ) < 2*N := by
  have hh := lt_of_le_of_lt (child_volume_mass g st j hj hreg hnum hlayer) hm
  nlinarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.GlobalDensity

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma global_active_identity (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hroot : RootIdentity g s α st) (hlayer : LayerIdentity g st)
    (j : ℕ) (hj : j ≤ st.top) (v : Fin n) (hv : v ∈ (st.frames j).active) :
    residual g.graph α s st.x v = (thresholdSum st j+(st.frames j).q)*LocalPush.deg g.graph v+
      (st.frames j).residual v := by
  have hh := virtual_state_identity g s α st hreg hroot hlayer j hj v
  rw [(virtual_actual g st j v ((hreg j hj).1 hv)).2] at hh
  simp only [hv,ite_true] at hh
  rw [hh]
  ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetEnergy

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma energyRow_nonneg (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) (j : ℕ) (v : Fin n) :
    0 ≤ energyRow g s α st j v := le_max_right _ _

lemma energyRow_active (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hroot : RootIdentity g s α st) (hlayer : LayerIdentity g st)
    (hnum : NumericalInvariant g st) (j : ℕ) (hj : j ≤ st.top) (v : Fin n)
    (hv : v ∈ (st.frames j).active) :
    energyRow g s α st j v = (st.frames j).residual v := by
  unfold energyRow
  rw [global_active_identity g s α st hreg hroot hlayer j hj v hv]
  simp only [hv,ite_true,add_zero,add_sub_cancel_left]
  exact max_eq_left (((hnum j hj).1 v ((hreg j hj).1 hv)).1)

lemma active_mass_le_budgetEnergy (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hroot : RootIdentity g s α st) (hlayer : LayerIdentity g st)
    (hnum : NumericalInvariant g st) (j : ℕ) (hj : j ≤ st.top) :
    (∑ v ∈ (st.frames j).active, (st.frames j).residual v) ≤ budgetEnergy g s α st j := by
  calc
    _ = ∑ v ∈ (st.frames j).active, energyRow g s α st j v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact (energyRow_active g s α st hreg hroot hlayer hnum j hj v hv).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => energyRow_nonneg g s α st j v)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetMass

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma run_budget_mass_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t j : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    j ≤ st.top → (st.frames j).openBudget = true →
      (∑ v ∈ (st.frames j).active, (st.frames j).residual v) ≤ (st.frames j).Q+(st.frames j).W := by
  intro st hj hb
  exact (active_mass_le_budgetEnergy g s α st (region_run m g s α q ℓ schedule t)
    (root_identity_run m g s α q ℓ schedule t) (layer_run m g s α q ℓ schedule t)
    (numerical_run m g s α q hα hq hs ℓ schedule t) j hj).trans
      (budget_energy_run m g s α q hα hq hs ℓ schedule t j hj hb)

lemma run_unexhausted_mass (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t j : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    j ≤ st.top → (st.frames j).openBudget = true → ¬exhausted st j →
      (∑ v ∈ (st.frames j).active, (st.frames j).residual v) < 2*(st.frames j).Q := by
  intro st hj hb he
  have hW : (st.frames j).W < (st.frames j).Q := by
    by_contra hn
    exact he ⟨hb,le_of_not_gt hn⟩
  have hm := run_budget_mass_bound m g s α q hα hq hs ℓ schedule t j hj hb
  linarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DiscoveryCredit

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_reserve_mass_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hi : RootIdentity g s α st) (hn : NumericalInvariant g st) :
    (st.frames 0).q*(volumeNat g (st.frames 0).active : ℝ)+
      4*(∑ v ∈ Finset.univ \ (st.frames 0).active, LocalPush.deg g.graph v*st.x v) ≤ 1 := by
  classical
  have hr (v : Fin n) : 0 ≤ (st.frames 0).residual v :=
    ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).1
  have hx (v : Fin n) : 0 ≤ st.x v := by
    simpa [relative] using ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).2.1
  have hd (v : Fin n) : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
  have hs : 0 ≤ ∑ v, LocalPush.deg g.graph v*st.x v :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (hd v) (hx v))
  have hb : (∑ v, LocalPush.deg g.graph v*(if v ∈ (st.frames 0).active then (st.frames 0).q else 4*st.x v)) ≤
      ∑ v, residual g.graph α s st.x v := by
    apply Finset.sum_le_sum
    intro v _
    rw [hi v]
    linarith [hr v]
  have hsum : (∑ v, LocalPush.deg g.graph v*(if v ∈ (st.frames 0).active then (st.frames 0).q else 4*st.x v)) =
      (st.frames 0).q*(volumeNat g (st.frames 0).active : ℝ)+
        4*(∑ v ∈ Finset.univ \ (st.frames 0).active, LocalPush.deg g.graph v*st.x v) := by
    rw [volume_real,Finset.mul_sum,Finset.mul_sum]
    have hfirst : (∑ v ∈ (st.frames 0).active, (st.frames 0).q*LocalPush.deg g.graph v) =
        ∑ v, if v ∈ (st.frames 0).active then (st.frames 0).q*LocalPush.deg g.graph v else 0 := by
      rw [←Finset.sum_filter]
      apply Finset.sum_congr
      · ext v; simp
      · intro v _; rfl
    have hsecond : (∑ v ∈ Finset.univ \ (st.frames 0).active, 4*(LocalPush.deg g.graph v*st.x v)) =
        ∑ v, if v ∉ (st.frames 0).active then 4*(LocalPush.deg g.graph v*st.x v) else 0 := by
      rw [←Finset.sum_filter]
      apply Finset.sum_congr
      · ext v; simp
      · intro v _; rfl
    rw [hfirst,hsecond,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ (st.frames 0).active <;> simp [hv] <;> ring

  rw [hsum,residual_sum] at hb
  nlinarith [mul_nonneg hα hs]

lemma root_discoveryCredit_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hi : RootIdentity g s α st) (hn : NumericalInvariant g st)
    (hq : 0 ≤ (st.frames 0).q) : discoveryCredit g st 0 ≤ 3/8 := by
  have hh := root_reserve_mass_bound g s α hα st hi hn
  have hs : 0 ≤ ∑ v ∈ Finset.univ \ (st.frames 0).active, LocalPush.deg g.graph v*st.x v := by
    apply Finset.sum_nonneg
    intro v _
    apply mul_nonneg
    · unfold LocalPush.deg; positivity
    · simpa [relative] using ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).2.1
  unfold discoveryCredit
  simp only [parentDomain,ite_true,relative]
  nlinarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueueMass

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_residual_mass_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hi : RootIdentity g s α st) (hn : NumericalInvariant g st)
    (hq : 0 ≤ (st.frames 0).q) : (∑ v, (st.frames 0).residual v) ≤ 1 := by
  classical
  have hx (v : Fin n) : 0 ≤ st.x v := by
    simpa [relative] using ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).2.1
  have hd (v : Fin n) : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
  have hs : 0 ≤ ∑ v, LocalPush.deg g.graph v*st.x v :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (hd v) (hx v))
  have hh : (∑ v, (st.frames 0).residual v) ≤ ∑ v, residual g.graph α s st.x v := by
    apply Finset.sum_le_sum
    intro v _
    rw [hi v]
    apply le_add_of_nonneg_right
    apply mul_nonneg (hd v)
    split
    · exact hq
    · have hh := hx v; positivity
  rw [residual_sum] at hh
  nlinarith [mul_nonneg hα hs]

lemma root_exterior_positive (g : InputGraph n) (st : RecursiveState n)
    (hk : KeysInvariant g st) (hiso : IsolateResidual g st) (v : Fin n)
    (hv : v ∈ (st.frames 0).exterior) : 0 < g.graph.degree v := by
  have hh := (((hk 0 (Nat.zero_le _)).1 v).mp hv).2.2
  by_contra hn
  have hd : g.graph.degree v = 0 := by omega
  have hr := hiso 0 (Nat.zero_le _) v hd
  simp [LocalPush.deg,hd,hr] at hh

lemma root_exterior_mass_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hi : RootIdentity g s α st) (hn : NumericalInvariant g st)
    (hk : KeysInvariant g st) (hq : 0 < (st.frames 0).q) :
    (volumeNat g (st.frames 0).exterior : ℝ) ≤ 1/(st.frames 0).q := by
  classical
  have hr := root_residual_mass_bound g s α hα st hi hn hq.le
  have hsum : (∑ v ∈ (st.frames 0).exterior, (st.frames 0).residual v) ≤ ∑ v, (st.frames 0).residual v :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ =>
      ((hn 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).1)
  have hh : (st.frames 0).q*(volumeNat g (st.frames 0).exterior : ℝ) ≤
      ∑ v ∈ (st.frames 0).exterior, (st.frames 0).residual v := by
    rw [volume_real,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    exact ((((hk 0 (Nat.zero_le _)).1 v).mp hv).2.2).le
  apply (le_div_iff₀ hq).mpr
  nlinarith [hh.trans (hsum.trans hr)]

lemma run_stored_volume_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    (volumeNat g (recursiveRun m g s α q ℓ schedule t).stored : ℝ) ≤ 3/q := by
  let st := recursiveRun m g s α q ℓ schedule t
  have hi : StoredCreditInvariant g st := stored_credit_run m g s α q hα hq hs ℓ schedule t
  have hqr : (st.frames 0).q = q := root_threshold_run m g s α q ℓ schedule t
  have hqr0 : 0 ≤ (st.frames 0).q := by rw [hqr]; exact hq.le
  have hc := root_discoveryCredit_bound g s α hα.1.le st (root_identity_run m g s α q ℓ schedule t)
    (numerical_run m g s α q hα hq hs ℓ schedule t) hqr0
  have hv := root_volume_bound g s α hα.1.le st (root_identity_run m g s α q ℓ schedule t)
    (numerical_run m g s α q hα hq hs ℓ schedule t)
  rw [hqr] at hv
  unfold StoredCreditInvariant rootScanPotential at hi
  rw [hqr] at hi
  have hm := mul_le_mul_of_nonneg_left hi hq.le
  have hcancel : q*(5/q*discoveryCredit g st 0+(volumeNat g (st.frames 0).active : ℝ)) =
      5*discoveryCredit g st 0+q*(volumeNat g (st.frames 0).active : ℝ) := by
    field_simp [hq.ne'] <;> ring
  rw [hcancel] at hm
  change (volumeNat g st.stored : ℝ) ≤ _
  apply (le_div_iff₀ hq).mpr
  nlinarith

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ProductionUnexhausted

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma production_unexhausted (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hp : stepProduction st=some (t,v)) : ¬anyExhausted st := by
  intro hx
  cases hpc : (st.frames st.top).pc <;>
    simp [stepProduction,drainProduction,hpc,hx] at hp <;>
    (try split_ifs at hp) <;> simp_all

lemma production_running (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hp : stepProduction st=some (t,v)) : st.done=false ∧ ¬componentComplete st := by
  have hd : st.done=false := by
    cases hh : st.done
    · rfl
    · simp only [stepProduction,hh,ite_true] at hp
      cases hp
  refine ⟨hd,?_⟩
  intro hc
  simp only [stepProduction,hd,Bool.false_eq_true,ite_false,hc,ite_true] at hp
  cases hp

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OperationalVolumes

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma run_child_volume_unexhausted (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t j : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    j < st.top → ¬exhausted st j →
      (volumeNat g (st.frames (j+1)).active : ℝ) < 2*(st.frames (j+1)).N := by
  intro st hj he
  have hbudget : BudgetInvariant st := budget_run m g s α q ℓ schedule t
  have hstack : StackInvariant st := stack_run m g s α q ℓ schedule t
  have hb : (st.frames j).openBudget = true := by
    simpa [hstack j hj,budgetPC] using hbudget j hj.le
  have hm := run_unexhausted_mass m g s α q hα hq hs ℓ schedule t j hj.le hb he
  have hscale : ScaleInvariant st := scale_run m g s α q hq ℓ schedule t
  have hQ := hscale.1 j hj.le hb
  have hN := hscale.2 j hj
  have hth : (st.frames (j+1)).q = (st.frames j).theta :=
    threshold_relation_run m g s α q ℓ schedule t j hj
  have hp : ParameterInvariant st := parameters_run m g s α q hq ℓ schedule t
  apply child_volume_bound g st j (st.frames (j+1)).N hj
    (region_run m g s α q ℓ schedule t) (numerical_run m g s α q hα hq hs ℓ schedule t)
    (layer_run m g s α q ℓ schedule t) (hp (j+1) hj).1
  change (∑ v ∈ (st.frames j).active, (st.frames j).residual v) < 2*(st.frames j).Q at hm
  rw [hQ] at hm
  rw [hth,hN]
  simpa [mul_assoc] using hm

lemma cache_volume_mass (g : InputGraph n) (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top)
    (hreg : RegionInvariant st) (hnum : NumericalInvariant g st) (hkeys : KeysInvariant g st)
    (hθ : 0 ≤ (st.frames j).theta) :
    (st.frames j).theta*(volumeNat g ((st.frames j).cache ∪ (st.frames j).high) : ℝ) ≤
      ∑ v ∈ (st.frames j).active, (st.frames j).residual v := by
  classical
  let C := (st.frames j).cache ∪ (st.frames j).high
  have hC : C ⊆ (st.frames j).active := Finset.union_subset_iff.mpr
    ⟨(hreg j hj).2.2.2,(hreg j hj).2.2.1⟩
  rw [volume_real,Finset.mul_sum]
  calc
    _ ≤ ∑ v ∈ C, (st.frames j).residual v := by
      apply Finset.sum_le_sum
      intro v hv
      have hd : 0 ≤ (st.frames j).theta*LocalPush.deg g.graph v := by
        apply mul_nonneg hθ
        unfold LocalPush.deg
        positivity
      obtain hv|hv := Finset.mem_union.mp hv
      · exact (hnum j hj).2 v hv
      · have hh := ((hkeys j hj).2 v).mp hv
        nlinarith [hh.2]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hC (fun v hv _ =>
      ((hnum j hj).1 v ((hreg j hj).1 hv)).1)

lemma run_cache_volume_unexhausted (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    (st.frames st.top).pc = .leafDrain → ¬exhausted st st.top →
      (volumeNat g ((st.frames st.top).cache ∪ (st.frames st.top).high) : ℝ) <
        2*(st.frames st.top).block := by
  intro st hpc he
  have hbudget : BudgetInvariant st := budget_run m g s α q ℓ schedule t
  have hb : (st.frames st.top).openBudget = true := by
    simpa [hpc,budgetPC] using hbudget st.top le_rfl
  have hp : ParameterInvariant st := parameters_run m g s α q hq ℓ schedule t
  have hθ : 0 < (st.frames st.top).theta := (hp st.top le_rfl).1.trans_le ((hp st.top le_rfl).2.2 hb)
  have hm := run_unexhausted_mass m g s α q hα hq hs ℓ schedule t st.top le_rfl hb he
  have hE := cache_volume_mass g st st.top le_rfl (region_run m g s α q ℓ schedule t)
    (numerical_run m g s α q hα hq hs ℓ schedule t) (keys_run m g s α q hq.le ℓ schedule t) hθ.le
  have hscale : ScaleInvariant st := scale_run m g s α q hq ℓ schedule t
  have hQ := hscale.1 st.top le_rfl hb
  change (∑ v ∈ (st.frames st.top).active, (st.frames st.top).residual v) < 2*(st.frames st.top).Q at hm
  rw [hQ] at hm
  nlinarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DebitEvents

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 1500000 in
lemma production_debit (m : SolveModel) (g : InputGraph n) (α : ℝ) (ℓ : ℕ) (st : RecursiveState n)
    (j : ℕ) (v : Fin n) (hp : stepProduction st=some (j,v)) :
    stepDebit m g α ℓ st=(j,((32*(st.top+1)*((g.neighbors v).length+1)*keyCost (exteriorPush g α st j v) : ℕ) : ℝ≥0∞)) := by
  have hd := (production_running st j v hp).1
  have hcomp := (production_running st j v hp).2
  have hpend := production_pending st j v hp
  have hno := production_unexhausted st j v hp
  cases hpc : (st.frames st.top).pc <;>
    simp_all [stepDebit,stepProduction,drainProduction] <;> (try split_ifs at hp ⊢) <;> simp_all

set_option maxHeartbeats 1500000 in
lemma nonproducing_debit_producer (m : SolveModel) (g : InputGraph n) (α : ℝ) (ℓ : ℕ)
    (st : RecursiveState n) (hd : st.done=false) (hp : stepProduction st=none) :
    (stepDebit m g α ℓ st).1=if componentComplete st then 0 else st.top := by
  by_cases hc : componentComplete st
  · simp [stepDebit,hd,hc]
  cases hpend : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;> simp [stepDebit,hd,hc,hpc,hpend] <;>
      (try split_ifs) <;> simp_all
  | some p =>
    obtain ⟨j,v⟩ := p
    cases hpc : (st.frames st.top).pc <;> simp [stepDebit,hd,hc,hpc,hpend] <;>
      (try split_ifs) <;> simp_all [stepProduction,drainProduction]

lemma cached_debit (m : SolveModel) (g : InputGraph n) (α : ℝ) (ℓ : ℕ)
    (st : RecursiveState n) (id : ℕ) (hc : cachedSolveEvent g st id) :
    stepDebit m g α ℓ st=(st.top,jointCost m g st ((st.frames st.top).cache ∪ (st.frames st.top).high)) := by
  obtain ⟨hd,hcomp,hpc,hno,hp,hhigh,hvalid,_⟩ := hc
  simp only [stepDebit,hd,Bool.false_eq_true,ite_false,hcomp,hpc,hno,hp,Option.isSome_none,
    Bool.false_eq_true,hhigh,hvalid,ite_true]
  simp_all only [true_and,ite_true,implies_true]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RunningStepGuards

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma running_step_guards (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hn : (recursiveStep m g s α ℓ schedule st).done = false) :
    st.done = false ∧ ¬componentComplete st := by
  classical
  have hd : st.done = false := by
    cases hh : st.done
    · rfl
    · simp [recursiveStep,hh] at hn
  refine ⟨hd,?_⟩
  intro hc
  simp [recursiveStep,hd,hc,completeComponent] at hn

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BeginEpisodeOrigin

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 3000000 in
lemma begin_episode_step_origin (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hstack : StackInvariant st)
    (hrunning : (recursiveStep m g s α ℓ schedule st).done = false)
    (hfull : currentPC (recursiveStep m g s α ℓ schedule st) = .beginEpisode) :
    (st.frames st.top).pc = .initialDrain ∨ (st.frames st.top).pc = .restartDrain ∨ (st.frames st.top).pc = .finishEpisode := by
  have hg := running_step_guards m g s α ℓ schedule st hrunning
  have hparent : st.top ≠ 0 → (st.frames (st.top-1)).pc = .afterChild := by
    intro hh
    exact hstack (st.top-1) (by omega)
  by_contra hn
  cases hpend : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp only [recursiveStep,hg.1,Bool.false_eq_true,ite_false,hg.2,hpc] at hfull <;>
      (try split_ifs at hfull) <;>
      simp_all (config := {maxSteps := 1000000}) [currentPC,changePC,changeFrame,debit,refreshKeys,jointUpdate,
        finishEpisode,endCall,freshFrame,emptyFrame,Function.update_apply] <;>
      (try split_ifs at hfull) <;> simp_all
  | some p =>
    obtain ⟨t,v⟩ := p
    cases hpc : (st.frames st.top).pc <;>
      simp only [recursiveStep,hg.1,Bool.false_eq_true,ite_false,hg.2,hpc] at hfull <;>
      (try split_ifs at hfull) <;>
      simp_all (config := {maxSteps := 1000000}) [currentPC,changePC,changeFrame,debit,refreshKeys,jointUpdate,
        finishEpisode,endCall,freshFrame,emptyFrame,Function.update_apply] <;>
      (try split_ifs at hfull) <;> simp_all

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BeginUnexhausted

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma ancestorExhausted_metadata (st : RecursiveState n) (f : NormalizeFrame n → NormalizeFrame n) :
    ancestorExhausted (changeFrame st st.top f) ↔ ancestorExhausted st := by
  unfold ancestorExhausted
  apply exists_congr
  intro i
  by_cases hi : i < st.top
  · simp [hi,exhausted,changeFrame,ne_of_lt hi]
  · simp [hi,changeFrame]

@[simp] lemma ancestorExhausted_PC (st : RecursiveState n) (pc : NormalizePC) :
    ancestorExhausted (changePC st pc) ↔ ancestorExhausted st := ancestorExhausted_metadata st _

@[simp] lemma ancestorExhausted_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    ancestorExhausted (debit st j w) ↔ ancestorExhausted st := Iff.rfl

@[simp] lemma ancestorExhausted_finish (st : RecursiveState n) :
    ancestorExhausted (finishEpisode st) ↔ ancestorExhausted st := by
  unfold finishEpisode
  rw [ancestorExhausted_metadata]
  rfl

set_option maxHeartbeats 2000000 in
lemma begin_episode_step_unexhausted (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hstack : StackInvariant st)
    (hrunning : (recursiveStep m g s α ℓ schedule st).done=false)
    (hbegin : currentPC (recursiveStep m g s α ℓ schedule st)=.beginEpisode) :
    ¬ancestorExhausted (recursiveStep m g s α ℓ schedule st) := by
  obtain ⟨hd,hcomp⟩ := running_step_guards m g s α ℓ schedule st hrunning
  rcases begin_episode_step_origin m g s α ℓ schedule st hstack hrunning hbegin with hpc|hpc|hpc
  all_goals
    have hanc : ¬ancestorExhausted st := by
      intro hh
      simp [currentPC,recursiveStep,hd,hcomp,hpc,hh,changePC,changeFrame,debit] at hbegin
    cases hpend : pendingPush st with
    | none =>
      simp [recursiveStep,hd,hcomp,hpc,hanc,hpend] <;> (try split_ifs) <;>
        simp_all [currentPC,recursiveStep,hd,hcomp,hpc,hanc,hpend,changePC,changeFrame,finishEpisode,debit] <;>
        (intro hh; obtain ⟨i,hi,hex⟩ := hh; change i < st.top at hi
         apply hanc
         refine ⟨i,hi,?_⟩
         have hne : i ≠ st.top := ne_of_lt hi
         simpa only [exhausted,Function.update_of_ne hne] using hex)
    | some p =>
      obtain ⟨t,v⟩ := p
      simp [recursiveStep,hd,hcomp,hpc,hanc,hpend] <;> (try split_ifs) <;>
        simp_all [currentPC,recursiveStep,hd,hcomp,hpc,hanc,hpend,changePC,changeFrame,finishEpisode,debit] <;>
        (intro hh; obtain ⟨i,hi,hex⟩ := hh; change i < st.top at hi
         apply hanc
         refine ⟨i,hi,?_⟩
         have hne : i ≠ st.top := ne_of_lt hi
         simpa only [exhausted,Function.update_of_ne hne] using hex)

lemma begin_episode_run_unexhausted (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ)
    (hrunning : (recursiveRun m g s α q ℓ schedule t).done=false)
    (hbegin : currentPC (recursiveRun m g s α q ℓ schedule t)=.beginEpisode) :
    ¬ancestorExhausted (recursiveRun m g s α q ℓ schedule t) := by
  cases t with
  | zero => simp [currentPC,recursiveRun,recursiveInit,freshFrame,emptyFrame] at hbegin
  | succ t =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      begin_episode_step_unexhausted m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule t)
        (stack_run m g s α q ℓ schedule t)
        (by simpa only [recursiveRun,Function.iterate_succ_apply'] using hrunning)
        (by simpa only [recursiveRun,Function.iterate_succ_apply'] using hbegin)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrozenFrame

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma frozenFrame_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t j : ℕ) (v : Fin n) :
    frozenFrame ((exteriorPush g α st t v).frames j) = frozenFrame (st.frames j) :=
  congrArg (fun f => (f.1,f.2.2.2.2.1,f.2.2.2.2.2.1,f.2.2.2.2.2.2))
    (exterior_parameters g α st t v j)

lemma frozenFrame_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ) (pc : NormalizePC) :
    frozenFrame ((if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc).frames j) = frozenFrame (st.frames j) := by
  split
  · by_cases hj : j = st.top <;> simp [frozenFrame,changePC,changeFrame,debit,hj]
  · cases hp : pendingPush st with
    | none => by_cases hj : j = st.top <;> simp [frozenFrame,changePC,changeFrame,debit,hj]
    | some p => obtain ⟨t,v⟩ := p; exact frozenFrame_exterior g α st t j v

set_option maxHeartbeats 1000000 in
lemma frozenFrame_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top) :
    frozenFrame ((recursiveStep m g s α ℓ schedule st).frames j) = frozenFrame (st.frames j) := by
  classical
  have hnew : j ≠ st.top+1 := by omega
  by_cases hd : st.done = true
  · simp [recursiveStep,hd]
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp [hc,completeComponent,debit]
  simp only [hc,ite_false]
  have hdrain := frozenFrame_drain g α st j
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · by_cases he : j = st.top <;> simp [frozenFrame,changePC,changeFrame,debit,he,hj]
    · split
      · exact hdrain _
      · split <;> (by_cases he : j = st.top) <;> simp [frozenFrame,changePC,changeFrame,debit,he,hj]
  | beginEpisode =>
    simp only [hpc]
    by_cases he : j = st.top <;> simp [frozenFrame,changeFrame,debit,he,hj]
  | fullSolve =>
    simp only [hpc]
    split
    · by_cases he : j = st.top <;> simp [frozenFrame,changePC,changeFrame,debit,he,hj]
    · split
      · by_cases he : j = st.top <;> simp [frozenFrame,changePC,changeFrame,debit,refreshKeys,jointUpdate,he,hj]
      · rfl
  | normalize =>
    simp only [hpc]
    split
    · by_cases he : j = st.top <;> simp [frozenFrame,changePC,changeFrame,debit,he,hj]
    · split
      · by_cases he : j = st.top <;> simp [frozenFrame,changePC,changeFrame,debit,he,hj]
      · by_cases he : j = st.top <;> simp [frozenFrame,changeFrame,debit,he,hnew]
  | leafDrain =>
    simp only [hpc]
    split
    · by_cases he : j = st.top <;> simp [frozenFrame,changePC,changeFrame,debit,he,hj]
    · split
      · cases hh : pendingPush st with
        | none => by_cases he : j = st.top <;> simp [frozenFrame,changePC,changeFrame,debit,he,hj]
        | some p => obtain ⟨t,v⟩ := p; exact frozenFrame_exterior g α st t j v
      · split
        · by_cases he : j = st.top <;> simp [frozenFrame,changePC,changeFrame,debit,he,hj]
        · split
          · by_cases he : j = st.top <;> simp [frozenFrame,debit,refreshKeys,jointUpdate,changeFrame,he,hj]
          · rfl
  | afterChild =>
    simp only [hpc]
    split
    · by_cases he : j = st.top <;> simp [frozenFrame,changePC,changeFrame,debit,finishEpisode,he,hj]
    · split
      · by_cases he : j = st.top <;> simp [frozenFrame,changePC,changeFrame,debit,finishEpisode,he,hj]
      · exact hdrain _
  | finishEpisode =>
    simp only [hpc]
    split
    · by_cases he : j = st.top <;> simp [frozenFrame,changePC,changeFrame,debit,finishEpisode,he,hj]
    · split <;> (by_cases he : j = st.top) <;> simp [frozenFrame,changePC,changeFrame,debit,finishEpisode,he,hj]
  | restartDrain =>
    simp only [hpc]
    split
    · by_cases he : j = st.top <;> simp [frozenFrame,changePC,changeFrame,debit,he,hj]
    · split
      · exact hdrain _
      · by_cases he : j = st.top <;> simp [frozenFrame,changeFrame,debit,he,hj]
  | normal => simp only [hpc]; simp [frozenFrame,endCall,debit] <;> split_ifs <;> simp_all [debit,frozenFrame]
  | interrupted => simp only [hpc]; simp [frozenFrame,endCall,debit] <;> split_ifs <;> simp_all [debit,frozenFrame]

lemma frozenFrame_interval (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top) :
    frozenFrame ((recursiveRun m g s α q ℓ schedule b).frames j) =
      frozenFrame ((recursiveRun m g s α q ℓ schedule a).frames j) := by
  have aux : ∀ d, a+d ≤ b → frozenFrame ((recursiveRun m g s α q ℓ schedule (a+d)).frames j) =
      frozenFrame ((recursiveRun m g s α q ℓ schedule a).frames j) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have hstep := frozenFrame_step m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+d))
        j (hopen (a+d) (by omega) (by omega))
      have heq : recursiveRun m g s α q ℓ schedule (a+(d+1)) =
          recursiveStep m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+d)) := by
        rw [show a+(d+1) = (a+d)+1 by omega]
        simp only [recursiveRun,Function.iterate_succ_apply']
      rw [heq,hstep]
      exact ih (by omega)
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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.InformationShape

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 2000000 in
lemma information_step_shape (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) :
    (recursiveStep m g s α ℓ schedule st).information=st.information ∨
      NewCallInformation st (recursiveStep m g s α ℓ schedule st) := by
  cases hpend : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp only [recursiveStep,hpc,hpend] <;> (try split_ifs) <;>
      first
      | left; simp; done
      | right
        refine ⟨⟨st.top+1,(st.frames st.top).block,blockScale schedule ℓ (st.top+1) (st.frames st.top).block⟩,?_,?_,?_,?_,?_,?_,?_⟩ <;>
          simp [freshFrame,changeFrame,debit]
  | some p =>
    obtain ⟨t,v⟩ := p
    have hh := (exterior_lifecycle g α st t v).2.1
    cases hpc : (st.frames st.top).pc <;>
      simp only [recursiveStep,hpc,hpend] <;> (try split_ifs) <;>
      first
      | left; simp [hh]; done
      | right
        refine ⟨⟨st.top+1,(st.frames st.top).block,blockScale schedule ℓ (st.top+1) (st.frames st.top).block⟩,?_,?_,?_,?_,?_,?_,?_⟩ <;>
          simp [freshFrame,changeFrame,debit]

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LevelMassBounds

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_scale_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ((recursiveRun m g s α q ℓ schedule t).frames 0).N=1/q := by
  have hh := frozenFrame_interval m g s α q ℓ schedule 0 t 0 (Nat.zero_le _) (fun _ _ _ => Nat.zero_le _)
  have hN := congrArg (fun f => f.2.1) hh
  simpa [frozenFrame,recursiveRun,recursiveInit,freshFrame] using hN

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BalancedBlocks

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma blockSearch_exact (N : ℝ) (r K fuel candidate : ℕ)
    (hcond : ∀ k : ℕ, (k : ℝ)^(r+2) ≤ N^(r+1) ↔ k ≤ K)
    (hc : candidate ≤ K) (hf : K < candidate+fuel) :
    blockSearch N r fuel candidate = K := by
  induction fuel generalizing candidate with
  | zero => omega
  | succ fuel ih =>
    unfold blockSearch
    by_cases he : candidate+1 ≤ K
    · rw [if_pos ((hcond _).mpr he)]
      exact ih (candidate+1) he (by omega)
    · rw [if_neg (fun h => he ((hcond _).mp h))]
      omega

lemma block_power_condition (N : ℝ) (hN : 1 ≤ N) (r k : ℕ) :
    (k : ℝ)^(r+2) ≤ N^(r+1) ↔
      (k : ℝ) ≤ N^((r+1 : ℝ)/(r+2)) := by
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hden : (r+2 : ℝ) ≠ 0 := by positivity
  have hp : (N^((r+1 : ℝ)/(r+2)))^(r+2 : ℕ) = N^(r+1) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN0]
    have he : ((r+1 : ℝ)/(r+2))*((r+2 : ℕ) : ℝ) = (r+1 : ℕ) := by
      push_cast
      field_simp
    rw [he,Real.rpow_natCast]
  rw [←hp]
  exact pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hN0 _) (by omega)

lemma balanced_block_exact (N : ℝ) (hN : 1 ≤ N) (r : ℕ) :
    blockSearch N r (⌈N⌉₊+1) 0 = ⌊N^((r+1 : ℝ)/(r+2))⌋₊ := by
  let x := N^((r+1 : ℝ)/(r+2))
  have hx0 : 0 ≤ x := Real.rpow_nonneg (le_trans zero_le_one hN) _
  have hxN : x ≤ N := Real.rpow_le_self_of_one_le hN ((div_le_one (by positivity)).mpr (by linarith))
  apply blockSearch_exact N r ⌊x⌋₊ _ 0
  · intro k
    rw [block_power_condition N hN r k]
    exact (Nat.le_floor_iff hx0).symm
  · exact Nat.zero_le _
  · have hf : (⌊x⌋₊ : ℝ) ≤ N := (Nat.floor_le hx0).trans hxN
    have hc : N ≤ (⌈N⌉₊ : ℝ) := Nat.le_ceil N
    have : ⌊x⌋₊ ≤ ⌈N⌉₊ := by exact_mod_cast hf.trans hc
    omega

lemma blockScale_balanced (ℓ j : ℕ) (N : ℝ) (hN : 1 ≤ N) :
    blockScale [] ℓ j N = ⌊N^(((ℓ-j : ℕ)+1 : ℝ)/((ℓ-j : ℕ)+2))⌋₊ := by
  unfold blockScale
  simp only [List.getElem?_nil]
  rw [balanced_block_exact N hN]
  have hx : 1 ≤ N^(((ℓ-j : ℕ)+1 : ℝ)/((ℓ-j : ℕ)+2)) :=
    Real.one_le_rpow hN (by positivity)
  have hf : 1 ≤ ⌊N^(((ℓ-j : ℕ)+1 : ℝ)/((ℓ-j : ℕ)+2))⌋₊ := by
    exact (Nat.le_floor_iff (by positivity)).mpr (by simpa using hx)
  exact max_eq_right hf

lemma floor_half_bounds (x : ℝ) (hx : 1 ≤ x) :
    1 ≤ ⌊x⌋₊ ∧ x/2 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ x := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have h1 : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa using hx)
  have hf := Nat.lt_floor_add_one x
  refine ⟨h1,?_,Nat.floor_le hx0⟩
  by_cases hh : 2 ≤ x
  · linarith
  · have hc : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
    linarith

lemma balanced_block_bounds (ℓ j : ℕ) (N : ℝ) (hN : 1 ≤ N) :
    let x := N^(((ℓ-j : ℕ)+1 : ℝ)/((ℓ-j : ℕ)+2))
    let b := blockScale [] ℓ j N
    1 ≤ b ∧ x/2 ≤ (b : ℝ) ∧ (b : ℝ) ≤ x ∧ (b : ℝ) ≤ N := by
  rw [blockScale_balanced ℓ j N hN]
  have hx : 1 ≤ N^(((ℓ-j : ℕ)+1 : ℝ)/((ℓ-j : ℕ)+2)) := Real.one_le_rpow hN (by positivity)
  obtain ⟨h1,h2,h3⟩ := floor_half_bounds _ hx
  exact ⟨h1,h2,h3,h3.trans (Real.rpow_le_self_of_one_le hN ((div_le_one (by positivity)).mpr (by linarith)))⟩

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BlockLegality

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma blockScale_le_scale (schedule : BlockSchedule) (ℓ j : ℕ) (N : ℝ) (hN : 1 ≤ N) :
    (blockScale schedule ℓ j N : ℝ) ≤ N := by
  cases hs : schedule[j]? with
  | none => simpa [blockScale,hs] using (balanced_block_bounds ℓ j N hN).2.2.2
  | some b =>
    cases b with
    | zero => simpa [blockScale,hs] using (balanced_block_bounds ℓ j N hN).2.2.2
    | succ b =>
      simp only [blockScale,hs]
      rw [Nat.cast_max]
      norm_num only [Nat.cast_one]
      apply max_le hN
      exact (Nat.cast_le.mpr (min_le_right (b+1) ⌊N⌋₊)).trans (Nat.floor_le (by linarith))

lemma scale_bounds_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q ∧ q ≤ 1) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ScaleBounds (1/q) (recursiveRun m g s α q ℓ schedule t) := by
  have hN₀ : 1 ≤ 1/q := (le_div_iff₀ hq.1).mpr (by simpa using hq.2)
  induction t with
  | zero =>
    intro j hj
    have hj0 : j=0 := by change j ≤ 0 at hj; omega
    subst j
    change 1 ≤ 1/q ∧ (blockScale schedule ℓ 0 (1/q) : ℝ) ≤ 1/q ∧ 1/q ≤ 1/q
    exact ⟨hN₀,blockScale_le_scale schedule ℓ 0 (1/q) hN₀,le_rfl⟩
  | succ t ih =>
    let st := recursiveRun m g s α q ℓ schedule t
    let next := recursiveStep m g s α ℓ schedule st
    have hstep : recursiveRun m g s α q ℓ schedule (t+1) = next := by
      simp only [next,st,recursiveRun,Function.iterate_succ_apply']
    rw [hstep]
    intro j hj
    by_cases hle : j ≤ st.top
    · have hh := frozenFrame_step m g s α ℓ schedule st j hle
      have hN : (next.frames j).N = (st.frames j).N := congrArg (fun f => f.2.1) hh
      have hb : (next.frames j).block = (st.frames j).block := congrArg (fun f => f.2.2.1) hh
      rw [hN,hb]
      exact ih j hle
    · have hg : st.top < next.top := by omega
      obtain ⟨hd,hcomp,hpc,he,hl⟩ := growing_step_guards m g s α ℓ schedule st hg
      have hjnew : j=st.top+1 := by
        change j ≤ (recursiveStep m g s α ℓ schedule st).top at hj
        simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hcomp,hpc,he,hl] at hj
        change j ≤ st.top+1 at hj
        omega
      subst j
      have hNN : (next.frames (st.top+1)).N = (st.frames st.top).block := by
        simp [next,recursiveStep,hd,hcomp,hpc,he,hl,freshFrame]
      have hbb : (next.frames (st.top+1)).block = blockScale schedule ℓ (st.top+1) (st.frames st.top).block := by
        simp [next,recursiveStep,hd,hcomp,hpc,he,hl,freshFrame]
      have hB : (1 : ℝ) ≤ (st.frames st.top).block := by
        exact_mod_cast (parameters_run m g s α q hq.1 ℓ schedule t st.top le_rfl).2.1
      rw [hNN,hbb]
      exact ⟨hB,blockScale_le_scale schedule ℓ (st.top+1) _ hB,(ih st.top le_rfl).2.1.trans (ih st.top le_rfl).2.2⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CachedIntervals

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma cached_production_none (g : InputGraph n) (st : RecursiveState n) (id : ℕ)
    (he : cachedSolveEvent g st id) : stepProduction st=none := by
  simp only [stepProduction,he.1,Bool.false_eq_true,ite_false,he.2.1,he.2.2.1,
    he.2.2.2.1,he.2.2.2.2.1,Option.isSome_none]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OpenFramePrefix

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma open_frame_prefix_parameters (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a T j id : ℕ) (info : CallInformation) (ha : a ≤ T)
    (hinfo : (recursiveRun m g s α q ℓ schedule T).information id=some info)
    (hj : j ≤ (recursiveRun m g s α q ℓ schedule a).top)
    (hid : ((recursiveRun m g s α q ℓ schedule a).frames j).id=id) :
    let st := recursiveRun m g s α q ℓ schedule a
    j=info.level ∧ (st.frames j).N=info.scale ∧ (st.frames j).block=info.block := by
  intro st
  have hi := open_frame_information_run m g s α q ℓ schedule a j hj
  rw [hid] at hi
  have hfuture := information_run_persistent m g s α q ℓ schedule a T id
    ⟨j,(st.frames j).N,(st.frames j).block⟩ ha hi
  rw [hinfo] at hfuture
  have heq : info=⟨j,(st.frames j).N,(st.frames j).block⟩ := Option.some.inj hfuture
  subst info
  exact ⟨rfl,rfl,rfl⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.InformationLegality

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma information_legal_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q ∧ q ≤ 1) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ∀ id info, (recursiveRun m g s α q ℓ schedule t).information id=some info →
      info.level ≤ ℓ ∧ 1 ≤ info.scale ∧ 1 ≤ info.block ∧ (info.block : ℝ) ≤ info.scale ∧ info.scale ≤ 1/q := by
  induction t with
  | zero =>
    intro id info hi
    change (if id=0 then some _ else none)=some info at hi
    split_ifs at hi with he
    · have hh := Option.some.inj hi
      subst info
      have hN : 1 ≤ 1/q := (le_div_iff₀ hq.1).mpr (by simpa using hq.2)
      exact ⟨Nat.zero_le _,hN,by
          change 1 ≤ ((recursiveInit g s q ℓ schedule).frames 0).block
          exact (parameters_run m g s α q hq.1 ℓ schedule 0 0 (Nat.zero_le _)).2.1,
        blockScale_le_scale schedule ℓ 0 (1/q) hN,le_rfl⟩
  | succ t ih =>
    intro id info hi
    let st := recursiveRun m g s α q ℓ schedule t
    let next := recursiveRun m g s α q ℓ schedule (t+1)
    have hstep : next=recursiveStep m g s α ℓ schedule st := by
      simp only [next,st,recursiveRun,Function.iterate_succ_apply']
    obtain hh|hh := information_step_shape m g s α ℓ schedule st
    · rw [←hstep] at hh
      exact ih id info (by rwa [hh] at hi)
    · rw [←hstep] at hh
      obtain ⟨newinfo,htop,hnext,hlevel,hid,hscale,hblock,hm⟩ := hh
      by_cases he : id=st.nextId
      · have hinfo : info=newinfo := by
          change next.information id=some info at hi
          rw [hm,he,Function.update_self] at hi
          exact (Option.some.inj hi).symm
        subst info
        rw [hlevel,hscale,hblock]
        have hb := scale_bounds_run m g s α q hq ℓ schedule (t+1) next.top le_rfl
        exact ⟨depth_run m g s α q ℓ schedule (t+1),hb.1,
          (parameters_run m g s α q hq.1 ℓ schedule (t+1) next.top le_rfl).2.1,hb.2.1,hb.2.2⟩
      · apply ih id info
        change next.information id=some info at hi
        rwa [hm,Function.update_of_ne he] at hi

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CallDiscoveryEffort

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma callDiscoveryEffort_nonnegative (g : InputGraph n) (st : RecursiveState n) (id : ℕ) :
    0 ≤ callDiscoveryEffort g st id := by
  cases hp : stepProduction st with
  | none => simp [callDiscoveryEffort,hp]
  | some p => obtain ⟨j,v⟩ := p; simp only [callDiscoveryEffort,hp]; split <;> (try unfold LocalPush.deg) <;> positivity

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.KeyCostBound

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma active_card_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hnum : NumericalInvariant g st) (hstore : StoredInvariant g st) (hq : 0 < (st.frames 0).q)
    (j : ℕ) (hj : j ≤ st.top) : ((st.frames j).active.card : ℝ) ≤ 1/(st.frames 0).q := by
  have hc : (st.frames j).active.card ≤ volumeNat g (st.frames 0).active :=
    (Finset.card_le_card (active_subset_root st hreg j hj)).trans
      (card_le_volume g (st.frames 0).active (fun v hv => hstore.2 v (hstore.1 0 (Nat.zero_le _) hv)))
  have hc' : ((st.frames j).active.card : ℝ) ≤ (volumeNat g (st.frames 0).active : ℝ) := by exact_mod_cast hc
  have hv := root_volume_bound g s α hα st hroot hnum
  apply hc'.trans
  apply (le_div_iff₀ hq).mpr
  nlinarith

lemma exterior_card_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hnum : NumericalInvariant g st) (hstore : StoredInvariant g st) (hkeys : KeysInvariant g st)
    (hiso : IsolateResidual g st) (hq : 0 < (st.frames 0).q)
    (j : ℕ) (hj : j ≤ st.top) : ((st.frames j).exterior.card : ℝ) ≤ 1/(st.frames 0).q := by
  by_cases hz : j = 0
  · subst j
    have hc := card_le_volume g (st.frames 0).exterior (fun v hv => root_exterior_positive g st hkeys hiso v hv)
    have hc' : ((st.frames 0).exterior.card : ℝ) ≤ (volumeNat g (st.frames 0).exterior : ℝ) := by exact_mod_cast hc
    exact hc'.trans (root_exterior_mass_bound g s α hα st hroot hnum hkeys hq)
  · have hp : parentDomain st j ⊆ (st.frames 0).active :=
      parent_domain_nested st hreg 0 j (Nat.pos_of_ne_zero hz) hj
    have hc := Finset.card_le_card (((hreg j hj).2.1.trans Finset.sdiff_subset).trans hp)
    have hc' : ((st.frames j).exterior.card : ℝ) ≤ ((st.frames 0).active.card : ℝ) := by exact_mod_cast hc
    exact hc'.trans (active_card_bound g s α hα st hreg hroot hnum hstore hq 0 (Nat.zero_le _))

lemma keyCost_log_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hnum : NumericalInvariant g st) (hstore : StoredInvariant g st) (hkeys : KeysInvariant g st)
    (hiso : IsolateResidual g st) (hq : 0 < (st.frames 0).q)
    (hvol : (volumeNat g st.stored : ℝ) ≤ 3/(st.frames 0).q) :
    (keyCost st : ℝ) ≤ 1+Real.logb 2 (2+(3+2*(st.top+1 : ℕ))/(st.frames 0).q) := by
  classical
  let L := 2+st.stored.card+∑ i ∈ Finset.range (st.top+1), ((st.frames i).exterior.card+(st.frames i).active.card)
  have hS : (st.stored.card : ℝ) ≤ 3/(st.frames 0).q := by
    have hh := card_le_volume g st.stored hstore.2
    exact (show (st.stored.card : ℝ) ≤ (volumeNat g st.stored : ℝ) by exact_mod_cast hh).trans hvol
  have hsum : ((∑ i ∈ Finset.range (st.top+1), ((st.frames i).exterior.card+(st.frames i).active.card) : ℕ) : ℝ) ≤
      (st.top+1 : ℕ)*(2/(st.frames 0).q) := by
    push_cast
    calc
      _ ≤ ∑ i ∈ Finset.range (st.top+1), (2/(st.frames 0).q) := by
        apply Finset.sum_le_sum
        intro i hi
        have his : i ≤ st.top := by have := Finset.mem_range.mp hi; omega
        have ha := active_card_bound g s α hα st hreg hroot hnum hstore hq i his
        have he := exterior_card_bound g s α hα st hreg hroot hnum hstore hkeys hiso hq i his
        calc
          _ ≤ 1/(st.frames 0).q+1/(st.frames 0).q := add_le_add he ha
          _ = _ := by ring
      _ = _ := by simp
  have hL : (L : ℝ) ≤ 2+(3+2*(st.top+1 : ℕ))/(st.frames 0).q := by
    calc
      (L : ℝ) = 2+(st.stored.card : ℝ)+
          ((∑ i ∈ Finset.range (st.top+1), ((st.frames i).exterior.card+(st.frames i).active.card) : ℕ) : ℝ) := by
        simp only [L,Nat.cast_add,Nat.cast_ofNat]
      _ ≤ 2+3/(st.frames 0).q+(st.top+1 : ℕ)*(2/(st.frames 0).q) :=
        add_le_add (add_le_add (le_refl (2 : ℝ)) hS) hsum
      _ = _ := by push_cast; ring
  have hLp : (0 : ℝ) < (L : ℝ) := by
    have hh : 2 ≤ L := by dsimp [L]; omega
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hh)
  have hlog := (Real.log2_le_logb L).trans (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hLp hL)
  change ((1+Nat.log2 L : ℕ) : ℝ) ≤ _
  push_cast
  simpa only [Nat.cast_add,Nat.cast_one] using add_le_add (le_refl (1 : ℝ)) hlog

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LogOverhead

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma queue_log_overhead_bound (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ t : ℕ) (ht : t ≤ ℓ) :
    1+Real.logb 2 (2+(3+2*(t+1 : ℕ))/rootThreshold ε ℓ) ≤
      (1+(Real.log 128+4)/Real.log 2)*(2+Real.log (2/ε)+(ℓ : ℝ)) := by
  have he0 : 0 < ε := hε.1
  have hel0 : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
  let A : ℝ := ℓ+3
  let L := Real.log (2/ε)
  let B : ℝ := 2+L+ℓ
  let D := Real.log 128+4
  let z : ℝ := 2+(3+2*(t+1 : ℕ))/rootThreshold ε ℓ
  have hA : 0 < A := by dsimp [A]; positivity
  have hA3 : 3 ≤ A := by dsimp [A]; linarith
  have hqr : rootThreshold ε ℓ = ε/(32*A) := by simp [rootThreshold,kappa,A]
  have hq : 0 < rootThreshold ε ℓ := by rw [hqr]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have htc : (t : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast ht
  have hP : (3+2*(t+1 : ℕ) : ℝ) ≤ 2*A := by dsimp [A]; push_cast; linarith
  have hze : z*ε = 2*ε+(3+2*(t+1 : ℕ))*32*A := by
    dsimp only [z]
    rw [hqr]
    field_simp [he0.ne',hA.ne'] <;> push_cast <;> ring
  have hupper : z ≤ 128*A^2/ε := by
    apply (le_div_iff₀ hε.1).mpr
    rw [hze]
    have hm := mul_le_mul_of_nonneg_right hP (show 0 ≤ 32*A by positivity)
    nlinarith [hε.2]
  have hlog : Real.log z ≤ Real.log 128+2*Real.log A-Real.log ε := by
    have hh := Real.log_le_log hz hupper
    have hnum : (128 : ℝ)*A^2 ≠ 0 := by positivity
    rw [Real.log_div hnum hε.1.ne',Real.log_mul (by norm_num : (128 : ℝ) ≠ 0) (pow_ne_zero 2 hA.ne'),Real.log_pow] at hh
    norm_num at hh
    exact hh
  have hL : 0 ≤ L := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hε.1).mpr
    linarith [hε.2]
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog128 : 0 ≤ Real.log (128 : ℝ) := Real.log_nonneg (by norm_num)
  have hLA : Real.log A ≤ (ℓ : ℝ)+2 := by
    have hh := Real.log_le_sub_one_of_pos hA
    dsimp [A] at hh
    linarith
  have hεL : -Real.log ε ≤ L := by
    dsimp only [L]
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hε.1.ne']
    linarith
  have hD : 2 ≤ D := by dsimp [D]; linarith
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hlogB : Real.log z ≤ D*B := by
    have hel : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    have hm1 := mul_le_mul_of_nonneg_right hD hel
    have hm2 := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ D by linarith) hL
    dsimp [D,B]
    dsimp [D] at hm1 hm2
    nlinarith [hlog,hLA,hεL]
  change 1+Real.logb 2 z ≤ (1+D/Real.log 2)*B
  rw [Real.logb]
  calc
    _ ≤ B+(D*B)/Real.log 2 := add_le_add hB (div_le_div_of_nonneg_right hlogB hlog2.le)
    _ = _ := by ring

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RunKeyCost

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
variable {n : ℕ}

lemma run_keyCost_linear (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    (keyCost (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t) : ℝ) ≤
      (1+(Real.log 128+4)/Real.log 2)*(2+Real.log (2/ε)+(ℓ : ℝ)) := by
  let q := rootThreshold ε ℓ
  let st := recursiveRun m g s α q ℓ schedule t
  have he : 0 < ε := hε.1
  have hq : 0 < q := by dsimp [q,rootThreshold,kappa]; positivity
  have hqr : (st.frames 0).q = q := root_threshold_run m g s α q ℓ schedule t
  have hvol : (volumeNat g st.stored : ℝ) ≤ 3/(st.frames 0).q := by
    rw [hqr]
    exact run_stored_volume_bound m g s α q hα hq hs ℓ schedule t
  have hK := keyCost_log_bound g s α hα.1.le st (region_run m g s α q ℓ schedule t)
    (root_identity_run m g s α q ℓ schedule t) (numerical_run m g s α q hα hq hs ℓ schedule t)
    (stored_run m g s α q hq.le hs ℓ schedule t) (keys_run m g s α q hq.le ℓ schedule t)
    (isolate_run m g s α q hs ℓ schedule t) (by rw [hqr]; exact hq) hvol
  rw [hqr] at hK
  exact hK.trans (queue_log_overhead_bound ε hε ℓ st.top (depth_run m g s α q ℓ schedule t))

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolverLogBound

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma queueLogConstant_positive : 0 < queueLogConstant := by
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h128 : 0 ≤ Real.log (128 : ℝ) := Real.log_nonneg (by norm_num)
  unfold queueLogConstant
  positivity

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OverheadMonotone

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma overhead_base_one (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ : ℕ) :
    1 ≤ 2+Real.log (2/ε)+(ℓ : ℝ) := by
  have hL := Real.log_nonneg ((le_div_iff₀ hε.1).mpr (by linarith [hε.2]) : 1 ≤ 2/ε)
  have hl : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
  linarith

lemma overhead_mono (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ a b : ℕ) (C D : ℝ)
    (hC : 0 ≤ C) (hCD : C ≤ D) (hab : a ≤ b) : overhead C a ε ℓ ≤ overhead D b ε ℓ := by
  have hX := overhead_base_one ε hε ℓ
  unfold overhead
  calc
    _ ≤ C*(2+Real.log (2/ε)+(ℓ : ℝ))^b := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX hab) hC
    _ ≤ _ := mul_le_mul_of_nonneg_right hCD (by positivity)

lemma overhead_one (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ c : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    1 ≤ overhead C c ε ℓ := by
  have hX := one_le_pow₀ (overhead_base_one ε hε ℓ) (n:=c)
  unfold overhead
  exact one_le_mul_of_one_le_of_one_le hC hX

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.UniformFullCount

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma root_threshold_unit (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ : ℕ) :
    0 < rootThreshold ε ℓ ∧ rootThreshold ε ℓ ≤ 1 := by
  have he : 0 < ε := hε.1
  have hk : (3 : ℝ) ≤ (kappa ℓ 0 : ℝ) := by
    exact_mod_cast (show 3 ≤ kappa ℓ 0 by simp only [kappa,Nat.sub_zero]; omega)
  unfold rootThreshold
  refine ⟨by positivity,?_⟩
  apply (div_le_one (by positivity : 0 < 32*(kappa ℓ 0 : ℝ))).mpr
  linarith [hε.2]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DiscoveryCharge

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 1500000 in
lemma discovery_charge_step_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ) :
    let st := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t
    callDiscoveryCharge g α st id ≤ ENNReal.ofReal
      (overhead (32*queueLogConstant) 2 ε ℓ*callDiscoveryEffort g st id) := by
  intro st
  let X := 2+Real.log (2/ε)+(ℓ : ℝ)
  cases hp : stepProduction st with
  | none => simp [callDiscoveryCharge,callDiscoveryEffort,hp]
  | some p =>
    obtain ⟨j,v⟩ := p
    by_cases hid : (st.frames j).id=id
    · have hnext : recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule (t+1)=exteriorPush g α st j v := by
        rw [show recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule (t+1)=recursiveStep m g s α ℓ schedule st by
          simp only [st,recursiveRun,Function.iterate_succ_apply']]
        exact production_push m g s α ℓ schedule st j v hp
      have hkey : (keyCost (exteriorPush g α st j v) : ℝ) ≤ queueLogConstant*X := by
        rw [←hnext]
        exact run_keyCost_linear m g s α ε hα hε hs ℓ schedule (t+1)
      have hL : 0 ≤ Real.log (2/ε) := Real.log_nonneg ((le_div_iff₀ hε.1).mpr (by linarith [hε.2]))
      have htop : ((st.top+1 : ℕ) : ℝ) ≤ X := by
        have hh : (st.top : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast depth_run m g s α (rootThreshold ε ℓ) ℓ schedule t
        dsimp only [X]
        push_cast
        linarith
      have hX0 : 0 ≤ X := (zero_le_one.trans (overhead_base_one ε hε ℓ))
      have hd0 : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
      simp only [Nat.cast_add,Nat.cast_one] at htop
      simp only [callDiscoveryCharge,callDiscoveryEffort,hp,hid,ite_true]
      rw [←ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      push_cast
      have hd : (((g.neighbors v).length : ℕ) : ℝ)+1=LocalPush.deg g.graph v+1 := by rw [neighbor_degree]; rfl
      rw [hd]
      calc
        _ ≤ 32*X*(LocalPush.deg g.graph v+1)*(queueLogConstant*X) := by gcongr <;> first | assumption | positivity
        _ = _ := by dsimp only [overhead,X]; ring
    · simp [callDiscoveryCharge,callDiscoveryEffort,hp,hid]

lemma discovery_charge_prefix_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) (info : CallInformation)
    (hinfo : (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule T).information id=some info) :
    (∑ k ∈ Finset.range T, callDiscoveryCharge g α
      (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule k) id) ≤
        ENNReal.ofReal (overhead (480*queueLogConstant) 2 ε ℓ*info.scale) := by
  let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
  let P := overhead (32*queueLogConstant) 2 ε ℓ
  have hQ := queueLogConstant_positive
  have hP : 0 ≤ P := by dsimp only [P,overhead]; positivity
  have hnon (k : ℕ) : 0 ≤ P*callDiscoveryEffort g (run k) id :=
    mul_nonneg hP (callDiscoveryEffort_nonnegative g (run k) id)
  have heff := call_discovery_effort_bound m g s α (rootThreshold ε ℓ) hα (root_threshold_unit ε hε ℓ) hs
    ℓ schedule T id info hinfo
  calc
    _ ≤ ∑ k ∈ Finset.range T, ENNReal.ofReal (P*callDiscoveryEffort g (run k) id) :=
      Finset.sum_le_sum (fun k _ => discovery_charge_step_bound m g s α ε hα hε hs ℓ schedule k id)
    _ = ENNReal.ofReal (∑ k ∈ Finset.range T, P*callDiscoveryEffort g (run k) id) :=
      (ENNReal.ofReal_sum_of_nonneg (fun k _ => hnon k)).symm
    _ = ENNReal.ofReal (P*(∑ k ∈ Finset.range T, callDiscoveryEffort g (run k) id)) := by rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (P*(15*info.scale)) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left heff hP)
    _ = _ := by congr 1; dsimp only [P,overhead]; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OwnChargeEvents

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma own_charge_events (m : SolveModel) (g : InputGraph n) (α : ℝ) (ℓ : ℕ)
    (st : RecursiveState n) (id : ℕ) :
    ownStepCharge m g α ℓ st id=callDiscoveryCharge g α st id+
      (if cachedSolveEvent g st id then (stepDebit m g α ℓ st).2 else 0)+
      (if controlEvent g st id then (stepDebit m g α ℓ st).2 else 0) := by
  by_cases hd : st.done=true
  · simp [ownStepCharge,stepDebit,callDiscoveryCharge,stepProduction,controlEvent,cachedSolveEvent,hd]
  have hdf : st.done=false := Bool.eq_false_of_not_eq_true hd
  cases hp : stepProduction st with
  | some p =>
    obtain ⟨j,v⟩ := p
    have hdebit := production_debit m g α ℓ st j v hp
    have hc : ¬cachedSolveEvent g st id := by
      intro hh
      have hh' := cached_production_none g st id hh
      rw [hp] at hh'
      cases hh'
    simp [ownStepCharge,hdebit,callDiscoveryCharge,hp,hc,controlEvent]
  | none =>
    have hproducer := nonproducing_debit_producer m g α ℓ st hdf hp
    by_cases hc : cachedSolveEvent g st id
    · have he := cached_debit m g α ℓ st id hc
      have hid : (st.frames st.top).id=id := hc.2.2.2.2.2.2.2
      simp [ownStepCharge,he,hid,callDiscoveryCharge,hp,hc,controlEvent]
    · simp only [ownStepCharge,callDiscoveryCharge,hp,hc,ite_false,add_zero,zero_add,controlEvent,hdf,
        Bool.false_eq_true,hproducer,not_false_eq_true,true_and]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControlDebitCases

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 2000000 in
lemma nonproducing_control_debit (m : SolveModel) (g : InputGraph n) (α : ℝ) (ℓ : ℕ)
    (st : RecursiveState n) (B : ℝ≥0∞) (hd : st.done=false) (hcomp : ¬componentComplete st)
    (hp : stepProduction st=none) (hc : ¬cachedSolveEvent g st (st.frames st.top).id)
    (hcheap : 1 ≤ B)
    (hbegin : (st.frames st.top).pc=.beginEpisode →
      (16*(volumeNat g (st.frames st.top).active+1)*keyCost st : ℕ) ≤ B)
    (hfull : ¬anyExhausted st → jointCost m g st (st.frames st.top).active ≤ B)
    (hnew : ¬anyExhausted st →
      (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
        8*(ℓ+2)*((st.frames st.top).block+2) : ℕ) ≤ B)
    (hfinish : ¬ancestorExhausted st →
      (16*(volumeNat g (st.frames st.top).active+1) : ℕ) ≤ B)
    (hend : st.top=0 → (1 : ℝ≥0∞)+(8*(st.frames 0).active.card+1 : ℕ) ≤ B) :
    (stepDebit m g α ℓ st).2 ≤ B := by
  cases hpend : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp only [stepDebit,hd,Bool.false_eq_true,ite_false,hcomp,hpc,hpend] <;>
      (try split_ifs) <;>
      first
      | assumption
      | exact hcheap
      | exact hbegin hpc
      | apply hfull; assumption
      | apply hnew; assumption
      | apply hfinish; assumption
      | apply hend; assumption
      | (simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hend (by assumption))
      | (have hz : st.top=0 := by assumption
         convert hend hz using 1 <;> simp [hz,Nat.cast_add,Nat.cast_mul] <;> ring)
      | (exfalso; apply hc; simp_all [cachedSolveEvent])
  | some p =>
    obtain ⟨j,v⟩ := p
    cases hpc : (st.frames st.top).pc <;>
      simp only [stepDebit,hd,Bool.false_eq_true,ite_false,hcomp,hpc,hpend] <;>
      (try split_ifs) <;>
      first
      | assumption
      | exact hcheap
      | exact hbegin hpc
      | apply hfull; assumption
      | apply hnew; assumption
      | apply hfinish; assumption
      | apply hend; assumption
      | (simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hend (by assumption))
      | (have hz : st.top=0 := by assumption
         convert hend hz using 1 <;> simp [hz,Nat.cast_add,Nat.cast_mul] <;> ring)
      | (exfalso; simp_all [stepProduction,drainProduction])

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControlVolumes

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma current_volume_unexhausted_ancestors (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ)
    (hn : ¬ancestorExhausted (recursiveRun m g s α q ℓ schedule t)) :
    let st := recursiveRun m g s α q ℓ schedule t
    (volumeNat g (st.frames st.top).active : ℝ) ≤ 2*(st.frames st.top).N := by
  intro st
  cases ht : st.top with
  | zero =>
    have hv : (volumeNat g (st.frames 0).active : ℝ) ≤ 1/q :=
      (run_root_volume_bound m g s α q hα hq hs ℓ schedule t).1
    have hN : (st.frames 0).N=1/q := root_scale_run m g s α q ℓ schedule t
    rw [hN]
    linarith [show 0 < 1/q by positivity]
  | succ j =>
    have hj : j < st.top := by omega
    have hx : ¬exhausted st j := fun hh => hn ⟨j,hj,hh⟩
    have hv := run_child_volume_unexhausted m g s α q hα hq hs ℓ schedule t j hj hx
    simpa only [ht] using hv.le

lemma active_card_le_volume (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t j : ℕ)
    (hj : j ≤ (recursiveRun m g s α q ℓ schedule t).top) :
    let st := recursiveRun m g s α q ℓ schedule t
    (st.frames j).active.card ≤ volumeNat g (st.frames j).active := by
  intro st
  have hstored := stored_run m g s α q hq hs ℓ schedule t
  rw [Finset.card_eq_sum_ones,volumeNat]
  apply Finset.sum_le_sum
  intro v hv
  rw [neighbor_degree]
  exact hstored.2 v (hstored.1 j hj hv)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControlChargeArithmetic

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma control_scan_costs (N X Q P V key b L card : ℝ)
    (hN : 1 ≤ N) (hX : 1 ≤ X) (hQ : 0 ≤ Q) (hP : 100*(Q+1)*X ≤ P)
    (hV : 0 ≤ V ∧ V ≤ 2*N) (hkey : 0 ≤ key ∧ key ≤ Q*X)
    (hb : 0 ≤ b ∧ b ≤ N) (hL : 0 ≤ L ∧ L ≤ X) (hc : 0 ≤ card ∧ card ≤ 2*N) :
    16*(V+1)*key+8*L*(b+2) ≤ P*N ∧ 16*(V+1) ≤ P*N ∧ 8*card+2 ≤ P*N := by
  have hVN : V+1 ≤ 3*N := by linarith
  have hbN : b+2 ≤ 3*N := by linarith
  have hscan : 16*(V+1)*key ≤ 48*N*(Q*X) := by
    calc
      _ ≤ 16*(3*N)*(Q*X) := by gcongr <;> linarith
      _ = _ := by ring
  have hprep : 8*L*(b+2) ≤ 24*X*N := by
    calc
      _ ≤ 8*X*(3*N) := by gcongr <;> linarith
      _ = _ := by ring
  have hPN : 100*(Q+1)*X*N ≤ P*N := mul_le_mul_of_nonneg_right hP (by linarith)
  have hQN : 0 ≤ Q*X*N := by positivity
  have hXN : N ≤ X*N := by nlinarith
  refine ⟨?_,?_,?_⟩ <;> nlinarith

lemma control_joint_cost (N J P V : ℝ) (hN : 1 ≤ N) (hJ : 0 ≤ J) (hP : 3*J+3 ≤ P)
    (hV : V ≤ 2*N) : J*(V+1) ≤ P*N := by
  have hV' : V+1 ≤ 3*N := by linarith
  have hh := mul_le_mul_of_nonneg_left hV' hJ
  have hp := mul_le_mul_of_nonneg_right hP (by linarith : 0 ≤ N)
  nlinarith

lemma completion_joint_cost (N J P V card : ℝ) (hN : 1 ≤ N) (hJ : 0 ≤ J)
    (hP : 3*J+3 ≤ P) (hV : V ≤ N) (hc : card ≤ V) :
    J*(V+1)+card+1 ≤ P*N := by
  have hV' : V+1 ≤ 2*N := by linarith
  have hh := mul_le_mul_of_nonneg_left hV' hJ
  have hp := mul_le_mul_of_nonneg_right hP (by linarith : 0 ≤ N)
  nlinarith

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControlPrice

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma control_price_majorants (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ cp : ℕ) (Cp : ℝ)
    (hCp : 0 < Cp) :
    let C := 100*(queueLogConstant+1)+3*Cp+3
    let P := overhead C (cp+1) ε ℓ
    0 < C ∧ 1 ≤ P ∧
      100*(queueLogConstant+1)*(2+Real.log (2/ε)+(ℓ : ℝ)) ≤ P ∧
      3*overhead Cp cp ε ℓ+3 ≤ P := by
  intro C P
  have hQ := queueLogConstant_positive
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hX := overhead_base_one ε hε ℓ
  have hmono := overhead_mono ε hε ℓ 1 (cp+1) (100*(queueLogConstant+1)) C
    (by positivity) (by dsimp only [C]; linarith) (by omega)
  have hmonoJ := overhead_mono ε hε ℓ cp (cp+1) (3*Cp+3) C
    (by positivity) (by dsimp only [C]; linarith) (by omega)
  refine ⟨by linarith,overhead_one ε hε ℓ (cp+1) C hC,?_,?_⟩
  · simpa only [P,overhead,pow_one] using hmono
  · apply le_trans _ hmonoJ
    have hp := one_le_pow₀ hX (n:=cp)
    dsimp only [overhead]
    nlinarith

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControlCharge

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 2000000 in
lemma uniform_control_charge (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ),
        (0 < α ∧ α < 1) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
        let st := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t
        controlEvent g st id →
        (stepDebit m g α ℓ st).2 ≤ ENNReal.ofReal
          (overhead C c ε ℓ*(st.frames (if componentComplete st then 0 else st.top)).N) := by
  obtain ⟨Cp,cp,hCp,hcp,hJoint⟩ := uniform_jointCost_overhead m
  let C := 100*(queueLogConstant+1)+3*Cp+3
  let c := cp+1
  have hQueue := queueLogConstant_positive
  refine ⟨C,c,by dsimp only [C]; positivity,by dsimp only [c]; omega,?_⟩
  intro n g s α ε ℓ schedule t id hα hε hs st he
  let X := 2+Real.log (2/ε)+(ℓ : ℝ)
  let P := overhead C c ε ℓ
  let J := overhead Cp cp ε ℓ
  have hprice := control_price_majorants ε hε ℓ cp Cp hCp
  have hP : 1 ≤ P := hprice.2.1
  have hPX : 100*(queueLogConstant+1)*X ≤ P := hprice.2.2.1
  have hPJ : 3*J+3 ≤ P := hprice.2.2.2
  have hX : 1 ≤ X := overhead_base_one ε hε ℓ
  have hQ := queueLogConstant_positive
  have hJ : 0 ≤ J := by dsimp only [J,overhead]; positivity
  have hq := root_threshold_unit ε hε ℓ
  have hscale := scale_bounds_run m g s α (rootThreshold ε ℓ) hq ℓ schedule t
  have hregion : RegionInvariant st := region_run m g s α (rootThreshold ε ℓ) ℓ schedule t
  have hkey : (keyCost st : ℝ) ≤ queueLogConstant*X := run_keyCost_linear m g s α ε hα hε hs ℓ schedule t
  have hL : ((ℓ+2 : ℕ) : ℝ) ≤ X := by
    have hh := Real.log_nonneg ((le_div_iff₀ hε.1).mpr (by linarith [hε.2]) : 1 ≤ 2/ε)
    dsimp only [X]
    push_cast
    linarith
  have hcard (j : ℕ) (hj : j ≤ st.top) : ((st.frames j).active.card : ℝ) ≤ (volumeNat g (st.frames j).active : ℝ) := by
    exact_mod_cast active_card_le_volume m g s α (rootThreshold ε ℓ) hq.1.le hs ℓ schedule t j hj
  have hcost (T : Finset (Fin n)) (hT : T ⊆ (st.frames 0).active) :
      jointCost m g st T ≤ ENNReal.ofReal (J*((volumeNat g T : ℝ)+1)) :=
    hJoint n g s α ε ℓ schedule t hα hε hs T hT
  obtain ⟨hd,hprod,hcache,hid⟩ := he
  by_cases hcomp : componentComplete st
  · simp only [if_pos hcomp]
    have hN : 1 ≤ (st.frames 0).N := (hscale 0 (Nat.zero_le _)).1
    have hv : (volumeNat g (st.frames 0).active : ℝ) ≤ (st.frames 0).N := by
      rw [show (st.frames 0).N=1/rootThreshold ε ℓ from root_scale_run m g s α (rootThreshold ε ℓ) ℓ schedule t]
      exact (run_root_volume_bound m g s α (rootThreshold ε ℓ) hα hq.1 hs ℓ schedule t).1
    have harith := completion_joint_cost (st.frames 0).N J P (volumeNat g (st.frames 0).active)
      (st.frames 0).active.card hN hJ hPJ hv (hcard 0 (Nat.zero_le _))
    simp only [stepDebit,hd,Bool.false_eq_true,ite_false,hcomp,ite_true]
    have hjoint := hcost (st.frames 0).active (subset_refl _)
    calc
      _ ≤ ENNReal.ofReal (J*((volumeNat g (st.frames 0).active : ℝ)+1))+
          (((st.frames 0).active.card+1 : ℕ) : ℝ≥0∞) := add_le_add hjoint le_rfl
      _ = ENNReal.ofReal (J*((volumeNat g (st.frames 0).active : ℝ)+1)+(st.frames 0).active.card+1) := by
        rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_add (by positivity : 0 ≤ J*((volumeNat g (st.frames 0).active : ℝ)+1)) (by positivity)]
        congr 1
        push_cast
        ring
      _ ≤ ENNReal.ofReal (P*(st.frames 0).N) := ENNReal.ofReal_le_ofReal harith
  · simp only [if_neg hcomp]
    have hidcur : (st.frames st.top).id=id := by simpa only [if_neg hcomp] using hid
    have hc : ¬cachedSolveEvent g st (st.frames st.top).id := by rwa [hidcur]
    have hN : 1 ≤ (st.frames st.top).N := (hscale st.top le_rfl).1
    have hb : ((st.frames st.top).block : ℝ) ≤ (st.frames st.top).N := (hscale st.top le_rfl).2.1
    have hvol (ha : ¬ancestorExhausted st) : (volumeNat g (st.frames st.top).active : ℝ) ≤ 2*(st.frames st.top).N :=
      current_volume_unexhausted_ancestors m g s α (rootThreshold ε ℓ) hα hq.1 hs ℓ schedule t ha
    have hscans (ha : ¬ancestorExhausted st) := control_scan_costs (st.frames st.top).N X queueLogConstant P
      (volumeNat g (st.frames st.top).active) (keyCost st) (st.frames st.top).block (ℓ+2) (st.frames st.top).active.card
      hN hX hQ.le hPX ⟨by positivity,hvol ha⟩ ⟨by positivity,hkey⟩ ⟨by positivity,hb⟩
      ⟨by positivity,by exact_mod_cast hL⟩ ⟨Nat.cast_nonneg _,(hcard st.top le_rfl).trans (hvol ha)⟩
    apply nonproducing_control_debit m g α ℓ st (ENNReal.ofReal (P*(st.frames st.top).N)) hd hcomp hprod hc
    · rw [←ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (one_le_mul_of_one_le_of_one_le hP hN)
    · intro hbegin
      have ha := begin_episode_run_unexhausted m g s α (rootThreshold ε ℓ) ℓ schedule t hd hbegin
      rw [←ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      push_cast
      have hh := (hscans ha).1
      have hp0 : 0 ≤ 8*((ℓ+2 : ℕ) : ℝ)*((st.frames st.top).block+2) := by positivity
      push_cast at hh hp0
      linarith
    · intro hno
      have ha : ¬ancestorExhausted st := fun ⟨i,hi,hx⟩ => hno ⟨i,hi.le,hx⟩
      exact (hcost _ (active_subset_root st hregion st.top le_rfl)).trans
        (ENNReal.ofReal_le_ofReal (control_joint_cost _ J P _ hN hJ hPJ (hvol ha)))
    · intro hno
      have ha : ¬ancestorExhausted st := fun ⟨i,hi,hx⟩ => hno ⟨i,hi.le,hx⟩
      rw [←ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      push_cast
      simpa only [Nat.cast_add,Nat.cast_ofNat] using (hscans ha).1
    · intro ha
      rw [←ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      push_cast
      exact (hscans ha).2.1
    · intro ht
      have ha : ¬ancestorExhausted st := by rintro ⟨i,hi,_⟩; omega
      have hh := (hscans ha).2.2
      rw [ht] at hh ⊢
      rw [←ENNReal.ofReal_one,←ENNReal.ofReal_natCast,←ENNReal.ofReal_add (by norm_num) (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      push_cast
      linarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControlPrefixCount

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma controlEvent_producer_le (g : InputGraph n) (st : RecursiveState n) :
    (if componentComplete st then 0 else st.top) ≤ st.top := by split <;> omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CachedCharge

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma uniform_cached_charge (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ),
        (0 < α ∧ α < 1) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
        let st := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t
        cachedSolveEvent g st id →
        jointCost m g st ((st.frames st.top).cache ∪ (st.frames st.top).high) ≤
          ENNReal.ofReal (overhead C c ε ℓ*(st.frames st.top).block) := by
  obtain ⟨Cp,cp,hCp,hcp,hCost⟩ := uniform_jointCost_overhead m
  refine ⟨3*Cp,cp,by positivity,hcp,?_⟩
  intro n g s α ε ℓ schedule t id hα hε hs st he
  have hq := root_threshold_unit ε hε ℓ
  have hreg : RegionInvariant st := region_run m g s α (rootThreshold ε ℓ) ℓ schedule t
  have hT : (st.frames st.top).cache ∪ (st.frames st.top).high ⊆ (st.frames 0).active :=
    (Finset.union_subset_iff.mpr ⟨(hreg st.top le_rfl).2.2.2,(hreg st.top le_rfl).2.2.1⟩).trans
      (active_subset_root st hreg st.top le_rfl)
  have hx : ¬exhausted st st.top := fun hh => he.2.2.2.1 ⟨st.top,le_rfl,hh⟩
  have hvol := run_cache_volume_unexhausted m g s α (rootThreshold ε ℓ) hα hq.1 hs ℓ schedule t he.2.2.1 hx
  have hb : 1 ≤ ((st.frames st.top).block : ℝ) := by
    exact_mod_cast (parameters_run m g s α (rootThreshold ε ℓ) hq.1 ℓ schedule t st.top le_rfl).2.1
  have hh := hCost n g s α ε ℓ schedule t hα hε hs _ hT
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hC : 0 ≤ overhead Cp cp ε ℓ := by unfold overhead; exact mul_nonneg hCp.le (pow_nonneg (by linarith [overhead_base_one ε hε ℓ]) _)
  have hv : (volumeNat g ((st.frames st.top).cache ∪ (st.frames st.top).high) : ℝ)+1 ≤ 3*(st.frames st.top).block := by linarith
  have hm := mul_le_mul_of_nonneg_left hv hC
  dsimp only [overhead] at hm ⊢
  nlinarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OwnChargeStep

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma uniform_own_charge_step (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule)
        (k T id : ℕ) (info : CallInformation),
        (0 < α ∧ α < 1) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s → k ≤ T →
        let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
        (run T).information id=some info →
        ownStepCharge m g α ℓ (run k) id ≤ callDiscoveryCharge g α (run k) id+
          (if controlEvent g (run k) id then ENNReal.ofReal (overhead C c ε ℓ*info.scale) else 0)+
          (if cachedSolveEvent g (run k) id then ENNReal.ofReal (overhead C c ε ℓ*info.block) else 0) := by
  obtain ⟨Cc,cc,hCc,hcc,hControl⟩ := uniform_control_charge m
  obtain ⟨Cs,cs,hCs,hcs,hCache⟩ := uniform_cached_charge m
  refine ⟨Cc+Cs,max cc cs,by positivity,lt_of_lt_of_le hcc (le_max_left _ _),?_⟩
  intro n g s α ε ℓ schedule k T id info hα hε hs hkT run hi
  have hq := root_threshold_unit ε hε ℓ
  have hlegal := information_legal_run m g s α (rootThreshold ε ℓ) hq ℓ schedule T id info hi
  have hN : 0 ≤ info.scale := by linarith [hlegal.2.1]
  have hmonoC := overhead_mono ε hε ℓ cc (max cc cs) Cc (Cc+Cs) hCc.le (by linarith) (le_max_left _ _)
  have hmonoS := overhead_mono ε hε ℓ cs (max cc cs) Cs (Cc+Cs) hCs.le (by linarith) (le_max_right _ _)
  have hc : (if controlEvent g (run k) id then (stepDebit m g α ℓ (run k)).2 else 0) ≤
      if controlEvent g (run k) id then ENNReal.ofReal (overhead (Cc+Cs) (max cc cs) ε ℓ*info.scale) else 0 := by
    split_ifs with he
    · have hj := controlEvent_producer_le g (run k)
      have hid := he.2.2.2
      have hp := open_frame_prefix_parameters m g s α (rootThreshold ε ℓ) ℓ schedule k T
        (if componentComplete (run k) then 0 else (run k).top) id info hkT hi hj hid
      have hh := hControl n g s α ε ℓ schedule k id hα hε hs he
      rw [hp.2.1] at hh
      exact hh.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hmonoC hN))
    · rfl
  have hcach : (if cachedSolveEvent g (run k) id then (stepDebit m g α ℓ (run k)).2 else 0) ≤
      if cachedSolveEvent g (run k) id then ENNReal.ofReal (overhead (Cc+Cs) (max cc cs) ε ℓ*info.block) else 0 := by
    split_ifs with he
    · have hid := he.2.2.2.2.2.2.2
      have hp := open_frame_prefix_parameters m g s α (rootThreshold ε ℓ) ℓ schedule k T
        (run k).top id info hkT hi le_rfl hid
      rw [cached_debit m g α ℓ (run k) id he]
      have hh := hCache n g s α ε ℓ schedule k id hα hε hs he
      rw [hp.2.2] at hh
      exact hh.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hmonoS (by positivity)))
    · rfl
  rw [own_charge_events]
  calc
    _ ≤ callDiscoveryCharge g α (run k) id+
        (if cachedSolveEvent g (run k) id then ENNReal.ofReal (overhead (Cc+Cs) (max cc cs) ε ℓ*info.block) else 0)+
        (if controlEvent g (run k) id then ENNReal.ofReal (overhead (Cc+Cs) (max cc cs) ε ℓ*info.scale) else 0) :=
      add_le_add (add_le_add le_rfl hcach) hc
    _ = _ := by ac_rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IndicatorSum

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma sum_indicator_ofReal (S : Finset ℕ) (P : ℕ → Prop) (A : ℝ) (hA : 0 ≤ A) :
    (∑ k ∈ S, if P k then ENNReal.ofReal A else 0)=ENNReal.ofReal (A*((S.filter P).card : ℝ)) := by
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  rw [mul_comm,←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul hA]

lemma sum_indicator_ofReal_bound (S : Finset ℕ) (P : ℕ → Prop) (A B : ℝ)
    (hA : 0 ≤ A) (hB : ((S.filter P).card : ℝ) ≤ B) :
    (∑ k ∈ S, if P k then ENNReal.ofReal A else 0) ≤ ENNReal.ofReal (A*B) := by
  rw [sum_indicator_ofReal S P A hA]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hB hA)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OwnChargePrefix

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma uniform_own_charge_prefix (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule)
        (T id : ℕ) (info : CallInformation),
        (0 < α ∧ α < 1) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
        let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
        (run T).information id=some info →
        (∑ k ∈ range T, ownStepCharge m g α ℓ (run k) id) ≤
          ENNReal.ofReal (overhead (480*queueLogConstant) 2 ε ℓ*info.scale+
            overhead C c ε ℓ*info.scale*(9+7*((run T).episodes id : ℝ))+
            overhead C c ε ℓ*info.block*
              (((range T).filter (fun k => cachedSolveEvent g (run k) id)).card : ℝ)) := by
  obtain ⟨C,c,hC,hc,hStep⟩ := uniform_own_charge_step m
  refine ⟨C,c,hC,hc,?_⟩
  intro n g s α ε ℓ schedule T id info hα hε hs run hi
  let P := overhead C c ε ℓ
  have hq := root_threshold_unit ε hε ℓ
  have hlegal := information_legal_run m g s α (rootThreshold ε ℓ) hq ℓ schedule T id info hi
  have hN : 0 ≤ info.scale := by linarith [hlegal.2.1]
  have hP : 0 ≤ P := by
    dsimp only [P,overhead]
    exact mul_nonneg hC.le (pow_nonneg (by linarith [overhead_base_one ε hε ℓ]) _)
  have hPN : 0 ≤ P*info.scale := mul_nonneg hP hN
  have hPb : 0 ≤ P*(info.block : ℝ) := mul_nonneg hP (Nat.cast_nonneg _)
  have hControls := control_prefix_count m g s α (rootThreshold ε ℓ) hq.1 hs ℓ schedule T id
  have hdiscovery := discovery_charge_prefix_bound m g s α ε hα hε hs ℓ schedule T id info hi
  have hcontrol := sum_indicator_ofReal_bound (range T) (fun k => controlEvent g (run k) id) (P*info.scale)
    (9+7*((run T).episodes id : ℝ)) hPN hControls
  have hcached := sum_indicator_ofReal (range T) (fun k => cachedSolveEvent g (run k) id) (P*info.block) hPb
  have htotal : (∑ k ∈ range T, ownStepCharge m g α ℓ (run k) id) ≤
      (∑ k ∈ range T, callDiscoveryCharge g α (run k) id)+
      (∑ k ∈ range T, if controlEvent g (run k) id then ENNReal.ofReal (P*info.scale) else 0)+
      (∑ k ∈ range T, if cachedSolveEvent g (run k) id then ENNReal.ofReal (P*info.block) else 0) := by
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k hk
    exact hStep n g s α ε ℓ schedule k T id info hα hε hs (mem_range.mp hk).le hi
  apply htotal.trans
  rw [hcached]
  have hh := add_le_add (add_le_add hdiscovery hcontrol) (le_refl (ENNReal.ofReal (P*info.block*(((range T).filter (fun k => cachedSolveEvent g (run k) id)).card : ℝ))))
  apply hh.trans
  have hD : 0 ≤ overhead (480*queueLogConstant) 2 ε ℓ*info.scale := by
    have hQ := queueLogConstant_positive
    unfold overhead
    positivity
  have hE : 0 ≤ P*info.scale*(9+7*((run T).episodes id : ℝ)) := mul_nonneg hPN (by positivity)
  have hK : 0 ≤ P*(info.block : ℝ)*(((range T).filter (fun k => cachedSolveEvent g (run k) id)).card : ℝ) := by positivity
  rw [←ENNReal.ofReal_add hD hE,←ENNReal.ofReal_add (add_nonneg hD hE) hK]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControlCountPolynomial

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma uniform_control_allowance :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
      (ℓ : ℕ) (schedule : BlockSchedule), (0 < α ∧ α ≤ 1/2) → (0 < ε ∧ ε ≤ 1) →
      0 < g.graph.degree s → ∀ (T id : ℕ) (info : CallInformation),
      let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
      (run T).information id=some info →
        9+7*((run T).episodes id : ℝ) ≤ overhead C 4 ε ℓ*info.scale/info.block := by
  obtain ⟨Ce,hCe,hEp⟩ := uniform_episode_count
  refine ⟨9+7*Ce,by positivity,?_⟩
  intro m n g s α ε ℓ schedule hα hε hs T id info run hi
  have hq := root_threshold_unit ε hε ℓ
  have hlegal := information_legal_run m g s α (rootThreshold ε ℓ) hq ℓ schedule T id info hi
  have hb0 : 0 < (info.block : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hlegal.2.2.1
  have hbN := hlegal.2.2.2.1
  have he := hEp m n g s α ε ℓ schedule hα hε hs T id info hi
  have hratio : 1 ≤ info.scale/info.block := (le_div_iff₀ hb0).mpr (by simpa using hbN)
  have hp : 1 ≤ (2+Real.log (2/ε)+(ℓ : ℝ))^4 := one_le_pow₀ (overhead_base_one ε hε ℓ)
  have hextra : 9 ≤ 9*(2+Real.log (2/ε)+(ℓ : ℝ))^4*(info.scale/info.block) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 7)
  dsimp only [overhead] at hmul ⊢
  have heq : (9+7*Ce)*(2+Real.log (2/ε)+(ℓ : ℝ))^4*info.scale/info.block=
      9*(2+Real.log (2/ε)+(ℓ : ℝ))^4*(info.scale/info.block)+
      7*(Ce*(2+Real.log (2/ε)+(ℓ : ℝ))^4*info.scale/info.block) := by ring
  rw [heq]
  linarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LeafEvents

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma cached_event_level (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (k T id : ℕ) (info : CallInformation) (hkT : k ≤ T)
    (hi : (recursiveRun m g s α q ℓ schedule T).information id=some info)
    (hc : cachedSolveEvent g (recursiveRun m g s α q ℓ schedule k) id) : info.level=ℓ := by
  let run := recursiveRun m g s α q ℓ schedule
  have hid := hc.2.2.2.2.2.2.2
  have hp := open_frame_prefix_parameters m g s α q ℓ schedule k T (run k).top id info hkT hi le_rfl hid
  have hleaf := (cache_run m g s α q ℓ schedule k (run k).top le_rfl).2.1 hc.2.2.1
  exact hp.1.symm.trans hleaf

lemma nonleaf_cached_count_zero (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) (info : CallInformation)
    (hi : (recursiveRun m g s α q ℓ schedule T).information id=some info) (hne : info.level ≠ ℓ) :
    ((range T).filter (fun k => cachedSolveEvent g (recursiveRun m g s α q ℓ schedule k) id)).card=0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  obtain ⟨hk,hc⟩ := Finset.mem_filter.mp hk
  exact hne (cached_event_level m g s α q ℓ schedule k T id info (mem_range.mp hk).le hi hc)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OverheadProducts

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma overhead_mul (A B ε : ℝ) (a b ℓ : ℕ) :
    overhead A a ε ℓ*overhead B b ε ℓ=overhead (A*B) (a+b) ε ℓ := by
  unfold overhead
  rw [pow_add]
  ring

lemma overhead_sum (A B ε : ℝ) (a ℓ : ℕ) :
    overhead A a ε ℓ+overhead B a ε ℓ=overhead (A+B) a ε ℓ := by
  unfold overhead
  ring

lemma overhead_aggregate (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ c : ℕ) (D C A B : ℝ)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    overhead D 2 ε ℓ+overhead C c ε ℓ*overhead A 4 ε ℓ+
      overhead C c ε ℓ*overhead B 4 ε ℓ ≤
      overhead (D+C*A+C*B) (c+4) ε ℓ := by
  rw [overhead_mul,overhead_mul]
  have hmono := overhead_mono ε hε ℓ 2 (c+4) D D hD le_rfl (by omega)
  calc
    _ ≤ overhead D (c+4) ε ℓ+overhead (C*A) (c+4) ε ℓ+overhead (C*B) (c+4) ε ℓ :=
      add_le_add (add_le_add hmono le_rfl) le_rfl
    _ = _ := by rw [overhead_sum,overhead_sum]

lemma own_cost_aggregate (N b D P A B L K χ : ℝ)
    (hN : 1 ≤ N) (hb : 0 < b ∧ b ≤ N)
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B) (hχ : 0 ≤ χ)
    (hL : L ≤ A*N/b) (hK : K ≤ B*N*χ) :
    D*N+P*N*L+P*b*K ≤ (D+P*A+P*B)*(N^2/b+χ*N*b) := by
  have hN0 : 0 ≤ N := by linarith
  have hb0 : 0 ≤ b := hb.1.le
  have hNN : N ≤ N^2/b := by
    apply (le_div_iff₀ hb.1).mpr
    nlinarith
  have hDL : D*N ≤ D*(N^2/b) := mul_le_mul_of_nonneg_left hNN hD
  have hPL : P*N*L ≤ P*A*(N^2/b) := by
    have hh := mul_le_mul_of_nonneg_left hL (mul_nonneg hP (by linarith : 0 ≤ N))
    calc
      _ ≤ P*N*(A*N/b) := hh
      _ = _ := by ring
  have hPK : P*b*K ≤ P*B*(χ*N*b) := by
    have hh := mul_le_mul_of_nonneg_left hK (mul_nonneg hP hb.1.le)
    calc
      _ ≤ P*b*(B*N*χ) := hh
      _ = _ := by ring
  have h0 : 0 ≤ D+P*A+P*B := by positivity
  have hcross1 : 0 ≤ (D+P*A)*(χ*N*b) := by positivity
  have hcross2 : 0 ≤ P*B*(N^2/b) := by positivity
  nlinarith

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OwnWorkBound

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma uniform_own_work_bound (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule)
        (T id : ℕ) (info : CallInformation),
        (0 < α ∧ α ≤ 1/2) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
        let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
        (run T).information id=some info →
        (∑ k ∈ range T, ownStepCharge m g α ℓ (run k) id) ≤
          ENNReal.ofReal (overhead C c ε ℓ*(info.scale^2/info.block+
            if info.level=ℓ then info.scale*info.block else 0)) := by
  obtain ⟨Cp,cp,hCp,hcp,hOwn⟩ := uniform_own_charge_prefix m
  obtain ⟨Ca,hCa,hControl⟩ := uniform_control_allowance
  obtain ⟨Cb,hCb,hCache⟩ := uniform_cached_solve_count
  let D := 480*queueLogConstant
  let C := D+Cp*Ca+Cp*Cb
  have hQ := queueLogConstant_positive
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨C,cp+4,by dsimp only [C]; positivity,by omega,?_⟩
  intro n g s α ε ℓ schedule T id info hα hε hs run hi
  have ha : 0 < α ∧ α < 1 := ⟨hα.1,by linarith [hα.2]⟩
  have hq := root_threshold_unit ε hε ℓ
  have hlegal := information_legal_run m g s α (rootThreshold ε ℓ) hq ℓ schedule T id info hi
  have hN : 1 ≤ info.scale := hlegal.2.1
  have hb : 0 < (info.block : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hlegal.2.2.1
  have hbN := hlegal.2.2.2.1
  let P := overhead Cp cp ε ℓ
  let A := overhead Ca 4 ε ℓ
  let B := overhead Cb 4 ε ℓ
  let DD := overhead D 2 ε ℓ
  let χ : ℝ := if info.level=ℓ then 1 else 0
  have hp (R : ℝ) (r : ℕ) (hR : 0 ≤ R) : 0 ≤ overhead R r ε ℓ := by
    unfold overhead
    exact mul_nonneg hR (pow_nonneg (by linarith [overhead_base_one ε hε ℓ]) _)
  have hχ : 0 ≤ χ := by dsimp only [χ]; split_ifs <;> norm_num
  have hL := hControl m n g s α ε ℓ schedule hα hε hs T id info hi
  have hK : (((range T).filter (fun k => cachedSolveEvent g (run k) id)).card : ℝ) ≤ B*info.scale*χ := by
    by_cases he : info.level=ℓ
    · simpa only [χ,he,ite_true,mul_one] using hCache m n g s α ε ℓ schedule hα hε hs T id info hi
    · rw [nonleaf_cached_count_zero m g s α (rootThreshold ε ℓ) ℓ schedule T id info hi he]
      simp [χ,he]
  have hh := own_cost_aggregate info.scale info.block DD P A B (9+7*((run T).episodes id : ℝ))
    (((range T).filter (fun k => cachedSolveEvent g (run k) id)).card : ℝ) χ
    hN ⟨hb,hbN⟩ (hp D 2 hD.le) (hp Cp cp hCp.le) (hp Ca 4 hCa.le) (hp Cb 4 hCb.le) hχ hL hK
  have hM : DD+P*A+P*B ≤ overhead C (cp+4) ε ℓ :=
    overhead_aggregate ε hε ℓ cp D Cp Ca Cb hD.le hCp.le hCa.le hCb.le
  have hF : 0 ≤ info.scale^2/(info.block : ℝ)+χ*info.scale*info.block := by
    exact add_nonneg (div_nonneg (sq_nonneg _) hb.le) (mul_nonneg (mul_nonneg hχ (by linarith)) hb.le)
  have hbound := hOwn n g s α ε ℓ schedule T id info ha hε hs hi
  apply hbound.trans
  apply ENNReal.ofReal_le_ofReal
  have hfinal := hh.trans (mul_le_mul_of_nonneg_right hM hF)
  by_cases he : info.level=ℓ <;> simpa only [D,DD,P,A,B,χ,he,ite_true,ite_false,one_mul,zero_mul,add_zero] using hfinal

end
end NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal

theorem solution (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule)
        (T id : ℕ) (info : CallInformation),
        (0 < α ∧ α ≤ 1/2) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
        let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
        (run T).information id=some info →
        (∑ k ∈ range T, ownStepCharge m g α ℓ (run k) id) ≤
          ENNReal.ofReal (overhead C c ε ℓ*(info.scale^2/info.block+
            if info.level=ℓ then info.scale*info.block else 0)) := by
  exact uniform_own_work_bound m
