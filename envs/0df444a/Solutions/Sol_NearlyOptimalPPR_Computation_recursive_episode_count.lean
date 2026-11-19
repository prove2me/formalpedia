-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_episode_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:15:55.695798+00:00
-- url     : https://prove2.me/submissions/2b11f872-a0b4-4615-a2cb-7fd6ac874dd1

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_budget_energy
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_full_solve_count
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_stack_scales
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_call_metadata
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_call_history

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

abbrev parameters_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_control_parameters m n g s α q ℓ schedule t).2.2.2 hq

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

abbrev uniform_full_solve_count :=
  recursive_full_solve_count

abbrev threshold_relation_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_stack_scales m n g s α q ℓ schedule t).1

abbrev stack_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_stack_scales m n g s α q ℓ schedule t).2.1

abbrev scale_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ) (hq : 0 < q)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_stack_scales m n g s α q ℓ schedule t).2.2 hq

abbrev call_locations_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_call_metadata m n g s α q ℓ schedule t).1

abbrev open_frame_information_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_call_metadata m n g s α q ℓ schedule t).2.2.2.2.1

abbrev running_open_not_closed_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_call_metadata m n g s α q ℓ schedule t).2.2.2.2.2

abbrev information_run_persistent (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (info : CallInformation) (hab : a ≤ b)
    (hinfo : (recursiveRun m g s α q ℓ schedule a).information id=some info) :=
  (recursive_call_history m n g s α q ℓ schedule).1 a b id info hab hinfo

lemma closed_run_monotone (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) : Monotone (fun t => (recursiveRun m g s α q ℓ schedule t).closed) := by
  intro a b hab
  exact (recursive_call_history m n g s α q ℓ schedule).2.1 a b hab

abbrev frozenFrame_interval (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top) :=
  (recursive_call_history m n g s α q ℓ schedule).2.2.1 a b j hab hopen

abbrev fullSolves_run_events (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) :=
  (recursive_call_history m n g s α q ℓ schedule).2.2.2 T id |>.1

abbrev episodes_run_events (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) :=
  (recursive_call_history m n g s α q ℓ schedule).2.2.2 T id |>.2

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

-- Proof module: Solutions.ExteriorStages

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}


lemma raw_q (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ)
    (v : Fin n) (δ : ℝ) (i : ℕ) :
    ((rawExterior g α st t v δ).frames i).q = (st.frames i).q := by
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

-- Proof module: Solutions.NumericalInvariant

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma layer_residual_dominance (g : InputGraph n) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hlayer : LayerIdentity g st)
    (hparam : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (a b : ℕ) (hab : a ≤ b) (hbt : b ≤ st.top) (v : Fin n)
    (hv : v ∈ parentDomain st b) : (st.frames b).residual v ≤ (st.frames a).residual v := by
  induction b with
  | zero =>
    have he : a = 0 := by omega
    subst a
    exact le_rfl
  | succ b ih =>
    by_cases he : a = b+1
    · subst a; exact le_rfl
    · have hvb : v ∈ (st.frames b).active := by simpa [parentDomain] using hv
      have hvp : v ∈ parentDomain st b := (hreg b (by omega)).1 hvb
      have hid := hlayer b hbt v hvb
      have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
      have hg : 0 ≤ (if v ∈ (st.frames (b+1)).active then (st.frames (b+1)).q
          else 4*relative st (b+1) v) := by
        split
        · exact (hparam (b+1) hbt).1.le
        · exact mul_nonneg (by norm_num) ((hnum (b+1) hbt).1 v hv).2.1
      have hdrop : (st.frames (b+1)).residual v ≤ (st.frames b).residual v := by
        have hh := mul_nonneg hd hg
        linarith
      exact hdrop.trans (ih (by omega) (by omega) hvp)

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

-- Proof module: Solutions.ExteriorBudgets

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma admit_budget_fields (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) (j : ℕ) :
    ((admitStage g st t v).frames j).Q = (st.frames j).Q ∧
    ((admitStage g st t v).frames j).W = (st.frames j).W+
      if j = t ∧ (st.frames j).openBudget = true then
        (t+3 : ℕ)*(st.frames t).q*LocalPush.deg g.graph v/2 else 0 := by
  classical
  have hnt : t ≠ t+1 := by omega
  have hnt' : t+1 ≠ t := by omega
  by_cases hz : t = 0
  · subst t
    by_cases ht : 0 < st.top <;> by_cases hj : j = 0 <;> by_cases hc : j = 1 <;>
      (try omega) <;> simp [admitStage,changeFrame,ht,hj,hc]
  · by_cases ht : t < st.top <;> by_cases hj : j = t <;> by_cases hc : j = t+1 <;>
      (try omega) <;> simp [admitStage,changeFrame,ht,hj,hc,hz,hnt,hnt']

lemma refresh_budget_fields (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (j : ℕ) :
    ((refreshKeys g st T).frames j).Q = (st.frames j).Q ∧
    ((refreshKeys g st T).frames j).W = (st.frames j).W := by
  by_cases hj : j ≤ st.top <;> simp [refreshKeys,hj]

lemma exterior_budget_fields (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (j : ℕ) (hj : j ≤ st.top) :
    let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)
    let activated := relative st t v+δ = 3*(st.frames t).q/8
    ((exteriorPush g α st t v).frames j).Q = (st.frames j).Q ∧
    ((exteriorPush g α st t v).frames j).W = (st.frames j).W+
      (if (st.frames j).openBudget = true ∧ t ≤ j then (1-α)*LocalPush.deg g.graph v*δ else 0)+
      (if activated ∧ j = t ∧ (st.frames j).openBudget = true then
        birthAllowance st j*LocalPush.deg g.graph v else 0) := by
  classical
  dsimp only
  let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)
  let base := rawExterior g α st t v δ
  have hQ : (base.frames j).Q = (st.frames j).Q := by simp [base,rawExterior,hj]
  have hW : (base.frames j).W = (st.frames j).W+
      if (st.frames j).openBudget = true ∧ t ≤ j then (1-α)*LocalPush.deg g.graph v*δ else 0 := by
    simp [base,rawExterior,hj]
  have ho : (base.frames j).openBudget = (st.frames j).openBudget := by simp [base,rawExterior,hj]
  have hqt : (base.frames t).q = (st.frames t).q := raw_q g α st t v δ t
  rw [exterior_stages]
  simp only [←show δ = min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
    (3*(st.frames t).q/8-relative st t v) from rfl]
  simp only [debit]
  change ((refreshKeys g (if relative st t v+δ = 3*(st.frames t).q/8 then admitStage g base t v else base)
      (insert v (g.neighbors v).toFinset)).frames j).Q = _ ∧
    ((refreshKeys g (if relative st t v+δ = 3*(st.frames t).q/8 then admitStage g base t v else base)
      (insert v (g.neighbors v).toFinset)).frames j).W = _
  rw [(refresh_budget_fields g _ _ j).1,(refresh_budget_fields g _ _ j).2]
  by_cases ha : relative st t v+δ = 3*(st.frames t).q/8
  · simp only [ha,ite_true]
    rw [(admit_budget_fields g base t v j).1,(admit_budget_fields g base t v j).2,hQ,hW,ho,hqt]
    refine ⟨rfl,?_⟩
    by_cases he : j = t
    · subst j
      by_cases hbo : (st.frames t).openBudget = true <;> simp [hbo,birthAllowance] <;> ring
    · simp [he]
  · simp [ha,hQ,hW]

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

lemma running_call_prefix_parameters (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t T id : ℕ) (info : CallInformation) (ht : t ≤ T)
    (hinfo : (recursiveRun m g s α q ℓ schedule T).information id=some info)
    (hd : (recursiveRun m g s α q ℓ schedule t).done=false)
    (hid : ((recursiveRun m g s α q ℓ schedule t).frames (recursiveRun m g s α q ℓ schedule t).top).id=id) :
    let st := recursiveRun m g s α q ℓ schedule t
    st.top=info.level ∧ (st.frames st.top).N=info.scale ∧ (st.frames st.top).block=info.block := by
  intro st
  have hi := (running_call_information m g s α q ℓ schedule t id hd hid).1
  have hifuture := information_run_persistent m g s α q ℓ schedule t T id
    ⟨st.top,(st.frames st.top).N,(st.frames st.top).block⟩ ht hi
  rw [hinfo] at hifuture
  have heq : info=⟨st.top,(st.frames st.top).N,(st.frames st.top).block⟩ := Option.some.inj hifuture
  subst info
  exact ⟨rfl,rfl,rfl⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NoninitialPersistence

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma existing_pc_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ) :
    ((endCall g α st).frames j).pc=(st.frames j).pc := by
  unfold endCall
  dsimp only
  split <;> rfl

@[simp] lemma existing_pc_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (j : ℕ) : ((completeComponent m g s α st).frames j).pc=(st.frames j).pc := rfl

set_option maxHeartbeats 2000000 in
lemma noninitial_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top)
    (hp : (st.frames j).pc ≠ .initialDrain) :
    ((recursiveStep m g s α ℓ schedule st).frames j).pc ≠ .initialDrain := by
  have hnew : j ≠ st.top+1 := by omega
  by_cases hje : j=st.top
  all_goals
    cases hpend : pendingPush st with
    | none =>
      cases hpc : (st.frames st.top).pc <;>
        simp [recursiveStep,hpc,hpend,hje,hnew] <;> (try split_ifs) <;>
        (try simp_all (config := {maxSteps := 1000000}) [changePC,changeFrame,finishEpisode,Function.update_apply,debit]) <;>
        (try split_ifs) <;> (first | assumption | simp_all)
    | some p =>
      obtain ⟨t,v⟩ := p
      cases hpc : (st.frames st.top).pc <;>
        simp [recursiveStep,hpc,hpend,hje,hnew] <;> (try split_ifs) <;>
        (try simp_all (config := {maxSteps := 1000000}) [changePC,changeFrame,finishEpisode,Function.update_apply,debit]) <;>
        (try split_ifs) <;> (first | assumption | simp_all)

lemma noninitial_interval (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top)
    (hp : ((recursiveRun m g s α q ℓ schedule a).frames j).pc ≠ .initialDrain) :
    ((recursiveRun m g s α q ℓ schedule b).frames j).pc ≠ .initialDrain := by
  have aux : ∀ d, a+d ≤ b → ((recursiveRun m g s α q ℓ schedule (a+d)).frames j).pc ≠ .initialDrain := by
    intro d
    induction d with
    | zero => intro _; simpa using hp
    | succ d ih =>
      intro hd
      have hh := noninitial_step m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+d)) j
        (hopen (a+d) (by omega) (by omega)) (ih (by omega))
      rw [show a+(d+1)=(a+d)+1 by omega]
      simpa only [recursiveRun,Function.iterate_succ_apply'] using hh
  simpa [Nat.add_sub_of_le hab] using aux (b-a) (by omega)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BeginEpisodeTransition

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma begin_episode_transition (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hpc : (st.frames st.top).pc = .beginEpisode)
    (hrunning : (recursiveStep m g s α ℓ schedule st).done = false) :
    let next := recursiveStep m g s α ℓ schedule st
    let j := st.top
    let f := st.frames j
    let Q := max (∑ v ∈ f.active, f.residual v) (f.q*f.block)
    next.top = st.top ∧ next.x = st.x ∧
      (next.frames j).active = f.active ∧ (next.frames j).residual = f.residual ∧
      (next.frames j).Q = Q ∧ (next.frames j).theta = Q/f.block ∧
      (next.frames j).W = 0 ∧ (next.frames j).openBudget = true ∧
      (next.frames j).pc = if f.needFull then .fullSolve else .normalize := by
  obtain ⟨hd,hc⟩ := running_step_guards m g s α ℓ schedule st hrunning
  simp [recursiveStep,hd,hc,hpc,changeFrame,debit]

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

lemma begin_episode_run_origin (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ)
    (hrunning : (recursiveRun m g s α q ℓ schedule (t+1)).done = false)
    (hbegin : currentPC (recursiveRun m g s α q ℓ schedule (t+1)) = .beginEpisode) :
    currentPC (recursiveRun m g s α q ℓ schedule t) = .initialDrain ∨
      currentPC (recursiveRun m g s α q ℓ schedule t) = .restartDrain ∨
      currentPC (recursiveRun m g s α q ℓ schedule t) = .finishEpisode := by
  apply begin_episode_step_origin m g s α ℓ schedule _ (stack_run m g s α q ℓ schedule t)
  · simpa only [recursiveRun,Function.iterate_succ_apply'] using hrunning
  · simpa only [recursiveRun,Function.iterate_succ_apply'] using hbegin

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BeginEpisodeTop

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma begin_episode_step_top (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hstack : StackInvariant st)
    (hrunning : (recursiveStep m g s α ℓ schedule st).done=false)
    (hbegin : currentPC (recursiveStep m g s α ℓ schedule st)=.beginEpisode) :
    (recursiveStep m g s α ℓ schedule st).top=st.top := by
  obtain ⟨hd,hcomp⟩ := running_step_guards m g s α ℓ schedule st hrunning
  rcases begin_episode_step_origin m g s α ℓ schedule st hstack hrunning hbegin with hpc|hpc|hpc
  all_goals
    cases hpend : pendingPush st with
    | none => simp [recursiveStep,hd,hcomp,hpc,hpend]
    | some p => obtain ⟨t,v⟩ := p; simp [recursiveStep,hd,hcomp,hpc,hpend]

lemma begin_episode_run_top (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ)
    (hrunning : (recursiveRun m g s α q ℓ schedule (t+1)).done=false)
    (hbegin : currentPC (recursiveRun m g s α q ℓ schedule (t+1))=.beginEpisode) :
    (recursiveRun m g s α q ℓ schedule (t+1)).top=(recursiveRun m g s α q ℓ schedule t).top := by
  have hh := begin_episode_step_top m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule t)
    (stack_run m g s α q ℓ schedule t)
    (by simpa only [recursiveRun,Function.iterate_succ_apply'] using hrunning)
    (by simpa only [recursiveRun,Function.iterate_succ_apply'] using hbegin)
  simpa only [recursiveRun,Function.iterate_succ_apply'] using hh

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BeginEntryData

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

set_option maxHeartbeats 2000000 in
lemma begin_entry_data (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hstack : StackInvariant st)
    (hrunning : (recursiveStep m g s α ℓ schedule st).done=false)
    (hbegin : currentPC (recursiveStep m g s α ℓ schedule st)=.beginEpisode) :
    let next := recursiveStep m g s α ℓ schedule st
    next.top=st.top ∧ next.x=st.x ∧ (next.frames st.top).active=(st.frames st.top).active ∧
      (next.frames st.top).residual=(st.frames st.top).residual := by
  classical
  obtain ⟨hd,hcomp⟩ := running_step_guards m g s α ℓ schedule st hrunning
  rcases begin_episode_step_origin m g s α ℓ schedule st hstack hrunning hbegin with hpc|hpc|hpc
  all_goals
    cases hpend : pendingPush st with
    | none =>
      simp [recursiveStep,hd,hcomp,hpc,hpend] <;> (try split_ifs) <;>
        simp_all [currentPC,recursiveStep,hd,hcomp,hpc,hpend,changePC,changeFrame,finishEpisode,debit]
    | some p =>
      obtain ⟨t,v⟩ := p
      simp [recursiveStep,hd,hcomp,hpc,hpend] <;> (try split_ifs) <;>
        simp_all [currentPC,recursiveStep,hd,hcomp,hpc,hpend,changePC,changeFrame,finishEpisode,debit]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeIntervals

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma episode_events_same_level (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a ≤ b)
    (ha : episodeEvent (recursiveRun m g s α q ℓ schedule a) id)
    (hb : episodeEvent (recursiveRun m g s α q ℓ schedule b) id) :
    (recursiveRun m g s α q ℓ schedule a).top=(recursiveRun m g s α q ℓ schedule b).top := by
  have hi := (running_call_information m g s α q ℓ schedule b id hb.1 hb.2.2.2).1
  exact (running_call_prefix_parameters m g s α q ℓ schedule a b id _ hab hi ha.1 ha.2.2.2).1

lemma episode_event_span (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a ≤ b)
    (ha : episodeEvent (recursiveRun m g s α q ℓ schedule a) id)
    (hb : episodeEvent (recursiveRun m g s α q ℓ schedule b) id) :
    let run := recursiveRun m g s α q ℓ schedule
    let st := run a
    ∀ k, a ≤ k → k ≤ b → st.top ≤ (run k).top ∧ ((run k).frames st.top).id=id ∧
      ((run k).frames st.top).N=(st.frames st.top).N ∧ ((run k).frames st.top).block=(st.frames st.top).block := by
  intro run st
  have hi := (running_call_information m g s α q ℓ schedule a id ha.1 ha.2.2.2).1
  have hn := (running_call_information m g s α q ℓ schedule b id hb.1 hb.2.2.2).2
  exact unclosed_call_interval m g s α q ℓ schedule a b id
    ⟨st.top,(st.frames st.top).N,(st.frames st.top).block⟩ hi hn

lemma episode_event_positive (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (he : episodeEvent (recursiveRun m g s α q ℓ schedule t) id) : 0 < t := by
  by_contra hn
  have ht : t=0 := by omega
  have hp := he.2.2.1
  simp [ht,recursiveRun,recursiveInit,freshFrame,emptyFrame] at hp

lemma episode_event_gap (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a < b)
    (ha : episodeEvent (recursiveRun m g s α q ℓ schedule a) id)
    (hb : episodeEvent (recursiveRun m g s α q ℓ schedule b) id) : a+2 ≤ b := by
  by_contra hn
  have hb' : b=a+1 := by omega
  have hh := begin_episode_run_origin m g s α q ℓ schedule a (by simpa only [hb'] using hb.1)
    (by simpa only [currentPC,hb'] using hb.2.2.1)
  have hpc : currentPC (recursiveRun m g s α q ℓ schedule a)=.beginEpisode := ha.2.2.1
  rw [hpc] at hh
  simp at hh

lemma nonfirst_episode_origin (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a < b)
    (ha : episodeEvent (recursiveRun m g s α q ℓ schedule a) id)
    (hb : episodeEvent (recursiveRun m g s α q ℓ schedule b) id) :
    currentPC (recursiveRun m g s α q ℓ schedule (b-1))=.restartDrain ∨
      currentPC (recursiveRun m g s α q ℓ schedule (b-1))=.finishEpisode := by
  let run := recursiveRun m g s α q ℓ schedule
  let j := (run a).top
  have hgap := episode_event_gap m g s α q ℓ schedule a b id hab ha hb
  have htime : b-1+1=b := by omega
  have htop := begin_episode_run_top m g s α q ℓ schedule (b-1)
    (by simpa only [htime] using hb.1) (by simpa only [currentPC,htime] using hb.2.2.1)
  rw [htime] at htop
  have hlevels := episode_events_same_level m g s α q ℓ schedule a b id hab.le ha hb
  have hspan := episode_event_span m g s α q ℓ schedule a b id hab.le ha hb
  have htopold : (run (b-1)).top=j := htop.symm.trans hlevels.symm
  have hstart : ((run a).frames j).pc ≠ .initialDrain := by
    change ((run a).frames (run a).top).pc ≠ .initialDrain
    rw [ha.2.2.1]
    decide
  have hn := noninitial_interval m g s α q ℓ schedule a (b-1) j (by omega)
    (fun k hak hkb => (hspan k hak (by omega)).1) hstart
  have hor := begin_episode_run_origin m g s α q ℓ schedule (b-1)
    (by simpa only [htime] using hb.1) (by simpa only [currentPC,htime] using hb.2.2.1)
  rcases hor with hi|hr|hf
  · unfold currentPC at hi
    rw [htopold] at hi
    exact False.elim (hn hi)
  · exact Or.inl hr
  · exact Or.inr hf

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FinishRequestTransition

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma finish_to_begin_transition (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hpc : (st.frames st.top).pc = .finishEpisode)
    (hrunning : (recursiveStep m g s α ℓ schedule st).done = false)
    (hbegin : currentPC (recursiveStep m g s α ℓ schedule st) = .beginEpisode) :
    let next := recursiveStep m g s α ℓ schedule st
    let j := st.top
    ¬ancestorExhausted st ∧ ¬exhausted st j ∧ (st.frames j).theta ≠ (st.frames j).q ∧
      next.top = st.top ∧ next.x = st.x ∧ (next.frames j).active = (st.frames j).active ∧
      (next.frames j).residual = (st.frames j).residual ∧
      (next.frames j).needFull = decide ((st.frames j).Q/2 ≤ ∑ v ∈ (st.frames j).active, (st.frames j).residual v) := by
  classical
  obtain ⟨hd,hcomp⟩ := running_step_guards m g s α ℓ schedule st hrunning
  have ha : ¬ancestorExhausted st := by
    intro hh
    simp [currentPC,recursiveStep,hd,hcomp,hpc,hh,changePC,changeFrame,debit] at hbegin
  have he : ¬exhausted st st.top := by
    intro hh
    simp [currentPC,recursiveStep,hd,hcomp,hpc,ha,hh,changePC,changeFrame,debit] at hbegin
  have hθ : (st.frames st.top).theta ≠ (st.frames st.top).q := by
    intro hh
    simp [currentPC,recursiveStep,hd,hcomp,hpc,ha,he,hh,changePC,changeFrame,finishEpisode,debit] at hbegin
  refine ⟨ha,he,hθ,?_⟩
  simp [recursiveStep,hd,hcomp,hpc,ha,he,hθ,changeFrame,finishEpisode,debit]

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

-- Proof module: Solutions.EpisodeBudgetControl

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma Q_changePC (st : RecursiveState n) (pc : NormalizePC) (j : ℕ) :
    ((changePC st pc).frames j).Q=(st.frames j).Q :=
  observe_changeFrame (fun f => f.Q) st st.top _ rfl j
@[simp] lemma Q_debit (st : RecursiveState n) (i j : ℕ) (c : ℝ≥0∞) :
    ((debit st i c).frames j).Q=(st.frames j).Q := rfl
@[simp] lemma Q_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (j : ℕ) :
    ((refreshKeys g st T).frames j).Q=(st.frames j).Q := (refresh_budget_fields g st T j).1
@[simp] lemma Q_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) (j : ℕ) :
    ((jointUpdate g α st h).frames j).Q=(st.frames j).Q := by by_cases hj : j ≤ st.top <;> simp [jointUpdate,hj]
@[simp] lemma Q_finish (st : RecursiveState n) (j : ℕ) :
    ((finishEpisode st).frames j).Q=(st.frames j).Q := by
  unfold finishEpisode
  exact observe_changeFrame (fun f => f.Q) _ st.top _ rfl j
@[simp] lemma Q_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ) :
    ((endCall g α st).frames j).Q=(st.frames j).Q := by unfold endCall; dsimp only; split <;> rfl
@[simp] lemma Q_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) (j : ℕ) :
    ((completeComponent m g s α st).frames j).Q=(st.frames j).Q := rfl

set_option maxHeartbeats 1500000 in
lemma Q_step_no_begin (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top)
    (hp : j=st.top → (st.frames st.top).pc ≠ .beginEpisode) :
    ((recursiveStep m g s α ℓ schedule st).frames j).Q=(st.frames j).Q := by
  have hnew : j ≠ st.top+1 := by omega
  have hext (t : ℕ) (v : Fin n) : ((exteriorPush g α st t v).frames j).Q=(st.frames j).Q :=
    (exterior_budget_fields g α st t v j hj).1
  by_cases hje : j=st.top
  all_goals
    cases hpend : pendingPush st with
    | none =>
      cases hpc : (st.frames st.top).pc <;>
        simp [recursiveStep,hpc,hpend,hje,hnew] <;> (try split_ifs) <;>
        simp_all [changeFrame,Function.update_apply,finishEpisode,debit]
    | some p =>
      obtain ⟨t,v⟩ := p
      cases hpc : (st.frames st.top).pc <;>
        simp [recursiveStep,hpc,hpend,hje,hnew,hext] <;> (try split_ifs) <;>
        simp_all [changeFrame,Function.update_apply,finishEpisode,debit]

lemma Q_step_no_episode (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top)
    (hp : ¬episodeEvent st (st.frames j).id) :
    ((recursiveStep m g s α ℓ schedule st).frames j).Q=(st.frames j).Q := by
  by_cases hd : st.done=true
  · simp [recursiveStep,hd]
  by_cases hc : componentComplete st
  · simp [recursiveStep,hd,hc]
  apply Q_step_no_begin m g s α ℓ schedule st j hj
  intro hje hpc
  apply hp
  refine ⟨Bool.eq_false_iff.mpr hd,hc,hpc,?_⟩
  rw [hje]

lemma Q_interval_no_episodes (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j id : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top ∧
      ((recursiveRun m g s α q ℓ schedule k).frames j).id=id)
    (hno : ∀ k, a ≤ k → k < b → ¬episodeEvent (recursiveRun m g s α q ℓ schedule k) id) :
    ((recursiveRun m g s α q ℓ schedule b).frames j).Q=
      ((recursiveRun m g s α q ℓ schedule a).frames j).Q := by
  have aux : ∀ d, a+d ≤ b → ((recursiveRun m g s α q ℓ schedule (a+d)).frames j).Q=
      ((recursiveRun m g s α q ℓ schedule a).frames j).Q := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      have hh := hopen (a+d) (by omega) (by omega)
      have hs := Q_step_no_episode m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+d)) j hh.1
        (by rw [hh.2]; exact hno (a+d) (by omega) (by omega))
      rw [show a+(d+1)=(a+d)+1 by omega]
      simpa only [recursiveRun,Function.iterate_succ_apply'] using hs.trans (ih (by omega))
  simpa only [Nat.add_sub_of_le hab] using aux (b-a) (by omega)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NonfullEpisode

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma restart_begin_needFull (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hpc : (st.frames st.top).pc=.restartDrain)
    (hrunning : (recursiveStep m g s α ℓ schedule st).done=false)
    (hbegin : currentPC (recursiveStep m g s α ℓ schedule st)=.beginEpisode) :
    ((recursiveStep m g s α ℓ schedule st).frames st.top).needFull=true := by
  obtain ⟨hd,hc⟩ := running_step_guards m g s α ℓ schedule st hrunning
  cases hpend : pendingPush st with
  | none =>
    simp [recursiveStep,hd,hc,hpc,hpend] <;> (try split_ifs) <;>
      simp_all [currentPC,recursiveStep,hd,hc,hpc,hpend,changePC,changeFrame,debit]
  | some p =>
    obtain ⟨t,v⟩ := p
    simp [recursiveStep,hd,hc,hpc,hpend] <;> (try split_ifs) <;>
      simp_all [currentPC,recursiveStep,hd,hc,hpc,hpend,changePC,changeFrame,debit]

lemma nonfull_episode_mass_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a < b)
    (ha : episodeEvent (recursiveRun m g s α q ℓ schedule a) id)
    (hb : episodeEvent (recursiveRun m g s α q ℓ schedule b) id)
    (hn : ((recursiveRun m g s α q ℓ schedule b).frames (recursiveRun m g s α q ℓ schedule b).top).needFull=false) :
    let st := recursiveRun m g s α q ℓ schedule b
    (st.frames st.top).q*(st.frames st.top).block < (st.frames st.top).Q ∧
      (∑ v ∈ (st.frames st.top).active, (st.frames st.top).residual v) < (st.frames st.top).Q/2 := by
  intro st
  let old := recursiveRun m g s α q ℓ schedule (b-1)
  have hbpos := episode_event_positive m g s α q ℓ schedule b id hb
  have htime : b-1+1=b := by omega
  have hstep : st=recursiveStep m g s α ℓ schedule old := by
    dsimp only [st]
    rw [←htime]
    simp only [old,recursiveRun,Function.iterate_succ_apply']
  have hentry := begin_entry_data m g s α ℓ schedule old (stack_run m g s α q ℓ schedule (b-1))
    (by rw [←hstep]; exact hb.1) (by rw [←hstep]; exact hb.2.2.1)
  rw [←hstep] at hentry
  have hfinish : (old.frames old.top).pc=.finishEpisode := by
    rcases nonfirst_episode_origin m g s α q ℓ schedule a b id hab ha hb with hr|hf
    · have hh := restart_begin_needFull m g s α ℓ schedule old hr (by rw [←hstep]; exact hb.1)
        (by rw [←hstep]; exact hb.2.2.1)
      rw [←hstep,←hentry.1] at hh
      rw [hn] at hh
      cases hh
    · exact hf
  have hft := finish_to_begin_transition m g s α ℓ schedule old hfinish (by rw [←hstep]; exact hb.1)
    (by rw [←hstep]; exact hb.2.2.1)
  rw [←hstep] at hft
  have hQ : (st.frames st.top).Q=(old.frames old.top).Q := by
    rw [hentry.1,hstep]
    exact Q_step_no_begin m g s α ℓ schedule old old.top le_rfl (by intro _; rw [hfinish]; decide)
  have hfixed := frozenFrame_step m g s α ℓ schedule old old.top le_rfl
  rw [←hstep] at hfixed
  have hqeq : (st.frames st.top).q=(old.frames old.top).q := by rw [hentry.1]; exact congrArg Prod.fst hfixed
  have hbeq : (st.frames st.top).block=(old.frames old.top).block := by rw [hentry.1]; exact congrArg (fun z => z.2.2.1) hfixed
  have hneed : (st.frames old.top).needFull=false := by rw [←hentry.1]; exact hn
  rw [hft.2.2.2.2.2.2.2] at hneed
  have hmass : (∑ v ∈ (old.frames old.top).active, (old.frames old.top).residual v) < (old.frames old.top).Q/2 :=
    lt_of_not_ge (of_decide_eq_false hneed)
  have hopen : (old.frames old.top).openBudget=true := by
    have hh : (old.frames old.top).openBudget=budgetPC (old.frames old.top).pc :=
      budget_run m g s α q ℓ schedule (b-1) old.top le_rfl
    simpa only [hfinish,budgetPC] using hh
  have htheta := (parameters_run m g s α q hq ℓ schedule (b-1) old.top le_rfl).2.2 hopen
  have hbpositive : (0 : ℝ) < (old.frames old.top).block := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (parameters_run m g s α q hq ℓ schedule (b-1) old.top le_rfl).2.1
  have hscale := (scale_run m g s α q hq ℓ schedule (b-1)).1 old.top le_rfl hopen
  refine ⟨?_,?_⟩
  · rw [hqeq,hbeq,hQ,hscale]
    exact mul_lt_mul_of_pos_right (lt_of_le_of_ne htheta (Ne.symm hft.2.2.1)) hbpositive
  · rw [hQ,hentry.1,hentry.2.2.1,hentry.2.2.2]
    exact hmass

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

lemma active_mass_le_parent (g : InputGraph n) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hlayer : LayerIdentity g st) (hp : ParameterInvariant st)
    (hnum : NumericalInvariant g st) (j : ℕ) (hj : j < st.top) :
    (∑ v ∈ (st.frames (j+1)).active, (st.frames (j+1)).residual v) ≤
      ∑ v ∈ (st.frames j).active, (st.frames j).residual v := by
  have hsub : (st.frames (j+1)).active ⊆ (st.frames j).active := by
    simpa [parentDomain] using (hreg (j+1) hj).1
  calc
    _ ≤ ∑ v ∈ (st.frames (j+1)).active, (st.frames j).residual v := by
      apply Finset.sum_le_sum
      intro v hv
      exact layer_residual_dominance g st hreg hlayer hp hnum j (j+1) (by omega) hj v ((hreg (j+1) hj).1 hv)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v hv _ =>
      ((hnum j hj.le).1 v ((hreg j hj.le).1 hv)).1)

lemma run_child_mass_unexhausted (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t j : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    j < st.top → ¬exhausted st j →
      (∑ v ∈ (st.frames (j+1)).active, (st.frames (j+1)).residual v) <
        2*(st.frames (j+1)).q*(st.frames (j+1)).N := by
  intro st hj he
  have hm := active_mass_le_parent g st (region_run m g s α q ℓ schedule t)
    (layer_run m g s α q ℓ schedule t) (parameters_run m g s α q hq ℓ schedule t)
    (numerical_run m g s α q hα hq hs ℓ schedule t) j hj
  have hopen : (st.frames j).openBudget=true := by
    simpa [stack_run m g s α q ℓ schedule t j hj,budgetPC] using budget_run m g s α q ℓ schedule t j hj.le
  have hp := run_unexhausted_mass m g s α q hα hq hs ℓ schedule t j hj.le hopen he
  have hscale : ScaleInvariant st := scale_run m g s α q hq ℓ schedule t
  have hQ : (st.frames j).Q=(st.frames (j+1)).q*(st.frames (j+1)).N := by
    rw [hscale.1 j hj.le hopen,hscale.2 j hj,threshold_relation_run m g s α q ℓ schedule t j hj]
  change (∑ v ∈ (st.frames j).active, (st.frames j).residual v) < 2*(st.frames j).Q at hp
  rw [hQ] at hp
  nlinarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CurrentMassBound

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma current_mass_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ)
    (he : ¬ancestorExhausted (recursiveRun m g s α q ℓ schedule t)) :
    let st := recursiveRun m g s α q ℓ schedule t
    (∑ v ∈ (st.frames st.top).active, (st.frames st.top).residual v) ≤ 2*(st.frames st.top).q*(st.frames st.top).N := by
  intro st
  cases htop : st.top with
  | zero =>
    have hnum : NumericalInvariant g st := numerical_run m g s α q hα hq hs ℓ schedule t
    have hmass := root_residual_mass_bound g s α hα.1.le st (root_identity_run m g s α q ℓ schedule t) hnum
      ((parameters_run m g s α q hq ℓ schedule t 0 (Nat.zero_le _)).1.le)
    have hsub : (∑ v ∈ (st.frames 0).active, (st.frames 0).residual v) ≤ ∑ v, (st.frames 0).residual v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ =>
        ((hnum 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).1)
    have hqr : (st.frames 0).q=q := root_threshold_run m g s α q ℓ schedule t
    have hNr : (st.frames 0).N=1/q := root_scale_run m g s α q ℓ schedule t
    rw [hqr,hNr]
    have hqN : 2*q*(1/q)=(2 : ℝ) := by field_simp
    rw [hqN]
    linarith
  | succ j =>
    have hj : j < st.top := by omega
    have hnot : ¬exhausted st j := fun hh => he ⟨j,hj,hh⟩
    have hh := run_child_mass_unexhausted m g s α q hα hq hs ℓ schedule t j hj hnot
    simpa only [htop] using hh.le

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DescentCounts

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation

lemma bounded_descent_count (a : ℕ → ℝ) (E : Finset ℕ) (T : ℕ) (B : ℝ)
    (hbound : ∀ k ≤ T, 0 ≤ a k ∧ a k ≤ B)
    (hdrop : ∀ k < T, k ∉ E → a (k+1)+1 ≤ a k) :
    (T : ℝ) ≤ B+(B+1)*((E ∩ Finset.range T).card : ℝ) := by
  classical
  have hB : 0 ≤ B := (hbound 0 (Nat.zero_le _)).1.trans (hbound 0 (Nat.zero_le _)).2
  have hrow (k : ℕ) (hk : k ∈ Finset.range T) :
      (1 : ℝ) ≤ a k-a (k+1)+(if k ∈ E then B+1 else 0) := by
    have hkt : k < T := Finset.mem_range.mp hk
    by_cases he : k ∈ E
    · rw [if_pos he]
      linarith [(hbound k hkt.le).1,(hbound (k+1) (by omega)).2]
    · rw [if_neg he]
      linarith [hdrop k hkt he]
  have hs := Finset.sum_le_sum hrow
  have htel : (∑ k ∈ Finset.range T, (a k-a (k+1))) = a 0-a T := by
    clear hbound hdrop hrow hs hB
    induction T with
    | zero => simp
    | succ T ih => rw [Finset.sum_range_succ,ih]; ring
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,Finset.sum_add_distrib,htel] at hs
  have hsum : (∑ k ∈ Finset.range T, if k ∈ E then B+1 else 0) =
      ((E ∩ Finset.range T).card : ℝ)*(B+1) := by
    rw [←Finset.sum_filter]
    have heq : (Finset.range T).filter (fun k => k ∈ E) = E ∩ Finset.range T := by
      ext k; simp [and_comm]
    rw [heq]
    simp only [Finset.sum_const,nsmul_eq_mul]
  rw [hsum] at hs
  nlinarith [(hbound 0 (Nat.zero_le _)).2,(hbound T le_rfl).1]

lemma bounded_nat_descent_count (a : ℕ → ℕ) (E : Finset ℕ) (T B : ℕ)
    (hbound : ∀ k ≤ T, a k ≤ B)
    (hdrop : ∀ k < T, k ∉ E → a (k+1) < a k) :
    T ≤ B+(B+1)*(E ∩ Finset.range T).card := by
  have hh := bounded_descent_count (fun k => (a k : ℝ)) E T (B : ℝ)
    (fun k hk => ⟨by positivity,by exact_mod_cast hbound k hk⟩)
    (fun k hk he => by exact_mod_cast hdrop k hk he)
  exact_mod_cast hh

lemma massRank_zero (L μ : ℝ) (hμ : μ ≤ L) : massRank L μ = 0 := by
  by_cases hL : L = 0
  · simp [massRank,hL]
  · simp [massRank,max_eq_right hμ,hL]

lemma massRank_pos (L μ : ℝ) (hL : 0 < L) (hμ : L < μ) : 0 < massRank L μ := by
  unfold massRank
  rw [max_eq_left hμ.le,Nat.ceil_pos]
  exact div_pos (Real.log_pos ((lt_div_iff₀ hL).mpr (by linarith)))
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))

lemma massRank_bound (L U μ : ℝ) (hL : 0 < L) (hLU : L ≤ U) (hμ : μ ≤ U) :
    massRank L μ ≤ ⌈Real.log (U/L)/Real.log 2⌉₊ := by
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  apply Real.log_le_log
  · exact div_pos (lt_of_lt_of_le hL (le_max_right _ _)) hL
  · exact div_le_div_of_nonneg_right (max_le hμ hLU) hL.le

lemma massRank_halving (L μ ν : ℝ) (hL : 0 < L) (hμ : L < μ) (hhalf : ν ≤ μ/2) :
    massRank L ν < massRank L μ := by
  by_cases hν : ν ≤ L
  · rw [massRank_zero L ν hν]
    exact massRank_pos L μ hL hμ
  · have hνL : L < ν := lt_of_not_ge hν
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hμ0 : 0 < μ := hL.trans hμ
    have hν0 : 0 < ν := hL.trans hνL
    have hh := Real.log_le_log (div_pos hν0 hL)
      (div_le_div_of_nonneg_right hhalf hL.le)
    have heq : Real.log ((μ/2)/L) = Real.log (μ/L)-Real.log 2 := by
      rw [show (μ/2)/L = (μ/L)/2 by ring]
      rw [Real.log_div (div_ne_zero hμ0.ne' hL.ne') (by norm_num)]
    rw [heq] at hh
    have hdiv : Real.log (ν/L)/Real.log 2 ≤ Real.log (μ/L)/Real.log 2-1 := by
      have hscaled := div_le_div_of_nonneg_right hh hl2.le
      calc
        _ ≤ (Real.log (μ/L)-Real.log 2)/Real.log 2 := hscaled
        _ = _ := by rw [sub_div,div_self hl2.ne']
    have hc := Nat.ceil_mono hdiv
    rw [Nat.ceil_sub_one] at hc
    have hp := massRank_pos L μ hL hμ
    unfold massRank at hp ⊢
    rw [max_eq_left hνL.le,max_eq_left hμ.le]
    rw [max_eq_left hμ.le] at hp
    omega

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ClippedHalving

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma massRank_clipped_halving (L μ ν : ℝ) (hL : 0 < L) (hμ : L < μ)
    (hν : ν ≤ max (μ/2) L) : massRank L ν < massRank L μ := by
  by_cases hh : μ/2 ≤ L
  · rw [max_eq_right hh] at hν
    rw [massRank_zero L ν hν]
    exact massRank_pos L μ hL hμ
  · rw [max_eq_left (le_of_not_ge hh)] at hν
    exact massRank_halving L μ ν hL hμ hν

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

-- Proof module: Solutions.EpisodePairHalving

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma episode_transition_Q (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (id : ℕ) (he : episodeEvent st id) :
    ((recursiveStep m g s α ℓ schedule st).frames st.top).Q=episodeBudget st st.top := by
  have hd : (recursiveStep m g s α ℓ schedule st).done=false := by
    simp [recursiveStep,he.1,he.2.1,he.2.2.1,changeFrame,debit]
  exact (begin_episode_transition m g s α ℓ schedule st he.2.2.1 hd).2.2.2.2.1

lemma episode_budget_bounds (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ) (he : episodeEvent (recursiveRun m g s α q ℓ schedule t) id) :
    let st := recursiveRun m g s α q ℓ schedule t
    (st.frames st.top).q*(st.frames st.top).block ≤ episodeBudget st st.top ∧
      episodeBudget st st.top ≤ 2*(st.frames st.top).q*(st.frames st.top).N := by
  intro st
  have hm := current_mass_bound m g s α q hα hq.1 hs ℓ schedule t
    (begin_episode_run_unexhausted m g s α q ℓ schedule t he.1 he.2.2.1)
  have hblock := (scale_bounds_run m g s α q hq ℓ schedule t st.top le_rfl).2.1
  have hN := (scale_bounds_run m g s α q hq ℓ schedule t st.top le_rfl).1
  have hqf := (parameters_run m g s α q hq.1 ℓ schedule t st.top le_rfl).1
  refine ⟨le_max_right _ _,max_le hm ?_⟩
  have hh := mul_le_mul_of_nonneg_left hblock hqf.le
  nlinarith

lemma nonfull_episode_pair_halving (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a < b)
    (ha : episodeEvent (recursiveRun m g s α q ℓ schedule a) id)
    (hb : episodeEvent (recursiveRun m g s α q ℓ schedule b) id)
    (hno : ∀ k, a < k → k < b → ¬episodeEvent (recursiveRun m g s α q ℓ schedule k) id)
    (hn : ((recursiveRun m g s α q ℓ schedule b).frames (recursiveRun m g s α q ℓ schedule b).top).needFull=false) :
    let run := recursiveRun m g s α q ℓ schedule
    let j := (run a).top
    let L := ((run a).frames j).q*((run a).frames j).block
    L < episodeBudget (run a) j ∧
      episodeBudget (run b) j ≤ max (episodeBudget (run a) j/2) L := by
  intro run j L
  have hspan := episode_event_span m g s α q ℓ schedule a b id hab.le ha hb
  have hlevel := episode_events_same_level m g s α q ℓ schedule a b id hab.le ha hb
  have hlevel' : (run b).top=j := hlevel.symm
  have hh := nonfull_episode_mass_bound m g s α q hq ℓ schedule a b id hab ha hb hn
  have hgap := episode_event_gap m g s α q ℓ schedule a b id hab ha hb
  have hconst := Q_interval_no_episodes m g s α q ℓ schedule (a+1) b j id (by omega)
    (fun k hak hkb => ⟨(hspan k (by omega) hkb.le).1,(hspan k (by omega) hkb.le).2.1⟩)
    (fun k hak hkb => hno k (by omega) hkb)
  have hnew := episode_transition_Q m g s α ℓ schedule (run a) id ha
  have hstep : run (a+1)=recursiveStep m g s α ℓ schedule (run a) := by
    simp only [run,recursiveRun,Function.iterate_succ_apply']
  rw [←hstep] at hnew
  have hQ : ((run b).frames j).Q=episodeBudget (run a) j := hconst.trans hnew
  have hf := frozenFrame_interval m g s α q ℓ schedule a b j hab.le
    (fun k hak hkb => (hspan k hak hkb.le).1)
  have hqeq : ((run b).frames j).q=((run a).frames j).q := congrArg Prod.fst hf
  have hbeq : ((run b).frames j).block=((run a).frames j).block := congrArg (fun z => z.2.2.1) hf
  change ((run b).frames (run b).top).q*((run b).frames (run b).top).block < _ ∧ _ at hh
  rw [hlevel',hQ,hqeq,hbeq] at hh
  refine ⟨hh.1,?_⟩
  unfold episodeBudget
  rw [hqeq,hbeq]
  exact max_le_max hh.2.le le_rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeNextFull

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma componentComplete_metadata (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) (hf : (f (st.frames j)).active=(st.frames j).active) :
    componentComplete (changeFrame st j f) ↔ componentComplete st := by
  unfold componentComplete
  rw [observe_changeFrame (fun f => f.active) st j f hf 0]
  rfl

lemma requested_episode_full_event (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (he : episodeEvent (recursiveRun m g s α q ℓ schedule t) id)
    (hn : ((recursiveRun m g s α q ℓ schedule t).frames (recursiveRun m g s α q ℓ schedule t).top).needFull=true) :
    fullSolveEvent g (recursiveRun m g s α q ℓ schedule (t+1)) id := by
  let st := recursiveRun m g s α q ℓ schedule t
  let next := recursiveRun m g s α q ℓ schedule (t+1)
  have hstep : next=recursiveStep m g s α ℓ schedule st := by
    simp only [next,st,recursiveRun,Function.iterate_succ_apply']
  have hd : st.done=false := he.1
  have hc : ¬componentComplete st := he.2.1
  have hp : (st.frames st.top).pc=.beginEpisode := he.2.2.1
  have hnd : next.done=false := by rw [hstep]; simp [recursiveStep,hd,hc,hp,changeFrame,debit]
  have ht := begin_episode_transition m g s α ℓ schedule st hp (by rwa [←hstep])
  rw [←hstep] at ht
  have hqpos := (parameters_run m g s α q hq ℓ schedule t st.top le_rfl).1
  have hbpos : (0 : ℝ) < (st.frames st.top).block := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (parameters_run m g s α q hq ℓ schedule t st.top le_rfl).2.1
  have hQ : 0 < (next.frames next.top).Q := by
    rw [ht.1,ht.2.2.2.2.1]
    exact lt_of_lt_of_le (mul_pos hqpos hbpos) (le_max_right _ _)
  have hW : (next.frames next.top).W=0 := by rw [ht.1]; exact ht.2.2.2.2.2.2.1
  have hanc : ¬ancestorExhausted next := by
    have hh := begin_episode_run_unexhausted m g s α q ℓ schedule t hd hp
    rw [hstep]
    simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hc,hp]
    intro hx
    obtain ⟨i,hi,hex⟩ := hx
    change i < st.top at hi
    apply hh
    refine ⟨i,hi,?_⟩
    simpa only [exhausted,changeFrame,debit,Function.update_of_ne (ne_of_lt hi)] using hex
  have hany : ¬anyExhausted next := by
    rintro ⟨i,hi,hex⟩
    by_cases hlt : i < next.top
    · exact hanc ⟨i,hlt,hex⟩
    · have heq : i=next.top := by omega
      rw [heq] at hex
      have hh := hex.2
      rw [hW] at hh
      linarith
  have hncomp : ¬componentComplete next := by
    rw [hstep]
    simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hc,hp]
    rw [componentComplete_metadata _ _ _ rfl]
    exact hc
  have hpc : (next.frames next.top).pc=.fullSolve := by
    rw [ht.1,ht.2.2.2.2.2.2.2.2]
    have hneed : (st.frames st.top).needFull=true := hn
    rw [hneed]
    rfl
  have hf := frozenFrame_step m g s α ℓ schedule st st.top le_rfl
  rw [←hstep] at hf
  have hid : (next.frames next.top).id=id := by
    rw [ht.1]
    exact (congrArg (fun z => z.2.2.2) hf).trans he.2.2.2
  exact ⟨hnd,hncomp,hpc,hany,run_active_domain_valid m g s α q hq.le hs ℓ schedule (t+1) next.top le_rfl,hid⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EventEnumeration

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma enumerateTimes_mem (S : Finset ℕ) (k : ℕ) (hk : k < S.card) : enumerateTimes S k ∈ S := by
  simp only [enumerateTimes,dif_pos hk]
  exact Finset.orderEmbOfFin_mem S rfl ⟨k,hk⟩

lemma enumerateTimes_strictMono (S : Finset ℕ) : StrictMono (enumerateTimes S) := by
  apply strictMono_nat_of_lt_succ
  intro k
  by_cases hk : k < S.card
  · by_cases hnext : k+1 < S.card
    · simp only [enumerateTimes,dif_pos hk,dif_pos hnext]
      exact (S.orderEmbOfFin rfl).strictMono (by simp)
    · have hh := enumerateTimes_mem S k hk
      have hmax : enumerateTimes S k ≤ S.sup id := Finset.le_sup (f := id) hh
      have he : k+1=S.card := by omega
      have heq : enumerateTimes S (k+1) = S.sup id+1 := by
        rw [he]
        simp [enumerateTimes]
      rw [heq]
      exact Nat.lt_succ_of_le hmax
  · have hn : ¬k+1 < S.card := by omega
    simp only [enumerateTimes,dif_neg hk,dif_neg hn]
    omega

lemma enumerateTimes_image (S : Finset ℕ) : (Finset.range S.card).image (enumerateTimes S) = S := by
  have hsub : (Finset.range S.card).image (enumerateTimes S) ⊆ S := by
    intro v hv
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hv
    exact enumerateTimes_mem S k (Finset.mem_range.mp hk)
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_image_of_injective _ (enumerateTimes_strictMono S).injective,Finset.card_range]

lemma enumeration_before_bound (S : Finset ℕ) (T : ℕ) (hS : S ⊆ Finset.range T)
    (k : ℕ) (hk : k < S.card) : enumerateTimes S k < T :=
  Finset.mem_range.mp (hS (enumerateTimes_mem S k hk))

lemma enumerateTimes_gap (S : Finset ℕ) (i t : ℕ) (hl : enumerateTimes S i < t)
    (hr : t < enumerateTimes S (i+1)) : t ∉ S := by
  intro ht
  rw [←enumerateTimes_image S] at ht
  obtain ⟨k,hk,hkt⟩ := Finset.mem_image.mp ht
  rw [←hkt] at hl hr
  have hik : i < k := (enumerateTimes_strictMono S).lt_iff_lt.mp hl
  have hki : k < i+1 := (enumerateTimes_strictMono S).lt_iff_lt.mp hr
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RequestedEpisodeCount

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma requested_episode_count (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule)
    (τ : ℕ → ℕ) (hτ : StrictMono τ) (R : Finset ℕ) (t id : ℕ)
    (hbefore : ∀ i ∈ R, τ i < t)
    (hfull : ∀ i ∈ R, episodeEvent (recursiveRun m g s α q ℓ schedule (τ i)) id ∧
      ((recursiveRun m g s α q ℓ schedule (τ i)).frames (recursiveRun m g s α q ℓ schedule (τ i)).top).needFull=true) :
    R.card ≤ (recursiveRun m g s α q ℓ schedule (t+1)).fullSolves id := by
  classical
  let S := (Finset.range (t+1)).filter (fun k => fullSolveEvent g (recursiveRun m g s α q ℓ schedule k) id)
  have hsub : R.image (fun i => τ i+1) ⊆ S := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by have := hbefore i hi; omega),?_⟩
    exact requested_episode_full_event m g s α q hq hs ℓ schedule (τ i) id (hfull i hi).1 (hfull i hi).2
  have hinj : Function.Injective (fun i => τ i+1) := by
    intro i j hij
    change τ i+1=τ j+1 at hij
    exact hτ.injective (Nat.add_right_cancel hij)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hc
  rw [fullSolves_run_events m g s α q ℓ schedule (t+1) id]
  exact hc

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodeSequenceCount

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

set_option maxHeartbeats 2000000 in
lemma episode_sequence_count (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (τ : ℕ → ℕ) (hτ : StrictMono τ) (T t id : ℕ)
    (hfull : ∀ i ≤ T, episodeEvent (recursiveRun m g s α q ℓ schedule (τ i)) id)
    (hbefore : τ T < t)
    (hno : ∀ i < T, ∀ k, τ i < k → k < τ (i+1) → ¬episodeEvent (recursiveRun m g s α q ℓ schedule k) id) :
    let st := recursiveRun m g s α q ℓ schedule (τ 0)
    let f := st.frames st.top
    let B := ⌈Real.log (4*f.N/f.block)/Real.log 2⌉₊
    T+1 ≤ (B+1)*((recursiveRun m g s α q ℓ schedule (t+1)).fullSolves id+1) := by
  classical
  intro st f B
  let run := recursiveRun m g s α q ℓ schedule
  let j := st.top
  let Q := fun i => episodeBudget (run (τ i)) j
  let L := f.q*f.block
  let E := (Finset.range T).filter (fun i => ((run (τ (i+1))).frames (run (τ (i+1))).top).needFull=true)
  have hparams := parameters_run m g s α q hq.1 ℓ schedule (τ 0) j le_rfl
  have hqf : 0 < f.q := hparams.1
  have hbf : (0 : ℝ) < f.block := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hparams.2.1
  have hNb : (f.block : ℝ) ≤ f.N := (scale_bounds_run m g s α q hq ℓ schedule (τ 0) j le_rfl).2.1
  have hN : 1 ≤ f.N := (scale_bounds_run m g s α q hq ℓ schedule (τ 0) j le_rfl).1
  have hspan := episode_event_span m g s α q ℓ schedule (τ 0) (τ T) id
    (hτ.monotone (Nat.zero_le _)) (hfull 0 (Nat.zero_le _)) (hfull T le_rfl)
  have hlevel (i : ℕ) (hi : i ≤ T) : (run (τ i)).top=j :=
    (episode_events_same_level m g s α q ℓ schedule (τ 0) (τ i) id (hτ.monotone (Nat.zero_le _))
      (hfull 0 (Nat.zero_le _)) (hfull i hi)).symm
  have hfixed (i : ℕ) (hi : i ≤ T) : frozenFrame ((run (τ i)).frames j)=frozenFrame f :=
    frozenFrame_interval m g s α q ℓ schedule (τ 0) (τ i) j (hτ.monotone (Nat.zero_le _))
      (fun k h0k hki => (hspan k h0k (hki.le.trans (hτ.monotone hi))).1)
  have hqeq (i : ℕ) (hi : i ≤ T) : ((run (τ i)).frames j).q=f.q := congrArg Prod.fst (hfixed i hi)
  have hNeq (i : ℕ) (hi : i ≤ T) : ((run (τ i)).frames j).N=f.N := congrArg (fun z => z.2.1) (hfixed i hi)
  have hbeq (i : ℕ) (hi : i ≤ T) : ((run (τ i)).frames j).block=f.block := congrArg (fun z => z.2.2.1) (hfixed i hi)
  have hupper (i : ℕ) (hi : i ≤ T) : Q i ≤ 4*f.q*f.N := by
    have hh := (episode_budget_bounds m g s α q hα hq hs ℓ schedule (τ i) id (hfull i hi)).2
    change episodeBudget (run (τ i)) (run (τ i)).top ≤ _ at hh
    rw [hlevel i hi,hqeq i hi,hNeq i hi] at hh
    change episodeBudget (run (τ i)) j ≤ _
    nlinarith
  have hL : 0 < L := mul_pos hqf hbf
  have hLU : L ≤ 4*f.q*f.N := by dsimp only [L]; nlinarith
  have hratio : (4*f.q*f.N)/L=4*f.N/f.block := by dsimp only [L]; field_simp
  have hbound (i : ℕ) (hi : i ≤ T) : massRank L (Q i) ≤ B := by
    have hh := massRank_bound L (4*f.q*f.N) (Q i) hL hLU (hupper i hi)
    rwa [hratio] at hh
  have hdrop (i : ℕ) (hi : i < T) (he : i ∉ E) : massRank L (Q (i+1)) < massRank L (Q i) := by
    have hneed : ((run (τ (i+1))).frames (run (τ (i+1))).top).needFull=false := by
      cases hn : ((run (τ (i+1))).frames (run (τ (i+1))).top).needFull
      · rfl
      · exact False.elim (he (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hn⟩))
    have hh := nonfull_episode_pair_halving m g s α q hq.1 ℓ schedule (τ i) (τ (i+1)) id
      (hτ (Nat.lt_succ_self i)) (hfull i hi.le) (hfull (i+1) (by omega)) (hno i hi) hneed
    have hh' : L < Q i ∧ Q (i+1) ≤ max (Q i/2) L := by
      simpa only [run,hlevel i hi.le,hqeq i hi.le,hbeq i hi.le] using hh
    exact massRank_clipped_halving L (Q i) (Q (i+1)) hL hh'.1 hh'.2
  have hc := bounded_nat_descent_count (fun i => massRank L (Q i)) E T B hbound hdrop
  have hEbound : E.card ≤ (run (t+1)).fullSolves id := by
    apply requested_episode_count m g s α q hq.1 hs ℓ schedule (fun i => τ (i+1))
      (hτ.comp (strictMono_nat_of_lt_succ (fun _ => by omega))) E t id
    · intro i hi
      have hiT := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      exact (hτ.monotone (show i+1 ≤ T by omega)).trans_lt hbefore
    · intro i hi
      have hiT := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      exact ⟨hfull (i+1) (by omega),(Finset.mem_filter.mp hi).2⟩
  have hi : (E ∩ Finset.range T).card ≤ E.card := Finset.card_le_card Finset.inter_subset_left
  have hh : T ≤ B+(B+1)*(run (t+1)).fullSolves id :=
    hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hi.trans hEbound)) _)
  nlinarith

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

-- Proof module: Solutions.EpisodePrefixCount

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma episode_prefix_count (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ) (info : CallInformation)
    (hinfo : (recursiveRun m g s α q ℓ schedule t).information id=some info) :
    let B := (⌈Real.log (4*info.scale/info.block)/Real.log 2⌉₊ : ℝ)
    ((recursiveRun m g s α q ℓ schedule t).episodes id : ℝ) ≤
      (B+1)*((recursiveRun m g s α q ℓ schedule (t+1)).fullSolves id+1) := by
  classical
  intro B
  let run := recursiveRun m g s α q ℓ schedule
  let S := (Finset.range t).filter (fun k => episodeEvent (run k) id)
  have hcount : (run t).episodes id=S.card := episodes_run_events m g s α q ℓ schedule t id
  by_cases hS : S.Nonempty
  · let τ := enumerateTimes S
    have hmono : StrictMono τ := enumerateTimes_strictMono S
    have hcard : 0 < S.card := Finset.card_pos.mpr hS
    let T := S.card-1
    have hfull (i : ℕ) (hi : i ≤ T) : episodeEvent (run (τ i)) id :=
      (Finset.mem_filter.mp (enumerateTimes_mem S i (by dsimp [T] at hi; omega))).2
    have hbefore : τ T < t := enumeration_before_bound S t (Finset.filter_subset _ _) T (by dsimp [T]; omega)
    have hno (i : ℕ) (hi : i < T) (k : ℕ) (hik : τ i < k) (hki : k < τ (i+1)) :
        ¬episodeEvent (run k) id := by
      intro he
      have hgap := enumerateTimes_gap S i k hik hki
      apply hgap
      apply Finset.mem_filter.mpr
      have hiT : τ (i+1) ≤ τ T := hmono.monotone (by omega)
      exact ⟨Finset.mem_range.mpr (by omega),he⟩
    have hh := episode_sequence_count m g s α q hα hq hs ℓ schedule τ hmono T t id hfull hbefore hno
    have hfirst := running_call_prefix_parameters m g s α q ℓ schedule (τ 0) t id info
      (enumeration_before_bound S t (Finset.filter_subset _ _) 0 hcard).le hinfo
      (hfull 0 (Nat.zero_le _)).1 (hfull 0 (Nat.zero_le _)).2.2.2
    have hN : ((run (τ 0)).frames (run (τ 0)).top).N=info.scale := hfirst.2.1
    have hb : ((run (τ 0)).frames (run (τ 0)).top).block=info.block := hfirst.2.2
    dsimp only [run] at hN hb
    dsimp only at hh
    rw [hN,hb] at hh
    have ht : T+1=S.card := by dsimp [T]; omega
    rw [ht] at hh
    rw [hcount]
    dsimp only [B]
    exact_mod_cast hh
  · have hz : S.card=0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hS)
    rw [hcount,hz,Nat.cast_zero]
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    positivity

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

-- Proof module: Solutions.SolverLogBound

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma queueLogConstant_positive : 0 < queueLogConstant := by
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h128 : 0 ≤ Real.log (128 : ℝ) := Real.log_nonneg (by norm_num)
  unfold queueLogConstant
  positivity

lemma primitiveLogConstant_bounds : 1 ≤ primitiveLogConstant ∧ queueLogConstant ≤ primitiveLogConstant ∧
    1+queueLogConstant*Real.log 2 ≤ primitiveLogConstant := by
  have hA := queueLogConstant_positive.le
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  refine ⟨?_,?_,?_⟩ <;> unfold primitiveLogConstant <;> nlinarith [mul_nonneg hA h2]

lemma solver_log_linear (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ : ℕ) (V : ℝ)
    (hV : 0 ≤ V) (hvol : V ≤ 1/rootThreshold ε ℓ) :
    1+Real.log (2+3*V) ≤ primitiveLogConstant*(2+Real.log (2/ε)+(ℓ : ℝ)) := by
  let q := rootThreshold ε ℓ
  let B := 2+Real.log (2/ε)+(ℓ : ℝ)
  let z : ℝ := 2+(3+2*(ℓ+1 : ℕ))/q
  have he : 0 < ε := hε.1
  have hq : 0 < q := by dsimp [q,rootThreshold,kappa]; positivity
  have hB : 1 ≤ B := by
    have hL : 0 ≤ Real.log (2/ε) := Real.log_nonneg ((le_div_iff₀ he).mpr (by linarith [hε.2]))
    have hl : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    dsimp only [B]
    linarith
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hP : (3 : ℝ) ≤ (3+2*(ℓ+1 : ℕ) : ℝ) := by
    have hl : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    push_cast
    linarith
  have hupper : 2+3*V ≤ z := by
    calc
      _ ≤ 2+3*(1/q) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hvol (by norm_num))
      _ = 2+3/q := by ring
      _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right hP hq.le)
  have hlog := Real.log_le_log (show 0 < 2+3*V by positivity) hupper
  have hqueue := queue_log_overhead_bound ε hε ℓ ℓ le_rfl
  change 1+Real.logb 2 z ≤ queueLogConstant*B at hqueue
  rw [Real.logb] at hqueue
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hz : Real.log z ≤ queueLogConstant*Real.log 2*B := by
    have hh : Real.log z/Real.log 2 ≤ queueLogConstant*B-1 := by linarith
    have hm := (div_le_iff₀ h2).mp hh
    nlinarith
  calc
    _ ≤ B+queueLogConstant*Real.log 2*B := add_le_add hB (hlog.trans hz)
    _ = (1+queueLogConstant*Real.log 2)*B := by ring
    _ ≤ primitiveLogConstant*B := mul_le_mul_of_nonneg_right primitiveLogConstant_bounds.2.2 hB0

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CountLogBounds

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma count_log_bounds (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ : ℕ) (N b : ℝ)
    (hN : 1 ≤ N) (hb : 1 ≤ b) (hbN : b ≤ N) (hupper : N ≤ 1/rootThreshold ε ℓ) :
    let X := 2+Real.log (2/ε)+(ℓ : ℝ)
    let A := primitiveLogConstant/Real.log 2
    (⌈Real.log (4*N/b)/Real.log 2⌉₊ : ℝ)+1 ≤ (2*A+2)*X ∧
      Real.log (2/rootThreshold ε ℓ)/Real.log 2 ≤ A*X ∧ (kappa ℓ 0 : ℝ) ≤ 2*X := by
  intro X A
  let q := rootThreshold ε ℓ
  let z := 2+3*(1/q)
  have he : 0 < ε := hε.1
  have hq : 0 < q := by dsimp [q,rootThreshold,kappa]; positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ Real.log (2/ε) := Real.log_nonneg ((le_div_iff₀ he).mpr (by linarith [hε.2]))
  have hX : 1 ≤ X := by
    have hl : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    dsimp only [X]
    linarith
  have hN0 : (1 : ℝ) ≤ 1/q := hN.trans hupper
  have hz : 0 < z := by dsimp [z]; positivity
  have hlinear := solver_log_linear ε hε ℓ (1/q) (by positivity) le_rfl
  have hlogz : Real.log z ≤ primitiveLogConstant*X := by
    change 1+Real.log z ≤ primitiveLogConstant*X at hlinear
    linarith
  have hratio : 4*N/b ≤ z^2 := by
    have hdiv : N/b ≤ N := div_le_self (by linarith) hb
    have hh : N/b ≤ 1/q := hdiv.trans hupper
    rw [mul_div_assoc]
    dsimp only [z]
    nlinarith [sq_nonneg (1/q)]
  have hratio1 : 1 ≤ 4*N/b := by
    apply (le_div_iff₀ (by linarith : 0 < b)).mpr
    linarith
  have hlogratio : Real.log (4*N/b)/Real.log 2 ≤ 2*A*X := by
    have hh := Real.log_le_log (by positivity : 0 < 4*N/b) hratio
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    apply (div_le_iff₀ hl2).mpr
    dsimp only [A]
    have heq : 2*(primitiveLogConstant/Real.log 2)*X*Real.log 2=2*primitiveLogConstant*X := by field_simp
    rw [heq]
    linarith
  have hceil := Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hratio1) hl2.le)
  have hsecond : Real.log (2/q)/Real.log 2 ≤ A*X := by
    have hh := Real.log_le_log (by positivity : 0 < 2/q) (show 2/q ≤ z by
      have heq : 2/q=2*(1/q) := by ring
      rw [heq]
      dsimp only [z]
      linarith)
    calc
      _ ≤ (primitiveLogConstant*X)/Real.log 2 := div_le_div_of_nonneg_right (hh.trans hlogz) hl2.le
      _ = _ := by dsimp only [A]; ring
  have hA : 0 ≤ A := div_nonneg (zero_le_one.trans primitiveLogConstant_bounds.1) hl2.le
  refine ⟨?_,hsecond,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hX (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  · simp only [kappa,Nat.sub_zero,Nat.cast_add,Nat.cast_ofNat]
    dsimp only [X]
    have hl : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    linarith

end
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

-- Proof module: Solutions.UniformEpisodeCount

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma uniform_episode_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n)
      (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule),
      (0 < α ∧ α ≤ 1/2) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
      ∀ (t id : ℕ) (info : CallInformation),
        (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).information id=some info →
          ((recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).episodes id : ℝ) ≤
            overhead C 4 ε ℓ*info.scale/info.block := by
  obtain ⟨Cf,hCf,hfull⟩ := uniform_full_solve_count
  let A := primitiveLogConstant/Real.log 2
  let D := 2*A+2
  let C := D*(Cf+1)
  have hA : 0 ≤ A := div_nonneg (zero_le_one.trans primitiveLogConstant_bounds.1)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro m n g s α ε ℓ schedule hα hε hs t id info hinfo
  let X := 2+Real.log (2/ε)+(ℓ : ℝ)
  let r := info.scale/info.block
  have hq := root_threshold_unit ε hε ℓ
  have ha : 0 < α ∧ α < 1 := ⟨hα.1,by linarith [hα.2]⟩
  have hlegal := information_legal_run m g s α (rootThreshold ε ℓ) hq ℓ schedule t id info hinfo
  have hb : (0 : ℝ) < info.block := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hlegal.2.2.1
  have hr : 1 ≤ r := (le_div_iff₀ hb).mpr (by simpa using hlegal.2.2.2.1)
  have hlogs := count_log_bounds ε hε ℓ info.scale info.block hlegal.2.1
    (by exact_mod_cast hlegal.2.2.1) hlegal.2.2.2.1 hlegal.2.2.2.2
  have hprefix := episode_prefix_count m g s α (rootThreshold ε ℓ) ha hq hs ℓ schedule t id info hinfo
  have hfuture := information_run_persistent m g s α (rootThreshold ε ℓ) ℓ schedule t (t+1) id info (Nat.le_succ t) hinfo
  have hF := hfull m n g s α ε ℓ schedule hα hε hs (t+1) id info hfuture
  have hX : 1 ≤ X := by
    have hl := Real.log_nonneg ((le_div_iff₀ hε.1).mpr (by linarith [hε.2]) : 1 ≤ 2/ε)
    have hel : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    dsimp only [X]
    linarith
  have hbase : 1 ≤ X^3*r := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hX) hr
  have hF1 : ((recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule (t+1)).fullSolves id : ℝ)+1 ≤
      (Cf+1)*X^3*r := by
    have heq : overhead Cf 3 ε ℓ*info.scale/info.block=Cf*X^3*r := by dsimp only [overhead,X,r]; ring
    rw [heq] at hF
    nlinarith
  have hlog : (⌈Real.log (4*info.scale/info.block)/Real.log 2⌉₊ : ℝ)+1 ≤ D*X := hlogs.1
  calc
    _ ≤ _ := hprefix
    _ ≤ (D*X)*((Cf+1)*X^3*r) := by gcongr
    _ = _ := by dsimp only [overhead,C,D,X,r]; ring

end
end NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n)
      (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule),
      (0 < α ∧ α ≤ 1/2) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
      ∀ (t id : ℕ) (info : CallInformation),
        (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).information id=some info →
          ((recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).episodes id : ℝ) ≤
            overhead C 4 ε ℓ*info.scale/info.block := by
  exact uniform_episode_count
