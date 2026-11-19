-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_work_recurrences
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:29:16.931124+00:00
-- url     : https://prove2.me/submissions/2e96d3d4-074f-4f67-8605-b671f661c8db

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_episode_count
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_stack_scales
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_call_metadata
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_event_count
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_call_history
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_own_work_bound
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_finite_prefix_counts

set_option linter.all false
set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

abbrev depth_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_control_parameters m n g s α q ℓ schedule t).1

abbrev parameters_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_control_parameters m n g s α q ℓ schedule t).2.2.2 hq

abbrev uniform_episode_count :=
  recursive_episode_count

abbrev scale_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ) (hq : 0 < q)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_stack_scales m n g s α q ℓ schedule t).2.2 hq

abbrev open_frame_information_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_call_metadata m n g s α q ℓ schedule t).2.2.2.2.1

abbrev control_prefix_count (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) :=
  recursive_control_event_count m n g s α q hq hs ℓ schedule T id

abbrev information_run_persistent (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (info : CallInformation) (hab : a ≤ b)
    (hinfo : (recursiveRun m g s α q ℓ schedule a).information id=some info) :=
  (recursive_call_history m n g s α q ℓ schedule).1 a b id info hab hinfo

abbrev uniform_own_work_bound (m : SolveModel) :=
  recursive_own_work_bound m

lemma created_call_eventually_closed (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α ≤ 1/2) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a id : ℕ) (info : CallInformation)
    (hi : (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule a).information id=some info) :
    ∃ t, a ≤ t ∧ id ∈ (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).closed := by
  obtain ⟨C,hC,H⟩ := recursive_finite_prefix_counts
  exact (H m ε ℓ schedule hε.1 hε.2 n g s α hα.1 hα.2 hs a id info hi).2.2.2.2

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

-- Proof module: Solutions.StepDebit

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}


lemma stepDebit_producer_le_top (m : SolveModel) (g : InputGraph n) (α : ℝ) (ℓ : ℕ)
    (st : RecursiveState n) : (stepDebit m g α ℓ st).1 ≤ st.top := by
  have hpush : ∀ t v, pendingPush st=some (t,v) → t ≤ st.top := fun t v hp => (pending_push_member st t v hp).1
  cases hp : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;> simp [stepDebit,hpc,hp] <;> split_ifs <;> simp_all
  | some p =>
    obtain ⟨t,v⟩ := p
    have ht := hpush t v hp
    cases hpc : (st.frames st.top).pc <;> simp [stepDebit,hpc,hp] <;> split_ifs <;> simp_all

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

-- Proof module: Solutions.StepWork

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma work_changeFrame (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).work=st.work := rfl
@[simp] lemma work_PC (st : RecursiveState n) (pc : NormalizePC) : (changePC st pc).work=st.work := rfl
@[simp] lemma work_debit (st : RecursiveState n) (j : ℕ) (c : ℝ≥0∞) : (debit st j c).work=st.work+c := rfl
@[simp] lemma work_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) : (refreshKeys g st T).work=st.work := rfl
@[simp] lemma work_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) : (jointUpdate g α st h).work=st.work := rfl
@[simp] lemma work_finish (st : RecursiveState n) : (finishEpisode st).work=st.work := rfl
@[simp] lemma work_admit (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) : (admitStage g st t v).work=st.work := by
  unfold admitStage
  dsimp only
  split_ifs <;> rfl
@[simp] lemma work_raw (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) (δ : ℝ) :
    (rawExterior g α st t v δ).work=st.work := rfl
@[simp] lemma work_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).work=if P then a.work else b.work := by split <;> rfl
@[simp] lemma keyCost_debit (st : RecursiveState n) (j : ℕ) (c : ℝ≥0∞) : keyCost (debit st j c)=keyCost st := rfl

@[simp] lemma work_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) :
    (completeComponent m g s α st).work=st.work+jointCost m g st (st.frames 0).active+((st.frames 0).active.card+1 : ℕ) := by
  simp [completeComponent,debit,add_assoc]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StepAccountHelpers

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

@[simp] lemma account_charged_metadata (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).charged=st.charged := rfl
@[simp] lemma account_charged_PC (st : RecursiveState n) (pc : NormalizePC) : (changePC st pc).charged=st.charged := rfl
@[simp] lemma account_charged_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) : (refreshKeys g st T).charged=st.charged := rfl
@[simp] lemma account_charged_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) : (jointUpdate g α st h).charged=st.charged := rfl
@[simp] lemma account_charged_finish (st : RecursiveState n) : (finishEpisode st).charged=st.charged := rfl
@[simp] lemma account_charged_raw (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) (δ : ℝ) : (rawExterior g α st t v δ).charged=st.charged := rfl
@[simp] lemma account_charged_admit (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) : (admitStage g st t v).charged=st.charged := by unfold admitStage; dsimp only; split_ifs <;> rfl
@[simp] lemma account_charged_ite (P : Prop) [Decidable P] (a b : RecursiveState n) : (if P then a else b).charged=if P then a.charged else b.charged := by split <;> rfl
@[simp] lemma account_charged_debit (st : RecursiveState n) (j id : ℕ) (c : ℝ≥0∞) :
    (debit st j c).charged id=st.charged id+if ∃ i ≤ j, (st.frames i).id=id then c else 0 := rfl

@[simp] lemma account_id_metadata (st : RecursiveState n) (k j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hf : (f (st.frames k)).id=(st.frames k).id) :
    ((changeFrame st k f).frames j).id=(st.frames j).id := observe_changeFrame (fun f => f.id) st k f hf j
@[simp] lemma account_id_PC (st : RecursiveState n) (pc : NormalizePC) (j : ℕ) :
    ((changePC st pc).frames j).id=(st.frames j).id := account_id_metadata st st.top j _ rfl
@[simp] lemma account_id_debit (st : RecursiveState n) (k j : ℕ) (c : ℝ≥0∞) :
    ((debit st k c).frames j).id=(st.frames j).id := rfl
@[simp] lemma account_id_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (j : ℕ) :
    ((refreshKeys g st T).frames j).id=(st.frames j).id := by by_cases hj : j ≤ st.top <;> simp [refreshKeys,hj]
@[simp] lemma account_id_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) (j : ℕ) :
    ((jointUpdate g α st h).frames j).id=(st.frames j).id := by by_cases hj : j ≤ st.top <;> simp [jointUpdate,hj]
@[simp] lemma account_id_finish (st : RecursiveState n) (j : ℕ) :
    ((finishEpisode st).frames j).id=(st.frames j).id := by unfold finishEpisode; exact account_id_metadata _ st.top j _ rfl
@[simp] lemma account_id_raw (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t j : ℕ) (v : Fin n) (δ : ℝ) :
    ((rawExterior g α st t v δ).frames j).id=(st.frames j).id := by by_cases hj : j ≤ st.top <;> simp [rawExterior,hj]
@[simp] lemma account_id_admit (g : InputGraph n) (st : RecursiveState n) (t j : ℕ) (v : Fin n) :
    ((admitStage g st t v).frames j).id=(st.frames j).id := by
  unfold admitStage
  dsimp only
  split_ifs <;> simp only [account_id_metadata]
@[simp] lemma account_id_ite (P : Prop) [Decidable P] (a b : RecursiveState n) (j : ℕ) :
    ((if P then a else b).frames j).id=if P then (a.frames j).id else (b.frames j).id := by split <;> rfl

lemma account_charged_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t id : ℕ) (v : Fin n) :
    (exteriorPush g α st t v).charged id=st.charged id+
      if ∃ i ≤ t, (st.frames i).id=id then
        (32*(st.top+1)*((g.neighbors v).length+1)*keyCost (exteriorPush g α st t v) : ℕ) else 0 := by
  classical
  rw [exterior_stages]
  simp only [account_charged_debit,account_charged_refresh,account_charged_ite,account_charged_admit,
    account_charged_raw,ite_self,account_id_refresh,account_id_ite,account_id_admit,account_id_raw,keyCost_debit]
  by_cases he : ∃ i ≤ t, (st.frames i).id=id <;> simp only [he,ite_true,ite_false,Nat.cast_zero]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StepAccount

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma account_charged_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (id : ℕ) :
    (completeComponent m g s α st).charged id=st.charged id+
      if (st.frames 0).id=id then jointCost m g st (st.frames 0).active+((st.frames 0).active.card+1 : ℕ) else 0 := by
  simp [completeComponent,debit]

lemma account_charged_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (id : ℕ) :
    (endCall g α st).charged id=st.charged id+
      if st.top=0 ∧ (st.frames 0).id=id then (((8*(st.frames 0).active.card+1 : ℕ) : ℝ≥0∞)) else 0 := by
  unfold endCall
  dsimp only
  split
  · rename_i hz
    simp [debit,hz]
  · rename_i hn
    simp [hn]

set_option maxHeartbeats 2500000 in
lemma recursiveStep_charged_debit (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (id : ℕ) :
    (recursiveStep m g s α ℓ schedule st).charged id=st.charged id+
      if ∃ i ≤ (stepDebit m g α ℓ st).1, (st.frames i).id=id then (stepDebit m g α ℓ st).2 else 0 := by
  cases hp : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,stepDebit,hpc,hp,account_charged_complete,account_charged_end,account_charged_exterior] <;>
      (try split_ifs) <;>
      simp_all [account_charged_complete,account_charged_end,account_charged_exterior,add_assoc,Nat.cast_add,Nat.cast_mul] <;>
      (try split_ifs) <;> (try simp_all [debit]) <;> (first | (solve | grind) | ring)
  | some p =>
    obtain ⟨t,v⟩ := p
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,stepDebit,hpc,hp,account_charged_complete,account_charged_end,account_charged_exterior] <;>
      (try split_ifs) <;>
      simp_all [account_charged_complete,account_charged_end,account_charged_exterior,add_assoc,Nat.cast_add,Nat.cast_mul] <;>
      (try split_ifs) <;> (try simp_all [debit]) <;> (first | (solve | grind) | ring)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ClosedCallWork

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma charged_run_monotone (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (id : ℕ) :
    Monotone (fun t => (recursiveRun m g s α q ℓ schedule t).charged id) := by
  apply monotone_nat_of_le_succ
  intro t
  have hh := recursiveStep_charged_debit m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule t) id
  have hs : (recursiveRun m g s α q ℓ schedule (t+1)).charged id=
      (recursiveStep m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule t)).charged id := by
    simp only [recursiveRun,Function.iterate_succ_apply']
  rw [hs,hh]
  exact le_add_of_nonneg_right (by positivity)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AccountAllocation

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma account_charge_telescope (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) :
    let run := recursiveRun m g s α q ℓ schedule
    (run T).charged id=(run 0).charged id+∑ k ∈ range T, accountCharge m g α ℓ (run k) id := by
  intro run
  induction T with
  | zero => simp
  | succ T ih =>
    have hstep : run (T+1)=recursiveStep m g s α ℓ schedule (run T) := by
      simp only [run,recursiveRun,Function.iterate_succ_apply']
    rw [hstep,recursiveStep_charged_debit,ih,Finset.sum_range_succ]
    simp only [accountCharge,add_assoc]

lemma account_charges_le_charged (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) :
    (∑ k ∈ range T, accountCharge m g α ℓ (recursiveRun m g s α q ℓ schedule k) id) ≤
      (recursiveRun m g s α q ℓ schedule T).charged id := by
  rw [account_charge_telescope]
  exact le_add_of_nonneg_left (by positivity)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CallIDs

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma call_ids_transport (st u : RecursiveState n) (hi : CallIDInvariant st)
    (ht : u.top ≤ st.top) (hn : u.nextId = st.nextId)
    (hf : ∀ i ≤ u.top, (u.frames i).id = (st.frames i).id) : CallIDInvariant u := by
  refine ⟨(hf 0 (Nat.zero_le _)).trans hi.1,by simpa [hn] using hi.2.1,?_⟩
  intro i hh hn0
  rw [hf i hh]
  exact hi.2.2 i (hh.trans ht) hn0

lemma call_ids_metadata (st : RecursiveState n) (hi : CallIDInvariant st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) (hid : (f (st.frames j)).id = (st.frames j).id) :
    CallIDInvariant (changeFrame st j f) :=
  call_ids_transport st _ hi le_rfl rfl (fun i _ => observe_changeFrame (fun f => f.id) st j f hid i)

lemma call_ids_PC (st : RecursiveState n) (pc : NormalizePC) (hi : CallIDInvariant st) :
    CallIDInvariant (changePC st pc) := call_ids_metadata st hi st.top _ rfl

lemma call_ids_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hi : CallIDInvariant st) : CallIDInvariant (exteriorPush g α st t v) := by
  refine call_ids_transport st (exteriorPush g α st t v) hi (by simp) ?_ ?_
  · simp [exteriorPush,changeFrame,refreshKeys,debit] <;> (try split_ifs) <;> rfl
  · intro i _
    exact congrArg (fun z => z.2.2.2.2.2.2) (exterior_parameters g α st t v i)

lemma call_ids_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ)
    (hi : CallIDInvariant st) : CallIDInvariant (jointUpdate g α st h) := by
  refine call_ids_transport st (jointUpdate g α st h) hi le_rfl rfl ?_
  intro i _
  by_cases he : i ≤ st.top <;> simp [jointUpdate,he]

lemma call_ids_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : CallIDInvariant st) : CallIDInvariant (refreshKeys g st T) := by
  refine call_ids_transport st (refreshKeys g st T) hi le_rfl rfl ?_
  intro i _
  by_cases he : i ≤ st.top <;> simp [refreshKeys,he]

lemma call_ids_finish (st : RecursiveState n) (hi : CallIDInvariant st) :
    CallIDInvariant (finishEpisode st) := by
  unfold finishEpisode
  apply call_ids_metadata
  · exact hi
  · rfl

lemma call_ids_new (st : RecursiveState n) (c : NormalizeFrame n) (hi : CallIDInvariant st)
    (hid : c.id = st.nextId) : CallIDInvariant
      {st with top := st.top+1,nextId := st.nextId+1,frames := Function.update st.frames (st.top+1) c} := by
  refine ⟨?_,by dsimp; omega,?_⟩
  · have hne : 0 ≠ st.top+1 := by omega
    simpa [hne] using hi.1
  · intro i hh hn
    change i ≤ st.top+1 at hh
    by_cases he : i = st.top+1
    · subst i
      simpa [hid] using hi.2.1
    · simpa [he] using hi.2.2 i (by omega) hn

lemma call_ids_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hi : CallIDInvariant st) :
    CallIDInvariant (endCall g α st) := by
  unfold endCall
  dsimp only
  split
  · exact hi
  · exact call_ids_transport st _ hi (Nat.sub_le _ _) rfl (fun _ _ => rfl)

lemma call_ids_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    CallIDInvariant (recursiveInit g s q ℓ schedule) := by
  refine ⟨?_,by simp [recursiveInit],?_⟩
  · simp [recursiveInit,freshFrame,emptyFrame]
  · intro i hi hn
    change i ≤ 0 at hi
    omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CallIDStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma call_ids_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : CallIDInvariant st) (pc : NormalizePC) :
    CallIDInvariant (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact call_ids_PC _ pc hi
  · cases hp : pendingPush st with
    | none => exact call_ids_PC _ pc hi
    | some p => obtain ⟨t,v⟩ := p; exact call_ids_exterior g α st t v hi

set_option maxHeartbeats 1000000 in
lemma call_ids_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hi : CallIDInvariant st) : CallIDInvariant (recursiveStep m g s α ℓ schedule st) := by
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
    · exact call_ids_PC _ _ hi
    · split
      · exact call_ids_drain g α st hi _
      · split <;> exact call_ids_PC _ _ hi
  | beginEpisode =>
    simp only [hpc]
    apply call_ids_metadata _ _ st.top _ rfl
    exact hi
  | fullSolve =>
    simp only [hpc]
    split
    · exact call_ids_PC _ _ hi
    · split
      · apply call_ids_PC _ _
        unfold CallIDInvariant
        exact call_ids_refresh g _ (touchedBy g (st.frames st.top).active)
          (call_ids_joint g α st _ hi)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact call_ids_PC _ _ hi
    · split
      · exact call_ids_PC _ _ hi
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : CallIDInvariant up := call_ids_metadata u hi st.top _ rfl
        exact call_ids_new up c hup (by simp [c,freshFrame,up,u,changeFrame,debit])
  | leafDrain =>
    simp only [hpc]
    split
    · exact call_ids_PC _ _ hi
    · split
      · cases hp : pendingPush st with
        | none => exact call_ids_PC _ _ hi
        | some p => obtain ⟨t,v⟩ := p; exact call_ids_exterior g α st t v hi
      · split
        · exact call_ids_PC _ _ hi
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : CallIDInvariant u := call_ids_metadata st hi st.top _ rfl
            unfold CallIDInvariant
            exact call_ids_refresh g _ (touchedBy g C) (call_ids_joint g α u _ hu)
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact call_ids_PC _ _ (call_ids_finish _ hi)
    · split
      · exact call_ids_PC _ _ (call_ids_finish _ hi)
      · exact call_ids_drain g α st hi _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact call_ids_PC _ _ (call_ids_finish _ hi)
    · split
      · exact call_ids_PC _ _ (call_ids_finish _ hi)
      · apply call_ids_metadata _ _ st.top _ rfl
        exact call_ids_finish _ hi
  | restartDrain =>
    simp only [hpc]
    split
    · exact call_ids_PC _ _ hi
    · split
      · exact call_ids_drain g α st hi _
      · exact call_ids_metadata (debit st st.top 1) hi st.top
          (fun fc => {fc with needFull := true, pc := .beginEpisode}) rfl
  | normal =>
    simp only [hpc]
    exact call_ids_end g α _ hi
  | interrupted =>
    simp only [hpc]
    exact call_ids_end g α _ hi

lemma call_ids_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    CallIDInvariant (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using call_ids_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using call_ids_step m g s α ℓ schedule _ ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootInformation

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

@[simp] lemma information_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    (exteriorPush g α st t v).information = st.information := by
  simp [exteriorPush,changeFrame,refreshKeys,debit] <;> (try split_ifs) <;> rfl

@[simp] lemma information_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).information = if P then a.information else b.information := by split <;> rfl

set_option maxHeartbeats 1000000 in
lemma root_information_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hi : CallIDInvariant st) :
    (recursiveStep m g s α ℓ schedule st).information 0 = st.information 0 := by
  classical
  have hn : 0 ≠ st.nextId := by have := hi.2.1; omega
  cases hp : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hp,freshFrame,hn] <;> (try split_ifs) <;> simp_all
  | some p =>
    obtain ⟨t,v⟩ := p
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hp,freshFrame,hn] <;> (try split_ifs) <;> simp_all

lemma root_information_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    (recursiveRun m g s α q ℓ schedule t).information 0 =
      some ⟨0,1/q,blockScale schedule ℓ 0 (1/q)⟩ := by
  induction t with
  | zero => simp [recursiveRun,recursiveInit,freshFrame]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      (root_information_step m g s α ℓ schedule _ (call_ids_run m g s α q ℓ schedule t)).trans ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ChildSnapshots

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 1500000 in
lemma top_step_upper (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) :
    (recursiveStep m g s α ℓ schedule st).top ≤ st.top+1 := by
  cases hp : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;> simp [recursiveStep,hpc,hp] <;>
      (try split_ifs) <;> simp_all [debit] <;> omega
  | some p =>
    obtain ⟨i,v⟩ := p
    cases hpc : (st.frames st.top).pc <;> simp [recursiveStep,hpc,hp] <;>
      (try split_ifs) <;> simp_all [debit] <;> omega

lemma child_snapshot_new (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (j id child : ℕ)
    (hn : child ∈ childSnapshot (recursiveStep m g s α ℓ schedule st) j id)
    (ho : child ∉ childSnapshot st j id) :
    st.top=j ∧ controlEvent g st id := by
  have hnew : j < (recursiveStep m g s α ℓ schedule st).top ∧
      ((recursiveStep m g s α ℓ schedule st).frames j).id=id ∧
      child=((recursiveStep m g s α ℓ schedule st).frames (j+1)).id := by
    unfold childSnapshot at hn
    split_ifs at hn with hh
    · exact ⟨hh.1,hh.2,Finset.mem_singleton.mp hn⟩
    · simp at hn
  have hupper := top_step_upper m g s α ℓ schedule st
  have hj : j ≤ st.top := by omega
  have hfid : ((recursiveStep m g s α ℓ schedule st).frames j).id=(st.frames j).id :=
    congrArg (fun f => f.2.2.2) (frozenFrame_step m g s α ℓ schedule st j hj)
  have hid : (st.frames j).id=id := hfid.symm.trans hnew.2.1
  have htop : st.top=j := by
    by_contra hne
    have hlt : j < st.top := by omega
    have hchild : ((recursiveStep m g s α ℓ schedule st).frames (j+1)).id=(st.frames (j+1)).id :=
      congrArg (fun f => f.2.2.2) (frozenFrame_step m g s α ℓ schedule st (j+1) (by omega))
    apply ho
    rw [childSnapshot,if_pos (show j < st.top ∧ (st.frames j).id=id from ⟨hlt,hid⟩),Finset.mem_singleton]
    exact hnew.2.2.trans hchild
  have hg : st.top < (recursiveStep m g s α ℓ schedule st).top := by omega
  obtain ⟨hd,hcomp,hpc,hno,hdepth⟩ := growing_step_guards m g s α ℓ schedule st hg
  refine ⟨htop,hd,?_,?_,?_⟩
  · simp [stepProduction,hd,hcomp,hpc]
  · intro hh
    have hhpc := hh.2.2.1
    rw [hpc] at hhpc
    cases hhpc
  · simpa only [if_neg hcomp,htop] using hid

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SeenChildren

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma child_snapshot_seen (run : ℕ → RecursiveState n) (j id k T : ℕ) (hkT : k ≤ T) :
    childSnapshot (run k) j id ⊆ seenChildren run j id T := by
  induction T with
  | zero =>
    have hk : k=0 := by omega
    subst k
    exact subset_refl _
  | succ T ih =>
    by_cases he : k=T+1
    · rw [he,seenChildren]
      exact Finset.subset_union_right
    · exact Finset.Subset.trans (ih (by omega)) Finset.subset_union_left

lemma seen_children_mem (run : ℕ → RecursiveState n) (j id T child : ℕ) :
    child ∈ seenChildren run j id T ↔ ∃ k, k ≤ T ∧ child ∈ childSnapshot (run k) j id := by
  induction T with
  | zero => simp only [seenChildren,Nat.le_zero]; simp
  | succ T ih =>
    rw [seenChildren,Finset.mem_union,ih]
    constructor
    · rintro (⟨k,hk,hm⟩|hm)
      · exact ⟨k,by omega,hm⟩
      · exact ⟨T+1,le_rfl,hm⟩
    · rintro ⟨k,hk,hm⟩
      by_cases he : k=T+1
      · exact Or.inr (he ▸ hm)
      · exact Or.inl ⟨k,by omega,hm⟩

lemma seen_children_count (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (T j id : ℕ) :
    let run := recursiveRun m g s α q ℓ schedule
    (seenChildren run j id T).card ≤
      ((range T).filter (fun k => controlEvent g (run k) id)).card := by
  intro run
  induction T with
  | zero => simp [seenChildren,childSnapshot,run,recursiveRun,recursiveInit]
  | succ T ih =>
    have hstep : run (T+1)=recursiveStep m g s α ℓ schedule (run T) := by
      simp only [run,recursiveRun,Function.iterate_succ_apply']
    rw [seenChildren,Finset.range_add_one,Finset.filter_insert]
    by_cases hsub : childSnapshot (run (T+1)) j id ⊆ seenChildren run j id T
    · have heq := Finset.union_eq_left.mpr hsub
      rw [heq]
      exact ih.trans (Finset.card_le_card (by split_ifs <;> simp))
    · have hex : ∃ child, child ∈ childSnapshot (run (T+1)) j id ∧ child ∉ seenChildren run j id T := by
        exact Finset.not_subset.mp hsub
      obtain ⟨child,hn,ho⟩ := hex
      have hold : child ∉ childSnapshot (run T) j id := fun hm => ho (child_snapshot_seen run j id T T le_rfl hm)
      have hc := (child_snapshot_new m g s α ℓ schedule (run T) j id child (hstep ▸ hn) hold).2
      rw [if_pos hc,Finset.card_insert_of_notMem (by simp)]
      have hsnap : (childSnapshot (run (T+1)) j id).card ≤ 1 := by
        unfold childSnapshot
        split_ifs <;> simp
      exact (Finset.card_union_le _ _).trans (by omega)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SeenChildrenInformation

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma seen_child_information (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (T id child : ℕ) (info : CallInformation)
    (hi : (recursiveRun m g s α q ℓ schedule T).information id=some info)
    (hc : child ∈ seenChildren (recursiveRun m g s α q ℓ schedule) info.level id T) :
    ∃ ci : CallInformation, (recursiveRun m g s α q ℓ schedule T).information child=some ci ∧
      ci.level=info.level+1 ∧ ci.scale=info.block := by
  classical
  let run := recursiveRun m g s α q ℓ schedule
  obtain ⟨k,hk,hmem⟩ := (seen_children_mem run info.level id T child).mp hc
  have hsnap : info.level < (run k).top ∧ ((run k).frames info.level).id=id ∧
      child=((run k).frames (info.level+1)).id := by
    unfold childSnapshot at hmem
    split_ifs at hmem with hh
    · exact ⟨hh.1,hh.2,Finset.mem_singleton.mp hmem⟩
    · simp at hmem
  have hparent := open_frame_prefix_parameters m g s α q ℓ schedule k T info.level id info hk hi hsnap.1.le hsnap.2.1
  let ci : CallInformation := ⟨info.level+1,((run k).frames (info.level+1)).N,((run k).frames (info.level+1)).block⟩
  have hci : (run k).information child=some ci := by
    rw [hsnap.2.2]
    have hchildle : info.level+1 ≤ (run k).top := by omega
    exact open_frame_information_run m g s α q ℓ schedule k (info.level+1) hchildle
  refine ⟨ci,information_run_persistent m g s α q ℓ schedule k T child ci hk hci,rfl,?_⟩
  have hscale := (scale_run m g s α q hq ℓ schedule k).2 info.level hsnap.1
  change ((run k).frames (info.level+1)).N=info.block
  exact hscale.trans (congrArg Nat.cast hparent.2.2)

lemma uniform_seen_children_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
      (ℓ : ℕ) (schedule : BlockSchedule), (0 < α ∧ α ≤ 1/2) → (0 < ε ∧ ε ≤ 1) →
      0 < g.graph.degree s → ∀ (T id : ℕ) (info : CallInformation),
      let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
      (run T).information id=some info →
        ((seenChildren run info.level id T).card : ℝ) ≤ overhead C 4 ε ℓ*info.scale/info.block := by
  obtain ⟨Ce,hCe,hEp⟩ := uniform_episode_count
  refine ⟨9+7*Ce,by positivity,?_⟩
  intro m n g s α ε ℓ schedule hα hε hs T id info run hi
  have hq := root_threshold_unit ε hε ℓ
  have hlegal := information_legal_run m g s α (rootThreshold ε ℓ) hq ℓ schedule T id info hi
  have hN := hlegal.2.1
  have hb0 : 0 < (info.block : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hlegal.2.2.1
  have hbN := hlegal.2.2.2.1
  have he := hEp m n g s α ε ℓ schedule hα hε hs T id info hi
  have hc := control_prefix_count m g s α (rootThreshold ε ℓ) hq.1 hs ℓ schedule T id
  have hsnap : ((seenChildren run info.level id T).card : ℝ) ≤
      (((range T).filter (fun k => controlEvent g (run k) id)).card : ℝ) := by
    exact_mod_cast seen_children_count m g s α (rootThreshold ε ℓ) ℓ schedule T info.level id
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

lemma leaf_children_empty (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) (info : CallInformation)
    (hi : (recursiveRun m g s α q ℓ schedule T).information id=some info) (he : info.level=ℓ) :
    seenChildren (recursiveRun m g s α q ℓ schedule) info.level id T=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro child hc
  obtain ⟨k,hk,hmem⟩ := (seen_children_mem _ info.level id T child).mp hc
  have hlt : info.level < (recursiveRun m g s α q ℓ schedule k).top := by
    unfold childSnapshot at hmem
    split_ifs at hmem with hh
    · exact hh.1
    · simp at hmem
  have hbound := depth_run m g s α q ℓ schedule k
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OverheadProducts

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma overhead_sum (A B ε : ℝ) (a ℓ : ℕ) :
    overhead A a ε ℓ+overhead B a ε ℓ=overhead (A+B) a ε ℓ := by
  unfold overhead
  ring

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.InitialCharge

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma initial_call_charge_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1) (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) (info : CallInformation)
    (hi : (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule T).information id=some info) :
    (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule 0).charged id ≤
      ENNReal.ofReal (overhead 32 1 ε ℓ*info.scale) := by
  have hq := root_threshold_unit ε hε ℓ
  have hN : 1 ≤ 1/rootThreshold ε ℓ := (le_div_iff₀ hq.1).mpr (by simpa using hq.2)
  have hL := overhead_base_one ε hε ℓ
  by_cases hid : id=0
  · subst id
    have hr := root_information_run m g s α (rootThreshold ε ℓ) ℓ schedule T
    rw [hr] at hi
    have hscale : info.scale=1/rootThreshold ε ℓ := congrArg CallInformation.scale (Option.some.inj hi).symm
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 1/rootThreshold ε ℓ by linarith)
    have hlog := Real.log_nonneg ((le_div_iff₀ hε.1).mpr (by linarith [hε.2]) : 1 ≤ 2/ε)
    change ((8*(ℓ+2)*(⌈1/rootThreshold ε ℓ⌉₊+2) : ℕ) : ℝ≥0∞) ≤ _
    rw [←ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    rw [hscale]
    have hLL : ((ℓ+2 : ℕ) : ℝ) ≤ 2+Real.log (2/ε)+(ℓ : ℝ) := by push_cast; linarith
    have hceil4 : (⌈1/rootThreshold ε ℓ⌉₊ : ℝ)+2 ≤ 4*(1/rootThreshold ε ℓ) := by linarith
    push_cast
    calc
      _ ≤ 8*(2+Real.log (2/ε)+(ℓ : ℝ))*(4*(1/rootThreshold ε ℓ)) := by
        have hLL' : (ℓ : ℝ)+2 ≤ 2+Real.log (2/ε)+(ℓ : ℝ) := by exact_mod_cast hLL
        have hfirst := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLL' (by norm_num : (0 : ℝ) ≤ 8))
          (show 0 ≤ (⌈1/rootThreshold ε ℓ⌉₊ : ℝ)+2 by positivity)
        have hsecond := mul_le_mul_of_nonneg_left hceil4
          (show 0 ≤ 8*(2+Real.log (2/ε)+(ℓ : ℝ)) by linarith)
        exact hfirst.trans hsecond
      _ = _ := by unfold overhead; ring
  · simp only [recursiveRun,Function.iterate_zero,Function.id_def,recursiveInit,hid,ite_false]
    positivity

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.AccountSplit

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma account_charge_split_level (m : SolveModel) (g : InputGraph n) (α : ℝ) (ℓ : ℕ)
    (st : RecursiveState n) (j id : ℕ)
    (hlevel : ∀ i, i ≤ st.top → (st.frames i).id=id → i=j) :
    accountCharge m g α ℓ st id=ownStepCharge m g α ℓ st id+descendantStepCharge m g α ℓ st j id := by
  let p := (stepDebit m g α ℓ st).1
  have hp : p ≤ st.top := stepDebit_producer_le_top m g α ℓ st
  have he : (∃ i ≤ p, (st.frames i).id=id) ↔ j ≤ p ∧ (st.frames j).id=id := by
    constructor
    · rintro ⟨i,hip,hid⟩
      have hij := hlevel i (hip.trans hp) hid
      subst i
      exact ⟨hip,hid⟩
    · rintro ⟨hj,hid⟩
      exact ⟨j,hj,hid⟩
  have hown : (st.frames p).id=id ↔ p=j ∧ (st.frames j).id=id := by
    constructor
    · intro hh
      have hhj := hlevel p hp hh
      exact ⟨hhj,hhj ▸ hh⟩
    · rintro ⟨rfl,hh⟩
      exact hh
  unfold accountCharge ownStepCharge descendantStepCharge
  change (if ∃ i ≤ p, (st.frames i).id=id then _ else _)=(if (st.frames p).id=id then _ else _)+
    (if j < p ∧ (st.frames j).id=id then _ else _)
  rw [if_congr he rfl rfl,if_congr hown rfl rfl]
  split_ifs <;> (try simp_all) <;> omega

lemma account_charge_run_split (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (k T id : ℕ) (info : CallInformation) (hkT : k ≤ T)
    (hi : (recursiveRun m g s α q ℓ schedule T).information id=some info) :
    let st := recursiveRun m g s α q ℓ schedule k
    accountCharge m g α ℓ st id=ownStepCharge m g α ℓ st id+descendantStepCharge m g α ℓ st info.level id := by
  intro st
  apply account_charge_split_level
  intro i hle hid
  exact (open_frame_prefix_parameters m g s α q ℓ schedule k T i id info hkT hi hle hid).1

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DescendantAccounting

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma descendant_charge_le_children (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (k T j id : ℕ) (hkT : k ≤ T) :
    let run := recursiveRun m g s α q ℓ schedule
    descendantStepCharge m g α ℓ (run k) j id ≤
      ∑ child ∈ seenChildren run j id T, accountCharge m g α ℓ (run k) child := by
  intro run
  unfold descendantStepCharge
  split_ifs with h
  · let child := ((run k).frames (j+1)).id
    have hp := stepDebit_producer_le_top m g α ℓ (run k)
    have hchild : child ∈ seenChildren run j id T := by
      apply child_snapshot_seen run j id k T hkT
      simp only [childSnapshot,if_pos (show j < (run k).top ∧ ((run k).frames j).id=id from ⟨by omega,h.2⟩),mem_singleton]
      rfl
    have haccount : accountCharge m g α ℓ (run k) child=(stepDebit m g α ℓ (run k)).2 := by
      apply if_pos
      exact ⟨j+1,by omega,rfl⟩
    rw [←haccount]
    exact Finset.single_le_sum (fun _ _ => by positivity) hchild
  · positivity

lemma descendant_prefix_le_child_charged (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (T j id : ℕ) :
    let run := recursiveRun m g s α q ℓ schedule
    (∑ k ∈ range T, descendantStepCharge m g α ℓ (run k) j id) ≤
      ∑ child ∈ seenChildren run j id T, (run T).charged child := by
  intro run
  calc
    _ ≤ ∑ k ∈ range T, ∑ child ∈ seenChildren run j id T, accountCharge m g α ℓ (run k) child := by
      apply Finset.sum_le_sum
      intro k hk
      exact descendant_charge_le_children m g s α q ℓ schedule k T j id (mem_range.mp hk).le
    _ = ∑ child ∈ seenChildren run j id T, ∑ k ∈ range T, accountCharge m g α ℓ (run k) child := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun child _ => account_charges_le_charged m g s α q ℓ schedule T child)

lemma charged_le_callWork_of_closes (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ)
    (hclose : ∃ a, id ∈ (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule a).closed) :
    (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule T).charged id ≤ callWork m g s α ε ℓ schedule id := by
  unfold callWork
  rw [if_pos hclose]
  exact le_iSup (fun t => (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).charged id) T

lemma charged_prefix_decomposition (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) (info : CallInformation)
    (hi : (recursiveRun m g s α q ℓ schedule T).information id=some info) :
    let run := recursiveRun m g s α q ℓ schedule
    (run T).charged id ≤ (run 0).charged id+
      (∑ k ∈ range T, ownStepCharge m g α ℓ (run k) id)+
      ∑ child ∈ seenChildren run info.level id T, (run T).charged child := by
  intro run
  rw [account_charge_telescope]
  have heq : (∑ k ∈ range T, accountCharge m g α ℓ (run k) id)=
      (∑ k ∈ range T, ownStepCharge m g α ℓ (run k) id)+
      (∑ k ∈ range T, descendantStepCharge m g α ℓ (run k) info.level id) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact account_charge_run_split m g s α q ℓ schedule k T id info (mem_range.mp hk).le hi
  rw [heq,←add_assoc]
  exact add_le_add le_rfl (descendant_prefix_le_child_charged m g s α q ℓ schedule T info.level id)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.InformationBlock

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma information_block_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (T : ℕ) :
    ∀ id info, (recursiveRun m g s α q ℓ schedule T).information id=some info →
      info.block=blockScale schedule ℓ info.level info.scale := by
  classical
  induction T with
  | zero =>
    intro id info hi
    change (if id=0 then some ⟨0,1/q,blockScale schedule ℓ 0 (1/q)⟩ else none)=some info at hi
    split_ifs at hi with he
    · have hh := Option.some.inj hi
      subst info
      rfl
  | succ T ih =>
    intro id info hi
    let st := recursiveRun m g s α q ℓ schedule T
    let next := recursiveRun m g s α q ℓ schedule (T+1)
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
        have hg : st.top < (recursiveStep m g s α ℓ schedule st).top := by rw [←hstep,htop]; omega
        obtain ⟨hd,hcomp,hpc,hno,hdepth⟩ := growing_step_guards m g s α ℓ schedule st hg
        simp [hstep,recursiveStep,hd,hcomp,hpc,hno,hdepth,freshFrame,changeFrame,debit]
      · apply ih id info
        change next.information id=some info at hi
        rwa [hm,Function.update_of_ne he] at hi

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ChildWorkEnvelope

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma seen_child_workEnvelope (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α ≤ 1/2) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id child : ℕ) (info : CallInformation)
    (hi : (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule T).information id=some info)
    (hc : child ∈ seenChildren (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule) info.level id T) :
    callWork m g s α ε ℓ schedule child ≤ workEnvelope m ε ℓ schedule (info.level+1) info.block := by
  have hq := root_threshold_unit ε hε ℓ
  obtain ⟨ci,hci,hlevel,hscale⟩ := seen_child_information m g s α (rootThreshold ε ℓ) hq.1 ℓ schedule T id child info hi hc
  have hb := information_block_run m g s α (rootThreshold ε ℓ) ℓ schedule T child ci hci
  have heq : ci=⟨info.level+1,info.block,blockScale schedule ℓ (info.level+1) info.block⟩ := by
    cases ci
    simp_all
  apply le_sSup
  exact ⟨n,g,s,α,child,T,hα.1,hα.2,hs,by rwa [←heq],rfl⟩

lemma child_charged_sum_envelope (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α ≤ 1/2) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) (info : CallInformation)
    (hi : (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule T).information id=some info) :
    let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
    (∑ child ∈ seenChildren run info.level id T, (run T).charged child) ≤
      ((seenChildren run info.level id T).card : ℝ≥0∞)*workEnvelope m ε ℓ schedule (info.level+1) info.block := by
  intro run
  calc
    _ ≤ ∑ child ∈ seenChildren run info.level id T, workEnvelope m ε ℓ schedule (info.level+1) info.block := by
      apply Finset.sum_le_sum
      intro child hc
      obtain ⟨ci,hci,_,_⟩ := seen_child_information m g s α (rootThreshold ε ℓ) (root_threshold_unit ε hε ℓ).1
        ℓ schedule T id child info hi hc
      have hclose := created_call_eventually_closed m g s α ε hα hε hs ℓ schedule T child ci hci
      exact (charged_le_callWork_of_closes m g s α ε ℓ schedule T child (by
        obtain ⟨u,_,hu⟩ := hclose
        exact ⟨u,hu⟩)).trans (seen_child_workEnvelope m g s α ε hα hε hs ℓ schedule T id child info hi hc)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CallWorkPrefix

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma callWork_bound_of_prefixes (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α ≤ 1/2) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a id : ℕ) (info : CallInformation) (B : ℝ≥0∞)
    (hi : (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule a).information id=some info)
    (hbound : ∀ T, (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule T).information id=some info →
      (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule T).charged id ≤ B) :
    callWork m g s α ε ℓ schedule id ≤ B := by
  obtain ⟨u,_,hu⟩ := created_call_eventually_closed m g s α ε hα hε hs ℓ schedule a id info hi
  unfold callWork
  rw [if_pos ⟨u,hu⟩]
  apply iSup_le
  intro T
  have hi' := information_run_persistent m g s α (rootThreshold ε ℓ) ℓ schedule a (max a T) id info (le_max_left _ _) hi
  exact (charged_run_monotone m g s α (rootThreshold ε ℓ) ℓ schedule id (le_max_right a T)).trans (hbound (max a T) hi')

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ChargedRecurrence

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma uniform_charged_recurrence (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule)
        (T id : ℕ) (info : CallInformation),
        (0 < α ∧ α ≤ 1/2) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
        let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
        (run T).information id=some info →
        (run T).charged id ≤
          if info.level=ℓ then ENNReal.ofReal (overhead C c ε ℓ*(info.scale^2/info.block+info.scale*info.block))
          else ENNReal.ofReal (overhead C c ε ℓ*(info.scale^2/info.block))+
            ENNReal.ofReal (overhead C c ε ℓ*info.scale/info.block)*
              workEnvelope m ε ℓ schedule (info.level+1) info.block := by
  obtain ⟨Co,co,hCo,hco,hOwn⟩ := uniform_own_work_bound m
  obtain ⟨Ck,hCk,hChildren⟩ := uniform_seen_children_count
  let C := Co+32+Ck
  let c := max co 4
  refine ⟨C,c,by dsimp only [C]; positivity,lt_of_lt_of_le hco (le_max_left _ _),?_⟩
  intro n g s α ε ℓ schedule T id info hα hε hs run hi
  let P := overhead C c ε ℓ
  let O := overhead Co co ε ℓ
  let I := overhead 32 1 ε ℓ
  let F := info.scale^2/info.block+if info.level=ℓ then info.scale*info.block else 0
  have hq := root_threshold_unit ε hε ℓ
  have hlegal := information_legal_run m g s α (rootThreshold ε ℓ) hq ℓ schedule T id info hi
  have hN : 1 ≤ info.scale := hlegal.2.1
  have hb : 0 < (info.block : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hlegal.2.2.1
  have hbN := hlegal.2.2.2.1
  have hpoly (R : ℝ) (r : ℕ) (hR : 0 ≤ R) : 0 ≤ overhead R r ε ℓ := by
    unfold overhead
    exact mul_nonneg hR (pow_nonneg (by linarith [overhead_base_one ε hε ℓ]) _)
  have hI : 0 ≤ I := hpoly 32 1 (by norm_num)
  have hO : 0 ≤ O := hpoly Co co hCo.le
  have hP : 0 ≤ P := hpoly C c (by dsimp only [C]; positivity)
  have hNN : info.scale ≤ info.scale^2/(info.block : ℝ) := by
    apply (le_div_iff₀ hb).mpr
    nlinarith
  have hF : info.scale ≤ F := by
    dsimp only [F]
    split_ifs <;> nlinarith [mul_nonneg (show 0 ≤ info.scale by linarith) hb.le]
  have hF0 : 0 ≤ F := by linarith
  have hOI : O+I ≤ P := by
    have ho := overhead_mono ε hε ℓ co c Co Co hCo.le le_rfl (le_max_left _ _)
    have hi' := overhead_mono ε hε ℓ 1 c 32 32 (by norm_num) le_rfl (by dsimp only [c]; omega)
    have hsum := add_le_add ho hi'
    rw [overhead_sum] at hsum
    exact hsum.trans (overhead_mono ε hε ℓ c c (Co+32) C (by positivity) (by dsimp only [C]; linarith) le_rfl)
  have hinit := initial_call_charge_bound m g s α ε hε ℓ schedule T id info hi
  have hown := hOwn n g s α ε ℓ schedule T id info hα hε hs hi
  have hbase : (run 0).charged id+(∑ k ∈ range T, ownStepCharge m g α ℓ (run k) id) ≤ ENNReal.ofReal (P*F) := by
    have hh := add_le_add hinit hown
    apply hh.trans
    rw [←ENNReal.ofReal_add (mul_nonneg hI (by linarith)) (mul_nonneg hO hF0)]
    apply ENNReal.ofReal_le_ofReal
    have hif := mul_le_mul_of_nonneg_left hF hI
    have hpm := mul_le_mul_of_nonneg_right hOI hF0
    nlinarith
  have hdecomp := charged_prefix_decomposition m g s α (rootThreshold ε ℓ) ℓ schedule T id info hi
  dsimp only at hdecomp
  by_cases he : info.level=ℓ
  · simp only [if_pos he]
    have hempty := leaf_children_empty m g s α (rootThreshold ε ℓ) hq.1 ℓ schedule T id info hi he
    rw [hempty,Finset.sum_empty,add_zero] at hdecomp
    exact hdecomp.trans (by simpa only [F,he,ite_true] using hbase)
  · simp only [if_neg he]
    have hc := child_charged_sum_envelope m g s α ε hα hε hs ℓ schedule T id info hi
    have hcard := hChildren m n g s α ε ℓ schedule hα hε hs T id info hi
    have hmono := overhead_mono ε hε ℓ 4 c Ck C hCk.le (by dsimp only [C]; linarith) (le_max_right _ _)
    have hcardP : ((seenChildren run info.level id T).card : ℝ) ≤ P*info.scale/info.block :=
      hcard.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmono (by linarith)) hb.le)
    have hcardENN : ((seenChildren run info.level id T).card : ℝ≥0∞) ≤ ENNReal.ofReal (P*info.scale/info.block) := by
      rw [←ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hcardP
    have hcP := hc.trans (mul_le_mul_of_nonneg_right hcardENN (by positivity))
    exact hdecomp.trans (add_le_add (by simpa only [F,he,ite_false,add_zero] using hbase) hcP)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.WorkRecurrence

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma uniform_work_recurrence (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧ ∀ (ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule),
      0 < ε → ε ≤ 1 →
      let P := overhead C c ε ℓ
      (∀ (j : ℕ) (N : ℝ), j < ℓ → 1 ≤ N → let b := blockScale schedule ℓ j N
        workEnvelope m ε ℓ schedule j N ≤ ENNReal.ofReal P*
          (ENNReal.ofReal (N^2/b)+ENNReal.ofReal (N/b)*workEnvelope m ε ℓ schedule (j+1) b)+ENNReal.ofReal (P*N)) ∧
      (∀ N : ℝ, 1 ≤ N → let b := blockScale schedule ℓ ℓ N
        workEnvelope m ε ℓ schedule ℓ N ≤ ENNReal.ofReal (P*(N^2/b+N*b))) := by
  obtain ⟨C,c,hC,hc,hPrefix⟩ := uniform_charged_recurrence m
  refine ⟨C,c,hC,hc,?_⟩
  intro ε ℓ schedule he he1 P
  have hP : 0 ≤ P := by
    dsimp only [P,overhead]
    exact mul_nonneg hC.le (pow_nonneg (by linarith [overhead_base_one ε ⟨he,he1⟩ ℓ]) _)
  constructor
  · intro j N hj hN b
    unfold workEnvelope
    apply sSup_le
    intro w hw
    obtain ⟨n,g,s,α,id,t,ha,ha1,hs,hi,rfl⟩ := hw
    have hbound : callWork m g s α ε ℓ schedule id ≤ ENNReal.ofReal (P*(N^2/b))+
        ENNReal.ofReal (P*N/b)*workEnvelope m ε ℓ schedule (j+1) b := by
      apply callWork_bound_of_prefixes m g s α ε ⟨ha,ha1⟩ ⟨he,he1⟩ hs ℓ schedule t id
        ⟨j,N,blockScale schedule ℓ j N⟩ _ hi
      intro T hiT
      have hh := hPrefix n g s α ε ℓ schedule T id ⟨j,N,blockScale schedule ℓ j N⟩ ⟨ha,ha1⟩ ⟨he,he1⟩ hs hiT
      simpa only [if_neg (show j ≠ ℓ by omega)] using hh
    have heq : ENNReal.ofReal (P*(N^2/b))+ENNReal.ofReal (P*N/b)*workEnvelope m ε ℓ schedule (j+1) b=
        ENNReal.ofReal P*(ENNReal.ofReal (N^2/b)+ENNReal.ofReal (N/b)*workEnvelope m ε ℓ schedule (j+1) b) := by
      rw [ENNReal.ofReal_mul hP,show P*N/(b : ℝ)=P*(N/b) by ring,ENNReal.ofReal_mul hP]
      ring
    apply hbound.trans
    rw [heq]
    exact le_add_of_nonneg_right (by positivity)
  · intro N hN b
    unfold workEnvelope
    apply sSup_le
    intro w hw
    obtain ⟨n,g,s,α,id,t,ha,ha1,hs,hi,rfl⟩ := hw
    apply callWork_bound_of_prefixes m g s α ε ⟨ha,ha1⟩ ⟨he,he1⟩ hs ℓ schedule t id
      ⟨ℓ,N,blockScale schedule ℓ ℓ N⟩ _ hi
    intro T hiT
    have hh := hPrefix n g s α ε ℓ schedule T id ⟨ℓ,N,blockScale schedule ℓ ℓ N⟩ ⟨ha,ha1⟩ ⟨he,he1⟩ hs hiT
    simpa only [if_pos rfl,ite_true] using hh

end
end NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal

theorem solution (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧ ∀ (ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule),
      0 < ε → ε ≤ 1 →
      let P := overhead C c ε ℓ
      (∀ (j : ℕ) (N : ℝ), j < ℓ → 1 ≤ N → let b := blockScale schedule ℓ j N
        workEnvelope m ε ℓ schedule j N ≤ ENNReal.ofReal P*
          (ENNReal.ofReal (N^2/b)+ENNReal.ofReal (N/b)*workEnvelope m ε ℓ schedule (j+1) b)+ENNReal.ofReal (P*N)) ∧
      (∀ N : ℝ, 1 ≤ N → let b := blockScale schedule ℓ ℓ N
        workEnvelope m ε ℓ schedule ℓ N ≤ ENNReal.ofReal (P*(N^2/b+N*b))) := by
  exact uniform_work_recurrence m
