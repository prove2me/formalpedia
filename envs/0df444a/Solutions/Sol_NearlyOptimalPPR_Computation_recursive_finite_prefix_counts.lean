-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_finite_prefix_counts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:04:34.747897+00:00
-- url     : https://prove2.me/submissions/bdb265d1-bb26-449c-93ac-0b6b1a5b8690

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_full_solve_count
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_episode_count
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_cached_solve_count
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_call_metadata
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_discovery_effort
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_event_count

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

abbrev uniform_full_solve_count :=
  recursive_full_solve_count

abbrev uniform_episode_count :=
  recursive_episode_count

abbrev uniform_cached_solve_count :=
  recursive_cached_solve_count

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

abbrev call_discovery_effort_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) (info : CallInformation)
    (hinfo : (recursiveRun m g s α q ℓ schedule T).information id=some info) :=
  recursive_discovery_effort m n g s α q hα hq hs ℓ schedule T id info hinfo

abbrev control_prefix_count (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) :=
  recursive_control_event_count m n g s α q hq hs ℓ schedule T id

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FiniteEvents

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma finite_events_of_prefix_bound (P : ℕ → Prop) (B : ℝ) (a : ℕ)
    (h : ∀ T, a ≤ T → (((range T).filter P).card : ℝ) ≤ B) :
    {t | P t}.Finite := by
  by_contra hn
  obtain ⟨k,hk⟩ := exists_nat_gt B
  obtain ⟨S,hS,hcard⟩ := Set.Infinite.exists_subset_card_eq hn k
  let T := max a (S.sup id+1)
  have hsub : S ⊆ (range T).filter P := by
    intro t ht
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_,hS ht⟩
    have hh : t ≤ S.sup id := Finset.le_sup (f:=id) ht
    dsimp only [T]
    omega
  have hc : (k : ℝ) ≤ (((range T).filter P).card : ℝ) := by
    exact_mod_cast (hcard ▸ Finset.card_le_card hsub)
  have hb := h T (by dsimp only [T]; omega)
  linarith

lemma finite_events_eventually_absent (P : ℕ → Prop) (h : {t | P t}.Finite) :
    ∃ T, ∀ t, T ≤ t → ¬P t := by
  let S := h.toFinset
  refine ⟨S.sup id+1,?_⟩
  intro t ht hp
  have hm : t ∈ S := h.mem_toFinset.mpr hp
  have hh : t ≤ S.sup id := Finset.le_sup (f:=id) hm
  omega

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

-- Proof module: Solutions.PoppedCallClosure

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 2000000 in
lemma top_step_lower (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) :
    st.top-1 ≤ (recursiveStep m g s α ℓ schedule st).top := by
  cases hpend : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;> simp [recursiveStep,hpc,hpend] <;>
      (try split_ifs) <;> simp_all [debit] <;> omega
  | some p =>
    obtain ⟨t,v⟩ := p
    cases hpc : (st.frames st.top).pc <;> simp [recursiveStep,hpc,hpend] <;>
      (try split_ifs) <;> simp_all [debit] <;> omega

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

-- Proof module: Solutions.ClosureShapes

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 2000000 in
lemma closed_step_running_shape (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hrunning : (recursiveStep m g s α ℓ schedule st).done = false) :
    (recursiveStep m g s α ℓ schedule st).closed=st.closed ∨
      ((recursiveStep m g s α ℓ schedule st).top < st.top ∧
        (recursiveStep m g s α ℓ schedule st).closed=insert (st.frames st.top).id st.closed) := by
  obtain ⟨hd,hcomp⟩ := running_step_guards m g s α ℓ schedule st hrunning
  cases hpend : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hcomp,hpc,hpend] at hrunning ⊢ <;>
      (try split_ifs at hrunning ⊢) <;>
      first
      | left; simp; done
      | right; constructor
        · simp_all [endCall,debit] <;> (try split_ifs) <;> simp_all <;> omega
        · simp [debit]
  | some p =>
    obtain ⟨t,v⟩ := p
    have hh := (exterior_lifecycle g α st t v).2.2
    cases hpc : (st.frames st.top).pc <;>
      simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hcomp,hpc,hpend] at hrunning ⊢ <;>
      (try split_ifs at hrunning ⊢) <;>
      first
      | left; simp [hh]; done
      | right; constructor
        · simp_all [endCall,debit] <;> (try split_ifs) <;> simp_all <;> omega
        · simp [debit]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OpenFrameInformation

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma open_frame_ids_injective (st : RecursiveState n) (hi : OpenFrameInformation st)
    (i j : ℕ) (his : i ≤ st.top) (hjs : j ≤ st.top) (hid : (st.frames i).id=(st.frames j).id) : i=j := by
  have hi' := hi i his
  have hj' := hi j hjs
  rw [hid,hj'] at hi'
  exact (congrArg CallInformation.level (Option.some.inj hi')).symm

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

-- Proof module: Solutions.CallFiniteEvents

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma own_push_prefix_count (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) (info : CallInformation)
    (hinfo : (recursiveRun m g s α q ℓ schedule T).information id=some info) :
    (((range T).filter (fun t => ownPushEvent (recursiveRun m g s α q ℓ schedule t) id)).card : ℝ) ≤
      15*info.scale := by
  apply le_trans _ (call_discovery_effort_bound m g s α q hα hq hs ℓ schedule T id info hinfo)
  rw [←Finset.sum_boole]
  apply Finset.sum_le_sum
  intro t ht
  split_ifs with hp
  · obtain ⟨j,v,hprod,hid⟩ := hp
    simp only [callDiscoveryEffort,hprod,hid,ite_true]
    unfold LocalPush.deg
    exact le_add_of_nonneg_left (by positivity)
  · exact callDiscoveryEffort_nonnegative g _ id

lemma created_call_finite_events (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α ≤ 1/2) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a id : ℕ) (info : CallInformation)
    (hinfo : (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule a).information id=some info) :
    let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
    {t | ownPushEvent (run t) id}.Finite ∧
    {t | cachedSolveEvent g (run t) id}.Finite ∧
    {t | controlEvent g (run t) id}.Finite := by
  intro run
  obtain ⟨Ce,hCe,hEp⟩ := uniform_episode_count
  obtain ⟨Cc,hCc,hCache⟩ := uniform_cached_solve_count
  have hi (T : ℕ) (haT : a ≤ T) : (run T).information id=some info :=
    information_run_persistent m g s α (rootThreshold ε ℓ) ℓ schedule a T id info haT hinfo
  have hq := root_threshold_unit ε hε ℓ
  refine ⟨?_,?_,?_⟩
  · apply finite_events_of_prefix_bound _ (15*info.scale) a
    intro T haT
    exact own_push_prefix_count m g s α (rootThreshold ε ℓ) ⟨hα.1,by linarith [hα.2]⟩ hq hs ℓ schedule T id info (hi T haT)
  · apply finite_events_of_prefix_bound _ (overhead Cc 4 ε ℓ*info.scale) a
    intro T haT
    exact hCache m n g s α ε ℓ schedule hα hε hs T id info (hi T haT)
  · apply finite_events_of_prefix_bound _ (9+7*(overhead Ce 4 ε ℓ*info.scale/info.block)) a
    intro T haT
    have hc := control_prefix_count m g s α (rootThreshold ε ℓ) hq.1 hs ℓ schedule T id
    have he := hEp m n g s α ε ℓ schedule hα hε hs T id info (hi T haT)
    exact hc.trans (by linarith)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DoneClosed

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma done_changeFrame (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).done=st.done := rfl
@[simp] lemma done_PC (st : RecursiveState n) (pc : NormalizePC) : (changePC st pc).done=st.done := rfl
@[simp] lemma done_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) : (debit st j w).done=st.done := rfl
@[simp] lemma done_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).done=st.done := rfl
@[simp] lemma done_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    (jointUpdate g α st h).done=st.done := rfl
@[simp] lemma done_finish (st : RecursiveState n) : (finishEpisode st).done=st.done := rfl
@[simp] lemma done_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ) (v : Fin n) :
    (exteriorPush g α st j v).done=st.done := by
  simp [exteriorPush,changeFrame,refreshKeys,debit] <;> (try split_ifs) <;> rfl

lemma doneClosed_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) :
    DoneClosed (completeComponent m g s α st) := by
  intro _ j hj
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  exact ⟨j,Finset.mem_range.mpr (by simpa [completeComponent,debit] using Nat.lt_succ_of_le hj),rfl⟩

lemma doneClosed_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hd : st.done=false) :
    DoneClosed (endCall g α st) := by
  unfold endCall
  dsimp only
  split
  · rename_i htop
    intro _ j hj
    have he : j=0 := by simpa [debit,htop] using hj
    subst j
    simp [debit,htop]
  · intro hh
    exact False.elim (by simpa [hd] using hh)

set_option maxHeartbeats 2000000 in
lemma doneClosed_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hi : DoneClosed st) :
    DoneClosed (recursiveStep m g s α ℓ schedule st) := by
  by_cases hd : st.done=true
  · simpa [recursiveStep,hd] using hi
  have hdf : st.done=false := Bool.eq_false_of_not_eq_true hd
  by_cases hc : componentComplete st
  · simpa [recursiveStep,hd,hc] using doneClosed_complete m g s α st
  cases hp : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp only [recursiveStep,hd,hc,ite_false,hpc,hp] <;>
      (try split_ifs) <;>
      first
      | exact doneClosed_end g α _ (by simp [hdf])
      | (unfold DoneClosed; simp only [done_changeFrame,done_PC,done_debit,done_refresh,done_joint,done_finish,done_exterior,hdf,Bool.false_eq_true,false_implies])
  | some p =>
    obtain ⟨j,v⟩ := p
    cases hpc : (st.frames st.top).pc <;>
      simp only [recursiveStep,hd,hc,ite_false,hpc,hp] <;>
      (try split_ifs) <;>
      first
      | exact doneClosed_end g α _ (by simp [hdf])
      | (unfold DoneClosed; simp only [done_changeFrame,done_PC,done_debit,done_refresh,done_joint,done_finish,done_exterior,hdf,Bool.false_eq_true,false_implies])

lemma doneClosed_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) : DoneClosed (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => intro hh; simp [recursiveRun,recursiveInit] at hh
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      doneClosed_step m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule t) ih

lemma unclosed_call_running (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ) (info : CallInformation)
    (hinfo : (recursiveRun m g s α q ℓ schedule t).information id=some info)
    (hn : id ∉ (recursiveRun m g s α q ℓ schedule t).closed) :
    (recursiveRun m g s α q ℓ schedule t).done=false := by
  rcases call_locations_run m g s α q ℓ schedule t id info hinfo with hc|⟨hj,hid,_⟩
  · exact False.elim (hn hc)
  · apply Bool.eq_false_of_not_eq_true
    intro hd
    apply hn
    rw [←hid]
    exact doneClosed_run m g s α q ℓ schedule t hd info.level hj

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ClosureReturn

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 2000000 in
lemma new_closure_running_top (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (id : ℕ)
    (hr : (recursiveStep m g s α ℓ schedule st).done=false)
    (ho : id ∉ st.closed) (hn : id ∈ (recursiveStep m g s α ℓ schedule st).closed) :
    (st.frames st.top).id=id ∧ (recursiveStep m g s α ℓ schedule st).top=st.top-1 := by
  obtain hc|⟨hdrop,hc⟩ := closed_step_running_shape m g s α ℓ schedule st hr
  · exact False.elim (ho (hc ▸ hn))
  have hid : (st.frames st.top).id=id := by
    rw [hc] at hn
    exact ((Finset.mem_insert.mp hn).resolve_right ho).symm
  have hlower := top_step_lower m g s α ℓ schedule st
  exact ⟨hid,by omega⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ChildReturnTime

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma child_closure_parent_time (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a parent child : ℕ) (pi ci : CallInformation)
    (hp : (recursiveRun m g s α q ℓ schedule a).information parent=some pi)
    (hc : (recursiveRun m g s α q ℓ schedule a).information child=some ci)
    (hlevel : ci.level=pi.level+1)
    (hcopen : child ∉ (recursiveRun m g s α q ℓ schedule a).closed)
    (hpnever : ∀ t, a ≤ t → parent ∉ (recursiveRun m g s α q ℓ schedule t).closed)
    (hcloses : ∃ t, a ≤ t ∧ child ∈ (recursiveRun m g s α q ℓ schedule t).closed) :
    ∃ t, a ≤ t ∧ (recursiveRun m g s α q ℓ schedule t).top=pi.level := by
  classical
  let run := recursiveRun m g s α q ℓ schedule
  let k := Nat.find hcloses
  have hk : a ≤ k ∧ child ∈ (run k).closed := Nat.find_spec hcloses
  have hka : a < k := by
    by_contra hn
    have he : k=a := by omega
    exact hcopen (he ▸ hk.2)
  have hak : a ≤ k-1 := by omega
  have hks : k-1+1=k := by omega
  have hn : child ∉ (run (k-1)).closed := by
    intro hh
    exact Nat.find_min hcloses (show k-1<k by omega) ⟨hak,hh⟩
  have hpi := information_run_persistent m g s α q ℓ schedule a k parent pi hk.1 hp
  have hr : (run k).done=false := unclosed_call_running m g s α q ℓ schedule k parent pi hpi (hpnever k hk.1)
  have hstep : run k=recursiveStep m g s α ℓ schedule (run (k-1)) := by
    conv_lhs => rw [←hks]
    simp only [run,recursiveRun,Function.iterate_succ_apply']
  have hshape := new_closure_running_top m g s α ℓ schedule (run (k-1)) child (hstep ▸ hr) hn (hstep ▸ hk.2)
  have hci := information_run_persistent m g s α q ℓ schedule a (k-1) child ci hak hc
  rcases call_locations_run m g s α q ℓ schedule (k-1) child ci hci with hclosed|⟨hle,hid,_⟩
  · exact False.elim (hn hclosed)
  have htop : ci.level=(run (k-1)).top :=
    open_frame_ids_injective (run (k-1)) (open_frame_information_run m g s α q ℓ schedule (k-1))
      ci.level (run (k-1)).top hle le_rfl (hid.trans hshape.1.symm)
  refine ⟨k,hk.1,?_⟩
  change (run k).top=pi.level
  rw [hstep,hshape.2,←htop,hlevel]
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QuietCall

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma call_eventually_quiet (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α ≤ 1/2) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a id : ℕ) (info : CallInformation)
    (hi : (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule a).information id=some info)
    (hj : info.level ≤ (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule a).top) :
    let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
    ∃ T, a ≤ T ∧ ∀ t, T ≤ t →
      (∀ i, i ≤ info.level → ¬ownPushEvent (run t) ((run a).frames i).id) ∧
      ¬cachedSolveEvent g (run t) id ∧ ¬controlEvent g (run t) id := by
  classical
  intro run
  have hpush (i : ℕ) : ∃ T, ∀ t, T ≤ t → i ≤ info.level →
      ¬ownPushEvent (run t) ((run a).frames i).id := by
    by_cases hle : i ≤ info.level
    · have hi' := open_frame_information_run m g s α (rootThreshold ε ℓ) ℓ schedule a i (hle.trans hj)
      obtain ⟨hfinite,_,_⟩ := created_call_finite_events m g s α ε hα hε hs ℓ schedule a
        ((run a).frames i).id ⟨i,((run a).frames i).N,((run a).frames i).block⟩ hi'
      obtain ⟨T,hT⟩ := finite_events_eventually_absent _ hfinite
      exact ⟨T,fun t ht _ => hT t ht⟩
    · exact ⟨0,fun _ _ hh => False.elim (hle hh)⟩
  let f := fun i => Classical.choose (hpush i)
  have hf (i : ℕ) := Classical.choose_spec (hpush i)
  obtain ⟨_,hcache,hcontrol⟩ := created_call_finite_events m g s α ε hα hε hs ℓ schedule a id info hi
  obtain ⟨Tc,hTc⟩ := finite_events_eventually_absent _ hcache
  obtain ⟨Tk,hTk⟩ := finite_events_eventually_absent _ hcontrol
  let T := max a (max ((range (info.level+1)).sup f) (max Tc Tk))
  refine ⟨T,by dsimp only [T]; omega,?_⟩
  intro t ht
  have htc : Tc ≤ t := by dsimp only [T] at ht; omega
  have htk : Tk ≤ t := by dsimp only [T] at ht; omega
  refine ⟨?_,hTc t htc,hTk t htk⟩
  intro i hle
  have hsup : f i ≤ (range (info.level+1)).sup f :=
    Finset.le_sup (f:=f) (mem_range.mpr (by omega))
  have hfi : f i ≤ t := by
    dsimp only [T] at ht
    omega
  exact hf i t hfi hle

lemma quiet_call_not_current (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a t id : ℕ) (info : CallInformation) (hat : a ≤ t)
    (hi : (recursiveRun m g s α q ℓ schedule a).information id=some info)
    (hn : id ∉ (recursiveRun m g s α q ℓ schedule t).closed)
    (hnnext : id ∉ (recursiveRun m g s α q ℓ schedule (t+1)).closed)
    (hp : ∀ i, i ≤ info.level → ¬ownPushEvent (recursiveRun m g s α q ℓ schedule t)
      ((recursiveRun m g s α q ℓ schedule a).frames i).id)
    (hc : ¬cachedSolveEvent g (recursiveRun m g s α q ℓ schedule t) id)
    (hk : ¬controlEvent g (recursiveRun m g s α q ℓ schedule t) id) :
    (recursiveRun m g s α q ℓ schedule t).top ≠ info.level := by
  classical
  let run := recursiveRun m g s α q ℓ schedule
  intro htop
  change (run t).top=info.level at htop
  have hinfo := information_run_persistent m g s α q ℓ schedule a t id info hat hi
  have hd := unclosed_call_running m g s α q ℓ schedule t id info hinfo hn
  change (run t).done=false at hd
  have hspan := unclosed_call_interval m g s α q ℓ schedule a t id info hi hn
  have hid : ((run t).frames info.level).id=id := (hspan t hat le_rfl).2.1
  have hf (i : ℕ) (hle : i ≤ info.level) : ((run t).frames i).id=((run a).frames i).id := by
    have hh := frozenFrame_interval m g s α q ℓ schedule a t i hat
      (fun k hak hkt => hle.trans (hspan k hak hkt.le).1)
    exact congrArg (fun f => f.2.2.2) hh
  have hprod : stepProduction (run t)=none := by
    cases he : stepProduction (run t) with
    | none => rfl
    | some p =>
      obtain ⟨i,v⟩ := p
      have hle : i ≤ info.level := by
        have hh := (pending_push_member (run t) i v (production_pending (run t) i v he)).1
        change (run t).top=info.level at htop
        omega
      exact False.elim (hp i hle ⟨i,v,he,hf i hle⟩)
  have hcomp : ¬componentComplete (run t) := by
    intro hco
    have hs : run (t+1)=recursiveStep m g s α ℓ schedule (run t) := by
      simp only [run,recursiveRun,Function.iterate_succ_apply']
    have hcnext : id ∈ (run (t+1)).closed := by
      rw [hs]
      simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hco,ite_true,closed_complete]
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨info.level,mem_range.mpr (by omega),hid⟩
    exact hnnext hcnext
  apply hk
  refine ⟨hd,hprod,hc,?_⟩
  rw [if_neg hcomp,htop]
  exact hid

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecursiveTermination

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma created_call_eventually_closed (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (hα : 0 < α ∧ α ≤ 1/2) (hε : 0 < ε ∧ ε ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a id : ℕ) (info : CallInformation)
    (hi : (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule a).information id=some info) :
    ∃ t, a ≤ t ∧ id ∈ (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).closed := by
  classical
  let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
  have aux : ∀ d a id (info : CallInformation), ℓ-info.level=d →
      (run a).information id=some info → ∃ t, a ≤ t ∧ id ∈ (run t).closed := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro a id info hdepth hi
      by_contra hnever
      push_neg at hnever
      have hloc := call_locations_run m g s α (rootThreshold ε ℓ) ℓ schedule a id info hi
      have hj : info.level ≤ (run a).top := by
        rcases hloc with hc|hc
        · exact False.elim (hnever a le_rfl hc)
        · exact hc.1
      obtain ⟨T,haT,hquiet⟩ := call_eventually_quiet m g s α ε hα hε hs ℓ schedule a id info hi hj
      have hinfoT : (run T).information id=some info :=
        information_run_persistent m g s α (rootThreshold ε ℓ) ℓ schedule a T id info haT hi
      have hlocT := unclosed_call_interval m g s α (rootThreshold ε ℓ) ℓ schedule a T id info hi (hnever T haT)
      have hle : info.level ≤ (run T).top := (hlocT T haT le_rfl).1
      have hneq : (run T).top ≠ info.level := quiet_call_not_current m g s α (rootThreshold ε ℓ) ℓ schedule a T id info haT hi
        (hnever T haT) (hnever (T+1) (by omega)) (hquiet T le_rfl).1 (hquiet T le_rfl).2.1 (hquiet T le_rfl).2.2
      have hchild : info.level+1 ≤ (run T).top := by omega
      let child := ((run T).frames (info.level+1)).id
      let ci : CallInformation := ⟨info.level+1,((run T).frames (info.level+1)).N,((run T).frames (info.level+1)).block⟩
      have hci : (run T).information child=some ci :=
        open_frame_information_run m g s α (rootThreshold ε ℓ) ℓ schedule T (info.level+1) hchild
      have hd := unclosed_call_running m g s α (rootThreshold ε ℓ) ℓ schedule T id info hinfoT (hnever T haT)
      have hcopen : child ∉ (run T).closed :=
        running_open_not_closed_run m g s α (rootThreshold ε ℓ) ℓ schedule T hd (info.level+1) hchild
      have hcloses : ∃ t, T ≤ t ∧ child ∈ (run t).closed := by
        apply ih (ℓ-ci.level) _ T child ci rfl hci
        have htopbound := depth_run m g s α (rootThreshold ε ℓ) ℓ schedule T
        change (run T).top ≤ ℓ at htopbound
        change ℓ-(info.level+1)<d
        omega
      obtain ⟨u,hTu,hu⟩ := child_closure_parent_time m g s α (rootThreshold ε ℓ) ℓ schedule T id child info ci
        hinfoT hci rfl hcopen (fun t hTt => hnever t (haT.trans hTt)) hcloses
      have haU : a ≤ u := haT.trans hTu
      exact quiet_call_not_current m g s α (rootThreshold ε ℓ) ℓ schedule a u id info haU hi
        (hnever u haU) (hnever (u+1) (by omega)) (hquiet u hTu).1 (hquiet u hTu).2.1 (hquiet u hTu).2.2 hu
  exact aux (ℓ-info.level) a id info rfl hi

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ChildCounts

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma child_counter_transport (st u : RecursiveState n) (hi : ChildCounterInvariant st)
    (hc : ∀ i, (u.frames i).childrenThisEpisode = (st.frames i).childrenThisEpisode)
    (hp : ∀ i, (u.frames i).pc = (st.frames i).pc)
    (hh : u.episodeChildCounts = st.episodeChildCounts) : ChildCounterInvariant u := by
  refine ⟨?_,?_⟩
  · intro i
    rw [hc,hp]
    exact hi.1 i
  · simpa [hh] using hi.2

lemma child_counter_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : ChildCounterInvariant st) : ChildCounterInvariant (refreshKeys g st T) := by
  apply child_counter_transport st _ hi
  · intro i; by_cases he : i ≤ st.top <;> simp [refreshKeys,he]
  · exact frame_pc_refresh g st T
  · rfl

lemma child_counter_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ)
    (hi : ChildCounterInvariant st) : ChildCounterInvariant (jointUpdate g α st h) := by
  apply child_counter_transport st _ hi
  · intro i; by_cases he : i ≤ st.top <;> simp [jointUpdate,he]
  · exact frame_pc_joint g α st h
  · rfl

@[simp] lemma frame_children_debit (st : RecursiveState n) (j i : ℕ) (w : ℝ≥0∞) :
    ((debit st j w).frames i).childrenThisEpisode = (st.frames i).childrenThisEpisode := rfl
@[simp] lemma frame_children_refresh (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).childrenThisEpisode = (st.frames i).childrenThisEpisode := by
  by_cases he : i ≤ st.top <;> simp [refreshKeys,he]

@[simp] lemma frame_children_changeFrame (st : RecursiveState n) (j i : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) :
    ((changeFrame st j f).frames i).childrenThisEpisode =
      if i = j then (f (st.frames j)).childrenThisEpisode else (st.frames i).childrenThisEpisode := by
  by_cases he : i = j <;> simp [changeFrame,he]

@[simp] lemma frame_children_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (i : ℕ) :
    ((exteriorPush g α st t v).frames i).childrenThisEpisode = (st.frames i).childrenThisEpisode := by
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
  have hb (i : ℕ) : (base.frames i).childrenThisEpisode = (st.frames i).childrenThisEpisode := by
    by_cases hi : i ≤ st.top <;> simp [base,hi]
  have ha (i : ℕ) : (admitted.frames i).childrenThisEpisode = (st.frames i).childrenThisEpisode := by
    simp only [admitted,frame_children_changeFrame]
    split <;> simp_all [hb]
  have hc (i : ℕ) : (child.frames i).childrenThisEpisode = (st.frames i).childrenThisEpisode := by
    unfold child
    split
    · simp only [frame_children_changeFrame]
      split <;> simp_all [ha]
    · exact ha i
  have hf (i : ℕ) : (final.frames i).childrenThisEpisode = (st.frames i).childrenThisEpisode := by
    unfold final
    split <;> exact hc i
  unfold exteriorPush
  simp only [frame_children_debit,frame_children_refresh]
  change ((if relative st t v+h = 3*f.q/8 then final else base).frames i).childrenThisEpisode = _
  split
  · exact hf i
  · exact hb i

lemma child_counter_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hi : ChildCounterInvariant st) : ChildCounterInvariant (exteriorPush g α st t v) := by
  apply child_counter_transport st _ hi
  · exact frame_children_exterior g α st t v
  · exact frame_pc_exterior g α st t v
  · simp [exteriorPush,refreshKeys,debit,changeFrame] <;> (try split_ifs) <;> rfl

lemma child_counter_PC (st : RecursiveState n) (pc : NormalizePC) (hi : ChildCounterInvariant st)
    (hp : pc = .fullSolve ∨ pc = .normalize → (st.frames st.top).childrenThisEpisode = 0) :
    ChildCounterInvariant (changePC st pc) := by
  refine ⟨?_,hi.2⟩
  intro i
  by_cases he : i = st.top
  · subst i
    simpa [changePC,changeFrame] using And.intro (hi.1 st.top).1 hp
  · simpa [changePC,changeFrame,he] using hi.1 i

lemma child_counter_finish (st : RecursiveState n) (hi : ChildCounterInvariant st) :
    ChildCounterInvariant (finishEpisode st) := by
  refine ⟨?_,?_⟩
  · intro i
    by_cases he : i = st.top <;> simpa [finishEpisode,changeFrame,he] using hi.1 i
  · intro id k hk
    by_cases he : id = (st.frames st.top).id
    · subst id
      simp only [finishEpisode,changeFrame,Function.update_self,List.mem_append,List.mem_singleton] at hk
      rcases hk with hk|rfl
      · exact hi.2 _ _ hk
      · exact (hi.1 st.top).1
    · exact hi.2 id k (by simpa [finishEpisode,changeFrame,he] using hk)

lemma child_counter_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    ChildCounterInvariant (recursiveInit g s q ℓ schedule) := by
  constructor
  · intro i; by_cases he : i = 0 <;> simp [recursiveInit,freshFrame,emptyFrame,he]
  · simp [recursiveInit]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ChildCountStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma child_counter_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (pc : NormalizePC)
    (hi : ChildCounterInvariant st) (hp : pc ≠ .fullSolve ∧ pc ≠ .normalize) :
    ChildCounterInvariant (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  have hh : pc = .fullSolve ∨ pc = .normalize → (st.frames st.top).childrenThisEpisode = 0 := by
    rintro (h|h) <;> simp_all
  split
  · exact child_counter_PC _ pc hi hh
  · cases he : pendingPush st with
    | none => exact child_counter_PC _ pc hi hh
    | some p => obtain ⟨t,v⟩ := p; exact child_counter_exterior g α st t v hi

lemma child_counter_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : ChildCounterInvariant st) : ChildCounterInvariant (endCall g α st) := by
  unfold endCall
  dsimp only
  split <;> exact hi

lemma child_counter_new (st : RecursiveState n) (c : NormalizeFrame n)
    (hi : ChildCounterInvariant st) (hz : c.childrenThisEpisode = 0) :
    ChildCounterInvariant {st with top := st.top+1,frames := Function.update st.frames (st.top+1) c} := by
  refine ⟨?_,hi.2⟩
  intro i
  by_cases he : i = st.top+1
  · subst i; simp [hz]
  · simpa [he] using hi.1 i

lemma child_counter_child (st : RecursiveState n) (hi : ChildCounterInvariant st)
    (hp : (st.frames st.top).pc = .normalize) :
    ChildCounterInvariant (changeFrame st st.top (fun f =>
      {f with pc := .afterChild,childrenThisEpisode := f.childrenThisEpisode+1})) := by
  refine ⟨?_,hi.2⟩
  intro i
  by_cases he : i = st.top
  · subst i
    have hz := (hi.1 st.top).2 (Or.inr hp)
    simp [changeFrame,hz]
  · simpa [changeFrame,he] using hi.1 i

lemma child_counter_episode (st : RecursiveState n) (hi : ChildCounterInvariant st)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hz : (f (st.frames st.top)).childrenThisEpisode = 0) :
    ChildCounterInvariant (changeFrame st st.top f) := by
  refine ⟨?_,hi.2⟩
  intro i
  by_cases he : i = st.top
  · subst i; simp [changeFrame,hz]
  · simpa [changeFrame,he] using hi.1 i

lemma child_counter_metadata (st : RecursiveState n) (hi : ChildCounterInvariant st)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hc : (f (st.frames st.top)).childrenThisEpisode = (st.frames st.top).childrenThisEpisode)
    (hp : (f (st.frames st.top)).pc = .fullSolve ∨ (f (st.frames st.top)).pc = .normalize →
      (st.frames st.top).childrenThisEpisode = 0) :
    ChildCounterInvariant (changeFrame st st.top f) := by
  refine ⟨?_,hi.2⟩
  intro i
  by_cases he : i = st.top
  · subst i
    simpa [changeFrame,hc] using And.intro (hi.1 st.top).1 hp
  · simpa [changeFrame,he] using hi.1 i

set_option maxHeartbeats 1000000 in
lemma child_counter_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hi : ChildCounterInvariant st) :
    ChildCounterInvariant (recursiveStep m g s α ℓ schedule st) := by
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
    · exact child_counter_PC _ _ hi (by simp)
    · split
      · exact child_counter_drain g α st _ hi (by simp)
      · split <;> exact child_counter_PC _ _ hi (by simp)
  | beginEpisode =>
    simp only [hpc]
    apply child_counter_episode
    · exact hi
    · rfl
  | fullSolve =>
    simp only [hpc]
    split
    · exact child_counter_PC _ _ hi (by simp)
    · split
      · apply child_counter_PC _ _
        · exact child_counter_refresh g _ _ (child_counter_joint g α st _ hi)
        · intro _
          simpa [debit,refreshKeys,jointUpdate] using (hi.1 st.top).2 (Or.inl hpc)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact child_counter_PC _ _ hi (by simp)
    · split
      · exact child_counter_PC _ _ hi (by simp)
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild,childrenThisEpisode := fc.childrenThisEpisode+1})
        exact child_counter_new up c (child_counter_child u hi hpc) rfl
  | leafDrain =>
    simp only [hpc]
    split
    · exact child_counter_PC _ _ hi (by simp)
    · split
      · cases hp : pendingPush st with
        | none => exact child_counter_PC _ _ hi (by simp)
        | some p => obtain ⟨t,v⟩ := p; exact child_counter_exterior g α st t v hi
      · split
        · exact child_counter_PC _ _ hi (by simp)
        · split
          · apply child_counter_refresh
            apply child_counter_joint
            apply child_counter_transport st _ hi
            · intro i; by_cases he : i = st.top <;> simp [changeFrame,he]
            · intro i; by_cases he : i = st.top <;> simp [changeFrame,he]
            · rfl
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact child_counter_PC _ _ (child_counter_finish _ hi) (by simp)
    · split
      · exact child_counter_PC _ _ (child_counter_finish _ hi) (by simp)
      · exact child_counter_drain g α st _ hi (by simp)
  | finishEpisode =>
    simp only [hpc]
    split
    · exact child_counter_PC _ _ (child_counter_finish _ hi) (by simp)
    · split
      · exact child_counter_PC _ _ (child_counter_finish _ hi) (by simp)
      · apply child_counter_metadata
        · exact child_counter_finish _ (by exact hi)
        · rfl
        · simp only
          split_ifs <;> simp
  | restartDrain =>
    simp only [hpc]
    split
    · exact child_counter_PC _ _ hi (by simp)
    · split
      · exact child_counter_drain g α st _ hi (by simp)
      · apply child_counter_metadata
        · exact hi
        · rfl
        · simp
  | normal => simp only [hpc]; exact child_counter_end g α _ hi
  | interrupted => simp only [hpc]; exact child_counter_end g α _ hi

lemma child_counter_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ChildCounterInvariant (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using child_counter_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using child_counter_step m g s α ℓ schedule _ ih

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

-- Proof module: Solutions.LevelCounts

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma uniform_level_counts_and_closure :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : SolveModel) (ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule),
      0 < ε → ε ≤ 1 → ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α : ℝ),
      0 < α → α ≤ 1/2 → 0 < g.graph.degree s → ∀ (t id : ℕ) (info : CallInformation),
      let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
      (run t).information id=some info →
        ((run t).episodes id : ℝ) ≤ overhead C 4 ε ℓ*info.scale/info.block ∧
        ((run t).fullSolves id : ℝ) ≤ overhead C 4 ε ℓ*info.scale/info.block ∧
        (∀ k ∈ (run t).episodeChildCounts id, k ≤ 1) ∧
        (∀ i ≤ (run t).top, ((run t).frames i).id=id → ((run t).frames i).childrenThisEpisode ≤ 1) ∧
        ∃ t' ≥ t, id ∈ (run t').closed := by
  obtain ⟨Ce,hCe,hEp⟩ := uniform_episode_count
  obtain ⟨Cf,hCf,hFull⟩ := uniform_full_solve_count
  refine ⟨Ce+Cf,by positivity,?_⟩
  intro m ε ℓ schedule he he1 n g s α ha ha1 hs t id info run hi
  have hlegal := information_legal_run m g s α (rootThreshold ε ℓ) (root_threshold_unit ε ⟨he,he1⟩ ℓ) ℓ schedule t id info hi
  have hN : 0 ≤ info.scale := by linarith [hlegal.2.1]
  have hmonoE := overhead_mono ε ⟨he,he1⟩ ℓ 4 4 Ce (Ce+Cf) hCe.le (by linarith) le_rfl
  have hmonoF := overhead_mono ε ⟨he,he1⟩ ℓ 3 4 Cf (Ce+Cf) hCf.le (by linarith) (by omega)
  have hchildren := child_counter_run m g s α (rootThreshold ε ℓ) ℓ schedule t
  refine ⟨?_,?_,hchildren.2 id,?_,?_⟩
  · apply (hEp m n g s α ε ℓ schedule ⟨ha,ha1⟩ ⟨he,he1⟩ hs t id info hi).trans
    gcongr
  · apply (hFull m n g s α ε ℓ schedule ⟨ha,ha1⟩ ⟨he,he1⟩ hs t id info hi).trans
    gcongr
  · intro i _ _
    exact (hchildren.1 i).1
  · exact created_call_eventually_closed m g s α ε ⟨ha,ha1⟩ ⟨he,he1⟩ hs ℓ schedule t id info hi

end
end NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : SolveModel) (ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule),
      0 < ε → ε ≤ 1 → ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α : ℝ),
      0 < α → α ≤ 1/2 → 0 < g.graph.degree s → ∀ (t id : ℕ) (info : CallInformation),
      let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
      (run t).information id=some info →
        ((run t).episodes id : ℝ) ≤ overhead C 4 ε ℓ*info.scale/info.block ∧
        ((run t).fullSolves id : ℝ) ≤ overhead C 4 ε ℓ*info.scale/info.block ∧
        (∀ k ∈ (run t).episodeChildCounts id, k ≤ 1) ∧
        (∀ i ≤ (run t).top, ((run t).frames i).id=id → ((run t).frames i).childrenThisEpisode ≤ 1) ∧
        ∃ t' ≥ t, id ∈ (run t').closed := by
  exact uniform_level_counts_and_closure
