-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_restart_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:27:31.695813+00:00
-- url     : https://prove2.me/submissions/d233e773-2729-4be1-9c18-42f45168ae54

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_stack_scales
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_call_metadata
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_call_history
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_full_call_production

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

abbrev budget_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_control_parameters m n g s α q ℓ schedule t).2.1

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

abbrev full_call_production_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a ≤ b)
    (ha : fullSolveEvent g (recursiveRun m g s α q ℓ schedule a) id)
    (hb : fullSolveEvent g (recursiveRun m g s α q ℓ schedule b) id) :=
  NearlyOptimalPPR.Computation.recursive_full_call_production m n g s α q hα hq hs ℓ schedule a b id hab ha hb

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RestartPCProjection
set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}
@[simp] lemma pc_finish_frame (st : RecursiveState n) (j : ℕ) :
    ((finishEpisode st).frames j).pc=(st.frames j).pc := by
  simp only [finishEpisode,frame_pc_changeFrame]
  split <;> simp_all
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

lemma production_nonnegative (g : InputGraph n) (α : ℝ) (hα : α ≤ 1) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hp : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st) (j : ℕ) :
    0 ≤ ownProduction g st j ∧ 0 ≤ incomingProduction g α st j ∧ 0 ≤ birthProduction g st j := by
  cases hh : stepProduction st with
  | none => simp [ownProduction,incomingProduction,birthProduction,hh]
  | some p =>
    obtain ⟨t,v⟩ := p
    have hδ := production_increment_nonnegative g st hreg hp hnum hkeys hiso t v hh
    have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
    have ht := (pending_push_member st t v (production_pending st t v hh)).1
    have hq := (hp t ht).1.le
    unfold ownProduction incomingProduction birthProduction
    simp only [hh]
    constructor
    · split <;> positivity
    · constructor
      · split
        · exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hα) hd) hδ
        · exact le_rfl
      · split <;> positivity

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetWProjection

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

@[simp] lemma chargeW_changeFrame (st : RecursiveState n) (k j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) :
    ((changeFrame st k f).frames j).W=if j=k then (f (st.frames k)).W else (st.frames j).W := by
  classical
  by_cases he : j=k <;> simp [changeFrame,he]
@[simp] lemma chargeW_PC (st : RecursiveState n) (pc : NormalizePC) (j : ℕ) :
    ((changePC st pc).frames j).W=(st.frames j).W := by
  classical
  by_cases he : j=st.top <;> simp [changePC,chargeW_changeFrame,he]
@[simp] lemma chargeW_debit (st : RecursiveState n) (k j : ℕ) (w : ℝ≥0∞) :
    ((debit st k w).frames j).W=(st.frames j).W := rfl
@[simp] lemma chargeW_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (j : ℕ) :
    ((refreshKeys g st T).frames j).W=(st.frames j).W := by
  classical
  by_cases he : j ≤ st.top <;> simp [refreshKeys,he]
@[simp] lemma chargeW_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (x : Fin n → ℝ) (j : ℕ) :
    ((jointUpdate g α st x).frames j).W=(st.frames j).W := by
  classical
  by_cases he : j ≤ st.top <;> simp [jointUpdate,he]
@[simp] lemma chargeW_finish (st : RecursiveState n) (j : ℕ) :
    ((finishEpisode st).frames j).W=(st.frames j).W := by
  classical
  unfold finishEpisode
  by_cases he : j=st.top <;> simp [chargeW_changeFrame,he]
@[simp] lemma chargeW_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ) :
    ((endCall g α st).frames j).W=(st.frames j).W := by
  classical
  unfold endCall
  dsimp only
  split <;> rfl
@[simp] lemma chargeW_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) (j : ℕ) :
    ((completeComponent m g s α st).frames j).W=(st.frames j).W := rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetCharges

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 2000000 in
lemma W_step_none_open (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top)
    (hb : BudgetInvariant st) (hopen : (st.frames j).openBudget = true)
    (hp : stepProduction st = none) :
    ((recursiveStep m g s α ℓ schedule st).frames j).W = (st.frames j).W := by
  classical
  have hnew : j ≠ st.top+1 := by omega
  have hbegin : j = st.top → (st.frames st.top).pc ≠ .beginEpisode := by
    intro he hpc
    have hh := hb j hj
    rw [he,hpc] at hh
    simp only [budgetPC] at hh
    rw [←he,hopen] at hh
    cases hh
  clear hb
  by_cases hd : st.done=true
  · simp only [recursiveStep,hd,ite_true]
  have hdf : st.done=false := Bool.eq_false_of_not_eq_true hd
  by_cases hc : componentComplete st
  · simp only [recursiveStep,hdf,Bool.false_eq_true,hc,ite_false,ite_true,chargeW_complete]
  by_cases hje : j=st.top
  all_goals
    cases hpend : pendingPush st with
    | none =>
      cases hpc : (st.frames st.top).pc <;>
        simp only [recursiveStep,hdf,Bool.false_eq_true,hc,ite_false,hpc,hpend] <;>
        (try split_ifs) <;>
        simp_all only [chargeW_PC,chargeW_debit,chargeW_refresh,chargeW_joint,chargeW_finish,
          chargeW_end,chargeW_complete,chargeW_changeFrame,Function.update_of_ne hnew,
          Function.update_self,hje,if_pos,if_neg] <;>
        (try simp_all [stepProduction,drainProduction,hdf,hc,hpc,hpend])
    | some p =>
      obtain ⟨t,v⟩ := p
      cases hpc : (st.frames st.top).pc <;>
        simp only [recursiveStep,hdf,Bool.false_eq_true,hc,ite_false,hpc,hpend] <;>
        (try split_ifs) <;>
        simp_all only [chargeW_PC,chargeW_debit,chargeW_refresh,chargeW_joint,chargeW_finish,
          chargeW_end,chargeW_complete,chargeW_changeFrame,Function.update_of_ne hnew,
          Function.update_self,hje,if_pos,if_neg] <;>
        (try simp_all [stepProduction,drainProduction,hdf,hc,hpc,hpend])

lemma W_step_open (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top)
    (hb : BudgetInvariant st) (hopen : (st.frames j).openBudget = true) :
    ((recursiveStep m g s α ℓ schedule st).frames j).W = (st.frames j).W+
      incomingProduction g α st j+birthProduction g st j := by
  classical
  cases hh : stepProduction st with
  | none => rw [W_step_none_open m g s α ℓ schedule st j hj hb hopen hh]; simp [incomingProduction,birthProduction,hh]
  | some p =>
    obtain ⟨t,v⟩ := p
    rw [production_push m g s α ℓ schedule st t v hh]
    have hw := (exterior_budget_fields g α st t v j hj).2
    unfold incomingProduction birthProduction pushIncrement
    rw [hh]
    by_cases he : t = j
    · subst t
      convert hw using 1 <;> simp [hopen,birthAllowance] <;> split_ifs <;> ring
    · have he' : j ≠ t := Ne.symm he
      simpa [hopen,he,he'] using hw

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

-- Proof module: Solutions.RestartEntry

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma exterior_pc (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t j : ℕ) (v : Fin n) : ((exteriorPush g α st t v).frames j).pc=(st.frames j).pc :=
  congrArg (fun z => z.2.2.2.1) (exterior_parameters g α st t v j)

set_option maxHeartbeats 3000000 in
lemma restart_frame_entry (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top)
    (hp : (st.frames j).pc ≠ .restartDrain)
    (hn : ((recursiveStep m g s α ℓ schedule st).frames j).pc = .restartDrain) :
    j=st.top ∧ exhausted st j ∧
      ((st.frames j).pc=.afterChild ∨ (st.frames j).pc=.finishEpisode) := by
  have hnew : j ≠ st.top+1 := by omega
  by_cases hd : st.done=true
  · simp [recursiveStep,hd,hp] at hn
  by_cases hc : componentComplete st
  · simp [recursiveStep,hd,hc,hp] at hn
  simp only [recursiveStep,hd,ite_false,hc] at hn
  cases hpc : (st.frames st.top).pc <;>
    simp only [hpc] at hn <;>
    (try split_ifs at hn) <;>
    simp_all only [frame_pc_debit,frame_pc_refresh,frame_pc_joint,frame_pc_exterior,
      frame_pc_changeFrame,existing_pc_end,existing_pc_complete,pc_finish_frame,
      changePC,Function.update_apply,top_debit,top_finish] <;>
    (try split_ifs at hn) <;> (try simp_all) <;>
    cases hpend : pendingPush st <;> (try simp_all) <;>
    (try split_ifs at hn) <;> simp_all

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetFlagProjection

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}
open scoped ENNReal

@[simp] lemma flag_debit (st : RecursiveState n) (j i : ℕ) (w : ℝ≥0∞) :
    ((debit st j w).frames i).openBudget=(st.frames i).openBudget := rfl
@[simp] lemma flag_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) (i : ℕ) :
    ((jointUpdate g α st h).frames i).openBudget=(st.frames i).openBudget := by
  by_cases hi : i ≤ st.top <;> simp [jointUpdate,hi]
@[simp] lemma flag_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).openBudget=(st.frames i).openBudget := by
  by_cases hi : i ≤ st.top <;> simp [refreshKeys,hi]
@[simp] lemma flag_PC (st : RecursiveState n) (pc : NormalizePC) (i : ℕ) :
    ((changePC st pc).frames i).openBudget=(st.frames i).openBudget := by
  by_cases he : i=st.top <;> simp [changePC,changeFrame,he]
@[simp] lemma flag_changeFrame (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) (i : ℕ) :
    ((changeFrame st j f).frames i).openBudget=
      if i=j then (f (st.frames j)).openBudget else (st.frames i).openBudget := by
  by_cases he : i=j <;> simp [changeFrame,he]
@[simp] lemma flag_finish (st : RecursiveState n) (i : ℕ) :
    ((finishEpisode st).frames i).openBudget=if i=st.top then false else (st.frames i).openBudget := by
  simp only [finishEpisode,flag_changeFrame]
@[simp] lemma flag_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (i : ℕ) :
    ((endCall g α st).frames i).openBudget=(st.frames i).openBudget := by
  unfold endCall
  dsimp only
  split <;> rfl
@[simp] lemma flag_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (i : ℕ) :
    ((completeComponent m g s α st).frames i).openBudget=(st.frames i).openBudget := rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LastReset

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma last_reset_before (B : ℕ → Bool) (W : ℕ → ℝ) (a p : ℕ) (hap : a ≤ p)
    (hWa : W a=0) (hBp : B p=true)
    (hreset : ∀ k, a ≤ k → k < p → B k=false → B (k+1)=true → W (k+1)=0) :
    ∃ A, a ≤ A ∧ A ≤ p ∧ W A=0 ∧ ∀ k, A ≤ k → k ≤ p → B k=true := by
  classical
  let S := (Finset.Icc a p).filter (fun k => B k=false)
  by_cases hS : S.Nonempty
  · let c := S.max' hS
    have hc : c ∈ S := Finset.max'_mem S hS
    obtain ⟨hcI,hBc⟩ := Finset.mem_filter.mp hc
    obtain ⟨hac,hcp⟩ := Finset.mem_Icc.mp hcI
    have hclt : c < p := by
      have hne : c ≠ p := by intro he; rw [he,hBp] at hBc; cases hBc
      omega
    have hafter : ∀ k, c+1 ≤ k → k ≤ p → B k=true := by
      intro k hck hkp
      cases hk : B k with
      | true => rfl
      | false =>
        have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hkp⟩,hk⟩
        have hkc : k ≤ c := Finset.le_max' S k hkS
        omega
    refine ⟨c+1,by omega,by omega,hreset c hac hclt hBc (hafter (c+1) le_rfl (by omega)),?_⟩
    exact hafter
  · refine ⟨a,le_rfl,hap,hWa,?_⟩
    intro k hak hkp
    cases hk : B k with
    | true => rfl
    | false =>
      apply False.elim
      apply hS
      exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hak,hkp⟩,hk⟩⟩

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

-- Proof module: Solutions.ChargeIntervals

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma W_interval_charges (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top ∧
      ((recursiveRun m g s α q ℓ schedule k).frames j).openBudget = true) :
    (∑ k ∈ Finset.range (b-a), (incomingProduction g α (recursiveRun m g s α q ℓ schedule (a+k)) j+
      birthProduction g (recursiveRun m g s α q ℓ schedule (a+k)) j)) =
      ((recursiveRun m g s α q ℓ schedule b).frames j).W-
        ((recursiveRun m g s α q ℓ schedule a).frames j).W := by
  have hs : (∑ k ∈ Finset.range (b-a), (incomingProduction g α (recursiveRun m g s α q ℓ schedule (a+k)) j+
      birthProduction g (recursiveRun m g s α q ℓ schedule (a+k)) j)) =
      ∑ k ∈ Finset.range (b-a), (((recursiveRun m g s α q ℓ schedule (a+k+1)).frames j).W-
        ((recursiveRun m g s α q ℓ schedule (a+k)).frames j).W) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkt : a+k < b := by have := Finset.mem_range.mp hk; omega
    obtain ⟨hj,hb⟩ := hopen (a+k) (by omega) hkt
    have hh := W_step_open m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+k)) j hj
      (budget_run m g s α q ℓ schedule (a+k)) hb
    have hstep : ((recursiveRun m g s α q ℓ schedule (a+k+1)).frames j).W =
        ((recursiveRun m g s α q ℓ schedule (a+k)).frames j).W+
          incomingProduction g α (recursiveRun m g s α q ℓ schedule (a+k)) j+
          birthProduction g (recursiveRun m g s α q ℓ schedule (a+k)) j := by
      simpa only [recursiveRun,Function.iterate_succ_apply'] using hh
    linarith
  rw [hs,offset_sum_difference (fun t => ((recursiveRun m g s α q ℓ schedule t).frames j).W) a (b-a),Nat.add_sub_of_le hab]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EpisodePayment

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma run_budget_floor (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (t j : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    j ≤ st.top → (st.frames j).openBudget = true →
      (st.frames j).q*(st.frames j).block ≤ (st.frames j).Q := by
  intro st hj hb
  have hp := parameters_run m g s α q hq ℓ schedule t j hj
  have hscale : ScaleInvariant st := scale_run m g s α q hq ℓ schedule t
  rw [hscale.1 j hj hb]
  exact mul_le_mul_of_nonneg_right (hp.2.2 hb) (by positivity)

lemma exhausted_episode_paid (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top ∧
      ((recursiveRun m g s α q ℓ schedule k).frames j).openBudget = true)
    (hjb : j ≤ (recursiveRun m g s α q ℓ schedule b).top)
    (hzero : ((recursiveRun m g s α q ℓ schedule a).frames j).W = 0)
    (hex : exhausted (recursiveRun m g s α q ℓ schedule b) j) :
    ((recursiveRun m g s α q ℓ schedule b).frames j).q*
        ((recursiveRun m g s α q ℓ schedule b).frames j).block ≤
      ∑ k ∈ Finset.range (b-a), (incomingProduction g α (recursiveRun m g s α q ℓ schedule (a+k)) j+
        birthProduction g (recursiveRun m g s α q ℓ schedule (a+k)) j) := by
  have hx : ((recursiveRun m g s α q ℓ schedule b).frames j).openBudget = true ∧
      ((recursiveRun m g s α q ℓ schedule b).frames j).Q ≤ ((recursiveRun m g s α q ℓ schedule b).frames j).W := hex
  have hfloor := run_budget_floor m g s α q hq ℓ schedule b j hjb hx.1
  rw [W_interval_charges m g s α q ℓ schedule a b j hab hopen,hzero,sub_zero]
  exact hfloor.trans hx.2

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetReset

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma exterior_openBudget (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t j : ℕ) (v : Fin n) : ((exteriorPush g α st t v).frames j).openBudget=(st.frames j).openBudget :=
  congrArg (fun z => z.2.2.1) (exterior_parameters g α st t v j)

set_option maxHeartbeats 3000000 in
lemma budget_opens_zero (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top)
    (hp : (st.frames j).openBudget = false)
    (hn : ((recursiveStep m g s α ℓ schedule st).frames j).openBudget = true) :
    ((recursiveStep m g s α ℓ schedule st).frames j).W = 0 := by
  have hnew : j ≠ st.top+1 := by omega
  by_cases hd : st.done=true
  · simp [recursiveStep,hd,hp] at hn
  by_cases hc : componentComplete st
  · simp [recursiveStep,hd,hc,hp] at hn
  simp only [recursiveStep,hd,ite_false,hc] at hn ⊢
  cases hpc : (st.frames st.top).pc <;>
    simp only [hpc] at hn ⊢ <;>
    (try split_ifs at hn ⊢) <;>
    (try simp_all only [flag_debit,flag_refresh,flag_joint,flag_PC,flag_changeFrame,
      flag_finish,flag_end,flag_complete,exterior_openBudget,top_debit,top_finish,
      chargeW_debit,chargeW_PC,chargeW_changeFrame,chargeW_finish,Function.update_apply]) <;> (try contradiction) <;>
    (try split_ifs at hn ⊢) <;> (try simp_all) <;>
    cases hpend : pendingPush st <;> (try simp_all) <;>
    (try split_ifs at hn ⊢) <;> simp_all [debit,changeFrame]

lemma run_last_budget_reset (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a p j : ℕ) (hap : a ≤ p)
    (hopen : ∀ k, a ≤ k → k ≤ p → j ≤ (recursiveRun m g s α q ℓ schedule k).top)
    (hzero : ((recursiveRun m g s α q ℓ schedule a).frames j).W=0)
    (hbp : ((recursiveRun m g s α q ℓ schedule p).frames j).openBudget=true) :
    ∃ A, a ≤ A ∧ A ≤ p ∧ ((recursiveRun m g s α q ℓ schedule A).frames j).W=0 ∧
      ∀ k, A ≤ k → k ≤ p → ((recursiveRun m g s α q ℓ schedule k).frames j).openBudget=true := by
  apply last_reset_before (fun k => ((recursiveRun m g s α q ℓ schedule k).frames j).openBudget)
    (fun k => ((recursiveRun m g s α q ℓ schedule k).frames j).W) a p hap hzero hbp
  intro k hak hkp hb hn
  simpa only [recursiveRun,Function.iterate_succ_apply'] using
    budget_opens_zero m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule k) j
      (hopen k hak hkp.le) hb (by simpa only [recursiveRun,Function.iterate_succ_apply'] using hn)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FirstEntry

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma first_entry_transition (P : ℕ → Prop) (a r : ℕ) (har : a ≤ r)
    (ha : ¬ P a) (hr : P r) :
    ∃ p, a ≤ p ∧ p < r ∧ ¬P p ∧ P (p+1) := by
  classical
  let S := (Finset.Icc a r).filter P
  have hS : S.Nonempty := ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨har,le_rfl⟩,hr⟩⟩
  let u := S.min' hS
  have hu := Finset.mem_filter.mp (Finset.min'_mem S hS)
  have hau : a ≤ u := (Finset.mem_Icc.mp hu.1).1
  have hur : u ≤ r := (Finset.mem_Icc.mp hu.1).2
  have hlt : a < u := by
    by_contra hn
    have he : u=a := by omega
    exact ha (he ▸ hu.2)
  refine ⟨u-1,by omega,by omega,?_,?_⟩
  · intro hp
    have hm : u-1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,hp⟩
    have hh : u ≤ u-1 := Finset.min'_le S (u-1) hm
    omega
  · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ u)] using hu.2

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FullSolveOrigin

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 3000000 in
lemma full_solve_step_origin (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hstack : StackInvariant st)
    (hvalid : (st.frames st.top).active ⊆ st.stored ∧ ∀ v ∈ (st.frames st.top).active, 0 < g.graph.degree v)
    (hrunning : (recursiveStep m g s α ℓ schedule st).done = false)
    (hfull : currentPC (recursiveStep m g s α ℓ schedule st) = .fullSolve) :
    (st.frames st.top).pc = .beginEpisode := by

  have hg := running_step_guards m g s α ℓ schedule st hrunning
  have hparent : st.top ≠ 0 → (st.frames (st.top-1)).pc = .afterChild := by
    intro hh
    exact hstack (st.top-1) (by omega)
  by_contra hn
  cases hpc : (st.frames st.top).pc <;>
    simp only [recursiveStep,hg.1,Bool.false_eq_true,ite_false,hg.2,hpc] at hfull <;>
    (try split_ifs at hfull) <;>
    (try simp_all only [currentPC,top_changePC,top_debit,top_finish,top_refresh,top_joint,top_changeFrame,
      top_end,top_exterior,frame_pc_changeFrame,frame_pc_debit,frame_pc_joint,frame_pc_refresh,
      frame_pc_exterior,pc_finish_frame,existing_pc_end,changePC,Function.update_apply,freshFrame]) <;>
    (try split_ifs at hfull) <;> (try simp_all) <;>
    cases hpend : pendingPush st <;> (try simp_all) <;>
    (try split_ifs at hfull) <;> (try simp_all) <;> (try contradiction)

lemma full_solve_run_origin (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ)
    (hrunning : (recursiveRun m g s α q ℓ schedule (t+1)).done = false)
    (hfull : currentPC (recursiveRun m g s α q ℓ schedule (t+1)) = .fullSolve) :
    currentPC (recursiveRun m g s α q ℓ schedule t) = .beginEpisode := by
  apply full_solve_step_origin m g s α ℓ schedule _ (stack_run m g s α q ℓ schedule t)
    (run_active_domain_valid m g s α q hq hs ℓ schedule t _ le_rfl)
  · simpa only [recursiveRun,Function.iterate_succ_apply'] using hrunning
  · simpa only [recursiveRun,Function.iterate_succ_apply'] using hfull

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

lemma full_solve_run_prior_data (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ)
    (hrunning : (recursiveRun m g s α q ℓ schedule (t+1)).done = false)
    (hfull : currentPC (recursiveRun m g s α q ℓ schedule (t+1)) = .fullSolve) :
    let before := recursiveRun m g s α q ℓ schedule t
    let next := recursiveRun m g s α q ℓ schedule (t+1)
    next.top = before.top ∧ (before.frames before.top).needFull = true ∧
      next.x = before.x ∧ (next.frames next.top).active = (before.frames before.top).active ∧
      (next.frames next.top).residual = (before.frames before.top).residual ∧
      (next.frames next.top).W = 0 := by
  intro before next
  have hpc := full_solve_run_origin m g s α q hq hs ℓ schedule t hrunning hfull
  have hstep : next = recursiveStep m g s α ℓ schedule before := by
    simp only [before,next,recursiveRun,Function.iterate_succ_apply']
  have hh := begin_episode_transition m g s α ℓ schedule before hpc (by rwa [←hstep])
  rw [←hstep] at hh
  have hneed : (before.frames before.top).needFull = true := by
    have hpf : (next.frames before.top).pc = .fullSolve := by
      rw [←hh.1]
      exact hfull
    rw [hh.2.2.2.2.2.2.2.2] at hpf
    cases hn : (before.frames before.top).needFull <;> simp_all
  refine ⟨hh.1,hneed,hh.2.1,?_,?_,?_⟩
  · rw [hh.1]; exact hh.2.2.1
  · rw [hh.1]; exact hh.2.2.2.1
  · rw [hh.1]; exact hh.2.2.2.2.2.2.1

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
  cases hpc : (st.frames st.top).pc <;>
    simp only [recursiveStep,hg.1,Bool.false_eq_true,ite_false,hg.2,hpc] at hfull <;>
    (try split_ifs at hfull) <;>
    (try simp_all only [currentPC,top_changePC,top_debit,top_finish,top_refresh,top_joint,top_changeFrame,
      top_end,top_exterior,frame_pc_changeFrame,frame_pc_debit,frame_pc_joint,frame_pc_refresh,
      frame_pc_exterior,pc_finish_frame,existing_pc_end,changePC,Function.update_apply,freshFrame]) <;>
    (try split_ifs at hfull) <;> (try simp_all) <;>
    cases hpend : pendingPush st <;> (try simp_all) <;>
    (try split_ifs at hfull) <;> (try simp_all) <;> (try contradiction)

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

-- Proof module: Solutions.FullEventSpacing

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma full_event_time_ge_two (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (he : fullSolveEvent g (recursiveRun m g s α q ℓ schedule t) id) : 2 ≤ t := by
  rcases he with ⟨hd,hcomp,hpc,hex,hvalid,hid⟩
  cases t with
  | zero => simp [recursiveRun,recursiveInit,freshFrame,emptyFrame] at hpc
  | succ t =>
    cases t with
    | zero =>
      have hp := full_solve_run_origin m g s α q hq hs ℓ schedule 0 hd hpc
      simp [currentPC,recursiveRun,recursiveInit,freshFrame,emptyFrame] at hp
    | succ t => omega

lemma full_event_gap (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ)
    (hab : a < b) (ha : fullSolveEvent g (recursiveRun m g s α q ℓ schedule a) id)
    (hb : fullSolveEvent g (recursiveRun m g s α q ℓ schedule b) id) : a+3 ≤ b := by
  rcases ha with ⟨hda,hcompa,hpca,hexa,hvala,hida⟩
  rcases hb with ⟨hdb,hcompb,hpcb,hexb,hvalb,hidb⟩
  by_contra hn
  have hcases : b=a+1 ∨ b=a+2 := by omega
  rcases hcases with h1|h2
  · subst b
    have hp := full_solve_run_origin m g s α q hq hs ℓ schedule a hdb hpcb
    change currentPC (recursiveRun m g s α q ℓ schedule a)=.fullSolve at hpca
    rw [hp] at hpca
    cases hpca
  · subst b
    have hdb' : (recursiveRun m g s α q ℓ schedule ((a+1)+1)).done=false := by simpa only [Nat.add_assoc] using hdb
    have hpcb' : currentPC (recursiveRun m g s α q ℓ schedule ((a+1)+1))=.fullSolve := by
      simpa only [currentPC,Nat.add_assoc] using hpcb
    have hp := full_solve_run_origin m g s α q hq hs ℓ schedule (a+1) hdb' hpcb'
    have hmidrunning : (recursiveRun m g s α q ℓ schedule (a+1)).done=false := by
      have hs' : recursiveRun m g s α q ℓ schedule ((a+1)+1) =
          recursiveStep m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+1)) := by
        simp only [recursiveRun,Function.iterate_succ_apply']
      exact (running_step_guards m g s α ℓ schedule _ (by rwa [←hs'])).1
    have hor := begin_episode_run_origin m g s α q ℓ schedule a hmidrunning hp
    change currentPC (recursiveRun m g s α q ℓ schedule a)=.fullSolve at hpca
    rw [hpca] at hor
    simp at hor

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FullRequestData

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
lemma full_event_request_data (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (he : fullSolveEvent g (recursiveRun m g s α q ℓ schedule t) id) :
    let last := recursiveRun m g s α q ℓ schedule t
    let old := recursiveRun m g s α q ℓ schedule (t-2)
    last.top=old.top ∧ (currentPC old=.initialDrain ∨ currentPC old=.restartDrain ∨ currentPC old=.finishEpisode) ∧
      (last.frames last.top).active=(old.frames old.top).active ∧
      (last.frames last.top).residual=(old.frames old.top).residual ∧
      frozenFrame (last.frames last.top)=frozenFrame (old.frames old.top) := by
  intro last old
  have ht := full_event_time_ge_two m g s α q hq hs ℓ schedule t id he
  let a := t-2
  let mid := recursiveRun m g s α q ℓ schedule (a+1)
  have htime : a+2=t := by dsimp [a]; omega
  have hstep1 : mid=recursiveStep m g s α ℓ schedule old := by
    simp only [mid,old,a,recursiveRun,Function.iterate_succ_apply']
  have hstep2 : last=recursiveStep m g s α ℓ schedule mid := by
    dsimp only [last]
    rw [←htime]
    rw [show a+2=(a+1)+1 by omega]
    simp only [last,mid,recursiveRun,Function.iterate_succ_apply']
  rcases he with ⟨hd,hcomp,hpc,hex,hvalid,hid⟩
  have hdmid : mid.done=false := (running_step_guards m g s α ℓ schedule mid (by rwa [←hstep2])).1
  have hsucc : a+1+1=t := by omega
  have hlastEq : recursiveRun m g s α q ℓ schedule (a+1+1)=last := by rw [hsucc]
  have hpcLast : currentPC last=.fullSolve := hpc
  have hpcmid : currentPC mid=.beginEpisode :=
    full_solve_run_origin m g s α q hq hs ℓ schedule (a+1)
      (by rw [hlastEq]; exact hd) (by rw [hlastEq]; exact hpcLast)
  have hentry := begin_entry_data m g s α ℓ schedule old (stack_run m g s α q ℓ schedule (t-2))
    (by rwa [←hstep1]) (by rwa [←hstep1])
  rw [←hstep1] at hentry
  have hprior := full_solve_run_prior_data m g s α q hq hs ℓ schedule (a+1)
    (by rw [hlastEq]; exact hd) (by rw [hlastEq]; exact hpcLast)
  rw [hlastEq] at hprior
  have hpriorTop : last.top=mid.top := hprior.1
  have hpriorH : (last.frames last.top).active=(mid.frames mid.top).active := hprior.2.2.2.1
  have hpriorR : (last.frames last.top).residual=(mid.frames mid.top).residual := hprior.2.2.2.2.1
  have htop : last.top=old.top := hpriorTop.trans hentry.1
  have hor := begin_episode_run_origin m g s α q ℓ schedule a hdmid hpcmid
  have hH : (last.frames last.top).active=(old.frames old.top).active := by
    rw [hpriorH,hentry.1]
    exact hentry.2.2.1
  have hR : (last.frames last.top).residual=(old.frames old.top).residual := by
    rw [hpriorR,hentry.1]
    exact hentry.2.2.2
  have hf1 := frozenFrame_step m g s α ℓ schedule old old.top le_rfl
  have hf2 := frozenFrame_step m g s α ℓ schedule mid old.top (by rw [hentry.1])
  rw [←hstep1] at hf1
  rw [←hstep2] at hf2
  refine ⟨htop,hor,hH,hR,?_⟩
  rw [htop]
  exact hf2.trans hf1

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

-- Proof module: Solutions.FullRequestClassification

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma full_events_same_level (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a ≤ b)
    (ha : fullSolveEvent g (recursiveRun m g s α q ℓ schedule a) id)
    (hb : fullSolveEvent g (recursiveRun m g s α q ℓ schedule b) id) :
    (recursiveRun m g s α q ℓ schedule a).top=(recursiveRun m g s α q ℓ schedule b).top := by
  have hinfo := (running_call_information m g s α q ℓ schedule b id hb.1 hb.2.2.2.2.2).1
  exact (running_call_prefix_parameters m g s α q ℓ schedule a b id _ hab hinfo ha.1 ha.2.2.2.2.2).1

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RestartPayment

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma full_event_zero_budget (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (he : fullSolveEvent g (recursiveRun m g s α q ℓ schedule t) id) :
    ((recursiveRun m g s α q ℓ schedule t).frames (recursiveRun m g s α q ℓ schedule t).top).W=0 := by
  have ht := full_event_time_ge_two m g s α q hq hs ℓ schedule t id he
  have heq : t-1+1=t := by omega
  have hh := full_solve_run_prior_data m g s α q hq hs ℓ schedule (t-1)
    (by simpa only [heq] using he.1) (by simpa only [currentPC,heq] using he.2.2.1)
  simpa only [heq] using hh.2.2.2.2.2

lemma restarted_full_event_paid (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ)
    (hab : a < b) (ha : fullSolveEvent g (recursiveRun m g s α q ℓ schedule a) id)
    (hb : fullSolveEvent g (recursiveRun m g s α q ℓ schedule b) id)
    (hr : currentPC (recursiveRun m g s α q ℓ schedule (b-2))=.restartDrain) :
    let run := recursiveRun m g s α q ℓ schedule
    let j := (run a).top
    ∃ A p, a ≤ A ∧ A ≤ p ∧ p < b ∧
      ((run a).frames j).q * ((run a).frames j).block ≤
        ∑ k ∈ Finset.range (p-A), (incomingProduction g α (run (A+k)) j+birthProduction g (run (A+k)) j) := by
  intro run j
  have hgap := full_event_gap m g s α q hq.le hs ℓ schedule a b id hab ha hb
  have hspan := full_solve_event_span m g s α q ℓ schedule a b id hab.le ha hb
  have hdata := full_event_request_data m g s α q hq.le hs ℓ schedule b id hb
  have hlevels := full_events_same_level m g s α q ℓ schedule a b id hab.le ha hb
  have hold : (run (b-2)).top=j := hdata.1.symm.trans hlevels.symm
  have hPr : ((run (b-2)).frames j).pc=.restartDrain := by
    change ((run (b-2)).frames (run (b-2)).top).pc=.restartDrain at hr
    rwa [hold] at hr
  have hPa : ((run a).frames j).pc ≠ .restartDrain := by
    change ((run a).frames (run a).top).pc ≠ .restartDrain
    rw [ha.2.2.1]
    decide
  obtain ⟨p,hap,hpr,hPp,hPn⟩ := first_entry_transition
    (fun t => ((run t).frames j).pc=.restartDrain) a (b-2) (by omega) hPa hPr
  have hjp : j ≤ (run p).top := (hspan p hap (by omega)).1
  have hstep : run (p+1)=recursiveStep m g s α ℓ schedule (run p) := by
    simp only [run,recursiveRun,Function.iterate_succ_apply']
  have hentry := restart_frame_entry m g s α ℓ schedule (run p) j hjp hPp (by rwa [←hstep])
  have hzero := full_event_zero_budget m g s α q hq.le hs ℓ schedule a id ha
  obtain ⟨A,haA,hAp,hWA,hBA⟩ := run_last_budget_reset m g s α q ℓ schedule a p j hap
    (fun k hak hkp => (hspan k hak (by omega)).1) hzero hentry.2.1.1
  have hpaid := exhausted_episode_paid m g s α q hq ℓ schedule A p j hAp
    (fun k hAk hkp => ⟨(hspan k (by omega) (by omega)).1,hBA k hAk hkp.le⟩)
    hjp hWA hentry.2.1
  have hf := frozenFrame_interval m g s α q ℓ schedule a p j hap
    (fun k hak hkp => (hspan k hak (by omega)).1)
  have hqeq : ((run p).frames j).q=((run a).frames j).q := congrArg Prod.fst hf
  have hbeq : ((run p).frames j).block=((run a).frames j).block := congrArg (fun z => z.2.2.1) hf
  refine ⟨A,p,haA,hAp,by omega,?_⟩
  rw [hqeq,hbeq] at hpaid
  exact hpaid

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DisjointAccounting

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {ι τ : Type*} [DecidableEq ι] [DecidableEq τ]

lemma paid_disjoint_sets_count (E : Finset ι) (S : ι → Finset τ) (U : Finset τ) (f : τ → ℝ) (δ : ℝ)
    (hdis : Set.PairwiseDisjoint (↑E : Set ι) S) (hsub : ∀ i ∈ E, S i ⊆ U)
    (hf : ∀ t ∈ U, 0 ≤ f t) (hpaid : ∀ i ∈ E, δ ≤ ∑ t ∈ S i, f t) :
    δ*(E.card : ℝ) ≤ ∑ t ∈ U, f t := by
  classical
  have hUnion : E.biUnion S ⊆ U := by
    intro t ht
    obtain ⟨i,hi,ht⟩ := Finset.mem_biUnion.mp ht
    exact hsub i hi ht
  calc
    _ = ∑ i ∈ E, δ := by simp [mul_comm]
    _ ≤ ∑ i ∈ E, ∑ t ∈ S i, f t := Finset.sum_le_sum hpaid
    _ = ∑ t ∈ E.biUnion S, f t := by rw [Finset.sum_biUnion hdis]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hUnion (fun t ht _ => hf t ht)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EventEnumeration

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma increasing_intervals_disjoint (τ : ℕ → ℕ) (hτ : StrictMono τ) :
    Set.PairwiseDisjoint (Set.univ : Set ℕ) (fun k => Finset.Ico (τ k) (τ (k+1))) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro t hti htj
  obtain ⟨hi1,hi2⟩ := Finset.mem_Ico.mp hti
  obtain ⟨hj1,hj2⟩ := Finset.mem_Ico.mp htj
  rcases lt_or_gt_of_ne hij with hh|hh
  · have hm : τ (i+1) ≤ τ j := hτ.monotone (show i+1 ≤ j by omega)
    exact (not_le_of_gt hi2) (hm.trans hj1)
  · have hm : τ (j+1) ≤ τ i := hτ.monotone (show j+1 ≤ i by omega)
    exact (not_le_of_gt hj2) (hm.trans hi1)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.IntervalAccounting

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma offset_sum_eq_Ico (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (∑ k ∈ Finset.range (b-a), f (a+k))=∑ k ∈ Finset.Ico a b, f k := by
  rw [Finset.sum_Ico_eq_sum_range]

lemma paid_subinterval_local_count (E : Finset ℕ) (τ A p : ℕ → ℕ) (f : ℕ → ℝ) (δ R : ℝ) (L T : ℕ)
    (hτ : StrictMono τ) (hL : ∀ i ∈ E, L ≤ τ i) (hbound : ∀ i ∈ E, τ (i+1) ≤ T)
    (hA : ∀ i ∈ E, τ i ≤ A i) (hp : ∀ i ∈ E, A i ≤ p i ∧ p i ≤ τ (i+1))
    (hf : ∀ t, L ≤ t → t < T → 0 ≤ f t)
    (hpaid : ∀ i ∈ E, δ ≤ ∑ k ∈ Finset.range (p i-A i), f (A i+k))
    (hR : (∑ t ∈ Finset.Ico L T, f t) ≤ R) : δ*(E.card : ℝ) ≤ R := by
  have hdis : Set.PairwiseDisjoint (↑E : Set ℕ) (fun i => Finset.Ico (A i) (p i)) := by
    intro i hi j hj hij
    have hh := increasing_intervals_disjoint τ hτ (Set.mem_univ i) (Set.mem_univ j) hij
    apply hh.mono
    · intro t ht
      obtain ⟨ha,hp'⟩ := Finset.mem_Ico.mp ht
      exact Finset.mem_Ico.mpr ⟨(hA i hi).trans ha,hp'.trans_le (hp i hi).2⟩
    · intro t ht
      obtain ⟨ha,hp'⟩ := Finset.mem_Ico.mp ht
      exact Finset.mem_Ico.mpr ⟨(hA j hj).trans ha,hp'.trans_le (hp j hj).2⟩
  apply le_trans (paid_disjoint_sets_count E (fun i => Finset.Ico (A i) (p i)) (Finset.Ico L T) f δ hdis ?_ ?_ ?_) hR
  · intro i hi t ht
    exact Finset.mem_Ico.mpr ⟨(hL i hi).trans ((hA i hi).trans (Finset.mem_Ico.mp ht).1),
      (Finset.mem_Ico.mp ht).2.trans_le ((hp i hi).2.trans (hbound i hi))⟩
  · intro t ht; exact hf t (Finset.mem_Ico.mp ht).1 (Finset.mem_Ico.mp ht).2
  · intro i hi
    rw [←offset_sum_eq_Ico f (A i) (p i) (hp i hi).1]
    exact hpaid i hi

lemma paid_exists_subinterval_count (E : Finset ℕ) (τ : ℕ → ℕ) (f : ℕ → ℝ) (δ R : ℝ) (L T : ℕ)
    (hτ : StrictMono τ) (hL : ∀ i ∈ E, L ≤ τ i) (hbound : ∀ i ∈ E, τ (i+1) ≤ T)
    (hf : ∀ t, L ≤ t → t < T → 0 ≤ f t)
    (hpaid : ∀ i ∈ E, ∃ A p, τ i ≤ A ∧ A ≤ p ∧ p ≤ τ (i+1) ∧
      δ ≤ ∑ k ∈ Finset.range (p-A), f (A+k))
    (hR : (∑ t ∈ Finset.Ico L T, f t) ≤ R) : δ*(E.card : ℝ) ≤ R := by
  classical
  have hall : ∀ i, ∃ A p, i ∈ E → τ i ≤ A ∧ A ≤ p ∧ p ≤ τ (i+1) ∧
      δ ≤ ∑ k ∈ Finset.range (p-A), f (A+k) := by
    intro i
    by_cases hi : i ∈ E
    · obtain ⟨A,p,hh⟩ := hpaid i hi
      exact ⟨A,p,fun _ => hh⟩
    · exact ⟨0,0,fun hh => False.elim (hi hh)⟩
  choose A p hAp using hall
  exact paid_subinterval_local_count E τ A p f δ R L T hτ hL hbound
    (fun i hi => (hAp i hi).1)
    (fun i hi => ⟨(hAp i hi).2.1,(hAp i hi).2.2.1⟩) hf
    (fun i hi => (hAp i hi).2.2.2) hR

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolveCountAlgebra

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma paid_scale_count (q b N A M : ℝ) (hq : 0 < q) (hb : 0 < b)
    (hpaid : q*b*M ≤ A*q*N) : M ≤ A*N/b := by
  have hh : M ≤ (A*q*N)/(q*b) := (le_div_iff₀ (mul_pos hq hb)).mpr (by nlinarith)
  calc
    _ ≤ _ := hh
    _ = _ := by field_simp

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RestartCounts

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma restart_origin_count (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (τ : ℕ → ℕ) (hτ : StrictMono τ) (T id : ℕ)
    (hfull : ∀ i ≤ T, fullSolveEvent g (recursiveRun m g s α q ℓ schedule (τ i)) id)
    (E : Finset ℕ) (hE : E ⊆ Finset.range T)
    (hrestart : ∀ i ∈ E, currentPC (recursiveRun m g s α q ℓ schedule (τ (i+1)-2))=.restartDrain) :
    let st := recursiveRun m g s α q ℓ schedule (τ 0)
    (E.card : ℝ) ≤ 2*(kappa ℓ 0 : ℝ)*(st.frames st.top).N/(st.frames st.top).block := by
  intro st
  let run := recursiveRun m g s α q ℓ schedule
  let j := st.top
  let f := st.frames j
  have hspan := full_solve_event_span m g s α q ℓ schedule (τ 0) (τ T) id
    (hτ.monotone (Nat.zero_le _)) (hfull 0 (Nat.zero_le _)) (hfull T le_rfl)
  have hparams := parameters_run m g s α q hq ℓ schedule (τ 0) j le_rfl
  have hb : (0 : ℝ) < f.block := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hparams.2.1
  have hR := full_call_production_bound m g s α q hα hq hs ℓ schedule (τ 0) (τ T) id
    (hτ.monotone (Nat.zero_le _)) (hfull 0 (Nat.zero_le _)) (hfull T le_rfl)
  have hpaid : f.q*f.block*(E.card : ℝ) ≤ 2*(kappa ℓ 0 : ℝ)*f.q*f.N := by
    apply paid_exists_subinterval_count E τ
      (fun t => incomingProduction g α (run t) j+birthProduction g (run t) j)
      (f.q*f.block) (2*(kappa ℓ 0 : ℝ)*f.q*f.N) (τ 0) (τ T) hτ
      (fun i _ => hτ.monotone (Nat.zero_le _))
      (fun i hi => hτ.monotone (Nat.succ_le_of_lt (Finset.mem_range.mp (hE hi)))) ?_ ?_ hR
    · intro t _ _
      have hn := production_nonnegative g α hα.2.le (run t)
        (region_run m g s α q ℓ schedule t) (parameters_run m g s α q hq ℓ schedule t)
        (numerical_run m g s α q hα hq hs ℓ schedule t) (keys_run m g s α q hq.le ℓ schedule t)
        (isolate_run m g s α q hs ℓ schedule t) j
      exact add_nonneg hn.2.1 hn.2.2
    · intro i hi
      have hiT : i < T := Finset.mem_range.mp (hE hi)
      have hai := hfull i hiT.le
      have hbi := hfull (i+1) (by omega)
      have hpay := restarted_full_event_paid m g s α q hq hs ℓ schedule (τ i) (τ (i+1)) id
        (hτ (Nat.lt_succ_self i)) hai hbi (hrestart i hi)
      obtain ⟨A,p,hA,hAp,hpb,hpay⟩ := hpay
      have hlevel := full_events_same_level m g s α q ℓ schedule (τ 0) (τ i) id
        (hτ.monotone (Nat.zero_le _)) (hfull 0 (Nat.zero_le _)) hai
      have hj : (run (τ i)).top=j := hlevel.symm
      have hf := frozenFrame_interval m g s α q ℓ schedule (τ 0) (τ i) j
        (hτ.monotone (Nat.zero_le _)) (fun k h0k hki =>
          (hspan k h0k (hki.le.trans (hτ.monotone hiT.le))).1)
      have hqeq : ((run (τ i)).frames j).q=f.q := congrArg Prod.fst hf
      have hbeq : ((run (τ i)).frames j).block=f.block := congrArg (fun z => z.2.2.1) hf
      change ((run (τ i)).frames (run (τ i)).top).q * ((run (τ i)).frames (run (τ i)).top).block ≤ _ at hpay
      rw [hj,hqeq,hbeq] at hpay
      refine ⟨A,p,hA,hAp,hpb.le,?_⟩
      simpa only [hj] using hpay
  exact paid_scale_count f.q f.block f.N (2*(kappa ℓ 0 : ℝ)) (E.card : ℝ) hparams.1 hb hpaid

end
end NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal

theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (τ : ℕ → ℕ) (hτ : StrictMono τ) (T id : ℕ)
    (hfull : ∀ i ≤ T, fullSolveEvent g (recursiveRun m g s α q ℓ schedule (τ i)) id)
    (E : Finset ℕ) (hE : E ⊆ Finset.range T)
    (hrestart : ∀ i ∈ E, currentPC (recursiveRun m g s α q ℓ schedule (τ (i+1)-2))=.restartDrain) :
    let st := recursiveRun m g s α q ℓ schedule (τ 0)
    (E.card : ℝ) ≤ 2*(kappa ℓ 0 : ℝ)*(st.frames st.top).N/(st.frames st.top).block := by
  exact restart_origin_count m g s α q hα hq hs ℓ schedule τ hτ T id hfull E hE hrestart
