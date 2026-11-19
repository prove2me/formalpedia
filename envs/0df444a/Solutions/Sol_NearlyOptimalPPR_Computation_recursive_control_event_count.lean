-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_control_event_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:01:29.229013+00:00
-- url     : https://prove2.me/submissions/f7da49a0-8195-46c2-90cf-d4833062076a

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
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

abbrev budget_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_control_parameters m n g s α q ℓ schedule t).2.1

abbrev stored_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_queue_domains m n g s α q ℓ schedule t).2.2 hq hs

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

-- Proof module: Solutions.CounterEvents

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma counters_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    (exteriorPush g α st t v).episodes = st.episodes ∧ (exteriorPush g α st t v).fullSolves = st.fullSolves := by
  simp [exteriorPush,changeFrame,refreshKeys,debit] <;> (try split_ifs) <;> (first | rfl | exact ⟨rfl,rfl⟩)

@[simp] lemma fullSolves_changeFrame (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).fullSolves = st.fullSolves := rfl

@[simp] lemma fullSolves_PC (st : RecursiveState n) (pc : NormalizePC) :
    (changePC st pc).fullSolves = st.fullSolves := rfl

@[simp] lemma fullSolves_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    (debit st j w).fullSolves = st.fullSolves := rfl

@[simp] lemma fullSolves_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).fullSolves = st.fullSolves := rfl

@[simp] lemma fullSolves_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    (jointUpdate g α st h).fullSolves = st.fullSolves := rfl

@[simp] lemma fullSolves_finish (st : RecursiveState n) :
    (finishEpisode st).fullSolves = st.fullSolves := rfl

@[simp] lemma fullSolves_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    (endCall g α st).fullSolves = st.fullSolves := by unfold endCall; dsimp only; split <;> rfl

@[simp] lemma fullSolves_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) :
    (completeComponent m g s α st).fullSolves = st.fullSolves := rfl

@[simp] lemma episodes_changeFrame (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).episodes = st.episodes := rfl

@[simp] lemma episodes_PC (st : RecursiveState n) (pc : NormalizePC) :
    (changePC st pc).episodes = st.episodes := rfl

@[simp] lemma episodes_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    (debit st j w).episodes = st.episodes := rfl

@[simp] lemma episodes_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).episodes = st.episodes := rfl

@[simp] lemma episodes_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    (jointUpdate g α st h).episodes = st.episodes := rfl

@[simp] lemma episodes_finish (st : RecursiveState n) :
    (finishEpisode st).episodes = st.episodes := rfl

@[simp] lemma episodes_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    (endCall g α st).episodes = st.episodes := by unfold endCall; dsimp only; split <;> rfl

@[simp] lemma episodes_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) :
    (completeComponent m g s α st).episodes = st.episodes := rfl

set_option maxHeartbeats 2000000 in
lemma episodes_step_event (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (id : ℕ) :
    (recursiveStep m g s α ℓ schedule st).episodes id = st.episodes id+if episodeEvent st id then 1 else 0 := by
  cases hd : st.done with
  | true => simp [recursiveStep,episodeEvent,hd]
  | false =>
    by_cases hc : componentComplete st
    · simp [recursiveStep,episodeEvent,hd,hc]
    by_cases hid : (st.frames st.top).id = id
    all_goals
      cases hpend : pendingPush st with
      | none =>
        cases hpc : (st.frames st.top).pc <;>
          simp [recursiveStep,episodeEvent,hd,hc,hpc,hpend,hid,Function.update_apply] <;>
          (try split_ifs) <;> simp_all <;>
          first | exact Ne.symm hid | exact Function.update_of_ne (Ne.symm hid) _ _
      | some p =>
        obtain ⟨t,v⟩ := p
        have hcounter := (counters_exterior g α st t v).1
        cases hpc : (st.frames st.top).pc <;>
          simp [recursiveStep,episodeEvent,hd,hc,hpc,hpend,hid,Function.update_apply,hcounter] <;>
          (try split_ifs) <;> simp_all <;>
          first | exact Ne.symm hid | exact Function.update_of_ne (Ne.symm hid) _ _


lemma episodes_run_events (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) :
    (recursiveRun m g s α q ℓ schedule T).episodes id =
      ((Finset.range T).filter (fun k => episodeEvent (recursiveRun m g s α q ℓ schedule k) id)).card := by
  induction T with
  | zero => simp [recursiveRun,recursiveInit]
  | succ T ih =>
    have hh := episodes_step_event m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule T) id
    rw [show recursiveRun m g s α q ℓ schedule (T+1) = recursiveStep m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule T) by
      simp only [recursiveRun,Function.iterate_succ_apply'],hh,ih]
    by_cases he : episodeEvent (recursiveRun m g s α q ℓ schedule T) id <;>
      simp [Finset.range_add_one,Finset.filter_insert,he]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControlRank

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma controlRank_bounds (pc : NormalizePC) : 1 ≤ controlRank pc ∧ controlRank pc ≤ 9 := by
  cases pc <;> decide

lemma callControlPotential_bound (st : RecursiveState n) (j id : ℕ) : callControlPotential st j id ≤ 9 := by
  unfold callControlPotential
  split
  · omega
  · exact (controlRank_bounds _).2

lemma anyExhausted_split (st : RecursiveState n) :
    anyExhausted st ↔ ancestorExhausted st ∨ exhausted st st.top := by
  constructor
  · rintro ⟨i,hi,hex⟩
    by_cases hh : i < st.top
    · exact Or.inl ⟨i,hh,hex⟩
    · have he : i=st.top := by omega
      exact Or.inr (he ▸ hex)
  · rintro (⟨i,hi,hex⟩|hex)
    · exact ⟨i,hi.le,hex⟩
    · exact ⟨st.top,le_rfl,hex⟩

set_option maxHeartbeats 1500000 in
lemma ancestor_pc_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (j : ℕ) (hj : j < st.top) :
    ((recursiveStep m g s α ℓ schedule st).frames j).pc=(st.frames j).pc := by
  by_cases hd : st.done=true
  · simp [recursiveStep,hd]
  have hjle : j ≤ st.top := hj.le
  have hje : j ≠ st.top := ne_of_lt hj
  have hnew : j ≠ st.top+1 := by omega
  cases hp : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hp,hje,hnew,hjle,hd] <;> (try split_ifs) <;>
      simp_all [changePC,changeFrame,finishEpisode,debit,refreshKeys,jointUpdate,endCall,completeComponent,hjle,hd]
  | some p =>
    obtain ⟨t,v⟩ := p
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hp,hje,hnew,hjle,hd] <;> (try split_ifs) <;>
      simp_all [changePC,changeFrame,finishEpisode,debit,refreshKeys,jointUpdate,endCall,completeComponent,hjle,hd]

lemma ancestor_control_nonincrease (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (j id : ℕ) (hj : j < st.top) :
    callControlPotential (recursiveStep m g s α ℓ schedule st) j id ≤ callControlPotential st j id := by
  by_cases hn : id ∈ (recursiveStep m g s α ℓ schedule st).closed
  · simp only [callControlPotential,hn,ite_true]
    omega
  · have ho : id ∉ st.closed := fun hh => hn (closed_step_monotone m g s α ℓ schedule st hh)
    simp only [callControlPotential,hn,ho,ite_false,ancestor_pc_step m g s α ℓ schedule st j hj]
    rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControlDrain

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma closed_pc_unexhausted (st : RecursiveState n) (hb : BudgetInvariant st)
    (hpc : budgetPC (st.frames st.top).pc=false) (hanc : ¬ancestorExhausted st) : ¬anyExhausted st := by
  have hop : (st.frames st.top).openBudget=false := (hb st.top le_rfl).trans hpc
  intro hh
  rcases anyExhausted_split st |>.mp hh with ha|he
  · exact hanc ha
  · rw [exhausted,hop] at he
    exact Bool.noConfusion he.1

lemma nonproducing_drain_empty (st : RecursiveState n)
    (hd : st.done=false) (hc : ¬componentComplete st) (hn : ¬anyExhausted st)
    (hp : stepProduction st=none)
    (hpc : (st.frames st.top).pc=.initialDrain ∨ (st.frames st.top).pc=.restartDrain ∨
      (st.frames st.top).pc=.leafDrain ∨ (st.frames st.top).pc=.afterChild) : pendingPush st=none := by
  have hanc : ¬ancestorExhausted st := fun ⟨i,hi,he⟩ => hn ⟨i,hi.le,he⟩
  have hown : ¬exhausted st st.top := fun he => hn ⟨st.top,le_rfl,he⟩
  cases hpend : pendingPush st with
  | none => rfl
  | some p =>
    obtain ⟨t,v⟩ := p
    rcases hpc with hpc|hpc|hpc|hpc <;>
      simp [stepProduction,drainProduction,hd,hc,hn,hanc,hown,hpc,hpend] at hp

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CurrentControlProgress

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 2000000 in
lemma current_control_progress (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hd : st.done=false) (hc : ¬componentComplete st) (hb : BudgetInvariant st) (hr : RegionInvariant st)
    (hvalid : (st.frames st.top).active ⊆ st.stored ∧ ∀ v ∈ (st.frames st.top).active, 0 < g.graph.degree v)
    (hp : stepProduction st=none) (hn : ¬cachedSolveEvent g st (st.frames st.top).id)
    (hbegin : (st.frames st.top).pc ≠ .beginEpisode) :
    callControlPotential (recursiveStep m g s α ℓ schedule st) st.top (st.frames st.top).id < controlRank (st.frames st.top).pc := by
  by_cases hclosed : (st.frames st.top).id ∈ (recursiveStep m g s α ℓ schedule st).closed
  · simp only [callControlPotential,hclosed,ite_true]
    exact lt_of_lt_of_le Nat.zero_lt_one (controlRank_bounds _).1
  simp only [callControlPotential,hclosed,ite_false]
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    by_cases hanc : ancestorExhausted st
    · simp [recursiveStep,hd,hc,hpc,hanc,changePC,changeFrame,debit,controlRank]
    · have hno := closed_pc_unexhausted st hb (by simp only [hpc,budgetPC]) hanc
      have hpend := nonproducing_drain_empty st hd hc hno hp (Or.inl hpc)
      simp [recursiveStep,hd,hc,hpc,hanc,hpend,changePC,changeFrame,debit,controlRank] <;>
        split_ifs <;> simp_all [changePC,changeFrame,debit,controlRank]
  | restartDrain =>
    by_cases hanc : ancestorExhausted st
    · simp [recursiveStep,hd,hc,hpc,hanc,changePC,changeFrame,debit,controlRank]
    · have hno := closed_pc_unexhausted st hb (by simp only [hpc,budgetPC]) hanc
      have hpend := nonproducing_drain_empty st hd hc hno hp (Or.inr (Or.inl hpc))
      simp [recursiveStep,hd,hc,hpc,hanc,hpend,changePC,changeFrame,debit,controlRank]
  | beginEpisode => exact False.elim (hbegin hpc)
  | fullSolve =>
    simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hc,hpc]
    split
    · simp [changePC,changeFrame,debit,controlRank]
    · try rw [if_pos hvalid]
      simp [changePC,changeFrame,debit,refreshKeys,jointUpdate,controlRank]
  | normalize =>
    simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hc,hpc]
    split
    · simp [changePC,changeFrame,debit,controlRank]
    · split
      · simp [changePC,changeFrame,debit,controlRank]
      · have hn : st.top ≠ st.top+1 := by omega
        simp [changeFrame,debit,controlRank,hn]
  | leafDrain =>
    by_cases hno : anyExhausted st
    · simp [recursiveStep,hd,hc,hpc,hno,changePC,changeFrame,debit,controlRank]
    · have hpend := nonproducing_drain_empty st hd hc hno hp (Or.inr (Or.inr (Or.inl hpc)))
      by_cases hhigh : (st.frames st.top).high=∅
      · simp [recursiveStep,hd,hc,hpc,hno,hpend,hhigh,changePC,changeFrame,debit,controlRank]
      · have hC : (st.frames st.top).cache ∪ (st.frames st.top).high ⊆ (st.frames st.top).active :=
          Finset.union_subset_iff.mpr ⟨(hr st.top le_rfl).2.2.2,(hr st.top le_rfl).2.2.1⟩
        have hvalidC : (st.frames st.top).cache ∪ (st.frames st.top).high ⊆ st.stored ∧
            ∀ v ∈ (st.frames st.top).cache ∪ (st.frames st.top).high, 0 < g.graph.degree v :=
          ⟨hC.trans hvalid.1,fun v hv => hvalid.2 v (hC hv)⟩
        exact False.elim (hn ⟨hd,hc,hpc,hno,hpend,hhigh,hvalidC,rfl⟩)
  | afterChild =>
    by_cases hanc : ancestorExhausted st
    · simp [recursiveStep,hd,hc,hpc,hanc,changePC,changeFrame,finishEpisode,debit,controlRank]
    · by_cases hex : exhausted st st.top
      · simp [recursiveStep,hd,hc,hpc,hanc,hex,changePC,changeFrame,finishEpisode,debit,controlRank]
      · have hno : ¬anyExhausted st := by rw [anyExhausted_split]; exact not_or.mpr ⟨hanc,hex⟩
        have hpend := nonproducing_drain_empty st hd hc hno hp (Or.inr (Or.inr (Or.inr hpc)))
        simp [recursiveStep,hd,hc,hpc,hanc,hex,hno,hpend,changePC,changeFrame,debit,controlRank]
  | finishEpisode =>
    simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hc,hpc]
    split
    · simp [changePC,changeFrame,finishEpisode,debit,controlRank]
    · split
      · simp [changePC,changeFrame,finishEpisode,debit,controlRank]
      · simp [changeFrame,finishEpisode,debit,controlRank] <;> split_ifs <;> simp [controlRank]
  | normal =>
    apply False.elim
    apply hclosed
    simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hc,hpc]
    unfold endCall
    dsimp only
    split <;> simp [debit]
  | interrupted =>
    apply False.elim
    apply hclosed
    simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hc,hpc]
    unfold endCall
    dsimp only
    split <;> simp [debit]

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

-- Proof module: Solutions.ControlUpdates

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma controlPotential_of_pc_same (st u : RecursiveState n) (j id : ℕ)
    (hclosed : st.closed ⊆ u.closed) (hpc : (u.frames j).pc=(st.frames j).pc) :
    callControlPotential u j id ≤ callControlPotential st j id := by
  by_cases hu : id ∈ u.closed
  · simp only [callControlPotential,hu,ite_true]
    omega
  · have hs : id ∉ st.closed := fun hh => hu (hclosed hh)
    simp only [callControlPotential,hu,hs,ite_false,hpc]
    rfl

lemma controlPotential_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t j id : ℕ) (v : Fin n) :
    callControlPotential (exteriorPush g α st t v) j id=callControlPotential st j id := by
  simp only [callControlPotential,(exterior_lifecycle g α st t v).2.2,frame_pc_exterior]

lemma cached_step_pc (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (id : ℕ)
    (he : cachedSolveEvent g st id) :
    ((recursiveStep m g s α ℓ schedule st).frames st.top).pc=(st.frames st.top).pc := by
  rcases he with ⟨hd,hcomp,hpc,hex,hpend,hhigh,hvalid,hid⟩
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hcomp,hpc,hex,hpend,Option.isSome_none,Bool.false_eq_true,hhigh]
  rw [if_pos hvalid]
  simp [changeFrame,jointUpdate,refreshKeys,debit,hpc]

lemma begin_control_allowance (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (id : ℕ)
    (hd : st.done=false) (hc : ¬componentComplete st) (hp : (st.frames st.top).pc=.beginEpisode)
    (hopen : id ∉ st.closed) :
    callControlPotential (recursiveStep m g s α ℓ schedule st) st.top id+1 ≤ callControlPotential st st.top id+7 := by
  have hpot : callControlPotential st st.top id=2 := by simp only [callControlPotential,hopen,ite_false,hp,controlRank]
  rw [hpot]
  by_cases hn : id ∈ (recursiveStep m g s α ℓ schedule st).closed
  · simp only [callControlPotential,hn,ite_true]
    omega
  simp only [callControlPotential,hn,ite_false]
  simp [recursiveStep,hd,hc,hp,changeFrame,debit,controlRank] <;> split_ifs <;> simp [controlRank]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ControlRunStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 2000000 in
lemma control_potential_run_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t j id : ℕ)
    (hd : (recursiveRun m g s α q ℓ schedule t).done=false)
    (hj : j ≤ (recursiveRun m g s α q ℓ schedule t).top)
    (hid : ((recursiveRun m g s α q ℓ schedule t).frames j).id=id) :
    let run := recursiveRun m g s α q ℓ schedule
    callControlPotential (run (t+1)) j id+(if controlEvent g (run t) id then 1 else 0) ≤
      callControlPotential (run t) j id+7*(if episodeEvent (run t) id then 1 else 0) := by
  intro run
  let st := run t
  have hj' : j ≤ st.top := hj
  have hstep : run (t+1)=recursiveStep m g s α ℓ schedule st := by
    simp only [run,st,recursiveRun,Function.iterate_succ_apply']
  have hopen : id ∉ st.closed := by
    have hh := running_open_not_closed_run m g s α q ℓ schedule t hd j hj
    rwa [hid] at hh
  have hcharge : (if controlEvent g st id then (1 : ℕ) else 0) ≤ 1 := by split <;> omega
  change callControlPotential (run (t+1)) j id+(if controlEvent g st id then 1 else 0) ≤
    callControlPotential st j id+7*(if episodeEvent st id then 1 else 0)
  rw [hstep]
  by_cases hc : componentComplete st
  · have hi : id ∈ (Finset.range (st.top+1)).image (fun i => (st.frames i).id) :=
      Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (Nat.lt_succ_of_le hj),hid⟩
    have hnew : id ∈ (recursiveStep m g s α ℓ schedule st).closed := by
      have hd' : st.done=false := hd
      simp [recursiveStep,hd',hc,completeComponent,debit,hi]
    simp only [callControlPotential,hnew,hopen,ite_true,ite_false]
    have hr := (controlRank_bounds (st.frames j).pc).1
    omega
  by_cases hje : j=st.top
  · subst j
    by_cases hb : (st.frames st.top).pc=.beginEpisode
    · have hep : episodeEvent st id := ⟨hd,hc,hb,hid⟩
      have hh := begin_control_allowance m g s α ℓ schedule st id hd hc hb hopen
      rw [if_pos hep]
      omega
    · by_cases hcached : cachedSolveEvent g st id
      · have hctrl : ¬controlEvent g st id := fun hh => hh.2.2.1 hcached
        rw [if_neg hctrl,add_zero]
        have hh := controlPotential_of_pc_same st (recursiveStep m g s α ℓ schedule st) st.top id
          (closed_step_monotone m g s α ℓ schedule st) (cached_step_pc m g s α ℓ schedule st id hcached)
        omega
      · cases hp : stepProduction st with
        | none =>
          have hn : ¬cachedSolveEvent g st (st.frames st.top).id := by rwa [hid]
          have hh := current_control_progress m g s α ℓ schedule st hd hc
            (budget_run m g s α q ℓ schedule t) (region_run m g s α q ℓ schedule t)
            (run_active_domain_valid m g s α q hq.le hs ℓ schedule t st.top le_rfl) hp hn hb
          rw [hid] at hh
          have hpot : callControlPotential st st.top id=controlRank (st.frames st.top).pc := by
            simp only [callControlPotential,hopen,ite_false]
          omega
        | some p =>
          obtain ⟨u,v⟩ := p
          have hctrl : ¬controlEvent g st id := by intro hh; have hx := hh.2.1; rw [hp] at hx; cases hx
          rw [if_neg hctrl,add_zero,production_push m g s α ℓ schedule st u v hp,controlPotential_exterior]
          omega
  · have hlt : j < st.top := by omega
    have hctrl : ¬controlEvent g st id := by
      intro hh
      have hcurrent : (st.frames st.top).id=id := by simpa only [if_neg hc] using hh.2.2.2
      have he := open_frame_ids_injective st (open_frame_information_run m g s α q ℓ schedule t)
        j st.top hj le_rfl (hid.trans hcurrent.symm)
      exact hje he
    rw [if_neg hctrl,add_zero]
    have hh := ancestor_control_nonincrease m g s α ℓ schedule st j id hlt
    omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RunningPrefix

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma running_prefix (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b : ℕ) (hab : a ≤ b)
    (hb : (recursiveRun m g s α q ℓ schedule b).done=false) :
    (recursiveRun m g s α q ℓ schedule a).done=false := by
  induction b generalizing a with
  | zero =>
    have ha : a=0 := by omega
    subst a
    exact hb
  | succ b ih =>
    by_cases he : a=b+1
    · simpa only [he] using hb
    · have hprev : (recursiveRun m g s α q ℓ schedule b).done=false := by
        apply (running_step_guards m g s α ℓ schedule _ ?_).1
        simpa only [recursiveRun,Function.iterate_succ_apply'] using hb
      exact ih a (by omega) hprev

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

-- Proof module: Solutions.AmortizedAccounting

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation

lemma amortized_interval_bound (E paid income : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hE : 0 ≤ E b)
    (hstep : ∀ k, a ≤ k → k < b → E (k+1)+paid k ≤ E k+income k) :
    (∑ k ∈ Finset.range (b-a), paid (a+k)) ≤ E a+∑ k ∈ Finset.range (b-a), income (a+k) := by
  have hrow (k : ℕ) (hk : k ∈ Finset.range (b-a)) :
      paid (a+k) ≤ (E (a+k)-E (a+k+1))+income (a+k) := by
    have hh := hstep (a+k) (by omega) (by have := Finset.mem_range.mp hk; omega)
    linarith
  have hs := Finset.sum_le_sum hrow
  have htel : (∑ k ∈ Finset.range (b-a), (E (a+k)-E (a+k+1)))=E a-E b := by
    have hh := congrArg Neg.neg (offset_sum_difference E a (b-a))
    simpa only [←Finset.sum_neg_distrib,neg_sub,Nat.add_sub_of_le hab] using hh
  rw [Finset.sum_add_distrib,htel] at hs
  linarith

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

-- Proof module: Solutions.IntervalAccounting

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma offset_sum_eq_Ico (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (∑ k ∈ Finset.range (b-a), f (a+k))=∑ k ∈ Finset.Ico a b, f k := by
  rw [Finset.sum_Ico_eq_sum_range]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheChargeIdentity

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma indicator_interval_bound (P : ℕ → Prop) (a b t : ℕ) (hbt : b ≤ t) :
    (∑ k ∈ Finset.Ico a b, if P k then (1 : ℝ) else 0) ≤ (((Finset.range t).filter P).card : ℝ) := by
  classical
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro k hk
  obtain ⟨hkI,hP⟩ := Finset.mem_filter.mp hk
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Finset.mem_Ico.mp hkI).2.trans_le hbt),hP⟩

lemma indicator_cover_bound (P : ℕ → Prop) (S U : Finset ℕ) (hS : ∀ k ∈ S, P k) (hsub : S ⊆ U) :
    (S.card : ℝ) ≤ ∑ k ∈ U, if P k then (1 : ℝ) else 0 := by
  classical
  calc
    _ = ∑ k ∈ S, if P k then (1 : ℝ) else 0 := by
      symm
      calc
        _ = ∑ k ∈ S, (1 : ℝ) := Finset.sum_congr rfl (fun k hk => if_pos (hS k hk))
        _ = _ := by simp
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by split <;> positivity)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OpenCallSpan

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma open_call_span (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j id : ℕ) (hab : a ≤ b)
    (hja : j ≤ (recursiveRun m g s α q ℓ schedule a).top)
    (hida : ((recursiveRun m g s α q ℓ schedule a).frames j).id=id)
    (hjb : j ≤ (recursiveRun m g s α q ℓ schedule b).top)
    (hidb : ((recursiveRun m g s α q ℓ schedule b).frames j).id=id)
    (hdb : (recursiveRun m g s α q ℓ schedule b).done=false) :
    let run := recursiveRun m g s α q ℓ schedule
    ∀ k, a ≤ k → k ≤ b → j ≤ (run k).top ∧ ((run k).frames j).id=id ∧
      frozenFrame ((run k).frames j)=frozenFrame ((run a).frames j) := by
  intro run
  have hi := open_frame_information_run m g s α q ℓ schedule a j hja
  rw [hida] at hi
  have hn := running_open_not_closed_run m g s α q ℓ schedule b hdb j hjb
  rw [hidb] at hn
  have hh := unclosed_call_interval m g s α q ℓ schedule a b id
    ⟨j,((run a).frames j).N,((run a).frames j).block⟩ hi hn
  intro k hak hkb
  refine ⟨(hh k hak hkb).1,(hh k hak hkb).2.1,?_⟩
  exact frozenFrame_interval m g s α q ℓ schedule a k j hak
    (fun u hau huk => (hh u hau (huk.le.trans hkb)).1)

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

-- Proof module: Solutions.ControlPrefixCount

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma controlEvent_producer_le (g : InputGraph n) (st : RecursiveState n) :
    (if componentComplete st then 0 else st.top) ≤ st.top := by split <;> omega

set_option maxHeartbeats 2000000 in
lemma control_prefix_count (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) :
    let run := recursiveRun m g s α q ℓ schedule
    (((Finset.range T).filter (fun k => controlEvent g (run k) id)).card : ℝ) ≤
      9+7*((run T).episodes id : ℝ) := by
  classical
  intro run
  let S := (Finset.range T).filter (fun k => controlEvent g (run k) id)
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let b := S.max' hS
    have haS : a ∈ S := Finset.min'_mem S hS
    have hbS : b ∈ S := Finset.max'_mem S hS
    have ha : controlEvent g (run a) id := (Finset.mem_filter.mp haS).2
    have hb : controlEvent g (run b) id := (Finset.mem_filter.mp hbS).2
    have hab : a ≤ b := Finset.min'_le S b hbS
    have hbt : b < T := Finset.mem_range.mp (Finset.mem_filter.mp hbS).1
    let ja := if componentComplete (run a) then 0 else (run a).top
    let jb := if componentComplete (run b) then 0 else (run b).top
    have hja : ja ≤ (run a).top := controlEvent_producer_le g (run a)
    have hjb : jb ≤ (run b).top := controlEvent_producer_le g (run b)
    have hida : ((run a).frames ja).id=id := ha.2.2.2
    have hidb : ((run b).frames jb).id=id := hb.2.2.2
    have hib := open_frame_information_run m g s α q ℓ schedule b jb hjb
    rw [hidb] at hib
    have hpar := open_frame_prefix_parameters m g s α q ℓ schedule a b ja id
      ⟨jb,((run b).frames jb).N,((run b).frames jb).block⟩ hab hib hja hida
    have hjab : ja=jb := hpar.1
    have hspan := open_call_span m g s α q ℓ schedule a b ja id hab hja hida
      (by rwa [hjab]) (by rwa [hjab]) hb.1
    let E := fun k => (callControlPotential (run k) ja id : ℝ)
    let paid := fun k => if controlEvent g (run k) id then (1 : ℝ) else 0
    let income := fun k => 7*(if episodeEvent (run k) id then (1 : ℝ) else 0)
    have hstep (k : ℕ) (hak : a ≤ k) (hkb : k < b+1) : E (k+1)+paid k ≤ E k+income k := by
      have hkt : k ≤ b := by omega
      have hh := control_potential_run_step m g s α q hq hs ℓ schedule k ja id
        (running_prefix m g s α q ℓ schedule k b hkt hb.1)
        (hspan k hak hkt).1 (hspan k hak hkt).2.1
      dsimp only at hh
      change (callControlPotential (run (k+1)) ja id)+
        (if controlEvent g (run k) id then (1 : ℕ) else 0) ≤
          callControlPotential (run k) ja id+7*(if episodeEvent (run k) id then (1 : ℕ) else 0) at hh
      dsimp only [E,paid,income]
      split_ifs at hh ⊢ <;> exact_mod_cast hh
    have haccount := amortized_interval_bound E paid income a (b+1) (by omega) (by dsimp [E]; positivity) hstep
    have hEa : E a ≤ 9 := by dsimp only [E]; exact_mod_cast callControlPotential_bound (run a) ja id
    have hincome : (∑ k ∈ Finset.range (b+1-a), income (a+k)) ≤ 7*((run T).episodes id : ℝ) := by
      rw [offset_sum_eq_Ico income a (b+1) (by omega)]
      dsimp only [income]
      rw [←Finset.mul_sum,episodes_run_events m g s α q ℓ schedule T id]
      exact mul_le_mul_of_nonneg_left (indicator_interval_bound (fun k => episodeEvent (run k) id) a (b+1) T (by omega)) (by norm_num)
    have hcount : (S.card : ℝ) ≤ ∑ k ∈ Finset.range (b+1-a), paid (a+k) := by
      rw [offset_sum_eq_Ico paid a (b+1) (by omega)]
      apply indicator_cover_bound (fun k => controlEvent g (run k) id) S (Finset.Ico a (b+1))
        (fun k hk => (Finset.mem_filter.mp hk).2)
      intro k hk
      exact Finset.mem_Ico.mpr ⟨Finset.min'_le S k hk,Nat.lt_succ_of_le (Finset.le_max' S k hk)⟩
    change (S.card : ℝ) ≤ _
    linarith
  · have hz : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change (S.card : ℝ) ≤ _
    rw [hz,Finset.card_empty,Nat.cast_zero]
    positivity

end
end NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal

theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) :
    let run := recursiveRun m g s α q ℓ schedule
    (((Finset.range T).filter (fun k => controlEvent g (run k) id)).card : ℝ) ≤
      9+7*((run T).episodes id : ℝ) := by
  exact control_prefix_count m g s α q hq hs ℓ schedule T id
