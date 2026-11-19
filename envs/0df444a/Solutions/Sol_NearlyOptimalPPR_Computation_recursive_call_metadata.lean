-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_call_metadata
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:00:09.884196+00:00
-- url     : https://prove2.me/submissions/18ed7288-42c4-4cb0-b5e2-5d769d1e7f7a

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push


set_option linter.all false
set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}



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

set_option maxHeartbeats 2000000 in
lemma nextId_step_monotone (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) :
    st.nextId ≤ (recursiveStep m g s α ℓ schedule st).nextId := by
  cases hpend : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hpend] <;>
      (try split_ifs) <;> simp_all
  | some p =>
    obtain ⟨t,v⟩ := p
    have hh := (exterior_lifecycle g α st t v).1
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hpend,hh] <;>
      (try split_ifs) <;> simp_all

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FreshCallIDs

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma open_id_bound_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hi : OpenIDBound st) :
    OpenIDBound (recursiveStep m g s α ℓ schedule st) := by
  intro j hj
  by_cases hle : j ≤ st.top
  · have hid : ((recursiveStep m g s α ℓ schedule st).frames j).id = (st.frames j).id :=
      congrArg (fun f => f.2.2.2) (frozenFrame_step m g s α ℓ schedule st j hle)
    rw [hid]
    exact (hi j hle).trans_le (nextId_step_monotone m g s α ℓ schedule st)
  · have hg : st.top < (recursiveStep m g s α ℓ schedule st).top := by omega
    obtain ⟨hd,hcomp,hpc,he,hl⟩ := growing_step_guards m g s α ℓ schedule st hg
    have hjnew : j=st.top+1 := by
      simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hcomp,hpc,he,hl] at hj
      change j ≤ st.top+1 at hj
      omega
    subst j
    simp [recursiveStep,hd,hcomp,hpc,he,hl,freshFrame]

lemma open_id_bound_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    OpenIDBound (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero =>
    intro j hj
    have hj0 : j=0 := by change j ≤ 0 at hj; omega
    subst j
    simp [recursiveRun,recursiveInit,freshFrame]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      open_id_bound_step m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule t) ih

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

-- Proof module: Solutions.ClosureShapes

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma current_id_mem_openIDs (st : RecursiveState n) : (st.frames st.top).id ∈ openIDs st := by
  apply Finset.mem_image.mpr
  exact ⟨st.top,Finset.mem_range.mpr (by omega),rfl⟩

set_option maxHeartbeats 2000000 in
lemma closed_step_subset (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) :
    (recursiveStep m g s α ℓ schedule st).closed ⊆ st.closed ∪ openIDs st := by
  have hmem := current_id_mem_openIDs st
  cases hpend : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;> simp [recursiveStep,hpc,hpend] <;>
      (try split_ifs) <;> simp_all [openIDs,debit,Finset.insert_subset_iff]
  | some p =>
    obtain ⟨t,v⟩ := p
    have hh := (exterior_lifecycle g α st t v).2.2
    cases hpc : (st.frames st.top).pc <;> simp [recursiveStep,hpc,hpend,hh] <;>
      (try split_ifs) <;> simp_all [openIDs,debit,Finset.insert_subset_iff]

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

lemma closed_id_bound_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hi : ClosedIDBound st) (hopen : OpenIDBound st) : ClosedIDBound (recursiveStep m g s α ℓ schedule st) := by
  intro id hid
  have hs := closed_step_subset m g s α ℓ schedule st hid
  have hidold : id < st.nextId := by
    rcases Finset.mem_union.mp hs with hc|hc
    · exact hi id hc
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hc
      exact hopen i (by have := Finset.mem_range.mp hi; omega)
  exact hidold.trans_le (nextId_step_monotone m g s α ℓ schedule st)

lemma closed_id_bound_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) : ClosedIDBound (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => intro id hid; simpa [recursiveRun,recursiveInit] using hid
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      closed_id_bound_step m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule t) ih
        (open_id_bound_run m g s α q ℓ schedule t)

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

lemma information_id_bound_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hi : InformationIDBound st) :
    InformationIDBound (recursiveStep m g s α ℓ schedule st) := by
  intro id info hinfo
  obtain hh|hh := information_step_shape m g s α ℓ schedule st
  · rw [hh] at hinfo
    exact (hi id info hinfo).trans_le (nextId_step_monotone m g s α ℓ schedule st)
  · obtain ⟨newinfo,htop,hnext,hlevel,hid,hscale,hblock,hm⟩ := hh
    rw [hm] at hinfo
    by_cases he : id=st.nextId
    · rw [he,hnext]
      omega
    · rw [Function.update_of_ne he] at hinfo
      rw [hnext]
      exact (hi id info hinfo).trans (Nat.lt_succ_self _)

lemma information_id_bound_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    InformationIDBound (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero =>
    intro id info hinfo
    change (if id=0 then some _ else none) = some info at hinfo
    split_ifs at hinfo with he
    · subst id
      change 0 < 1
      omega
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      information_id_bound_step m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule t) ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OpenFrameInformation

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma open_frame_information_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hi : OpenFrameInformation st) (hid : OpenIDBound st) :
    OpenFrameInformation (recursiveStep m g s α ℓ schedule st) := by
  intro j hj
  by_cases hle : j ≤ st.top
  · have hs := information_step_old m g s α ℓ schedule st (st.frames j).id (hid j hle)
    have hf := frozenFrame_step m g s α ℓ schedule st j hle
    have hID : ((recursiveStep m g s α ℓ schedule st).frames j).id=(st.frames j).id := congrArg (fun f => f.2.2.2) hf
    have hN : ((recursiveStep m g s α ℓ schedule st).frames j).N=(st.frames j).N := congrArg (fun f => f.2.1) hf
    have hb : ((recursiveStep m g s α ℓ schedule st).frames j).block=(st.frames j).block := congrArg (fun f => f.2.2.1) hf
    rw [hID,hN,hb,hs]
    exact hi j hle
  · have hg : st.top < (recursiveStep m g s α ℓ schedule st).top := by omega
    obtain ⟨hd,hcomp,hpc,he,hl⟩ := growing_step_guards m g s α ℓ schedule st hg
    have hjnew : j=st.top+1 := by
      simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hcomp,hpc,he,hl] at hj
      change j ≤ st.top+1 at hj
      omega
    subst j
    simp [recursiveStep,hd,hcomp,hpc,he,hl,freshFrame]

lemma open_frame_information_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    OpenFrameInformation (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero =>
    intro j hj
    have hj0 : j=0 := by change j ≤ 0 at hj; omega
    subst j
    simp [recursiveRun,recursiveInit,freshFrame]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      open_frame_information_step m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule t) ih
        (open_id_bound_run m g s α q ℓ schedule t)

lemma open_frame_ids_injective (st : RecursiveState n) (hi : OpenFrameInformation st)
    (i j : ℕ) (his : i ≤ st.top) (hjs : j ≤ st.top) (hid : (st.frames i).id=(st.frames j).id) : i=j := by
  have hi' := hi i his
  have hj' := hi j hjs
  rw [hid,hj'] at hi'
  exact (congrArg CallInformation.level (Option.some.inj hi')).symm

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OpenNotClosed

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma running_open_not_closed_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hi : RunningOpenNotClosed st) (hinfo : OpenFrameInformation st) (hcids : ClosedIDBound st) :
    RunningOpenNotClosed (recursiveStep m g s α ℓ schedule st) := by
  intro hdnext j hj hclosed
  have hd := (running_step_guards m g s α ℓ schedule st hdnext).1
  by_cases hle : j ≤ st.top
  · have hid : ((recursiveStep m g s α ℓ schedule st).frames j).id=(st.frames j).id :=
      congrArg (fun f => f.2.2.2) (frozenFrame_step m g s α ℓ schedule st j hle)
    rw [hid] at hclosed
    rcases closed_step_running_shape m g s α ℓ schedule st hdnext with hc|⟨hpop,hc⟩
    · rw [hc] at hclosed
      exact hi hd j hle hclosed
    · rw [hc] at hclosed
      rcases Finset.mem_insert.mp hclosed with hidtop|hcold
      · have hjtop := open_frame_ids_injective st hinfo j st.top hle le_rfl hidtop
        subst j
        omega
      · exact hi hd j hle hcold
  · have hg : st.top < (recursiveStep m g s α ℓ schedule st).top := by omega
    obtain ⟨hdold,hcomp,hpc,he,hl⟩ := growing_step_guards m g s α ℓ schedule st hg
    have hjnew : j=st.top+1 := by
      simp only [recursiveStep,hdold,Bool.false_eq_true,ite_false,hcomp,hpc,he,hl] at hj
      change j ≤ st.top+1 at hj
      omega
    subst j
    have hid : ((recursiveStep m g s α ℓ schedule st).frames (st.top+1)).id=st.nextId := by
      simp [recursiveStep,hdold,hcomp,hpc,he,hl,freshFrame]
    have hc : (recursiveStep m g s α ℓ schedule st).closed=st.closed := by
      simp [recursiveStep,hdold,hcomp,hpc,he,hl]
    rw [hid,hc] at hclosed
    have hh := hcids st.nextId hclosed
    omega

lemma running_open_not_closed_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    RunningOpenNotClosed (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => intro _ j hj; simp [recursiveRun,recursiveInit]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      running_open_not_closed_step m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule t) ih
        (open_frame_information_run m g s α q ℓ schedule t) (closed_id_bound_run m g s α q ℓ schedule t)

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

set_option maxHeartbeats 2000000 in
lemma closed_dropped_top (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hpop : (recursiveStep m g s α ℓ schedule st).top < st.top) :
    (st.frames st.top).id ∈ (recursiveStep m g s α ℓ schedule st).closed := by
  cases hpend : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;> simp [recursiveStep,hpc,hpend] at hpop ⊢ <;>
      (try split_ifs at hpop ⊢) <;> simp_all [debit] <;> omega
  | some p =>
    obtain ⟨t,v⟩ := p
    cases hpc : (st.frames st.top).pc <;> simp [recursiveStep,hpc,hpend] at hpop ⊢ <;>
      (try split_ifs at hpop ⊢) <;> simp_all [debit] <;> omega

lemma popped_frame_closed (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top)
    (hpop : (recursiveStep m g s α ℓ schedule st).top < j) :
    (st.frames j).id ∈ (recursiveStep m g s α ℓ schedule st).closed := by
  have hlower := top_step_lower m g s α ℓ schedule st
  have hjtop : j=st.top := by omega
  subst j
  exact closed_dropped_top m g s α ℓ schedule st hpop

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CallLocations

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma call_locations_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hi : CallLocations st) :
    CallLocations (recursiveStep m g s α ℓ schedule st) := by
  let next := recursiveStep m g s α ℓ schedule st
  have hold (id : ℕ) (info : CallInformation) (hinfo : st.information id=some info) : id ∈ next.closed ∨
      info.level ≤ next.top ∧ (next.frames info.level).id=id ∧
        (next.frames info.level).N=info.scale ∧ (next.frames info.level).block=info.block := by
    rcases hi id info hinfo with hc|⟨hj,hid,hN,hb⟩
    · exact Or.inl (closed_step_monotone m g s α ℓ schedule st hc)
    · by_cases hle : info.level ≤ next.top
      · right
        have hf := frozenFrame_step m g s α ℓ schedule st info.level hj
        have hid' : (next.frames info.level).id=(st.frames info.level).id := congrArg (fun f => f.2.2.2) hf
        have hN' : (next.frames info.level).N=(st.frames info.level).N := congrArg (fun f => f.2.1) hf
        have hb' : (next.frames info.level).block=(st.frames info.level).block := congrArg (fun f => f.2.2.1) hf
        exact ⟨hle,hid'.trans hid,hN'.trans hN,hb'.trans hb⟩
      · left
        rw [←hid]
        exact popped_frame_closed m g s α ℓ schedule st info.level hj (Nat.lt_of_not_ge hle)
  intro id info hinfo
  rcases information_step_shape m g s α ℓ schedule st with hs|hs
  · rw [hs] at hinfo
    exact hold id info hinfo
  · obtain ⟨newinfo,htop,hnext,hlevel,hid,hscale,hblock,hm⟩ := hs
    rw [hm] at hinfo
    by_cases he : id=st.nextId
    · subst id
      rw [Function.update_self] at hinfo
      have hEq : info=newinfo := (Option.some.inj hinfo).symm
      subst info
      right
      refine ⟨?_,?_,?_,?_⟩
      · rw [hlevel]
      · rw [hlevel]; exact hid
      · rw [hlevel]; exact hscale.symm
      · rw [hlevel]; exact hblock.symm
    · rw [Function.update_of_ne he] at hinfo
      exact hold id info hinfo

lemma call_locations_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) : CallLocations (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero =>
    intro id info hinfo
    change (if id=0 then some ⟨0,1/q,blockScale schedule ℓ 0 (1/q)⟩ else none)=some info at hinfo
    split_ifs at hinfo with he
    subst id
    have hEq : info=⟨0,1/q,blockScale schedule ℓ 0 (1/q)⟩ := (Option.some.inj hinfo).symm
    subst info
    right
    simp [recursiveRun,recursiveInit,freshFrame]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      call_locations_step m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule t) ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ProtocolInvariants

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma recursive_call_metadata_proof (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    CallLocations st ∧ InformationIDBound st ∧ OpenIDBound st ∧ ClosedIDBound st ∧
      OpenFrameInformation st ∧ RunningOpenNotClosed st := by
  exact ⟨call_locations_run m g s α q ℓ schedule t,information_id_bound_run m g s α q ℓ schedule t,
    open_id_bound_run m g s α q ℓ schedule t,closed_id_bound_run m g s α q ℓ schedule t,
    open_frame_information_run m g s α q ℓ schedule t,running_open_not_closed_run m g s α q ℓ schedule t⟩

end
end NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation

theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    CallLocations st ∧ InformationIDBound st ∧ OpenIDBound st ∧ ClosedIDBound st ∧
      OpenFrameInformation st ∧ RunningOpenNotClosed st := by
  exact recursive_call_metadata_proof m n g s α q ℓ schedule t

