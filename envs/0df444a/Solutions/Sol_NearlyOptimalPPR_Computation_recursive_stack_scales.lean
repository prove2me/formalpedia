-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_stack_scales
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:00:09.060471+00:00
-- url     : https://prove2.me/submissions/7cf48ee9-da8e-4b51-939a-d5f908da38da

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters

set_option linter.all false
set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

abbrev parameters_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_control_parameters m n g s α q ℓ schedule t).2.2.2 hq

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

-- Proof module: Solutions.ThresholdRelation

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma threshold_relation_transport (st u : RecursiveState n) (hi : ThresholdRelation st)
    (ht : u.top ≤ st.top) (hq : ∀ i ≤ u.top, (u.frames i).q = (st.frames i).q)
    (hθ : ∀ i < u.top, (u.frames i).theta = (st.frames i).theta) : ThresholdRelation u := by
  intro j hj
  rw [hq (j+1) hj,hθ j hj]
  exact hi j (lt_of_lt_of_le hj ht)

lemma threshold_relation_topFrame (st : RecursiveState n) (hi : ThresholdRelation st)
    (f : NormalizeFrame n → NormalizeFrame n) (hq : (f (st.frames st.top)).q = (st.frames st.top).q) :
    ThresholdRelation (changeFrame st st.top f) := by
  apply threshold_relation_transport st (changeFrame st st.top f) hi le_rfl
  · intro i hh
    by_cases he : i = st.top <;> simp [changeFrame,he,hq]
  · intro i hh
    have he : i ≠ st.top := by change i < st.top at hh; omega
    simp [changeFrame,he]

lemma threshold_relation_PC (st : RecursiveState n) (pc : NormalizePC) (hi : ThresholdRelation st) :
    ThresholdRelation (changePC st pc) := threshold_relation_topFrame st hi _ rfl

lemma threshold_relation_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hi : ThresholdRelation st) : ThresholdRelation (exteriorPush g α st t v) := by
  apply threshold_relation_transport st (exteriorPush g α st t v) hi (by simp)
  · intro i hh
    exact congrArg Prod.fst (exterior_parameters g α st t v i)
  · intro i hh
    exact congrArg (fun z => z.2.1) (exterior_parameters g α st t v i)

lemma threshold_relation_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (hi : ThresholdRelation st) : ThresholdRelation (jointUpdate g α st h) := by
  apply threshold_relation_transport st (jointUpdate g α st h) hi le_rfl
  · intro i hh
    have his : i ≤ st.top := hh
    simp [jointUpdate,his]
  · intro i hh
    have his : i ≤ st.top := Nat.le_of_lt hh
    simp [jointUpdate,his]

lemma threshold_relation_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : ThresholdRelation st) : ThresholdRelation (refreshKeys g st T) := by
  apply threshold_relation_transport st (refreshKeys g st T) hi le_rfl
  · intro i hh
    have his : i ≤ st.top := hh
    simp [refreshKeys,his]
  · intro i hh
    have his : i ≤ st.top := Nat.le_of_lt hh
    simp [refreshKeys,his]

lemma threshold_relation_finish (st : RecursiveState n) (hi : ThresholdRelation st) :
    ThresholdRelation (finishEpisode st) := by
  apply threshold_relation_topFrame _ (by exact hi) _ rfl

lemma threshold_relation_newFrame (st : RecursiveState n) (f : NormalizeFrame n)
    (hi : ThresholdRelation st) (hf : f.q = (st.frames st.top).theta) :
    ThresholdRelation {st with top := st.top+1, frames := Function.update st.frames (st.top+1) f} := by
  intro j hj
  change j < st.top+1 at hj
  by_cases he : j = st.top
  · subst j
    simpa using hf
  · have hj' : j < st.top := by omega
    have hne : j+1 ≠ st.top+1 := by omega
    have hne' : j ≠ st.top+1 := by omega
    simpa [he,hne,hne'] using hi j hj'

lemma threshold_relation_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : ThresholdRelation st) : ThresholdRelation (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · intro j hj
    exact hi j (lt_of_lt_of_le hj (Nat.sub_le _ _))

lemma threshold_relation_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    ThresholdRelation (recursiveInit g s q ℓ schedule) := by
  intro j hj
  change j < 0 at hj
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ThresholdRelationStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma threshold_relation_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : ThresholdRelation st) (pc : NormalizePC) :
    ThresholdRelation (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact threshold_relation_PC _ pc hi
  · cases hp : pendingPush st with
    | none => exact threshold_relation_PC _ pc hi
    | some p => obtain ⟨t,v⟩ := p; exact threshold_relation_exterior g α st t v hi

set_option maxHeartbeats 1000000 in
lemma threshold_relation_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hi : ThresholdRelation st) : ThresholdRelation (recursiveStep m g s α ℓ schedule st) := by
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
    · exact threshold_relation_PC _ _ hi
    · split
      · exact threshold_relation_drain g α st hi _
      · split <;> exact threshold_relation_PC _ _ hi
  | beginEpisode =>
    simp only [hpc]
    apply threshold_relation_topFrame _ _ _ rfl
    exact hi
  | fullSolve =>
    simp only [hpc]
    split
    · exact threshold_relation_PC _ _ hi
    · split
      · apply threshold_relation_PC _ _
        unfold ThresholdRelation
        exact threshold_relation_refresh g _ (touchedBy g (st.frames st.top).active)
          (threshold_relation_joint g α st _ hi)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact threshold_relation_PC _ _ hi
    · split
      · exact threshold_relation_PC _ _ hi
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : ThresholdRelation up := threshold_relation_topFrame u hi _ rfl
        exact threshold_relation_newFrame up c hup (by simp [c,freshFrame,up,u,changeFrame,debit])
  | leafDrain =>
    simp only [hpc]
    split
    · exact threshold_relation_PC _ _ hi
    · split
      · cases hp : pendingPush st with
        | none => exact threshold_relation_PC _ _ hi
        | some p => obtain ⟨t,v⟩ := p; exact threshold_relation_exterior g α st t v hi
      · split
        · exact threshold_relation_PC _ _ hi
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : ThresholdRelation u := threshold_relation_topFrame st hi _ rfl
            unfold ThresholdRelation
            exact threshold_relation_refresh g _ (touchedBy g C) (threshold_relation_joint g α u _ hu)
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact threshold_relation_PC _ _ (threshold_relation_finish _ hi)
    · split
      · exact threshold_relation_PC _ _ (threshold_relation_finish _ hi)
      · exact threshold_relation_drain g α st hi _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact threshold_relation_PC _ _ (threshold_relation_finish _ hi)
    · split
      · exact threshold_relation_PC _ _ (threshold_relation_finish _ hi)
      · apply threshold_relation_topFrame _ _ _ rfl
        exact threshold_relation_finish _ hi
  | restartDrain =>
    simp only [hpc]
    split
    · exact threshold_relation_PC _ _ hi
    · split
      · exact threshold_relation_drain g α st hi _
      · exact threshold_relation_topFrame (debit st st.top 1) hi
          (fun fc => {fc with needFull := true, pc := .beginEpisode}) rfl
  | normal =>
    simp only [hpc]
    exact threshold_relation_end g α _ hi
  | interrupted =>
    simp only [hpc]
    exact threshold_relation_end g α _ hi

lemma threshold_relation_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ThresholdRelation (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using threshold_relation_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using threshold_relation_step m g s α ℓ schedule _ ih

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

-- Proof module: Solutions.StackControl

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma stack_transport (st u : RecursiveState n) (hi : StackInvariant st) (ht : u.top ≤ st.top)
    (hp : ∀ i < u.top, (u.frames i).pc = (st.frames i).pc) : StackInvariant u := by
  intro i hh
  rw [hp i hh]
  exact hi i (lt_of_lt_of_le hh ht)

lemma stack_topFrame (st : RecursiveState n) (hi : StackInvariant st)
    (f : NormalizeFrame n → NormalizeFrame n) : StackInvariant (changeFrame st st.top f) := by
  apply stack_transport st (changeFrame st st.top f) hi le_rfl
  intro i hh
  have he : i ≠ st.top := by change i < st.top at hh; omega
  simp [changeFrame,he]

lemma stack_PC (st : RecursiveState n) (pc : NormalizePC) (hi : StackInvariant st) :
    StackInvariant (changePC st pc) := stack_topFrame st hi _

lemma stack_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hi : StackInvariant st) : StackInvariant (exteriorPush g α st t v) := by
  apply stack_transport st (exteriorPush g α st t v) hi (by simp)
  intro i _
  exact frame_pc_exterior g α st t v i

lemma stack_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (hi : StackInvariant st) : StackInvariant (jointUpdate g α st h) := by
  apply stack_transport st (jointUpdate g α st h) hi le_rfl
  intro i hh
  exact frame_pc_joint g α st h i

lemma stack_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : StackInvariant st) : StackInvariant (refreshKeys g st T) := by
  apply stack_transport st (refreshKeys g st T) hi le_rfl
  intro i _
  exact frame_pc_refresh g st T i

lemma stack_finish (st : RecursiveState n) (hi : StackInvariant st) : StackInvariant (finishEpisode st) := by
  apply stack_topFrame _ (by exact hi)

lemma stack_newFrame (st : RecursiveState n) (f : NormalizeFrame n) (hi : StackInvariant st)
    (hp : (st.frames st.top).pc = .afterChild) :
    StackInvariant {st with top := st.top+1, frames := Function.update st.frames (st.top+1) f} := by
  intro i hh
  change i < st.top+1 at hh
  have hne : i ≠ st.top+1 := by omega
  by_cases he : i = st.top
  · subst i
    simpa using hp
  · simpa [hne] using hi i (by omega)

lemma stack_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hi : StackInvariant st) :
    StackInvariant (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · intro i hh
    exact hi i (lt_of_lt_of_le hh (Nat.sub_le _ _))

lemma stack_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    StackInvariant (recursiveInit g s q ℓ schedule) := by
  intro i hh
  change i < 0 at hh
  omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StackStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma stack_metadata (st : RecursiveState n) (hi : StackInvariant st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) (hj : j = st.top) :
    StackInvariant (changeFrame st j f) := by
  rw [hj]
  exact stack_topFrame st hi f

lemma stack_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : StackInvariant st) (pc : NormalizePC) :
    StackInvariant (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact stack_PC _ pc hi
  · cases hp : pendingPush st with
    | none => exact stack_PC _ pc hi
    | some p => obtain ⟨t,v⟩ := p; exact stack_exterior g α st t v hi

set_option maxHeartbeats 1000000 in
lemma stack_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hi : StackInvariant st) : StackInvariant (recursiveStep m g s α ℓ schedule st) := by
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
    · exact stack_PC _ _ hi
    · split
      · exact stack_drain g α st hi _
      · split <;> exact stack_PC _ _ hi
  | beginEpisode =>
    simp only [hpc]
    apply stack_metadata _ _ _ _ rfl
    exact hi
  | fullSolve =>
    simp only [hpc]
    split
    · exact stack_PC _ _ hi
    · split
      · apply stack_PC _ _
        unfold StackInvariant
        exact stack_refresh g _ (touchedBy g (st.frames st.top).active)
          (stack_joint g α st _ hi)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact stack_PC _ _ hi
    · split
      · exact stack_PC _ _ hi
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : StackInvariant up := stack_metadata u hi st.top _ rfl
        exact stack_newFrame up c hup (by simp [up,u,changeFrame,debit])
  | leafDrain =>
    simp only [hpc]
    split
    · exact stack_PC _ _ hi
    · split
      · cases hp : pendingPush st with
        | none => exact stack_PC _ _ hi
        | some p => obtain ⟨t,v⟩ := p; exact stack_exterior g α st t v hi
      · split
        · exact stack_PC _ _ hi
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : StackInvariant u := stack_metadata st hi st.top _ rfl
            unfold StackInvariant
            exact stack_refresh g _ (touchedBy g C) (stack_joint g α u _ hu)
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact stack_PC _ _ (stack_finish _ hi)
    · split
      · exact stack_PC _ _ (stack_finish _ hi)
      · exact stack_drain g α st hi _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact stack_PC _ _ (stack_finish _ hi)
    · split
      · exact stack_PC _ _ (stack_finish _ hi)
      · apply stack_metadata _ _ _ _ rfl
        exact stack_finish _ hi
  | restartDrain =>
    simp only [hpc]
    split
    · exact stack_PC _ _ hi
    · split
      · exact stack_drain g α st hi _
      · exact stack_metadata (debit st st.top 1) hi st.top
          (fun fc => {fc with needFull := true, pc := .beginEpisode}) rfl
  | normal =>
    simp only [hpc]
    exact stack_end g α _ hi
  | interrupted =>
    simp only [hpc]
    exact stack_end g α _ hi

lemma stack_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    StackInvariant (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using stack_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using stack_step m g s α ℓ schedule _ ih

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

-- Proof module: Solutions.EpisodeShape

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma episode_shape_transport (st u : RecursiveState n) (hi : EpisodeShape st) (ht : u.top ≤ st.top)
    (hQ : ∀ i ≤ u.top, (u.frames i).Q = (st.frames i).Q)
    (hθ : ∀ i ≤ u.top, (u.frames i).theta = (st.frames i).theta)
    (hb : ∀ i ≤ u.top, (u.frames i).block = (st.frames i).block)
    (ho : ∀ i ≤ u.top, (u.frames i).openBudget = true → (st.frames i).openBudget = true) : EpisodeShape u := by
  intro i hh hop
  rw [hQ i hh,hθ i hh,hb i hh]
  exact hi i (hh.trans ht) (ho i hh hop)

lemma episode_shape_metadata (st : RecursiveState n) (hi : EpisodeShape st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hQ : (f (st.frames j)).Q = (st.frames j).Q)
    (hθ : (f (st.frames j)).theta = (st.frames j).theta)
    (hb : (f (st.frames j)).block = (st.frames j).block)
    (ho : (f (st.frames j)).openBudget = true → (st.frames j).openBudget = true) :
    EpisodeShape (changeFrame st j f) := by
  apply episode_shape_transport st (changeFrame st j f) hi le_rfl
  · intro i _; exact observe_changeFrame (fun f => f.Q) st j f hQ i
  · intro i _; exact observe_changeFrame (fun f => f.theta) st j f hθ i
  · intro i _; exact observe_changeFrame (fun f => f.block) st j f hb i
  · intro i _ hop
    by_cases he : i = j
    · subst i; exact ho (by simpa [changeFrame] using hop)
    · simpa [changeFrame,he] using hop

lemma episode_shape_PC (st : RecursiveState n) (pc : NormalizePC) (hi : EpisodeShape st) :
    EpisodeShape (changePC st pc) := episode_shape_metadata st hi st.top _ rfl rfl rfl (fun h => h)

lemma episode_shape_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hi : EpisodeShape st) : EpisodeShape (exteriorPush g α st t v) := by
  apply episode_shape_transport st (exteriorPush g α st t v) hi (by simp)
  · intro i hh; exact (exterior_budget_fields g α st t v i (by simpa using hh)).1
  · intro i _; exact congrArg (fun z => z.2.1) (exterior_parameters g α st t v i)
  · intro i _; exact congrArg (fun z => z.2.2.2.2.2.1) (exterior_parameters g α st t v i)
  · intro i _ hop
    have ho := congrArg (fun z => z.2.2.1) (exterior_parameters g α st t v i)
    exact ho.symm.trans hop

lemma child_scale_transport (st u : RecursiveState n) (hi : ChildScale st) (ht : u.top ≤ st.top)
    (hN : ∀ i ≤ u.top, (u.frames i).N = (st.frames i).N)
    (hb : ∀ i < u.top, (u.frames i).block = (st.frames i).block) : ChildScale u := by
  intro i hh
  rw [hN (i+1) hh,hb i hh]
  exact hi i (lt_of_lt_of_le hh ht)

lemma child_scale_metadata (st : RecursiveState n) (hi : ChildScale st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hN : (f (st.frames j)).N = (st.frames j).N)
    (hb : (f (st.frames j)).block = (st.frames j).block) : ChildScale (changeFrame st j f) := by
  apply child_scale_transport st (changeFrame st j f) hi le_rfl
  · intro i _; exact observe_changeFrame (fun f => f.N) st j f hN i
  · intro i _; exact observe_changeFrame (fun f => f.block) st j f hb i

lemma child_scale_PC (st : RecursiveState n) (pc : NormalizePC) (hi : ChildScale st) :
    ChildScale (changePC st pc) := child_scale_metadata st hi st.top _ rfl rfl

lemma child_scale_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hi : ChildScale st) : ChildScale (exteriorPush g α st t v) := by
  apply child_scale_transport st (exteriorPush g α st t v) hi (by simp)
  · intro i _; exact congrArg (fun z => z.2.2.2.2.1) (exterior_parameters g α st t v i)
  · intro i _; exact congrArg (fun z => z.2.2.2.2.2.1) (exterior_parameters g α st t v i)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ScaleControl

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma episode_shape_current (st : RecursiveState n) (hi : EpisodeShape st)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hnew : (f (st.frames st.top)).openBudget = true →
      (f (st.frames st.top)).Q = (f (st.frames st.top)).theta*(f (st.frames st.top)).block) :
    EpisodeShape (changeFrame st st.top f) := by
  intro i hh hop
  have his : i ≤ st.top := hh
  by_cases he : i = st.top
  · subst i
    simpa [changeFrame] using hnew (by simpa [changeFrame] using hop)
  · simpa [changeFrame,he] using hi i his (by simpa [changeFrame,he] using hop)

lemma episode_shape_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ)
    (hi : EpisodeShape st) : EpisodeShape (jointUpdate g α st h) := by
  apply episode_shape_transport st (jointUpdate g α st h) hi le_rfl
  all_goals intro i hh
  all_goals by_cases he : i ≤ st.top <;> simp [jointUpdate,he]

lemma child_scale_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ)
    (hi : ChildScale st) : ChildScale (jointUpdate g α st h) := by
  apply child_scale_transport st (jointUpdate g α st h) hi le_rfl
  · intro i hh; by_cases he : i ≤ st.top <;> simp [jointUpdate,he]
  · intro i hh; by_cases he : i ≤ st.top <;> simp [jointUpdate,he]

lemma episode_shape_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : EpisodeShape st) : EpisodeShape (refreshKeys g st T) := by
  apply episode_shape_transport st (refreshKeys g st T) hi le_rfl
  all_goals intro i hh
  all_goals by_cases he : i ≤ st.top <;> simp [refreshKeys,he]

lemma child_scale_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : ChildScale st) : ChildScale (refreshKeys g st T) := by
  apply child_scale_transport st (refreshKeys g st T) hi le_rfl
  · intro i hh; by_cases he : i ≤ st.top <;> simp [refreshKeys,he]
  · intro i hh; by_cases he : i ≤ st.top <;> simp [refreshKeys,he]

lemma episode_shape_finish (st : RecursiveState n) (hi : EpisodeShape st) : EpisodeShape (finishEpisode st) := by
  unfold finishEpisode
  apply episode_shape_metadata
  · exact hi
  · rfl
  · rfl
  · rfl
  · simp

lemma child_scale_finish (st : RecursiveState n) (hi : ChildScale st) : ChildScale (finishEpisode st) := by
  unfold finishEpisode
  apply child_scale_metadata
  · exact hi
  · rfl
  · rfl

lemma episode_shape_new (st : RecursiveState n) (c : NormalizeFrame n) (hi : EpisodeShape st)
    (hc : c.openBudget = false) :
    EpisodeShape {st with top := st.top+1,frames := Function.update st.frames (st.top+1) c} := by
  classical
  intro i hh ho
  change i ≤ st.top+1 at hh
  have hne : i ≠ st.top+1 := by intro he; subst i; simpa [hc] using ho
  have hi' : i ≤ st.top := by omega
  simpa [hne] using hi i hi' (by simpa [hne] using ho)

lemma child_scale_new (st : RecursiveState n) (c : NormalizeFrame n) (hi : ChildScale st)
    (hc : c.N = (st.frames st.top).block) :
    ChildScale {st with top := st.top+1,frames := Function.update st.frames (st.top+1) c} := by
  classical
  intro i hh
  change i < st.top+1 at hh
  have hin : i ≠ st.top+1 := by omega
  by_cases he : i = st.top
  · subst i; simpa using hc
  · have his : i < st.top := by omega
    have hin' : i+1 ≠ st.top+1 := by omega
    simpa [hin,hin',he] using hi i his

lemma episode_shape_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hi : EpisodeShape st) :
    EpisodeShape (endCall g α st) := by
  unfold endCall
  dsimp only
  split
  · exact hi
  · exact episode_shape_transport st _ hi (Nat.sub_le _ _) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ h => h)

lemma child_scale_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hi : ChildScale st) :
    ChildScale (endCall g α st) := by
  unfold endCall
  dsimp only
  split
  · exact hi
  · exact child_scale_transport st _ hi (Nat.sub_le _ _) (fun _ _ => rfl) (fun _ _ => rfl)

lemma scale_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    EpisodeShape (recursiveInit g s q ℓ schedule) ∧ ChildScale (recursiveInit g s q ℓ schedule) := by
  constructor
  · intro i hh ho
    have hz : i = 0 := by change i ≤ 0 at hh; omega
    subst i
    simp [recursiveInit,freshFrame,emptyFrame] at ho
  · intro i hh
    change i < 0 at hh
    omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ScaleInvariant

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma scale_metadata (st : RecursiveState n) (hi : ScaleInvariant st) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hQ : (f (st.frames j)).Q = (st.frames j).Q)
    (hθ : (f (st.frames j)).theta = (st.frames j).theta)
    (hb : (f (st.frames j)).block = (st.frames j).block)
    (hN : (f (st.frames j)).N = (st.frames j).N)
    (ho : (f (st.frames j)).openBudget = true → (st.frames j).openBudget = true) :
    ScaleInvariant (changeFrame st j f) :=
  ⟨episode_shape_metadata st hi.1 j f hQ hθ hb ho,child_scale_metadata st hi.2 j f hN hb⟩

lemma scale_current (st : RecursiveState n) (hi : ScaleInvariant st)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hshape : (f (st.frames st.top)).openBudget = true →
      (f (st.frames st.top)).Q = (f (st.frames st.top)).theta*(f (st.frames st.top)).block)
    (hN : (f (st.frames st.top)).N = (st.frames st.top).N)
    (hb : (f (st.frames st.top)).block = (st.frames st.top).block) :
    ScaleInvariant (changeFrame st st.top f) :=
  ⟨episode_shape_current st hi.1 f hshape,child_scale_metadata st hi.2 st.top f hN hb⟩

lemma scale_PC (st : RecursiveState n) (pc : NormalizePC) (hi : ScaleInvariant st) :
    ScaleInvariant (changePC st pc) := ⟨episode_shape_PC st pc hi.1,child_scale_PC st pc hi.2⟩
lemma scale_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hi : ScaleInvariant st) : ScaleInvariant (exteriorPush g α st t v) :=
  ⟨episode_shape_exterior g α st t v hi.1,child_scale_exterior g α st t v hi.2⟩
lemma scale_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ)
    (hi : ScaleInvariant st) : ScaleInvariant (jointUpdate g α st h) :=
  ⟨episode_shape_joint g α st h hi.1,child_scale_joint g α st h hi.2⟩
lemma scale_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (hi : ScaleInvariant st) :
    ScaleInvariant (refreshKeys g st T) := ⟨episode_shape_refresh g st T hi.1,child_scale_refresh g st T hi.2⟩
lemma scale_finish (st : RecursiveState n) (hi : ScaleInvariant st) : ScaleInvariant (finishEpisode st) :=
  ⟨episode_shape_finish st hi.1,child_scale_finish st hi.2⟩
lemma scale_new (st : RecursiveState n) (c : NormalizeFrame n) (hi : ScaleInvariant st)
    (ho : c.openBudget = false) (hN : c.N = (st.frames st.top).block) :
    ScaleInvariant {st with top := st.top+1,frames := Function.update st.frames (st.top+1) c} :=
  ⟨episode_shape_new st c hi.1 ho,child_scale_new st c hi.2 hN⟩
lemma scale_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hi : ScaleInvariant st) :
    ScaleInvariant (endCall g α st) := ⟨episode_shape_end g α st hi.1,child_scale_end g α st hi.2⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ScaleStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma scale_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : ScaleInvariant st) (pc : NormalizePC) :
    ScaleInvariant (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact scale_PC _ pc hi
  · cases hp : pendingPush st with
    | none => exact scale_PC _ pc hi
    | some p => obtain ⟨t,v⟩ := p; exact scale_exterior g α st t v hi

set_option maxHeartbeats 1000000 in
lemma scale_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hp : ParameterInvariant st) (hi : ScaleInvariant st) : ScaleInvariant (recursiveStep m g s α ℓ schedule st) := by
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
    · exact scale_PC _ _ hi
    · split
      · exact scale_drain g α st hi _
      · split <;> exact scale_PC _ _ hi
  | beginEpisode =>
    simp only [hpc]
    apply scale_current
    · exact hi
    · intro _
      have hbpos : 0 < (st.frames st.top).block := by have := (hp st.top le_rfl).2.1; omega
      have hbne : ((st.frames st.top).block : ℝ) ≠ 0 := by exact_mod_cast hbpos.ne'
      dsimp only
      simp only [debit]
      rw [div_mul_cancel₀ _ hbne]
    · rfl
    · rfl
  | fullSolve =>
    simp only [hpc]
    split
    · exact scale_PC _ _ hi
    · split
      · apply scale_PC _ _
        unfold ScaleInvariant
        exact scale_refresh g _ (touchedBy g (st.frames st.top).active)
          (scale_joint g α st _ hi)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact scale_PC _ _ hi
    · split
      · exact scale_PC _ _ hi
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : ScaleInvariant up := scale_metadata u hi st.top _ rfl rfl rfl rfl (fun h => h)
        exact scale_new up c hup rfl (by simp [c,freshFrame,up,u,changeFrame,debit])
  | leafDrain =>
    simp only [hpc]
    split
    · exact scale_PC _ _ hi
    · split
      · cases hp : pendingPush st with
        | none => exact scale_PC _ _ hi
        | some p => obtain ⟨t,v⟩ := p; exact scale_exterior g α st t v hi
      · split
        · exact scale_PC _ _ hi
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : ScaleInvariant u := scale_metadata st hi st.top _ rfl rfl rfl rfl (fun h => h)
            unfold ScaleInvariant
            exact scale_refresh g _ (touchedBy g C) (scale_joint g α u _ hu)
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact scale_PC _ _ (scale_finish _ hi)
    · split
      · exact scale_PC _ _ (scale_finish _ hi)
      · exact scale_drain g α st hi _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact scale_PC _ _ (scale_finish _ hi)
    · split
      · exact scale_PC _ _ (scale_finish _ hi)
      · apply scale_metadata
        · exact scale_finish _ hi
        · rfl
        · rfl
        · rfl
        · rfl
        · exact fun h => h
  | restartDrain =>
    simp only [hpc]
    split
    · exact scale_PC _ _ hi
    · split
      · exact scale_drain g α st hi _
      · apply scale_metadata
        · exact hi
        · rfl
        · rfl
        · rfl
        · rfl
        · exact fun h => h
  | normal =>
    simp only [hpc]
    exact scale_end g α _ hi
  | interrupted =>
    simp only [hpc]
    exact scale_end g α _ hi

lemma scale_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ) (hq : 0 < q)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ScaleInvariant (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun,ScaleInvariant] using scale_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using scale_step m g s α ℓ schedule _ (parameters_run m g s α q hq ℓ schedule t) ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ProtocolInvariants

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma recursive_stack_scales_proof (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    ThresholdRelation st ∧ StackInvariant st ∧ (0 < q → ScaleInvariant st) := by
  exact ⟨threshold_relation_run m g s α q ℓ schedule t,stack_run m g s α q ℓ schedule t,
    fun hq => scale_run m g s α q hq ℓ schedule t⟩

end
end NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation

theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    ThresholdRelation st ∧ StackInvariant st ∧ (0 < q → ScaleInvariant st) := by
  exact recursive_stack_scales_proof m n g s α q ℓ schedule t

