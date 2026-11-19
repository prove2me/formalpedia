-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_successful_request_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:08:37.896085+00:00
-- url     : https://prove2.me/submissions/f8d65e11-ee0a-490d-8a55-0b39f8b7023a

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_budget_energy
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_discovery_credit
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_forcing_bound
import Theorems.Thm_NearlyOptimalPPR_Computation_active_region_potentials

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

namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}
lemma budget_energy_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    BudgetEnergyInvariant g s α (recursiveRun m g s α q ℓ schedule t) := by
  exact recursive_budget_energy m n g s α q hα hq hs ℓ schedule t

lemma stored_credit_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    StoredCreditInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  exact recursive_discovery_credit m n g s α q hα hq hs ℓ schedule t

lemma forcing_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ForcingInvariant g s α (recursiveRun m g s α q ℓ schedule t) := by
  exact recursive_forcing_bound m n g s α q hα hq hs ℓ schedule t

end
end NearlyOptimalPPR.Computation

namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}
lemma run_proper_potential_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α ≤ 1/2) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    let H := (st.frames 0).active
    (∃ v, g.graph.Reachable s v ∧ v ∉ H) → ∀ v, st.x v ≤ 3/q  := by
  intro st H hp v
  exact ((active_region_potentials m n g s α q ℓ schedule hα hq hs t).2 hp v).2
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

-- Proof module: Solutions.DrainedConditions

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma pending_none_queues_empty (st : RecursiveState n) (hp : pendingPush st = none) :
    ∀ i ≤ st.top, (st.frames i).exterior = ∅ := by
  classical
  intro i hi
  by_contra he
  have hn : (st.frames i).exterior.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  let levels := (Finset.range (st.top+1)).filter (fun j => (st.frames j).exterior.Nonempty)
  have hl : levels.Nonempty := ⟨i,by simp [levels,hi,hn]⟩
  have hm := Finset.min'_mem levels hl
  have hmin : (st.frames (levels.min' hl)).exterior.Nonempty := (Finset.mem_filter.mp hm).2
  change (if h : levels.Nonempty then
    if h' : (st.frames (levels.min' h)).exterior.Nonempty then
      some (levels.min' h, (st.frames (levels.min' h)).exterior.min' h') else none
    else none) = none at hp
  simp [hl,hmin] at hp

lemma high_empty_density (g : InputGraph n) (st : RecursiveState n) (hk : KeysInvariant g st)
    (i : ℕ) (hi : i ≤ st.top) (hh : (st.frames i).high = ∅) :
    ∀ v ∈ (st.frames i).active,
      (st.frames i).residual v < 3*(st.frames i).theta*LocalPush.deg g.graph v := by
  intro v hv
  by_contra hn
  have hge := le_of_not_gt hn
  have hm := ((hk i hi).2 v).mpr ⟨hv,hge⟩
  rw [hh] at hm
  simp at hm

lemma return_conditions_from_density (g : InputGraph n) (ℓ j : ℕ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hnum : NumericalInvariant g st) (hk : KeysInvariant g st)
    (hj : j ≤ st.top) (hp : pendingPush st = none)
    (hd : ∀ v ∈ (st.frames j).active,
      (st.frames j).residual v ≤ kappa ℓ j*(st.frames j).q*LocalPush.deg g.graph v) :
    returnConditions g ℓ j st := by
  have he := pending_none_queues_empty st hp
  refine ⟨?_,?_,?_,?_⟩
  · intro v hv
    exact ⟨((hnum j hj).1 v ((hreg j hj).1 hv)).1,hd v hv⟩
  · intro t ht v hv
    obtain ⟨hdom,hout⟩ := Finset.mem_sdiff.mp hv
    have hts : t ≤ st.top := ht.trans hj
    have hn := ((hnum t hts).1 v hdom).1
    refine ⟨hn,?_⟩
    by_contra hgt
    have hm := ((hk t hts).1 v).mpr ⟨hdom,hout,lt_of_not_ge hgt⟩
    rw [he t hts] at hm
    simp at hm
  · intro v hv
    obtain ⟨hdom,hout⟩ := Finset.mem_sdiff.mp hv
    have hn := (hnum j hj).1 v hdom
    exact ⟨hn.2.1,(hn.2.2.2 hout).le⟩
  · intro v hv
    exact ((hnum j hj).1 v ((hreg j hj).1 hv)).2.2.1 hv

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DensityTransfer

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma kappa_succ (ℓ j : ℕ) (hj : j < ℓ) :
    (kappa ℓ j : ℝ) = (kappa ℓ (j+1) : ℝ)+1 := by
  have hh : kappa ℓ j = kappa ℓ (j+1)+1 := by unfold kappa; omega
  exact_mod_cast hh

lemma parent_density_of_return (g : InputGraph n) (ℓ j : ℕ) (st : RecursiveState n)
    (hdepth : st.top ≤ ℓ) (hj : j < st.top) (hlayer : LayerIdentity g st)
    (hparam : ParameterInvariant st) (hthreshold : ThresholdRelation st)
    (hret : returnConditions g ℓ (j+1) st) :
    ActiveDensity g ℓ j (st.frames j).theta st := by
  intro v hv
  have hid := hlayer j hj v hv
  have hq := hthreshold j hj
  have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
  have hqd : 0 ≤ (st.frames (j+1)).q*LocalPush.deg g.graph v :=
    mul_nonneg (hparam (j+1) hj).1.le hd
  by_cases ha : v ∈ (st.frames (j+1)).active
  · simp only [ha,ite_true] at hid
    calc
      _ = (st.frames (j+1)).residual v+LocalPush.deg g.graph v*(st.frames (j+1)).q := hid
      _ ≤ (kappa ℓ (j+1) : ℝ)*(st.frames (j+1)).q*LocalPush.deg g.graph v+
          LocalPush.deg g.graph v*(st.frames (j+1)).q := add_le_add (hret.1 v ha).2 le_rfl
      _ = _ := by rw [kappa_succ ℓ j (by omega),← hq]; ring
  · simp only [ha,ite_false] at hid
    have hvdom : v ∈ parentDomain st (j+1) \ (st.frames (j+1)).active := by
      simp [parentDomain,hv,ha]
    have hr := (hret.2.1 (j+1) le_rfl v hvdom).2
    have hy := (hret.2.2.1 v hvdom).2
    have hk : (5/2 : ℝ) ≤ (kappa ℓ j : ℝ) := by
      have hh : (3 : ℝ) ≤ (kappa ℓ j : ℝ) := by simp [kappa]
      linarith
    calc
      _ = (st.frames (j+1)).residual v+LocalPush.deg g.graph v*(4*relative st (j+1) v) := hid
      _ ≤ (5/2 : ℝ)*(st.frames (j+1)).q*LocalPush.deg g.graph v := by
        have hh := mul_le_mul_of_nonneg_left hy hd
        nlinarith
      _ ≤ (kappa ℓ j : ℝ)*(st.frames (j+1)).q*LocalPush.deg g.graph v := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hk hqd
      _ = _ := by rw [hq]

lemma leaf_density_of_high_empty (g : InputGraph n) (ℓ : ℕ) (st : RecursiveState n)
    (hk : KeysInvariant g st) (hlevel : st.top = ℓ) (hh : (st.frames st.top).high = ∅) :
    ActiveDensity g ℓ st.top (st.frames st.top).theta st := by
  intro v hv
  have hd := (high_empty_density g st hk st.top le_rfl hh v hv).le
  simpa [hlevel,kappa] using hd

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.InterruptedControl

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma ancestor_exhausted_metadata (st : RecursiveState n) (f : NormalizeFrame n → NormalizeFrame n) :
    ancestorExhausted (changeFrame st st.top f) ↔ ancestorExhausted st := by
  constructor
  · rintro ⟨i,hi,he⟩
    have hne : i ≠ st.top := by change i < st.top at hi; omega
    refine ⟨i,hi,?_⟩
    simpa [exhausted,changeFrame,hne] using he
  · rintro ⟨i,hi,he⟩
    have hne : i ≠ st.top := by omega
    exact ⟨i,hi,by simpa [exhausted,changeFrame,hne] using he⟩

lemma ancestor_exhausted_PC (st : RecursiveState n) (pc : NormalizePC) :
    ancestorExhausted (changePC st pc) ↔ ancestorExhausted st := ancestor_exhausted_metadata st _

lemma ancestor_exhausted_finish (st : RecursiveState n) :
    ancestorExhausted (finishEpisode st) ↔ ancestorExhausted st := by
  unfold finishEpisode
  exact ancestor_exhausted_metadata _ _

lemma interrupted_safe (st : RecursiveState n) (hp : (st.frames st.top).pc ≠ .interrupted) :
    InterruptedInvariant st := fun h => False.elim (hp h)

lemma interrupted_PC_safe (st : RecursiveState n) (pc : NormalizePC) (hp : pc ≠ .interrupted) :
    InterruptedInvariant (changePC st pc) := by
  apply interrupted_safe
  simpa [changePC,changeFrame] using hp

lemma interrupted_PC_ancestor (st : RecursiveState n) (pc : NormalizePC) (ha : ancestorExhausted st) :
    InterruptedInvariant (changePC st pc) := fun _ => (ancestor_exhausted_PC st pc).mpr ha

lemma interrupted_finish_PC (st : RecursiveState n) (pc : NormalizePC) (ha : ancestorExhausted st) :
    InterruptedInvariant (changePC (finishEpisode st) pc) :=
  interrupted_PC_ancestor _ pc ((ancestor_exhausted_finish st).mpr ha)

lemma interrupted_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hp : (st.frames st.top).pc ≠ .interrupted) :
    InterruptedInvariant (exteriorPush g α st t v) := by
  apply interrupted_safe
  simpa only [top_exterior,frame_pc_exterior] using hp

lemma interrupted_newFrame (st : RecursiveState n) (f : NormalizeFrame n) (hp : f.pc = .initialDrain) :
    InterruptedInvariant {st with top := st.top+1, frames := Function.update st.frames (st.top+1) f} := by
  apply interrupted_safe
  simp [hp]

lemma interrupted_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hstack : StackInvariant st) (hi : InterruptedInvariant st) : InterruptedInvariant (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · rename_i ht
    have hp := hstack (st.top-1) (by omega)
    apply interrupted_safe
    simpa [hp]

lemma interrupted_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    InterruptedInvariant (recursiveInit g s q ℓ schedule) := by
  apply interrupted_safe
  simp [recursiveInit,freshFrame,emptyFrame]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.InterruptedStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma interrupted_drain_safe (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (pc : NormalizePC)
    (hn : (st.frames st.top).pc ≠ .interrupted) (hp : pc ≠ .interrupted) :
    InterruptedInvariant (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact interrupted_PC_safe _ pc hp
  · cases he : pendingPush st with
    | none => exact interrupted_PC_safe _ pc hp
    | some p => obtain ⟨t,v⟩ := p; exact interrupted_exterior g α st t v hn

set_option maxHeartbeats 1000000 in
lemma interrupted_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hstack : StackInvariant st) (hi : InterruptedInvariant st) :
    InterruptedInvariant (recursiveStep m g s α ℓ schedule st) := by
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
    · rename_i ha
      exact interrupted_PC_ancestor _ _ ha
    · split
      · exact interrupted_drain_safe g α st _ (by simp [hpc]) (by simp)
      · split <;> exact interrupted_PC_safe _ _ (by simp)
  | beginEpisode =>
    simp only [hpc]
    apply interrupted_safe
    simp [changeFrame,debit] <;> (try split_ifs) <;> simp
  | fullSolve =>
    simp only [hpc]
    split
    · exact interrupted_PC_safe _ _ (by simp)
    · split
      · exact interrupted_PC_safe _ _ (by simp)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact interrupted_PC_safe _ _ (by simp)
    · split
      · exact interrupted_PC_safe _ _ (by simp)
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        exact interrupted_newFrame up c rfl
  | leafDrain =>
    simp only [hpc]
    split
    · exact interrupted_PC_safe _ _ (by simp)
    · split
      · cases hp : pendingPush st with
        | none => exact interrupted_PC_safe _ _ (by simp)
        | some p =>
          obtain ⟨t,v⟩ := p
          exact interrupted_exterior g α st t v (by simp [hpc])
      · split
        · exact interrupted_PC_safe _ _ (by simp)
        · split
          · apply interrupted_safe
            simp [changeFrame,refreshKeys,jointUpdate,debit,hpc]
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · rename_i ha
      exact interrupted_finish_PC _ _ ha
    · split
      · exact interrupted_PC_safe _ _ (by simp)
      · exact interrupted_drain_safe g α st _ (by simp [hpc]) (by simp)
  | finishEpisode =>
    simp only [hpc]
    split
    · rename_i ha
      exact interrupted_finish_PC _ _ ha
    · split
      · exact interrupted_PC_safe _ _ (by simp)
      · apply interrupted_safe
        simp [changeFrame,debit] <;> (try split_ifs) <;> simp
  | restartDrain =>
    simp only [hpc]
    split
    · rename_i ha
      exact interrupted_PC_ancestor _ _ ha
    · split
      · exact interrupted_drain_safe g α st _ (by simp [hpc]) (by simp)
      · apply interrupted_safe
        simp [changeFrame,debit]
  | normal =>
    simp only [hpc]
    exact interrupted_end g α _ hstack hi
  | interrupted =>
    simp only [hpc]
    exact interrupted_end g α _ hstack hi

lemma interrupted_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    InterruptedInvariant (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using interrupted_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      interrupted_step m g s α ℓ schedule _ (stack_run m g s α q ℓ schedule t) ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ReturnDensityControl

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma return_density_safe (g : InputGraph n) (ℓ : ℕ) (st : RecursiveState n)
    (ha : (st.frames st.top).pc ≠ .afterChild)
    (hf : (st.frames st.top).pc ≠ .finishEpisode) (hn : (st.frames st.top).pc ≠ .normal) :
    ReturnDensity g ℓ st :=
  ⟨fun h => False.elim (ha h),fun h => False.elim (hf h),fun h => False.elim (hn h)⟩

lemma return_density_PC_safe (g : InputGraph n) (ℓ : ℕ) (st : RecursiveState n) (pc : NormalizePC)
    (ha : pc ≠ .afterChild) (hf : pc ≠ .finishEpisode) (hn : pc ≠ .normal) :
    ReturnDensity g ℓ (changePC st pc) := by
  apply return_density_safe
  · simpa [changePC,changeFrame] using ha
  · simpa [changePC,changeFrame] using hf
  · simpa [changePC,changeFrame] using hn

lemma density_changeFrame (g : InputGraph n) (ℓ j : ℕ) (q : ℝ) (st : RecursiveState n)
    (f : NormalizeFrame n → NormalizeFrame n)
    (ha : (f (st.frames st.top)).active = (st.frames st.top).active)
    (hr : (f (st.frames st.top)).residual = (st.frames st.top).residual) :
    ActiveDensity g ℓ j q (changeFrame st st.top f) ↔ ActiveDensity g ℓ j q st := by
  unfold ActiveDensity
  have hH := observe_changeFrame (fun f => f.active) st st.top f ha j
  have hR := observe_changeFrame (fun f => f.residual) st st.top f hr j
  rw [hH,hR]

lemma density_PC (g : InputGraph n) (ℓ j : ℕ) (q : ℝ) (st : RecursiveState n) (pc : NormalizePC) :
    ActiveDensity g ℓ j q (changePC st pc) ↔ ActiveDensity g ℓ j q st :=
  density_changeFrame g ℓ j q st _ rfl rfl

lemma any_exhausted_PC (st : RecursiveState n) (pc : NormalizePC) :
    anyExhausted (changePC st pc) ↔ anyExhausted st := by
  unfold anyExhausted exhausted changePC changeFrame
  simp only [Function.update_apply]
  constructor <;> rintro ⟨i,hi,he⟩ <;> refine ⟨i,hi,?_⟩ <;>
    by_cases heq : i = st.top <;> simp_all

lemma return_density_after_exhausted (g : InputGraph n) (ℓ : ℕ) (st : RecursiveState n)
    (he : anyExhausted st) : ReturnDensity g ℓ (changePC st .afterChild) := by
  refine ⟨fun _ hn => False.elim (hn ((any_exhausted_PC st _).mpr he)),?_,?_⟩ <;>
    intro h <;> simp [changePC,changeFrame] at h

lemma return_density_after_good (g : InputGraph n) (ℓ : ℕ) (st : RecursiveState n)
    (hp : pendingPush st = none) (hd : ActiveDensity g ℓ st.top (st.frames st.top).theta st) :
    ReturnDensity g ℓ (changePC st .afterChild) := by
  refine ⟨fun _ _ => ⟨(pending_PC st _).trans hp,?_⟩,?_,?_⟩
  · simpa only [changePC,changeFrame,Function.update_self] using (density_PC g ℓ st.top _ st .afterChild).mpr hd
  · intro h; simp [changePC,changeFrame] at h
  · intro h; simp [changePC,changeFrame] at h

lemma return_density_finish (g : InputGraph n) (ℓ : ℕ) (st : RecursiveState n)
    (hd : ActiveDensity g ℓ st.top (st.frames st.top).theta st) :
    ReturnDensity g ℓ (changePC st .finishEpisode) := by
  refine ⟨?_,fun _ => ?_,?_⟩
  · intro h; simp [changePC,changeFrame] at h
  · simpa only [changePC,changeFrame,Function.update_self] using (density_PC g ℓ st.top _ st .finishEpisode).mpr hd
  · intro h; simp [changePC,changeFrame] at h

lemma return_density_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    ReturnDensity g ℓ (recursiveInit g s q ℓ schedule) := by
  apply return_density_safe <;> simp [recursiveInit,freshFrame,emptyFrame]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ReturnDensityEnd

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma pending_none_of_empty (st : RecursiveState n)
    (he : ∀ i ≤ st.top, (st.frames i).exterior = ∅) : pendingPush st = none := by
  classical
  have hh : ((Finset.range (st.top+1)).filter fun i => (st.frames i).exterior.Nonempty) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hr,hn⟩ := Finset.mem_filter.mp hi
    rw [he i (by simpa using Finset.mem_range.mp hr)] at hn
    exact Finset.not_nonempty_empty hn
  simp [pendingPush,hh]

lemma pending_restrict_top (st : RecursiveState n) (k : ℕ) (hk : k ≤ st.top)
    (hp : pendingPush st = none) : pendingPush {st with top := k} = none :=
  pending_none_of_empty _ (fun i hi => pending_none_queues_empty st hp i (hi.trans hk))

lemma return_density_end (g : InputGraph n) (α : ℝ) (ℓ : ℕ) (st : RecursiveState n)
    (hstack : StackInvariant st) (hreg : RegionInvariant st) (hnum : NumericalInvariant g st)
    (hkeys : KeysInvariant g st) (hparam : ParameterInvariant st) (hth : ThresholdRelation st)
    (hlayer : LayerIdentity g st) (hdepth : st.top ≤ ℓ)
    (hdrain : ReturnDrained st) (hint : InterruptedInvariant st)
    (hi : ReturnDensity g ℓ st)
    (hpc : (st.frames st.top).pc = .normal ∨ (st.frames st.top).pc = .interrupted) :
    ReturnDensity g ℓ (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · rename_i ht
    let j := st.top-1
    have hj : j < st.top := by dsimp [j]; omega
    have hs := hstack j hj
    have hje : j+1=st.top := by dsimp [j]; omega
    have hex : (st.frames st.top).pc ≠ .afterChild := by rcases hpc with h|h <;> simp [h]
    refine ⟨?_,?_,?_⟩
    · intro _ hnot
      rcases hpc with hn|hintpc
      · have hp := hdrain (Or.inl hn)
        have hr := return_conditions_from_density g ℓ st.top st hreg hnum hkeys le_rfl hp (hi.2.2 hn)
        have hd : ActiveDensity g ℓ j (st.frames j).theta st :=
          parent_density_of_return g ℓ j st hdepth hj hlayer hparam hth (by simpa [hje] using hr)
        exact ⟨pending_restrict_top st j (Nat.sub_le _ _) hp,hd⟩
      · obtain ⟨i,hij,he⟩ := hint hintpc
        exact False.elim (hnot ⟨i,by change i ≤ st.top-1; omega,he⟩)
    · intro hh
      have : (st.frames j).pc = .finishEpisode := hh
      rw [hs] at this
      contradiction
    · intro hh
      have : (st.frames j).pc = .normal := hh
      rw [hs] at this
      contradiction

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ReturnDensityStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma return_density_exterior_safe (g : InputGraph n) (α : ℝ) (ℓ : ℕ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (ha : (st.frames st.top).pc ≠ .afterChild)
    (hf : (st.frames st.top).pc ≠ .finishEpisode) (hn : (st.frames st.top).pc ≠ .normal) :
    ReturnDensity g ℓ (exteriorPush g α st t v) := by
  apply return_density_safe
  · simpa only [top_exterior,frame_pc_exterior] using ha
  · simpa only [top_exterior,frame_pc_exterior] using hf
  · simpa only [top_exterior,frame_pc_exterior] using hn

lemma return_density_drain_safe (g : InputGraph n) (α : ℝ) (ℓ : ℕ) (st : RecursiveState n)
    (pc : NormalizePC) (ha : (st.frames st.top).pc ≠ .afterChild)
    (hf : (st.frames st.top).pc ≠ .finishEpisode) (hn : (st.frames st.top).pc ≠ .normal)
    (hpa : pc ≠ .afterChild) (hpf : pc ≠ .finishEpisode) (hpn : pc ≠ .normal) :
    ReturnDensity g ℓ (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact return_density_PC_safe g ℓ _ pc hpa hpf hpn
  · cases he : pendingPush st with
    | none => exact return_density_PC_safe g ℓ _ pc hpa hpf hpn
    | some p => obtain ⟨t,v⟩ := p; exact return_density_exterior_safe g α ℓ st t v ha hf hn

set_option maxHeartbeats 1500000 in
lemma return_density_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hstack : StackInvariant st) (hreg : RegionInvariant st) (hnum : NumericalInvariant g st)
    (hkeys : KeysInvariant g st) (hparam : ParameterInvariant st) (hth : ThresholdRelation st)
    (hlayer : LayerIdentity g st) (hdepth : st.top ≤ ℓ) (hc : CacheControlInvariant ℓ st)
    (hdrain : ReturnDrained st) (hint : InterruptedInvariant st)
    (hi : ReturnDensity g ℓ st) : ReturnDensity g ℓ (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hcomp : componentComplete st
  · simp only [hcomp,ite_true]
    exact hi
  simp only [hcomp,ite_false]
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact return_density_PC_safe g ℓ _ _ (by simp) (by simp) (by simp)
    · split
      · exact return_density_drain_safe g α ℓ st _ (by simp [hpc]) (by simp [hpc])
          (by simp [hpc]) (by simp) (by simp) (by simp)
      · split
        · rename_i he
          simp [ReturnDensity,ActiveDensity,changePC,changeFrame,debit,he]
        · exact return_density_PC_safe g ℓ _ _ (by simp) (by simp) (by simp)
  | beginEpisode =>
    simp only [hpc]
    apply return_density_safe <;>
      simp [changeFrame,debit] <;> (try split_ifs) <;> simp
  | fullSolve =>
    simp only [hpc]
    split
    · rename_i he
      exact return_density_after_exhausted g ℓ _ he
    · split
      · exact return_density_PC_safe g ℓ _ _ (by simp) (by simp) (by simp)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · rename_i he
      exact return_density_after_exhausted g ℓ _ he
    · split
      · exact return_density_PC_safe g ℓ _ _ (by simp) (by simp) (by simp)
      · apply return_density_safe <;> simp [freshFrame,emptyFrame]
  | leafDrain =>
    simp only [hpc]
    split
    · rename_i he
      exact return_density_after_exhausted g ℓ _ he
    · split
      · cases hp : pendingPush st with
        | none => exact return_density_PC_safe g ℓ _ _ (by simp) (by simp) (by simp)
        | some p =>
          obtain ⟨t,v⟩ := p
          exact return_density_exterior_safe g α ℓ st t v (by simp [hpc]) (by simp [hpc]) (by simp [hpc])
      · rename_i hp
        have hn : pendingPush st = none := by cases h : pendingPush st <;> simp_all
        split
        · rename_i hh
          have hlevel := (hc st.top le_rfl).2.1 hpc
          exact return_density_after_good g ℓ _ hn (leaf_density_of_high_empty g ℓ st hkeys hlevel hh)
        · split
          · apply return_density_safe <;> simp [changeFrame,refreshKeys,jointUpdate,debit,hpc]
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact return_density_PC_safe g ℓ _ _ (by simp) (by simp) (by simp)
    · rename_i ha
      split
      · exact return_density_PC_safe g ℓ _ _ (by simp) (by simp) (by simp)
      · rename_i he
        have hn : ¬anyExhausted st := by simp [any_exhausted_iff,ha,he]
        have hcert := hi.1 hpc hn
        simp only [if_neg hn,hcert.1]
        exact return_density_finish g ℓ _ hcert.2
  | finishEpisode =>
    simp only [hpc]
    split
    · exact return_density_PC_safe g ℓ _ _ (by simp) (by simp) (by simp)
    · split
      · exact return_density_PC_safe g ℓ _ _ (by simp) (by simp) (by simp)
      · have hden := hi.2.1 hpc
        by_cases heq : (st.frames st.top).theta = (st.frames st.top).q
        · simpa [ReturnDensity,ActiveDensity,changeFrame,finishEpisode,debit,heq] using hden
        · apply return_density_safe <;> simp [changeFrame,finishEpisode,debit,heq]
  | restartDrain =>
    simp only [hpc]
    split
    · exact return_density_PC_safe g ℓ _ _ (by simp) (by simp) (by simp)
    · split
      · exact return_density_drain_safe g α ℓ st _ (by simp [hpc]) (by simp [hpc])
          (by simp [hpc]) (by simp) (by simp) (by simp)
      · apply return_density_safe <;> simp [changeFrame,debit]
  | normal =>
    simp only [hpc]
    exact return_density_end g α ℓ _ hstack hreg hnum hkeys hparam hth hlayer hdepth hdrain hint hi (Or.inl hpc)
  | interrupted =>
    simp only [hpc]
    exact return_density_end g α ℓ _ hstack hreg hnum hkeys hparam hth hlayer hdepth hdrain hint hi (Or.inr hpc)

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

-- Proof module: Solutions.SuccessfulRequestBounds

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma successful_finish_density (g : InputGraph n) (ℓ : ℕ) (st : RecursiveState n)
    (hp : ParameterInvariant st) (hb : BudgetInvariant st) (hscale : ScaleInvariant st)
    (hr : ReturnDensity g ℓ st) (hpc : (st.frames st.top).pc = .finishEpisode)
    (hθ : (st.frames st.top).theta ≠ (st.frames st.top).q)
    (hμ : (st.frames st.top).Q/2 ≤ ∑ v ∈ (st.frames st.top).active, (st.frames st.top).residual v) :
    (st.frames st.top).q*(st.frames st.top).block < 2*(∑ v ∈ (st.frames st.top).active, (st.frames st.top).residual v) ∧
      ∀ v ∈ (st.frames st.top).active, (st.frames st.top).residual v ≤
        (kappa ℓ 0 : ℝ)*(2*(∑ w ∈ (st.frames st.top).active, (st.frames st.top).residual w)/(st.frames st.top).block)*
          LocalPush.deg g.graph v := by
  have hopen : (st.frames st.top).openBudget = true := by simpa [hpc,budgetPC] using hb st.top le_rfl
  have hθq := (hp st.top le_rfl).2.2 hopen
  have hθgt : (st.frames st.top).q < (st.frames st.top).theta := lt_of_le_of_ne hθq (Ne.symm hθ)
  have hbpos : (0 : ℝ) < (st.frames st.top).block := by
    have hh := (hp st.top le_rfl).2.1
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hh
  have hQ := hscale.1 st.top le_rfl hopen
  have hθmass : (st.frames st.top).theta ≤
      2*(∑ w ∈ (st.frames st.top).active, (st.frames st.top).residual w)/(st.frames st.top).block := by
    apply (le_div_iff₀ hbpos).mpr
    linarith
  have hk : (kappa ℓ st.top : ℝ) ≤ (kappa ℓ 0 : ℝ) := by
    unfold kappa
    exact_mod_cast Nat.add_le_add_right (Nat.sub_le ℓ st.top) 3
  have hqpos := (hp st.top le_rfl).1
  have hθpos : 0 ≤ (st.frames st.top).theta := hqpos.le.trans hθq
  refine ⟨?_,?_⟩
  · have hh := mul_lt_mul_of_pos_right hθgt hbpos
    linarith
  · intro v hv
    have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
    calc
      _ ≤ (kappa ℓ st.top : ℝ)*(st.frames st.top).theta*LocalPush.deg g.graph v := hr.2.1 hpc v hv
      _ ≤ (kappa ℓ 0 : ℝ)*(st.frames st.top).theta*LocalPush.deg g.graph v := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hθpos) hd
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθmass (by positivity)) hd

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NormalizationProof

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma return_density_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ReturnDensity g ℓ (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using return_density_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      return_density_step m g s α ℓ schedule _
        (stack_run m g s α q ℓ schedule t)
        (region_run m g s α q ℓ schedule t)
        (numerical_run m g s α q hα hq hs ℓ schedule t)
        (keys_run m g s α q hq.le ℓ schedule t)
        (parameters_run m g s α q hq ℓ schedule t)
        (threshold_relation_run m g s α q ℓ schedule t)
        (layer_run m g s α q ℓ schedule t)
        (depth_run m g s α q ℓ schedule t)
        (cache_run m g s α q ℓ schedule t)
        (return_drained_run m g s α q ℓ schedule t)
        (interrupted_run m g s α q ℓ schedule t) ih

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

lemma finish_requested_run_bounds (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ)
    (hfinish : currentPC (recursiveRun m g s α q ℓ schedule t) = .finishEpisode)
    (hrunning : (recursiveRun m g s α q ℓ schedule (t+2)).done = false)
    (hfull : currentPC (recursiveRun m g s α q ℓ schedule (t+2)) = .fullSolve) :
    let st := recursiveRun m g s α q ℓ schedule t
    (st.frames st.top).q*(st.frames st.top).block < 2*(∑ v ∈ (st.frames st.top).active, (st.frames st.top).residual v) ∧
      ∀ v ∈ (st.frames st.top).active, (st.frames st.top).residual v ≤
        (kappa ℓ 0 : ℝ)*(2*(∑ w ∈ (st.frames st.top).active, (st.frames st.top).residual w)/(st.frames st.top).block)*
          LocalPush.deg g.graph v := by
  classical
  intro st
  let mid := recursiveRun m g s α q ℓ schedule (t+1)
  have hstep1 : mid = recursiveStep m g s α ℓ schedule st := by
    simp only [mid,st,recursiveRun,Function.iterate_succ_apply']
  have hstep2 : recursiveRun m g s α q ℓ schedule (t+2) = recursiveStep m g s α ℓ schedule mid := by
    rw [show t+2 = (t+1)+1 by omega]
    simp only [mid,recursiveRun,Function.iterate_succ_apply']
  have hmidrunning : mid.done = false := (running_step_guards m g s α ℓ schedule mid (by rwa [←hstep2])).1
  have hmidpc : currentPC mid = .beginEpisode := by
    simpa only [mid,show t+1+1=t+2 by omega] using
      full_solve_run_origin m g s α q hq.le hs ℓ schedule (t+1) (by simpa only [show t+1+1=t+2 by omega] using hrunning)
        (by simpa only [show t+1+1=t+2 by omega] using hfull)
  have hft := finish_to_begin_transition m g s α ℓ schedule st hfinish (by rwa [←hstep1]) (by rwa [←hstep1])
  rw [←hstep1] at hft
  have hprior := full_solve_run_prior_data m g s α q hq.le hs ℓ schedule (t+1)
    (by simpa only [show t+1+1=t+2 by omega] using hrunning) (by simpa only [show t+1+1=t+2 by omega] using hfull)
  have hneed : (mid.frames mid.top).needFull = true := hprior.2.1
  rw [hft.2.2.2.1,hft.2.2.2.2.2.2.2] at hneed
  apply successful_finish_density g ℓ st (parameters_run m g s α q hq ℓ schedule t)
    (budget_run m g s α q ℓ schedule t) (scale_run m g s α q hq ℓ schedule t)
    (return_density_run m g s α q hα hq hs ℓ schedule t) hfinish hft.2.2.1
  exact of_decide_eq_true hneed

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

lemma successful_full_event_bounds (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (he : fullSolveEvent g (recursiveRun m g s α q ℓ schedule t) id)
    (hfinish : currentPC (recursiveRun m g s α q ℓ schedule (t-2))=.finishEpisode) :
    let st := recursiveRun m g s α q ℓ schedule t
    (st.frames st.top).q*(st.frames st.top).block < 2*(∑ v ∈ (st.frames st.top).active, (st.frames st.top).residual v) ∧
      ∀ v ∈ (st.frames st.top).active, (st.frames st.top).residual v ≤
        (kappa ℓ 0 : ℝ)*(2*(∑ w ∈ (st.frames st.top).active, (st.frames st.top).residual w)/(st.frames st.top).block)*
          LocalPush.deg g.graph v := by
  intro st
  have ht := full_event_time_ge_two m g s α q hq.le hs ℓ schedule t id he
  have htime : t-2+2=t := by omega
  have hdata := full_event_request_data m g s α q hq.le hs ℓ schedule t id he
  have hh := finish_requested_run_bounds m g s α q hα hq hs ℓ schedule (t-2) hfinish
    (by simpa only [htime] using he.1) (by simpa only [currentPC,htime] using he.2.2.1)
  have hqeq : (st.frames st.top).q=((recursiveRun m g s α q ℓ schedule (t-2)).frames
      (recursiveRun m g s α q ℓ schedule (t-2)).top).q := congrArg Prod.fst hdata.2.2.2.2
  have hbeq : (st.frames st.top).block=((recursiveRun m g s α q ℓ schedule (t-2)).frames
      (recursiveRun m g s α q ℓ schedule (t-2)).top).block := congrArg (fun f => f.2.2.1) hdata.2.2.2.2
  have hHeq : (st.frames st.top).active=((recursiveRun m g s α q ℓ schedule (t-2)).frames (recursiveRun m g s α q ℓ schedule (t-2)).top).active := hdata.2.2.1
  have hReq : (st.frames st.top).residual=((recursiveRun m g s α q ℓ schedule (t-2)).frames (recursiveRun m g s α q ℓ schedule (t-2)).top).residual := hdata.2.2.2.1
  rw [hHeq,hReq,hqeq,hbeq]
  exact hh

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation

theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (he : fullSolveEvent g (recursiveRun m g s α q ℓ schedule t) id)
    (hfinish : currentPC (recursiveRun m g s α q ℓ schedule (t-2))=.finishEpisode) :
    let st := recursiveRun m g s α q ℓ schedule t
    (st.frames st.top).q*(st.frames st.top).block < 2*(∑ v ∈ (st.frames st.top).active, (st.frames st.top).residual v) ∧
      ∀ v ∈ (st.frames st.top).active, (st.frames st.top).residual v ≤
        (kappa ℓ 0 : ℝ)*(2*(∑ w ∈ (st.frames st.top).active, (st.frames st.top).residual w)/(st.frames st.top).block)*
          LocalPush.deg g.graph v := by
  exact successful_full_event_bounds m g s α q hα hq hs ℓ schedule t id he hfinish

