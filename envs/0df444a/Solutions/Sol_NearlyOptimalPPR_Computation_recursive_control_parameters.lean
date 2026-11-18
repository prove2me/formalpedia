-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_control_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:31:31.730345+00:00
-- url     : https://prove2.me/submissions/b901b13e-873f-43c9-b13e-e80874e01656

import Definitions.Def_NearlyOptimalPPR_Computation_proof_invariants


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

set_option maxHeartbeats 1000000 in
lemma depth_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hi : st.top ≤ ℓ) :
    (recursiveStep m g s α ℓ schedule st).top ≤ ℓ := by
  classical
  cases hp : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hp,debit] <;> (try split_ifs) <;> simp_all <;> omega
  | some p =>
    obtain ⟨t,v⟩ := p
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hp,debit] <;> (try split_ifs) <;> simp_all <;> omega

lemma depth_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    (recursiveRun m g s α q ℓ schedule t).top ≤ ℓ := by
  induction t with
  | zero => simp [recursiveRun,recursiveInit]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using depth_step m g s α ℓ schedule _ ih

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

namespace NearlyOptimalPPR.Computation
variable {n : ℕ}
lemma frame_pc_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) (i : ℕ) :
    ((exteriorPush g α st t v).frames i).pc = (st.frames i).pc :=
  congrArg (fun z => z.2.2.2.1) (exterior_parameters g α st t v i)
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetControl

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma budget_transport (st u : RecursiveState n) (hi : BudgetInvariant st)
    (ht : u.top ≤ st.top)
    (hf : ∀ i ≤ u.top, ((u.frames i).openBudget,(u.frames i).pc) =
      ((st.frames i).openBudget,(st.frames i).pc)) : BudgetInvariant u := by
  intro i hh
  have he := hf i hh
  obtain ⟨hb,hpc⟩ := Prod.mk.inj he
  rw [hb,hpc]
  exact hi i (hh.trans ht)

lemma budget_changeFrame (st : RecursiveState n) (hi : BudgetInvariant st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hf : j ≤ st.top → (f (st.frames j)).openBudget = budgetPC (f (st.frames j)).pc) :
    BudgetInvariant (changeFrame st j f) := by
  intro i hh
  have his : i ≤ st.top := hh
  by_cases he : i = j
  · subst i
    simpa [changeFrame] using hf his
  · simpa [changeFrame,he] using hi i his

lemma budget_changePC (st : RecursiveState n) (hi : BudgetInvariant st)
    (pc : NormalizePC) (hpc : (st.frames st.top).openBudget = budgetPC pc) :
    BudgetInvariant (changePC st pc) := by
  apply budget_changeFrame st hi st.top _
  intro _
  exact hpc

lemma budget_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hi : BudgetInvariant st) :
    BudgetInvariant (exteriorPush g α st t v) := by
  apply budget_transport st (exteriorPush g α st t v) hi (by simp)
  intro i hh
  have he := exterior_parameters g α st t v i
  exact congrArg (fun z => (z.2.2.1,z.2.2.2.1)) he

lemma budget_init (g : InputGraph n) (s : Fin n) (q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) : BudgetInvariant (recursiveInit g s q ℓ schedule) := by
  intro i hi
  have he : i = 0 := by change i ≤ 0 at hi; omega
  subst i
  simp [recursiveInit,freshFrame,emptyFrame,budgetPC]

lemma budget_finish_update (st : RecursiveState n) (hi : BudgetInvariant st)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hf : (f {st.frames st.top with openBudget := false, cache := ∅}).openBudget =
      budgetPC (f {st.frames st.top with openBudget := false, cache := ∅}).pc) :
    BudgetInvariant (changeFrame (finishEpisode st) st.top f) := by
  intro i hh
  have his : i ≤ st.top := hh
  by_cases he : i = st.top
  · subst i
    simpa [changeFrame,finishEpisode] using hf
  · simpa [changeFrame,finishEpisode,he] using hi i his

lemma budget_finishPC (st : RecursiveState n) (hi : BudgetInvariant st)
    (pc : NormalizePC) (hp : budgetPC pc = false) :
    BudgetInvariant (changePC (finishEpisode st) pc) := by
  apply budget_finish_update st hi
  simp [hp]

lemma budget_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (hi : BudgetInvariant st) : BudgetInvariant (jointUpdate g α st h) := by
  intro i hh
  have his : i ≤ st.top := hh
  simpa [jointUpdate,his] using hi i his

lemma budget_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : BudgetInvariant st) : BudgetInvariant (refreshKeys g st T) := by
  intro i hh
  have his : i ≤ st.top := hh
  simpa [refreshKeys,his] using hi i his

lemma budget_newFrame (st : RecursiveState n) (f : NormalizeFrame n)
    (hi : BudgetInvariant st) (hf : f.openBudget = budgetPC f.pc) :
    BudgetInvariant {st with top := st.top+1, frames := Function.update st.frames (st.top+1) f} := by
  intro i hh
  change i ≤ st.top+1 at hh
  by_cases he : i = st.top+1
  · subst i
    simpa using hf
  · have his : i ≤ st.top := by omega
    simpa [he] using hi i his

lemma budget_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : BudgetInvariant st) : BudgetInvariant (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · intro i hh
    exact hi i (hh.trans (Nat.sub_le _ _))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma budget_PC_same (st : RecursiveState n) (pc : NormalizePC) (hi : BudgetInvariant st)
    (hp : budgetPC pc = budgetPC (st.frames st.top).pc) : BudgetInvariant (changePC st pc) := by
  apply budget_changePC st hi pc
  rw [hp]
  exact hi st.top le_rfl

lemma budget_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : BudgetInvariant st) (pc : NormalizePC)
    (hp : budgetPC pc = budgetPC (st.frames st.top).pc) :
    BudgetInvariant (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact budget_PC_same _ pc hi hp
  · cases h : pendingPush st with
    | none => exact budget_PC_same _ pc hi hp
    | some p => obtain ⟨t,v⟩ := p; exact budget_exterior g α st t v hi

set_option maxHeartbeats 1000000 in
lemma budget_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hi : BudgetInvariant st) : BudgetInvariant (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]
    exact hi
  simp only [hc,ite_false]
  have hb := hi st.top le_rfl
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact budget_PC_same _ _ hi (by simp [hpc,budgetPC,debit])
    · split
      · exact budget_drain g α st hi _ (by simp [hpc,budgetPC])
      · split <;> exact budget_PC_same _ _ hi (by simp [hpc,budgetPC,debit])
  | beginEpisode =>
    simp only [hpc]
    apply budget_changeFrame _ (by exact hi)
    intro _
    split_ifs <;> rfl
  | fullSolve =>
    simp only [hpc]
    split
    · exact budget_PC_same _ _ hi (by simp [hpc,budgetPC,debit])
    · split
      · apply budget_changePC
        · unfold BudgetInvariant
          exact budget_refresh g _ (touchedBy g (st.frames st.top).active) (budget_joint g α st _ hi)
        · simpa [hpc,budgetPC,debit,refreshKeys,jointUpdate] using hb
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact budget_PC_same _ _ hi (by simp [hpc,budgetPC,debit])
    · split
      · exact budget_PC_same _ _ hi (by simp [hpc,budgetPC,debit])
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : BudgetInvariant up := by
          apply budget_changeFrame u (by exact hi)
          intro _
          simpa [u,debit,hpc,budgetPC] using hb
        exact budget_newFrame up c hup rfl
  | leafDrain =>
    simp only [hpc]
    split
    · exact budget_PC_same _ _ hi (by simp [hpc,budgetPC,debit])
    · split
      · cases hp : pendingPush st with
        | none => exact budget_PC_same _ _ hi (by simp [hpc,budgetPC,debit])
        | some p => obtain ⟨t,v⟩ := p; exact budget_exterior g α st t v hi
      · split
        · exact budget_PC_same _ _ hi (by simp [hpc,budgetPC,debit])
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : BudgetInvariant u := by
              apply budget_changeFrame st hi
              intro _
              exact hb
            unfold BudgetInvariant
            exact budget_refresh g _ (touchedBy g C) (budget_joint g α u _ hu)
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact budget_finishPC _ hi _ rfl
    · split
      · exact budget_finishPC _ hi _ rfl
      · exact budget_drain g α st hi _ (by simp [hpc,budgetPC])
  | finishEpisode =>
    simp only [hpc]
    split
    · exact budget_finishPC _ hi _ rfl
    · split
      · exact budget_finishPC _ hi _ rfl
      · apply budget_finish_update _ (by exact hi)
        split_ifs <;> rfl
  | restartDrain =>
    simp only [hpc]
    split
    · exact budget_PC_same _ _ hi (by simp [hpc,budgetPC,debit])
    · split
      · exact budget_drain g α st hi _ (by simp [hpc,budgetPC])
      · apply budget_changeFrame _ (by exact hi)
        intro _
        simpa [hpc,budgetPC,debit] using hb
  | normal =>
    simp only [hpc]
    exact budget_end g α _ hi
  | interrupted =>
    simp only [hpc]
    exact budget_end g α _ hi

lemma budget_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    BudgetInvariant (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using budget_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using budget_step m g s α ℓ schedule _ ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ParameterInvariant

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma blockScale_positive (schedule : BlockSchedule) (ℓ j : ℕ) (N : ℝ) :
    1 ≤ blockScale schedule ℓ j N := by
  cases hs : schedule[j]? with
  | none => simp [blockScale,hs]
  | some b => cases b <;> simp [blockScale,hs]

lemma parameters_transport (st u : RecursiveState n) (hi : ParameterInvariant st)
    (ht : u.top ≤ st.top)
    (hf : ∀ i ≤ u.top, frameParameters (u.frames i) = frameParameters (st.frames i)) :
    ParameterInvariant u := by
  intro i hh
  have he := hf i hh
  have hp := hi i (hh.trans ht)
  have hfields : (u.frames i).q = (st.frames i).q ∧
      (u.frames i).theta = (st.frames i).theta ∧
      (u.frames i).openBudget = (st.frames i).openBudget ∧
      (u.frames i).pc = (st.frames i).pc ∧
      (u.frames i).N = (st.frames i).N ∧
      (u.frames i).block = (st.frames i).block ∧ (u.frames i).id = (st.frames i).id := by
    simpa only [frameParameters,Prod.mk.injEq] using he
  simpa only [FrameParametersPositive,hfields.1,hfields.2.1,hfields.2.2.1,
    hfields.2.2.2.2.2.1] using hp

lemma parameters_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hi : ParameterInvariant st) :
    ParameterInvariant (exteriorPush g α st t v) := by
  apply parameters_transport st (exteriorPush g α st t v) hi (by simp)
  intro i _
  exact exterior_parameters g α st t v i

lemma parameters_changeFrame (st : RecursiveState n) (hi : ParameterInvariant st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hf : j ≤ st.top → FrameParametersPositive (f (st.frames j))) :
    ParameterInvariant (changeFrame st j f) := by
  intro i hh
  have his : i ≤ st.top := hh
  by_cases he : i = j
  · subst i
    simpa [changeFrame] using hf his
  · simpa [changeFrame,he] using hi i his

lemma parameters_metadata (st : RecursiveState n) (hi : ParameterInvariant st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hq : (f (st.frames j)).q = (st.frames j).q)
    (hb : (f (st.frames j)).block = (st.frames j).block)
    (hθ : (f (st.frames j)).theta = (st.frames j).theta)
    (ho : (f (st.frames j)).openBudget = (st.frames j).openBudget) :
    ParameterInvariant (changeFrame st j f) := by
  apply parameters_changeFrame st hi j f
  intro hh
  simpa only [FrameParametersPositive,hq,hb,hθ,ho] using hi j hh

lemma parameters_episode (f : NormalizeFrame n) (hf : FrameParametersPositive f) (μ : ℝ) :
    FrameParametersPositive {f with theta := max μ (f.q*f.block)/f.block, openBudget := true} := by
  have hb : (0 : ℝ) < (f.block : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hf.2.1)
  refine ⟨hf.1,hf.2.1,?_⟩
  intro _
  exact (le_div_iff₀ hb).mpr (le_max_right μ (f.q*(f.block : ℝ)))

lemma parameters_init (g : InputGraph n) (s : Fin n) (q : ℝ) (hq : 0 < q)
    (ℓ : ℕ) (schedule : BlockSchedule) : ParameterInvariant (recursiveInit g s q ℓ schedule) := by
  intro i hi
  have he : i = 0 := by change i ≤ 0 at hi; omega
  subst i
  simpa [recursiveInit,freshFrame,emptyFrame,FrameParametersPositive] using
    And.intro hq (blockScale_positive schedule ℓ 0 (1/q))

lemma parameters_PC (st : RecursiveState n) (pc : NormalizePC) (hi : ParameterInvariant st) :
    ParameterInvariant (changePC st pc) := parameters_metadata st hi st.top _ rfl rfl rfl rfl

lemma parameters_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (hi : ParameterInvariant st) : ParameterInvariant (jointUpdate g α st h) := by
  apply parameters_transport st (jointUpdate g α st h) hi le_rfl
  intro i hh
  have his : i ≤ st.top := hh
  simp [jointUpdate,his,frameParameters]

lemma parameters_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : ParameterInvariant st) : ParameterInvariant (refreshKeys g st T) := by
  apply parameters_transport st (refreshKeys g st T) hi le_rfl
  intro i hh
  have his : i ≤ st.top := hh
  simp [refreshKeys,his,frameParameters]

lemma parameters_finish (st : RecursiveState n) (hi : ParameterInvariant st) :
    ParameterInvariant (finishEpisode st) := by
  apply parameters_changeFrame _ (by exact hi) st.top
  intro hh
  have hf := hi st.top hh
  exact ⟨hf.1,hf.2.1,by simp⟩

lemma parameters_newFrame (st : RecursiveState n) (f : NormalizeFrame n)
    (hi : ParameterInvariant st) (hf : FrameParametersPositive f) :
    ParameterInvariant {st with top := st.top+1, frames := Function.update st.frames (st.top+1) f} := by
  intro i hh
  change i ≤ st.top+1 at hh
  by_cases he : i = st.top+1
  · subst i
    simpa using hf
  · have his : i ≤ st.top := by omega
    simpa [he] using hi i his

lemma parameters_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : ParameterInvariant st) : ParameterInvariant (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · intro i hh
    exact hi i (hh.trans (Nat.sub_le _ _))

lemma parameters_control (st : RecursiveState n) (hi : ParameterInvariant st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hf : parameterView (f (st.frames j)) = parameterView (st.frames j)) :
    ParameterInvariant (changeFrame st j f) := by
  have hh : (f (st.frames j)).q = (st.frames j).q ∧
      (f (st.frames j)).block = (st.frames j).block ∧
      (f (st.frames j)).theta = (st.frames j).theta ∧
      (f (st.frames j)).openBudget = (st.frames j).openBudget := by
    simpa only [parameterView,Prod.mk.injEq] using hf
  exact parameters_metadata st hi j f hh.1 hh.2.1 hh.2.2.1 hh.2.2.2

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ParameterStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma parameters_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : ParameterInvariant st) (pc : NormalizePC) :
    ParameterInvariant (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact parameters_PC _ pc hi
  · cases hp : pendingPush st with
    | none => exact parameters_PC _ pc hi
    | some p => obtain ⟨t,v⟩ := p; exact parameters_exterior g α st t v hi

set_option maxHeartbeats 1000000 in
lemma parameters_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hi : ParameterInvariant st) (hbudget : BudgetInvariant st) :
    ParameterInvariant (recursiveStep m g s α ℓ schedule st) := by
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
    · exact parameters_PC _ _ hi
    · split
      · exact parameters_drain g α st hi _
      · split <;> exact parameters_PC _ _ hi
  | beginEpisode =>
    simp only [hpc]
    apply parameters_changeFrame _ (by exact hi)
    intro hh
    exact parameters_episode (st.frames st.top) (hi st.top le_rfl) _
  | fullSolve =>
    simp only [hpc]
    split
    · exact parameters_PC _ _ hi
    · split
      · apply parameters_PC _ _
        unfold ParameterInvariant FrameParametersPositive
        exact parameters_refresh g _ (touchedBy g (st.frames st.top).active)
          (parameters_joint g α st _ hi)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact parameters_PC _ _ hi
    · split
      · exact parameters_PC _ _ hi
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : ParameterInvariant up := parameters_control u hi st.top _ rfl
        have hopen : (st.frames st.top).openBudget = true := by
          simpa [hpc,budgetPC] using hbudget st.top le_rfl
        have hθ : 0 < (st.frames st.top).theta :=
          lt_of_lt_of_le (hi st.top le_rfl).1 ((hi st.top le_rfl).2.2 hopen)
        apply parameters_newFrame up c hup
        exact ⟨hθ,blockScale_positive schedule ℓ (st.top+1) (st.frames st.top).block,by simp [c,freshFrame,emptyFrame]⟩
  | leafDrain =>
    simp only [hpc]
    split
    · exact parameters_PC _ _ hi
    · split
      · cases hp : pendingPush st with
        | none => exact parameters_PC _ _ hi
        | some p => obtain ⟨t,v⟩ := p; exact parameters_exterior g α st t v hi
      · split
        · exact parameters_PC _ _ hi
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : ParameterInvariant u := parameters_control st hi st.top _ rfl
            unfold ParameterInvariant FrameParametersPositive
            exact parameters_refresh g _ (touchedBy g C) (parameters_joint g α u _ hu)
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact parameters_PC _ _ (parameters_finish _ hi)
    · split
      · exact parameters_PC _ _ (parameters_finish _ hi)
      · exact parameters_drain g α st hi _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact parameters_PC _ _ (parameters_finish _ hi)
    · split
      · exact parameters_PC _ _ (parameters_finish _ hi)
      · apply parameters_control _ _ _ _ rfl
        exact parameters_finish _ hi
  | restartDrain =>
    simp only [hpc]
    split
    · exact parameters_PC _ _ hi
    · split
      · exact parameters_drain g α st hi _
      · exact parameters_control (debit st st.top 1) hi st.top
          (fun fc => {fc with needFull := true, pc := .beginEpisode}) rfl
  | normal =>
    simp only [hpc]
    exact parameters_end g α _ hi
  | interrupted =>
    simp only [hpc]
    exact parameters_end g α _ hi

lemma parameters_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ParameterInvariant (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using parameters_init g s q hq ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using parameters_step m g s α ℓ schedule _ ih
      (budget_run m g s α q ℓ schedule t)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheControl

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

@[simp] lemma cache_state_ite (P : Prop) [Decidable P] (a b : RecursiveState n) (i : ℕ) :
    ((if P then a else b).frames i).cache = if P then (a.frames i).cache else (b.frames i).cache := by
  split <;> rfl
@[simp] lemma cache_frame_ite (P : Prop) [Decidable P] (a b : NormalizeFrame n) :
    (if P then a else b).cache = if P then a.cache else b.cache := by split <;> rfl
@[simp] lemma cache_debit (st : RecursiveState n) (j i : ℕ) (w : ℝ≥0∞) :
    ((debit st j w).frames i).cache = (st.frames i).cache := rfl
@[simp] lemma cache_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).cache = (st.frames i).cache := by
  by_cases hh : i ≤ st.top <;> simp [refreshKeys,hh]
@[simp] lemma cache_control (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) (hf : (f (st.frames j)).cache = (st.frames j).cache) (i : ℕ) :
    ((changeFrame st j f).frames i).cache = (st.frames i).cache :=
  observe_changeFrame (fun f => f.cache) st j f hf i

lemma exterior_cache (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) (i : ℕ) :
    ((exteriorPush g α st t v).frames i).cache = (st.frames i).cache := by
  simp only [exteriorPush,cache_debit,cache_refresh,cache_control,cache_state_ite,cache_frame_ite,ite_self]

lemma cache_control_init (g : InputGraph n) (s : Fin n) (q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) : CacheControlInvariant ℓ (recursiveInit g s q ℓ schedule) := by
  intro i hi
  have he : i = 0 := by change i ≤ 0 at hi; omega
  subst i
  simp [recursiveInit,freshFrame,emptyFrame]

lemma cache_control_transport (ℓ : ℕ) (st u : RecursiveState n) (hi : CacheControlInvariant ℓ st)
    (ht : u.top ≤ st.top)
    (hf : ∀ i ≤ u.top, ((u.frames i).cache,(u.frames i).pc) = ((st.frames i).cache,(st.frames i).pc)) :
    CacheControlInvariant ℓ u := by
  intro i hh
  obtain ⟨hc,hpc⟩ := Prod.mk.inj (hf i hh)
  simpa only [hc,hpc] using hi i (hh.trans ht)

lemma cache_control_changeFrame (ℓ : ℕ) (st : RecursiveState n) (hi : CacheControlInvariant ℓ st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hf : j ≤ st.top →
      (j ≠ ℓ → (f (st.frames j)).cache = ∅) ∧
      ((f (st.frames j)).pc = .leafDrain → j = ℓ) ∧
      ((f (st.frames j)).pc = .fullSolve → (f (st.frames j)).cache = ∅)) :
    CacheControlInvariant ℓ (changeFrame st j f) := by
  intro i hh
  have his : i ≤ st.top := hh
  by_cases he : i = j
  · subst i
    simpa [changeFrame] using hf his
  · simpa [changeFrame,he] using hi i his

lemma cache_PC (ℓ : ℕ) (st : RecursiveState n) (hi : CacheControlInvariant ℓ st)
    (pc : NormalizePC) (hl : pc = .leafDrain → st.top = ℓ)
    (hf : pc = .fullSolve → (st.frames st.top).cache = ∅) :
    CacheControlInvariant ℓ (changePC st pc) := by
  apply cache_control_changeFrame ℓ st hi st.top
  intro _
  exact ⟨(hi st.top le_rfl).1,hl,hf⟩

lemma cache_exterior (ℓ : ℕ) (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hi : CacheControlInvariant ℓ st) :
    CacheControlInvariant ℓ (exteriorPush g α st t v) := by
  apply cache_control_transport ℓ st (exteriorPush g α st t v) hi (by simp)
  intro i _
  rw [exterior_cache,frame_pc_exterior]

lemma cache_joint (ℓ : ℕ) (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (hi : CacheControlInvariant ℓ st) :
    CacheControlInvariant ℓ (jointUpdate g α st h) := by
  apply cache_control_transport ℓ st (jointUpdate g α st h) hi le_rfl
  intro i hh
  have his : i ≤ st.top := hh
  simp [jointUpdate,his]

lemma cache_key_refresh (ℓ : ℕ) (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : CacheControlInvariant ℓ st) : CacheControlInvariant ℓ (refreshKeys g st T) := by
  apply cache_control_transport ℓ st (refreshKeys g st T) hi le_rfl
  intro i hh
  have his : i ≤ st.top := hh
  simp [refreshKeys,his]

lemma cache_finish (ℓ : ℕ) (st : RecursiveState n) (hi : CacheControlInvariant ℓ st) :
    CacheControlInvariant ℓ (finishEpisode st) := by
  apply cache_control_changeFrame ℓ _ (by exact hi) st.top
  intro hh
  exact ⟨fun _ => rfl,(hi st.top hh).2.1,fun _ => rfl⟩

lemma cache_newFrame (ℓ : ℕ) (st : RecursiveState n) (f : NormalizeFrame n)
    (hi : CacheControlInvariant ℓ st) (hc : f.cache = ∅)
    (hp : f.pc = .initialDrain) :
    CacheControlInvariant ℓ {st with top := st.top+1, frames := Function.update st.frames (st.top+1) f} := by
  intro i hh
  change i ≤ st.top+1 at hh
  by_cases he : i = st.top+1
  · subst i
    simpa [hc,hp]
  · have his : i ≤ st.top := by omega
    simpa [he] using hi i his

lemma cache_end (ℓ : ℕ) (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : CacheControlInvariant ℓ st) : CacheControlInvariant ℓ (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · intro i hh
    exact hi i (hh.trans (Nat.sub_le _ _))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma cache_drain (ℓ : ℕ) (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : CacheControlInvariant ℓ st) (pc : NormalizePC)
    (hl : pc = .leafDrain → st.top = ℓ)
    (hf : pc = .fullSolve → (st.frames st.top).cache = ∅) :
    CacheControlInvariant ℓ (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact cache_PC ℓ _ hi pc hl hf
  · cases hp : pendingPush st with
    | none => exact cache_PC ℓ _ hi pc hl hf
    | some p => obtain ⟨t,v⟩ := p; exact cache_exterior ℓ g α st t v hi

set_option maxHeartbeats 1000000 in
lemma cache_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hi : CacheControlInvariant ℓ st) : CacheControlInvariant ℓ (recursiveStep m g s α ℓ schedule st) := by
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
    · exact cache_PC ℓ _ hi _ (by simp) (by simp)
    · split
      · exact cache_drain ℓ g α st hi _ (by simp) (by simp)
      · split <;> exact cache_PC ℓ _ hi _ (by simp) (by simp)
  | beginEpisode =>
    simp only [hpc]
    apply cache_control_changeFrame ℓ _ (by exact hi)
    intro _
    split_ifs <;> simp
  | fullSolve =>
    simp only [hpc]
    split
    · exact cache_PC ℓ _ hi _ (by simp) (by simp)
    · split
      · apply cache_PC ℓ _ _ _ (by simp) (by simp)
        unfold CacheControlInvariant
        exact cache_key_refresh ℓ g _ (touchedBy g (st.frames st.top).active) (cache_joint ℓ g α st _ hi)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact cache_PC ℓ _ hi _ (by simp) (by simp)
    · split
      · rename_i he
        exact cache_PC ℓ _ hi _ (fun _ => he) (by simp)
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : CacheControlInvariant ℓ up := by
          apply cache_control_changeFrame ℓ u (by exact hi)
          intro hh
          exact ⟨(hi st.top hh).1,by simp,by simp⟩
        exact cache_newFrame ℓ up c hup rfl rfl
  | leafDrain =>
    have hlevel : st.top = ℓ := (hi st.top le_rfl).2.1 hpc
    simp only [hpc]
    split
    · exact cache_PC ℓ _ hi _ (by simp) (by simp)
    · split
      · cases hp : pendingPush st with
        | none => exact cache_PC ℓ _ hi _ (fun _ => hlevel) (by simp)
        | some p => obtain ⟨t,v⟩ := p; exact cache_exterior ℓ g α st t v hi
      · split
        · exact cache_PC ℓ _ hi _ (by simp) (by simp)
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : CacheControlInvariant ℓ u := by
              apply cache_control_changeFrame ℓ st hi
              intro _
              refine ⟨?_,?_,?_⟩
              · intro hn
                exact False.elim (hn hlevel)
              · intro _
                exact hlevel
              · intro hf
                have hh : (st.frames st.top).pc = .fullSolve := hf
                rw [hpc] at hh
                cases hh
            unfold CacheControlInvariant
            exact cache_key_refresh ℓ g _ (touchedBy g C) (cache_joint ℓ g α u _ hu)
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact cache_PC ℓ _ (cache_finish ℓ _ hi) _ (by simp) (by simp)
    · split
      · exact cache_PC ℓ _ (cache_finish ℓ _ hi) _ (by simp) (by simp)
      · exact cache_drain ℓ g α st hi _ (by simp) (by simp)
  | finishEpisode =>
    simp only [hpc]
    split
    · exact cache_PC ℓ _ (cache_finish ℓ _ hi) _ (by simp) (by simp)
    · split
      · exact cache_PC ℓ _ (cache_finish ℓ _ hi) _ (by simp) (by simp)
      · apply cache_control_changeFrame ℓ _ (cache_finish ℓ _ (by exact hi))
        intro _
        split_ifs <;> simp [finishEpisode,changeFrame,debit]
  | restartDrain =>
    simp only [hpc]
    split
    · exact cache_PC ℓ _ hi _ (by simp) (by simp)
    · split
      · exact cache_drain ℓ g α st hi _ (by simp) (by simp)
      · apply cache_control_changeFrame ℓ _ (by exact hi)
        intro hh
        exact ⟨(hi st.top hh).1,by simp,by simp⟩
  | normal =>
    simp only [hpc]
    exact cache_end ℓ g α _ hi
  | interrupted =>
    simp only [hpc]
    exact cache_end ℓ g α _ hi

lemma cache_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    CacheControlInvariant ℓ (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using cache_control_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using cache_step m g s α ℓ schedule _ ih

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
noncomputable section
theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    st.top ≤ ℓ ∧ BudgetInvariant st ∧ CacheControlInvariant ℓ st ∧ (0 < q → ParameterInvariant st) := by
  exact ⟨depth_run m g s α q ℓ schedule t,budget_run m g s α q ℓ schedule t,
    cache_run m g s α q ℓ schedule t,fun hq => parameters_run m g s α q hq ℓ schedule t⟩
end

