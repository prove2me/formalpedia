-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_discovery_effort
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:01:28.717466+00:00
-- url     : https://prove2.me/submissions/73285d4a-8ad5-42cb-b6d4-5599cfee956c

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_budget_energy
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_stack_scales
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

-- Proof module: Solutions.RegionInvariants

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

@[simp] lemma refresh_active (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).active = (st.frames i).active := by
  by_cases hi : i ≤ st.top <;> simp [refreshKeys,hi]

@[simp] lemma refresh_parentDomain (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    parentDomain (refreshKeys g st T) i = parentDomain st i := by
  unfold parentDomain
  split <;> simp

lemma parentDomain_same (st st' : RecursiveState n)
    (ha : ∀ i, (st'.frames i).active = (st.frames i).active) :
    ∀ i, parentDomain st' i = parentDomain st i := by
  intro i
  unfold parentDomain
  split <;> simp [ha]

lemma region_same (st st' : RecursiveState n) (ht : st'.top = st.top)
    (ha : ∀ i, (st'.frames i).active = (st.frames i).active)
    (he : ∀ i, (st'.frames i).exterior = (st.frames i).exterior)
    (hh : ∀ i, (st'.frames i).high = (st.frames i).high)
    (hc : ∀ i, (st'.frames i).cache ⊆ (st.frames i).cache)
    (hi : RegionInvariant st) : RegionInvariant st' := by
  intro i hle
  rw [ht] at hle
  have h := hi i hle
  rw [ha, he, hh, parentDomain_same st st' ha]
  exact ⟨h.1,h.2.1,h.2.2.1,(hc i).trans h.2.2.2⟩

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

-- Proof module: Solutions.RootIdentityControl

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma solveOn_outside (g : InputGraph n) (α : ℝ) (T : Finset (Fin n))
    (b : Fin n → ℝ) (v : Fin n) (hv : v ∉ T) : solveOn g α T b v = 0 := by
  classical
  simp [solveOn,hv]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RegionControl

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma region_changeFrame (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) (hi : RegionInvariant st)
    (hA : (f (st.frames j)).active = (st.frames j).active)
    (hE : (f (st.frames j)).exterior ⊆ (st.frames j).exterior)
    (hH : (f (st.frames j)).high ⊆ (st.frames j).active)
    (hC : (f (st.frames j)).cache ⊆ (st.frames j).active) :
    RegionInvariant (changeFrame st j f) := by
  have ha : ∀ i, ((changeFrame st j f).frames i).active = (st.frames i).active := by
    intro i
    by_cases he : i = j <;> simp [changeFrame,he,hA]
  have hp := parentDomain_same st (changeFrame st j f) ha
  intro i hle
  have hh := hi i hle
  rw [hp,ha]
  by_cases he : i = j
  · subst i
    simp only [changeFrame,Function.update_self]
    exact ⟨hh.1,hE.trans hh.2.1,hH,hC⟩
  · simpa [changeFrame,he] using hh

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


lemma raw_relative (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (δ : ℝ) (i : ℕ) (w : Fin n) :
    relative (rawExterior g α st t v δ) i w =
      relative st i w+(if w = v then δ else 0) := by
  classical
  by_cases hi : i = 0 <;> by_cases hw : w = v <;> by_cases ht : i ≤ st.top <;>
    simp [relative,rawExterior,hi,hw,ht] <;> ring

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


lemma admit_stage_fields (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    let u := admitStage g st t v
    u.top = st.top ∧ u.x = st.x ∧
      (∀ i, (u.frames i).q = (st.frames i).q) ∧
      (∀ i, (u.frames i).theta = (st.frames i).theta) ∧
      (∀ i, (u.frames i).cache = (st.frames i).cache) ∧
      (∀ i, (u.frames i).active = if i = t then insert v (st.frames i).active else (st.frames i).active) ∧
      (∀ i w, (u.frames i).reference w =
        if t < st.top ∧ i = t+1 ∧ w = v then st.x v else (st.frames i).reference w) ∧
      (∀ i w, (u.frames i).residual w =
        if t < st.top ∧ i = t+1 ∧ w = v then
          (st.frames t).residual v+(st.frames t).q*LocalPush.deg g.graph v/2
        else (st.frames i).residual w+
          if i = t ∧ w = v then (st.frames t).q*LocalPush.deg g.graph v/2 else 0) := by
  classical
  dsimp only
  let a := changeFrame st t (fun fi =>
    {fi with
      active := insert v fi.active
      residual := Function.update fi.residual v (fi.residual v+(st.frames t).q*LocalPush.deg g.graph v/2)
      W := fi.W + if fi.openBudget then (t+3 : ℕ)*(st.frames t).q*LocalPush.deg g.graph v/2 else 0})
  let b := if t < st.top then changeFrame a (t+1) (fun fc =>
    {fc with
      reference := Function.update fc.reference v (a.x v)
      residual := Function.update fc.residual v ((a.frames t).residual v)}) else a
  let c := if t = 0 then {b with boundaryEdges := st.boundaryEdges+(g.neighbors v).length-
    2*((g.neighbors v).filter (fun w => w ∈ (st.frames t).active)).length} else b
  have hdef : admitStage g st t v = c := rfl
  have hbtop : b.top = st.top := by unfold b; split <;> rfl
  have hbx : b.x = st.x := by unfold b; split <;> rfl
  have hframes : (admitStage g st t v).frames = b.frames := by
    rw [hdef]
    unfold c
    split <;> rfl
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hdef]
    unfold c
    split <;> exact hbtop
  · rw [hdef]
    unfold c
    split <;> exact hbx
  · intro i
    rw [hframes]
    by_cases hc : t < st.top <;> by_cases hit : i = t <;> by_cases hic : i = t+1 <;>
      simp [b,hc,a,changeFrame,hit,hic]
  · intro i
    rw [hframes]
    by_cases hc : t < st.top <;> by_cases hit : i = t <;> by_cases hic : i = t+1 <;>
      simp [b,hc,a,changeFrame,hit,hic]
  · intro i
    rw [hframes]
    by_cases hc : t < st.top <;> by_cases hit : i = t <;> by_cases hic : i = t+1 <;>
      simp [b,hc,a,changeFrame,hit,hic]
  · intro i
    rw [hframes]
    by_cases hc : t < st.top <;> by_cases hit : i = t <;> by_cases hic : i = t+1 <;>
      simp [b,hc,a,changeFrame,hit,hic]
  · intro i w
    rw [hframes]
    by_cases hc : t < st.top <;> by_cases hit : i = t <;>
      by_cases hic : i = t+1 <;> by_cases hw : w = v <;>
      simp [b,hc,a,changeFrame,Function.update_apply,hit,hic,hw]
  · intro i w
    rw [hframes]
    by_cases hc : t < st.top <;> by_cases hit : i = t <;>
      by_cases hic : i = t+1 <;> by_cases hw : w = v <;>
      simp [b,hc,a,changeFrame,Function.update_apply,hit,hic,hw]

lemma admit_domain (g : InputGraph n) (st : RecursiveState n) (t i : ℕ) (v w : Fin n) :
    w ∈ parentDomain (admitStage g st t v) i ↔
      w ∈ parentDomain st i ∨ i = t+1 ∧ w = v := by
  classical
  have hA := (admit_stage_fields g st t v).2.2.2.2.2.1
  unfold parentDomain
  by_cases hz : i = 0
  · subst i
    simp
  · simp only [hz,ite_false]
    rw [hA]
    by_cases he : i = t+1
    · subst i
      simp [or_comm]
    · have hn : i-1 ≠ t := by omega
      simp [hn,he]

lemma admit_relative (g : InputGraph n) (st : RecursiveState n) (t i : ℕ) (v w : Fin n) :
    relative (admitStage g st t v) i w =
      if t < st.top ∧ i = t+1 ∧ w = v then 0 else relative st i w := by
  classical
  obtain ⟨ht,hx,hq,hθ,hC,hA,href,hr⟩ := admit_stage_fields g st t v
  by_cases hz : i = 0
  · subst i
    simp [relative,hx]
  · unfold relative
    simp only [hz,ite_false,hx]
    rw [href]
    split
    · rename_i hh
      obtain ⟨_,_,he⟩ := hh
      subst w
      simp
    · rfl

lemma raw_q (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ)
    (v : Fin n) (δ : ℝ) (i : ℕ) :
    ((rawExterior g α st t v δ).frames i).q = (st.frames i).q := by
  by_cases hi : i ≤ st.top <;> simp [rawExterior,hi]

lemma raw_active (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ)
    (v : Fin n) (δ : ℝ) (i : ℕ) :
    ((rawExterior g α st t v δ).frames i).active = (st.frames i).active := by
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

-- Proof module: Solutions.BoundaryInvariant

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma boundary_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    (debit st j w).boundaryEdges = st.boundaryEdges := rfl
@[simp] lemma boundary_changeFrame (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).boundaryEdges = st.boundaryEdges := rfl
@[simp] lemma boundary_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).boundaryEdges = st.boundaryEdges := rfl
@[simp] lemma active_debit (st : RecursiveState n) (j i : ℕ) (w : ℝ≥0∞) :
    ((debit st j w).frames i).active = (st.frames i).active := by
  classical
  simp [debit]
@[simp] lemma active_changeFrame (st : RecursiveState n) (j i : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) :
    ((changeFrame st j f).frames i).active =
      if i = j then (f (st.frames j)).active else (st.frames i).active := by
  classical
  by_cases h : i = j <;> simp [changeFrame,h]
@[simp] lemma active_refresh (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).active = (st.frames i).active := by
  classical
  by_cases h : i ≤ st.top <;> simp [refreshKeys,h]

@[simp] lemma boundary_id_debit (g : InputGraph n) (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    BoundaryIdentity g (debit st j w) ↔ BoundaryIdentity g st := by
  simp [BoundaryIdentity]

@[simp] lemma boundary_id_changeFrame (g : InputGraph n) (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hf : (f (st.frames j)).active = (st.frames j).active) :
    BoundaryIdentity g (changeFrame st j f) ↔ BoundaryIdentity g st := by
  by_cases he : (0 : ℕ) = j <;> simp_all (config := {maxSteps := 500000}) [BoundaryIdentity]

@[simp] lemma boundary_id_changePC (g : InputGraph n) (st : RecursiveState n) (pc : NormalizePC) :
    BoundaryIdentity g (changePC st pc) ↔ BoundaryIdentity g st :=
  boundary_id_changeFrame g st st.top _ rfl

@[simp] lemma boundary_id_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    BoundaryIdentity g (refreshKeys g st T) ↔ BoundaryIdentity g st := by simp [BoundaryIdentity]

@[simp] lemma boundary_id_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    BoundaryIdentity g (jointUpdate g α st h) ↔ BoundaryIdentity g st := by
  simp [BoundaryIdentity,jointUpdate]

@[simp] lemma boundary_id_finish (g : InputGraph n) (st : RecursiveState n) :
    BoundaryIdentity g (finishEpisode st) ↔ BoundaryIdentity g st := by
  by_cases he : (0 : ℕ) = st.top <;> simp [finishEpisode,BoundaryIdentity,he]

@[simp] lemma boundary_id_complete (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α : ℝ) (st : RecursiveState n) :
    BoundaryIdentity g (completeComponent m g s α st) ↔ BoundaryIdentity g st := Iff.rfl

@[simp] lemma boundary_id_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    BoundaryIdentity g (endCall g α st) ↔ BoundaryIdentity g st := by
  unfold endCall
  dsimp only
  split <;> rfl

@[simp] lemma active_ite (P : Prop) [Decidable P] (a b : RecursiveState n) (i : ℕ) :
    ((if P then a else b).frames i).active =
      if P then (a.frames i).active else (b.frames i).active := by split <;> rfl
@[simp] lemma boundary_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).boundaryEdges = if P then a.boundaryEdges else b.boundaryEdges := by split <;> rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.StoredInvariant

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

@[simp] lemma stored_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).stored = if P then a.stored else b.stored := by split <;> rfl

set_option maxHeartbeats 1000000 in
lemma exterior_active (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (i : ℕ) :
    let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)
    ((exteriorPush g α st t v).frames i).active =
      if relative st t v+δ = 3*(st.frames t).q/8 ∧ i = t then insert v (st.frames i).active
      else (st.frames i).active := by
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
  have hb (i : ℕ) : (base.frames i).active = (st.frames i).active := by
    by_cases hh : i ≤ st.top <;> simp [base,rawExterior,hh]
  have ha (i : ℕ) : (admitted.frames i).active =
      if i = t then insert v (st.frames i).active else (st.frames i).active := by
    simp only [admitted,active_changeFrame]
    by_cases hh : i = t <;> simp [hh,hb]
  have hc (i : ℕ) : (child.frames i).active = (admitted.frames i).active := by
    unfold child
    split
    · exact observe_changeFrame (fun f => f.active) admitted (t+1) _ rfl i
    · rfl
  have hf (i : ℕ) : (final.frames i).active = (admitted.frames i).active := by
    unfold final
    split <;> exact hc i
  have hp (i : ℕ) : (prepared.frames i).active =
      if relative st t v+δ = 3*f.q/8 ∧ i = t then insert v (st.frames i).active
      else (st.frames i).active := by
    unfold prepared
    split
    · rename_i hh
      rw [hf,ha]
      simp [hh]
    · rename_i hh
      rw [hb]
      simp [hh]
  dsimp only
  unfold exteriorPush
  simp only [active_debit,active_refresh]
  change (prepared.frames i).active = _
  exact hp i

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

lemma nonactivating_push_clears (d q r y : ℝ)
    (hn : y+min (r/(5*d)) (3*q/8-y) ≠ 3*q/8) :
    min (r/(5*d)) (3*q/8-y) = r/(5*d) := by
  by_cases hh : r/(5*d) ≤ 3*q/8-y
  · exact min_eq_left hh
  · have he := min_eq_right (le_of_not_ge hh)
    exfalso
    apply hn
    rw [he]
    ring

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

lemma inactive_push_level (st : RecursiveState n) (hreg : RegionInvariant st)
    (t i : ℕ) (ht : t ≤ st.top) (hi : i ≤ st.top) (v : Fin n)
    (hvt : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active)
    (hvi : v ∈ parentDomain st i) (hoi : v ∉ (st.frames i).active) : i = t := by
  by_contra he
  by_cases hlt : i < t
  · exact hoi (parent_domain_nested st hreg i t hlt ht hvt)
  · exact hout (parent_domain_nested st hreg t i (by omega) hi hvi)

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

lemma discoveryCredit_nonnegative (g : InputGraph n) (st : RecursiveState n)
    (hnum : NumericalInvariant g st) (hparam : ParameterInvariant st) (j : ℕ) (hj : j ≤ st.top) :
    0 ≤ discoveryCredit g st j := by
  unfold discoveryCredit
  apply add_nonneg
  · have hq := (hparam j hj).1.le
    positivity
  · apply Finset.sum_nonneg
    intro v hv
    have hdom := (Finset.mem_sdiff.mp hv).1
    have hy := ((hnum j hj).1 v hdom).2.1
    apply mul_nonneg
    · unfold LocalPush.deg; positivity
    · exact hy

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

lemma discoveryCredit_as_sum_of_subset (g : InputGraph n) (st : RecursiveState n)
    (j : ℕ) (hsub : (st.frames j).active ⊆ parentDomain st j) :
    discoveryCredit g st j = ∑ v ∈ parentDomain st j,
      if v ∈ (st.frames j).active then 3*(st.frames j).q/8*LocalPush.deg g.graph v
      else LocalPush.deg g.graph v*relative st j v := by
  classical
  let f := fun v => if v ∈ (st.frames j).active then 3*(st.frames j).q/8*LocalPush.deg g.graph v
      else LocalPush.deg g.graph v*relative st j v
  have hactive : (∑ v ∈ (st.frames j).active, f v) =
      3*(st.frames j).q/8*(volumeNat g (st.frames j).active : ℝ) := by
    rw [volume_real,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    simp [f,hv]
  have houtside : (∑ v ∈ parentDomain st j \ (st.frames j).active, f v) =
      ∑ v ∈ parentDomain st j \ (st.frames j).active, LocalPush.deg g.graph v*relative st j v := by
    apply Finset.sum_congr rfl
    intro v hv
    simp [f,(Finset.mem_sdiff.mp hv).2]
  have he := Finset.sum_sdiff (f := f) hsub
  rw [hactive,houtside] at he
  unfold discoveryCredit
  change _ = ∑ v ∈ parentDomain st j, f v
  linarith

lemma discoveryCredit_as_sum (g : InputGraph n) (st : RecursiveState n)
    (hreg : RegionInvariant st) (j : ℕ) (hj : j ≤ st.top) :
    discoveryCredit g st j = ∑ v ∈ parentDomain st j,
      if v ∈ (st.frames j).active then 3*(st.frames j).q/8*LocalPush.deg g.graph v
      else LocalPush.deg g.graph v*relative st j v :=
  discoveryCredit_as_sum_of_subset g st j ((hreg j hj).1)

lemma discoveryCredit_parent_mass_bound (g : InputGraph n) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hlayer : LayerIdentity g st) (hnum : NumericalInvariant g st)
    (j : ℕ) (hj : j < st.top) :
    discoveryCredit g st (j+1) ≤ (3/8 : ℝ)*(∑ v ∈ (st.frames j).active, (st.frames j).residual v) := by
  rw [discoveryCredit_as_sum g st hreg (j+1) hj,Finset.mul_sum]
  simp only [parentDomain,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,Nat.add_sub_cancel]
  apply Finset.sum_le_sum
  intro v hv
  have hvdom : v ∈ parentDomain st (j+1) := by simpa [parentDomain] using hv
  have hn := (hnum (j+1) hj).1 v hvdom
  have hid := hlayer j hj v hv
  have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
  by_cases ha : v ∈ (st.frames (j+1)).active
  · simp only [ha,ite_true] at hid ⊢
    nlinarith [hn.1]
  · simp only [ha,ite_false] at hid ⊢
    nlinarith [hn.1,mul_nonneg hd hn.2.1]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DiscoveryRaw

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma discoveryCredit_raw (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (t j : ℕ) (ht : t ≤ st.top) (hj : j ≤ st.top)
    (v : Fin n) (hvt : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active) (δ : ℝ) :
    discoveryCredit g (rawExterior g α st t v δ) j = discoveryCredit g st j+
      (if j = t then LocalPush.deg g.graph v*δ else 0) := by
  classical
  have hA (i : ℕ) : ((rawExterior g α st t v δ).frames i).active = (st.frames i).active := raw_active g α st t v δ i
  have hU := parentDomain_same st (rawExterior g α st t v δ) hA
  have hm : v ∈ parentDomain st j \ (st.frames j).active ↔ j = t := by
    constructor
    · intro hv
      obtain ⟨hdom,houtj⟩ := Finset.mem_sdiff.mp hv
      exact inactive_push_level st hreg t j ht hj v hvt hout hdom houtj
    · intro he
      subst j
      exact Finset.mem_sdiff.mpr ⟨hvt,hout⟩
  unfold discoveryCredit
  rw [raw_q,hA j,hU j]
  simp only [raw_relative,mul_add,mul_ite,mul_zero]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq']
  simp only [hm]
  ring

lemma discoveryCredit_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ)
    (j : ℕ) (hs : ∀ v ∈ parentDomain st j \ (st.frames j).active, h v = 0) :
    discoveryCredit g (jointUpdate g α st h) j = discoveryCredit g st j := by
  classical
  have hq (i : ℕ) : ((jointUpdate g α st h).frames i).q = (st.frames i).q := by
    by_cases hi : i ≤ st.top <;> simp [jointUpdate,hi]
  have hA (i : ℕ) : ((jointUpdate g α st h).frames i).active = (st.frames i).active := by
    by_cases hi : i ≤ st.top <;> simp [jointUpdate,hi]
  have hU := parentDomain_same st (jointUpdate g α st h) hA
  unfold discoveryCredit
  rw [hq,hA j,hU j]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  have hh := hs v hv
  have href : ((jointUpdate g α st h).frames j).reference = (st.frames j).reference := by
    by_cases hi : j ≤ st.top <;> simp [jointUpdate,hi]
  unfold relative
  rw [href]
  by_cases hz : j = 0 <;> simp [hz,jointUpdate,Pi.add_apply,hh]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DiscoveryAdmission

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma discoveryCredit_admit (g : InputGraph n) (st : RecursiveState n) (hreg : RegionInvariant st)
    (t j : ℕ) (ht : t ≤ st.top) (hj : j ≤ st.top) (v : Fin n)
    (hvt : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active)
    (hcap : relative st t v = 3*(st.frames t).q/8) :
    discoveryCredit g (admitStage g st t v) j = discoveryCredit g st j := by
  classical
  obtain ⟨htop,hx,hq,hθ,hC,hA,hrest⟩ := admit_stage_fields g st t v
  have hU : parentDomain (admitStage g st t v) j =
      if j = t+1 then insert v (parentDomain st j) else parentDomain st j := by
    ext w
    by_cases he : j = t+1 <;> simp [admit_domain,he,or_comm]
  have hsub : ((admitStage g st t v).frames j).active ⊆ parentDomain (admitStage g st t v) j := by
    intro w hw
    rw [hA j] at hw
    apply (admit_domain g st t j v w).mpr
    left
    by_cases he : j = t
    · subst j
      simp only [ite_true] at hw
      obtain rfl|hw := Finset.mem_insert.mp hw
      · exact hvt
      · exact (hreg t ht).1 hw
    · exact (hreg j hj).1 (by simpa [he] using hw)
  rw [discoveryCredit_as_sum_of_subset g _ j hsub,discoveryCredit_as_sum g st hreg j hj]
  rw [hq j,hA j,hU]
  by_cases he : j = t
  · subst j
    have hnt : t ≠ t+1 := by omega
    simp only [ite_true,hnt,ite_false]
    apply Finset.sum_congr rfl
    intro w _
    rw [admit_relative]
    have hfalse : ¬(t < st.top ∧ t = t+1 ∧ w = v) := by omega
    simp only [hfalse,ite_false]
    by_cases hw : w = v
    · subst w
      simp [hout,hcap]
      ring
    · simp [Finset.mem_insert,hw]
  · simp only [he,ite_false]
    by_cases hchild : j = t+1
    · have ht' : t < st.top := by omega
      have hnotdom : v ∉ parentDomain st j := by simpa [hchild,parentDomain] using hout
      have hnotactive : v ∉ (st.frames j).active := fun hv => hnotdom ((hreg j hj).1 hv)
      rw [if_pos hchild,Finset.sum_insert hnotdom]
      have hzero : (if v ∈ (st.frames j).active then 3*(st.frames j).q/8*LocalPush.deg g.graph v
          else LocalPush.deg g.graph v*relative (admitStage g st t v) j v) = 0 := by
        rw [if_neg hnotactive,admit_relative]
        simp [ht',hchild]
      rw [hzero,zero_add]
      apply Finset.sum_congr rfl
      intro w hw
      have hne : w ≠ v := by intro he; subst w; exact hnotdom hw
      rw [admit_relative]
      simp [hne]
    · rw [if_neg hchild]
      apply Finset.sum_congr rfl
      intro w _
      rw [admit_relative]
      simp [hchild]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DiscoveryExterior

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma region_raw (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) (δ : ℝ)
    (hi : RegionInvariant st) : RegionInvariant (rawExterior g α st t v δ) := by
  apply region_same st (rawExterior g α st t v δ) rfl
  · intro i; exact raw_active g α st t v δ i
  · intro i; by_cases he : i ≤ st.top <;> simp [rawExterior,he]
  · intro i; by_cases he : i ≤ st.top <;> simp [rawExterior,he]
  · intro i; by_cases he : i ≤ st.top <;> simp [rawExterior,he]
  · exact hi

lemma discoveryCredit_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (j : ℕ) :
    discoveryCredit g (refreshKeys g st T) j = discoveryCredit g st j := by
  classical
  have hA (i : ℕ) : ((refreshKeys g st T).frames i).active = (st.frames i).active := by
    by_cases hi : i ≤ st.top <;> simp [refreshKeys,hi]
  have hq : ((refreshKeys g st T).frames j).q = (st.frames j).q := by
    by_cases hi : j ≤ st.top <;> simp [refreshKeys,hi]
  have href : ((refreshKeys g st T).frames j).reference = (st.frames j).reference := by
    by_cases hi : j ≤ st.top <;> simp [refreshKeys,hi]
  have hU := parentDomain_same st (refreshKeys g st T) hA
  unfold discoveryCredit
  rw [hq,hA j,hU j]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  unfold relative
  rw [href]
  rfl

lemma discoveryCredit_debit (g : InputGraph n) (st : RecursiveState n) (j t : ℕ) (w : ℝ≥0∞) :
    discoveryCredit g (debit st t w) j = discoveryCredit g st j := rfl

lemma discoveryCredit_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (t j : ℕ) (ht : t ≤ st.top) (hj : j ≤ st.top)
    (v : Fin n) (hvt : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active) :
    let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)
    discoveryCredit g (exteriorPush g α st t v) j = discoveryCredit g st j+
      (if j = t then LocalPush.deg g.graph v*δ else 0) := by
  classical
  dsimp only
  let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)
  let base := rawExterior g α st t v δ
  have hr : RegionInvariant base := region_raw g α st t v δ hreg
  have hA (i : ℕ) := raw_active g α st t v δ i
  have hU := parentDomain_same st base hA
  have hvt' : v ∈ parentDomain base t := by simpa [hU t] using hvt
  have hout' : v ∉ (base.frames t).active := by
    change v ∉ ((rawExterior g α st t v δ).frames t).active
    rw [raw_active]
    exact hout
  have hq := raw_q g α st t v δ t
  rw [exterior_stages,discoveryCredit_debit,discoveryCredit_refresh]
  simp only [←show δ = min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
    (3*(st.frames t).q/8-relative st t v) from rfl]
  by_cases ha : relative st t v+δ = 3*(st.frames t).q/8
  · rw [if_pos ha]
    have hcap : relative base t v = 3*(base.frames t).q/8 := by
      rw [raw_relative,hq]
      simpa using ha
    rw [discoveryCredit_admit g base hr t j ht hj v hvt' hout' hcap]
    exact discoveryCredit_raw g α st hreg t j ht hj v hvt hout δ
  · rw [if_neg ha]
    exact discoveryCredit_raw g α st hreg t j ht hj v hvt hout δ

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

-- Proof module: Solutions.DiscoveryControl

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma discoveryCredit_transport (g : InputGraph n) (st u : RecursiveState n) (j : ℕ)
    (hx : u.x = st.x)
    (hH : ∀ i ≤ j, (u.frames i).active = (st.frames i).active)
    (hq : (u.frames j).q = (st.frames j).q)
    (href : (u.frames j).reference = (st.frames j).reference) :
    discoveryCredit g u j = discoveryCredit g st j := by
  have hU : parentDomain u j = parentDomain st j := by
    by_cases hj : j = 0
    · simp [parentDomain,hj]
    · simp only [parentDomain,hj,ite_false]
      rw [hH (j-1) (by omega)]
  unfold discoveryCredit
  rw [hq,hH j le_rfl,hU]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  simp only [relative,hx,href]

lemma discoveryCredit_metadata (g : InputGraph n) (st : RecursiveState n) (k j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hq : (f (st.frames k)).q = (st.frames k).q)
    (hH : (f (st.frames k)).active = (st.frames k).active)
    (href : (f (st.frames k)).reference = (st.frames k).reference) :
    discoveryCredit g (changeFrame st k f) j = discoveryCredit g st j :=
  discoveryCredit_transport g st _ j rfl
    (fun i _ => observe_changeFrame (fun f => f.active) st k f hH i)
    (observe_changeFrame (fun f => f.q) st k f hq j)
    (observe_changeFrame (fun f => f.reference) st k f href j)

lemma discoveryCredit_PC (g : InputGraph n) (st : RecursiveState n) (j : ℕ) (pc : NormalizePC) :
    discoveryCredit g (changePC st pc) j = discoveryCredit g st j :=
  discoveryCredit_metadata g st st.top j _ rfl rfl rfl

lemma discoveryCredit_finish (g : InputGraph n) (st : RecursiveState n) (j : ℕ) :
    discoveryCredit g (finishEpisode st) j = discoveryCredit g st j := by
  unfold finishEpisode
  rw [discoveryCredit_metadata g _ st.top j _ rfl rfl rfl]
  rfl

lemma discoveryCredit_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ) :
    discoveryCredit g (endCall g α st) j = discoveryCredit g st j := by
  unfold endCall
  dsimp only
  split
  · rfl
  · rfl

lemma discoveryCredit_new (g : InputGraph n) (st : RecursiveState n) (c : NormalizeFrame n)
    (j : ℕ) (hj : j ≤ st.top) : discoveryCredit g
      {st with top := st.top+1,frames := Function.update st.frames (st.top+1) c} j = discoveryCredit g st j := by
  apply discoveryCredit_transport g st {st with top := st.top+1,frames := Function.update st.frames (st.top+1) c} j rfl
  · intro i hi
    have he : i ≠ st.top+1 := by omega
    simp [he]
  · have he : j ≠ st.top+1 := by omega
    simp [he]
  · have he : j ≠ st.top+1 := by omega
    simp [he]

lemma discoveryCredit_principal (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (j : ℕ) (hj : j ≤ st.top)
    (T : Finset (Fin n)) (hT : T ⊆ (st.frames st.top).active) (b : Fin n → ℝ) :
    discoveryCredit g (jointUpdate g α st (solveOn g α T b)) j = discoveryCredit g st j := by
  apply discoveryCredit_joint
  intro v hv
  apply solveOn_outside
  intro hvT
  exact (Finset.mem_sdiff.mp hv).2 (active_subset_between st hreg j st.top hj le_rfl (hT hvT))

lemma discoveryCredit_pending (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hreg : RegionInvariant st)
    (j : ℕ) (hj : j ≤ st.top) (t : ℕ) (v : Fin n) (hprod : stepProduction st = some (t,v)) :
    discoveryCredit g (exteriorPush g α st t v) j = discoveryCredit g st j+ownProduction g st j := by
  have hpend := production_pending st t v hprod
  obtain ⟨ht,hm⟩ := pending_push_member st t v hpend
  obtain ⟨hv,hout⟩ := Finset.mem_sdiff.mp ((hreg t ht).2.1 hm)
  simpa only [ownProduction,hprod,pushIncrement,eq_comm] using
    discoveryCredit_exterior g α st hreg t j ht hj v hv hout

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DiscoveryStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma discoveryCredit_drain_none (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ)
    (pc : NormalizePC) (hp : drainProduction st = none) :
    discoveryCredit g (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) j = discoveryCredit g st j := by
  unfold drainProduction at hp
  split
  · rw [discoveryCredit_PC,discoveryCredit_debit]
  · rename_i he
    rw [if_neg he] at hp
    rw [hp,discoveryCredit_PC,discoveryCredit_debit]

set_option maxHeartbeats 1500000 in
lemma discoveryCredit_step_none (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hreg : RegionInvariant st)
    (j : ℕ) (hj : j ≤ st.top) (hp : stepProduction st = none) :
    discoveryCredit g (recursiveStep m g s α ℓ schedule st) j = discoveryCredit g st j := by
  classical
  by_cases hd : st.done = true
  · simp only [recursiveStep,hd,ite_true]
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]; rfl
  simp only [hc,ite_false]
  have hp' := hp
  simp only [stepProduction,hd,Bool.false_eq_true,ite_false,hc] at hp'
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc] at hp' ⊢
    split
    · rw [discoveryCredit_PC,discoveryCredit_debit]
    · rename_i ha
      split
      · rename_i his
        exact discoveryCredit_drain_none g α st j _ (by simpa only [ha,ite_false,his,ite_true] using hp')
      · split <;> rw [discoveryCredit_PC,discoveryCredit_debit]
  | beginEpisode =>
    simp only [hpc]
    rw [discoveryCredit_metadata g _ st.top j _ rfl rfl rfl]
    rfl
  | fullSolve =>
    simp only [hpc]
    split
    · rw [discoveryCredit_PC,discoveryCredit_debit]
    · split
      · rw [discoveryCredit_PC]
        trans discoveryCredit g (debit (refreshKeys g
          (jointUpdate g α st (solveOn g α (st.frames st.top).active (st.frames st.top).residual))
          (touchedBy g (st.frames st.top).active)) st.top (jointCost m g st (st.frames st.top).active)) j
        · rfl
        · rw [discoveryCredit_debit,discoveryCredit_refresh,discoveryCredit_principal g α st hreg j hj _ (Finset.Subset.refl _)]
      · exact discoveryCredit_debit g st j st.top 1
  | normalize =>
    simp only [hpc]
    split
    · rw [discoveryCredit_PC,discoveryCredit_debit]
    · split
      · rw [discoveryCredit_PC,discoveryCredit_debit]
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun f => {f with pc := .afterChild,childrenThisEpisode := f.childrenThisEpisode+1})
        trans discoveryCredit g {up with top := up.top+1,frames := Function.update up.frames (up.top+1) c} j
        · rfl
        · rw [discoveryCredit_new g up c j hj,discoveryCredit_metadata g u st.top j _ rfl rfl rfl]
          exact discoveryCredit_debit g st j st.top _
  | leafDrain =>
    simp only [hpc] at hp' ⊢
    split
    · rw [discoveryCredit_PC,discoveryCredit_debit]
    · rename_i he
      split
      · rename_i his
        have hdn : drainProduction st = none := by simpa only [he,ite_false,his,ite_true] using hp'
        have hpn : pendingPush st = none := by simpa only [drainProduction,he,ite_false] using hdn
        simp [hpn] at his
      · split
        · rw [discoveryCredit_PC,discoveryCredit_debit]
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun f => {f with cache := C})
            have hu : RegionInvariant u := by
              refine region_changeFrame st st.top _ hreg rfl (Finset.Subset.refl _) (hreg st.top le_rfl).2.2.1 ?_
              exact Finset.union_subset_iff.mpr ⟨(hreg st.top le_rfl).2.2.2,(hreg st.top le_rfl).2.2.1⟩
            have hT : C ⊆ (u.frames u.top).active := by
              simpa [u,changeFrame] using Finset.union_subset_iff.mpr
                ⟨(hreg st.top le_rfl).2.2.2,(hreg st.top le_rfl).2.2.1⟩
            rw [discoveryCredit_debit,discoveryCredit_refresh]
            rw [discoveryCredit_principal g α u hu j hj C hT]
            exact discoveryCredit_metadata g st st.top j _ rfl rfl rfl
          · exact discoveryCredit_debit g st j st.top 1
  | afterChild =>
    simp only [hpc] at hp' ⊢
    split
    · rw [discoveryCredit_PC,discoveryCredit_finish,discoveryCredit_debit]
    · rename_i ha
      split
      · rw [discoveryCredit_PC,discoveryCredit_finish,discoveryCredit_debit]
      · rename_i he
        exact discoveryCredit_drain_none g α st j _ (by simpa only [ha,he,ite_false] using hp')
  | finishEpisode =>
    simp only [hpc]
    split
    · rw [discoveryCredit_PC,discoveryCredit_finish,discoveryCredit_debit]
    · split
      · rw [discoveryCredit_PC,discoveryCredit_finish,discoveryCredit_debit]
      · rw [discoveryCredit_metadata g _ st.top j _ rfl rfl rfl,discoveryCredit_finish,discoveryCredit_debit]
  | restartDrain =>
    simp only [hpc] at hp' ⊢
    split
    · rw [discoveryCredit_PC,discoveryCredit_debit]
    · rename_i ha
      split
      · rename_i his
        exact discoveryCredit_drain_none g α st j _ (by simpa only [ha,ite_false,his,ite_true] using hp')
      · rw [discoveryCredit_metadata g _ st.top j _ rfl rfl rfl,discoveryCredit_debit]
  | normal => simp only [hpc]; rw [discoveryCredit_end,discoveryCredit_debit]
  | interrupted => simp only [hpc]; rw [discoveryCredit_end,discoveryCredit_debit]

lemma discoveryCredit_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hreg : RegionInvariant st)
    (j : ℕ) (hj : j ≤ st.top) :
    discoveryCredit g (recursiveStep m g s α ℓ schedule st) j = discoveryCredit g st j+ownProduction g st j := by
  cases hh : stepProduction st with
  | none => rw [discoveryCredit_step_none m g s α ℓ schedule st hreg j hj hh]; simp [ownProduction,hh]
  | some p =>
    obtain ⟨t,v⟩ := p
    rw [production_push m g s α ℓ schedule st t v hh]
    exact discoveryCredit_pending g α st hreg j hj t v hh

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ActivationEvents

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 2000000 in
lemma active_step_none (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top)
    (hp : stepProduction st = none) :
    ((recursiveStep m g s α ℓ schedule st).frames j).active = (st.frames j).active := by
  classical
  have hnew : j ≠ st.top+1 := by omega
  cases hpend : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,stepProduction,drainProduction,hpc,hpend] at hp ⊢ <;>
      (try split_ifs at hp ⊢) <;>
      simp_all [changePC,changeFrame,debit,refreshKeys,jointUpdate,finishEpisode,endCall,completeComponent,Function.update_apply] <;>
      (try split_ifs) <;> simp_all
  | some p =>
    obtain ⟨t,v⟩ := p
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,stepProduction,drainProduction,hpc,hpend] at hp ⊢ <;>
      (try split_ifs at hp ⊢) <;>
      simp_all [changePC,changeFrame,debit,refreshKeys,jointUpdate,finishEpisode,endCall,completeComponent,Function.update_apply] <;>
      (try split_ifs) <;> simp_all

lemma birthProduction_volume_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hreg : RegionInvariant st)
    (j : ℕ) (hj : j ≤ st.top) :
    birthProduction g st j = ((j+3 : ℕ) : ℝ)*(st.frames j).q/2*
      ((volumeNat g ((recursiveStep m g s α ℓ schedule st).frames j).active : ℝ)-
        (volumeNat g (st.frames j).active : ℝ)) := by
  classical
  cases hh : stepProduction st with
  | none => rw [active_step_none m g s α ℓ schedule st j hj hh]; simp [birthProduction,hh]
  | some p =>
    obtain ⟨t,v⟩ := p
    have hpend := production_pending st t v hh
    obtain ⟨ht,hm⟩ := pending_push_member st t v hpend
    have hout := (Finset.mem_sdiff.mp ((hreg t ht).2.1 hm)).2
    rw [production_push m g s α ℓ schedule st t v hh,exterior_active]
    unfold birthProduction pushIncrement
    rw [hh]
    by_cases he : t = j
    · subst t
      have hvol : (volumeNat g (insert v (st.frames j).active) : ℝ)-
          (volumeNat g (st.frames j).active : ℝ) = LocalPush.deg g.graph v := by
        rw [volume_real,volume_real,Finset.sum_insert hout]
        ring
      split_ifs <;> simp_all <;> ring
    · have he' : j ≠ t := Ne.symm he
      simp [he,he']

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

-- Proof module: Solutions.OwnProductionBounds

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma child_discoveryCredit_unexhausted (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t j : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    j < st.top → ¬exhausted st j →
      discoveryCredit g st (j+1) < (3/4 : ℝ)*(st.frames (j+1)).q*(st.frames (j+1)).N := by
  intro st hj he
  have hreg : RegionInvariant st := region_run m g s α q ℓ schedule t
  have hc := discoveryCredit_parent_mass_bound g st hreg (layer_run m g s α q ℓ schedule t)
    (numerical_run m g s α q hα hq hs ℓ schedule t) j hj
  have hopen : (st.frames j).openBudget = true := by
    simpa [stack_run m g s α q ℓ schedule t j hj,budgetPC] using budget_run m g s α q ℓ schedule t j hj.le
  have hm := run_unexhausted_mass m g s α q hα hq hs ℓ schedule t j hj.le hopen he
  have hscale : ScaleInvariant st := scale_run m g s α q hq ℓ schedule t
  have hQ : (st.frames j).Q = (st.frames (j+1)).q*(st.frames (j+1)).N := by
    rw [hscale.1 j hj.le hopen,hscale.2 j hj,threshold_relation_run m g s α q ℓ schedule t j hj]
  change (∑ v ∈ (st.frames j).active, (st.frames j).residual v) < 2*(st.frames j).Q at hm
  rw [hQ] at hm
  nlinarith

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

-- Proof module: Solutions.ProducingDegreeBound

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma producing_degree_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a t : ℕ) (v : Fin n)
    (hp : stepProduction (recursiveRun m g s α q ℓ schedule a)=some (t,v)) :
    let st := recursiveRun m g s α q ℓ schedule a
    LocalPush.deg g.graph v < 2*(st.frames t).N := by
  intro st
  have hreg : RegionInvariant st := region_run m g s α q ℓ schedule a
  have hnum : NumericalInvariant g st := numerical_run m g s α q hα hq hs ℓ schedule a
  have hparams : ParameterInvariant st := parameters_run m g s α q hq ℓ schedule a
  have hkeys : KeysInvariant g st := keys_run m g s α q hq.le ℓ schedule a
  have hpend := production_pending st t v hp
  obtain ⟨ht,hm⟩ := pending_push_member st t v hpend
  have hvU := (Finset.mem_sdiff.mp ((hreg t ht).2.1 hm)).1
  have hres : (st.frames t).q*LocalPush.deg g.graph v < (st.frames t).residual v :=
    (((hkeys t ht).1 v).mp hm).2.2
  have hno := production_unexhausted st t v hp
  cases htid : t with
  | zero =>
    rw [htid] at ht hvU hres
    have hroot := root_residual_mass_bound g s α hα.1.le st (root_identity_run m g s α q ℓ schedule a) hnum
      (hparams 0 (Nat.zero_le _)).1.le
    have hrv : (st.frames 0).residual v ≤ ∑ w, (st.frames 0).residual w :=
      Finset.single_le_sum (fun w _ => ((hnum 0 (Nat.zero_le _)).1 w (by simp [parentDomain])).1) (Finset.mem_univ v)
    have hqr : (st.frames 0).q=q := root_threshold_run m g s α q ℓ schedule a
    have hNr : (st.frames 0).N=1/q := root_scale_run m g s α q ℓ schedule a
    rw [hqr] at hres
    rw [hNr]
    have hupper : LocalPush.deg g.graph v < 1/q := (lt_div_iff₀ hq).mpr (by nlinarith)
    have hN0 : 0 ≤ 1/q := by positivity
    linarith
  | succ i =>
    rw [htid] at ht hvU hres
    have hip : i < st.top := by omega
    have hvP : v ∈ (st.frames i).active := by simpa [parentDomain] using hvU
    have hdom := layer_residual_dominance g st hreg (layer_run m g s α q ℓ schedule a) hparams hnum
      i (i+1) (by omega) ht v hvU
    have hsingle : (st.frames i).residual v ≤ ∑ w ∈ (st.frames i).active, (st.frames i).residual w :=
      Finset.single_le_sum (fun w hw => ((hnum i hip.le).1 w ((hreg i hip.le).1 hw)).1) hvP
    have hopen : (st.frames i).openBudget=true := by
      simpa [stack_run m g s α q ℓ schedule a i hip,budgetPC] using budget_run m g s α q ℓ schedule a i hip.le
    have hm := run_unexhausted_mass m g s α q hα hq hs ℓ schedule a i hip.le hopen
      (fun hx => hno ⟨i,hip.le,hx⟩)
    have hscale : ScaleInvariant st := scale_run m g s α q hq ℓ schedule a
    have hQ : (st.frames i).Q=(st.frames (i+1)).q*(st.frames (i+1)).N := by
      rw [hscale.1 i hip.le hopen,hscale.2 i hip,threshold_relation_run m g s α q ℓ schedule a i hip]
    change (∑ w ∈ (st.frames i).active, (st.frames i).residual w) < 2*(st.frames i).Q at hm
    rw [hQ] at hm
    have hqf := (hparams (i+1) ht).1
    nlinarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DiscoveryEffort

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma birthProduction_factor (g : InputGraph n) (st : RecursiveState n) (j : ℕ) :
    birthProduction g st j = ((j+3 : ℕ) : ℝ)*(st.frames j).q/2*activatedDegree g st j := by
  classical
  cases hh : stepProduction st with
  | none => simp [birthProduction,activatedDegree,hh]
  | some p =>
    obtain ⟨t,v⟩ := p
    by_cases he : t = j
    · subst t
      unfold birthProduction activatedDegree
      rw [hh]
      dsimp only
      split_ifs <;> ring
    · simp [birthProduction,activatedDegree,hh,he]

lemma activatedDegree_volume_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hreg : RegionInvariant st)
    (hp : ParameterInvariant st) (j : ℕ) (hj : j ≤ st.top) :
    activatedDegree g st j = (volumeNat g ((recursiveStep m g s α ℓ schedule st).frames j).active : ℝ)-
      (volumeNat g (st.frames j).active : ℝ) := by
  have hh := birthProduction_volume_step m g s α ℓ schedule st hreg j hj
  rw [birthProduction_factor] at hh
  have hq : 0 < (st.frames j).q := (hp j hj).1
  have hc : 0 < ((j+3 : ℕ) : ℝ)*(st.frames j).q/2 := by positivity
  nlinarith

lemma discoveryEffort_step_bound (g : InputGraph n) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hp : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st) (j : ℕ) (hj : j ≤ st.top) :
    discoveryEffort g st j ≤ 2*activatedDegree g st j+10/(st.frames j).q*ownProduction g st j := by
  cases hh : stepProduction st with
  | none => simp [discoveryEffort,activatedDegree,ownProduction,hh]
  | some p =>
    obtain ⟨t,v⟩ := p
    by_cases he : t = j
    · subst t
      have hpend := production_pending st j v hh
      have hm := (pending_push_member st j v hpend).2
      have hr := (((hkeys j hj).1 v).mp hm).2.2
      have hdNat := isolate_pending_positive g st hiso hkeys j v hpend
      have hd : 0 < LocalPush.deg g.graph v := by unfold LocalPush.deg; exact_mod_cast hdNat
      have hd1 : 1 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; exact_mod_cast hdNat
      have hq : 0 < (st.frames j).q := (hp j hj).1
      have hδ := production_increment_nonnegative g st hreg hp hnum hkeys hiso j v hh
      have hmass : 0 ≤ 10/(st.frames j).q*(LocalPush.deg g.graph v*pushIncrement g st j v) := by positivity
      unfold discoveryEffort activatedDegree ownProduction
      simp only [hh,le_refl,ite_true,true_and]
      by_cases ha : relative st j v+pushIncrement g st j v=3*(st.frames j).q/8
      · rw [if_pos ha]
        nlinarith
      · rw [if_neg ha]
        have hclear := nonactivating_push_clears (LocalPush.deg g.graph v) (st.frames j).q
          ((st.frames j).residual v) (relative st j v) ha
        have hmin : (st.frames j).q/5 < pushIncrement g st j v := by
          unfold pushIncrement
          rw [hclear]
          apply (lt_div_iff₀ (by positivity : 0 < 5*LocalPush.deg g.graph v)).mpr
          nlinarith
        have hcost : 2*LocalPush.deg g.graph v ≤ 10/(st.frames j).q*
            (LocalPush.deg g.graph v*pushIncrement g st j v) := by
          rw [show 10/(st.frames j).q*(LocalPush.deg g.graph v*pushIncrement g st j v) =
            (10*LocalPush.deg g.graph v*pushIncrement g st j v)/(st.frames j).q by ring]
          apply (le_div_iff₀ hq).mpr
          have hh := mul_le_mul_of_nonneg_left hmin.le hd.le
          nlinarith
        nlinarith
    · simp [discoveryEffort,activatedDegree,ownProduction,hh,he]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DiscoveryEffortBounds

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma discoveryEffortPotential_nonnegative (g : InputGraph n) (st : RecursiveState n)
    (hnum : NumericalInvariant g st) (hp : ParameterInvariant st) (j : ℕ) (hj : j ≤ st.top) :
    0 ≤ discoveryEffortPotential g st j := by
  have hq := (hp j hj).1
  have hc := discoveryCredit_nonnegative g st hnum hp j hj
  unfold discoveryEffortPotential
  positivity

lemma discoveryEffort_step_potential (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hp : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st) (j : ℕ) (hj : j ≤ st.top) :
    discoveryEffort g st j ≤ discoveryEffortPotential g (recursiveStep m g s α ℓ schedule st) j-
      discoveryEffortPotential g st j := by
  have hh := discoveryEffort_step_bound g st hreg hp hnum hkeys hiso j hj
  have hv := activatedDegree_volume_step m g s α ℓ schedule st hreg hp j hj
  have hC := discoveryCredit_step m g s α ℓ schedule st hreg j hj
  have hq : ((recursiveStep m g s α ℓ schedule st).frames j).q = (st.frames j).q :=
    congrArg Prod.fst (frozenFrame_step m g s α ℓ schedule st j hj)
  unfold discoveryEffortPotential
  rw [hq,hC]
  rw [hv] at hh
  nlinarith

lemma discoveryEffort_interval (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top) :
    (∑ k ∈ Finset.range (b-a), discoveryEffort g (recursiveRun m g s α q ℓ schedule (a+k)) j) ≤
      discoveryEffortPotential g (recursiveRun m g s α q ℓ schedule b) j-
        discoveryEffortPotential g (recursiveRun m g s α q ℓ schedule a) j := by
  have hh : (∑ k ∈ Finset.range (b-a), discoveryEffort g (recursiveRun m g s α q ℓ schedule (a+k)) j) ≤
      ∑ k ∈ Finset.range (b-a), (discoveryEffortPotential g (recursiveRun m g s α q ℓ schedule (a+k+1)) j-
        discoveryEffortPotential g (recursiveRun m g s α q ℓ schedule (a+k)) j) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkt : a+k < b := by have := Finset.mem_range.mp hk; omega
    have hh := discoveryEffort_step_potential m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+k))
      (region_run m g s α q ℓ schedule (a+k)) (parameters_run m g s α q hq ℓ schedule (a+k))
      (numerical_run m g s α q hα hq hs ℓ schedule (a+k)) (keys_run m g s α q hq.le ℓ schedule (a+k))
      (isolate_run m g s α q hs ℓ schedule (a+k)) j (hopen (a+k) (by omega) hkt)
    simpa only [recursiveRun,Function.iterate_succ_apply'] using hh
  rw [offset_sum_difference (fun t => discoveryEffortPotential g (recursiveRun m g s α q ℓ schedule t) j) a (b-a),
    Nat.add_sub_of_le hab] at hh
  exact hh

lemma root_discoveryEffortPotential_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    discoveryEffortPotential g (recursiveRun m g s α q ℓ schedule t) 0 ≤ 6/q := by
  let st := recursiveRun m g s α q ℓ schedule t
  have hvol := (run_root_volume_bound m g s α q hα hq hs ℓ schedule t).1
  have hc := root_discoveryCredit_bound g s α hα.1.le st (root_identity_run m g s α q ℓ schedule t)
    (numerical_run m g s α q hα hq hs ℓ schedule t) ((parameters_run m g s α q hq ℓ schedule t 0 (Nat.zero_le _)).1.le)
  have hqr : (st.frames 0).q = q := root_threshold_run m g s α q ℓ schedule t
  apply (le_div_iff₀ hq).mpr
  have hv : q*(volumeNat g (st.frames 0).active : ℝ) ≤ 1 := by
    have hh := (le_div_iff₀ hq).mp hvol
    nlinarith
  change discoveryEffortPotential g st 0*q ≤ 6
  unfold discoveryEffortPotential
  rw [hqr]
  have hcancel : (2*(volumeNat g (st.frames 0).active : ℝ)+10/q*discoveryCredit g st 0)*q =
      2*q*(volumeNat g (st.frames 0).active : ℝ)+10*discoveryCredit g st 0 := by field_simp
  rw [hcancel]
  nlinarith

lemma child_discoveryEffortPotential_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t j : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    j < st.top → ¬exhausted st j → discoveryEffortPotential g st (j+1) < 12*(st.frames (j+1)).N := by
  intro st hj he
  have hqj : 0 < (st.frames (j+1)).q := (parameters_run m g s α q hq ℓ schedule t (j+1) hj).1
  have hc := child_discoveryCredit_unexhausted m g s α q hα hq hs ℓ schedule t j hj he
  have hv := run_child_volume_unexhausted m g s α q hα hq hs ℓ schedule t j hj he
  have hV : (0 : ℝ) ≤ (volumeNat g (st.frames (j+1)).active : ℝ) := by positivity
  have hN : 0 < (st.frames (j+1)).N := by linarith
  have hvq := mul_lt_mul_of_pos_left hv hqj
  have hcancel : (st.frames (j+1)).q*discoveryEffortPotential g st (j+1) =
      2*(st.frames (j+1)).q*(volumeNat g (st.frames (j+1)).active : ℝ)+10*discoveryCredit g st (j+1) := by
    unfold discoveryEffortPotential
    field_simp
  have hprod : (st.frames (j+1)).q*discoveryEffortPotential g st (j+1) <
      (st.frames (j+1)).q*(12*(st.frames (j+1)).N) := by
    rw [hcancel]
    nlinarith [mul_pos hqj hN]
  nlinarith

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

-- Proof module: Solutions.ProducingEffortInterval

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma producing_potential_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a j : ℕ) (v : Fin n)
    (hp : stepProduction (recursiveRun m g s α q ℓ schedule a)=some (j,v)) :
    let st := recursiveRun m g s α q ℓ schedule a
    discoveryEffortPotential g st j ≤ 12*(st.frames j).N := by
  intro st
  have ht := (pending_push_member st j v (production_pending st j v hp)).1
  have hno := production_unexhausted st j v hp
  cases hj : j with
  | zero =>
    have hh := root_discoveryEffortPotential_bound m g s α q hα hq hs ℓ schedule a
    have hN := root_scale_run m g s α q ℓ schedule a
    rw [hN]
    have hqN : 0 ≤ 1/q := by positivity
    change discoveryEffortPotential g st 0 ≤ 6/q at hh
    have heq : 6/q=6*(1/q) := by ring
    rw [heq] at hh
    linarith
  | succ i =>
    have hlt : i < st.top := by omega
    have hh := child_discoveryEffortPotential_bound m g s α q hα hq hs ℓ schedule a i hlt
      (fun he => hno ⟨i,hlt.le,he⟩)
    exact hh.le

lemma producing_effort_interval_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j id : ℕ) (v : Fin n) (hab : a ≤ b)
    (hja : j ≤ (recursiveRun m g s α q ℓ schedule a).top)
    (hida : ((recursiveRun m g s α q ℓ schedule a).frames j).id=id)
    (hp : stepProduction (recursiveRun m g s α q ℓ schedule b)=some (j,v))
    (hidb : ((recursiveRun m g s α q ℓ schedule b).frames j).id=id) :
    let run := recursiveRun m g s α q ℓ schedule
    (∑ k ∈ Finset.Ico a (b+1), discoveryEffort g (run k) j) ≤ 15*((run a).frames j).N := by
  intro run
  have hjb := (pending_push_member (run b) j v (production_pending (run b) j v hp)).1
  have hdb := (production_running (run b) j v hp).1
  have hspan := open_call_span m g s α q ℓ schedule a b j id hab hja hida hjb hidb hdb
  have hh := discoveryEffort_interval m g s α q hα hq.1 hs ℓ schedule a b j hab
    (fun k hak hkb => (hspan k hak hkb.le).1)
  change (∑ k ∈ Finset.range (b-a), discoveryEffort g (run (a+k)) j) ≤
    discoveryEffortPotential g (run b) j-discoveryEffortPotential g (run a) j at hh
  rw [offset_sum_eq_Ico (fun k => discoveryEffort g (run k) j) a b hab] at hh
  have hP : discoveryEffortPotential g (run b) j ≤ 12*((run b).frames j).N := producing_potential_bound m g s α q hα hq.1 hs ℓ schedule b j v hp
  have hPa := discoveryEffortPotential_nonnegative g (run a)
    (numerical_run m g s α q hα hq.1 hs ℓ schedule a) (parameters_run m g s α q hq.1 ℓ schedule a) j hja
  have hN : ((run b).frames j).N=((run a).frames j).N := congrArg (fun z => z.2.1) (hspan b hab le_rfl).2.2
  have hd : LocalPush.deg g.graph v < 2*((run b).frames j).N := producing_degree_bound m g s α q hα hq.1 hs ℓ schedule b j v hp
  have hN1 : 1 ≤ ((run b).frames j).N := (scale_bounds_run m g s α q hq ℓ schedule b j hjb).1
  have hlast : discoveryEffort g (run b) j ≤ 3*((run b).frames j).N := by
    have hp' : stepProduction (run b)=some (j,v) := hp
    simp only [discoveryEffort,hp',ite_true]
    nlinarith
  rw [Finset.sum_Ico_succ_top hab]
  rw [hN] at hP hlast
  nlinarith

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

lemma callDiscoveryEffort_no_event (g : InputGraph n) (st : RecursiveState n) (id : ℕ)
    (hn : ¬ownPushEvent st id) : callDiscoveryEffort g st id=0 := by
  cases hp : stepProduction st with
  | none => simp [callDiscoveryEffort,hp]
  | some p =>
    obtain ⟨j,v⟩ := p
    have hi : (st.frames j).id ≠ id := fun hh => hn ⟨j,v,hp,hh⟩
    simp [callDiscoveryEffort,hp,hi]

set_option maxHeartbeats 2000000 in
lemma call_discovery_effort_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) (info : CallInformation)
    (hinfo : (recursiveRun m g s α q ℓ schedule T).information id=some info) :
    (∑ k ∈ Finset.range T, callDiscoveryEffort g (recursiveRun m g s α q ℓ schedule k) id) ≤ 15*info.scale := by
  classical
  let run := recursiveRun m g s α q ℓ schedule
  let S := (Finset.range T).filter (fun k => ownPushEvent (run k) id)
  have hsum : (∑ k ∈ Finset.range T, callDiscoveryEffort g (run k) id)=
      ∑ k ∈ S, callDiscoveryEffort g (run k) id := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hn
    apply callDiscoveryEffort_no_event
    intro he
    exact hn (Finset.mem_filter.mpr ⟨hk,he⟩)
  rw [hsum]
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let b := S.max' hS
    have haS : a ∈ S := Finset.min'_mem S hS
    have hbS : b ∈ S := Finset.max'_mem S hS
    obtain ⟨ja,va,hpa,hida⟩ := (Finset.mem_filter.mp haS).2
    obtain ⟨jb,vb,hpb,hidb⟩ := (Finset.mem_filter.mp hbS).2
    have hja := (pending_push_member (run a) ja va (production_pending (run a) ja va hpa)).1
    have hjb := (pending_push_member (run b) jb vb (production_pending (run b) jb vb hpb)).1
    have haT : a ≤ T := (Finset.mem_range.mp (Finset.mem_filter.mp haS).1).le
    have hbT : b ≤ T := (Finset.mem_range.mp (Finset.mem_filter.mp hbS).1).le
    have hpara := open_frame_prefix_parameters m g s α q ℓ schedule a T ja id info haT hinfo hja hida
    have hparb := open_frame_prefix_parameters m g s α q ℓ schedule b T jb id info hbT hinfo hjb hidb
    have hjeq : jb=ja := hparb.1.trans hpara.1.symm
    subst jb
    have hab : a ≤ b := Finset.min'_le S b hbS
    have hbound := producing_effort_interval_bound m g s α q hα hq hs ℓ schedule a b ja id vb hab hja hida hpb hidb
    have hN : ((run a).frames ja).N=info.scale := hpara.2.1
    change (∑ k ∈ Finset.Ico a (b+1), discoveryEffort g (run k) ja) ≤ 15*((run a).frames ja).N at hbound
    rw [hN] at hbound
    apply le_trans ?_ hbound
    have heq : (∑ k ∈ S, callDiscoveryEffort g (run k) id)=∑ k ∈ S, discoveryEffort g (run k) ja := by
      apply Finset.sum_congr rfl
      intro k hk
      obtain ⟨j,v,hp,hid⟩ := (Finset.mem_filter.mp hk).2
      have hj := (pending_push_member (run k) j v (production_pending (run k) j v hp)).1
      have hpar := open_frame_prefix_parameters m g s α q ℓ schedule k T j id info
        (Finset.mem_range.mp (Finset.mem_filter.mp hk).1).le hinfo hj hid
      have he : j=ja := hpar.1.trans hpara.1.symm
      subst j
      simp only [callDiscoveryEffort,discoveryEffort,hp,hid,ite_true]
    rw [heq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact Finset.mem_Ico.mpr ⟨Finset.min'_le S k hk,Nat.lt_succ_of_le (Finset.le_max' S k hk)⟩
    · intro k _ _
      cases hp : stepProduction (run k) with
      | none => simp [discoveryEffort,hp]
      | some p => obtain ⟨j,v⟩ := p; simp only [discoveryEffort,hp]; split <;> (try unfold LocalPush.deg) <;> positivity
  · have hzero : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hzero,Finset.sum_empty]
    have hlegal := information_legal_run m g s α q hq ℓ schedule T id info hinfo
    have hN : 0 ≤ info.scale := by linarith [hlegal.2.1]
    positivity

end
end NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal

theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (T id : ℕ) (info : CallInformation)
    (hinfo : (recursiveRun m g s α q ℓ schedule T).information id=some info) :
    (∑ k ∈ Finset.range T, callDiscoveryEffort g (recursiveRun m g s α q ℓ schedule k) id) ≤ 15*info.scale := by
  exact call_discovery_effort_bound m g s α q hα hq hs ℓ schedule T id info hinfo
