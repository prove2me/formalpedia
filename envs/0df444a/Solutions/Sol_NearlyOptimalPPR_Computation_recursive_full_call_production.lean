-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_full_call_production
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:30:31.184105+00:00
-- url     : https://prove2.me/submissions/7ffa4458-ca2f-45f9-940b-f899440b61db

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
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

lemma ownProduction_interval (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top) :
    (∑ k ∈ Finset.range (b-a), ownProduction g (recursiveRun m g s α q ℓ schedule (a+k)) j) =
      discoveryCredit g (recursiveRun m g s α q ℓ schedule b) j-
        discoveryCredit g (recursiveRun m g s α q ℓ schedule a) j := by
  have hs : (∑ k ∈ Finset.range (b-a), ownProduction g (recursiveRun m g s α q ℓ schedule (a+k)) j) =
      ∑ k ∈ Finset.range (b-a), (discoveryCredit g (recursiveRun m g s α q ℓ schedule (a+k+1)) j-
        discoveryCredit g (recursiveRun m g s α q ℓ schedule (a+k)) j) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hh := discoveryCredit_step m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+k))
      (region_run m g s α q ℓ schedule (a+k)) j (hopen (a+k) (by omega) (by have := Finset.mem_range.mp hk; omega))
    have hstep : discoveryCredit g (recursiveRun m g s α q ℓ schedule (a+k+1)) j =
        discoveryCredit g (recursiveRun m g s α q ℓ schedule (a+k)) j+
          ownProduction g (recursiveRun m g s α q ℓ schedule (a+k)) j := by
      simpa only [recursiveRun,Function.iterate_succ_apply'] using hh
    linarith
  rw [hs,offset_sum_difference (fun t => discoveryCredit g (recursiveRun m g s α q ℓ schedule t) j) a (b-a),Nat.add_sub_of_le hab]

lemma birthProduction_interval (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top) :
    (∑ k ∈ Finset.range (b-a), birthProduction g (recursiveRun m g s α q ℓ schedule (a+k)) j) =
      ((j+3 : ℕ) : ℝ)*((recursiveRun m g s α q ℓ schedule a).frames j).q/2*
        ((volumeNat g ((recursiveRun m g s α q ℓ schedule b).frames j).active : ℝ)-
          (volumeNat g ((recursiveRun m g s α q ℓ schedule a).frames j).active : ℝ)) := by
  have hs : (∑ k ∈ Finset.range (b-a), birthProduction g (recursiveRun m g s α q ℓ schedule (a+k)) j) =
      ∑ k ∈ Finset.range (b-a), (((j+3 : ℕ) : ℝ)*((recursiveRun m g s α q ℓ schedule a).frames j).q/2*
        ((volumeNat g ((recursiveRun m g s α q ℓ schedule (a+k+1)).frames j).active : ℝ)-
          (volumeNat g ((recursiveRun m g s α q ℓ schedule (a+k)).frames j).active : ℝ))) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkt : a+k < b := by have := Finset.mem_range.mp hk; omega
    have hh := birthProduction_volume_step m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+k))
      (region_run m g s α q ℓ schedule (a+k)) j (hopen (a+k) (by omega) hkt)
    have hfixed := frozenFrame_interval m g s α q ℓ schedule a (a+k) j (by omega)
      (fun t hat htt => hopen t hat (by omega))
    have hqfixed : ((recursiveRun m g s α q ℓ schedule (a+k)).frames j).q =
        ((recursiveRun m g s α q ℓ schedule a).frames j).q := congrArg Prod.fst hfixed
    rw [hqfixed] at hh
    simpa only [recursiveRun,Function.iterate_succ_apply'] using hh
  rw [hs,←Finset.mul_sum,offset_sum_difference (fun t => (volumeNat g ((recursiveRun m g s α q ℓ schedule t).frames j).active : ℝ)) a (b-a),Nat.add_sub_of_le hab]

lemma incomingProduction_child (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ) :
    incomingProduction g α st (j+1) = (1-α)*ownProduction g st (j+1)+incomingProduction g α st j := by
  classical
  cases hh : stepProduction st with
  | none => simp [incomingProduction,ownProduction,hh]
  | some p =>
    obtain ⟨t,v⟩ := p
    simp only [incomingProduction,ownProduction,hh]
    by_cases he : t = j+1
    · subst t
      simp
      ring
    · have hle : t ≤ j+1 ↔ t ≤ j := by omega
      simp [he,hle]

lemma incomingProduction_root (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    incomingProduction g α st 0 = (1-α)*ownProduction g st 0 := by
  classical
  cases hh : stepProduction st with
  | none => simp [incomingProduction,ownProduction,hh]
  | some p => obtain ⟨t,v⟩ := p; simp [incomingProduction,ownProduction,hh,Nat.le_zero,mul_assoc]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OwnProductionBounds

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma ownProduction_interval_le_credit (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hja : j ≤ (recursiveRun m g s α q ℓ schedule a).top)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top) :
    (∑ k ∈ Finset.range (b-a), ownProduction g (recursiveRun m g s α q ℓ schedule (a+k)) j) ≤
      discoveryCredit g (recursiveRun m g s α q ℓ schedule b) j := by
  rw [ownProduction_interval m g s α q ℓ schedule a b j hab hopen]
  have hc := discoveryCredit_nonnegative g (recursiveRun m g s α q ℓ schedule a)
    (numerical_run m g s α q hα hq hs ℓ schedule a) (parameters_run m g s α q hq ℓ schedule a) j hja
  linarith

lemma ownProduction_root_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b : ℕ) (hab : a ≤ b) :
    (∑ k ∈ Finset.range (b-a), ownProduction g (recursiveRun m g s α q ℓ schedule (a+k)) 0) ≤ (3/8 : ℝ) := by
  have hh := ownProduction_interval_le_credit m g s α q hα hq hs ℓ schedule a b 0 hab
    (Nat.zero_le _) (fun _ _ _ => Nat.zero_le _)
  exact hh.trans (root_discoveryCredit_bound g s α hα.1.le _ (root_identity_run m g s α q ℓ schedule b)
    (numerical_run m g s α q hα hq hs ℓ schedule b) ((parameters_run m g s α q hq ℓ schedule b 0 (Nat.zero_le _)).1.le))

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

-- Proof module: Solutions.RootProductionCharges

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_production_charge_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b : ℕ) (hab : a ≤ b) :
    (∑ k ∈ Finset.range (b-a), (incomingProduction g α (recursiveRun m g s α q ℓ schedule (a+k)) 0+
      birthProduction g (recursiveRun m g s α q ℓ schedule (a+k)) 0)) ≤ (15/8 : ℝ) := by
  have hown := ownProduction_root_bound m g s α q hα hq hs ℓ schedule a b hab
  have hflow : (∑ k ∈ Finset.range (b-a), incomingProduction g α (recursiveRun m g s α q ℓ schedule (a+k)) 0) ≤ (3/8 : ℝ) := by
    simp_rw [incomingProduction_root]
    rw [←Finset.mul_sum]
    calc
      _ ≤ (1-α)*(3/8) := mul_le_mul_of_nonneg_left hown (by linarith [hα.2])
      _ ≤ _ := by linarith [hα.1]
  have hbirth := birthProduction_interval m g s α q ℓ schedule a b 0 hab (fun _ _ _ => Nat.zero_le _)
  rw [root_threshold_run m g s α q ℓ schedule a] at hbirth
  norm_num only [Nat.cast_zero,zero_add,Nat.cast_ofNat] at hbirth
  have hvol := (run_root_volume_bound m g s α q hα hq hs ℓ schedule b).1
  have hqvol : q*(volumeNat g ((recursiveRun m g s α q ℓ schedule b).frames 0).active : ℝ) ≤ 1 := by
    apply (le_div_iff₀ hq).mp at hvol
    nlinarith
  have hva : (0 : ℝ) ≤ (volumeNat g ((recursiveRun m g s α q ℓ schedule a).frames 0).active : ℝ) := by positivity
  have hbirthbound : (∑ k ∈ Finset.range (b-a), birthProduction g (recursiveRun m g s α q ℓ schedule (a+k)) 0) ≤ (3/2 : ℝ) := by
    rw [hbirth]
    nlinarith [mul_nonneg hq.le hva]
  rw [Finset.sum_add_distrib]
  linarith

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

lemma incoming_interval_le_parent_account (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top ∧
      ((recursiveRun m g s α q ℓ schedule k).frames j).openBudget = true) :
    (∑ k ∈ Finset.range (b-a), incomingProduction g α (recursiveRun m g s α q ℓ schedule (a+k)) j) ≤
      ((recursiveRun m g s α q ℓ schedule b).frames j).W-
        ((recursiveRun m g s α q ℓ schedule a).frames j).W := by
  rw [←W_interval_charges m g s α q ℓ schedule a b j hab hopen,Finset.sum_add_distrib]
  have hb : (0 : ℝ) ≤ ∑ k ∈ Finset.range (b-a), birthProduction g (recursiveRun m g s α q ℓ schedule (a+k)) j := by
    apply Finset.sum_nonneg
    intro k _
    exact (production_nonnegative g α hα.2.le _ (region_run m g s α q ℓ schedule (a+k))
      (parameters_run m g s α q hq ℓ schedule (a+k)) (numerical_run m g s α q hα hq hs ℓ schedule (a+k))
      (keys_run m g s α q hq.le ℓ schedule (a+k)) (isolate_run m g s α q hs ℓ schedule (a+k)) j).2.2
  linarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetNonnegative

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma W_exterior_closed (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t j : ℕ) (v : Fin n) (hj : j ≤ st.top) (hc : (st.frames j).openBudget = false) :
    ((exteriorPush g α st t v).frames j).W = (st.frames j).W := by
  simpa only [hc,Bool.false_eq_true,false_and,and_false,ite_false,add_zero] using
    (exterior_budget_fields g α st t v j hj).2

lemma W_closed_top_step_nonnegative (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hb : BudgetInvariant st) (hc : (st.frames st.top).openBudget = false)
    (hW : 0 ≤ (st.frames st.top).W) :
    0 ≤ ((recursiveStep m g s α ℓ schedule st).frames st.top).W := by
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hW
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hcomp : componentComplete st
  · simpa [hcomp,completeComponent,debit] using hW
  simp only [hcomp,ite_false]
  have hpcfalse := hb st.top le_rfl
  rw [hc] at hpcfalse
  cases hpc : (st.frames st.top).pc <;> try (simp [hpc,budgetPC] at hpcfalse)
  · simp only [hpc]
    split
    · simpa [changePC,changeFrame,debit] using hW
    · split
      · split
        · simpa [changePC,changeFrame,debit] using hW
        · cases hh : pendingPush st with
          | none => simpa [changePC,changeFrame,debit] using hW
          | some p =>
            obtain ⟨t,v⟩ := p
            rw [W_exterior_closed g α st t st.top v le_rfl hc]
            exact hW
      · split <;> simpa [changePC,changeFrame,debit] using hW
  · simp [changeFrame,debit]
  · simp only [hpc]
    split
    · simpa [changePC,changeFrame,debit] using hW
    · split
      · split
        · simpa [changePC,changeFrame,debit] using hW
        · cases hh : pendingPush st with
          | none => simpa [changePC,changeFrame,debit] using hW
          | some p =>
            obtain ⟨t,v⟩ := p
            rw [W_exterior_closed g α st t st.top v le_rfl hc]
            exact hW
      · simpa [changePC,changeFrame,debit] using hW
  · simp only [hpc,endCall]
    split <;> exact hW
  · simp only [hpc,endCall]
    split <;> exact hW

lemma W_existing_step_nonnegative (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (hα : α ≤ 1) (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hp : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st) (hb : BudgetInvariant st) (hstack : StackInvariant st)
    (j : ℕ) (hj : j ≤ st.top) (hW : 0 ≤ (st.frames j).W) :
    0 ≤ ((recursiveStep m g s α ℓ schedule st).frames j).W := by
  by_cases ho : (st.frames j).openBudget = true
  · rw [W_step_open m g s α ℓ schedule st j hj hb ho]
    have hn := production_nonnegative g α hα st hreg hp hnum hkeys hiso j
    exact add_nonneg (add_nonneg hW hn.2.1) hn.2.2
  · have hjtop : j = st.top := by
      by_contra he
      have hpc := hstack j (by omega)
      have hh := hb j hj
      rw [hpc] at hh
      exact ho (by simpa [budgetPC] using hh)
    subst j
    exact W_closed_top_step_nonnegative m g s α ℓ schedule st hb (Bool.eq_false_iff.mpr ho) hW

lemma W_nonnegative_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ∀ j ≤ (recursiveRun m g s α q ℓ schedule t).top,
      0 ≤ ((recursiveRun m g s α q ℓ schedule t).frames j).W := by
  induction t with
  | zero => intro j hj; simp [recursiveRun,recursiveInit,freshFrame,emptyFrame] <;> split_ifs <;> norm_num
  | succ t ih =>
    let st := recursiveRun m g s α q ℓ schedule t
    have hexisting (j : ℕ) (hj : j ≤ st.top) :
        0 ≤ ((recursiveStep m g s α ℓ schedule st).frames j).W :=
      W_existing_step_nonnegative m g s α hα.2.le ℓ schedule st
        (region_run m g s α q ℓ schedule t) (parameters_run m g s α q hq ℓ schedule t)
        (numerical_run m g s α q hα hq hs ℓ schedule t) (keys_run m g s α q hq.le ℓ schedule t)
        (isolate_run m g s α q hs ℓ schedule t) (budget_run m g s α q ℓ schedule t)
        (stack_run m g s α q ℓ schedule t) j hj (ih j hj)
    have hstep : recursiveRun m g s α q ℓ schedule (t+1) = recursiveStep m g s α ℓ schedule st := by
      simp only [st,recursiveRun,Function.iterate_succ_apply']
    rw [hstep]
    intro j hj
    by_cases hle : j ≤ st.top
    · exact hexisting j hle
    · have hg : st.top < (recursiveStep m g s α ℓ schedule st).top := by omega
      obtain ⟨hd,hcomp,hpc,he,hl⟩ := growing_step_guards m g s α ℓ schedule st hg
      have hjnew : j = st.top+1 := by
        simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hcomp,hpc,he,hl] at hj
        change j ≤ st.top+1 at hj
        omega
      subst j
      simp [recursiveStep,hd,hcomp,hpc,he,hl,freshFrame,emptyFrame]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ChildProductionCharges

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma child_production_account (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j+1 ≤ (recursiveRun m g s α q ℓ schedule k).top) :
    let run := recursiveRun m g s α q ℓ schedule
    (∑ k ∈ Finset.range (b-a), (incomingProduction g α (run (a+k)) (j+1)+birthProduction g (run (a+k)) (j+1))) ≤
      (1-α)*(discoveryCredit g (run b) (j+1)-discoveryCredit g (run a) (j+1))+
      ((run b).frames j).W-((run a).frames j).W+
      ((j+1+3 : ℕ) : ℝ)*((run a).frames (j+1)).q/2*
        ((volumeNat g ((run b).frames (j+1)).active : ℝ)-(volumeNat g ((run a).frames (j+1)).active : ℝ)) := by
  intro run
  have hparent : ∀ k, a ≤ k → k < b → j ≤ (run k).top ∧ ((run k).frames j).openBudget = true := by
    intro k hak hkb
    have hj := hopen k hak hkb
    have hjraw : j+1 ≤ (recursiveRun m g s α q ℓ schedule k).top := hj
    have hpc := stack_run m g s α q ℓ schedule k j (Nat.lt_of_succ_le hjraw)
    have hb := budget_run m g s α q ℓ schedule k j (Nat.le_of_succ_le hjraw)
    refine ⟨Nat.le_of_succ_le hj,?_⟩
    simpa [hpc,budgetPC] using hb
  have hW := incoming_interval_le_parent_account m g s α q hα hq hs ℓ schedule a b j hab hparent
  have hown := ownProduction_interval m g s α q ℓ schedule a b (j+1) hab hopen
  have hbirth := birthProduction_interval m g s α q ℓ schedule a b (j+1) hab hopen
  simp_rw [incomingProduction_child]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,hown,hbirth]
  linarith

set_option maxHeartbeats 1000000 in
lemma child_production_charge_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hja : j+1 ≤ (recursiveRun m g s α q ℓ schedule a).top)
    (hopen : ∀ k, a ≤ k → k < b → j+1 ≤ (recursiveRun m g s α q ℓ schedule k).top) :
    let run := recursiveRun m g s α q ℓ schedule
    j < (run b).top → ¬exhausted (run b) j →
      (∑ k ∈ Finset.range (b-a), (incomingProduction g α (run (a+k)) (j+1)+birthProduction g (run (a+k)) (j+1))) <
        ((j+6 : ℕ) : ℝ)*((run b).frames (j+1)).q*((run b).frames (j+1)).N := by
  intro run hjb he
  let st := run b
  let qa := ((run a).frames (j+1)).q
  let qb := (st.frames (j+1)).q
  let N := (st.frames (j+1)).N
  let V := (volumeNat g (st.frames (j+1)).active : ℝ)
  let A := ((j+1+3 : ℕ) : ℝ)*qb/2
  have hacc := child_production_account m g s α q hα hq hs ℓ schedule a b j hab hopen
  have hqfixed : ((run b).frames (j+1)).q = ((run a).frames (j+1)).q :=
    congrArg Prod.fst (frozenFrame_interval m g s α q ℓ schedule a b (j+1) hab hopen)
  have hqeq : qa = qb := hqfixed.symm
  have hqa : 0 < qb := (parameters_run m g s α q hq ℓ schedule b (j+1) hjb).1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hca : 0 ≤ discoveryCredit g (run a) (j+1) := discoveryCredit_nonnegative g (run a)
    (numerical_run m g s α q hα hq hs ℓ schedule a) (parameters_run m g s α q hq ℓ schedule a) (j+1) hja
  have hcb : 0 ≤ discoveryCredit g st (j+1) := discoveryCredit_nonnegative g st
    (numerical_run m g s α q hα hq hs ℓ schedule b) (parameters_run m g s α q hq ℓ schedule b) (j+1) hjb
  have hWa : 0 ≤ ((run a).frames j).W := W_nonnegative_run m g s α q hα hq hs ℓ schedule a j (by omega)
  have hVa : (0 : ℝ) ≤ (volumeNat g ((run a).frames (j+1)).active : ℝ) := by positivity
  have hcoef : 0 ≤ 1-α := by linarith [hα.2]
  have hsmallC := child_discoveryCredit_unexhausted m g s α q hα hq hs ℓ schedule b j hjb he
  have hsmallV := run_child_volume_unexhausted m g s α q hα hq hs ℓ schedule b j hjb he
  have hbudget : (st.frames j).openBudget = true := by
    simpa [stack_run m g s α q ℓ schedule b j hjb,budgetPC] using budget_run m g s α q ℓ schedule b j hjb.le
  have hW : (st.frames j).W < qb*N := by
    have hscale : ScaleInvariant st := scale_run m g s α q hq ℓ schedule b
    have hQ : (st.frames j).Q = qb*N := by
      dsimp only [qb,N]
      rw [hscale.1 j hjb.le hbudget,hscale.2 j hjb,threshold_relation_run m g s α q ℓ schedule b j hjb]
    have hh : (st.frames j).W < (st.frames j).Q := by
      have he' : ¬exhausted st j := he
      simpa only [exhausted,hbudget,true_and,not_le] using he'
    rwa [hQ] at hh
  have hraw : (∑ k ∈ Finset.range (b-a), (incomingProduction g α (run (a+k)) (j+1)+birthProduction g (run (a+k)) (j+1))) ≤
      discoveryCredit g st (j+1)+(st.frames j).W+A*V := by
    have hc1 := mul_nonneg hcoef hca
    have hc2 := mul_nonneg hα.1.le hcb
    have hv1 := mul_nonneg hA.le hVa
    change _ ≤ (1-α)*(discoveryCredit g st (j+1)-discoveryCredit g (run a) (j+1))+
      (st.frames j).W-((run a).frames j).W+
      ((j+1+3 : ℕ) : ℝ)*qa/2*(V-(volumeNat g ((run a).frames (j+1)).active : ℝ)) at hacc
    rw [hqeq] at hacc
    change _ ≤ _+_+A*(V-_) at hacc
    nlinarith
  have hAV : A*V < ((j+1+3 : ℕ) : ℝ)*qb*N := by
    have hh := mul_lt_mul_of_pos_left hsmallV hA
    dsimp only [A,V] at hh ⊢
    nlinarith
  change discoveryCredit g st (j+1) < (3/4 : ℝ)*qb*N at hsmallC
  have hqN : 0 < qb*N := by
    have hN : (1 : ℝ) ≤ N := by
      dsimp only [N]
      have hscale : ScaleInvariant st := scale_run m g s α q hq ℓ schedule b
      rw [hscale.2 j hjb]
      exact_mod_cast (parameters_run m g s α q hq ℓ schedule b j hjb.le).2.1
    exact mul_pos hqa (by linarith)
  push_cast at hAV ⊢
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

-- Proof module: Solutions.FullCallResources

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma full_solve_volume_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (he : fullSolveEvent g (recursiveRun m g s α q ℓ schedule t) id) :
    let st := recursiveRun m g s α q ℓ schedule t
    (volumeNat g (st.frames st.top).active : ℝ) ≤ 2*(st.frames st.top).N := by
  intro st
  cases hj : st.top with
  | zero =>
    have hv := (run_root_volume_bound m g s α q hα hq hs ℓ schedule t).1
    have hN := root_scale_run m g s α q ℓ schedule t
    rw [hN]
    have hqpos : 0 ≤ 1/q := by positivity
    linarith
  | succ j =>
    have hlt : j < st.top := by omega
    have hx : ¬exhausted st j := fun hh => he.2.2.2.1 ⟨j,hlt.le,hh⟩
    have hv := run_child_volume_unexhausted m g s α q hα hq hs ℓ schedule t j hlt hx
    simpa only [hj] using hv.le

lemma full_call_production_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a ≤ b)
    (ha : fullSolveEvent g (recursiveRun m g s α q ℓ schedule a) id)
    (hb : fullSolveEvent g (recursiveRun m g s α q ℓ schedule b) id) :
    let run := recursiveRun m g s α q ℓ schedule
    let j := (run a).top
    (∑ k ∈ Finset.Ico a b, (incomingProduction g α (run k) j+birthProduction g (run k) j)) ≤
      2*(kappa ℓ 0 : ℝ)*((run a).frames j).q*((run a).frames j).N := by
  intro run j
  have hspan := full_solve_event_span m g s α q ℓ schedule a b id hab ha hb
  have hlevels := full_events_same_level m g s α q ℓ schedule a b id hab ha hb
  have hf := frozenFrame_interval m g s α q ℓ schedule a b j hab
    (fun k hak hkb => (hspan k hak hkb.le).1)
  have hqeq : ((run b).frames j).q=((run a).frames j).q := congrArg Prod.fst hf
  have hNeq : ((run b).frames j).N=((run a).frames j).N := congrArg (fun f => f.2.1) hf
  rw [←offset_sum_eq_Ico _ a b hab]
  cases hj : j with
  | zero =>
    have hp := root_production_charge_bound m g s α q hα hq hs ℓ schedule a b hab
    have hqr : ((run a).frames 0).q=q := root_threshold_run m g s α q ℓ schedule a
    have hNr : ((run a).frames 0).N=1/q := root_scale_run m g s α q ℓ schedule a
    rw [hqr,hNr]
    have heq : 2*(kappa ℓ 0 : ℝ)*q*(1/q)=2*(kappa ℓ 0 : ℝ) := by field_simp
    rw [heq]
    have hk : (3 : ℝ) ≤ (kappa ℓ 0 : ℝ) := by
      exact_mod_cast (show 3 ≤ kappa ℓ 0 by simp only [kappa,Nat.sub_zero]; omega)
    linarith
  | succ i =>
    have hja : i+1 ≤ (run a).top := by change i+1 ≤ j; omega
    have hjb : i < (run b).top := by
      have htA : (run a).top=i+1 := hj
      have htB : (run b).top=i+1 := hlevels.symm.trans htA
      omega
    have hex : ¬exhausted (run b) i := fun hh => hb.2.2.2.1 ⟨i,hjb.le,hh⟩
    have hp := child_production_charge_bound m g s α q hα hq hs ℓ schedule a b i hab hja
      (fun k hak hkb => by
        have hk : j ≤ (run k).top := (hspan k hak hkb.le).1
        change i+1 ≤ (run k).top
        omega) hjb hex
    have hd : j ≤ ℓ := depth_run m g s α q ℓ schedule a
    have hcoef : ((i+6 : ℕ) : ℝ) ≤ 2*(kappa ℓ 0 : ℝ) := by
      simp only [kappa,Nat.sub_zero]
      push_cast
      have hi : (i : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (show i ≤ ℓ by omega)
      linarith
    have hparams := parameters_run m g s α q hq ℓ schedule a j le_rfl
    have hN : 0 ≤ ((run a).frames j).N := by
      have hv := full_solve_volume_bound m g s α q hα hq hs ℓ schedule a id ha
      have hv0 : (0 : ℝ) ≤ (volumeNat g ((run a).frames j).active : ℝ) := by positivity
      linarith
    rw [hj] at hqeq hNeq
    rw [hqeq,hNeq] at hp
    exact hp.le.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (by simpa only [hj] using hparams.1.le)) (by simpa only [hj] using hN))

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation

theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a ≤ b)
    (ha : fullSolveEvent g (recursiveRun m g s α q ℓ schedule a) id)
    (hb : fullSolveEvent g (recursiveRun m g s α q ℓ schedule b) id) :
    let run := recursiveRun m g s α q ℓ schedule
    let j := (run a).top
    (∑ k ∈ Finset.Ico a b, (incomingProduction g α (run k) j+birthProduction g (run k) j)) ≤
      2*(kappa ℓ 0 : ℝ)*((run a).frames j).q*((run a).frames j).N := by
  exact full_call_production_bound m g s α q hα hq hs ℓ schedule a b id hab ha hb
