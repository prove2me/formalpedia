-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_large_doubling_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:20:22.083736+00:00
-- url     : https://prove2.me/submissions/78d7b6ee-0b4e-45a9-bfc6-3c51510e7007

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_budget_energy
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_discovery_credit
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_forcing_bound
import Theorems.Thm_NearlyOptimalPPR_Computation_active_region_potentials
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_successful_request_bounds
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_full_call_production
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_full_solve_comparison
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_doubling_volume

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

namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}
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
  exact NearlyOptimalPPR.Computation.recursive_successful_request_bounds m n g s α q hα hq hs ℓ schedule t id he hfinish

lemma full_call_production_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a ≤ b)
    (ha : fullSolveEvent g (recursiveRun m g s α q ℓ schedule a) id)
    (hb : fullSolveEvent g (recursiveRun m g s α q ℓ schedule b) id) :
    let run := recursiveRun m g s α q ℓ schedule
    let j := (run a).top
    (∑ k ∈ Finset.Ico a b, (incomingProduction g α (run k) j+birthProduction g (run k) j)) ≤
      2*(kappa ℓ 0 : ℝ)*((run a).frames j).q*((run a).frames j).N := by
  exact NearlyOptimalPPR.Computation.recursive_full_call_production m n g s α q hα hq hs ℓ schedule a b id hab ha hb

lemma actual_full_solve_comparison (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b : ℕ) (hab : a+1 ≤ b) :
    let run := recursiveRun m g s α q ℓ schedule
    let st := run a
    let next := run b
    let j := st.top
    let H := (st.frames j).active
    let F := (next.frames j).active
    let Z := F \ H
    let h := solveOn g α H (st.frames j).residual
    let u := next.x-(run (a+1)).x
    let D := doubledSet H h (virtualPotential st j)
    (∀ k, a ≤ k → k < b → j ≤ (run k).top) → j ≤ next.top →
    st.done = false → ¬componentComplete st → (st.frames j).pc = .fullSolve →
      ¬anyExhausted st → pendingPush st = none →
      (∑ v ∈ F, (next.frames j).residual v) ≤
        (1-α)*(∑ v ∈ Fᶜ, LocalPush.deg g.graph v*u v)+
        4*(kappa ℓ 0 : ℝ)*(st.frames j).q*(volumeNat g Z : ℝ)+
        2*(kappa ℓ 0 : ℝ)*(st.frames j).q*(volumeNat g D : ℝ)+
        2*∑ v ∈ D, (st.frames j).residual v := by
  exact NearlyOptimalPPR.Computation.recursive_full_solve_comparison m n g s α q hα hq hs ℓ schedule a b hab

lemma actual_doubling_volume_sum (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α ≤ 1/2) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (τ : ℕ → ℕ) (hτ : StrictMono τ) (T j : ℕ) :
    let run := recursiveRun m g s α q ℓ schedule
    let F := ((run (τ T)).frames j).active
    (∀ t, τ 0 ≤ t → t ≤ τ T → j ≤ (run t).top) →
    (∀ k < T, (run (τ k)).top = j ∧ (run (τ k)).done = false ∧
      ¬componentComplete (run (τ k)) ∧ ((run (τ k)).frames j).pc = .fullSolve ∧
      ¬anyExhausted (run (τ k))) →
    (∃ v, g.graph.Reachable s v ∧ v ∉ ((run (τ T)).frames 0).active) →
    (∑ k ∈ Finset.range T, (volumeNat g (fullSolveDoubles g α (run (τ k)) j) : ℝ)) ≤
      (volumeNat g F : ℝ)*((Real.log (3/q)-Real.log (3*q/8))/Real.log 2) := by
  exact NearlyOptimalPPR.Computation.recursive_doubling_volume m n g s α q hα hq hs ℓ schedule τ hτ T j

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

-- Proof module: Solutions.RecursiveInvariants

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

variable {n : ℕ}

lemma root_exterior_projection (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (v : Fin n) :
    let f := st.frames 0
    let h := min (f.residual v / (5 * LocalPush.deg g.graph v)) (3*f.q/8 - st.x v)
    let activated := st.x v+h = 3*f.q/8
    let u := exteriorPush g α st 0 v
    u.x = Function.update st.x v (st.x v+h) ∧
    (u.frames 0).q = f.q ∧
    (u.frames 0).active = (if activated then insert v f.active else f.active) ∧
    (u.frames 0).residual = fun w => f.residual w +
      (if w = v then -5*LocalPush.deg g.graph v*h else 0) +
      (if g.graph.Adj w v then (1-α)*h else 0) +
      (if activated ∧ w = v then f.q*LocalPush.deg g.graph v/2 else 0) := by
  classical
  dsimp only
  by_cases ha : st.x v + min ((st.frames 0).residual v / (5*LocalPush.deg g.graph v))
      (3*(st.frames 0).q/8 - st.x v) = 3*(st.frames 0).q/8
  · by_cases ht : 0 < st.top
    all_goals
      simp [exteriorPush, relative, ha, ht, refreshKeys, debit, changeFrame, parentDomain]
      ext w
      by_cases hw : w = v <;> simp [Function.update_apply, hw] <;> ring
  · simp [exteriorPush, relative, ha, refreshKeys, debit, changeFrame, parentDomain]

lemma nonroot_exterior_projection (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (ht : 0 < t) :
    let f := st.frames t
    let h := min (f.residual v / (5*LocalPush.deg g.graph v)) (3*f.q/8-relative st t v)
    let u := exteriorPush g α st t v
    u.x = Function.update st.x v (st.x v+h) ∧
    (u.frames 0).q = (st.frames 0).q ∧
    (u.frames 0).active = (st.frames 0).active ∧
    (u.frames 0).residual = fun w => (st.frames 0).residual w +
      (if w = v then -LocalPush.deg g.graph v*h else 0) +
      (if g.graph.Adj w v then (1-α)*h else 0) := by
  classical
  dsimp only
  by_cases ha : relative st t v +
      min ((st.frames t).residual v / (5*LocalPush.deg g.graph v))
        (3*(st.frames t).q/8-relative st t v) = 3*(st.frames t).q/8
  · by_cases htop : t < st.top
    all_goals simp [exteriorPush,ha,htop,refreshKeys,debit,changeFrame,parentDomain,
      ht,ht.ne',Ne.symm ht.ne']
  · simp [exteriorPush,ha,refreshKeys,debit,changeFrame,parentDomain,
      ht,ht.ne',Ne.symm ht.ne']

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

-- Proof module: Solutions.GraphCut

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma neighbor_count (g : InputGraph n) (v : Fin n) (H : Finset (Fin n)) :
    (((g.neighbors v).filter (fun u => u ∈ H)).length : ℤ) =
      ∑ u ∈ H, if g.graph.Adj v u then 1 else 0 := by
  classical
  have he : ((g.neighbors v).filter (fun u => u ∈ H)).toFinset = H.filter (g.graph.Adj v) := by
    ext u
    simp [g.correct,and_comm]
  rw [← List.toFinset_card_of_nodup ((g.nodup v).filter _),he]
  simp

lemma neighbor_degree (g : InputGraph n) (v : Fin n) :
    (g.neighbors v).length = g.graph.degree v := by
  have he : (g.neighbors v).toFinset = g.graph.neighborFinset v := by
    ext u
    simp [g.correct]
  rw [← List.toFinset_card_of_nodup (g.nodup v),he,SimpleGraph.card_neighborFinset_eq_degree]

lemma graphCut_insert (g : InputGraph n) (H : Finset (Fin n)) (v : Fin n) (hv : v ∉ H) :
    graphCut g (insert v H) = graphCut g H + (g.neighbors v).length -
      2*((g.neighbors v).filter (fun u => u ∈ H)).length := by
  classical
  have hrow (u : Fin n) :
      (∑ w, if g.graph.Adj u w ∧ w ∉ insert v H then (1 : ℤ) else 0) =
        (∑ w, if g.graph.Adj u w ∧ w ∉ H then 1 else 0) -
          (if g.graph.Adj u v then 1 else 0) := by
    have he : (fun w => if g.graph.Adj u w ∧ w ∉ insert v H then (1 : ℤ) else 0) =
        (fun w => (if g.graph.Adj u w ∧ w ∉ H then 1 else 0) -
          (if w = v then (if g.graph.Adj u v then 1 else 0) else 0)) := by
      ext w
      by_cases hw : w = v
      · subst w
        simp [hv]
      · simp [hw]
    rw [he,Finset.sum_sub_distrib]
    simp
  have hnew : (∑ w, if g.graph.Adj v w ∧ w ∉ insert v H then (1 : ℤ) else 0) =
      (g.graph.degree v : ℤ) - ∑ w ∈ H, if g.graph.Adj v w then 1 else 0 := by
    rw [hrow]
    simp only [SimpleGraph.irrefl,ite_false,sub_zero]
    have he : (fun w => if g.graph.Adj v w ∧ w ∉ H then (1 : ℤ) else 0) =
        (fun w => (if g.graph.Adj v w then 1 else 0) -
          (if w ∈ H then (if g.graph.Adj v w then 1 else 0) else 0)) := by
      ext w
      by_cases ha : g.graph.Adj v w <;> by_cases hh : w ∈ H <;> simp [ha,hh]
    rw [he,Finset.sum_sub_distrib,← SimpleGraph.degree_eq_sum_if_adj]
    simp
  unfold graphCut
  rw [Finset.sum_insert hv,hnew]
  simp only [hrow,Finset.sum_sub_distrib]
  have hs : (∑ u ∈ H, if g.graph.Adj u v then (1 : ℤ) else 0) =
      ∑ u ∈ H, if g.graph.Adj v u then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro u _
    simp only [g.graph.adj_comm]
  rw [hs,← neighbor_count,← neighbor_degree]
  ring

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

lemma boundary_exterior_projection (g : InputGraph n) (α : ℝ)
    (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    let h := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)
    let a := relative st t v+h = 3*(st.frames t).q/8
    let u := exteriorPush g α st t v
    u.boundaryEdges = (if a ∧ t = 0 then st.boundaryEdges+(g.neighbors v).length-
      2*((g.neighbors v).filter (fun w => w ∈ (st.frames 0).active)).length else st.boundaryEdges) ∧
    (u.frames 0).active = (if a ∧ t = 0 then insert v (st.frames 0).active else (st.frames 0).active) := by
  classical
  dsimp only
  by_cases ha : relative st t v+min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v) = 3*(st.frames t).q/8
  · by_cases ht : t = 0
    · subst t
      by_cases htop : 0 < st.top
      all_goals simp [exteriorPush,ha,htop,refreshKeys,debit,changeFrame]
    · by_cases htop : t < st.top
      all_goals simp [exteriorPush,ha,ht,htop,refreshKeys,debit,changeFrame,Ne.symm ht]
  · simp [exteriorPush,ha,refreshKeys,debit]

lemma boundary_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hi : BoundaryIdentity g st)
    (hv : t = 0 → v ∉ (st.frames 0).active) :
    BoundaryIdentity g (exteriorPush g α st t v) := by
  classical
  obtain ⟨hb,hH⟩ := boundary_exterior_projection g α st t v
  unfold BoundaryIdentity
  rw [hb,hH]
  split
  · rename_i ha
    rw [graphCut_insert g (st.frames 0).active v (hv ha.2),hi]
  · exact hi

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

lemma boundary_pending (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hr : RegionInvariant st) (hi : BoundaryIdentity g st)
    (hp : pendingPush st = some (t,v)) :
    BoundaryIdentity g (exteriorPush g α st t v) := by
  apply boundary_exterior g α st t v hi
  intro ht
  obtain ⟨hlev,hm⟩ := pending_push_member st t v hp
  subst t
  exact (Finset.mem_sdiff.mp ((hr 0 (Nat.zero_le _)).2.1 hm)).2

@[simp] lemma active_ite (P : Prop) [Decidable P] (a b : RecursiveState n) (i : ℕ) :
    ((if P then a else b).frames i).active =
      if P then (a.frames i).active else (b.frames i).active := by split <;> rfl
@[simp] lemma boundary_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).boundaryEdges = if P then a.boundaryEdges else b.boundaryEdges := by split <;> rfl

set_option maxHeartbeats 1000000 in
lemma boundary_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hr : RegionInvariant st) (hi : BoundaryIdentity g st) :
    BoundaryIdentity g (recursiveStep m g s α ℓ schedule st) := by
  classical
  change st.boundaryEdges = graphCut g (st.frames 0).active at hi
  by_cases htop : st.top = 0
  · have ht : (0 : ℕ) = st.top := htop.symm
    cases hp : pendingPush st with
    | none =>
      cases hpc : (st.frames st.top).pc <;>
        simp only [htop] at hpc <;>
        simp [recursiveStep,hpc,hp,BoundaryIdentity,htop,debit,
          changePC,changeFrame,Function.update_apply,finishEpisode,refreshKeys,
          jointUpdate,completeComponent,endCall,hi]
    | some p =>
      obtain ⟨t,v⟩ := p
      have he := boundary_pending g α st t v hr hi hp
      unfold BoundaryIdentity at he
      cases hpc : (st.frames st.top).pc <;>
        simp only [htop] at hpc <;>
        simp [recursiveStep,hpc,hp,BoundaryIdentity,htop,debit,
          changePC,changeFrame,Function.update_apply,finishEpisode,refreshKeys,
          jointUpdate,completeComponent,endCall,hi,he] <;> split_ifs <;> rfl
  · have ht : (0 : ℕ) ≠ st.top := Ne.symm htop
    cases hp : pendingPush st with
    | none =>
      cases hpc : (st.frames st.top).pc <;>
        simp [recursiveStep,hpc,hp,BoundaryIdentity,htop,ht,debit,
          changePC,changeFrame,Function.update_apply,finishEpisode,refreshKeys,
          jointUpdate,completeComponent,endCall,hi]
    | some p =>
      obtain ⟨t,v⟩ := p
      have he := boundary_pending g α st t v hr hi hp
      unfold BoundaryIdentity at he
      cases hpc : (st.frames st.top).pc <;>
        simp [recursiveStep,hpc,hp,BoundaryIdentity,htop,ht,debit,
          changePC,changeFrame,Function.update_apply,finishEpisode,refreshKeys,
          jointUpdate,completeComponent,endCall,hi,he] <;> split_ifs <;> rfl

lemma boundary_run (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    BoundaryIdentity g (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simp [recursiveRun,recursiveInit,freshFrame,emptyFrame,BoundaryIdentity,graphCut]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      boundary_step m g s α ℓ schedule _ (region_run m g s α q ℓ schedule t) ih

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

-- Proof module: Solutions.PPRLinearAlgebra

set_option autoImplicit false
open Finset Matrix
open NearlyOptimalPPR.Computation

namespace NearlyOptimalPPR.Computation
variable {V : Type*} [Fintype V] [DecidableEq V]
local instance positive_adjacency (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (positiveGraph G).Adj :=
  inferInstanceAs (DecidableRel (G.induce {v | 0 < G.degree v}).Adj)

lemma lap_mul_apply (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (x : V → ℝ) (v : V) :
    (LocalPush.Lα G α *ᵥ x) v =
      LocalPush.deg G v * x v - (1 - α) * ∑ u ∈ G.neighborFinset v, x u := by
  simp [LocalPush.Lα, LocalPush.degM, LocalPush.adjM, sub_mulVec,
    smul_mulVec, SimpleGraph.adjMatrix_mulVec_apply, mulVec_diagonal]

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

-- Proof module: Solutions.IsolateStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma run_pending_positive (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule)
    (k t : ℕ) (v : Fin n)
    (hp : pendingPush (recursiveRun m g s α q ℓ schedule k) = some (t,v)) : 0 < g.graph.degree v := by
  exact isolate_pending_positive g _ (isolate_run m g s α q hs ℓ schedule k)
    (keys_run m g s α q hq ℓ schedule k) t v hp

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

-- Proof module: Solutions.DoublingCounts

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma paid_event_count (f : ℕ → ℝ) (E : Finset ℕ) (T : ℕ) (δ : ℝ)
    (hE : E ⊆ Finset.range T) (hf : ∀ k < T, 0 ≤ f k)
    (hpaid : ∀ k ∈ E, δ ≤ f k) :
    δ*(E.card : ℝ) ≤ ∑ k ∈ Finset.range T, f k := by
  calc
    _ = ∑ k ∈ E, δ := by simp [mul_comm]
    _ ≤ ∑ k ∈ E, f k := Finset.sum_le_sum hpaid
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hE (fun k hk _ => hf k (Finset.mem_range.mp hk))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ConnectedInsertion

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma singleton_connected (g : InputGraph n) (v : Fin n) :
    (g.graph.induce (↑({v} : Finset (Fin n)) : Set (Fin n))).Connected := by
  letI : Nonempty {w : Fin n // w ∈ ({v} : Finset (Fin n))} := ⟨⟨v,by simp⟩⟩
  letI : Subsingleton {w : Fin n // w ∈ ({v} : Finset (Fin n))} :=
    ⟨fun a b => Subtype.ext (by
      have ha : a.val = v := Finset.mem_singleton.mp a.property
      have hb : b.val = v := Finset.mem_singleton.mp b.property
      exact ha.trans hb.symm)⟩
  exact SimpleGraph.Connected.of_subsingleton

lemma connected_insert_neighbor (g : InputGraph n) (H : Finset (Fin n))
    (hH : (g.graph.induce (↑H : Set (Fin n))).Connected) (v w : Fin n)
    (hw : w ∈ H) (hvw : g.graph.Adj v w) :
    (g.graph.induce (↑(insert v H) : Set (Fin n))).Connected := by
  classical
  let φ : g.graph.induce (↑H : Set (Fin n)) →g g.graph.induce (↑(insert v H) : Set (Fin n)) :=
    { toFun := fun a => ⟨a.val,Finset.mem_insert_of_mem a.property⟩
      map_rel' := fun ha => ha }
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨w,Finset.mem_insert_of_mem hw⟩,?_⟩
  intro u
  by_cases hu : u.val = v
  · have he : u = ⟨v,Finset.mem_insert_self _ _⟩ := Subtype.ext hu
    rw [he]
    exact SimpleGraph.Adj.reachable hvw.symm
  · have huH : u.val ∈ H := (Finset.mem_insert.mp u.property).resolve_left hu
    simpa [φ] using (hH.preconnected ⟨w,hw⟩ ⟨u.val,huH⟩).map φ

lemma connected_insert_source (g : InputGraph n) (s : Fin n) (H : Finset (Fin n))
    (hi : H.Nonempty → s ∈ H ∧ (g.graph.induce (↑H : Set (Fin n))).Connected)
    (v : Fin n) (hout : v ∉ H) (hv : v = s ∨ ∃ w ∈ H, g.graph.Adj v w) :
    s ∈ insert v H ∧ (g.graph.induce (↑(insert v H) : Set (Fin n))).Connected := by
  classical
  by_cases he : H = ∅
  · subst H
    have hvs : v = s := by
      rcases hv with hs|⟨w,hw,_⟩
      · exact hs
      · simp at hw
    subst v
    simpa using And.intro (by simp : s ∈ ({s} : Finset (Fin n))) (singleton_connected g s)
  · obtain ⟨hs,hconn⟩ := hi (Finset.nonempty_iff_ne_empty.mpr he)
    have hneighbor : ∃ w ∈ H, g.graph.Adj v w := by
      rcases hv with hv|hh
      · subst v
        exact False.elim (hout hs)
      · exact hh
    obtain ⟨w,hw,hvw⟩ := hneighbor
    exact ⟨Finset.mem_insert_of_mem hs,connected_insert_neighbor g H hconn v w hw hvw⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.Activation

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma activation_attaches (g : InputGraph n) (s v : Fin n) (α : ℝ)
    (st : RecursiveState n) (hα : 0 < α ∧ α < 1)
    (hi : RootIdentity g s α st) (hq : 0 < (st.frames 0).q)
    (hd : 0 < g.graph.degree v) (hv : v ∉ (st.frames 0).active)
    (hvs : v ≠ s)
    (hx : ∀ w ∉ (st.frames 0).active, st.x w ≤ 3*(st.frames 0).q/8)
    (δ : ℝ) (hc : st.x v+δ = 3*(st.frames 0).q/8)
    (hr : 5*LocalPush.deg g.graph v*δ ≤ (st.frames 0).residual v) :
    ∃ w ∈ (st.frames 0).active, g.graph.Adj v w := by
  classical
  by_contra hn
  have hw : ∀ w ∈ g.graph.neighborFinset v, w ∉ (st.frames 0).active := by
    intro w ha hm
    exact hn ⟨w,hm,by simpa using ha⟩
  have hsum : (∑ w ∈ g.graph.neighborFinset v, st.x w) ≤
      LocalPush.deg g.graph v*(3*(st.frames 0).q/8) := by
    calc
      _ ≤ ∑ w ∈ g.graph.neighborFinset v, (3*(st.frames 0).q/8) :=
        Finset.sum_le_sum fun w ha => hx w (hw w ha)
      _ = _ := by simp [LocalPush.deg]
  have hid := hi v
  simp only [hv,ite_false] at hid
  unfold residual at hid
  simp only [Pi.sub_apply,LocalPush.e,Pi.single_apply, hvs,ite_false] at hid
  rw [lap_mul_apply] at hid
  have hdeg : 0 < LocalPush.deg g.graph v := by
    unfold LocalPush.deg
    exact_mod_cast hd
  have hcap : 0 < 3*(st.frames 0).q/8 := by positivity
  have hh := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hα.2.le)
  have hprod := mul_pos (mul_pos hα.1 hdeg) hcap
  nlinarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootConnected

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_connected_transport (g : InputGraph n) (s : Fin n) (st u : RecursiveState n)
    (hi : RootConnected g s st) (hA : (u.frames 0).active = (st.frames 0).active) :
    RootConnected g s u := by
  change ConnectedRootSet g s (u.frames 0).active
  rw [hA]
  exact hi

lemma root_connected_exterior (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (st : RecursiveState n) (hroot : RootIdentity g s α st) (hparam : ParameterInvariant st)
    (hnum : NumericalInvariant g st) (hi : RootConnected g s st)
    (t : ℕ) (v : Fin n) (hout : v ∉ (st.frames t).active) (hd : 0 < g.graph.degree v) :
    RootConnected g s (exteriorPush g α st t v) := by
  classical
  by_cases ht : t = 0
  · subst t
    let δ := min ((st.frames 0).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames 0).q/8-st.x v)
    have hA := (root_exterior_projection g α st v).2.2.1
    change ConnectedRootSet g s ((exteriorPush g α st 0 v).frames 0).active
    rw [hA]
    by_cases ha : st.x v+δ = 3*(st.frames 0).q/8
    · rw [if_pos ha]
      intro _
      apply connected_insert_source g s (st.frames 0).active hi v hout
      by_cases hvs : v = s
      · exact Or.inl hvs
      · apply Or.inr
        have hx (w : Fin n) (hw : w ∉ (st.frames 0).active) : st.x w ≤ 3*(st.frames 0).q/8 := by
          simpa [relative] using (((hnum 0 (Nat.zero_le _)).1 w (by simp [parentDomain])).2.2.2 hw).le
        have hn := (hnum 0 (Nat.zero_le _)).1 v (by simp [parentDomain])
        have hd' : 0 < LocalPush.deg g.graph v := by unfold LocalPush.deg; exact_mod_cast hd
        have hb := crossing_push_bounds (LocalPush.deg g.graph v) (st.frames 0).q
          ((st.frames 0).residual v) (st.x v) hd' (hparam 0 (Nat.zero_le _)).1 hn.1
          ⟨by simpa [relative] using hn.2.1,hx v hout⟩
        exact activation_attaches g s v α st hα hroot (hparam 0 (Nat.zero_le _)).1 hd hout hvs hx δ ha
          (sub_nonneg.mp hb.2.1)
    · rw [if_neg ha]
      exact hi
  · apply root_connected_transport g s st _ hi
    exact (nonroot_exterior_projection g α st t v (Nat.pos_of_ne_zero ht)).2.2.1

lemma root_connected_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    RootConnected g s (recursiveInit g s q ℓ schedule) := by
  simp [RootConnected,ConnectedRootSet,recursiveInit,freshFrame,emptyFrame]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootConnectedControl

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_connected_metadata (g : InputGraph n) (s : Fin n) (st : RecursiveState n)
    (hi : RootConnected g s st) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hA : (f (st.frames j)).active = (st.frames j).active) :
    RootConnected g s (changeFrame st j f) := by
  apply root_connected_transport g s st (changeFrame st j f) hi
  by_cases he : (0 : ℕ) = j <;> simp [changeFrame,he,hA]

lemma root_connected_PC (g : InputGraph n) (s : Fin n) (st : RecursiveState n)
    (pc : NormalizePC) (hi : RootConnected g s st) : RootConnected g s (changePC st pc) :=
  root_connected_metadata g s st hi st.top _ rfl

lemma root_connected_joint (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (hi : RootConnected g s st) : RootConnected g s (jointUpdate g α st h) := by
  apply root_connected_transport g s st (jointUpdate g α st h) hi
  simp [jointUpdate]

lemma root_connected_refresh (g : InputGraph n) (s : Fin n) (st : RecursiveState n)
    (T : Finset (Fin n)) (hi : RootConnected g s st) : RootConnected g s (refreshKeys g st T) :=
  root_connected_transport g s st (refreshKeys g st T) hi (refresh_active g st T 0)

lemma root_connected_finish (g : InputGraph n) (s : Fin n) (st : RecursiveState n)
    (hi : RootConnected g s st) : RootConnected g s (finishEpisode st) := by
  apply root_connected_transport g s st (finishEpisode st) hi
  by_cases he : (0 : ℕ) = st.top <;> simp [finishEpisode,changeFrame,he]

lemma root_connected_newFrame (g : InputGraph n) (s : Fin n) (st : RecursiveState n)
    (f : NormalizeFrame n) (hi : RootConnected g s st) :
    RootConnected g s {st with top := st.top+1, frames := Function.update st.frames (st.top+1) f} := by
  apply root_connected_transport g s st _ hi
  simp

lemma root_connected_end (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hi : RootConnected g s st) : RootConnected g s (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split <;> exact hi

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootConnectedStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma root_connected_pending (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hparam : ParameterInvariant st) (hnum : NumericalInvariant g st) (hi : RootConnected g s st)
    (hpend : ∀ t v, pendingPush st = some (t,v) → 0 < g.graph.degree v)
    (t : ℕ) (v : Fin n) (hp : pendingPush st = some (t,v)) :
    RootConnected g s (exteriorPush g α st t v) := by
  obtain ⟨ht,hm⟩ := pending_push_member st t v hp
  have hout := (Finset.mem_sdiff.mp ((hreg t ht).2.1 hm)).2
  exact root_connected_exterior g s α hα st hroot hparam hnum hi t v hout (hpend t v hp)

lemma root_connected_drain (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hparam : ParameterInvariant st) (hnum : NumericalInvariant g st) (hi : RootConnected g s st)
    (hpend : ∀ t v, pendingPush st = some (t,v) → 0 < g.graph.degree v) (pc : NormalizePC) :
    RootConnected g s (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact root_connected_PC g s _ pc hi
  · cases hp : pendingPush st with
    | none => exact root_connected_PC g s _ pc hi
    | some p =>
      obtain ⟨t,v⟩ := p
      exact root_connected_pending g s α hα st hreg hroot hparam hnum hi hpend t v hp

set_option maxHeartbeats 1000000 in
lemma root_connected_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hroot : RootIdentity g s α st) (hparam : ParameterInvariant st)
    (hnum : NumericalInvariant g st) (hi : RootConnected g s st)
    (hpend : ∀ t v, pendingPush st = some (t,v) → 0 < g.graph.degree v) :
    RootConnected g s (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]
    exact hi
  simp only [hc,ite_false]
  have hdrain (pc : NormalizePC) := root_connected_drain g s α hα st hreg hroot hparam hnum hi hpend pc
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact root_connected_PC g s _ _ hi
    · split
      · exact hdrain _
      · split <;> exact root_connected_PC g s _ _ hi
  | beginEpisode =>
    simp only [hpc]
    apply root_connected_metadata g s _ (by exact hi) _ _ rfl
  | fullSolve =>
    simp only [hpc]
    split
    · exact root_connected_PC g s _ _ hi
    · split
      · apply root_connected_PC g s _ _
        unfold RootConnected
        exact root_connected_refresh g s _ (touchedBy g (st.frames st.top).active)
          (root_connected_joint g s α st _ hi)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact root_connected_PC g s _ _ hi
    · split
      · exact root_connected_PC g s _ _ hi
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : RootConnected g s up := root_connected_metadata g s u hi st.top _ rfl
        exact root_connected_newFrame g s up c hup
  | leafDrain =>
    simp only [hpc]
    split
    · exact root_connected_PC g s _ _ hi
    · split
      · cases hp : pendingPush st with
        | none => exact root_connected_PC g s _ _ hi
        | some p =>
          obtain ⟨t,v⟩ := p
          exact root_connected_pending g s α hα st hreg hroot hparam hnum hi hpend t v hp
      · split
        · exact root_connected_PC g s _ _ hi
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : RootConnected g s u := root_connected_metadata g s st hi st.top _ rfl
            unfold RootConnected
            exact root_connected_refresh g s _ (touchedBy g C) (root_connected_joint g s α u _ hu)
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact root_connected_PC g s _ _ (root_connected_finish g s _ hi)
    · split
      · exact root_connected_PC g s _ _ (root_connected_finish g s _ hi)
      · exact hdrain _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact root_connected_PC g s _ _ (root_connected_finish g s _ hi)
    · split
      · exact root_connected_PC g s _ _ (root_connected_finish g s _ hi)
      · apply root_connected_metadata g s _ (root_connected_finish g s _ (by exact hi)) _ _ rfl
  | restartDrain =>
    simp only [hpc]
    split
    · exact root_connected_PC g s _ _ hi
    · split
      · exact hdrain _
      · exact root_connected_metadata g s (debit st st.top 1) hi st.top
          (fun fc => {fc with needFull := true, pc := .beginEpisode}) rfl
  | normal =>
    simp only [hpc]
    exact root_connected_end g s α _ hi
  | interrupted =>
    simp only [hpc]
    exact root_connected_end g s α _ hi

lemma root_connected_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    RootConnected g s (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using root_connected_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      root_connected_step m g s α hα ℓ schedule _ (region_run m g s α q ℓ schedule t)
        (root_identity_run m g s α q ℓ schedule t) (parameters_run m g s α q hq ℓ schedule t)
        (numerical_run m g s α q hα hq hs ℓ schedule t) ih
        (fun level v hp => run_pending_positive m g s α q hq.le hs ℓ schedule t level v hp)

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DoublingLog

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma doubling_log_upper (q : ℝ) (hq : 0 < q ∧ q ≤ 1) :
    (Real.log (3/q)-Real.log (3*q/8))/Real.log 2 ≤ 3*Real.log (2/q)/Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlq : Real.log q ≤ 0 := Real.log_nonpos hq.1.le hq.2
  have hq0 : q ≠ 0 := hq.1.ne'
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) hq0,
    Real.log_div (mul_ne_zero (by norm_num : (3 : ℝ) ≠ 0) hq0) (by norm_num : (8 : ℝ) ≠ 0),
    Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hq0,
    Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hq0]
  have hlog8 : Real.log 8=3*Real.log 2 := by
    rw [show (8 : ℝ)=2^3 by norm_num,Real.log_pow]
    norm_num
  rw [hlog8]
  apply div_le_div_of_nonneg_right _ hl2.le
  linarith

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolveCountAlgebra

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma large_doubling_count (κ b N L M : ℝ) (hκ : 0 < κ) (hb : 0 < b)
    (hpaid : b/(64*κ)*M ≤ 6*N*L) : M ≤ 384*κ*N*L/b := by
  have hden : 0 < b/(64*κ) := by positivity
  have hh : M ≤ (6*N*L)/(b/(64*κ)) := (le_div_iff₀ hden).mpr (by nlinarith)
  calc
    _ ≤ _ := hh
    _ = _ := by field_simp; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ProperRoot

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_not_complete_proper (g : InputGraph n) (s : Fin n) (st : RecursiveState n)
    (hconn : RootConnected g s st) (hboundary : BoundaryIdentity g st)
    (hc : ¬componentComplete st) : ∃ v, g.graph.Reachable s v ∧ v ∉ (st.frames 0).active := by
  classical
  let H := (st.frames 0).active
  by_cases hH : H.Nonempty
  · obtain ⟨hsH,hconnected⟩ := hconn hH
    by_contra hn
    have hall : ∀ v, g.graph.Reachable s v → v ∈ H := by
      intro v hr
      by_contra hv
      exact hn ⟨v,hr,hv⟩
    have hclosed (a : Fin n) (ha : a ∈ H) (b : Fin n) (hab : g.graph.Adj a b) : b ∈ H := by
      have hr : g.graph.Reachable s a := by
        obtain ⟨p⟩ := hconnected.preconnected ⟨s,hsH⟩ ⟨a,ha⟩
        exact ⟨p.map (⟨Subtype.val,fun h => h⟩ : g.graph.induce (↑H : Set (Fin n)) →g g.graph)⟩
      exact hall b (hr.trans hab.reachable)
    have hcut : graphCut g H = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      apply Finset.sum_eq_zero
      intro b _
      split
      · rename_i hh
        exact False.elim (hh.2 (hclosed a ha b hh.1))
      · rfl
    apply hc
    refine ⟨hH,?_⟩
    exact hboundary.trans hcut
  · refine ⟨s,⟨.nil⟩,?_⟩
    change s ∉ H
    rw [Finset.not_nonempty_iff_eq_empty.mp hH]
    simp

lemma run_not_complete_proper (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ)
    (hc : ¬componentComplete (recursiveRun m g s α q ℓ schedule t)) :
    ∃ v, g.graph.Reachable s v ∧ v ∉ ((recursiveRun m g s α q ℓ schedule t).frames 0).active := by
  exact root_not_complete_proper g s _ (root_connected_run m g s α q hα hq hs ℓ schedule t)
    (boundary_run m g s α q ℓ schedule t) hc

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FullDoublingCount

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma large_full_doubling_count (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α ≤ 1/2) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (τ : ℕ → ℕ) (hτ : StrictMono τ) (T id : ℕ)
    (hfull : ∀ i ≤ T, fullSolveEvent g (recursiveRun m g s α q ℓ schedule (τ i)) id)
    (E : Finset ℕ) (hE : E ⊆ Finset.range T) :
    let run := recursiveRun m g s α q ℓ schedule
    let st := run (τ 0)
    let j := st.top
    (∀ i ∈ E, ((st.frames j).block : ℝ)/(64*(kappa ℓ 0 : ℝ)) ≤
      (volumeNat g (fullSolveDoubles g α (run (τ i)) j) : ℝ)) →
      (E.card : ℝ) ≤ 384*(kappa ℓ 0 : ℝ)*(st.frames j).N*
        (Real.log (2/q)/Real.log 2)/(st.frames j).block := by
  intro run st j hpaid
  have ha : 0 < α ∧ α < 1 := ⟨hα.1,by linarith [hα.2]⟩
  have hparams := parameters_run m g s α q hq.1 ℓ schedule (τ 0) j le_rfl
  have hb : (0 : ℝ) < (st.frames j).block := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hparams.2.1
  have hspan := full_solve_event_span m g s α q ℓ schedule (τ 0) (τ T) id
    (hτ.monotone (Nat.zero_le _)) (hfull 0 (Nat.zero_le _)) (hfull T le_rfl)
  have hsum := actual_doubling_volume_sum m g s α q hα hq hs ℓ schedule τ hτ T j
    (fun k h0k hkT => (hspan k h0k hkT).1) (by
      intro i hi
      have hh := hfull i hi.le
      have hlevel : (run (τ i)).top=j :=
        (full_events_same_level m g s α q ℓ schedule (τ 0) (τ i) id
          (hτ.monotone (Nat.zero_le _)) (hfull 0 (Nat.zero_le _)) hh).symm
      refine ⟨hlevel,hh.1,hh.2.1,?_,hh.2.2.2.1⟩
      simpa only [run,hlevel] using hh.2.2.1)
    (run_not_complete_proper m g s α q ha hq.1 hs ℓ schedule (τ T) (hfull T le_rfl).2.1)
  have hf := frozenFrame_interval m g s α q ℓ schedule (τ 0) (τ T) j (hτ.monotone (Nat.zero_le _))
    (fun k hk0 hkT => (hspan k hk0 hkT.le).1)
  have hN : ((run (τ T)).frames j).N=(st.frames j).N := congrArg (fun z => z.2.1) hf
  have hlast : (run (τ T)).top=j :=
    (full_events_same_level m g s α q ℓ schedule (τ 0) (τ T) id (hτ.monotone (Nat.zero_le _))
      (hfull 0 (Nat.zero_le _)) (hfull T le_rfl)).symm
  have hvol := full_solve_volume_bound m g s α q ha hq.1 hs ℓ schedule (τ T) id (hfull T le_rfl)
  change (volumeNat g ((run (τ T)).frames (run (τ T)).top).active : ℝ) ≤ _ at hvol
  rw [hlast,hN] at hvol
  have hlog : 0 ≤ Real.log (2/q)/Real.log 2 := div_nonneg
    (Real.log_nonneg ((le_div_iff₀ hq.1).mpr (by linarith [hq.2])))
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hbound : (∑ i ∈ Finset.range T, (volumeNat g (fullSolveDoubles g α (run (τ i)) j) : ℝ)) ≤
      6*(st.frames j).N*(Real.log (2/q)/Real.log 2) := by
    calc
      _ ≤ _ := hsum
      _ ≤ (volumeNat g ((run (τ T)).frames j).active : ℝ)*(3*Real.log (2/q)/Real.log 2) :=
        mul_le_mul_of_nonneg_left (doubling_log_upper q hq) (by positivity)
      _ ≤ (2*(st.frames j).N)*(3*Real.log (2/q)/Real.log 2) :=
        mul_le_mul_of_nonneg_right hvol (by simpa only [mul_div_assoc] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hlog)
      _ = _ := by ring
  apply large_doubling_count (kappa ℓ 0 : ℝ) (st.frames j).block (st.frames j).N
    (Real.log (2/q)/Real.log 2) (E.card : ℝ) (by unfold kappa; positivity) hb
  exact (paid_event_count (fun i => (volumeNat g (fullSolveDoubles g α (run (τ i)) j) : ℝ)) E T
    (((st.frames j).block : ℝ)/(64*(kappa ℓ 0 : ℝ))) hE (fun _ _ => by positivity) hpaid).trans hbound

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation

theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α ≤ 1/2) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (τ : ℕ → ℕ) (hτ : StrictMono τ) (T id : ℕ)
    (hfull : ∀ i ≤ T, fullSolveEvent g (recursiveRun m g s α q ℓ schedule (τ i)) id)
    (E : Finset ℕ) (hE : E ⊆ Finset.range T) :
    let run := recursiveRun m g s α q ℓ schedule
    let st := run (τ 0)
    let j := st.top
    (∀ i ∈ E, ((st.frames j).block : ℝ)/(64*(kappa ℓ 0 : ℝ)) ≤
      (volumeNat g (fullSolveDoubles g α (run (τ i)) j) : ℝ)) →
      (E.card : ℝ) ≤ 384*(kappa ℓ 0 : ℝ)*(st.frames j).N*
        (Real.log (2/q)/Real.log 2)/(st.frames j).block := by
  exact large_full_doubling_count m g s α q hα hq hs ℓ schedule τ hτ T id hfull E hE

