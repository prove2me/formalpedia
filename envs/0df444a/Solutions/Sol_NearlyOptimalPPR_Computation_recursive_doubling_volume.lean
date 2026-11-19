-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_doubling_volume
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:08:39.401961+00:00
-- url     : https://prove2.me/submissions/85c5a7dd-38ab-44ce-ab94-177ef38230b9

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

-- Proof module: Solutions.PrincipalSolves

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma matrix_maximum_principle {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hOff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hRow : ∀ i, 0 < ∑ j, A i j) (x : V → ℝ)
    (hx : ∀ i, 0 ≤ (A *ᵥ x) i) : ∀ i, 0 ≤ x i := by
  intro v
  by_contra hv
  have hv : x v < 0 := lt_of_not_ge hv
  obtain ⟨w, _, hw⟩ := Finset.exists_min_image univ x ⟨v, mem_univ v⟩
  have hwn : x w < 0 := lt_of_le_of_lt (hw v (mem_univ v)) hv
  have hs : ∑ j, A w j * (x j - x w) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    by_cases hj : j = w
    · simp [hj]
    · exact mul_nonpos_of_nonpos_of_nonneg (hOff w j (Ne.symm hj))
        (sub_nonneg.mpr (hw j (mem_univ j)))
  have he : (A *ᵥ x) w = (∑ j, A w j) * x w + ∑ j, A w j * (x j - x w) := by
    simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    ring
  have hn := mul_neg_of_pos_of_neg (hRow w) hwn
  have hp := hx w
  rw [he] at hp
  linarith

lemma matrix_inverse_positive {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hOff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hRow : ∀ i, 0 < ∑ j, A i j) :
    IsUnit A ∧ ∀ b : V → ℝ, (∀ i, 0 ≤ b i) → ∀ i, 0 ≤ (A⁻¹ *ᵥ b) i := by
  have hu : IsUnit A := by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro x y hxy
    have hp := matrix_maximum_principle A hOff hRow (x-y) (by
      rw [mulVec_sub,hxy,sub_self]
      simp)
    have hn := matrix_maximum_principle A hOff hRow (y-x) (by
      rw [mulVec_sub,hxy,sub_self]
      simp)
    ext v
    have := hp v
    have := hn v
    simp only [Pi.sub_apply] at *
    linarith
  refine ⟨hu, ?_⟩
  intro b hb
  apply matrix_maximum_principle A hOff hRow
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), one_mulVec]
  exact hb

lemma principal_signs {n : ℕ} (g : InputGraph n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (T : Finset (Fin n))
    (hT : ∀ v ∈ T, 0 < g.graph.degree v) :
    let A := (LocalPush.Lα g.graph α).submatrix (fun v : T => v.val) (fun v : T => v.val)
    (∀ i j, i ≠ j → A i j ≤ 0) ∧ (∀ i, 0 < ∑ j, A i j) := by
  classical
  let H := g.graph.induce (↑T : Set (Fin n))
  letI : DecidableRel H.Adj := Classical.decRel _
  let A := (LocalPush.Lα g.graph α).submatrix (fun v : T => v.val) (fun v : T => v.val)
  have hdegree (i : T) : H.degree i ≤ g.graph.degree i.val := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    apply Fintype.card_le_of_injective
      (fun u : H.neighborSet i => (⟨u.val.val, u.property⟩ : g.graph.neighborSet i.val))
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : g.graph.neighborSet i.val => w.val) h
  have hA : A = Matrix.diagonal (fun i : T => LocalPush.deg g.graph i.val) -
      (1-α) • H.adjMatrix ℝ := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [A, LocalPush.Lα, LocalPush.degM, LocalPush.adjM, Matrix.submatrix_apply]
    · have hij' : i.val ≠ j.val := fun he => hij (Subtype.ext he)
      simp [A, LocalPush.Lα, LocalPush.degM, LocalPush.adjM,
        Matrix.submatrix_apply, Matrix.diagonal_apply_ne _ hij', Matrix.diagonal_apply_ne _ hij,
        SimpleGraph.adjMatrix_apply]
      simp only [H, SimpleGraph.induce_adj]
  constructor
  · intro i j hij
    have hij' : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    simp only [A, Matrix.submatrix_apply, LocalPush.Lα, Matrix.sub_apply,
      LocalPush.degM, Matrix.diagonal_apply_ne _ hij', LocalPush.adjM,
      Matrix.smul_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply]
    split <;> linarith [hα.2]
  · intro i
    have hr : (∑ j, A i j) = LocalPush.deg g.graph i.val - (1-α) * (H.degree i : ℝ) := by
      calc
        _ = (A *ᵥ (fun _ => (1 : ℝ))) i := by simp [Matrix.mulVec, dotProduct]
        _ = _ := by
          rw [hA, Matrix.sub_mulVec, Matrix.smul_mulVec]
          simp [Matrix.mulVec_diagonal, SimpleGraph.adjMatrix_mulVec_apply]
    rw [hr]
    have hd : (0 : ℝ) < LocalPush.deg g.graph i.val := by
      unfold LocalPush.deg
      exact_mod_cast hT i.val i.property
    have hd' : (H.degree i : ℝ) ≤ LocalPush.deg g.graph i.val := by
      unfold LocalPush.deg
      exact_mod_cast hdegree i
    have hh := mul_le_mul_of_nonneg_left hd' (sub_nonneg.mpr hα.2.le)
    nlinarith [mul_pos hα.1 hd]

lemma principal_inverse_positive {n : ℕ} (g : InputGraph n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (T : Finset (Fin n))
    (hT : ∀ v ∈ T, 0 < g.graph.degree v) :
    IsUnit ((LocalPush.Lα g.graph α).submatrix (fun v : T => v.val) (fun v : T => v.val)) ∧
    ∀ b : T → ℝ, (∀ i, 0 ≤ b i) →
      ∀ i, 0 ≤ (((LocalPush.Lα g.graph α).submatrix (fun v : T => v.val) (fun v : T => v.val))⁻¹ *ᵥ b) i := by
  have hh := principal_signs g α hα T hT
  exact matrix_inverse_positive _ hh.1 hh.2

lemma solveOn_nonneg {n : ℕ} (g : InputGraph n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (T : Finset (Fin n))
    (hT : ∀ v ∈ T, 0 < g.graph.degree v) (b : Fin n → ℝ)
    (hb : ∀ v ∈ T, 0 ≤ b v) : ∀ v, 0 ≤ solveOn g α T b v := by
  intro v
  classical
  unfold solveOn
  split
  · exact (principal_inverse_positive g α hα T hT).2 _ (fun i => hb i.val i.property) _
  · exact le_rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LayerIdentity

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}


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

-- Proof module: Solutions.VirtualReferenceTransport

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma virtualReference_transport (st u : RecursiveState n) (j : ℕ)
    (hq : ∀ i ≤ j, (u.frames i).q = (st.frames i).q)
    (hH : ∀ i ≤ j, (u.frames i).active = (st.frames i).active)
    (href : ∀ i ≤ j, (u.frames i).reference = (st.frames i).reference) :
    virtualReference u j = virtualReference st j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext v
    simp only [virtualReference]
    rw [hH j (by omega),href (j+1) le_rfl,hq j (by omega),
      ih (fun i hi => hq i (by omega)) (fun i hi => hH i (by omega)) (fun i hi => href i (by omega))]

lemma virtualReference_raw (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t j : ℕ) (v : Fin n) (δ : ℝ) :
    virtualReference (rawExterior g α st t v δ) j = virtualReference st j := by
  apply virtualReference_transport st (rawExterior g α st t v δ) j
  · intro i _; exact raw_q g α st t v δ i
  · intro i _; exact raw_active g α st t v δ i
  · intro i _; by_cases he : i ≤ st.top <;> simp [rawExterior,he]

lemma virtualReference_admit (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hvt : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active)
    (hcap : relative st t v = 3*(st.frames t).q/8) :
    ∀ j ≤ st.top, virtualReference (admitStage g st t v) j = virtualReference st j := by
  obtain ⟨htop,hx,hq,hθ,hC,hA,href,hr⟩ := admit_stage_fields g st t v
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hjs : j ≤ st.top := by omega
    funext w
    simp only [virtualReference]
    rw [hA j,hq j,ih hjs]
    by_cases hje : j = t
    · subst j
      simp only [ite_true]
      by_cases hw : w = v
      · subst w
        simp only [Finset.mem_insert_self,ite_true]
        rw [href]
        have htl : t < st.top := by omega
        simp only [htl,true_and,and_self,ite_true]
        simp only [hout,ite_false]
        have hh := (virtual_actual g st t v hvt).1
        unfold virtualPotential at hh
        linarith
      · have hcond : ¬(t < st.top ∧ t+1 = t+1 ∧ w = v) := by simp [hw]
        rw [href]
        simp [Finset.mem_insert,hw]
    · simp only [hje,ite_false]
      rw [href]
      have hcond : ¬(t < st.top ∧ j+1 = t+1 ∧ w = v) := by omega
      simp only [hcond,ite_false]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ReferenceData

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma referenceData_transport (st u : RecursiveState n) (j : ℕ)
    (hq : ∀ i ≤ j, (u.frames i).q = (st.frames i).q)
    (hH : ∀ i ≤ j, (u.frames i).active = (st.frames i).active)
    (href : ∀ i ≤ j, (u.frames i).reference = (st.frames i).reference) :
    referenceData u j = referenceData st j := by
  simp only [referenceData]
  apply Prod.ext
  · change thresholdSum u j = thresholdSum st j
    unfold thresholdSum
    apply Finset.sum_congr rfl
    intro i hi
    exact hq i (Nat.le_of_lt (Finset.mem_range.mp hi))
  · exact virtualReference_transport st u j hq hH href

lemma referenceData_frames (st u : RecursiveState n) (j : ℕ) (hf : u.frames = st.frames) :
    referenceData u j = referenceData st j := by
  apply referenceData_transport
  all_goals intro i _; rw [hf]

lemma referenceData_metadata (st : RecursiveState n) (k j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hq : (f (st.frames k)).q = (st.frames k).q)
    (hH : (f (st.frames k)).active = (st.frames k).active)
    (href : (f (st.frames k)).reference = (st.frames k).reference) :
    referenceData (changeFrame st k f) j = referenceData st j := by
  apply referenceData_transport
  · intro i _; exact observe_changeFrame (fun f => f.q) st k f hq i
  · intro i _; exact observe_changeFrame (fun f => f.active) st k f hH i
  · intro i _; exact observe_changeFrame (fun f => f.reference) st k f href i

lemma referenceData_metadata_trans (st u : RecursiveState n) (k j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hq : (f (u.frames k)).q = (u.frames k).q)
    (hH : (f (u.frames k)).active = (u.frames k).active)
    (href : (f (u.frames k)).reference = (u.frames k).reference)
    (hbase : referenceData u j = referenceData st j) :
    referenceData (changeFrame u k f) j = referenceData st j :=
  (referenceData_metadata u k j f hq hH href).trans hbase

lemma referenceData_episodes (st : RecursiveState n) (episodes : ℕ → ℕ) (j : ℕ) :
    referenceData {st with episodes := episodes} j = referenceData st j :=
  referenceData_frames st {st with episodes := episodes} j rfl
lemma referenceData_fullSolves (st : RecursiveState n) (fullSolves : ℕ → ℕ) (j : ℕ) :
    referenceData {st with fullSolves := fullSolves} j = referenceData st j :=
  referenceData_frames st {st with fullSolves := fullSolves} j rfl

lemma referenceData_PC (st : RecursiveState n) (pc : NormalizePC) (j : ℕ) :
    referenceData (changePC st pc) j = referenceData st j := referenceData_metadata st st.top j _ rfl rfl rfl
lemma referenceData_debit (st : RecursiveState n) (k j : ℕ) (w : ℝ≥0∞) :
    referenceData (debit st k w) j = referenceData st j := referenceData_frames st (debit st k w) j rfl

lemma referenceData_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) (j : ℕ) :
    referenceData (jointUpdate g α st h) j = referenceData st j := by
  apply referenceData_transport
  all_goals intro i _; by_cases hi : i ≤ st.top <;> simp [jointUpdate,hi]

lemma referenceData_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (j : ℕ) :
    referenceData (refreshKeys g st T) j = referenceData st j := by
  apply referenceData_transport
  all_goals intro i _; by_cases hi : i ≤ st.top <;> simp [refreshKeys,hi]

lemma referenceData_finish (st : RecursiveState n) (j : ℕ) :
    referenceData (finishEpisode st) j = referenceData st j := by
  apply referenceData_transport
  all_goals intro i _; by_cases hi : i = st.top <;> simp [finishEpisode,changeFrame,hi]

lemma referenceData_new (st : RecursiveState n) (c : NormalizeFrame n) (j : ℕ) (hj : j ≤ st.top) :
    referenceData {st with top := st.top+1,frames := Function.update st.frames (st.top+1) c} j = referenceData st j := by
  apply referenceData_transport
  all_goals intro i hi; have hn : i ≠ st.top+1 := by omega
  all_goals simp [hn]

lemma referenceData_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ) :
    referenceData (endCall g α st) j = referenceData st j := by
  unfold endCall
  dsimp only
  split <;> apply referenceData_frames <;> rfl

lemma virtualReference_debit (st : RecursiveState n) (k j : ℕ) (w : ℝ≥0∞) :
    virtualReference (debit st k w) j = virtualReference st j := by
  simpa only [referenceData] using congrArg Prod.snd (referenceData_debit st k j w)
lemma virtualReference_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (j : ℕ) :
    virtualReference (refreshKeys g st T) j = virtualReference st j := by
  simpa only [referenceData] using congrArg Prod.snd (referenceData_refresh g st T j)

lemma referenceData_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t j : ℕ) (hj : j ≤ st.top) (v : Fin n) (hvt : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active) :
    referenceData (exteriorPush g α st t v) j = referenceData st j := by
  classical
  simp only [referenceData]
  apply Prod.ext
  · change thresholdSum (exteriorPush g α st t v) j = thresholdSum st j
    unfold thresholdSum
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun z => z.1) (exterior_parameters g α st t v i)
  · let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
        (3*(st.frames t).q/8-relative st t v)
    let base := rawExterior g α st t v δ
    have hA (i : ℕ) := raw_active g α st t v δ i
    have hU := parentDomain_same st base hA
    have hvt' : v ∈ parentDomain base t := by simpa [hU t] using hvt
    have hout' : v ∉ (base.frames t).active := by
      change v ∉ ((rawExterior g α st t v δ).frames t).active
      rw [raw_active]
      exact hout
    have hq := raw_q g α st t v δ t
    rw [exterior_stages,virtualReference_debit,virtualReference_refresh]
    simp only [←show δ = min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v) from rfl]
    by_cases ha : relative st t v+δ = 3*(st.frames t).q/8
    · rw [if_pos ha]
      have hcap : relative base t v = 3*(base.frames t).q/8 := by rw [raw_relative,hq]; simpa using ha
      rw [virtualReference_admit g base t v hvt' hout' hcap j hj]
      exact virtualReference_raw g α st t j v δ
    · rw [if_neg ha]
      exact virtualReference_raw g α st t j v δ

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ReferenceDataStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma referenceData_pending (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hreg : RegionInvariant st)
    (j : ℕ) (hj : j ≤ st.top) (t : ℕ) (v : Fin n) (hp : pendingPush st = some (t,v)) :
    referenceData (exteriorPush g α st t v) j = referenceData st j := by
  obtain ⟨ht,hm⟩ := pending_push_member st t v hp
  obtain ⟨hv,hout⟩ := Finset.mem_sdiff.mp ((hreg t ht).2.1 hm)
  exact referenceData_exterior g α st t j hj v hv hout

lemma referenceData_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hreg : RegionInvariant st)
    (j : ℕ) (hj : j ≤ st.top) (pc : NormalizePC) :
    referenceData (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) j = referenceData st j := by
  split
  · rw [referenceData_PC,referenceData_debit]
  · cases hp : pendingPush st with
    | none => rw [referenceData_PC,referenceData_debit]
    | some p => obtain ⟨t,v⟩ := p; exact referenceData_pending g α st hreg j hj t v hp

set_option maxHeartbeats 1500000 in
lemma referenceData_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hreg : RegionInvariant st)
    (j : ℕ) (hj : j ≤ st.top) :
    referenceData (recursiveStep m g s α ℓ schedule st) j = referenceData st j := by
  classical
  by_cases hd : st.done = true
  · simp only [recursiveStep,hd,ite_true]
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hcomp : componentComplete st
  · simp only [hcomp,ite_true]
    apply referenceData_frames
    rfl
  simp only [hcomp,ite_false]
  have hdrain := referenceData_drain g α st hreg j hj
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · rw [referenceData_PC,referenceData_debit]
    · split
      · exact hdrain _
      · split <;> rw [referenceData_PC,referenceData_debit]
  | beginEpisode =>
    simp only [hpc]
    apply referenceData_metadata_trans st
    · rfl
    · rfl
    · rfl
    · rw [referenceData_episodes,referenceData_debit]
  | fullSolve =>
    simp only [hpc]
    split
    · rw [referenceData_PC,referenceData_debit]
    · split
      · rw [referenceData_PC,referenceData_fullSolves,referenceData_debit,referenceData_refresh,referenceData_joint]
      · exact referenceData_debit st st.top j 1
  | normalize =>
    simp only [hpc]
    split
    · rw [referenceData_PC,referenceData_debit]
    · split
      · rw [referenceData_PC,referenceData_debit]
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild,childrenThisEpisode := fc.childrenThisEpisode+1})
        trans referenceData {up with top := st.top+1,frames := Function.update up.frames (st.top+1) c} j
        · apply referenceData_frames
          rfl
        · have hh : j ≤ up.top := hj
          change referenceData {up with top := up.top+1,frames := Function.update up.frames (up.top+1) c} j = referenceData st j
          rw [referenceData_new up c j hh]
          apply referenceData_metadata_trans st
          · rfl
          · rfl
          · rfl
          · exact referenceData_debit st st.top j _
  | leafDrain =>
    simp only [hpc]
    split
    · rw [referenceData_PC,referenceData_debit]
    · split
      · cases hp : pendingPush st with
        | none => rw [referenceData_PC,referenceData_debit]
        | some p => obtain ⟨t,v⟩ := p; exact referenceData_pending g α st hreg j hj t v hp
      · split
        · rw [referenceData_PC,referenceData_debit]
        · split
          · rw [referenceData_debit,referenceData_refresh,referenceData_joint]
            apply referenceData_metadata
            · rfl
            · rfl
            · rfl
          · exact referenceData_debit st st.top j 1
  | afterChild =>
    simp only [hpc]
    split
    · rw [referenceData_PC,referenceData_finish,referenceData_debit]
    · split
      · rw [referenceData_PC,referenceData_finish,referenceData_debit]
      · exact hdrain _
  | finishEpisode =>
    simp only [hpc]
    split
    · rw [referenceData_PC,referenceData_finish,referenceData_debit]
    · split
      · rw [referenceData_PC,referenceData_finish,referenceData_debit]
      · apply referenceData_metadata_trans st
        · rfl
        · rfl
        · rfl
        · rw [referenceData_finish,referenceData_debit]
  | restartDrain =>
    simp only [hpc]
    split
    · rw [referenceData_PC,referenceData_debit]
    · split
      · exact hdrain _
      · apply referenceData_metadata_trans st
        · rfl
        · rfl
        · rfl
        · exact referenceData_debit st st.top j 1
  | normal => simp only [hpc]; rw [referenceData_end,referenceData_debit]
  | interrupted => simp only [hpc]; rw [referenceData_end,referenceData_debit]

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

-- Proof module: Solutions.ActiveGrowth

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma frame_active_metadata (st : RecursiveState n) (k j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) (hH : (f (st.frames k)).active = (st.frames k).active) :
    ((changeFrame st k f).frames j).active = (st.frames j).active :=
  observe_changeFrame (fun f => f.active) st k f hH j

lemma active_exterior_growth (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t j : ℕ) (v : Fin n) : (st.frames j).active ⊆ ((exteriorPush g α st t v).frames j).active := by
  classical
  rw [exterior_active]
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

lemma active_drain_growth (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ) (pc : NormalizePC) :
    (st.frames j).active ⊆ ((if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc).frames j).active := by
  split
  · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
  · cases hp : pendingPush st with
    | none => simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
    | some p => obtain ⟨t,v⟩ := p; exact active_exterior_growth g α st t j v

set_option maxHeartbeats 1000000 in
lemma active_step_growth (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top) :
    (st.frames j).active ⊆ ((recursiveStep m g s α ℓ schedule st).frames j).active := by
  classical
  have hnew : j ≠ st.top+1 := by omega
  by_cases hd : st.done = true
  · simp [recursiveStep,hd] <;> (try split_ifs) <;> simp_all
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp [hc,completeComponent,debit] <;> (try split_ifs) <;> simp_all
  simp only [hc,ite_false]
  have hdrain := active_drain_growth g α st j
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
    · split
      · exact hdrain _
      · split <;> simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
  | beginEpisode => simp only [hpc]; simp [changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
  | fullSolve =>
    simp only [hpc]
    split
    · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
    · split
      · simp [changePC,changeFrame,Function.update_apply,debit,refreshKeys,jointUpdate] <;> (try split_ifs) <;> simp_all
      · simp [debit] <;> (try split_ifs) <;> simp_all
  | normalize =>
    simp only [hpc]
    split
    · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
    · split
      · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
      · simp [changeFrame,Function.update_apply,debit,hnew] <;> (try split_ifs) <;> simp_all
  | leafDrain =>
    simp only [hpc]
    split
    · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
    · split
      · cases hh : pendingPush st with
        | none => simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
        | some p => obtain ⟨t,v⟩ := p; exact active_exterior_growth g α st t j v
      · split
        · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
        · split
          · simp [debit,refreshKeys,jointUpdate,changeFrame,Function.update_apply] <;> (try split_ifs) <;> simp_all
          · simp [debit] <;> (try split_ifs) <;> simp_all
  | afterChild =>
    simp only [hpc]
    split
    · simp [changePC,changeFrame,Function.update_apply,debit,finishEpisode] <;> (try split_ifs) <;> simp_all
    · split
      · simp [changePC,changeFrame,Function.update_apply,debit,finishEpisode] <;> (try split_ifs) <;> simp_all
      · exact hdrain _
  | finishEpisode =>
    simp only [hpc]
    split
    · simp [changePC,changeFrame,Function.update_apply,debit,finishEpisode] <;> (try split_ifs) <;> simp_all
    · split <;> simp [changePC,changeFrame,Function.update_apply,debit,finishEpisode] <;> (try split_ifs) <;> simp_all
  | restartDrain =>
    simp only [hpc]
    split
    · simp [changePC,changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
    · split
      · exact hdrain _
      · simp [changeFrame,Function.update_apply,debit] <;> (try split_ifs) <;> simp_all
  | normal => simp only [hpc]; simp [endCall,debit] <;> (try split_ifs) <;> simp_all
  | interrupted => simp only [hpc]; simp [endCall,debit] <;> (try split_ifs) <;> simp_all

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

-- Proof module: Solutions.RootMass

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma volume_real (g : InputGraph n) (H : Finset (Fin n)) :
    (volumeNat g H : ℝ) = ∑ v ∈ H, LocalPush.deg g.graph v := by
  simp [volumeNat,LocalPush.deg,neighbor_degree]

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

lemma open_threshold_mono (st : RecursiveState n) (hs : StackInvariant st)
    (hb : BudgetInvariant st) (hp : ParameterInvariant st) (ht : ThresholdRelation st)
    (j : ℕ) (hj : j < st.top) : (st.frames j).q ≤ (st.frames (j+1)).q := by
  have hpc := hs j hj
  have hopen : (st.frames j).openBudget = true := by simpa [hpc,budgetPC] using hb j hj.le
  rw [ht j hj]
  exact (hp j hj.le).2.2 hopen

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VirtualCaps

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma virtual_inactive_cap (g : InputGraph n) (st : RecursiveState n)
    (hnum : NumericalInvariant g st) (hp : ParameterInvariant st) :
    ∀ j ≤ st.top, ∀ v ∉ (st.frames j).active, virtualPotential st j v ≤ 3*(st.frames j).q/8 := by
  intro j
  induction j with
  | zero =>
    intro hj v hv
    have hdom : v ∈ parentDomain st 0 := by simp [parentDomain]
    rw [(virtual_actual g st 0 v hdom).1]
    exact (((hnum 0 hj).1 v hdom).2.2.2 hv).le
  | succ j ih =>
    intro hj v hv
    by_cases hdom : v ∈ parentDomain st (j+1)
    · rw [(virtual_actual g st (j+1) v hdom).1]
      exact (((hnum (j+1) hj).1 v hdom).2.2.2 hv).le
    · have hout : v ∉ (st.frames j).active := by simpa [parentDomain] using hdom
      have hh := ih (by omega) v hout
      have hq := (hp (j+1) hj).1.le
      unfold virtualPotential virtualReference
      simp only [hout,ite_false]
      unfold virtualPotential at hh
      linarith

lemma virtual_active_floor (g : InputGraph n) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hnum : NumericalInvariant g st)
    (j : ℕ) (hj : j ≤ st.top) (v : Fin n) (hv : v ∈ (st.frames j).active) :
    3*(st.frames j).q/8 ≤ virtualPotential st j v := by
  rw [(virtual_actual g st j v ((hreg j hj).1 hv)).1]
  exact ((hnum j hj).1 v ((hreg j hj).1 hv)).2.2.1 hv

lemma virtualReference_child_max (g : InputGraph n) (st u : RecursiveState n)
    (hreg : RegionInvariant st) (hnum : NumericalInvariant g st) (hp : ParameterInvariant st)
    (j : ℕ) (hj : j ≤ st.top)
    (hξ : virtualReference u j = virtualReference st j)
    (hq : (u.frames j).q = (st.frames j).q)
    (hH : (u.frames j).active = (st.frames j).active)
    (href : (u.frames (j+1)).reference = st.x) :
    virtualReference u (j+1) = fun v => max (st.x v) (virtualReference st j v+3*(st.frames j).q/8) := by
  funext v
  simp only [virtualReference]
  rw [hξ,hq,hH,href]
  by_cases hv : v ∈ (st.frames j).active
  · simp only [hv,ite_true]
    apply (max_eq_left _).symm
    have hh := virtual_active_floor g st hreg hnum j hj v hv
    unfold virtualPotential at hh
    linarith
  · simp only [hv,ite_false]
    apply (max_eq_right _).symm
    have hh := virtual_inactive_cap g st hnum hp j hj v hv
    unfold virtualPotential at hh
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

-- Proof module: Solutions.ReferenceNonnegative

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
lemma reference_nonnegative_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hnum : NumericalInvariant g st)
    (hp : ParameterInvariant st) (hi : ReferenceNonnegative st) :
    ReferenceNonnegative (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hle : (recursiveStep m g s α ℓ schedule st).top ≤ st.top
  · intro j hj v
    have hh : virtualReference (recursiveStep m g s α ℓ schedule st) j = virtualReference st j :=
      congrArg Prod.snd (referenceData_step m g s α ℓ schedule st hreg j (hj.trans hle))
    rw [hh]
    exact hi j (hj.trans hle) v
  · have hg : st.top < (recursiveStep m g s α ℓ schedule st).top := Nat.lt_of_not_ge hle
    obtain ⟨hd,hcomp,hpc,hex,hlevel⟩ := growing_step_guards m g s α ℓ schedule st hg
    let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
      (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
    let pre := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
      8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
    let up := changeFrame pre st.top (fun f => {f with pc := .afterChild,childrenThisEpisode := f.childrenThisEpisode+1})
    let next : RecursiveState n :=
      { up with
        top := st.top+1
        nextId := st.nextId+1
        frames := Function.update up.frames (st.top+1) c
        information := Function.update up.information c.id (some ⟨st.top+1,(st.frames st.top).block,c.block⟩) }
    have hnext : recursiveStep m g s α ℓ schedule st = next := by
      simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hcomp,hpc,hex,hlevel]
      rfl
    have hdata (j : ℕ) (hj : j ≤ st.top) : referenceData next j = referenceData st j := by
      rw [←hnext]
      exact referenceData_step m g s α ℓ schedule st hreg j hj
    have hξ : virtualReference next st.top = virtualReference st st.top := congrArg Prod.snd (hdata st.top le_rfl)
    have hS : thresholdSum next st.top = thresholdSum st st.top := congrArg Prod.fst (hdata st.top le_rfl)
    have hq : (next.frames st.top).q = (st.frames st.top).q := by
      simp [next,up,pre,changeFrame,debit]
    have hH : (next.frames st.top).active = (st.frames st.top).active := by
      simp [next,up,pre,changeFrame,debit]
    have href : (next.frames (st.top+1)).reference = st.x := by simp [next,c,freshFrame]
    have hsum : thresholdSum next (st.top+1) = thresholdSum st st.top+(st.frames st.top).q := by
      have hh : thresholdSum next (st.top+1) = thresholdSum next st.top+(next.frames st.top).q := by
        simp [thresholdSum,Finset.sum_range_succ]
      rw [hh,hS,hq]
    rw [hnext]
    intro j hj v
    by_cases hjs : j ≤ st.top
    · have hSj : thresholdSum next j = thresholdSum st j := congrArg Prod.fst (hdata j hjs)
      have hξj : virtualReference next j = virtualReference st j := congrArg Prod.snd (hdata j hjs)
      rw [hξj]
      exact hi j hjs v
    · have hje : j = st.top+1 := by change j ≤ st.top+1 at hj; omega
      subst j
      rw [virtualReference_child_max g st next hreg hnum hp st.top le_rfl hξ hq hH href]
      have hx := ((hnum 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).2.1
      have hx0 : 0 ≤ st.x v := by simpa [relative] using hx
      exact hx0.trans (le_max_left _ _)

lemma reference_nonnegative_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ReferenceNonnegative (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero =>
    intro j hj v
    have hj0 : j = 0 := by change j ≤ 0 at hj; omega
    subst j
    simp [virtualReference]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      reference_nonnegative_step m g s α ℓ schedule _ (region_run m g s α q ℓ schedule t)
        (numerical_run m g s α q hα hq hs ℓ schedule t) (parameters_run m g s α q hq ℓ schedule t) ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SharedMonotone

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma exterior_x (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    (exteriorPush g α st t v).x = Function.update st.x v (st.x v+
      min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
        (3*(st.frames t).q/8-relative st t v)) := by
  classical
  simp only [exteriorPush]
  split_ifs <;> rfl

lemma exterior_x_mono (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hp : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (t : ℕ) (ht : t ≤ st.top) (v : Fin n) (hvt : v ∈ parentDomain st t)
    (hout : v ∉ (st.frames t).active) (hd : 0 < g.graph.degree v) :
    st.x ≤ (exteriorPush g α st t v).x := by
  have hd' : 0 < LocalPush.deg g.graph v := by unfold LocalPush.deg; exact_mod_cast hd
  have hn := (hnum t ht).1 v hvt
  have hh := (crossing_push_bounds (LocalPush.deg g.graph v) (st.frames t).q
    ((st.frames t).residual v) (relative st t v) hd' (hp t ht).1 hn.1
    ⟨hn.2.1,(hn.2.2.2 hout).le⟩).1
  rw [exterior_x]
  intro w
  by_cases hw : w = v
  · subst w; simp only [Function.update_self]; linarith
  · simp [Function.update_of_ne hw]

lemma pending_x_mono (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hp : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st)
    (t : ℕ) (v : Fin n) (hpend : pendingPush st = some (t,v)) :
    st.x ≤ (exteriorPush g α st t v).x := by
  obtain ⟨ht,hm⟩ := pending_push_member st t v hpend
  obtain ⟨hv,hout⟩ := Finset.mem_sdiff.mp ((hreg t ht).2.1 hm)
  exact exterior_x_mono g α st hreg hp hnum t ht v hv hout
    (isolate_pending_positive g st hiso hkeys t v hpend)

lemma full_increment_nonnegative (g : InputGraph n) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hnum : NumericalInvariant g st)
    (hpos : ∀ v ∈ (st.frames st.top).active, 0 < g.graph.degree v) :
    ∀ v, 0 ≤ solveOn g α (st.frames st.top).active (st.frames st.top).residual v := by
  apply solveOn_nonneg g α hα _ hpos
  intro v hv
  exact ((hnum st.top le_rfl).1 v ((hreg st.top le_rfl).1 hv)).1

lemma cached_increment_nonnegative (g : InputGraph n) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (st : RecursiveState n) (hnum : NumericalInvariant g st) (hkeys : KeysInvariant g st)
    (hp : ParameterInvariant st) (hb : (st.frames st.top).openBudget = true)
    (hpos : ∀ v ∈ (st.frames st.top).cache ∪ (st.frames st.top).high, 0 < g.graph.degree v) :
    ∀ v, 0 ≤ solveOn g α ((st.frames st.top).cache ∪ (st.frames st.top).high)
      (fun v => (st.frames st.top).residual v-(st.frames st.top).theta*LocalPush.deg g.graph v) v := by
  apply solveOn_nonneg g α hα _ hpos
  intro v hv
  apply sub_nonneg.mpr
  obtain hv|hv := Finset.mem_union.mp hv
  · exact (hnum st.top le_rfl).2 v hv
  · have hh := ((hkeys st.top le_rfl).2 v).mp hv
    have hd : 0 ≤ (st.frames st.top).theta*LocalPush.deg g.graph v := by
      apply mul_nonneg (((hp st.top le_rfl).1.trans_le ((hp st.top le_rfl).2.2 hb)).le)
      unfold LocalPush.deg; positivity
    nlinarith [hh.2]

lemma drain_x_mono (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hp : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st) (pc : NormalizePC) :
    st.x ≤ (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc).x := by
  split
  · exact le_rfl
  · cases hh : pendingPush st with
    | none => exact le_rfl
    | some p => obtain ⟨t,v⟩ := p; exact pending_x_mono g α st hreg hp hnum hkeys hiso t v hh

set_option maxHeartbeats 1000000 in
lemma shared_x_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hp : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st) (hbudget : BudgetInvariant st) :
    st.x ≤ (recursiveStep m g s α ℓ schedule st).x := by
  classical
  by_cases hd : st.done = true
  · simp only [recursiveStep,hd,ite_true]; exact le_rfl
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hcomp : componentComplete st
  · simp only [hcomp,ite_true]; exact le_rfl
  simp only [hcomp,ite_false]
  have hdrain := drain_x_mono g α st hreg hp hnum hkeys hiso
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact le_rfl
    · split
      · exact hdrain _
      · split <;> exact le_rfl
  | beginEpisode => simp only [hpc]; exact le_rfl
  | fullSolve =>
    simp only [hpc]
    split
    · exact le_rfl
    · split
      · rename_i hvalid
        have hn := full_increment_nonnegative g α hα st hreg hnum hvalid.2
        intro v
        exact le_add_of_nonneg_right (hn v)
      · exact le_rfl
  | normalize =>
    simp only [hpc]
    split
    · exact le_rfl
    · split <;> exact le_rfl
  | leafDrain =>
    simp only [hpc]
    split
    · exact le_rfl
    · split
      · cases hh : pendingPush st with
        | none => exact le_rfl
        | some p => obtain ⟨t,v⟩ := p; exact pending_x_mono g α st hreg hp hnum hkeys hiso t v hh
      · split
        · exact le_rfl
        · split
          · rename_i hvalid
            have hb : (st.frames st.top).openBudget = true := by
              simpa [hpc,budgetPC] using hbudget st.top le_rfl
            have hn := cached_increment_nonnegative g α hα st hnum hkeys hp hb hvalid.2
            intro v
            exact le_add_of_nonneg_right (hn v)
          · exact le_rfl
  | afterChild =>
    simp only [hpc]
    split
    · exact le_rfl
    · split
      · exact le_rfl
      · exact hdrain _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact le_rfl
    · split <;> exact le_rfl
  | restartDrain =>
    simp only [hpc]
    split
    · exact le_rfl
    · split
      · exact hdrain _
      · exact le_rfl
  | normal => simp only [hpc]; simp only [endCall]; split <;> exact le_rfl
  | interrupted => simp only [hpc]; simp only [endCall]; split <;> exact le_rfl

lemma shared_x_run_monotone (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) :
    Monotone (fun t => (recursiveRun m g s α q ℓ schedule t).x) := by
  apply monotone_nat_of_le_succ
  intro t
  simpa only [recursiveRun,Function.iterate_succ_apply'] using shared_x_step m g s α hα ℓ schedule _
    (region_run m g s α q ℓ schedule t) (parameters_run m g s α q hq ℓ schedule t)
    (numerical_run m g s α q hα hq hs ℓ schedule t) (keys_run m g s α q hq.le ℓ schedule t)
    (isolate_run m g s α q hs ℓ schedule t) (budget_run m g s α q ℓ schedule t)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SnapshotIntervals

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma referenceData_interval (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top) :
    referenceData (recursiveRun m g s α q ℓ schedule b) j =
      referenceData (recursiveRun m g s α q ℓ schedule a) j := by
  have aux : ∀ d, a+d ≤ b → referenceData (recursiveRun m g s α q ℓ schedule (a+d)) j =
      referenceData (recursiveRun m g s α q ℓ schedule a) j := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have hstep := referenceData_step m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+d))
        (region_run m g s α q ℓ schedule (a+d)) j (hopen (a+d) (by omega) (by omega))
      have heq : recursiveRun m g s α q ℓ schedule (a+(d+1)) =
          recursiveStep m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+d)) := by
        rw [show a+(d+1) = (a+d)+1 by omega]
        simp only [recursiveRun,Function.iterate_succ_apply']
      rw [heq,hstep]
      exact ih (by omega)
  simpa [Nat.add_sub_of_le hab] using aux (b-a) (by omega)

lemma active_interval_growth (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top) :
    ((recursiveRun m g s α q ℓ schedule a).frames j).active ⊆
      ((recursiveRun m g s α q ℓ schedule b).frames j).active := by
  have aux : ∀ d, a+d ≤ b → ((recursiveRun m g s α q ℓ schedule a).frames j).active ⊆
      ((recursiveRun m g s α q ℓ schedule (a+d)).frames j).active := by
    intro d
    induction d with
    | zero => intro _; exact Finset.Subset.refl _
    | succ d ih =>
      intro hd
      have hstep := active_step_growth m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+d))
        j (hopen (a+d) (by omega) (by omega))
      have heq : recursiveRun m g s α q ℓ schedule (a+(d+1)) =
          recursiveStep m g s α ℓ schedule (recursiveRun m g s α q ℓ schedule (a+d)) := by
        rw [show a+(d+1) = (a+d)+1 by omega]
        simp only [recursiveRun,Function.iterate_succ_apply']
      rw [heq]
      exact (ih (by omega)).trans hstep
  simpa [Nat.add_sub_of_le hab] using aux (b-a) (by omega)

lemma virtualPotential_interval_mono (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b j : ℕ) (hab : a ≤ b)
    (hopen : ∀ k, a ≤ k → k < b → j ≤ (recursiveRun m g s α q ℓ schedule k).top) :
    virtualPotential (recursiveRun m g s α q ℓ schedule a) j ≤
      virtualPotential (recursiveRun m g s α q ℓ schedule b) j := by
  have href : virtualReference (recursiveRun m g s α q ℓ schedule b) j =
      virtualReference (recursiveRun m g s α q ℓ schedule a) j :=
    congrArg Prod.snd (referenceData_interval m g s α q ℓ schedule a b j hab hopen)
  have hx := shared_x_run_monotone m g s α q hα hq hs ℓ schedule hab
  intro v
  unfold virtualPotential
  rw [href]
  exact sub_le_sub_right (hx v) _

lemma virtualPotential_le_shared (st : RecursiveState n) (hi : ReferenceNonnegative st)
    (j : ℕ) (hj : j ≤ st.top) (v : Fin n) : virtualPotential st j v ≤ st.x v :=
  sub_le_self _ (hi j hj v)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.VirtualBounds

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma threshold_le_current (st : RecursiveState n) (hmono : ∀ j < st.top, (st.frames j).q ≤ (st.frames (j+1)).q)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ st.top) : (st.frames i).q ≤ (st.frames j).q := by
  induction j with
  | zero =>
    have hi : i=0 := by omega
    subst i
    exact le_rfl
  | succ j ih =>
    by_cases he : i = j+1
    · subst i; exact le_rfl
    · exact (ih (by omega) (by omega)).trans (hmono j (by omega))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FullSolveSnapshots

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma full_solve_run_x (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    st.done = false → ¬componentComplete st → (st.frames st.top).pc = .fullSolve →
      ¬anyExhausted st → (recursiveRun m g s α q ℓ schedule (t+1)).x =
        st.x+solveOn g α (st.frames st.top).active (st.frames st.top).residual := by
  intro st hd hc hpc he
  have hv : (st.frames st.top).active ⊆ st.stored ∧ ∀ v ∈ (st.frames st.top).active, 0 < g.graph.degree v :=
    run_active_domain_valid m g s α q hq hs ℓ schedule t _ le_rfl
  have hh : recursiveRun m g s α q ℓ schedule (t+1) = recursiveStep m g s α ℓ schedule st := by
    simp only [st,recursiveRun,Function.iterate_succ_apply']
  rw [hh]
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hc,hpc,he]
  split
  · rfl
  · rename_i hno
    exact False.elim (hno hv)

lemma full_solve_run_doubling (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    let j := st.top
    let h := solveOn g α (st.frames j).active (st.frames j).residual
    st.done = false → ¬componentComplete st → (st.frames j).pc = .fullSolve →
      ¬anyExhausted st → ∀ v ∈ doubledSet (st.frames j).active h (virtualPotential st j),
        2*virtualPotential st j v ≤ virtualPotential (recursiveRun m g s α q ℓ schedule (t+1)) j v := by
  intro st j h hd hc hpc he v hv
  have hx := full_solve_run_x m g s α q hq hs ℓ schedule t hd hc hpc he
  have href : virtualReference (recursiveRun m g s α q ℓ schedule (t+1)) j = virtualReference st j := by
    have hh := referenceData_step m g s α ℓ schedule st (region_run m g s α q ℓ schedule t) j le_rfl
    simpa only [referenceData,st,recursiveRun,Function.iterate_succ_apply'] using congrArg Prod.snd hh
  have hv' : virtualPotential st j v < h v := (Finset.mem_filter.mp hv).2
  unfold virtualPotential at hv' ⊢
  rw [hx,href]
  simp only [Pi.add_apply]
  change 2*(st.x v-virtualReference st j v) ≤ st.x v+h v-virtualReference st j v
  linarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DoublingCounts

set_option autoImplicit false
open Finset
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma hitCount_succ (D : ℕ → Finset ι) (v : ι) (T : ℕ) :
    hitCount D v (T+1) = hitCount D v T+if v ∈ D T then 1 else 0 := by
  classical
  by_cases hv : v ∈ D T <;> simp [hitCount,Finset.range_add_one,Finset.filter_insert,hv]

lemma iterated_doubling (D : ℕ → Finset ι) (y : ℕ → ι → ℝ) (l : ℝ)
    (hinit : ∀ v, l ≤ y 0 v)
    (hmono : ∀ k v, y k v ≤ y (k+1) v)
    (hdouble : ∀ k v, v ∈ D k → 2*y k v ≤ y (k+1) v) :
    ∀ T v, (2 : ℝ)^hitCount D v T*l ≤ y T v := by
  intro T
  induction T with
  | zero => intro v; simpa [hitCount] using hinit v
  | succ T ih =>
    intro v
    rw [hitCount_succ]
    by_cases hv : v ∈ D T
    · rw [if_pos hv,pow_succ]
      have hh := hdouble T v hv
      nlinarith [ih v]
    · rw [if_neg hv,add_zero]
      exact (ih v).trans (hmono T v)

lemma doubling_log_bound (D : ℕ → Finset ι) (y : ℕ → ι → ℝ) (l U : ℝ)
    (hl : 0 < l) (hinit : ∀ v, l ≤ y 0 v)
    (hmono : ∀ k v, y k v ≤ y (k+1) v)
    (hdouble : ∀ k v, v ∈ D k → 2*y k v ≤ y (k+1) v)
    (T : ℕ) (hupper : ∀ v, y T v ≤ U) (v : ι) :
    (hitCount D v T : ℝ) ≤ (Real.log U-Real.log l)/Real.log 2 := by
  have hh := (iterated_doubling D y l hinit hmono hdouble T v).trans (hupper v)
  have hp : 0 < (2 : ℝ)^hitCount D v T*l := by positivity
  have hlog := Real.log_le_log hp hh
  rw [Real.log_mul (by positivity) hl.ne',Real.log_pow] at hlog
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  linarith

lemma weighted_hit_identity (D : ℕ → Finset ι) (w : ι → ℝ) (T : ℕ) :
    (∑ k ∈ Finset.range T, ∑ v ∈ D k, w v) = ∑ v, w v*(hitCount D v T : ℝ) := by
  classical
  induction T with
  | zero => simp [hitCount]
  | succ T ih =>
    rw [Finset.sum_range_succ,ih]
    simp_rw [hitCount_succ,Nat.cast_add,mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero,mul_ite,mul_one,mul_zero]
    simp

lemma weighted_doubling_bound (D : ℕ → Finset ι) (y : ℕ → ι → ℝ) (w : ι → ℝ) (l U : ℝ)
    (hw : ∀ v, 0 ≤ w v) (hl : 0 < l) (hinit : ∀ v, l ≤ y 0 v)
    (hmono : ∀ k v, y k v ≤ y (k+1) v)
    (hdouble : ∀ k v, v ∈ D k → 2*y k v ≤ y (k+1) v)
    (T : ℕ) (hupper : ∀ v, y T v ≤ U) :
    (∑ k ∈ Finset.range T, ∑ v ∈ D k, w v) ≤
      (∑ v, w v)*((Real.log U-Real.log l)/Real.log 2) := by
  rw [weighted_hit_identity,Finset.sum_mul]
  exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left
    (doubling_log_bound D y l U hl hinit hmono hdouble T hupper v) (hw v))

lemma weighted_active_doubling_bound (D : ℕ → Finset ι) (y : ℕ → ι → ℝ) (w : ι → ℝ) (l U : ℝ)
    (hw : ∀ v, 0 ≤ w v) (hl : 0 < l) (hLU : l ≤ U)
    (hmono : ∀ k v, y k v ≤ y (k+1) v)
    (hdouble : ∀ k v, v ∈ D k → l ≤ y k v ∧ 2*y k v ≤ y (k+1) v)
    (T : ℕ) (hupper : ∀ v, y T v ≤ U) :
    (∑ k ∈ Finset.range T, ∑ v ∈ D k, w v) ≤
      (∑ v, w v)*((Real.log U-Real.log l)/Real.log 2) := by
  apply weighted_doubling_bound D (fun k v => max (y k v) l) w l U hw hl
  · intro v; exact le_max_right _ _
  · intro k v; exact max_le_max_right l (hmono k v)
  · intro k v hv
    rw [max_eq_left (hdouble k v hv).1]
    exact (hdouble k v hv).2.trans (le_max_left _ _)
  · intro v; exact max_le (hupper v) hLU

lemma weighted_active_doubling_bound_finite (D : ℕ → Finset ι) (y : ℕ → ι → ℝ)
    (w : ι → ℝ) (l U : ℝ) (T : ℕ) (hw : ∀ v, 0 ≤ w v) (hl : 0 < l) (hLU : l ≤ U)
    (hmono : ∀ k < T, ∀ v, y k v ≤ y (k+1) v)
    (hdouble : ∀ k < T, ∀ v ∈ D k, l ≤ y k v ∧ 2*y k v ≤ y (k+1) v)
    (hupper : ∀ v, y T v ≤ U) :
    (∑ k ∈ Finset.range T, ∑ v ∈ D k, w v) ≤
      (∑ v, w v)*((Real.log U-Real.log l)/Real.log 2) := by
  classical
  let E := fun k => if k < T then D k else ∅
  let z := fun k v => y (min k T) v
  have hm : ∀ k v, z k v ≤ z (k+1) v := by
    intro k v
    by_cases hk : k < T
    · simpa [z,Nat.min_eq_left hk.le,Nat.min_eq_left (show k+1 ≤ T by omega)] using hmono k hk v
    · simp [z,Nat.min_eq_right (by omega : T ≤ k),Nat.min_eq_right (by omega : T ≤ k+1)]
  have hd : ∀ k v, v ∈ E k → l ≤ z k v ∧ 2*z k v ≤ z (k+1) v := by
    intro k v hv
    by_cases hk : k < T
    · have hv' : v ∈ D k := by simpa [E,hk] using hv
      simpa [z,Nat.min_eq_left hk.le,Nat.min_eq_left (show k+1 ≤ T by omega)] using hdouble k hk v hv'
    · simp [E,hk] at hv
  have hh := weighted_active_doubling_bound E z w l U hw hl hLU hm hd T (by simpa [z] using hupper)
  have hs : (∑ k ∈ Finset.range T, ∑ v ∈ E k, w v) = ∑ k ∈ Finset.range T, ∑ v ∈ D k, w v := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [E,Finset.mem_range.mp hk]
  rw [hs] at hh
  exact hh

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ActualDoublingCounts

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_threshold_le_open (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (t j : ℕ)
    (hj : j ≤ (recursiveRun m g s α q ℓ schedule t).top) :
    q ≤ ((recursiveRun m g s α q ℓ schedule t).frames j).q := by
  let st := recursiveRun m g s α q ℓ schedule t
  have hp := parameters_run m g s α q hq ℓ schedule t
  have hm := open_threshold_mono st (stack_run m g s α q ℓ schedule t)
    (budget_run m g s α q ℓ schedule t) hp (threshold_relation_run m g s α q ℓ schedule t)
  have hh := threshold_le_current st hm 0 j (Nat.zero_le _) hj
  rw [root_threshold_run m g s α q ℓ schedule t] at hh
  exact hh

set_option maxHeartbeats 1500000 in
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
  classical
  intro run F hopen hfull hproper
  have ha : 0 < α ∧ α < 1 := ⟨hα.1,by linarith [hα.2]⟩
  let D := fun k => fullSolveDoubles g α (run (τ k)) j
  let y := fun k => virtualPotential (run (τ k)) j
  let w := fun v => if v ∈ F then LocalPush.deg g.graph v else 0
  have ht0 (k : ℕ) : τ 0 ≤ τ k := hτ.monotone (Nat.zero_le _)
  have htT (k : ℕ) (hk : k ≤ T) : τ k ≤ τ T := hτ.monotone hk
  have hD (k : ℕ) (hk : k < T) : D k ⊆ F := by
    have hh := active_interval_growth m g s α q ℓ schedule (τ k) (τ T) j (htT k hk.le)
      (fun t hkt ht => hopen t ((ht0 k).trans hkt) ht.le)
    exact (Finset.filter_subset _ _).trans hh
  have hw (v : Fin n) : 0 ≤ w v := by
    dsimp only [w]
    split
    · unfold LocalPush.deg; positivity
    · exact le_rfl
  have hmono (k : ℕ) (hk : k < T) (v : Fin n) : y k v ≤ y (k+1) v := by
    exact virtualPotential_interval_mono m g s α q ha hq.1 hs ℓ schedule (τ k) (τ (k+1)) j
      (hτ.monotone (Nat.le_succ _)) (fun t hkt ht =>
        hopen t ((ht0 k).trans hkt) (ht.le.trans (htT (k+1) (by omega)))) v
  have hdouble (k : ℕ) (hk : k < T) (v : Fin n) (hv : v ∈ D k) :
      3*q/8 ≤ y k v ∧ 2*y k v ≤ y (k+1) v := by
    obtain ⟨hj,hd,hc,hpc,he⟩ := hfull k hk
    have hj' : (recursiveRun m g s α q ℓ schedule (τ k)).top = j := hj
    have hnum := numerical_run m g s α q ha hq.1 hs ℓ schedule (τ k)
    have hreg := region_run m g s α q ℓ schedule (τ k)
    have hqj := root_threshold_le_open m g s α q hq.1 ℓ schedule (τ k) j (by rw [hj])
    have hvH : v ∈ ((run (τ k)).frames j).active := (Finset.mem_filter.mp hv).1
    have hfloor := virtual_active_floor g (run (τ k)) hreg hnum j (by rw [hj]) v hvH
    have hdoub := full_solve_run_doubling m g s α q hq.1.le hs ℓ schedule (τ k) hd hc
      (by simpa only [run,hj'] using hpc) he v (by simpa only [D,fullSolveDoubles,run,hj'] using hv)
    have hafter : virtualPotential (run (τ k+1)) j v ≤ y (k+1) v :=
      virtualPotential_interval_mono m g s α q ha hq.1 hs ℓ schedule (τ k+1) (τ (k+1)) j
        (Nat.succ_le_of_lt (hτ (Nat.lt_succ_self k)))
        (fun t hkt ht => hopen t ((ht0 k).trans (by omega)) (ht.le.trans (htT (k+1) (by omega)))) v
    constructor
    · dsimp only [y]
      linarith
    · have hh : 2*y k v ≤ virtualPotential (run (τ k+1)) j v := by simpa only [y,run,hj'] using hdoub
      exact hh.trans hafter
  have hupper (v : Fin n) : y T v ≤ 3/q := by
    exact (virtualPotential_le_shared (run (τ T))
      (reference_nonnegative_run m g s α q ha hq.1 hs ℓ schedule (τ T)) j
      (hopen (τ T) (ht0 T) le_rfl) v).trans
      (run_proper_potential_bound m g s α q hα hq hs ℓ schedule (τ T) hproper v)
  have hLU : 3*q/8 ≤ 3/q := by
    have hh : q*q ≤ 1 := by nlinarith [hq.2]
    apply (le_div_iff₀ hq.1).mpr
    nlinarith
  have hq0 : 0 < q := hq.1
  have hh := weighted_active_doubling_bound_finite D y w (3*q/8) (3/q) T hw (by positivity) hLU hmono hdouble hupper
  have hleft : (∑ k ∈ Finset.range T, ∑ v ∈ D k, w v) =
      ∑ k ∈ Finset.range T, (volumeNat g (D k) : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [volume_real]
    apply Finset.sum_congr rfl
    intro v hv
    exact if_pos (hD k (Finset.mem_range.mp hk) hv)
  have hright : (∑ v, w v) = (volumeNat g F : ℝ) := by
    rw [volume_real]
    simp [w]
  rw [hleft,hright] at hh
  exact hh

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation

theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
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
  exact actual_doubling_volume_sum m g s α q hα hq hs ℓ schedule τ hτ T j

