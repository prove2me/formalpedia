-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_cached_solve_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:02:50.917407+00:00
-- url     : https://prove2.me/submissions/806e90f8-db3d-422a-9b2d-9b1111c3fc47

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_budget_energy
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_episode_count
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_running_call_production
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

abbrev cache_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_control_parameters m n g s α q ℓ schedule t).2.2.1

abbrev parameters_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_control_parameters m n g s α q ℓ schedule t).2.2.2 hq

abbrev keys_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_queue_domains m n g s α q ℓ schedule t).1 hq

abbrev isolate_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  (recursive_queue_domains m n g s α q ℓ schedule t).2.1 hs

abbrev numerical_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  recursive_numerical_invariants m n g s α q hα hq hs ℓ schedule t

abbrev budget_energy_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :=
  recursive_budget_energy m n g s α q hα hq hs ℓ schedule t

abbrev uniform_episode_count :=
  recursive_episode_count

abbrev unexhausted_call_production_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a ≤ b)
    (hda : (recursiveRun m g s α q ℓ schedule a).done=false)
    (hida : ((recursiveRun m g s α q ℓ schedule a).frames (recursiveRun m g s α q ℓ schedule a).top).id=id)
    (hdb : (recursiveRun m g s α q ℓ schedule b).done=false)
    (hidb : ((recursiveRun m g s α q ℓ schedule b).frames (recursiveRun m g s α q ℓ schedule b).top).id=id)
    (hexb : ¬anyExhausted (recursiveRun m g s α q ℓ schedule b)) :=
  recursive_running_call_production m n g s α q hα hq.1 hs ℓ schedule a b id hab hda hida hdb hidb hexb

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

lemma mulVec_extend_subtype {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (T : Finset V) (x : T → ℝ) (i : T) :
    (M *ᵥ (fun v => if h : v ∈ T then x ⟨v,h⟩ else 0)) i.val =
      (M.submatrix (fun v : T => v.val) (fun v : T => v.val) *ᵥ x) i := by
  classical
  let xe : V → ℝ := fun v => if h : v ∈ T then x ⟨v,h⟩ else 0
  have he : (fun j : T => M i.val j.val * xe j.val) =
      (fun j : T => M i.val j.val * x j) := by
    ext j
    simp only [xe, dif_pos j.property]
  change (∑ j, M i.val j * xe j) = ∑ j : T, M i.val j.val * x j
  calc
    _ = ∑ j ∈ T, M i.val j * xe j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ T)
      intro j _ hj
      simp [xe, hj]
    _ = ∑ j : T, M i.val j.val * xe j.val :=
      (Finset.sum_coe_sort T (fun j : V => M i.val j * xe j)).symm
    _ = _ := congrArg (fun f : T → ℝ => ∑ j, f j) he

lemma solveOn_exact {n : ℕ} (g : InputGraph n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (T : Finset (Fin n))
    (hT : ∀ v ∈ T, 0 < g.graph.degree v) (b : Fin n → ℝ) :
    ∀ v ∈ T, (LocalPush.Lα g.graph α *ᵥ solveOn g α T b) v = b v := by
  classical
  intro v hv
  let i : T := ⟨v,hv⟩
  unfold solveOn
  have hm := (principal_inverse_positive g α hα T hT).1
  rw [show v = i.val from rfl, mulVec_extend_subtype, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hm), Matrix.one_mulVec]

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

lemma card_le_volume (g : InputGraph n) (H : Finset (Fin n))
    (hH : ∀ v ∈ H, 0 < g.graph.degree v) : H.card ≤ volumeNat g H := by
  calc
    H.card = ∑ v ∈ H, (1 : ℕ) := by simp
    _ ≤ ∑ v ∈ H, (g.neighbors v).length := by
      apply Finset.sum_le_sum
      intro v hv
      rw [neighbor_degree]
      exact hH v hv

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

-- Proof module: Solutions.OperationalVolumes

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma cache_volume_mass (g : InputGraph n) (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top)
    (hreg : RegionInvariant st) (hnum : NumericalInvariant g st) (hkeys : KeysInvariant g st)
    (hθ : 0 ≤ (st.frames j).theta) :
    (st.frames j).theta*(volumeNat g ((st.frames j).cache ∪ (st.frames j).high) : ℝ) ≤
      ∑ v ∈ (st.frames j).active, (st.frames j).residual v := by
  classical
  let C := (st.frames j).cache ∪ (st.frames j).high
  have hC : C ⊆ (st.frames j).active := Finset.union_subset_iff.mpr
    ⟨(hreg j hj).2.2.2,(hreg j hj).2.2.1⟩
  rw [volume_real,Finset.mul_sum]
  calc
    _ ≤ ∑ v ∈ C, (st.frames j).residual v := by
      apply Finset.sum_le_sum
      intro v hv
      have hd : 0 ≤ (st.frames j).theta*LocalPush.deg g.graph v := by
        apply mul_nonneg hθ
        unfold LocalPush.deg
        positivity
      obtain hv|hv := Finset.mem_union.mp hv
      · exact (hnum j hj).2 v hv
      · have hh := ((hkeys j hj).2 v).mp hv
        nlinarith [hh.2]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hC (fun v hv _ =>
      ((hnum j hj).1 v ((hreg j hj).1 hv)).1)

lemma run_cache_volume_unexhausted (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    (st.frames st.top).pc = .leafDrain → ¬exhausted st st.top →
      (volumeNat g ((st.frames st.top).cache ∪ (st.frames st.top).high) : ℝ) <
        2*(st.frames st.top).block := by
  intro st hpc he
  have hbudget : BudgetInvariant st := budget_run m g s α q ℓ schedule t
  have hb : (st.frames st.top).openBudget = true := by
    simpa [hpc,budgetPC] using hbudget st.top le_rfl
  have hp : ParameterInvariant st := parameters_run m g s α q hq ℓ schedule t
  have hθ : 0 < (st.frames st.top).theta := (hp st.top le_rfl).1.trans_le ((hp st.top le_rfl).2.2 hb)
  have hm := run_unexhausted_mass m g s α q hα hq hs ℓ schedule t st.top le_rfl hb he
  have hE := cache_volume_mass g st st.top le_rfl (region_run m g s α q ℓ schedule t)
    (numerical_run m g s α q hα hq hs ℓ schedule t) (keys_run m g s α q hq.le ℓ schedule t) hθ.le
  have hscale : ScaleInvariant st := scale_run m g s α q hq ℓ schedule t
  have hQ := hscale.1 st.top le_rfl hb
  change (∑ v ∈ (st.frames st.top).active, (st.frames st.top).residual v) < 2*(st.frames st.top).Q at hm
  rw [hQ] at hm
  nlinarith

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

-- Proof module: Solutions.CachedEvents

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma cacheExcess_nonnegative (g : InputGraph n) (st : RecursiveState n) (j : ℕ) :
    0 ≤ cacheExcess g st j := Finset.sum_nonneg (fun _ _ => le_max_right _ _)

lemma cached_solve_row_exact (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (he : cachedSolveEvent g (recursiveRun m g s α q ℓ schedule t) id) :
    let run := recursiveRun m g s α q ℓ schedule
    let st := run t
    let j := st.top
    let C := (st.frames j).cache ∪ (st.frames j).high
    ((run (t+1)).frames j).cache=C ∧
      ∀ v ∈ C, ((run (t+1)).frames j).residual v=(st.frames j).theta*LocalPush.deg g.graph v := by
  intro run st j C
  change cachedSolveEvent g st id at he
  obtain ⟨hd,hcomp,hpc,hex,hpend,hhigh,hvalid,hid⟩ := he
  have hstep : run (t+1)=recursiveStep m g s α ℓ schedule st := by
    simp only [run,st,recursiveRun,Function.iterate_succ_apply']
  have hreg : RegionInvariant st := region_run m g s α q ℓ schedule t
  have hC : C ⊆ (st.frames j).active := Finset.union_subset_iff.mpr
    ⟨(hreg j le_rfl).2.2.2,(hreg j le_rfl).2.2.1⟩
  have hvalid' : C ⊆ st.stored ∧ ∀ v ∈ C, 0 < g.graph.degree v := hvalid
  rw [hstep]
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hcomp,hpc,hex,hpend,Option.isSome_none,Bool.false_eq_true,hhigh]
  rw [if_pos hvalid]
  constructor
  · simp [changeFrame,jointUpdate,refreshKeys,debit,C,j]
  · intro v hv
    have hvU : v ∈ parentDomain st j := (hreg j le_rfl).1 (hC hv)
    have hx := solveOn_exact g α hα C hvalid'.2
      (fun v => (st.frames j).residual v-(st.frames j).theta*LocalPush.deg g.graph v) v hv
    have hclear : (st.frames j).residual v-
        (LocalPush.Lα g.graph α *ᵥ solveOn g α C (fun w => (st.frames j).residual w-(st.frames j).theta*LocalPush.deg g.graph w)) v=
          (st.frames j).theta*LocalPush.deg g.graph v := by rw [hx]; ring
    by_cases hz : st.top=0
    · simpa [changeFrame,jointUpdate,refreshKeys,debit,j,C,parentDomain,hz] using hclear
    · have hne : st.top-1 ≠ st.top := by omega
      have hv : v ∈ (st.frames (st.top-1)).active := by simpa [parentDomain,j,hz] using hvU
      simpa [changeFrame,jointUpdate,refreshKeys,debit,j,C,parentDomain,hz,hne,hv] using hclear

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheCapacity

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma cacheCapacity_nonnegative (st : RecursiveState n) (j : ℕ) : 0 ≤ cacheCapacity st j := by
  unfold cacheCapacity
  split
  · exact le_max_right _ _
  · rfl

lemma cacheCapacity_metadata (st : RecursiveState n) (k j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hC : (f (st.frames k)).cache=(st.frames k).cache)
    (hb : (f (st.frames k)).block=(st.frames k).block)
    (ho : (f (st.frames k)).openBudget=(st.frames k).openBudget) :
    cacheCapacity (changeFrame st k f) j=cacheCapacity st j := by
  unfold cacheCapacity
  rw [observe_changeFrame (fun f => f.cache) st k f hC j,
    observe_changeFrame (fun f => f.block) st k f hb j,
    observe_changeFrame (fun f => f.openBudget) st k f ho j]

@[simp] lemma cacheCapacity_PC (st : RecursiveState n) (pc : NormalizePC) (j : ℕ) :
    cacheCapacity (changePC st pc) j=cacheCapacity st j := cacheCapacity_metadata st st.top j _ rfl rfl rfl
@[simp] lemma cacheCapacity_debit (st : RecursiveState n) (k j : ℕ) (c : ℝ≥0∞) :
    cacheCapacity (debit st k c) j=cacheCapacity st j := rfl
@[simp] lemma cacheCapacity_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (j : ℕ) :
    cacheCapacity (refreshKeys g st T) j=cacheCapacity st j := by
  by_cases hj : j ≤ st.top <;> simp [cacheCapacity,refreshKeys,hj]
@[simp] lemma cacheCapacity_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) (j : ℕ) :
    cacheCapacity (jointUpdate g α st h) j=cacheCapacity st j := by
  by_cases hj : j ≤ st.top <;> simp [cacheCapacity,jointUpdate,hj]
@[simp] lemma cacheCapacity_finish (st : RecursiveState n) : cacheCapacity (finishEpisode st) st.top=0 := by
  simp [cacheCapacity,finishEpisode,changeFrame]
@[simp] lemma cacheCapacity_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ) :
    cacheCapacity (endCall g α st) j=cacheCapacity st j := by unfold endCall; dsimp only; split <;> rfl
@[simp] lemma cacheCapacity_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) (j : ℕ) :
    cacheCapacity (completeComponent m g s α st) j=cacheCapacity st j := rfl
@[simp] lemma cacheCapacity_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t j : ℕ) (v : Fin n) :
    cacheCapacity (exteriorPush g α st t v) j=cacheCapacity st j := by
  have hp := exterior_parameters g α st t v j
  have ho : ((exteriorPush g α st t v).frames j).openBudget=(st.frames j).openBudget := congrArg (fun z => z.2.2.1) hp
  have hb : ((exteriorPush g α st t v).frames j).block=(st.frames j).block := congrArg (fun z => z.2.2.2.2.2.1) hp
  unfold cacheCapacity
  rw [exterior_cache,ho,hb]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheCapacityStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma cacheCapacity_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (pc : NormalizePC) :
    cacheCapacity (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) st.top=cacheCapacity st st.top := by
  split
  · simp
  · cases hp : pendingPush st with
    | none => simp
    | some p => obtain ⟨t,v⟩ := p; simp

set_option maxHeartbeats 1000000 in
lemma cacheCapacity_step_non_cached (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hlevel : st.top=ℓ)
    (hn : ¬cachedSolveEvent g st (st.frames st.top).id) :
    cacheCapacity (recursiveStep m g s α ℓ schedule st) st.top ≤
      cacheCapacity st st.top+episodeCapacityCharge st := by
  have hnon := cacheCapacity_nonnegative st st.top
  by_cases hd : st.done=true
  · simp [recursiveStep,episodeCapacityCharge,episodeEvent,hd]
  have hd' : st.done=false := Bool.eq_false_iff.mpr hd
  by_cases hc : componentComplete st
  · simp [recursiveStep,episodeCapacityCharge,episodeEvent,hd,hc]
  by_cases hb : (st.frames st.top).pc=.beginEpisode
  · have hcharge : episodeCapacityCharge st=2*((st.frames st.top).block : ℝ) := by
      simp only [episodeCapacityCharge,episodeEvent,hd',Bool.false_eq_true,hc,hb,not_false_eq_true,and_self,ite_true]
    rw [hcharge]
    have hnew : cacheCapacity (recursiveStep m g s α ℓ schedule st) st.top=2*((st.frames st.top).block : ℝ) := by
      simp [cacheCapacity,recursiveStep,hd,hc,hb,changeFrame,debit]
    rw [hnew]
    linarith
  have hcharge : episodeCapacityCharge st=0 := by simp [episodeCapacityCharge,episodeEvent,hb]
  rw [hcharge,add_zero]
  simp only [recursiveStep,hd',Bool.false_eq_true,ite_false,hc]
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · simp
    · split
      · exact (cacheCapacity_drain g α st .initialDrain).le
      · split <;> simp
  | restartDrain =>
    simp only [hpc]
    split
    · simp
    · split
      · exact (cacheCapacity_drain g α st .restartDrain).le
      · rw [cacheCapacity_metadata _ _ _ _ rfl rfl rfl]
        rfl
  | beginEpisode => exact False.elim (hb hpc)
  | fullSolve =>
    simp only [hpc]
    split
    · simp
    · split
      · simp only [cacheCapacity_PC]
        change cacheCapacity (refreshKeys g (jointUpdate g α st
          (solveOn g α (st.frames st.top).active (st.frames st.top).residual))
          (touchedBy g (st.frames st.top).active)) st.top ≤ cacheCapacity st st.top
        rw [cacheCapacity_refresh,cacheCapacity_joint]
      · simp
  | normalize => simp only [hpc,hlevel,ite_true]; split <;> simp
  | leafDrain =>
    simp only [hpc]
    split
    · simp
    · rename_i hex
      split
      · cases hpending : pendingPush st with
        | none => simp [hpending]
        | some p => obtain ⟨t,v⟩ := p; simp [hpending]
      · rename_i hpend
        have hpnone : pendingPush st=none := by cases hh : pendingPush st <;> simp_all
        split
        · simp
        · rename_i hhigh
          split
          · rename_i hvalid
            exact False.elim (hn ⟨hd',hc,hpc,hex,hpnone,hhigh,hvalid,rfl⟩)
          · simp
  | afterChild =>
    simp only [hpc]
    have hz : cacheCapacity (finishEpisode (debit st st.top 1)) st.top=0 := cacheCapacity_finish (debit st st.top 1)
    split
    · simpa only [cacheCapacity_PC,hz] using hnon
    · split
      · simpa only [cacheCapacity_PC,hz] using hnon
      · exact (cacheCapacity_drain g α st .finishEpisode).le
  | finishEpisode =>
    have hz : cacheCapacity (recursiveStep m g s α ℓ schedule st) st.top=0 := by
      simp [cacheCapacity,recursiveStep,hd,hc,hpc,changePC,changeFrame,finishEpisode,debit] <;>
        split_ifs <;> simp_all [cacheCapacity,changePC,changeFrame,finishEpisode,debit]
    simpa only [recursiveStep,hd',Bool.false_eq_true,ite_false,hc,hpc] using hz.le.trans hnon
  | normal => simp [hpc]
  | interrupted => simp [hpc]

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

-- Proof module: Solutions.CachedCapacityPayment

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma cached_step_openBudget (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (id : ℕ)
    (he : cachedSolveEvent g st id) :
    ((recursiveStep m g s α ℓ schedule st).frames st.top).openBudget=(st.frames st.top).openBudget := by
  rcases he with ⟨hd,hcomp,hpc,hex,hpend,hhigh,hvalid,hid⟩
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hcomp,hpc,hex,hpend,Option.isSome_none,Bool.false_eq_true,hhigh]
  rw [if_pos hvalid]
  simp [changeFrame,jointUpdate,refreshKeys,debit]

lemma cached_capacity_payment (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (he : cachedSolveEvent g (recursiveRun m g s α q ℓ schedule t) id) :
    let run := recursiveRun m g s α q ℓ schedule
    let st := run t
    cacheCapacity (run (t+1)) st.top+newCacheCharge g st ≤ cacheCapacity st st.top := by
  intro run st
  change cachedSolveEvent g st id at he
  let C := (st.frames st.top).cache ∪ (st.frames st.top).high
  have hself : cachedSolveEvent g st (st.frames st.top).id := by
    simpa only [he.2.2.2.2.2.2.2] using he
  have hcache := (cached_solve_row_exact m g s α q hα hq hs ℓ schedule t id he).1
  have hstep : run (t+1)=recursiveStep m g s α ℓ schedule st := by
    simp only [run,st,recursiveRun,Function.iterate_succ_apply']
  have hopen : (st.frames st.top).openBudget=true := by
    have hh : (st.frames st.top).openBudget=budgetPC (st.frames st.top).pc := budget_run m g s α q ℓ schedule t st.top le_rfl
    simpa only [he.2.2.1,budgetPC] using hh
  have hopen' := cached_step_openBudget m g s α ℓ schedule st id he
  rw [←hstep,hopen] at hopen'
  have hb := congrArg (fun z => z.2.2.1) (frozenFrame_step m g s α ℓ schedule st st.top le_rfl)
  have hb' : ((run (t+1)).frames st.top).block=(st.frames st.top).block := by
    rw [hstep]
    exact hb
  have hvol := run_cache_volume_unexhausted m g s α q hα hq hs ℓ schedule t he.2.2.1
    (fun hx => he.2.2.2.1 ⟨st.top,le_rfl,hx⟩)
  have hcard : (C.card : ℝ) < 2*((st.frames st.top).block : ℝ) :=
    lt_of_le_of_lt (by exact_mod_cast card_le_volume g C he.2.2.2.2.2.2.1.2) hvol
  have holdcard : ((st.frames st.top).cache.card : ℝ) ≤ (C.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.subset_union_left : (st.frames st.top).cache ⊆ C)
  unfold cacheCapacity
  rw [hopen',hopen,hcache,hb']
  simp only [ite_true]
  rw [max_eq_left (by linarith : 0 ≤ 2*((st.frames st.top).block : ℝ)-(C.card : ℝ)),
    max_eq_left (by linarith : 0 ≤ 2*((st.frames st.top).block : ℝ)-((st.frames st.top).cache.card : ℝ))]
  by_cases hnew : (st.frames st.top).high ⊆ (st.frames st.top).cache
  · simp only [newCacheCharge,hself,hnew,not_true_eq_false,and_false,ite_false,add_zero]
    linarith
  · have hproper : (st.frames st.top).cache ⊂ C := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.subset_union_left,?_⟩
      intro heq
      apply hnew
      rw [heq]
      exact Finset.subset_union_right
    have hgap : ((st.frames st.top).cache.card : ℝ)+1 ≤ (C.card : ℝ) := by
      exact_mod_cast Finset.card_lt_card hproper
    simp only [newCacheCharge,hself,hnew,not_false_eq_true,and_self,ite_true]
    linarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheCapacityRun

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma cacheCapacity_run_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ)
    (hlevel : (recursiveRun m g s α q ℓ schedule t).top=ℓ) :
    let run := recursiveRun m g s α q ℓ schedule
    cacheCapacity (run (t+1)) ℓ+newCacheCharge g (run t) ≤
      cacheCapacity (run t) ℓ+episodeCapacityCharge (run t) := by
  intro run
  let st := run t
  have hlevel' : st.top=ℓ := hlevel
  have hstep : run (t+1)=recursiveStep m g s α ℓ schedule st := by
    simp only [run,st,recursiveRun,Function.iterate_succ_apply']
  by_cases he : cachedSolveEvent g st (st.frames st.top).id
  · have hz : episodeCapacityCharge st=0 := by simp [episodeCapacityCharge,episodeEvent,he.2.2.1]
    have hh := cached_capacity_payment m g s α q hα hq hs ℓ schedule t (st.frames st.top).id he
    change cacheCapacity (run (t+1)) ℓ+newCacheCharge g st ≤ cacheCapacity st ℓ+episodeCapacityCharge st
    rw [hz,add_zero]
    change cacheCapacity (run (t+1)) st.top+newCacheCharge g st ≤ cacheCapacity st st.top at hh
    rwa [hlevel'] at hh
  · have hz : newCacheCharge g st=0 := by simp only [newCacheCharge,he,false_and,ite_false]
    change cacheCapacity (run (t+1)) ℓ+newCacheCharge g st ≤ cacheCapacity st ℓ+episodeCapacityCharge st
    rw [hz,add_zero,hstep]
    simpa only [hlevel'] using cacheCapacity_step_non_cached m g s α ℓ schedule st hlevel' he

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheExcessControl

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma cacheExcess_metadata (g : InputGraph n) (st : RecursiveState n) (k j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hC : (f (st.frames k)).cache=(st.frames k).cache)
    (hθ : (f (st.frames k)).theta=(st.frames k).theta)
    (hr : (f (st.frames k)).residual=(st.frames k).residual) :
    cacheExcess g (changeFrame st k f) j=cacheExcess g st j := by
  unfold cacheExcess
  rw [observe_changeFrame (fun f => f.cache) st k f hC j,
    observe_changeFrame (fun f => f.theta) st k f hθ j,
    observe_changeFrame (fun f => f.residual) st k f hr j]

lemma cacheExcess_empty (g : InputGraph n) (st : RecursiveState n) (j : ℕ)
    (hC : (st.frames j).cache=∅) : cacheExcess g st j=0 := by simp only [cacheExcess,hC,Finset.sum_empty]

@[simp] lemma cacheExcess_PC (g : InputGraph n) (st : RecursiveState n) (pc : NormalizePC) (j : ℕ) :
    cacheExcess g (changePC st pc) j=cacheExcess g st j := cacheExcess_metadata g st st.top j _ rfl rfl rfl
@[simp] lemma cacheExcess_debit (g : InputGraph n) (st : RecursiveState n) (k j : ℕ) (c : ℝ≥0∞) :
    cacheExcess g (debit st k c) j=cacheExcess g st j := rfl
@[simp] lemma cacheExcess_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (j : ℕ) :
    cacheExcess g (refreshKeys g st T) j=cacheExcess g st j := by
  by_cases hj : j ≤ st.top <;> simp [cacheExcess,refreshKeys,hj]
@[simp] lemma cacheExcess_finish (g : InputGraph n) (st : RecursiveState n) :
    cacheExcess g (finishEpisode st) st.top=0 := cacheExcess_empty g _ _ (by simp [finishEpisode,changeFrame])
@[simp] lemma cacheExcess_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (j : ℕ) :
    cacheExcess g (endCall g α st) j=cacheExcess g st j := by unfold endCall; dsimp only; split <;> rfl
@[simp] lemma cacheExcess_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) (j : ℕ) :
    cacheExcess g (completeComponent m g s α st) j=cacheExcess g st j := rfl

lemma cacheExcess_joint_empty (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) (j : ℕ)
    (hC : (st.frames j).cache=∅) : cacheExcess g (jointUpdate g α st h) j=0 := by
  apply cacheExcess_empty
  by_cases hj : j ≤ st.top <;> simp [jointUpdate,hj,hC]

lemma cacheExcess_changeFrame_zero (g : InputGraph n) (st : RecursiveState n) (f : NormalizeFrame n → NormalizeFrame n)
    (hf : (f (st.frames st.top)).cache=∅) : cacheExcess g (changeFrame st st.top f) st.top=0 := by
  apply cacheExcess_empty
  simpa only [changeFrame,Function.update_self] using hf

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheExteriorRows

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

@[simp] lemma residual_debit (st : RecursiveState n) (j i : ℕ) (c : ℝ≥0∞) :
    ((debit st j c).frames i).residual=(st.frames i).residual := rfl
@[simp] lemma residual_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).residual=(st.frames i).residual := by
  by_cases hi : i ≤ st.top <;> simp [refreshKeys,hi]

lemma exterior_other_row (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t j : ℕ) (v w : Fin n)
    (hj : j ≤ st.top) (hw : w ≠ v) (hdom : w ∈ parentDomain st j) :
    ((exteriorPush g α st t v).frames j).residual w=(st.frames j).residual w+
      if g.graph.Adj w v then (1-α)*pushIncrement g st t v else 0 := by
  classical
  let δ := pushIncrement g st t v
  let base := rawExterior g α st t v δ
  have hadmit : ((admitStage g base t v).frames j).residual w=(base.frames j).residual w := by
    have hh := (admit_stage_fields g base t v).2.2.2.2.2.2.2 j w
    simpa only [hw,and_false,ite_false,add_zero] using hh
  rw [exterior_stages]
  change ((debit (refreshKeys g (if relative st t v+δ=3*(st.frames t).q/8 then admitStage g base t v else base)
    (insert v (g.neighbors v).toFinset)) t _).frames j).residual w=_
  rw [residual_debit,residual_refresh]
  by_cases ha : relative st t v+δ=3*(st.frames t).q/8
  · simp only [ha,ite_true,hadmit]
    simp [base,rawExterior,hj,hw,hdom,δ]
  · simp only [ha,ite_false]
    simp [base,rawExterior,hj,hw,hdom,δ]

lemma positive_part_add_le (a b : ℝ) (hb : 0 ≤ b) : max (a+b) 0 ≤ max a 0+b := by
  apply max_le <;> linarith [le_max_left a 0,le_max_right a 0]

lemma cache_neighbor_flow_bound (g : InputGraph n) (C : Finset (Fin n)) (v : Fin n) (F : ℝ) (hF : 0 ≤ F) :
    (∑ w ∈ C, if g.graph.Adj w v then F else 0) ≤ LocalPush.deg g.graph v*F := by
  classical
  have hsub : C.filter (fun w => g.graph.Adj w v) ⊆ g.graph.neighborFinset v := by
    intro w hw
    simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_filter.mp hw).2.symm
  have hc : ((C.filter (fun w => g.graph.Adj w v)).card : ℝ) ≤ LocalPush.deg g.graph v := by
    unfold LocalPush.deg
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (g.graph.card_neighborFinset_eq_degree v)
  have hs : (∑ w ∈ C, if g.graph.Adj w v then F else 0)=
      ((C.filter (fun w => g.graph.Adj w v)).card : ℝ)*F := by
    rw [←Finset.sum_filter]
    simp
  rw [hs]
  exact mul_le_mul_of_nonneg_right hc hF

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CachedExcessDrop

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma cached_step_theta (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (id : ℕ)
    (he : cachedSolveEvent g st id) :
    ((recursiveStep m g s α ℓ schedule st).frames st.top).theta=(st.frames st.top).theta := by
  rcases he with ⟨hd,hcomp,hpc,hex,hpend,hhigh,hvalid,hid⟩
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false,hcomp,hpc,hex,hpend,Option.isSome_none,Bool.false_eq_true,hhigh]
  rw [if_pos hvalid]
  simp [changeFrame,jointUpdate,refreshKeys,debit]

lemma cached_excess_after_zero (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (he : cachedSolveEvent g (recursiveRun m g s α q ℓ schedule t) id) :
    let run := recursiveRun m g s α q ℓ schedule
    cacheExcess g (run (t+1)) (run t).top=0 := by
  intro run
  have hr := cached_solve_row_exact m g s α q hα hq hs ℓ schedule t id he
  have hθ := cached_step_theta m g s α ℓ schedule (run t) id he
  have hstep : run (t+1)=recursiveStep m g s α ℓ schedule (run t) := by
    simp only [run,recursiveRun,Function.iterate_succ_apply']
  rw [←hstep] at hθ
  unfold cacheExcess
  rw [hr.1]
  apply Finset.sum_eq_zero
  intro v hv
  rw [hr.2 v hv,hθ]
  simp only [run,sub_self,max_self]

lemma cached_no_new_excess_floor (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (he : cachedSolveEvent g (recursiveRun m g s α q ℓ schedule t) id)
    (hnew : ((recursiveRun m g s α q ℓ schedule t).frames (recursiveRun m g s α q ℓ schedule t).top).high ⊆
      ((recursiveRun m g s α q ℓ schedule t).frames (recursiveRun m g s α q ℓ schedule t).top).cache) :
    let st := recursiveRun m g s α q ℓ schedule t
    (st.frames st.top).q ≤ cacheExcess g st st.top := by
  intro st
  change cachedSolveEvent g st id at he
  obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr he.2.2.2.2.2.1
  have hvC := hnew hv
  have hkey := ((keys_run m g s α q hq.le ℓ schedule t st.top le_rfl).2 v).mp hv
  have hbudget : (st.frames st.top).openBudget=true := by
    have hh : (st.frames st.top).openBudget=budgetPC (st.frames st.top).pc := budget_run m g s α q ℓ schedule t st.top le_rfl
    simpa only [he.2.2.1,budgetPC] using hh
  have hqf := (parameters_run m g s α q hq ℓ schedule t st.top le_rfl).1
  have hθq := (parameters_run m g s α q hq ℓ schedule t st.top le_rfl).2.2 hbudget
  have hdpos : 0 < g.graph.degree v := he.2.2.2.2.2.2.1.2 v (Finset.mem_union_right _ hv)
  have hd : 1 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; exact_mod_cast hdpos
  have hθd : (st.frames st.top).q ≤ (st.frames st.top).theta*LocalPush.deg g.graph v := by
    have hh := mul_le_mul_of_nonneg_left hd (hqf.le.trans hθq)
    nlinarith
  have hterm : (st.frames st.top).q ≤ max ((st.frames st.top).residual v-
      (st.frames st.top).theta*LocalPush.deg g.graph v) 0 := by
    have hh := hkey.2
    have hm := le_max_left ((st.frames st.top).residual v-(st.frames st.top).theta*LocalPush.deg g.graph v) 0
    nlinarith
  have hsum : max ((st.frames st.top).residual v-(st.frames st.top).theta*LocalPush.deg g.graph v) 0 ≤
      cacheExcess g st st.top := by
    unfold cacheExcess
    exact Finset.single_le_sum (fun w _ => le_max_right ((st.frames st.top).residual w-(st.frames st.top).theta*LocalPush.deg g.graph w) 0) hvC
  exact hterm.trans hsum

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheExcessExterior

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma cacheExcess_exterior_le (g : InputGraph n) (α : ℝ) (hα : α ≤ 1) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hp : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st) (t : ℕ) (v : Fin n)
    (hprod : stepProduction st=some (t,v)) :
    cacheExcess g (exteriorPush g α st t v) st.top ≤ cacheExcess g st st.top+incomingProduction g α st st.top := by
  classical
  have hpend := production_pending st t v hprod
  obtain ⟨ht,hm⟩ := pending_push_member st t v hpend
  have hout := (Finset.mem_sdiff.mp ((hreg t ht).2.1 hm)).2
  have hδ := production_increment_nonnegative g st hreg hp hnum hkeys hiso t v hprod
  let F := (1-α)*pushIncrement g st t v
  have hF : 0 ≤ F := mul_nonneg (sub_nonneg.mpr hα) hδ
  have hθ : ((exteriorPush g α st t v).frames st.top).theta=(st.frames st.top).theta :=
    congrArg (fun z => z.2.1) (exterior_parameters g α st t v st.top)
  have hrow (w : Fin n) (hw : w ∈ (st.frames st.top).cache) :
      ((exteriorPush g α st t v).frames st.top).residual w=(st.frames st.top).residual w+
        if g.graph.Adj w v then F else 0 := by
    have hwH := (hreg st.top le_rfl).2.2.2 hw
    have hne : w ≠ v := by
      intro heq
      have hh := active_subset_between st hreg t st.top ht le_rfl hwH
      exact hout (heq ▸ hh)
    exact exterior_other_row g α st t st.top v w le_rfl hne ((hreg st.top le_rfl).1 hwH)
  unfold cacheExcess
  rw [exterior_cache,hθ]
  calc
    _ ≤ ∑ w ∈ (st.frames st.top).cache,
        (max ((st.frames st.top).residual w-(st.frames st.top).theta*LocalPush.deg g.graph w) 0+
          if g.graph.Adj w v then F else 0) := by
      apply Finset.sum_le_sum
      intro w hw
      rw [hrow w hw]
      have hh : 0 ≤ if g.graph.Adj w v then F else 0 := by split <;> positivity
      convert positive_part_add_le ((st.frames st.top).residual w-(st.frames st.top).theta*LocalPush.deg g.graph w)
        (if g.graph.Adj w v then F else 0) hh using 1 <;> congr 1 <;> ring
    _ = (∑ w ∈ (st.frames st.top).cache, max ((st.frames st.top).residual w-(st.frames st.top).theta*LocalPush.deg g.graph w) 0)+
      ∑ w ∈ (st.frames st.top).cache, if g.graph.Adj w v then F else 0 := Finset.sum_add_distrib
    _ ≤ (∑ w ∈ (st.frames st.top).cache, max ((st.frames st.top).residual w-(st.frames st.top).theta*LocalPush.deg g.graph w) 0)+
      LocalPush.deg g.graph v*F := add_le_add le_rfl (cache_neighbor_flow_bound g _ v F hF)
    _ = _ := by simp only [incomingProduction,hprod,if_pos ht]; dsimp only [F]; ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheExcessStep

set_option autoImplicit false
set_option maxRecDepth 4096
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local simp] cacheExcess_metadata cacheExcess_joint_empty cacheExcess_changeFrame_zero
variable {n : ℕ}

lemma cacheExcess_drain_none (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (pc : NormalizePC)
    (hp : drainProduction st=none) :
    cacheExcess g (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) st.top=cacheExcess g st st.top := by
  unfold drainProduction at hp
  split
  · simp
  · rename_i he
    rw [if_neg he] at hp
    simp only [hp,cacheExcess_PC,cacheExcess_debit]

set_option maxHeartbeats 1500000 in
lemma cacheExcess_step_nonproducing (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hlevel : st.top=ℓ)
    (hcache : CacheControlInvariant ℓ st)
    (hp : stepProduction st=none) (hn : ¬cachedSolveEvent g st (st.frames st.top).id) :
    cacheExcess g (recursiveStep m g s α ℓ schedule st) st.top ≤ cacheExcess g st st.top := by
  have hnon := cacheExcess_nonnegative g st st.top
  have hfinish0 : cacheExcess g (finishEpisode (debit st st.top 1)) st.top=0 := cacheExcess_finish g (debit st st.top 1)
  by_cases hd : st.done=true
  · simp [recursiveStep,hd]
  have hd' : st.done=false := Bool.eq_false_iff.mpr hd
  by_cases hc : componentComplete st
  · simp [recursiveStep,hd,hc]
  simp only [recursiveStep,hd',Bool.false_eq_true,ite_false,hc]
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · simp
    · rename_i hanc
      split
      · rename_i hpend
        have hh : drainProduction st=none := by
          simpa only [stepProduction,hd',Bool.false_eq_true,ite_false,hc,hpc,hanc,hpend,ite_true] using hp
        exact (cacheExcess_drain_none g α st .initialDrain hh).le
      · split <;> simp
  | restartDrain =>
    simp only [hpc]
    split
    · simp
    · rename_i hanc
      split
      · rename_i hpend
        have hh : drainProduction st=none := by
          simpa only [stepProduction,hd',Bool.false_eq_true,ite_false,hc,hpc,hanc,hpend,ite_true] using hp
        exact (cacheExcess_drain_none g α st .restartDrain hh).le
      · rw [cacheExcess_metadata g _ _ _ _ rfl rfl rfl]
        rfl
  | beginEpisode =>
    simp only [hpc]
    have hz : cacheExcess g (recursiveStep m g s α ℓ schedule st) st.top=0 := by
      apply cacheExcess_empty
      simp [recursiveStep,hd,hc,hpc,changeFrame,debit]
    simpa only [recursiveStep,hd',Bool.false_eq_true,ite_false,hc,hpc] using hz.le.trans hnon
  | fullSolve =>
    have hC := (hcache st.top le_rfl).2.2 hpc
    simp only [hpc]
    split
    · simp
    · split
      · simp only [cacheExcess_PC,cacheExcess_debit,cacheExcess_refresh]
        have hz := cacheExcess_joint_empty g α st (solveOn g α (st.frames st.top).active (st.frames st.top).residual) st.top hC
        change cacheExcess g (refreshKeys g (jointUpdate g α st
          (solveOn g α (st.frames st.top).active (st.frames st.top).residual))
          (touchedBy g (st.frames st.top).active)) st.top ≤ cacheExcess g st st.top
        rw [cacheExcess_refresh]
        exact hz.le.trans hnon
      · simp
  | normalize =>
    simp only [hpc,hlevel,ite_true]
    split <;> simp
  | leafDrain =>
    simp only [hpc]
    split
    · simp
    · rename_i hex
      split
      · rename_i hpend
        have hh : drainProduction st=none := by
          simpa only [stepProduction,hd',Bool.false_eq_true,ite_false,hc,hpc,hex,hpend,ite_true] using hp
        have hpnone : pendingPush st=none := by simpa only [drainProduction,if_neg hex] using hh
        simp only [hpnone,Option.isSome_none,Bool.false_eq_true] at hpend
      · rename_i hpend
        have hpnone : pendingPush st=none := by cases hh : pendingPush st <;> simp_all
        split
        · simp
        · rename_i hhigh
          split
          · rename_i hvalid
            exact False.elim (hn ⟨hd',hc,hpc,hex,hpnone,hhigh,hvalid,rfl⟩)
          · simp
  | afterChild =>
    simp only [hpc]
    split
    · simpa only [cacheExcess_PC,hfinish0] using hnon
    · rename_i hanc
      split
      · simpa only [cacheExcess_PC,hfinish0] using hnon
      · rename_i hex
        have hh : drainProduction st=none := by
          simpa only [stepProduction,hd',Bool.false_eq_true,ite_false,hc,hpc,hanc,hex] using hp
        exact (cacheExcess_drain_none g α st .finishEpisode hh).le
  | finishEpisode =>
    have hz : cacheExcess g (recursiveStep m g s α ℓ schedule st) st.top=0 := by
      apply cacheExcess_empty
      simp [recursiveStep,hd,hc,hpc,changePC,changeFrame,finishEpisode,debit] <;> split_ifs <;> simp_all [changePC,changeFrame,finishEpisode,debit]
    simpa only [recursiveStep,hd',Bool.false_eq_true,ite_false,hc,hpc] using hz.le.trans hnon
  | normal => simp [hpc]
  | interrupted => simp [hpc]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheExcessRun

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma cacheExcess_run_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ)
    (hlevel : (recursiveRun m g s α q ℓ schedule t).top=ℓ) :
    let run := recursiveRun m g s α q ℓ schedule
    cacheExcess g (run (t+1)) ℓ+noNewCacheCharge g (run t) ≤
      cacheExcess g (run t) ℓ+incomingProduction g α (run t) ℓ := by
  intro run
  let st := run t
  have hlevel' : st.top=ℓ := hlevel
  have hstep : run (t+1)=recursiveStep m g s α ℓ schedule st := by
    simp only [run,st,recursiveRun,Function.iterate_succ_apply']
  by_cases he : cachedSolveEvent g st (st.frames st.top).id
  · have hz := cached_excess_after_zero m g s α q hα hq hs ℓ schedule t (st.frames st.top).id he
    have hin : incomingProduction g α st ℓ=0 := by
      simp only [incomingProduction,stepProduction,he.1,Bool.false_eq_true,ite_false,he.2.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2.1,Option.isSome_none]
    change cacheExcess g (run (t+1)) ℓ+noNewCacheCharge g st ≤ cacheExcess g st ℓ+incomingProduction g α st ℓ
    rw [hin,←hlevel',hz,add_zero]
    by_cases hnew : (st.frames st.top).high ⊆ (st.frames st.top).cache
    · rw [noNewCacheCharge,if_pos ⟨he,hnew⟩,zero_add]
      exact cached_no_new_excess_floor m g s α q hq ℓ schedule t (st.frames st.top).id he hnew
    · simp only [noNewCacheCharge,he,hnew,and_false,ite_false,zero_add]
      exact cacheExcess_nonnegative g st st.top
  · have hz : noNewCacheCharge g st=0 := by simp only [noNewCacheCharge,he,false_and,ite_false]
    change cacheExcess g (run (t+1)) ℓ+noNewCacheCharge g st ≤ cacheExcess g st ℓ+incomingProduction g α st ℓ
    rw [hz,add_zero,hstep]
    cases hp : stepProduction st with
    | none =>
      simp only [incomingProduction,hp,add_zero]
      simpa only [hlevel'] using cacheExcess_step_nonproducing m g s α ℓ schedule st hlevel'
        (cache_run m g s α q ℓ schedule t) hp he
    | some p =>
      obtain ⟨u,v⟩ := p
      rw [production_push m g s α ℓ schedule st u v hp]
      simpa only [hlevel'] using cacheExcess_exterior_le g α hα.2.le st (region_run m g s α q ℓ schedule t)
        (parameters_run m g s α q hq ℓ schedule t) (numerical_run m g s α q hα hq hs ℓ schedule t)
        (keys_run m g s α q hq.le ℓ schedule t) (isolate_run m g s α q hs ℓ schedule t) u v hp

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

lemma active_mass_le_parent (g : InputGraph n) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hlayer : LayerIdentity g st) (hp : ParameterInvariant st)
    (hnum : NumericalInvariant g st) (j : ℕ) (hj : j < st.top) :
    (∑ v ∈ (st.frames (j+1)).active, (st.frames (j+1)).residual v) ≤
      ∑ v ∈ (st.frames j).active, (st.frames j).residual v := by
  have hsub : (st.frames (j+1)).active ⊆ (st.frames j).active := by
    simpa [parentDomain] using (hreg (j+1) hj).1
  calc
    _ ≤ ∑ v ∈ (st.frames (j+1)).active, (st.frames j).residual v := by
      apply Finset.sum_le_sum
      intro v hv
      exact layer_residual_dominance g st hreg hlayer hp hnum j (j+1) (by omega) hj v ((hreg (j+1) hj).1 hv)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v hv _ =>
      ((hnum j hj.le).1 v ((hreg j hj.le).1 hv)).1)

lemma run_child_mass_unexhausted (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t j : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    j < st.top → ¬exhausted st j →
      (∑ v ∈ (st.frames (j+1)).active, (st.frames (j+1)).residual v) <
        2*(st.frames (j+1)).q*(st.frames (j+1)).N := by
  intro st hj he
  have hm := active_mass_le_parent g st (region_run m g s α q ℓ schedule t)
    (layer_run m g s α q ℓ schedule t) (parameters_run m g s α q hq ℓ schedule t)
    (numerical_run m g s α q hα hq hs ℓ schedule t) j hj
  have hopen : (st.frames j).openBudget=true := by
    simpa [stack_run m g s α q ℓ schedule t j hj,budgetPC] using budget_run m g s α q ℓ schedule t j hj.le
  have hp := run_unexhausted_mass m g s α q hα hq hs ℓ schedule t j hj.le hopen he
  have hscale : ScaleInvariant st := scale_run m g s α q hq ℓ schedule t
  have hQ : (st.frames j).Q=(st.frames (j+1)).q*(st.frames (j+1)).N := by
    rw [hscale.1 j hj.le hopen,hscale.2 j hj,threshold_relation_run m g s α q ℓ schedule t j hj]
  change (∑ v ∈ (st.frames j).active, (st.frames j).residual v) < 2*(st.frames j).Q at hp
  rw [hQ] at hp
  nlinarith

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

-- Proof module: Solutions.CachedIntervals

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma cached_production_none (g : InputGraph n) (st : RecursiveState n) (id : ℕ)
    (he : cachedSolveEvent g st id) : stepProduction st=none := by
  simp only [stepProduction,he.1,Bool.false_eq_true,ite_false,he.2.1,he.2.2.1,
    he.2.2.2.1,he.2.2.2.2.1,Option.isSome_none]

lemma cached_income_zero (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (id j : ℕ)
    (he : cachedSolveEvent g st id) : incomingProduction g α st j=0 := by
  simp only [incomingProduction,cached_production_none g st id he]

lemma cacheCapacity_upper (st : RecursiveState n) (j : ℕ) :
    cacheCapacity st j ≤ 2*((st.frames j).block : ℝ) := by
  unfold cacheCapacity
  split
  · apply max_le
    · have hc : (0 : ℝ) ≤ ((st.frames j).cache.card : ℝ) := by positivity
      linarith
    · positivity
  · positivity

lemma cached_event_span (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a ≤ b)
    (ha : cachedSolveEvent g (recursiveRun m g s α q ℓ schedule a) id)
    (hb : cachedSolveEvent g (recursiveRun m g s α q ℓ schedule b) id) :
    let run := recursiveRun m g s α q ℓ schedule
    ∀ k, a ≤ k → k ≤ b → (run k).top=ℓ ∧ ((run k).frames ℓ).id=id ∧
      frozenFrame ((run k).frames ℓ)=frozenFrame ((run a).frames ℓ) := by
  intro run
  have hia := (running_call_information m g s α q ℓ schedule a id ha.1 ha.2.2.2.2.2.2.2).1
  have hnb := (running_call_information m g s α q ℓ schedule b id hb.1 hb.2.2.2.2.2.2.2).2
  have hspan := unclosed_call_interval m g s α q ℓ schedule a b id
    ⟨(run a).top,((run a).frames (run a).top).N,((run a).frames (run a).top).block⟩ hia hnb
  have hlevel : (run a).top=ℓ := (cache_run m g s α q ℓ schedule a (run a).top le_rfl).2.1 ha.2.2.1
  intro k hak hkb
  have hle : ℓ ≤ (run k).top := by rw [←hlevel]; exact (hspan k hak hkb).1
  have htop : (run k).top=ℓ := Nat.le_antisymm (depth_run m g s α q ℓ schedule k) hle
  refine ⟨htop,?_,?_⟩
  · have hh := (hspan k hak hkb).2.1
    simpa only [hlevel] using hh
  · exact frozenFrame_interval m g s α q ℓ schedule a k ℓ hak
      (fun u hau huk => by
        have hh : (run a).top ≤ (run u).top := (hspan u hau (huk.le.trans hkb)).1
        simpa only [hlevel] using hh)

lemma cache_amortized_intervals (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b : ℕ) (hab : a ≤ b)
    (hlevel : ∀ k, a ≤ k → k < b → (recursiveRun m g s α q ℓ schedule k).top=ℓ) :
    let run := recursiveRun m g s α q ℓ schedule
    (∑ k ∈ Finset.range (b-a), noNewCacheCharge g (run (a+k))) ≤
      cacheExcess g (run a) ℓ+∑ k ∈ Finset.range (b-a), incomingProduction g α (run (a+k)) ℓ ∧
    (∑ k ∈ Finset.range (b-a), newCacheCharge g (run (a+k))) ≤
      cacheCapacity (run a) ℓ+∑ k ∈ Finset.range (b-a), episodeCapacityCharge (run (a+k)) := by
  intro run
  constructor
  · exact amortized_interval_bound (fun t => cacheExcess g (run t) ℓ)
      (fun t => noNewCacheCharge g (run t)) (fun t => incomingProduction g α (run t) ℓ) a b hab
      (cacheExcess_nonnegative g (run b) ℓ) (fun k hak hkb =>
        cacheExcess_run_step m g s α q hα hq hs ℓ schedule k (hlevel k hak hkb))
  · exact amortized_interval_bound (fun t => cacheCapacity (run t) ℓ)
      (fun t => newCacheCharge g (run t)) (fun t => episodeCapacityCharge (run t)) a b hab
      (cacheCapacity_nonnegative (run b) ℓ) (fun k hak hkb =>
        cacheCapacity_run_step m g s α q hα hq hs ℓ schedule k (hlevel k hak hkb))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheChargeIdentity

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma cache_charge_identity (g : InputGraph n) (st : RecursiveState n) (hq : 0 < (st.frames st.top).q) :
    (if cachedSolveEvent g st (st.frames st.top).id then (1 : ℝ) else 0)=
      noNewCacheCharge g st/(st.frames st.top).q+newCacheCharge g st := by
  unfold noNewCacheCharge newCacheCharge
  by_cases he : cachedSolveEvent g st (st.frames st.top).id
  · by_cases hnew : (st.frames st.top).high ⊆ (st.frames st.top).cache <;> simp [he,hnew,hq.ne']
  · simp [he]

lemma episode_capacity_identity (st : RecursiveState n) (id ℓ b : ℕ)
    (hlevel : st.top=ℓ) (hid : (st.frames ℓ).id=id) (hb : (st.frames ℓ).block=b) :
    episodeCapacityCharge st=2*(b : ℝ)*(if episodeEvent st id then 1 else 0) := by
  unfold episodeCapacityCharge
  rw [hlevel,hid,hb]
  split <;> simp

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

-- Proof module: Solutions.CurrentMassBound

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma current_mass_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ)
    (he : ¬ancestorExhausted (recursiveRun m g s α q ℓ schedule t)) :
    let st := recursiveRun m g s α q ℓ schedule t
    (∑ v ∈ (st.frames st.top).active, (st.frames st.top).residual v) ≤ 2*(st.frames st.top).q*(st.frames st.top).N := by
  intro st
  cases htop : st.top with
  | zero =>
    have hnum : NumericalInvariant g st := numerical_run m g s α q hα hq hs ℓ schedule t
    have hmass := root_residual_mass_bound g s α hα.1.le st (root_identity_run m g s α q ℓ schedule t) hnum
      ((parameters_run m g s α q hq ℓ schedule t 0 (Nat.zero_le _)).1.le)
    have hsub : (∑ v ∈ (st.frames 0).active, (st.frames 0).residual v) ≤ ∑ v, (st.frames 0).residual v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ =>
        ((hnum 0 (Nat.zero_le _)).1 v (by simp [parentDomain])).1)
    have hqr : (st.frames 0).q=q := root_threshold_run m g s α q ℓ schedule t
    have hNr : (st.frames 0).N=1/q := root_scale_run m g s α q ℓ schedule t
    rw [hqr,hNr]
    have hqN : 2*q*(1/q)=(2 : ℝ) := by field_simp
    rw [hqN]
    linarith
  | succ j =>
    have hj : j < st.top := by omega
    have hnot : ¬exhausted st j := fun hh => he ⟨j,hj,hh⟩
    have hh := run_child_mass_unexhausted m g s α q hα hq hs ℓ schedule t j hj hnot
    simpa only [htop] using hh.le

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CacheExcessMass

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma cacheExcess_le_active_mass (g : InputGraph n) (st : RecursiveState n) (j : ℕ)
    (hj : j ≤ st.top) (hreg : RegionInvariant st) (hnum : NumericalInvariant g st)
    (hθ : 0 ≤ (st.frames j).theta) :
    cacheExcess g st j ≤ ∑ v ∈ (st.frames j).active, (st.frames j).residual v := by
  have hsub := (hreg j hj).2.2.2
  unfold cacheExcess
  calc
    _ ≤ ∑ v ∈ (st.frames j).cache, (st.frames j).residual v := by
      apply Finset.sum_le_sum
      intro v hv
      have hn := ((hnum j hj).1 v ((hreg j hj).1 (hsub hv))).1
      have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
      apply max_le
      · exact sub_le_self _ (mul_nonneg hθ hd)
      · exact hn
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v hv _ =>
      ((hnum j hj).1 v ((hreg j hj).1 hv)).1)

lemma cached_excess_mass_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (he : cachedSolveEvent g (recursiveRun m g s α q ℓ schedule t) id) :
    let st := recursiveRun m g s α q ℓ schedule t
    cacheExcess g st st.top ≤ 2*(st.frames st.top).q*(st.frames st.top).N := by
  intro st
  change cachedSolveEvent g st id at he
  have hopen : (st.frames st.top).openBudget=true := by
    have hh : (st.frames st.top).openBudget=budgetPC (st.frames st.top).pc := budget_run m g s α q ℓ schedule t st.top le_rfl
    simpa only [he.2.2.1,budgetPC] using hh
  have hθ := (parameters_run m g s α q hq ℓ schedule t st.top le_rfl).2.2 hopen
  have hqf := (parameters_run m g s α q hq ℓ schedule t st.top le_rfl).1
  have hh := cacheExcess_le_active_mass g st st.top le_rfl (region_run m g s α q ℓ schedule t)
    (numerical_run m g s α q hα hq hs ℓ schedule t) (hqf.le.trans hθ)
  exact hh.trans (current_mass_bound m g s α q hα hq hs ℓ schedule t
    (fun hx => he.2.2.2.1 (by obtain ⟨i,hi,he⟩ := hx; exact ⟨i,hi.le,he⟩)))

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CachedIntervalCount

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

set_option maxHeartbeats 2000000 in
lemma cached_interval_count_bound (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b t id : ℕ) (hab : a ≤ b) (hbt : b < t)
    (ha : cachedSolveEvent g (recursiveRun m g s α q ℓ schedule a) id)
    (hb : cachedSolveEvent g (recursiveRun m g s α q ℓ schedule b) id) :
    let run := recursiveRun m g s α q ℓ schedule
    let f := (run a).frames ℓ
    (∑ k ∈ Finset.Ico a (b+1), if cachedSolveEvent g (run k) id then (1 : ℝ) else 0) ≤
      2*(f.block : ℝ)*((run t).episodes id+1)+(2+2*(kappa ℓ 0 : ℝ))*f.N := by
  intro run f
  have hspan := cached_event_span m g s α q ℓ schedule a b id hab ha hb
  have hla : (run a).top=ℓ := (hspan a le_rfl hab).1
  have hqf : 0 < f.q := (parameters_run m g s α q hq.1 ℓ schedule a ℓ (by rw [hla])).1
  have hqk (k : ℕ) (hak : a ≤ k) (hkb : k ≤ b) : ((run k).frames ℓ).q=f.q :=
    congrArg Prod.fst (hspan k hak hkb).2.2
  have hbk (k : ℕ) (hak : a ≤ k) (hkb : k ≤ b) : ((run k).frames ℓ).block=f.block :=
    congrArg (fun z => z.2.2.1) (hspan k hak hkb).2.2
  have hprod := unexhausted_call_production_bound m g s α q hα hq hs ℓ schedule a b id hab
    ha.1 ha.2.2.2.2.2.2.2 hb.1 hb.2.2.2.2.2.2.2 hb.2.2.2.1
  dsimp only at hprod
  change (∑ k ∈ Finset.Ico a b, (incomingProduction g α (run k) (run a).top+birthProduction g (run k) (run a).top)) ≤ _ at hprod
  rw [hla] at hprod
  have hprodNon (k : ℕ) := production_nonnegative g α hα.2.le (run k)
    (region_run m g s α q ℓ schedule k) (parameters_run m g s α q hq.1 ℓ schedule k)
    (numerical_run m g s α q hα hq.1 hs ℓ schedule k) (keys_run m g s α q hq.1.le ℓ schedule k)
    (isolate_run m g s α q hs ℓ schedule k) ℓ
  have hinput : (∑ k ∈ Finset.Ico a b, incomingProduction g α (run k) ℓ) ≤ 2*(kappa ℓ 0 : ℝ)*f.q*f.N := by
    apply le_trans ?_ hprod
    exact Finset.sum_le_sum (fun k _ => le_add_of_nonneg_right (hprodNon k).2.2)
  have hacc := cache_amortized_intervals m g s α q hα hq.1 hs ℓ schedule a (b+1) (by omega)
    (fun k hak hkb => (hspan k hak (by omega)).1)
  have hfloweq : (∑ k ∈ Finset.range (b+1-a), incomingProduction g α (run (a+k)) ℓ)=
      ∑ k ∈ Finset.Ico a b, incomingProduction g α (run k) ℓ := by
    rw [offset_sum_eq_Ico (fun k => incomingProduction g α (run k) ℓ) a (b+1) (by omega),Finset.sum_Ico_succ_top hab,
      cached_income_zero g α (run b) id ℓ hb,add_zero]
  have hEa : cacheExcess g (run a) ℓ ≤ 2*f.q*f.N := by
    have hh := cached_excess_mass_bound m g s α q hα hq.1 hs ℓ schedule a id ha
    change cacheExcess g (run a) (run a).top ≤ _ at hh
    rwa [hla] at hh
  have hNo : (∑ k ∈ Finset.range (b+1-a), noNewCacheCharge g (run (a+k))) ≤
      (2+2*(kappa ℓ 0 : ℝ))*f.q*f.N := by
    have hh := hacc.1
    rw [hfloweq] at hh
    nlinarith
  have hEp : (∑ k ∈ Finset.range (b+1-a), episodeCapacityCharge (run (a+k))) ≤
      2*(f.block : ℝ)*((run t).episodes id : ℝ) := by
    rw [offset_sum_eq_Ico (fun k => episodeCapacityCharge (run k)) a (b+1) (by omega)]
    calc
      _ = ∑ k ∈ Finset.Ico a (b+1), 2*(f.block : ℝ)*(if episodeEvent (run k) id then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro k hk
        obtain ⟨hak,hkb⟩ := Finset.mem_Ico.mp hk
        exact episode_capacity_identity (run k) id ℓ f.block (hspan k hak (by omega)).1
          (hspan k hak (by omega)).2.1 (hbk k hak (by omega))
      _ = 2*(f.block : ℝ)*(∑ k ∈ Finset.Ico a (b+1), if episodeEvent (run k) id then 1 else 0) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [episodes_run_events m g s α q ℓ schedule t id]
        exact indicator_interval_bound (fun k => episodeEvent (run k) id) a (b+1) t (by omega)
  have hNew : (∑ k ∈ Finset.range (b+1-a), newCacheCharge g (run (a+k))) ≤
      2*(f.block : ℝ)*((run t).episodes id+1) := by
    have hc := cacheCapacity_upper (run a) ℓ
    have hh := hacc.2
    nlinarith
  have hCharge : (∑ k ∈ Finset.Ico a (b+1), if cachedSolveEvent g (run k) id then (1 : ℝ) else 0)=
      (∑ k ∈ Finset.range (b+1-a), noNewCacheCharge g (run (a+k)))/f.q+
        ∑ k ∈ Finset.range (b+1-a), newCacheCharge g (run (a+k)) := by
    rw [offset_sum_eq_Ico (fun k => noNewCacheCharge g (run k)) a (b+1) (by omega),offset_sum_eq_Ico (fun k => newCacheCharge g (run k)) a (b+1) (by omega),
      Finset.sum_div,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨hak,hkb⟩ := Finset.mem_Ico.mp hk
    have htop : (run k).top=ℓ := (hspan k hak (by omega)).1
    have hid : ((run k).frames (run k).top).id=id := by rw [htop]; exact (hspan k hak (by omega)).2.1
    have hqeq : ((run k).frames (run k).top).q=f.q := by rw [htop]; exact hqk k hak (by omega)
    have hh := cache_charge_identity g (run k) (by rw [hqeq]; exact hqf)
    rwa [hid,hqeq] at hh
  rw [hCharge]
  have hNoDiv : (∑ k ∈ Finset.range (b+1-a), noNewCacheCharge g (run (a+k)))/f.q ≤
      (2+2*(kappa ℓ 0 : ℝ))*f.N := by
    apply (div_le_iff₀ hqf).mpr
    nlinarith
  calc
    _ ≤ (2+2*(kappa ℓ 0 : ℝ))*f.N+2*(f.block : ℝ)*((run t).episodes id+1) := add_le_add hNoDiv hNew
    _ = _ := by ring

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

-- Proof module: Solutions.CachedPrefixCount

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma cached_solve_prefix_count (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ) (info : CallInformation)
    (hinfo : (recursiveRun m g s α q ℓ schedule t).information id=some info) :
    let run := recursiveRun m g s α q ℓ schedule
    (((Finset.range t).filter (fun k => cachedSolveEvent g (run k) id)).card : ℝ) ≤
      2*(info.block : ℝ)*((run t).episodes id+1)+(2+2*(kappa ℓ 0 : ℝ))*info.scale := by
  classical
  intro run
  let S := (Finset.range t).filter (fun k => cachedSolveEvent g (run k) id)
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let b := S.max' hS
    have haS : a ∈ S := Finset.min'_mem S hS
    have hbS : b ∈ S := Finset.max'_mem S hS
    have ha : cachedSolveEvent g (run a) id := (Finset.mem_filter.mp haS).2
    have hb : cachedSolveEvent g (run b) id := (Finset.mem_filter.mp hbS).2
    have hab : a ≤ b := Finset.min'_le S b hbS
    have hbt : b < t := Finset.mem_range.mp (Finset.mem_filter.mp hbS).1
    have hat : a ≤ t := (Finset.mem_range.mp (Finset.mem_filter.mp haS).1).le
    have hcover : S ⊆ Finset.Ico a (b+1) := by
      intro k hk
      exact Finset.mem_Ico.mpr ⟨Finset.min'_le S k hk,Nat.lt_succ_of_le (Finset.le_max' S k hk)⟩
    have hcovered := indicator_cover_bound (fun k => cachedSolveEvent g (run k) id) S (Finset.Ico a (b+1))
      (fun k hk => (Finset.mem_filter.mp hk).2) hcover
    have hbound := cached_interval_count_bound m g s α q hα hq hs ℓ schedule a b t id hab hbt ha hb
    have hfirst := running_call_prefix_parameters m g s α q ℓ schedule a t id info hat hinfo ha.1 ha.2.2.2.2.2.2.2
    have hlevel : (run a).top=ℓ := (cache_run m g s α q ℓ schedule a (run a).top le_rfl).2.1 ha.2.2.1
    have hN : ((run a).frames ℓ).N=info.scale := by
      have hh : ((run a).frames (run a).top).N=info.scale := hfirst.2.1
      rwa [hlevel] at hh
    have hb' : ((run a).frames ℓ).block=info.block := by
      have hh : ((run a).frames (run a).top).block=info.block := hfirst.2.2
      rwa [hlevel] at hh
    dsimp only at hbound
    change (∑ k ∈ Finset.Ico a (b+1), if cachedSolveEvent g (run k) id then (1 : ℝ) else 0) ≤
      2*(((run a).frames ℓ).block : ℝ)*((run t).episodes id+1)+(2+2*(kappa ℓ 0 : ℝ))*((run a).frames ℓ).N at hbound
    rw [hN,hb'] at hbound
    exact hcovered.trans hbound
  · have hz : S.card=0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hS)
    have hlegal := information_legal_run m g s α q hq ℓ schedule t id info hinfo
    have hN : 0 ≤ info.scale := by linarith [hlegal.2.1]
    change (S.card : ℝ) ≤ _
    rw [hz,Nat.cast_zero]
    positivity

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.LogOverhead

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma queue_log_overhead_bound (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ t : ℕ) (ht : t ≤ ℓ) :
    1+Real.logb 2 (2+(3+2*(t+1 : ℕ))/rootThreshold ε ℓ) ≤
      (1+(Real.log 128+4)/Real.log 2)*(2+Real.log (2/ε)+(ℓ : ℝ)) := by
  have he0 : 0 < ε := hε.1
  have hel0 : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
  let A : ℝ := ℓ+3
  let L := Real.log (2/ε)
  let B : ℝ := 2+L+ℓ
  let D := Real.log 128+4
  let z : ℝ := 2+(3+2*(t+1 : ℕ))/rootThreshold ε ℓ
  have hA : 0 < A := by dsimp [A]; positivity
  have hA3 : 3 ≤ A := by dsimp [A]; linarith
  have hqr : rootThreshold ε ℓ = ε/(32*A) := by simp [rootThreshold,kappa,A]
  have hq : 0 < rootThreshold ε ℓ := by rw [hqr]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have htc : (t : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast ht
  have hP : (3+2*(t+1 : ℕ) : ℝ) ≤ 2*A := by dsimp [A]; push_cast; linarith
  have hze : z*ε = 2*ε+(3+2*(t+1 : ℕ))*32*A := by
    dsimp only [z]
    rw [hqr]
    field_simp [he0.ne',hA.ne'] <;> push_cast <;> ring
  have hupper : z ≤ 128*A^2/ε := by
    apply (le_div_iff₀ hε.1).mpr
    rw [hze]
    have hm := mul_le_mul_of_nonneg_right hP (show 0 ≤ 32*A by positivity)
    nlinarith [hε.2]
  have hlog : Real.log z ≤ Real.log 128+2*Real.log A-Real.log ε := by
    have hh := Real.log_le_log hz hupper
    have hnum : (128 : ℝ)*A^2 ≠ 0 := by positivity
    rw [Real.log_div hnum hε.1.ne',Real.log_mul (by norm_num : (128 : ℝ) ≠ 0) (pow_ne_zero 2 hA.ne'),Real.log_pow] at hh
    norm_num at hh
    exact hh
  have hL : 0 ≤ L := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hε.1).mpr
    linarith [hε.2]
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog128 : 0 ≤ Real.log (128 : ℝ) := Real.log_nonneg (by norm_num)
  have hLA : Real.log A ≤ (ℓ : ℝ)+2 := by
    have hh := Real.log_le_sub_one_of_pos hA
    dsimp [A] at hh
    linarith
  have hεL : -Real.log ε ≤ L := by
    dsimp only [L]
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hε.1.ne']
    linarith
  have hD : 2 ≤ D := by dsimp [D]; linarith
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hlogB : Real.log z ≤ D*B := by
    have hel : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    have hm1 := mul_le_mul_of_nonneg_right hD hel
    have hm2 := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ D by linarith) hL
    dsimp [D,B]
    dsimp [D] at hm1 hm2
    nlinarith [hlog,hLA,hεL]
  change 1+Real.logb 2 z ≤ (1+D/Real.log 2)*B
  rw [Real.logb]
  calc
    _ ≤ B+(D*B)/Real.log 2 := add_le_add hB (div_le_div_of_nonneg_right hlogB hlog2.le)
    _ = _ := by ring

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.SolverLogBound

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma queueLogConstant_positive : 0 < queueLogConstant := by
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h128 : 0 ≤ Real.log (128 : ℝ) := Real.log_nonneg (by norm_num)
  unfold queueLogConstant
  positivity

lemma primitiveLogConstant_bounds : 1 ≤ primitiveLogConstant ∧ queueLogConstant ≤ primitiveLogConstant ∧
    1+queueLogConstant*Real.log 2 ≤ primitiveLogConstant := by
  have hA := queueLogConstant_positive.le
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  refine ⟨?_,?_,?_⟩ <;> unfold primitiveLogConstant <;> nlinarith [mul_nonneg hA h2]

lemma solver_log_linear (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ : ℕ) (V : ℝ)
    (hV : 0 ≤ V) (hvol : V ≤ 1/rootThreshold ε ℓ) :
    1+Real.log (2+3*V) ≤ primitiveLogConstant*(2+Real.log (2/ε)+(ℓ : ℝ)) := by
  let q := rootThreshold ε ℓ
  let B := 2+Real.log (2/ε)+(ℓ : ℝ)
  let z : ℝ := 2+(3+2*(ℓ+1 : ℕ))/q
  have he : 0 < ε := hε.1
  have hq : 0 < q := by dsimp [q,rootThreshold,kappa]; positivity
  have hB : 1 ≤ B := by
    have hL : 0 ≤ Real.log (2/ε) := Real.log_nonneg ((le_div_iff₀ he).mpr (by linarith [hε.2]))
    have hl : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    dsimp only [B]
    linarith
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hP : (3 : ℝ) ≤ (3+2*(ℓ+1 : ℕ) : ℝ) := by
    have hl : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    push_cast
    linarith
  have hupper : 2+3*V ≤ z := by
    calc
      _ ≤ 2+3*(1/q) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hvol (by norm_num))
      _ = 2+3/q := by ring
      _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right hP hq.le)
  have hlog := Real.log_le_log (show 0 < 2+3*V by positivity) hupper
  have hqueue := queue_log_overhead_bound ε hε ℓ ℓ le_rfl
  change 1+Real.logb 2 z ≤ queueLogConstant*B at hqueue
  rw [Real.logb] at hqueue
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hz : Real.log z ≤ queueLogConstant*Real.log 2*B := by
    have hh : Real.log z/Real.log 2 ≤ queueLogConstant*B-1 := by linarith
    have hm := (div_le_iff₀ h2).mp hh
    nlinarith
  calc
    _ ≤ B+queueLogConstant*Real.log 2*B := add_le_add hB (hlog.trans hz)
    _ = (1+queueLogConstant*Real.log 2)*B := by ring
    _ ≤ primitiveLogConstant*B := mul_le_mul_of_nonneg_right primitiveLogConstant_bounds.2.2 hB0

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CountLogBounds

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma count_log_bounds (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ : ℕ) (N b : ℝ)
    (hN : 1 ≤ N) (hb : 1 ≤ b) (hbN : b ≤ N) (hupper : N ≤ 1/rootThreshold ε ℓ) :
    let X := 2+Real.log (2/ε)+(ℓ : ℝ)
    let A := primitiveLogConstant/Real.log 2
    (⌈Real.log (4*N/b)/Real.log 2⌉₊ : ℝ)+1 ≤ (2*A+2)*X ∧
      Real.log (2/rootThreshold ε ℓ)/Real.log 2 ≤ A*X ∧ (kappa ℓ 0 : ℝ) ≤ 2*X := by
  intro X A
  let q := rootThreshold ε ℓ
  let z := 2+3*(1/q)
  have he : 0 < ε := hε.1
  have hq : 0 < q := by dsimp [q,rootThreshold,kappa]; positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ Real.log (2/ε) := Real.log_nonneg ((le_div_iff₀ he).mpr (by linarith [hε.2]))
  have hX : 1 ≤ X := by
    have hl : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    dsimp only [X]
    linarith
  have hN0 : (1 : ℝ) ≤ 1/q := hN.trans hupper
  have hz : 0 < z := by dsimp [z]; positivity
  have hlinear := solver_log_linear ε hε ℓ (1/q) (by positivity) le_rfl
  have hlogz : Real.log z ≤ primitiveLogConstant*X := by
    change 1+Real.log z ≤ primitiveLogConstant*X at hlinear
    linarith
  have hratio : 4*N/b ≤ z^2 := by
    have hdiv : N/b ≤ N := div_le_self (by linarith) hb
    have hh : N/b ≤ 1/q := hdiv.trans hupper
    rw [mul_div_assoc]
    dsimp only [z]
    nlinarith [sq_nonneg (1/q)]
  have hratio1 : 1 ≤ 4*N/b := by
    apply (le_div_iff₀ (by linarith : 0 < b)).mpr
    linarith
  have hlogratio : Real.log (4*N/b)/Real.log 2 ≤ 2*A*X := by
    have hh := Real.log_le_log (by positivity : 0 < 4*N/b) hratio
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    apply (div_le_iff₀ hl2).mpr
    dsimp only [A]
    have heq : 2*(primitiveLogConstant/Real.log 2)*X*Real.log 2=2*primitiveLogConstant*X := by field_simp
    rw [heq]
    linarith
  have hceil := Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hratio1) hl2.le)
  have hsecond : Real.log (2/q)/Real.log 2 ≤ A*X := by
    have hh := Real.log_le_log (by positivity : 0 < 2/q) (show 2/q ≤ z by
      have heq : 2/q=2*(1/q) := by ring
      rw [heq]
      dsimp only [z]
      linarith)
    calc
      _ ≤ (primitiveLogConstant*X)/Real.log 2 := div_le_div_of_nonneg_right (hh.trans hlogz) hl2.le
      _ = _ := by dsimp only [A]; ring
  have hA : 0 ≤ A := div_nonneg (zero_le_one.trans primitiveLogConstant_bounds.1) hl2.le
  refine ⟨?_,hsecond,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hX (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  · simp only [kappa,Nat.sub_zero,Nat.cast_add,Nat.cast_ofNat]
    dsimp only [X]
    have hl : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    linarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.UniformFullCount

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma root_threshold_unit (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ : ℕ) :
    0 < rootThreshold ε ℓ ∧ rootThreshold ε ℓ ≤ 1 := by
  have he : 0 < ε := hε.1
  have hk : (3 : ℝ) ≤ (kappa ℓ 0 : ℝ) := by
    exact_mod_cast (show 3 ≤ kappa ℓ 0 by simp only [kappa,Nat.sub_zero]; omega)
  unfold rootThreshold
  refine ⟨by positivity,?_⟩
  apply (div_le_one (by positivity : 0 < 32*(kappa ℓ 0 : ℝ))).mpr
  linarith [hε.2]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.UniformCachedCount

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

lemma uniform_cached_solve_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n)
      (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule),
      (0 < α ∧ α ≤ 1/2) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
      ∀ (t id : ℕ) (info : CallInformation),
        (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).information id=some info →
          (((Finset.range t).filter (fun k => cachedSolveEvent g
            (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule k) id)).card : ℝ) ≤
              overhead C 4 ε ℓ*info.scale := by
  obtain ⟨Ce,hCe,hEpisodes⟩ := uniform_episode_count
  let C := 2*Ce+8
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro m n g s α ε ℓ schedule hα hε hs t id info hinfo
  let X := 2+Real.log (2/ε)+(ℓ : ℝ)
  have hq := root_threshold_unit ε hε ℓ
  have ha : 0 < α ∧ α < 1 := ⟨hα.1,by linarith [hα.2]⟩
  have hlegal := information_legal_run m g s α (rootThreshold ε ℓ) hq ℓ schedule t id info hinfo
  have hb : (0 : ℝ) < info.block := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hlegal.2.2.1
  have hN : 0 ≤ info.scale := by linarith [hlegal.2.1]
  have hbN := hlegal.2.2.2.1
  have hprefix := cached_solve_prefix_count m g s α (rootThreshold ε ℓ) ha hq hs ℓ schedule t id info hinfo
  have hEp := hEpisodes m n g s α ε ℓ schedule hα hε hs t id info hinfo
  have hX : 1 ≤ X := by
    have hl := Real.log_nonneg ((le_div_iff₀ hε.1).mpr (by linarith [hε.2]) : 1 ≤ 2/ε)
    have hel : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    dsimp only [X]
    linarith
  have hX4 : 1 ≤ X^4 := one_le_pow₀ hX
  have hXX4 : X ≤ X^4 := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hX : 1 ≤ X^3) (by linarith : 0 ≤ X)
    nlinarith
  have hκ : (kappa ℓ 0 : ℝ) ≤ 2*X := (count_log_bounds ε hε ℓ info.scale info.block hlegal.2.1
    (by exact_mod_cast hlegal.2.2.1) hbN hlegal.2.2.2.2).2.2
  have hEpPaid : 2*(info.block : ℝ)*
      ((recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).episodes id : ℝ) ≤
        2*Ce*X^4*info.scale := by
    have hh := mul_le_mul_of_nonneg_left hEp (by positivity : 0 ≤ 2*(info.block : ℝ))
    have heq : 2*(info.block : ℝ)*(overhead Ce 4 ε ℓ*info.scale/info.block)=2*Ce*X^4*info.scale := by
      dsimp only [overhead,X]
      field_simp
    rwa [heq] at hh
  have hcoeff : 4+2*(kappa ℓ 0 : ℝ) ≤ 8*X^4 := by linarith
  have hExtra : 2*(info.block : ℝ)+(2+2*(kappa ℓ 0 : ℝ))*info.scale ≤ 8*X^4*info.scale := by
    have hh := mul_le_mul_of_nonneg_right hcoeff hN
    nlinarith
  apply hprefix.trans
  change _ ≤ C*X^4*info.scale
  dsimp only [C]
  nlinarith

end
end NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n)
      (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule),
      (0 < α ∧ α ≤ 1/2) → (0 < ε ∧ ε ≤ 1) → 0 < g.graph.degree s →
      ∀ (t id : ℕ) (info : CallInformation),
        (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).information id=some info →
          (((Finset.range t).filter (fun k => cachedSolveEvent g
            (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule k) id)).card : ℝ) ≤
              overhead C 4 ε ℓ*info.scale := by
  exact uniform_cached_solve_count
