-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_budget_energy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T10:56:59.998956+00:00
-- url     : https://prove2.me/submissions/eb16c06e-81b4-43ee-8ccc-64d7739731f2

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants

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

-- Proof module: Solutions.RecursiveInvariants

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

variable {n : ℕ}

lemma residual_addition (g : InputGraph n) (s : Fin n) (α : ℝ)
    (x h : Fin n → ℝ) :
    residual g.graph α s (x+h) = residual g.graph α s x - LocalPush.Lα g.graph α *ᵥ h := by
  unfold residual
  rw [Matrix.mulVec_add]
  abel

lemma residual_coordinate_update (g : InputGraph n) (s v : Fin n) (α h : ℝ)
    (x : Fin n → ℝ) :
    residual g.graph α s (Function.update x v (x v+h)) =
      residual g.graph α s x - fun u => LocalPush.Lα g.graph α u v * h := by
  have he : Function.update x v (x v+h) = x + Pi.single v h := by
    ext u
    by_cases hu : u = v <;> simp [hu]
  rw [he, residual_addition, Matrix.mulVec_single]
  rfl


end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootIdentityControl

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_identity_same (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st st' : RecursiveState n) (hx : st'.x = st.x)
    (hq : (st'.frames 0).q = (st.frames 0).q)
    (hA : (st'.frames 0).active = (st.frames 0).active)
    (hr : (st'.frames 0).residual = (st.frames 0).residual)
    (hi : RootIdentity g s α st) : RootIdentity g s α st' := by
  intro v
  simpa only [hx,hq,hA,hr] using hi v

lemma root_identity_changeFrame (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hq : (f (st.frames j)).q = (st.frames j).q)
    (hA : (f (st.frames j)).active = (st.frames j).active)
    (hr : (f (st.frames j)).residual = (st.frames j).residual)
    (hi : RootIdentity g s α st) : RootIdentity g s α (changeFrame st j f) := by
  refine root_identity_same g s α st (changeFrame st j f) rfl ?_ ?_ ?_ hi
  all_goals by_cases he : (0 : ℕ) = j <;> simp_all [changeFrame]

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


lemma layer_identity_transport (g : InputGraph n) (st st' : RecursiveState n)
    (ht : st'.top ≤ st.top) (hx : st'.x = st.x)
    (hf : ∀ i ≤ st'.top, layerView (st'.frames i) = layerView (st.frames i))
    (hi : LayerIdentity g st) : LayerIdentity g st' := by
  intro j hj v hv
  have hfields (i : ℕ) (hh : i ≤ st'.top) :
      (st'.frames i).q = (st.frames i).q ∧
      (st'.frames i).active = (st.frames i).active ∧
      (st'.frames i).reference = (st.frames i).reference ∧
      (st'.frames i).residual = (st.frames i).residual := by
    simpa only [layerView,Prod.mk.injEq] using hf i hh
  have hp := hfields j (by omega)
  have hc := hfields (j+1) hj
  rw [hp.2.1] at hv
  have hh := hi j (lt_of_lt_of_le hj ht) v hv
  simpa only [hp.2.2.2,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,relative,hx] using hh

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

-- Proof module: Solutions.LayerControl

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma layer_changeFrame (g : InputGraph n) (st : RecursiveState n)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hf : layerView (f (st.frames j)) = layerView (st.frames j))
    (hi : LayerIdentity g st) : LayerIdentity g (changeFrame st j f) := by
  apply layer_identity_transport g st (changeFrame st j f) le_rfl rfl _ hi
  intro i hh
  by_cases he : i = j
  · subst i
    simpa [changeFrame] using hf
  · simp [changeFrame,he]

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

-- Proof module: Solutions.ParameterInvariant

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

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

-- Proof module: Solutions.SolveUpdates

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma lap_outside_nonpositive (g : InputGraph n) (α : ℝ) (hα : α ≤ 1)
    (T : Finset (Fin n)) (h : Fin n → ℝ) (hh : ∀ v, 0 ≤ h v)
    (hs : ∀ v ∉ T, h v = 0) (v : Fin n) (hv : v ∉ T) :
    (LocalPush.Lα g.graph α *ᵥ h) v ≤ 0 := by
  rw [lap_mul_apply,hs v hv,mul_zero,zero_sub]
  exact neg_nonpos.mpr (mul_nonneg (sub_nonneg.mpr hα)
    (Finset.sum_nonneg fun w _ => hh w))

end
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

-- Proof module: Solutions.NumericalControl

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma numerical_changeFrame (g : InputGraph n) (st : RecursiveState n) (hi : NumericalInvariant g st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hq : (f (st.frames j)).q = (st.frames j).q)
    (hA : (f (st.frames j)).active = (st.frames j).active)
    (href : (f (st.frames j)).reference = (st.frames j).reference)
    (hr : (f (st.frames j)).residual = (st.frames j).residual)
    (hcache : j ≤ st.top → ∀ v ∈ (f (st.frames j)).cache,
      (f (st.frames j)).theta*LocalPush.deg g.graph v ≤ (f (st.frames j)).residual v) :
    NumericalInvariant g (changeFrame st j f) := by
  classical
  have ha (i : ℕ) : ((changeFrame st j f).frames i).active = (st.frames i).active := by
    by_cases he : i = j <;> simp [changeFrame,he,hA]
  have hp := parentDomain_same st (changeFrame st j f) ha
  have hrel (i : ℕ) (v : Fin n) : relative (changeFrame st j f) i v = relative st i v := by
    by_cases hz : i = 0 <;> by_cases he : i = j <;> simp [relative,hz,changeFrame,he,href]
  intro i hh
  have his : i ≤ st.top := hh
  constructor
  · intro v hv
    rw [hp] at hv
    have hn := (hi i his).1 v hv
    simp only [hrel]
    by_cases he : i = j
    · subst i
      simpa [changeFrame,hq,hA,hr,hrel] using hn
    · simpa [changeFrame,he,hrel] using hn
  · intro v hv
    by_cases he : i = j
    · subst i
      simpa [changeFrame] using hcache his v (by simpa [changeFrame] using hv)
    · simpa [changeFrame,he] using (hi i his).2 v (by simpa [changeFrame,he] using hv)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NumericalSolves

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma principal_ancestor_update_bounds (g : InputGraph n) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hlayer : LayerIdentity g st)
    (hparam : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (T : Finset (Fin n)) (hT : T ⊆ (st.frames st.top).active)
    (hpos : ∀ v ∈ T, 0 < g.graph.degree v) (b : Fin n → ℝ)
    (hb : ∀ v ∈ T, 0 ≤ b v) (hbr : ∀ v ∈ T, b v ≤ (st.frames st.top).residual v) :
    let h := solveOn g α T b
    (∀ v, 0 ≤ h v) ∧
      ∀ i ≤ st.top, ∀ v ∈ parentDomain st i,
        (LocalPush.Lα g.graph α *ᵥ h) v ≤ (st.frames i).residual v := by
  have hh := solveOn_nonneg g α hα T hpos b hb
  refine ⟨hh,?_⟩
  intro i his v hv
  by_cases hvT : v ∈ T
  · rw [solveOn_exact g α hα T hpos b v hvT]
    have hvtop : v ∈ parentDomain st st.top := (hreg st.top le_rfl).1 (hT hvT)
    exact (hbr v hvT).trans (layer_residual_dominance g st hreg hlayer hparam hnum i st.top his le_rfl v hvtop)
  · have hn := lap_outside_nonpositive g α hα.2.le T _ hh
      (fun w hw => solveOn_outside g α T b w hw) v hvT
    exact hn.trans ((hnum i his).1 v hv).1

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

lemma global_inactive_drained_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hroot : RootIdentity g s α st) (hlayer : LayerIdentity g st)
    (hnum : NumericalInvariant g st) (hkeys : KeysInvariant g st) (hparam : ParameterInvariant st)
    (hmono : ∀ j < st.top, (st.frames j).q ≤ (st.frames (j+1)).q)
    (hp : pendingPush st = none) (j : ℕ) (hj : j ≤ st.top) (v : Fin n)
    (hv : v ∉ (st.frames j).active) :
    residual g.graph α s st.x v ≤
      (thresholdSum st j+(5/2 : ℝ)*(st.frames j).q)*LocalPush.deg g.graph v := by
  have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
  induction j with
  | zero =>
    have hdom : v ∈ parentDomain st 0 := by simp [parentDomain]
    have hh := virtual_state_identity g s α st hreg hroot hlayer 0 (Nat.zero_le _) v
    have hy := ((hnum 0 (Nat.zero_le _)).1 v hdom).2.2.2 hv
    have hr : (st.frames 0).residual v ≤ (st.frames 0).q*LocalPush.deg g.graph v := by
      by_contra hn
      have he := ((hkeys 0 (Nat.zero_le _)).1 v).mpr ⟨hdom,hv,lt_of_not_ge hn⟩
      rw [pending_none_queues_empty st hp 0 (Nat.zero_le _)] at he
      simp at he
    simp [thresholdSum,virtualPotential,virtualReference,virtualResidual,hv] at hh ⊢
    have hhcap : 4*LocalPush.deg g.graph v*st.x v ≤
        (3/2 : ℝ)*(st.frames 0).q*LocalPush.deg g.graph v := by
      have hh := mul_le_mul_of_nonneg_left hy.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hd)
      simp only [relative,ite_true] at hh
      nlinarith
    nlinarith
  | succ j ih =>
    have hjj : j < st.top := by omega
    by_cases hdom : v ∈ parentDomain st (j+1)
    · have hh := virtual_state_identity g s α st hreg hroot hlayer (j+1) hj v
      obtain ⟨hy,hract⟩ := virtual_actual g st (j+1) v hdom
      rw [hy,hract] at hh
      simp only [hv,ite_false] at hh
      have hycap := ((hnum (j+1) hj).1 v hdom).2.2.2 hv
      have hr : (st.frames (j+1)).residual v ≤ (st.frames (j+1)).q*LocalPush.deg g.graph v := by
        by_contra hn
        have he := ((hkeys (j+1) hj).1 v).mpr ⟨hdom,hv,lt_of_not_ge hn⟩
        rw [pending_none_queues_empty st hp (j+1) hj] at he
        simp at he
      have hmul := mul_le_mul_of_nonneg_left hycap.le hd
      nlinarith
    · have hout : v ∉ (st.frames j).active := by simpa [parentDomain] using hdom
      have hh := ih hjj.le hout
      have hq := hmono j hjj
      have hq0 := (hparam j hjj.le).1
      have hmul := mul_le_mul_of_nonneg_right hq hd
      have hsum : thresholdSum st (j+1) = thresholdSum st j+(st.frames j).q := by
        simp [thresholdSum,Finset.sum_range_succ]
      rw [hsum]
      nlinarith [mul_nonneg hq0.le hd]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetEnergy

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma energyRow_active (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hroot : RootIdentity g s α st) (hlayer : LayerIdentity g st)
    (hnum : NumericalInvariant g st) (j : ℕ) (hj : j ≤ st.top) (v : Fin n)
    (hv : v ∈ (st.frames j).active) :
    energyRow g s α st j v = (st.frames j).residual v := by
  unfold energyRow
  rw [global_active_identity g s α st hreg hroot hlayer j hj v hv]
  simp only [hv,ite_true,add_zero,add_sub_cancel_left]
  exact max_eq_left (((hnum j hj).1 v ((hreg j hj).1 hv)).1)

lemma energyRow_inactive_drained (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hroot : RootIdentity g s α st) (hlayer : LayerIdentity g st)
    (hnum : NumericalInvariant g st) (hkeys : KeysInvariant g st) (hparam : ParameterInvariant st)
    (hmono : ∀ j < st.top, (st.frames j).q ≤ (st.frames (j+1)).q)
    (hp : pendingPush st = none) (j : ℕ) (hj : j ≤ st.top) (v : Fin n)
    (hv : v ∉ (st.frames j).active) : energyRow g s α st j v = 0 := by
  have hh := global_inactive_drained_bound g s α st hreg hroot hlayer hnum hkeys hparam hmono hp j hj v hv
  have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
  have hq : 0 ≤ (st.frames j).q := (hparam j hj).1.le
  have hb : (3/2 : ℝ)*(st.frames j).q ≤ birthAllowance st j := by
    unfold birthAllowance
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
    push_cast
    nlinarith [mul_nonneg hj0 hq]
  unfold energyRow
  simp only [hv,ite_false]
  apply max_eq_right
  have hm := mul_le_mul_of_nonneg_right hb hd
  nlinarith

lemma budgetEnergy_drained (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hroot : RootIdentity g s α st) (hlayer : LayerIdentity g st)
    (hnum : NumericalInvariant g st) (hkeys : KeysInvariant g st) (hparam : ParameterInvariant st)
    (hmono : ∀ j < st.top, (st.frames j).q ≤ (st.frames (j+1)).q)
    (hp : pendingPush st = none) (j : ℕ) (hj : j ≤ st.top) :
    budgetEnergy g s α st j = ∑ v ∈ (st.frames j).active, (st.frames j).residual v := by
  unfold budgetEnergy
  calc
    _ = ∑ v ∈ (st.frames j).active, energyRow g s α st j v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      exact energyRow_inactive_drained g s α st hreg hroot hlayer hnum hkeys hparam hmono hp j hj v hv
    _ = _ := Finset.sum_congr rfl (fun v hv => energyRow_active g s α st hreg hroot hlayer hnum j hj v hv)

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ClippedMass

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma clipped_sum_sub (a L : Fin n → ℝ) (H : Finset (Fin n))
    (ha : ∀ v ∈ H, 0 ≤ a v) (hb : ∀ v ∈ H, 0 ≤ a v-L v)
    (hL : ∀ v ∉ H, L v ≤ 0) :
    (∑ v, max (a v-L v) 0) ≤ (∑ v, max (a v) 0)-∑ v, L v := by
  calc
    _ ≤ ∑ v, (max (a v) 0-L v) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : v ∈ H
      · rw [max_eq_left (ha v hv),max_eq_left (hb v hv)]
      · apply max_le
        · linarith [le_max_left (a v) 0]
        · linarith [le_max_right (a v) 0,hL v hv]
    _ = _ := by rw [Finset.sum_sub_distrib]

lemma clipped_joint_nonincrease (g : InputGraph n) (α : ℝ) (hα : 0 ≤ α ∧ α ≤ 1)
    (a h : Fin n → ℝ) (H : Finset (Fin n))
    (hh : ∀ v, 0 ≤ h v) (hs : ∀ v ∉ H, h v = 0)
    (ha : ∀ v ∈ H, 0 ≤ a v)
    (hb : ∀ v ∈ H, 0 ≤ a v-(LocalPush.Lα g.graph α *ᵥ h) v) :
    (∑ v, max (a v-(LocalPush.Lα g.graph α *ᵥ h) v) 0) ≤ ∑ v, max (a v) 0 := by
  have hL : ∀ v ∉ H, (LocalPush.Lα g.graph α *ᵥ h) v ≤ 0 :=
    lap_outside_nonpositive g α hα.2 H h hh hs
  have hsum : 0 ≤ ∑ v, (LocalPush.Lα g.graph α *ᵥ h) v := by
    rw [lap_sum]
    exact mul_nonneg hα.1 (Finset.sum_nonneg (fun v _ => mul_nonneg (by unfold LocalPush.deg; positivity) (hh v)))
  exact (clipped_sum_sub a _ H ha hb hL).trans (sub_le_self _ hsum)

lemma clipped_coordinate_flow (g : InputGraph n) (α : ℝ) (hα : α ≤ 1)
    (a : Fin n → ℝ) (v : Fin n) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∑ w, max (a w-LocalPush.Lα g.graph α w v*δ) 0) ≤
      (∑ w, max (a w) 0)+(1-α)*LocalPush.deg g.graph v*δ := by
  classical
  have hrow (w : Fin n) : max (a w-LocalPush.Lα g.graph α w v*δ) 0 ≤
      max (a w) 0+(if g.graph.Adj w v then (1-α)*δ else 0) := by
    by_cases he : w = v
    · subst w
      have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
      have hl : LocalPush.Lα g.graph α v v = LocalPush.deg g.graph v := by
        simp [LocalPush.Lα,LocalPush.degM,LocalPush.adjM,SimpleGraph.adjMatrix_apply]
      rw [hl]
      simp only [SimpleGraph.irrefl,ite_false,add_zero]
      apply max_le
      · linarith [le_max_left (a v) 0,mul_nonneg hd hδ]
      · exact le_max_right _ _
    · by_cases hadj : g.graph.Adj w v
      · have hl : LocalPush.Lα g.graph α w v = -(1-α) := by
          simp [LocalPush.Lα,LocalPush.degM,LocalPush.adjM,SimpleGraph.adjMatrix_apply,he,hadj]
        rw [hl,if_pos hadj]
        apply max_le
        · linarith [le_max_left (a w) 0]
        · linarith [le_max_right (a w) 0,mul_nonneg (sub_nonneg.mpr hα) hδ]
      · have hl : LocalPush.Lα g.graph α w v = 0 := by
          simp [LocalPush.Lα,LocalPush.degM,LocalPush.adjM,SimpleGraph.adjMatrix_apply,he,hadj]
        simp [hl,hadj]
  calc
    _ ≤ ∑ w, (max (a w) 0+if g.graph.Adj w v then (1-α)*δ else 0) :=
      Finset.sum_le_sum (fun w _ => hrow w)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      have hs : (∑ w : Fin n, if g.graph.Adj w v then (1-α)*δ else 0) =
          ∑ w ∈ g.graph.neighborFinset v, (1-α)*δ := by
        rw [←Finset.sum_filter]
        apply Finset.sum_congr
        · ext w; simp [SimpleGraph.mem_neighborFinset,g.graph.adj_comm]
        · intro w _; rfl
      rw [hs]
      simp [LocalPush.deg]
      ring

lemma clipped_admission (a : Fin n → ℝ) (v : Fin n) (B : ℝ) (hB : 0 ≤ B) :
    (∑ w, max (a w+(if w = v then B else 0)) 0) ≤ (∑ w, max (a w) 0)+B := by
  classical
  calc
    _ ≤ ∑ w, (max (a w) 0+if w = v then B else 0) := by
      apply Finset.sum_le_sum
      intro w _
      by_cases he : w = v
      · subst w
        simp only [ite_true]
        apply max_le
        · linarith [le_max_left (a v) 0]
        · linarith [le_max_right (a v) 0]
      · simp [he]
    _ = _ := by simp [Finset.sum_add_distrib]

lemma clipped_coordinate_nonincrease (g : InputGraph n) (α : ℝ) (hα : 0 ≤ α ∧ α ≤ 1)
    (a : Fin n → ℝ) (H : Finset (Fin n)) (v : Fin n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hv : v ∈ H) (ha : ∀ w ∈ H, 0 ≤ a w) (hav : LocalPush.deg g.graph v*δ ≤ a v) :
    (∑ w, max (a w-LocalPush.Lα g.graph α w v*δ) 0) ≤ ∑ w, max (a w) 0 := by
  classical
  have hh : ∀ w : Fin n, 0 ≤ (Pi.single v δ : Fin n → ℝ) w := by
    intro w; by_cases he : w = v <;> simp [Pi.single_apply,he,hδ]
  have hs : ∀ w ∉ H, (Pi.single v δ : Fin n → ℝ) w = 0 := by
    intro w hw
    have he : w ≠ v := by intro he; subst w; exact hw hv
    simp [Pi.single_apply,he]
  have hafter (w : Fin n) (hw : w ∈ H) :
      0 ≤ a w-(LocalPush.Lα g.graph α *ᵥ Pi.single v δ) w := by
    by_cases he : w = v
    · subst w
      simpa [Matrix.mulVec_single,LocalPush.Lα,LocalPush.degM,LocalPush.adjM,
        SimpleGraph.adjMatrix_apply] using sub_nonneg.mpr hav
    · have hl := lap_outside_nonpositive g α hα.2 {v} (Pi.single v δ) hh
        (fun u hu => by simp_all [Pi.single_apply]) w (by simp [he])
      linarith [ha w hw]
  simpa [Matrix.mulVec_single] using clipped_joint_nonincrease g α hα a (Pi.single v δ) H hh hs ha hafter

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EnergyTransport

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma energyArgument_active (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hroot : RootIdentity g s α st) (hlayer : LayerIdentity g st)
    (j : ℕ) (hj : j ≤ st.top) (v : Fin n) (hv : v ∈ (st.frames j).active) :
    energyArgument g s α st j v = (st.frames j).residual v := by
  unfold energyArgument
  rw [global_active_identity g s α st hreg hroot hlayer j hj v hv]
  simp [hv]

lemma thresholdSum_same (st u : RecursiveState n) (j : ℕ)
    (hq : ∀ k ≤ j, (u.frames k).q = (st.frames k).q) : thresholdSum u j = thresholdSum st j := by
  apply Finset.sum_congr rfl
  intro k hk
  exact hq k (Nat.le_of_lt (Finset.mem_range.mp hk))

lemma energyArgument_transport (g : InputGraph n) (s : Fin n) (α : ℝ) (st u : RecursiveState n) (j : ℕ)
    (hx : u.x = st.x) (hq : ∀ k ≤ j, (u.frames k).q = (st.frames k).q)
    (hH : (u.frames j).active = (st.frames j).active) (v : Fin n) :
    energyArgument g s α u j v = energyArgument g s α st j v := by
  unfold energyArgument birthAllowance
  rw [hx,thresholdSum_same st u j hq,hq j le_rfl,hH]

lemma budgetEnergy_transport (g : InputGraph n) (s : Fin n) (α : ℝ) (st u : RecursiveState n) (j : ℕ)
    (hx : u.x = st.x) (hq : ∀ k ≤ j, (u.frames k).q = (st.frames k).q)
    (hH : (u.frames j).active = (st.frames j).active) :
    budgetEnergy g s α u j = budgetEnergy g s α st j := by
  apply Finset.sum_congr rfl
  intro v _
  change max (energyArgument g s α u j v) 0 = max (energyArgument g s α st j v) 0
  rw [energyArgument_transport g s α st u j hx hq hH]

lemma energyArgument_joint (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (j : ℕ) (v : Fin n) :
    energyArgument g s α (jointUpdate g α st h) j v =
      energyArgument g s α st j v-(LocalPush.Lα g.graph α *ᵥ h) v := by
  have hq (k : ℕ) : ((jointUpdate g α st h).frames k).q = (st.frames k).q := by
    by_cases he : k ≤ st.top <;> simp [jointUpdate,he]
  have hH : ((jointUpdate g α st h).frames j).active = (st.frames j).active := by
    by_cases he : j ≤ st.top <;> simp [jointUpdate,he]
  unfold energyArgument birthAllowance
  rw [thresholdSum_same st _ j (fun k _ => hq k),hq j,hH]
  change residual g.graph α s (st.x+h) v-_
    = _
  rw [residual_addition]
  simp only [Pi.sub_apply]
  ring

lemma budgetEnergy_joint (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α ∧ α ≤ 1)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hlayer : LayerIdentity g st) (hnum : NumericalInvariant g st)
    (h : Fin n → ℝ) (j : ℕ) (hj : j ≤ st.top) (hh : ∀ v, 0 ≤ h v)
    (hs : ∀ v ∉ (st.frames j).active, h v = 0)
    (hr : ∀ v ∈ (st.frames j).active, (LocalPush.Lα g.graph α *ᵥ h) v ≤ (st.frames j).residual v) :
    budgetEnergy g s α (jointUpdate g α st h) j ≤ budgetEnergy g s α st j := by
  change (∑ v, max (energyArgument g s α (jointUpdate g α st h) j v) 0) ≤ _
  simp only [energyArgument_joint]
  apply clipped_joint_nonincrease g α hα _ h (st.frames j).active hh hs
  · intro v hv
    rw [energyArgument_active g s α st hreg hroot hlayer j hj v hv]
    exact ((hnum j hj).1 v ((hreg j hj).1 hv)).1
  · intro v hv
    rw [energyArgument_active g s α st hreg hroot hlayer j hj v hv]
    exact sub_nonneg.mpr (hr v hv)

lemma energyArgument_raw (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (t j : ℕ) (v w : Fin n) (δ : ℝ) :
    energyArgument g s α (rawExterior g α st t v δ) j w =
      energyArgument g s α st j w-LocalPush.Lα g.graph α w v*δ := by
  unfold energyArgument birthAllowance
  rw [thresholdSum_same st _ j (fun k _ => raw_q g α st t v δ k),raw_q,raw_active]
  change residual g.graph α s (Function.update st.x v (st.x v+δ)) w-_= _
  rw [residual_coordinate_update]
  simp only [Pi.sub_apply]
  ring

lemma budgetEnergy_raw_flow (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : α ≤ 1)
    (st : RecursiveState n) (t j : ℕ) (v : Fin n) (δ : ℝ) (hδ : 0 ≤ δ) :
    budgetEnergy g s α (rawExterior g α st t v δ) j ≤
      budgetEnergy g s α st j+(1-α)*LocalPush.deg g.graph v*δ := by
  change (∑ w, max (energyArgument g s α (rawExterior g α st t v δ) j w) 0) ≤ _
  simp only [energyArgument_raw]
  exact clipped_coordinate_flow g α hα _ v δ hδ

lemma budgetEnergy_refresh (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (T : Finset (Fin n)) (j : ℕ) :
    budgetEnergy g s α (refreshKeys g st T) j = budgetEnergy g s α st j := by
  apply budgetEnergy_transport g s α st (refreshKeys g st T) j rfl
  · intro k _; by_cases hk : k ≤ st.top <;> simp [refreshKeys,hk]
  · by_cases hj : j ≤ st.top <;> simp [refreshKeys,hj]

lemma budgetEnergy_debit (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (j t : ℕ) (w : ℝ≥0∞) : budgetEnergy g s α (debit st t w) j = budgetEnergy g s α st j := rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EnergyAdmission

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma energyArgument_admit_other (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (t j : ℕ) (v w : Fin n) (hj : j ≠ t) :
    energyArgument g s α (admitStage g st t v) j w = energyArgument g s α st j w := by
  obtain ⟨ht,hx,hq,hθ,hC,hH,hrest⟩ := admit_stage_fields g st t v
  exact energyArgument_transport g s α st _ j hx (fun k _ => hq k) (by simpa [hj] using hH j) w

lemma energyArgument_admit_current (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v w : Fin n) (hout : v ∉ (st.frames t).active) :
    energyArgument g s α (admitStage g st t v) t w = energyArgument g s α st t w+
      (if w = v then birthAllowance st t*LocalPush.deg g.graph v else 0) := by
  classical
  obtain ⟨ht,hx,hq,hθ,hC,hH,hrest⟩ := admit_stage_fields g st t v
  unfold energyArgument birthAllowance
  rw [hx,thresholdSum_same st _ t (fun k _ => hq k),hq t,hH t]
  simp only [ite_true]
  by_cases he : w = v
  · subst w
    simp [hout]
    ring
  · simp [Finset.mem_insert,he]

lemma budgetEnergy_admit_other (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (t j : ℕ) (v : Fin n) (hj : j ≠ t) :
    budgetEnergy g s α (admitStage g st t v) j = budgetEnergy g s α st j := by
  apply Finset.sum_congr rfl
  intro w _
  change max (energyArgument g s α (admitStage g st t v) j w) 0 = _
  rw [energyArgument_admit_other g s α st t j v w hj]
  rfl

lemma budgetEnergy_admit_current (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (hout : v ∉ (st.frames t).active) (hq : 0 ≤ (st.frames t).q) :
    budgetEnergy g s α (admitStage g st t v) t ≤
      budgetEnergy g s α st t+birthAllowance st t*LocalPush.deg g.graph v := by
  change (∑ w, max (energyArgument g s α (admitStage g st t v) t w) 0) ≤ _
  simp only [energyArgument_admit_current g s α st t v _ hout]
  apply clipped_admission
  unfold birthAllowance LocalPush.deg
  positivity

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.EnergyRawInside

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma budgetEnergy_raw_inside (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α ∧ α ≤ 1)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hlayer : LayerIdentity g st) (hnum : NumericalInvariant g st) (hparam : ParameterInvariant st)
    (t j : ℕ) (ht : t ≤ st.top) (hj : j < t) (v : Fin n) (hvt : v ∈ parentDomain st t)
    (δ : ℝ) (hδ : 0 ≤ δ) (hrδ : 5*LocalPush.deg g.graph v*δ ≤ (st.frames t).residual v) :
    budgetEnergy g s α (rawExterior g α st t v δ) j ≤ budgetEnergy g s α st j := by
  have hjs : j ≤ st.top := hj.le.trans ht
  have hvj : v ∈ (st.frames j).active := parent_domain_nested st hreg j t hj ht hvt
  have ha : ∀ w ∈ (st.frames j).active, 0 ≤ energyArgument g s α st j w := by
    intro w hw
    rw [energyArgument_active g s α st hreg hroot hlayer j hjs w hw]
    exact ((hnum j hjs).1 w ((hreg j hjs).1 hw)).1
  have hav : LocalPush.deg g.graph v*δ ≤ energyArgument g s α st j v := by
    rw [energyArgument_active g s α st hreg hroot hlayer j hjs v hvj]
    have hdom := layer_residual_dominance g st hreg hlayer hparam hnum j t hj.le ht v hvt
    have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
    nlinarith [mul_nonneg hd hδ]
  change (∑ w, max (energyArgument g s α (rawExterior g α st t v δ) j w) 0) ≤ _
  simp only [energyArgument_raw]
  exact clipped_coordinate_nonincrease g α hα _ (st.frames j).active v δ hδ hvj ha hav

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

-- Proof module: Solutions.EnergyExterior

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma budgetEnergy_exterior_bound (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α ∧ α ≤ 1)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hlayer : LayerIdentity g st) (hnum : NumericalInvariant g st) (hparam : ParameterInvariant st)
    (t j : ℕ) (ht : t ≤ st.top) (hj : j ≤ st.top) (v : Fin n)
    (hvt : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active)
    (δ : ℝ) (hδeq : δ = min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)) (hδ : 0 ≤ δ)
    (hrδ : 5*LocalPush.deg g.graph v*δ ≤ (st.frames t).residual v) :
    budgetEnergy g s α (exteriorPush g α st t v) j ≤ budgetEnergy g s α st j+
      (if t ≤ j then (1-α)*LocalPush.deg g.graph v*δ else 0)+
      (if relative st t v+δ = 3*(st.frames t).q/8 ∧ j = t then
        birthAllowance st j*LocalPush.deg g.graph v else 0) := by
  classical
  let base := rawExterior g α st t v δ
  have hq : (base.frames t).q = (st.frames t).q := raw_q g α st t v δ t
  have hbo : birthAllowance base t = birthAllowance st t := by unfold birthAllowance; rw [hq]
  have hbout : v ∉ (base.frames t).active := by simpa [base,raw_active] using hout
  rw [exterior_stages]
  simp only [←hδeq]
  rw [budgetEnergy_debit,budgetEnergy_refresh]
  by_cases ha : relative st t v+δ = 3*(st.frames t).q/8
  · simp only [ha,ite_true]
    by_cases he : j = t
    · subst j
      have hb := budgetEnergy_admit_current g s α base t v hbout (by rw [hq]; exact (hparam t ht).1.le)
      rw [hbo] at hb
      have hf := budgetEnergy_raw_flow g s α hα.2 st t t v δ hδ
      simp only [le_refl,ite_true,and_self,ha] at ⊢
      linarith
    · rw [budgetEnergy_admit_other g s α base t j v he]
      simp only [he,and_false,ite_false,add_zero]
      by_cases htj : t ≤ j
      · simp only [htj,ite_true]
        exact budgetEnergy_raw_flow g s α hα.2 st t j v δ hδ
      · simp only [htj,ite_false,add_zero]
        exact budgetEnergy_raw_inside g s α hα st hreg hroot hlayer hnum hparam t j ht (by omega) v hvt δ hδ hrδ
  · simp only [ha,ite_false,false_and,add_zero]
    by_cases htj : t ≤ j
    · simp only [htj,ite_true]
      exact budgetEnergy_raw_flow g s α hα.2 st t j v δ hδ
    · simp only [htj,ite_false,add_zero]
      exact budgetEnergy_raw_inside g s α hα st hreg hroot hlayer hnum hparam t j ht (by omega) v hvt δ hδ hrδ

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

-- Proof module: Solutions.EntryDrained

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma entry_safe (st : RecursiveState n) (hpc : (st.frames st.top).pc ≠ .beginEpisode) : EntryDrained st :=
  fun h => False.elim (hpc h)
lemma entry_none (st : RecursiveState n) (hp : pendingPush st = none) : EntryDrained st := fun _ => hp
lemma entry_PC_safe (st : RecursiveState n) (pc : NormalizePC) (hp : pc ≠ .beginEpisode) : EntryDrained (changePC st pc) := by
  apply entry_safe
  simpa [changePC,changeFrame] using hp
lemma entry_PC_none (st : RecursiveState n) (pc : NormalizePC) (hp : pendingPush st = none) : EntryDrained (changePC st pc) :=
  entry_none _ ((pending_PC st pc).trans hp)
lemma entry_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hp : (st.frames st.top).pc ≠ .beginEpisode) : EntryDrained (exteriorPush g α st t v) := by
  apply entry_safe
  simpa only [top_exterior,frame_pc_exterior] using hp
lemma entry_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (pc : NormalizePC)
    (hp : (st.frames st.top).pc ≠ .beginEpisode) (hn : pc ≠ .beginEpisode) :
    EntryDrained (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact entry_PC_safe _ pc hn
  · cases he : pendingPush st with
    | none => exact entry_PC_safe _ pc hn
    | some p => obtain ⟨t,v⟩ := p; exact entry_exterior g α st t v hp
lemma entry_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hs : StackInvariant st) (hi : EntryDrained st) : EntryDrained (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · rename_i ht
    apply entry_safe
    simpa [hs (st.top-1) (by omega)]

set_option maxHeartbeats 1000000 in
lemma entry_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hs : StackInvariant st) (hr : ReturnDrained st) (hi : EntryDrained st) :
    EntryDrained (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]; exact hi
  simp only [hc,ite_false]
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact entry_PC_safe _ _ (by simp)
    · split
      · exact entry_drain g α st _ (by simp [hpc]) (by simp)
      · rename_i hp
        have hn : pendingPush st = none := by cases h : pendingPush st <;> simp_all
        split <;> exact entry_PC_none _ _ hn
  | beginEpisode =>
    simp only [hpc]
    apply entry_safe
    simp [changeFrame,debit] <;> (try split_ifs) <;> simp
  | fullSolve =>
    simp only [hpc]
    split
    · exact entry_PC_safe _ _ (by simp)
    · split
      · exact entry_PC_safe _ _ (by simp)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact entry_PC_safe _ _ (by simp)
    · split
      · exact entry_PC_safe _ _ (by simp)
      · apply entry_safe; simp [freshFrame,emptyFrame]
  | leafDrain =>
    simp only [hpc]
    split
    · exact entry_PC_safe _ _ (by simp)
    · split
      · cases hp : pendingPush st with
        | none => exact entry_PC_safe _ _ (by simp)
        | some p => obtain ⟨t,v⟩ := p; exact entry_exterior g α st t v (by simp [hpc])
      · split
        · exact entry_PC_safe _ _ (by simp)
        · split
          · apply entry_safe; simp [changeFrame,refreshKeys,jointUpdate,debit,hpc]
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact entry_PC_safe _ _ (by simp)
    · split
      · exact entry_PC_safe _ _ (by simp)
      · exact entry_drain g α st _ (by simp [hpc]) (by simp)
  | finishEpisode =>
    have hp := hr (Or.inr hpc)
    simp only [hpc]
    split
    · exact entry_PC_safe _ _ (by simp)
    · split
      · exact entry_PC_safe _ _ (by simp)
      · apply entry_none
        rw [pending_metadata _ st.top _ rfl,pending_finish]
        exact hp
  | restartDrain =>
    simp only [hpc]
    split
    · exact entry_PC_safe _ _ (by simp)
    · split
      · exact entry_drain g α st _ (by simp [hpc]) (by simp)
      · rename_i hp
        have hn : pendingPush st = none := by cases h : pendingPush st <;> simp_all
        apply entry_none
        rw [pending_metadata _ st.top _ rfl]
        exact hn
  | normal => simp only [hpc]; exact entry_end g α _ hs hi
  | interrupted => simp only [hpc]; exact entry_end g α _ hs hi

lemma entry_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    EntryDrained (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => apply entry_safe; simp [recursiveRun,recursiveInit,freshFrame,emptyFrame]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      entry_step m g s α ℓ schedule _ (stack_run m g s α q ℓ schedule t)
        (return_drained_run m g s α q ℓ schedule t) ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetEnergyInvariant

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma budgetEnergy_changeFrame (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (k j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hq : (f (st.frames k)).q = (st.frames k).q)
    (hH : (f (st.frames k)).active = (st.frames k).active) :
    budgetEnergy g s α (changeFrame st k f) j = budgetEnergy g s α st j := by
  apply budgetEnergy_transport g s α st (changeFrame st k f) j rfl
  · intro i _; exact observe_changeFrame (fun f => f.q) st k f hq i
  · exact observe_changeFrame (fun f => f.active) st k f hH j

lemma budget_energy_metadata (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hi : BudgetEnergyInvariant g s α st) (k : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hq : (f (st.frames k)).q = (st.frames k).q)
    (hH : (f (st.frames k)).active = (st.frames k).active)
    (hQ : (f (st.frames k)).Q = (st.frames k).Q)
    (hW : (f (st.frames k)).W = (st.frames k).W)
    (hB : (f (st.frames k)).openBudget = true → (st.frames k).openBudget = true) :
    BudgetEnergyInvariant g s α (changeFrame st k f) := by
  intro j hj hb
  have hjs : j ≤ st.top := hj
  rw [budgetEnergy_changeFrame g s α st k j f hq hH]
  rw [observe_changeFrame (fun f => f.Q) st k f hQ j,
    observe_changeFrame (fun f => f.W) st k f hW j]
  apply hi j hjs
  by_cases he : j = k
  · subst j
    apply hB
    simpa [changeFrame] using hb
  · simpa [changeFrame,he] using hb

lemma budget_energy_PC (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hi : BudgetEnergyInvariant g s α st) (pc : NormalizePC) :
    BudgetEnergyInvariant g s α (changePC st pc) :=
  budget_energy_metadata g s α st hi st.top _ rfl rfl rfl rfl (fun h => h)

lemma budget_energy_finish (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hi : BudgetEnergyInvariant g s α st) : BudgetEnergyInvariant g s α (finishEpisode st) := by
  unfold finishEpisode
  apply budget_energy_metadata
  · exact hi
  · rfl
  · rfl
  · rfl
  · rfl
  · simp

lemma budget_energy_refresh (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hi : BudgetEnergyInvariant g s α st) (T : Finset (Fin n)) :
    BudgetEnergyInvariant g s α (refreshKeys g st T) := by
  intro j hj hb
  have hjs : j ≤ st.top := hj
  rw [budgetEnergy_refresh]
  rw [(refresh_budget_fields g st T j).1,(refresh_budget_fields g st T j).2]
  exact hi j hjs (by simpa [refreshKeys,hjs] using hb)

lemma budget_energy_init (g : InputGraph n) (s : Fin n) (α q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    BudgetEnergyInvariant g s α (recursiveInit g s q ℓ schedule) := by
  intro j hj hb
  have hz : j = 0 := by change j ≤ 0 at hj; omega
  subst j
  simp [recursiveInit,freshFrame,emptyFrame] at hb

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetEnergyUpdates

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma budget_energy_solve (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hlayer : LayerIdentity g st) (hparam : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hi : BudgetEnergyInvariant g s α st)
    (T : Finset (Fin n)) (hT : T ⊆ (st.frames st.top).active)
    (hpos : ∀ v ∈ T, 0 < g.graph.degree v) (b : Fin n → ℝ)
    (hb : ∀ v ∈ T, 0 ≤ b v) (hbr : ∀ v ∈ T, b v ≤ (st.frames st.top).residual v) :
    BudgetEnergyInvariant g s α (jointUpdate g α st (solveOn g α T b)) := by
  obtain ⟨hh,hres⟩ := principal_ancestor_update_bounds g α hα st hreg hlayer hparam hnum T hT hpos b hb hbr
  intro j hj hopen
  have hjs : j ≤ st.top := hj
  have hbp : (st.frames j).openBudget = true := by simpa [jointUpdate,hjs] using hopen
  have hsupport : ∀ v ∉ (st.frames j).active, solveOn g α T b v = 0 := by
    intro v hv
    apply solveOn_outside
    intro hvt
    exact hv (active_subset_between st hreg j st.top hjs le_rfl (hT hvt))
  have hE := budgetEnergy_joint g s α ⟨hα.1.le,hα.2.le⟩ st hreg hroot hlayer hnum _ j hjs hh hsupport
    (fun v hv => hres j hjs v ((hreg j hjs).1 hv))
  simpa [jointUpdate,hjs] using hE.trans (hi j hjs hbp)

lemma budget_energy_exterior (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α ∧ α ≤ 1)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hlayer : LayerIdentity g st) (hnum : NumericalInvariant g st) (hparam : ParameterInvariant st)
    (hi : BudgetEnergyInvariant g s α st) (t : ℕ) (ht : t ≤ st.top) (v : Fin n)
    (hvt : v ∈ parentDomain st t) (hout : v ∉ (st.frames t).active) (hd : 0 < g.graph.degree v) :
    BudgetEnergyInvariant g s α (exteriorPush g α st t v) := by
  let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
    (3*(st.frames t).q/8-relative st t v)
  have hd' : 0 < LocalPush.deg g.graph v := by unfold LocalPush.deg; exact_mod_cast hd
  have hn := (hnum t ht).1 v hvt
  have hclip := crossing_push_bounds (LocalPush.deg g.graph v) (st.frames t).q
    ((st.frames t).residual v) (relative st t v) hd' (hparam t ht).1 hn.1
    ⟨hn.2.1,(hn.2.2.2 hout).le⟩
  intro j hj hopen
  have hjs : j ≤ st.top := by simpa using hj
  have ho := congrArg (fun z => z.2.2.1) (exterior_parameters g α st t v j)
  have hbp : (st.frames j).openBudget = true := ho.symm.trans hopen
  have hfields := exterior_budget_fields g α st t v j hjs
  have hE := budgetEnergy_exterior_bound g s α hα st hreg hroot hlayer hnum hparam t j ht hjs v
    hvt hout δ rfl hclip.1 (sub_nonneg.mp hclip.2.1)
  dsimp only at hfields
  simp only [hbp,true_and,and_true] at hfields
  rw [hfields.1,hfields.2]
  have hh := hi j hjs hbp
  change _ ≤ _+((st.frames j).W+
    (if t ≤ j then (1-α)*LocalPush.deg g.graph v*δ else 0)+
    (if relative st t v+δ = 3*(st.frames t).q/8 ∧ j = t then
      birthAllowance st j*LocalPush.deg g.graph v else 0))
  linarith

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetEnergySolves

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma budget_energy_cached_solve (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (ℓ : ℕ) (st : RecursiveState n) (hreg : RegionInvariant st) (hlayer : LayerIdentity g st)
    (hparam : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hroot : RootIdentity g s α st) (hi : BudgetEnergyInvariant g s α st)
    (hkeys : KeysInvariant g st) (hbudget : BudgetInvariant st)
    (hc : CacheControlInvariant ℓ st) (hpc : (st.frames st.top).pc = .leafDrain)
    (hpos : ∀ v ∈ (st.frames st.top).cache ∪ (st.frames st.top).high, 0 < g.graph.degree v) :
    let C := (st.frames st.top).cache ∪ (st.frames st.top).high
    let u := changeFrame st st.top (fun f => {f with cache := C})
    BudgetEnergyInvariant g s α (jointUpdate g α u (solveOn g α C
      (fun v => (st.frames st.top).residual v-(st.frames st.top).theta*LocalPush.deg g.graph v))) := by
  classical
  let C := (st.frames st.top).cache ∪ (st.frames st.top).high
  let u := changeFrame st st.top (fun f => {f with cache := C})
  let b := fun v => (st.frames st.top).residual v-(st.frames st.top).theta*LocalPush.deg g.graph v
  have hlevel : st.top = ℓ := (hc st.top le_rfl).2.1 hpc
  have hopen : (st.frames st.top).openBudget = true := by
    simpa [hpc,budgetPC] using hbudget st.top le_rfl
  have hθ : 0 ≤ (st.frames st.top).theta :=
    ((hparam st.top le_rfl).1.trans_le ((hparam st.top le_rfl).2.2 hopen)).le
  have hd (v : Fin n) : 0 ≤ (st.frames st.top).theta*LocalPush.deg g.graph v := by
    apply mul_nonneg hθ
    unfold LocalPush.deg
    positivity
  have hC : C ⊆ (st.frames st.top).active := Finset.union_subset_iff.mpr
    ⟨(hreg st.top le_rfl).2.2.2,(hreg st.top le_rfl).2.2.1⟩
  have hbound (v : Fin n) (hv : v ∈ C) :
      (st.frames st.top).theta*LocalPush.deg g.graph v ≤ (st.frames st.top).residual v := by
    obtain hv|hv := Finset.mem_union.mp hv
    · exact (hnum st.top le_rfl).2 v hv
    · have hh := ((hkeys st.top le_rfl).2 v).mp hv
      have hr := hh.2
      nlinarith [hd v]
  have hnu : NumericalInvariant g u := by
    apply numerical_changeFrame g st hnum st.top _ rfl rfl rfl rfl
    intro _ v hv
    exact hbound v hv
  have hru : RegionInvariant u := by
    apply region_changeFrame st st.top _ hreg rfl (Finset.Subset.refl _)
    · exact (hreg st.top le_rfl).2.2.1
    · exact hC
  have hlu : LayerIdentity g u := layer_changeFrame g st st.top _ rfl hlayer
  have hpu : ParameterInvariant u := parameters_control st hparam st.top _ rfl
  have hCu : C ⊆ (u.frames u.top).active := by simpa [u,changeFrame] using hC
  have hb : ∀ v ∈ C, 0 ≤ b v := fun v hv => sub_nonneg.mpr (hbound v hv)
  have hbr : ∀ v ∈ C, b v ≤ (u.frames u.top).residual v := by
    intro v hv
    simpa [u,changeFrame,b] using sub_le_self ((st.frames st.top).residual v) (hd v)
  have hrootu : RootIdentity g s α u := root_identity_changeFrame g s α st st.top _ rfl rfl rfl hroot
  have hiu : BudgetEnergyInvariant g s α u := budget_energy_metadata g s α st hi st.top _
    rfl rfl rfl rfl (fun h => h)
  exact budget_energy_solve g s α hα u hru hrootu hlu hpu hnu hiu C hCu hpos b hb hbr

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetEnergyControl

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma budget_energy_new (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hi : BudgetEnergyInvariant g s α st) (c : NormalizeFrame n) (hc : c.openBudget = false) :
    BudgetEnergyInvariant g s α
      {st with top := st.top+1,frames := Function.update st.frames (st.top+1) c} := by
  classical
  intro j hj hb
  change j ≤ st.top+1 at hj
  have hne : j ≠ st.top+1 := by intro he; subst j; simpa [hc] using hb
  have hjs : j ≤ st.top := by omega
  have he : budgetEnergy g s α {st with top := st.top+1,frames := Function.update st.frames (st.top+1) c} j =
      budgetEnergy g s α st j := by
    apply budgetEnergy_transport g s α st
      {st with top := st.top+1,frames := Function.update st.frames (st.top+1) c} j rfl
    · intro k hk
      have hh : k ≠ st.top+1 := by omega
      simp [hh]
    · simp [hne]
  rw [he]
  simpa [hne] using hi j hjs (by simpa [hne] using hb)

lemma budget_energy_end (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hi : BudgetEnergyInvariant g s α st) : BudgetEnergyInvariant g s α (endCall g α st) := by
  unfold endCall
  dsimp only
  split
  · exact hi
  · intro j hj hb
    exact hi j (hj.trans (Nat.sub_le _ _)) hb

lemma budget_energy_episode (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n)
    (hi : BudgetEnergyInvariant g s α st) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hlayer : LayerIdentity g st) (hnum : NumericalInvariant g st) (hkeys : KeysInvariant g st)
    (hparam : ParameterInvariant st) (hmono : ∀ j < st.top, (st.frames j).q ≤ (st.frames (j+1)).q)
    (hp : pendingPush st = none) (f : NormalizeFrame n → NormalizeFrame n)
    (hq : (f (st.frames st.top)).q = (st.frames st.top).q)
    (hH : (f (st.frames st.top)).active = (st.frames st.top).active)
    (hQ : (∑ v ∈ (st.frames st.top).active, (st.frames st.top).residual v) ≤ (f (st.frames st.top)).Q)
    (hW : (f (st.frames st.top)).W = 0) :
    BudgetEnergyInvariant g s α (changeFrame st st.top f) := by
  classical
  intro j hj hb
  have hjs : j ≤ st.top := hj
  rw [budgetEnergy_changeFrame g s α st st.top j f hq hH]
  by_cases he : j = st.top
  · subst j
    simp only [changeFrame,Function.update_self,hW,add_zero]
    rw [budgetEnergy_drained g s α st hreg hroot hlayer hnum hkeys hparam hmono hp st.top le_rfl]
    exact hQ
  · have hbp : (st.frames j).openBudget = true := by simpa [changeFrame,he] using hb
    simpa [changeFrame,he] using hi j hjs hbp

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetEnergyStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma budget_energy_pending (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α ∧ α ≤ 1)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hlayer : LayerIdentity g st) (hnum : NumericalInvariant g st) (hparam : ParameterInvariant st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st)
    (hi : BudgetEnergyInvariant g s α st) (t : ℕ) (v : Fin n) (hp : pendingPush st = some (t,v)) :
    BudgetEnergyInvariant g s α (exteriorPush g α st t v) := by
  obtain ⟨ht,hm⟩ := pending_push_member st t v hp
  obtain ⟨hv,hout⟩ := Finset.mem_sdiff.mp ((hreg t ht).2.1 hm)
  exact budget_energy_exterior g s α hα st hreg hroot hlayer hnum hparam hi t ht v hv hout
    (isolate_pending_positive g st hiso hkeys t v hp)

lemma budget_energy_drain (g : InputGraph n) (s : Fin n) (α : ℝ) (hα : 0 ≤ α ∧ α ≤ 1)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hroot : RootIdentity g s α st)
    (hlayer : LayerIdentity g st) (hnum : NumericalInvariant g st) (hparam : ParameterInvariant st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st)
    (hi : BudgetEnergyInvariant g s α st) (pc : NormalizePC) :
    BudgetEnergyInvariant g s α (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact budget_energy_PC g s α _ hi pc
  · cases hp : pendingPush st with
    | none => exact budget_energy_PC g s α _ hi pc
    | some p =>
      obtain ⟨t,v⟩ := p
      exact budget_energy_pending g s α hα st hreg hroot hlayer hnum hparam hkeys hiso hi t v hp

set_option maxHeartbeats 1500000 in
lemma budget_energy_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hroot : RootIdentity g s α st) (hlayer : LayerIdentity g st)
    (hparam : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st) (hbudget : BudgetInvariant st)
    (hc : CacheControlInvariant ℓ st) (hs : StackInvariant st) (hth : ThresholdRelation st)
    (he : EntryDrained st) (hi : BudgetEnergyInvariant g s α st) :
    BudgetEnergyInvariant g s α (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hcomp : componentComplete st
  · simp only [hcomp,ite_true]; exact hi
  simp only [hcomp,ite_false]
  have hdrain := budget_energy_drain g s α ⟨hα.1.le,hα.2.le⟩ st hreg hroot hlayer hnum hparam hkeys hiso hi
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact budget_energy_PC g s α _ hi _
    · split
      · exact hdrain _
      · split <;> exact budget_energy_PC g s α _ hi _
  | beginEpisode =>
    simp only [hpc]
    apply budget_energy_episode
    · exact hi
    · exact hreg
    · exact hroot
    · exact hlayer
    · exact hnum
    · exact hkeys
    · exact hparam
    · exact open_threshold_mono st hs hbudget hparam hth
    · exact he hpc
    · rfl
    · rfl
    · exact le_max_left _ _
    · rfl
  | fullSolve =>
    simp only [hpc]
    split
    · exact budget_energy_PC g s α _ hi _
    · split
      · rename_i hg
        have hsolve := budget_energy_solve g s α hα st hreg hroot hlayer hparam hnum hi
          (st.frames st.top).active (Finset.Subset.refl _) hg.2 (st.frames st.top).residual
          (fun v hv => ((hnum st.top le_rfl).1 v ((hreg st.top le_rfl).1 hv)).1) (fun _ _ => le_rfl)
        apply budget_energy_PC
        exact budget_energy_refresh g s α _ hsolve _
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact budget_energy_PC g s α _ hi _
    · split
      · exact budget_energy_PC g s α _ hi _
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild,childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : BudgetEnergyInvariant g s α up := budget_energy_metadata g s α u hi st.top _
          rfl rfl rfl rfl (fun h => h)
        exact budget_energy_new g s α up hup c rfl
  | leafDrain =>
    simp only [hpc]
    split
    · exact budget_energy_PC g s α _ hi _
    · split
      · cases hp : pendingPush st with
        | none => exact budget_energy_PC g s α _ hi _
        | some p =>
          obtain ⟨t,v⟩ := p
          exact budget_energy_pending g s α ⟨hα.1.le,hα.2.le⟩ st hreg hroot hlayer hnum hparam hkeys hiso hi t v hp
      · split
        · exact budget_energy_PC g s α _ hi _
        · split
          · rename_i hg
            have hsolve := budget_energy_cached_solve g s α hα ℓ st hreg hlayer hparam hnum hroot hi
              hkeys hbudget hc hpc hg.2
            exact budget_energy_refresh g s α _ hsolve _
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact budget_energy_PC g s α _ (budget_energy_finish g s α _ hi) _
    · split
      · exact budget_energy_PC g s α _ (budget_energy_finish g s α _ hi) _
      · exact hdrain _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact budget_energy_PC g s α _ (budget_energy_finish g s α _ hi) _
    · split
      · exact budget_energy_PC g s α _ (budget_energy_finish g s α _ hi) _
      · apply budget_energy_metadata
        · exact budget_energy_finish g s α _ hi
        · rfl
        · rfl
        · rfl
        · rfl
        · exact fun h => h
  | restartDrain =>
    simp only [hpc]
    split
    · exact budget_energy_PC g s α _ hi _
    · split
      · exact hdrain _
      · apply budget_energy_metadata
        · exact hi
        · rfl
        · rfl
        · rfl
        · rfl
        · exact fun h => h
  | normal => simp only [hpc]; exact budget_energy_end g s α _ hi
  | interrupted => simp only [hpc]; exact budget_energy_end g s α _ hi

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BudgetMass

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma budget_energy_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    BudgetEnergyInvariant g s α (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using budget_energy_init g s α q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      budget_energy_step m g s α hα ℓ schedule _
        (region_run m g s α q ℓ schedule t)
        (root_identity_run m g s α q ℓ schedule t)
        (layer_run m g s α q ℓ schedule t)
        (parameters_run m g s α q hq ℓ schedule t)
        (numerical_run m g s α q hα hq hs ℓ schedule t)
        (keys_run m g s α q hq.le ℓ schedule t)
        (isolate_run m g s α q hs ℓ schedule t)
        (budget_run m g s α q ℓ schedule t)
        (cache_run m g s α q ℓ schedule t)
        (stack_run m g s α q ℓ schedule t)
        (threshold_relation_run m g s α q ℓ schedule t)
        (entry_run m g s α q ℓ schedule t) ih

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open NearlyOptimalPPR.Computation

theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    BudgetEnergyInvariant g s α (recursiveRun m g s α q ℓ schedule t) := by
  exact budget_energy_run m g s α q hα hq hs ℓ schedule t

