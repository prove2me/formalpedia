-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_numerical_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:34:42.116424+00:00
-- url     : https://prove2.me/submissions/0b0ddec3-0927-4f10-b267-6f0a8ae8e676

import Definitions.Def_NearlyOptimalPPR_Computation_proof_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains

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

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RegionInvariants

set_option autoImplicit false
open Finset
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma active_subset_root (st : RecursiveState n) (hi : RegionInvariant st)
    (j : ℕ) (hj : j ≤ st.top) : (st.frames j).active ⊆ (st.frames 0).active := by
  induction j with
  | zero => exact Finset.Subset.refl _
  | succ j ih =>
    have hh := (hi (j+1) hj).1
    have hp : parentDomain st (j+1) = (st.frames j).active := by simp [parentDomain]
    rw [hp] at hh
    exact hh.trans (ih (Nat.le_of_succ_le hj))

lemma region_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ)
    (schedule : BlockSchedule) : RegionInvariant (recursiveInit g s q ℓ schedule) := by
  intro i hi
  have hi0 : i = 0 := by simpa only [recursiveInit, Nat.le_zero] using hi
  subst i
  simp [recursiveInit, freshFrame, emptyFrame, parentDomain]

@[simp] lemma refresh_active (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).active = (st.frames i).active := by
  by_cases hi : i ≤ st.top <;> simp [refreshKeys,hi]

@[simp] lemma refresh_parentDomain (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    parentDomain (refreshKeys g st T) i = parentDomain st i := by
  unfold parentDomain
  split <;> simp

lemma region_refresh (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (hi : RegionInvariant st) : RegionInvariant (refreshKeys g st T) := by
  intro i hle
  have hle' : i ≤ st.top := hle
  have hh := hi i hle'
  refine ⟨?_,?_,?_,?_⟩
  · simpa using hh.1
  · rw [refresh_parentDomain, refresh_active]
    simp only [refreshKeys, if_pos hle']
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hh.2.1 ((Finset.mem_sdiff.mp hv).1)
    · have hv' := (Finset.mem_filter.mp hv).2
      exact Finset.mem_sdiff.mpr ⟨hv'.1,hv'.2.1⟩
  · rw [refresh_active]
    simp only [refreshKeys, if_pos hle']
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hh.2.2.1 ((Finset.mem_sdiff.mp hv).1)
    · exact ((Finset.mem_filter.mp hv).2).1
  · simpa only [refreshKeys, if_pos hle'] using hh.2.2.2

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

lemma region_debit (st : RecursiveState n) (producer : ℕ) (cost : ℝ≥0∞)
    (hi : RegionInvariant st) : RegionInvariant (debit st producer cost) := hi

lemma region_changePC (st : RecursiveState n) (pc : NormalizePC)
    (hi : RegionInvariant st) : RegionInvariant (changePC st pc) := by
  refine region_same st (changePC st pc) rfl ?_ ?_ ?_ ?_ hi
  all_goals intro i; by_cases he : i = st.top <;> simp [changePC,changeFrame,he]

lemma region_finishEpisode (st : RecursiveState n)
    (hi : RegionInvariant st) : RegionInvariant (finishEpisode st) := by
  refine region_same st (finishEpisode st) rfl ?_ ?_ ?_ ?_ hi
  all_goals intro i; by_cases he : i = st.top <;> simp [finishEpisode,changeFrame,he]

lemma parentDomain_mono (st st' : RecursiveState n)
    (ha : ∀ i, (st.frames i).active ⊆ (st'.frames i).active) :
    ∀ i, parentDomain st i ⊆ parentDomain st' i := by
  intro i
  unfold parentDomain
  split
  · exact Finset.Subset.refl _
  · exact ha _

lemma region_refresh_of_growth (g : InputGraph n) (st st' : RecursiveState n)
    (T : Finset (Fin n)) (hi : RegionInvariant st) (ht : st'.top = st.top)
    (ha : ∀ i, (st.frames i).active ⊆ (st'.frames i).active)
    (hnew : ∀ i, (st'.frames i).active ⊆ (st.frames i).active ∪ T)
    (hvalid : ∀ i ≤ st.top, (st'.frames i).active ⊆ parentDomain st' i)
    (he : ∀ i, (st'.frames i).exterior ⊆ (st.frames i).exterior)
    (hh : ∀ i, (st'.frames i).high ⊆ (st.frames i).high)
    (hc : ∀ i, (st'.frames i).cache ⊆ (st.frames i).cache) :
    RegionInvariant (refreshKeys g st' T) := by
  intro i hle
  have hle' : i ≤ st'.top := hle
  have hle0 : i ≤ st.top := ht ▸ hle'
  have hs := hi i hle0
  refine ⟨?_,?_,?_,?_⟩
  · simpa using hvalid i hle0
  · rw [refresh_parentDomain,refresh_active]
    simp only [refreshKeys,if_pos hle']
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have ho := Finset.mem_sdiff.mp hv
      have hold := Finset.mem_sdiff.mp (hs.2.1 (he i ho.1))
      refine Finset.mem_sdiff.mpr ⟨parentDomain_mono st st' ha i hold.1, ?_⟩
      intro hv'
      rcases Finset.mem_union.mp (hnew i hv') with hv' | hv'
      · exact hold.2 hv'
      · exact ho.2 hv'
    · have hn := (Finset.mem_filter.mp hv).2
      exact Finset.mem_sdiff.mpr ⟨hn.1,hn.2.1⟩
  · rw [refresh_active]
    simp only [refreshKeys,if_pos hle']
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ha i (hs.2.2.1 (hh i (Finset.mem_sdiff.mp hv).1))
    · exact (Finset.mem_filter.mp hv).2.1
  · have hcache := (hc i).trans hs.2.2.2 |>.trans (ha i)
    simpa only [refreshKeys,if_pos hle'] using hcache

lemma region_insert_refresh (g : InputGraph n) (st : RecursiveState n) (t : ℕ)
    (v : Fin n) (T : Finset (Fin n)) (hi : RegionInvariant st)
    (hv : v ∈ parentDomain st t) (hvt : v ∈ T) :
    RegionInvariant (refreshKeys g (changeFrame st t (fun f => {f with active := insert v f.active})) T) := by
  let u := changeFrame st t (fun f => {f with active := insert v f.active})
  have ha : ∀ i, (st.frames i).active ⊆ (u.frames i).active := by
    intro i
    by_cases he : i = t <;> simp [u,changeFrame,he]
  apply region_refresh_of_growth g st u T hi rfl ha
  · intro i
    by_cases he : i = t
    · simp only [u,changeFrame,he,Function.update_self]
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Finset.mem_union_right _ hvt
      · exact Finset.mem_union_left _ hw
    · simp [u,changeFrame,he]
  · intro i hle
    have hm := parentDomain_mono st u ha i
    by_cases he : i = t
    · subst i
      simp only [u,changeFrame,Function.update_self]
      apply Finset.insert_subset
      · exact hm hv
      · exact ((hi t hle).1).trans hm
    · simpa [u,changeFrame,he] using ((hi i hle).1).trans hm
  all_goals intro i; by_cases he : i = t <;> simp [u,changeFrame,he]

lemma region_jointUpdate (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (hi : RegionInvariant st) : RegionInvariant (jointUpdate g α st h) := by
  refine region_same st (jointUpdate g α st h) rfl ?_ ?_ ?_ ?_ hi
  all_goals intro i; by_cases he : i ≤ st.top <;> simp [jointUpdate,he]

lemma region_after_admission (g : InputGraph n) (st st' : RecursiveState n)
    (t : ℕ) (v : Fin n) (T : Finset (Fin n)) (hi : RegionInvariant st)
    (hv : v ∈ parentDomain st t) (hvt : v ∈ T) (ht : st'.top = st.top)
    (hA : ∀ i, (st'.frames i).active =
      if i = t then insert v (st.frames i).active else (st.frames i).active)
    (hE : ∀ i, (st'.frames i).exterior = (st.frames i).exterior)
    (hH : ∀ i, (st'.frames i).high = (st.frames i).high)
    (hC : ∀ i, (st'.frames i).cache = (st.frames i).cache) :
    RegionInvariant (refreshKeys g st' T) := by
  have ha : ∀ i, (st.frames i).active ⊆ (st'.frames i).active := by
    intro i
    rw [hA]
    split <;> simp
  apply region_refresh_of_growth g st st' T hi ht ha
  · intro i
    rw [hA]
    split
    · exact Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ hvt,Finset.subset_union_left⟩
    · exact Finset.subset_union_left
  · intro i hle
    have hm := parentDomain_mono st st' ha i
    rw [hA]
    split
    · rename_i he
      subst i
      exact Finset.insert_subset_iff.mpr ⟨hm hv,((hi t hle).1).trans hm⟩
    · exact ((hi i hle).1).trans hm
  · intro i; rw [hE]
  · intro i; rw [hH]
  · intro i; rw [hC]

lemma changeFrame_regions_same (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n)
    (hf : frameRegions (f (st.frames j)) = frameRegions (st.frames j)) :
    ∀ i, frameRegions ((changeFrame st j f).frames i) = frameRegions (st.frames i) := by
  intro i
  by_cases he : i = j <;> simp [changeFrame,he,hf]


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

lemma region_controlFrame (st : RecursiveState n) (j : ℕ) (hj : j ≤ st.top)
    (f : NormalizeFrame n → NormalizeFrame n) (hi : RegionInvariant st)
    (hA : (f (st.frames j)).active = (st.frames j).active)
    (hE : (f (st.frames j)).exterior = (st.frames j).exterior)
    (hH : (f (st.frames j)).high = (st.frames j).high)
    (hC : (f (st.frames j)).cache = (st.frames j).cache) :
    RegionInvariant (changeFrame st j f) := by
  apply region_changeFrame st j f hi hA
  · rw [hE]
  · rw [hH]
    exact (hi j hj).2.2.1
  · rw [hC]
    exact (hi j hj).2.2.2

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

lemma symm_rows_sdd {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hSymm : A.IsSymm)
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0) (hRow : ∀ i, 0 < ∑ j, A i j) :
    LocalPush.IsSDD A := by
  refine ⟨hSymm, ?_⟩
  intro i
  have he : ∑ j ∈ univ.erase i, |A i j| = -(∑ j ∈ univ.erase i, A i j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact abs_of_nonpos (hOff i j (Ne.symm (Finset.mem_erase.mp hj).1))
  rw [he, Finset.sum_erase_eq_sub (mem_univ i)]
  linarith [hRow i]

lemma principal_posDef {n : ℕ} (g : InputGraph n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (T : Finset (Fin n))
    (hT : ∀ v ∈ T, 0 < g.graph.degree v) :
    ((LocalPush.Lα g.graph α).submatrix (fun v : T => v.val) (fun v : T => v.val)).PosDef := by
  classical
  have he : (LocalPush.Lα g.graph α).submatrix (fun v : T => v.val) (fun v : T => v.val) =
      Matrix.diagonal (fun v : T => α * LocalPush.deg g.graph v.val) +
        (1-α) • ((g.graph.lapMatrix ℝ).submatrix (fun v : T => v.val) (fun v : T => v.val)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LocalPush.Lα, LocalPush.degM, LocalPush.adjM, SimpleGraph.lapMatrix, SimpleGraph.degMatrix, LocalPush.deg]
      ring
    · have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp [LocalPush.Lα, LocalPush.degM, LocalPush.adjM, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij']
  rw [he]
  apply Matrix.PosDef.add_posSemidef
  · apply Matrix.PosDef.diagonal
    intro i
    apply mul_pos hα.1
    unfold LocalPush.deg
    exact_mod_cast hT i.val i.property
  · exact ((g.graph.posSemidef_lapMatrix ℝ).submatrix _).smul (sub_nonneg.mpr hα.2.le)

lemma principal_SDDM {n : ℕ} (g : InputGraph n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (T : Finset (Fin n))
    (hT : ∀ v ∈ T, 0 < g.graph.degree v) :
    let A := (LocalPush.Lα g.graph α).submatrix (fun v : T => v.val) (fun v : T => v.val)
    A.PosDef ∧ LocalPush.IsSDD A ∧ (∀ i j, i ≠ j → A i j ≤ 0) := by
  have hh := principal_signs g α hα T hT
  refine ⟨principal_posDef g α hα T hT, ?_, hh.1⟩
  apply symm_rows_sdd _ _ hh.1 hh.2
  apply Matrix.IsSymm.submatrix
  exact (Matrix.isSymm_diagonal _).sub ((g.graph.isSymm_adjMatrix).smul (1-α))

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

-- Proof module: Solutions.LayerIdentity

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

/-- The relative residual identity (source equation (4)) between adjacent open calls. -/
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

/-- Coordinate update before the optional activation and child reference reset. -/
lemma raw_relative (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (δ : ℝ) (i : ℕ) (w : Fin n) :
    relative (rawExterior g α st t v δ) i w =
      relative st i w+(if w = v then δ else 0) := by
  classical
  by_cases hi : i = 0 <;> by_cases hw : w = v <;> by_cases ht : i ≤ st.top <;>
    simp [relative,rawExterior,hi,hw,ht] <;> ring

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

-- Proof module: Solutions.ParameterInvariant

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

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

lemma queued_push_positive (d q r y : ℝ) (hd : 0 < d) (hq : 0 < q)
    (hr : q*d < r) (hy : y < 3*q/8) :
    0 < min (r/(5*d)) (3*q/8-y) := by
  apply lt_min
  · exact div_pos (lt_trans (mul_pos hq hd) hr) (by positivity)
  · linarith

lemma activation_credit_nonnegative (d q r y : ℝ) (hd : 0 < d) (hq : 0 < q)
    (hr : 0 ≤ r) (hy : 0 ≤ y ∧ y ≤ 3*q/8) :
    q*d/2 ≤ r-5*d*min (r/(5*d)) (3*q/8-y)+q*d/2 := by
  have hh := (crossing_push_bounds d q r y hd hq hr hy).2.1
  linarith

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

lemma solve_update_nonnegative (g : InputGraph n) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (T : Finset (Fin n)) (hT : ∀ v ∈ T, 0 < g.graph.degree v)
    (b r : Fin n → ℝ) (hb : ∀ v ∈ T, 0 ≤ b v) (hr : ∀ v, 0 ≤ r v)
    (hbr : ∀ v ∈ T, b v ≤ r v) :
    ∀ v, 0 ≤ r v-(LocalPush.Lα g.graph α *ᵥ solveOn g α T b) v := by
  intro v
  by_cases hv : v ∈ T
  · rw [solveOn_exact g α hα T hT b v hv]
    exact sub_nonneg.mpr (hbr v hv)
  · have hh := solveOn_nonneg g α hα T hT b hb
    have hl := lap_outside_nonpositive g α hα.2.le T _ hh
      (fun w hw => solveOn_outside g α T b w hw) v hv
    linarith [hr v]

lemma solve_full_clears (g : InputGraph n) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (T : Finset (Fin n)) (hT : ∀ v ∈ T, 0 < g.graph.degree v)
    (r : Fin n → ℝ) (v : Fin n) (hv : v ∈ T) :
    r v-(LocalPush.Lα g.graph α *ᵥ solveOn g α T r) v = 0 := by
  rw [solveOn_exact g α hα T hT r v hv,sub_self]

lemma solve_threshold_clears (g : InputGraph n) (α θ : ℝ) (hα : 0 < α ∧ α < 1)
    (T : Finset (Fin n)) (hT : ∀ v ∈ T, 0 < g.graph.degree v)
    (r : Fin n → ℝ) (v : Fin n) (hv : v ∈ T) :
    r v-(LocalPush.Lα g.graph α *ᵥ solveOn g α T
      (fun w => r w-θ*LocalPush.deg g.graph w)) v = θ*LocalPush.deg g.graph v := by
  rw [solveOn_exact g α hα T hT _ v hv]
  ring

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NumericalInvariant

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma numerical_init (g : InputGraph n) (s : Fin n) (q : ℝ) (hq : 0 < q)
    (ℓ : ℕ) (schedule : BlockSchedule) : NumericalInvariant g (recursiveInit g s q ℓ schedule) := by
  classical
  intro i hi
  have he : i = 0 := by change i ≤ 0 at hi; omega
  subst i
  constructor
  · intro v hv
    simp [recursiveInit,freshFrame,emptyFrame,relative,LocalPush.e,Pi.single_apply]
    constructor <;> positivity
  · simp [recursiveInit,freshFrame,emptyFrame]

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

lemma raw_residual_nonnegative (g : InputGraph n) (α : ℝ) (hα : α ≤ 1)
    (st : RecursiveState n) (hreg : RegionInvariant st) (hlayer : LayerIdentity g st)
    (hparam : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (t : ℕ) (ht : t ≤ st.top) (v : Fin n) (hvt : v ∈ parentDomain st t)
    (hout : v ∉ (st.frames t).active) (δ : ℝ) (hδ : 0 ≤ δ)
    (hrδ : 5*LocalPush.deg g.graph v*δ ≤ (st.frames t).residual v)
    (i : ℕ) (his : i ≤ st.top) (w : Fin n) (hw : w ∈ parentDomain st i) :
    0 ≤ ((rawExterior g α st t v δ).frames i).residual w := by
  classical
  have hr := ((hnum i his).1 w hw).1
  have hflow : 0 ≤ (1-α)*δ := mul_nonneg (sub_nonneg.mpr hα) hδ
  have hd : 0 ≤ LocalPush.deg g.graph v := by unfold LocalPush.deg; positivity
  by_cases hwv : w = v
  · subst w
    by_cases hit : i < t
    · have hdom := layer_residual_dominance g st hreg hlayer hparam hnum i t hit.le ht v hvt
      have hn : 0 ≤ (st.frames i).residual v-LocalPush.deg g.graph v*δ := by
        nlinarith [mul_nonneg hd hδ]
      simpa [rawExterior,his,hit,hw] using hn
    · by_cases hie : i = t
      · subst i
        have hn : 0 ≤ (st.frames t).residual v-5*LocalPush.deg g.graph v*δ := sub_nonneg.mpr hrδ
        simpa [rawExterior,ht,hw] using hn
      · exact False.elim (hout (parent_domain_nested st hreg t i (by omega) his hw))
  · have hn : 0 ≤ (if w ∈ parentDomain st i ∧ g.graph.Adj w v then (1-α)*δ else 0) := by
      split <;> positivity
    simpa [rawExterior,his,hwv] using add_nonneg hr hn

lemma numerical_raw (g : InputGraph n) (α : ℝ) (hα : α ≤ 1)
    (ℓ : ℕ) (st : RecursiveState n) (hreg : RegionInvariant st) (hlayer : LayerIdentity g st)
    (hparam : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hc : CacheControlInvariant ℓ st) (hdepth : st.top ≤ ℓ)
    (t : ℕ) (ht : t ≤ st.top) (v : Fin n) (hvt : v ∈ parentDomain st t)
    (hout : v ∉ (st.frames t).active) (δ : ℝ) (hδ : 0 ≤ δ)
    (hrδ : 5*LocalPush.deg g.graph v*δ ≤ (st.frames t).residual v)
    (hcap : relative st t v+δ ≤ 3*(st.frames t).q/8) :
    RawNumericalInvariant g (rawExterior g α st t v δ) t v := by
  classical
  have hact (i : ℕ) : ((rawExterior g α st t v δ).frames i).active = (st.frames i).active := by
    by_cases hh : i ≤ st.top <;> simp [rawExterior,hh]
  have hp := parentDomain_same st (rawExterior g α st t v δ) hact
  intro i hle
  have his : i ≤ st.top := hle
  constructor
  · intro w hw
    rw [hp] at hw
    have hn := (hnum i his).1 w hw
    refine ⟨raw_residual_nonnegative g α hα st hreg hlayer hparam hnum t ht v hvt hout δ hδ hrδ i his w hw,?_,?_,?_⟩
    · rw [raw_relative]
      exact add_nonneg hn.2.1 (by split <;> positivity)
    · intro ha
      rw [hact] at ha
      rw [raw_relative]
      simp only [rawExterior,his,ite_true]
      exact (hn.2.2.1 ha).trans (le_add_of_nonneg_right (by split <;> positivity))
    · intro ha
      rw [hact] at ha
      rw [raw_relative]
      simp only [rawExterior,his,ite_true]
      by_cases hwv : w = v
      · subst w
        have he := inactive_push_level st hreg t i ht his v hvt hout hw ha
        subst i
        simpa using hcap
      · simpa [hwv] using hn.2.2.2 ha
  · intro w hw
    have hw' : w ∈ (st.frames i).cache := by simpa [rawExterior,his] using hw
    have hwv : w ≠ v := by
      intro he
      subst w
      have hie : i = ℓ := by
        by_contra hn
        have hz := (hc i his).1 hn
        rw [hz] at hw'
        simp at hw'
      have hti : t ≤ i := by omega
      exact hout (active_subset_between st hreg t i hti his ((hreg i his).2.2.2 hw'))
    have hb := (hnum i his).2 w hw'
    have hflow : 0 ≤ (if w ∈ parentDomain st i ∧ g.graph.Adj w v then (1-α)*δ else 0) := by
      split
      · exact mul_nonneg (sub_nonneg.mpr hα) hδ
      · exact le_rfl
    simpa [rawExterior,his,hwv] using hb.trans (le_add_of_nonneg_right hflow)

lemma numerical_of_raw (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hi : RawNumericalInvariant g st t v)
    (hn : relative st t v ≠ 3*(st.frames t).q/8) : NumericalInvariant g st := by
  intro i his
  refine ⟨?_,(hi i his).2⟩
  intro w hw
  have hh := (hi i his).1 w hw
  refine ⟨hh.1,hh.2.1,hh.2.2.1,?_⟩
  intro hout
  have hb := hh.2.2.2 hout
  by_cases he : i = t ∧ w = v
  · obtain ⟨hi,hw⟩ := he
    subst i
    subst w
    simp only [and_self,ite_true] at hb
    exact lt_of_le_of_ne hb hn
  · simpa only [he,ite_false] using hb

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorStages

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

/-- The optional admission following a completed clipped coordinate update. -/
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

-- Proof module: Solutions.NumericalAdmission

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
lemma numerical_admission (g : InputGraph n) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hparam : ParameterInvariant st)
    (t : ℕ) (ht : t ≤ st.top) (v : Fin n) (hvt : v ∈ parentDomain st t)
    (hout : v ∉ (st.frames t).active) (hraw : RawNumericalInvariant g st t v)
    (hcap : relative st t v = 3*(st.frames t).q/8) :
    NumericalInvariant g (admitStage g st t v) := by
  classical
  obtain ⟨htop,hx,hq,hθ,hC,hA,href,hr⟩ := admit_stage_fields g st t v
  have hcredit : 0 ≤ (st.frames t).q*LocalPush.deg g.graph v/2 := by
    apply div_nonneg
    · apply mul_nonneg (hparam t ht).1.le
      unfold LocalPush.deg
      positivity
    · norm_num
  intro i hle
  have his : i ≤ st.top := by simpa [htop] using hle
  constructor
  · intro w hw
    by_cases hnew : t < st.top ∧ i = t+1 ∧ w = v
    · obtain ⟨hlt,hi,hwv⟩ := hnew
      subst i
      subst w
      have hno : v ∉ (st.frames (t+1)).active := by
        intro ha
        have hm := (hreg (t+1) his).1 ha
        exact hout (by simpa [parentDomain] using hm)
      have hres := add_nonneg ((hraw t ht).1 v hvt).1 hcredit
      have hpos : 0 < 3*(st.frames (t+1)).q/8 := by
        have hh := (hparam (t+1) his).1
        positivity
      have hne : t+1 ≠ t := by omega
      simpa [admit_relative,hq,hr,hA,hlt,hne,hno] using And.intro hres hpos
    · have hwold : w ∈ parentDomain st i := by
        have hh := (admit_domain g st t i v w).mp hw
        rcases hh with hold|⟨hi,hwv⟩
        · exact hold
        · exact False.elim (hnew ⟨by omega,hi,hwv⟩)
      have hh := (hraw i his).1 w hwold
      by_cases hex : i = t ∧ w = v
      · obtain ⟨hi,hwv⟩ := hex
        subst i
        subst w
        have hres := add_nonneg hh.1 hcredit
        simpa [admit_relative,hq,hr,hA,hnew] using
          And.intro hres (And.intro hh.2.1 hcap.ge)
      · have hmem : w ∈ ((admitStage g st t v).frames i).active ↔ w ∈ (st.frames i).active := by
          rw [hA]
          by_cases hi : i = t
          · have hwv : w ≠ v := by intro he; exact hex ⟨hi,he⟩
            simp [hi,hwv]
          · simp [hi]
        have hstrict : w ∉ (st.frames i).active → relative st i w < 3*(st.frames i).q/8 := by
          intro ho
          simpa only [hex,ite_false] using hh.2.2.2 ho
        have hn := And.intro hh.1 (And.intro hh.2.1 (And.intro hh.2.2.1 hstrict))
        simpa only [admit_relative,hnew,ite_false,hq,hr,hex,add_zero,hmem] using hn
  · intro w hw
    rw [hC] at hw
    have hex : ¬(i = t ∧ w = v) := by
      rintro ⟨hi,hwv⟩
      subst i
      subst w
      exact hout ((hreg t ht).2.2.2 hw)
    have hnew : ¬(t < st.top ∧ i = t+1 ∧ w = v) := by
      rintro ⟨hlt,hi,hwv⟩
      subst i
      subst w
      have hm := (hreg (t+1) his).1 ((hreg (t+1) his).2.2.2 hw)
      exact hout (by simpa [parentDomain] using hm)
    simpa only [hθ,hr,hnew,hex,ite_false,add_zero] using (hraw i his).2 w hw

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NumericalControl

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma numerical_transport (g : InputGraph n) (st u : RecursiveState n)
    (hi : NumericalInvariant g st) (ht : u.top ≤ st.top) (hx : u.x = st.x)
    (hf : ∀ i, numericalView (u.frames i) = numericalView (st.frames i)) : NumericalInvariant g u := by
  have hfields (i : ℕ) : (u.frames i).q = (st.frames i).q ∧
      (u.frames i).theta = (st.frames i).theta ∧
      (u.frames i).active = (st.frames i).active ∧
      (u.frames i).cache = (st.frames i).cache ∧
      (u.frames i).reference = (st.frames i).reference ∧
      (u.frames i).residual = (st.frames i).residual := by
    simpa only [numericalView,Prod.mk.injEq] using hf i
  have hq (i : ℕ) := (hfields i).1
  have hθ (i : ℕ) := (hfields i).2.1
  have hA (i : ℕ) := (hfields i).2.2.1
  have hC (i : ℕ) := (hfields i).2.2.2.1
  have href (i : ℕ) := (hfields i).2.2.2.2.1
  have hr (i : ℕ) := (hfields i).2.2.2.2.2
  intro i hh
  simpa only [parentDomain,relative,hq,hθ,hA,hC,href,hr,hx] using hi i (hh.trans ht)

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

lemma numerical_PC (g : InputGraph n) (st : RecursiveState n) (pc : NormalizePC)
    (hi : NumericalInvariant g st) : NumericalInvariant g (changePC st pc) := by
  apply numerical_changeFrame g st hi st.top _ rfl rfl rfl rfl
  intro hh v hv
  exact (hi st.top hh).2 v hv

lemma numerical_finish (g : InputGraph n) (st : RecursiveState n) (hi : NumericalInvariant g st) :
    NumericalInvariant g (finishEpisode st) := by
  apply numerical_changeFrame g _ (by exact hi) st.top _ rfl rfl rfl rfl
  intro hh v hv
  simpa using hv

lemma numerical_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : NumericalInvariant g st) : NumericalInvariant g (refreshKeys g st T) := by
  apply numerical_transport g st (refreshKeys g st T) hi le_rfl rfl
  intro i
  by_cases hh : i ≤ st.top <;> simp [refreshKeys,hh,numericalView]

lemma numerical_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : NumericalInvariant g st) : NumericalInvariant g (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · exact hi
  · intro i hh
    exact hi i (hh.trans (Nat.sub_le _ _))

lemma numerical_newFrame (g : InputGraph n) (st : RecursiveState n) (f : NormalizeFrame n)
    (hreg : RegionInvariant st) (hi : NumericalInvariant g st)
    (hA : f.active = ∅) (hC : f.cache = ∅) (hq : 0 < f.q)
    (href : f.reference = st.x) (hr : f.residual = (st.frames st.top).residual) :
    NumericalInvariant g {st with top := st.top+1, frames := Function.update st.frames (st.top+1) f} := by
  classical
  let u : RecursiveState n := {st with top := st.top+1, frames := Function.update st.frames (st.top+1) f}
  change NumericalInvariant g u
  intro i hh
  change i ≤ st.top+1 at hh
  by_cases he : i = st.top+1
  · subst i
    have hf : u.frames (st.top+1) = f := by simp [u]
    have hp : parentDomain u (st.top+1) = (st.frames st.top).active := by simp [u,parentDomain]
    constructor
    · intro v hv
      rw [hp] at hv
      have hn := ((hi st.top le_rfl).1 v ((hreg st.top le_rfl).1 hv)).1
      have hcapp : 0 < 3*f.q/8 := by positivity
      simpa [hf,relative,u,hA,href,hr] using And.intro hn hcapp
    · simp [hf,hC]
  · have his : i ≤ st.top := by omega
    have hf : u.frames i = st.frames i := by simp [u,he]
    have hp : parentDomain u i = parentDomain st i := by
      unfold parentDomain
      split
      · rfl
      · have hne : i-1 ≠ st.top+1 := by omega
        simp [u,hne]
    have hrel (v : Fin n) : relative u i v = relative st i v := by
      unfold relative
      rw [hf]
    constructor
    · intro v hv
      rw [hp] at hv
      simpa only [hrel,hf] using (hi i his).1 v hv
    · intro v hv
      rw [hf] at hv
      simpa only [hf] using (hi i his).2 v hv

lemma numerical_metadata (g : InputGraph n) (st : RecursiveState n) (hi : NumericalInvariant g st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hf : numericalView (f (st.frames j)) = numericalView (st.frames j)) :
    NumericalInvariant g (changeFrame st j f) := by
  have hh : (f (st.frames j)).q = (st.frames j).q ∧
      (f (st.frames j)).theta = (st.frames j).theta ∧
      (f (st.frames j)).active = (st.frames j).active ∧
      (f (st.frames j)).cache = (st.frames j).cache ∧
      (f (st.frames j)).reference = (st.frames j).reference ∧
      (f (st.frames j)).residual = (st.frames j).residual := by
    simpa only [numericalView,Prod.mk.injEq] using hf
  apply numerical_changeFrame g st hi j f hh.1 hh.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2
  intro hj v hv
  simpa only [hh.2.1,hh.2.2.2.1,hh.2.2.2.2.2] using
    (hi j hj).2 v (by simpa only [hh.2.2.2.1] using hv)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NumericalExterior

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
lemma numerical_exterior (g : InputGraph n) (α : ℝ) (hα : α ≤ 1)
    (ℓ : ℕ) (st : RecursiveState n) (hreg : RegionInvariant st) (hlayer : LayerIdentity g st)
    (hparam : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hc : CacheControlInvariant ℓ st) (hdepth : st.top ≤ ℓ)
    (t : ℕ) (ht : t ≤ st.top) (v : Fin n) (hvt : v ∈ parentDomain st t)
    (hout : v ∉ (st.frames t).active) (hd : 0 < g.graph.degree v) :
    NumericalInvariant g (exteriorPush g α st t v) := by
  classical
  let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
    (3*(st.frames t).q/8-relative st t v)
  let base := rawExterior g α st t v δ
  have hd' : 0 < LocalPush.deg g.graph v := by unfold LocalPush.deg; exact_mod_cast hd
  have hvnum := (hnum t ht).1 v hvt
  have hbounds := crossing_push_bounds (LocalPush.deg g.graph v) (st.frames t).q
    ((st.frames t).residual v) (relative st t v) hd' (hparam t ht).1 hvnum.1
    ⟨hvnum.2.1,(hvnum.2.2.2 hout).le⟩
  have hrδ : 5*LocalPush.deg g.graph v*δ ≤ (st.frames t).residual v :=
    sub_nonneg.mp hbounds.2.1
  have hraw : RawNumericalInvariant g base t v := numerical_raw g α hα ℓ st hreg hlayer hparam hnum
    hc hdepth t ht v hvt hout δ hbounds.1 hrδ hbounds.2.2.2
  have hact (i : ℕ) : (base.frames i).active = (st.frames i).active := raw_active g α st t v δ i
  have hpdom := parentDomain_same st base hact
  have hbr : RegionInvariant base := by
    apply region_same st base rfl hact _ _ _ hreg
    all_goals intro i; by_cases hh : i ≤ st.top <;> simp [base,rawExterior,hh]
  have hbp : ParameterInvariant base := by
    apply parameters_transport st base hparam le_rfl
    intro i hh
    by_cases he : i ≤ st.top <;> simp [base,rawExterior,he,frameParameters]
  have hbaseRel : relative base t v = relative st t v+δ := by rw [raw_relative]; simp
  have hbaseQ : (base.frames t).q = (st.frames t).q := raw_q g α st t v δ t
  have hdom : v ∈ parentDomain base t := by rw [hpdom]; exact hvt
  have hno : v ∉ (base.frames t).active := by rw [hact]; exact hout
  let prepared := if relative st t v+δ = 3*(st.frames t).q/8 then admitStage g base t v else base
  have hprepared : NumericalInvariant g prepared := by
    unfold prepared
    split
    · rename_i ha
      apply numerical_admission g base hbr hbp t ht v hdom hno hraw
      rw [hbaseRel,hbaseQ]
      exact ha
    · rename_i ha
      apply numerical_of_raw g base t v hraw
      rw [hbaseRel,hbaseQ]
      exact ha
  rw [exterior_stages]
  unfold NumericalInvariant relative parentDomain
  change NumericalInvariant g (refreshKeys g prepared (insert v (g.neighbors v).toFinset))
  exact numerical_refresh g prepared _ hprepared

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NumericalJoint

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma joint_relative (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (i : ℕ) (v : Fin n) :
    relative (jointUpdate g α st h) i v = relative st i v+h v := by
  by_cases hi : i = 0 <;> by_cases hh : i ≤ st.top <;>
    simp [jointUpdate,relative,hi,hh] <;> ring

lemma numerical_joint_update (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hi : NumericalInvariant g st)
    (T : Finset (Fin n)) (hT : T ⊆ (st.frames st.top).active)
    (h : Fin n → ℝ) (hs : ∀ v ∉ T, h v = 0) (hh : ∀ v, 0 ≤ h v)
    (hres : ∀ i ≤ st.top, ∀ v ∈ parentDomain st i,
      (LocalPush.Lα g.graph α *ᵥ h) v ≤ (st.frames i).residual v)
    (hcache : ∀ i ≤ st.top, ∀ v ∈ (st.frames i).cache,
      (st.frames i).theta*LocalPush.deg g.graph v ≤
        (st.frames i).residual v-(LocalPush.Lα g.graph α *ᵥ h) v) :
    NumericalInvariant g (jointUpdate g α st h) := by
  classical
  have hact (i : ℕ) : ((jointUpdate g α st h).frames i).active = (st.frames i).active := by
    by_cases he : i ≤ st.top <;> simp [jointUpdate,he]
  have hp := parentDomain_same st (jointUpdate g α st h) hact
  intro i hle
  have his : i ≤ st.top := hle
  constructor
  · intro v hv
    rw [hp] at hv
    have hn := (hi i his).1 v hv
    simp only [joint_relative]
    simp only [jointUpdate,his,ite_true]
    simp only [hv,ite_true]
    refine ⟨sub_nonneg.mpr (hres i his v hv),add_nonneg hn.2.1 (hh v),?_,?_⟩
    · intro ha
      exact (hn.2.2.1 ha).trans (le_add_of_nonneg_right (hh v))
    · intro ha
      have hz : h v = 0 := by
        apply hs v
        intro hm
        exact ha (active_subset_between st hreg i st.top his le_rfl (hT hm))
      simpa [hz] using hn.2.2.2 ha
  · intro v hv
    have hv' : v ∈ (st.frames i).cache := by simpa [jointUpdate,his] using hv
    have hdom : v ∈ parentDomain st i := (hreg i his).1 ((hreg i his).2.2.2 hv')
    simpa [jointUpdate,his,hdom] using hcache i his v hv'

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

lemma full_solve_caches_empty (ℓ : ℕ) (st : RecursiveState n) (hc : CacheControlInvariant ℓ st)
    (hdepth : st.top ≤ ℓ) (hpc : (st.frames st.top).pc = .fullSolve) :
    ∀ i ≤ st.top, (st.frames i).cache = ∅ := by
  intro i his
  by_cases he : i = st.top
  · subst i
    exact (hc st.top le_rfl).2.2 hpc
  · exact (hc i his).1 (by omega)

lemma numerical_full_solve (g : InputGraph n) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (ℓ : ℕ) (st : RecursiveState n) (hreg : RegionInvariant st) (hlayer : LayerIdentity g st)
    (hparam : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hc : CacheControlInvariant ℓ st) (hdepth : st.top ≤ ℓ)
    (hpc : (st.frames st.top).pc = .fullSolve)
    (hpos : ∀ v ∈ (st.frames st.top).active, 0 < g.graph.degree v) :
    NumericalInvariant g (jointUpdate g α st
      (solveOn g α (st.frames st.top).active (st.frames st.top).residual)) := by
  classical
  let T := (st.frames st.top).active
  have hb : ∀ v ∈ T, 0 ≤ (st.frames st.top).residual v := by
    intro v hv
    exact ((hnum st.top le_rfl).1 v ((hreg st.top le_rfl).1 hv)).1
  obtain ⟨hh,hres⟩ := principal_ancestor_update_bounds g α hα st hreg hlayer hparam hnum
    T (Finset.Subset.refl _) hpos _ hb (fun _ _ => le_rfl)
  apply numerical_joint_update g α st hreg hnum T (Finset.Subset.refl _) _
    (fun v hv => solveOn_outside g α T _ v hv) hh hres
  intro i his v hv
  rw [full_solve_caches_empty ℓ st hc hdepth hpc i his] at hv
  simp at hv

lemma numerical_cached_solve (g : InputGraph n) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (ℓ : ℕ) (st : RecursiveState n) (hreg : RegionInvariant st) (hlayer : LayerIdentity g st)
    (hparam : ParameterInvariant st) (hnum : NumericalInvariant g st)
    (hkeys : KeysInvariant g st) (hbudget : BudgetInvariant st)
    (hc : CacheControlInvariant ℓ st) (hpc : (st.frames st.top).pc = .leafDrain)
    (hpos : ∀ v ∈ (st.frames st.top).cache ∪ (st.frames st.top).high, 0 < g.graph.degree v) :
    let C := (st.frames st.top).cache ∪ (st.frames st.top).high
    let u := changeFrame st st.top (fun f => {f with cache := C})
    NumericalInvariant g (jointUpdate g α u (solveOn g α C
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
  obtain ⟨hh,hres⟩ := principal_ancestor_update_bounds g α hα u hru hlu hpu hnu C hCu hpos b hb hbr
  apply numerical_joint_update g α u hru hnu C hCu _
    (fun v hv => solveOn_outside g α C b v hv) hh hres
  intro i his v hv
  have hi' : i ≤ st.top := his
  by_cases he : i = st.top
  · subst i
    have hvC : v ∈ C := by simpa [u,changeFrame] using hv
    have hh := solve_threshold_clears g α (st.frames st.top).theta hα C hpos
      (st.frames st.top).residual v hvC
    simpa [u,changeFrame,b] using hh.symm.le
  · have hne : i ≠ ℓ := by omega
    have hz := (hc i hi').1 hne
    have hv' : v ∈ (st.frames i).cache := by simpa [u,changeFrame,he] using hv
    rw [hz] at hv'
    simp at hv'

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.NumericalStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma numerical_pending (g : InputGraph n) (α : ℝ) (hα : α ≤ 1) (ℓ : ℕ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hlayer : LayerIdentity g st) (hparam : ParameterInvariant st)
    (hnum : NumericalInvariant g st) (hc : CacheControlInvariant ℓ st) (hdepth : st.top ≤ ℓ)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st)
    (t : ℕ) (v : Fin n) (hp : pendingPush st = some (t,v)) :
    NumericalInvariant g (exteriorPush g α st t v) := by
  obtain ⟨ht,hm⟩ := pending_push_member st t v hp
  obtain ⟨hv,hout⟩ := Finset.mem_sdiff.mp ((hreg t ht).2.1 hm)
  exact numerical_exterior g α hα ℓ st hreg hlayer hparam hnum hc hdepth t ht v hv hout
    (isolate_pending_positive g st hiso hkeys t v hp)

lemma numerical_drain (g : InputGraph n) (α : ℝ) (hα : α ≤ 1) (ℓ : ℕ) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hlayer : LayerIdentity g st) (hparam : ParameterInvariant st)
    (hnum : NumericalInvariant g st) (hc : CacheControlInvariant ℓ st) (hdepth : st.top ≤ ℓ)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st) (pc : NormalizePC) :
    NumericalInvariant g (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact numerical_PC g _ pc hnum
  · cases hp : pendingPush st with
    | none => exact numerical_PC g _ pc hnum
    | some p =>
      obtain ⟨t,v⟩ := p
      exact numerical_pending g α hα ℓ st hreg hlayer hparam hnum hc hdepth hkeys hiso t v hp

set_option maxHeartbeats 1000000 in
lemma numerical_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hreg : RegionInvariant st) (hlayer : LayerIdentity g st) (hparam : ParameterInvariant st)
    (hnum : NumericalInvariant g st) (hc : CacheControlInvariant ℓ st) (hdepth : st.top ≤ ℓ)
    (hkeys : KeysInvariant g st) (hiso : IsolateResidual g st) (hbudget : BudgetInvariant st) :
    NumericalInvariant g (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hnum
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hcomp : componentComplete st
  · simp only [hcomp,ite_true]
    exact hnum
  simp only [hcomp,ite_false]
  have hdrain (pc : NormalizePC) := numerical_drain g α hα.2.le ℓ st hreg hlayer hparam hnum hc hdepth hkeys hiso pc
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact numerical_PC g _ _ hnum
    · split
      · exact hdrain _
      · split <;> exact numerical_PC g _ _ hnum
  | beginEpisode =>
    simp only [hpc]
    apply numerical_changeFrame g _ (by exact hnum) _ _ rfl rfl rfl rfl
    intro hh v hv
    simpa using hv
  | fullSolve =>
    simp only [hpc]
    split
    · exact numerical_PC g _ _ hnum
    · split
      · rename_i hg
        apply numerical_PC g _ _
        unfold NumericalInvariant relative parentDomain
        exact numerical_refresh g _ (touchedBy g (st.frames st.top).active)
          (numerical_full_solve g α hα ℓ st hreg hlayer hparam hnum hc hdepth hpc hg.2)
      · exact hnum
  | normalize =>
    simp only [hpc]
    split
    · exact numerical_PC g _ _ hnum
    · split
      · exact numerical_PC g _ _ hnum
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : NumericalInvariant g up := numerical_metadata g u hnum st.top _ rfl
        have hrup : RegionInvariant up := region_controlFrame u st.top le_rfl _ hreg rfl rfl rfl rfl
        have hopen : (st.frames st.top).openBudget = true := by
          simpa [hpc,budgetPC] using hbudget st.top le_rfl
        have hθ : 0 < (st.frames st.top).theta :=
          lt_of_lt_of_le (hparam st.top le_rfl).1 ((hparam st.top le_rfl).2.2 hopen)
        exact numerical_newFrame g up c hrup hup rfl rfl hθ rfl (by
          simp [c,freshFrame,up,u,changeFrame,debit])
  | leafDrain =>
    simp only [hpc]
    split
    · exact numerical_PC g _ _ hnum
    · split
      · cases hp : pendingPush st with
        | none => exact numerical_PC g _ _ hnum
        | some p =>
          obtain ⟨t,v⟩ := p
          exact numerical_pending g α hα.2.le ℓ st hreg hlayer hparam hnum hc hdepth hkeys hiso t v hp
      · split
        · exact numerical_PC g _ _ hnum
        · split
          · rename_i hg
            let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            unfold NumericalInvariant relative parentDomain
            exact numerical_refresh g _ (touchedBy g C)
              (numerical_cached_solve g α hα ℓ st hreg hlayer hparam hnum hkeys hbudget hc hpc hg.2)
          · exact hnum
  | afterChild =>
    simp only [hpc]
    split
    · exact numerical_PC g _ _ (numerical_finish g _ hnum)
    · split
      · exact numerical_PC g _ _ (numerical_finish g _ hnum)
      · exact hdrain _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact numerical_PC g _ _ (numerical_finish g _ hnum)
    · split
      · exact numerical_PC g _ _ (numerical_finish g _ hnum)
      · apply numerical_metadata g _ (numerical_finish g _ (by exact hnum)) _ _ rfl
  | restartDrain =>
    simp only [hpc]
    split
    · exact numerical_PC g _ _ hnum
    · split
      · exact hdrain _
      · exact numerical_metadata g (debit st st.top 1) hnum st.top
          (fun fc => {fc with needFull := true, pc := .beginEpisode}) rfl
  | normal =>
    simp only [hpc]
    exact numerical_end g α _ hnum
  | interrupted =>
    simp only [hpc]
    exact numerical_end g α _ hnum

lemma numerical_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    NumericalInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using numerical_init g s q hq ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      numerical_step m g s α hα ℓ schedule _
        (region_run m g s α q ℓ schedule t) (layer_run m g s α q ℓ schedule t)
        (parameters_run m g s α q hq ℓ schedule t) ih
        (cache_run m g s α q ℓ schedule t) (depth_run m g s α q ℓ schedule t)
        (keys_run m g s α q hq.le ℓ schedule t) (isolate_run m g s α q hs ℓ schedule t)
        (budget_run m g s α q ℓ schedule t)

end
end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
noncomputable section
theorem solution (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    NumericalInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  exact numerical_run m g s α q hα hq hs ℓ schedule t
end

