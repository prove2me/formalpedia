-- Prove2me | solution 1 for LloydConvergence.lloyd_converges
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-17T05:40:30.243276+00:00
-- url     : https://prove2.me/submissions/fbf53126-4e99-4be0-b8eb-6d33c38c4b2d

import Mathlib
import Definitions.Def_UnderstandingML_Clustering
import Definitions.Def_LloydConvergence
/-!
# Lloyd's (k-means) convergence — submission file

Main theorem: Lloyd's algorithm (k-means, strict-move tie-breaking, empty
clusters keep centroid `0` per the platform convention) converges in finitely
many steps — at most `k ^ S.card` — to a Lloyd fixed point: a stable assignment
whose centroids are the cluster means.

The iteration definitions (`fiber`, `centroidS`, `centers`, `obj`, `cost`,
`argminDist`, `step`, `orbit`, `part`) are imported from the platform
definition `LloydConvergence` (`Definitions.Def_LloydConvergence`); the
platform's `centroid` / `kmeansObjective` are imported from
`Definitions.Def_UnderstandingML_Clustering`. This file contains only theorems.
-/
open MeasureTheory
open UnderstandingML
open Finset
open scoped InnerProductSpace

namespace LloydConvergence

variable {n : ℕ}

/-- `centroid` is the platform's `UnderstandingML.centroid`
(`(C.card : ℝ)⁻¹ • ∑ x ∈ C, x`), imported above. -/

theorem sum_eq_card_smul_mean {ι : Type*} (T : Finset ι)
    (p : ι → EuclideanSpace ℝ (Fin n)) :
    ∑ x ∈ T, p x = (T.card : ℝ) • ((T.card : ℝ)⁻¹ • ∑ y ∈ T, p y) := by
  by_cases h : (T.card : ℝ) = 0
  · have hT : T = ∅ := by
      rw [← Finset.card_eq_zero]
      exact_mod_cast h
    simp [hT]
  · rw [smul_smul, mul_inv_cancel₀ h, one_smul]

/-- The parallel-axis identity, for an arbitrary finite family of points:
the sum of squared distances to an arbitrary point `μ` equals the sum of
squared distances to the mean plus `|T| * ‖mean - μ‖²`. -/
theorem sum_sq_sub_mean_eq {ι : Type*} (T : Finset ι)
    (p : ι → EuclideanSpace ℝ (Fin n)) (μ : EuclideanSpace ℝ (Fin n)) :
    ∑ x ∈ T, ‖p x - μ‖ ^ 2
      = ∑ x ∈ T, ‖p x - (T.card : ℝ)⁻¹ • ∑ y ∈ T, p y‖ ^ 2
        + (T.card : ℝ) * ‖(T.card : ℝ)⁻¹ • ∑ y ∈ T, p y - μ‖ ^ 2 := by
  have key : ∀ ν : EuclideanSpace ℝ (Fin n),
      ∑ x ∈ T, ⟪p x, ν⟫_ℝ
        = (T.card : ℝ) * ⟪(T.card : ℝ)⁻¹ • ∑ y ∈ T, p y, ν⟫_ℝ := by
    intro ν
    rw [← sum_inner]
    conv_lhs => rw [sum_eq_card_smul_mean, inner_smul_left]
    simp
  have expand : ∀ ν : EuclideanSpace ℝ (Fin n),
      ∑ x ∈ T, ‖p x - ν‖ ^ 2
        = ∑ x ∈ T, ‖p x‖ ^ 2 - 2 * ∑ x ∈ T, ⟪p x, ν⟫_ℝ + (T.card : ℝ) * ‖ν‖ ^ 2 := by
    intro ν
    simp_rw [norm_sub_sq_real]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
  rw [expand μ, expand ((T.card : ℝ)⁻¹ • ∑ y ∈ T, p y), key μ,
    key ((T.card : ℝ)⁻¹ • ∑ y ∈ T, p y), real_inner_self_eq_norm_sq,
    norm_sub_sq_real]
  ring

/-- The mean-minimizer lemma (step (a)): the mean of a finite family uniquely
minimizes the sum of squared distances. -/
theorem sum_sq_sub_mean_le {ι : Type*} (T : Finset ι)
    (p : ι → EuclideanSpace ℝ (Fin n)) (μ : EuclideanSpace ℝ (Fin n)) :
    ∑ x ∈ T, ‖p x - (T.card : ℝ)⁻¹ • ∑ y ∈ T, p y‖ ^ 2
      ≤ ∑ x ∈ T, ‖p x - μ‖ ^ 2 := by
  rw [sum_sq_sub_mean_eq T p μ]
  have h : 0 ≤ (T.card : ℝ) * ‖(T.card : ℝ)⁻¹ • ∑ y ∈ T, p y - μ‖ ^ 2 := by
    positivity
  linarith

/-- Special case for a Finset of points: the centroid minimizes. -/
theorem sum_sq_sub_centroid_le (T : Finset (EuclideanSpace ℝ (Fin n)))
    (μ : EuclideanSpace ℝ (Fin n)) :
    ∑ x ∈ T, ‖x - UnderstandingML.centroid T‖ ^ 2 ≤ ∑ x ∈ T, ‖x - μ‖ ^ 2 := by
  have h := sum_sq_sub_mean_le T (fun x : EuclideanSpace ℝ (Fin n) => x) μ
  simpa [UnderstandingML.centroid] using h

/-! ### The Lloyd step (step (b)) -/

variable {k : ℕ}

theorem argminDist_le [NeZero k] (μ : Fin k → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin k) :
    ‖x - μ (argminDist μ x)‖ ≤ ‖x - μ j‖ := by
  have h := Classical.choose_spec
    (Finset.exists_min_image Finset.univ (fun j => ‖x - μ j‖) Finset.univ_nonempty)
  exact h.2 j (Finset.mem_univ j)

theorem step_apply (S : Finset (EuclideanSpace ℝ (Fin n))) [NeZero k]
    (f : S → Fin k) (x : S) :
    step S f x =
      if ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f (argminDist (centers S f) x)‖
          < ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f (f x)‖
        then argminDist (centers S f) x
        else f x :=
  rfl

/-- A step never moves a point to a farther center. -/
theorem step_dist_le (S : Finset (EuclideanSpace ℝ (Fin n))) [NeZero k]
    (f : S → Fin k) (x : S) :
    ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f (step S f x)‖
      ≤ ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f (f x)‖ := by
  rw [step_apply]
  split_ifs with h
  · exact le_of_lt h
  · exact le_refl _

/-- A point that moves, moves to a strictly nearer center. -/
theorem step_dist_lt_of_ne (S : Finset (EuclideanSpace ℝ (Fin n))) [NeZero k]
    (f : S → Fin k) (x : S) (h : step S f x ≠ f x) :
    ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f (step S f x)‖
      < ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f (f x)‖ := by
  by_cases hc : ‖(x : EuclideanSpace ℝ (Fin n))
        - centers S f (argminDist (centers S f) x)‖
        < ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f (f x)‖
  · rw [step_apply, if_pos hc]
    exact hc
  · rw [step_apply, if_neg hc] at h
    exact absurd rfl h

/-- Grouping a sum over `S` by the fibers of an assignment. -/
theorem sum_fiber_eq (S : Finset (EuclideanSpace ℝ (Fin n))) (f : S → Fin k)
    (g : S → ℝ) :
    ∑ x : S, g x = ∑ i, ∑ x ∈ fiber S f i, g x := by
  show ∑ x : S, g x
    = ∑ i, ∑ x ∈ Finset.univ.filter (fun x => f x = i), g x
  rw [Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ _)]

/-- The objective after a step, against the OLD centers, is at most the cost
of the new assignment against the old centers: each new cluster's centroid
is the mean of that cluster, hence optimal for it. -/
theorem obj_step_le_cost (S : Finset (EuclideanSpace ℝ (Fin n))) [NeZero k]
    (f : S → Fin k) :
    obj S (step S f) ≤ cost S (centers S f) (step S f) := by
  have h1 : obj S (step S f)
      = ∑ i, ∑ x ∈ fiber S (step S f) i,
          ‖(x : EuclideanSpace ℝ (Fin n)) - centers S (step S f) i‖ ^ 2 := by
    unfold obj
    rw [sum_fiber_eq]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨_, hx2⟩ := Finset.mem_filter.mp hx
    rw [hx2]
  have h2 : cost S (centers S f) (step S f)
      = ∑ i, ∑ x ∈ fiber S (step S f) i,
          ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f i‖ ^ 2 := by
    unfold cost
    rw [sum_fiber_eq]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨_, hx2⟩ := Finset.mem_filter.mp hx
    rw [hx2]
  rw [h1, h2]
  apply Finset.sum_le_sum
  intro i _
  -- `centers S (step S f) i` is the mean of the fiber, hence minimizes.
  -- (Definitionally the mean expression in `sum_sq_sub_mean_le`.)
  exact sum_sq_sub_mean_le (fiber S (step S f) i)
    (fun x : S => (x : EuclideanSpace ℝ (Fin n))) (centers S f i)

/-- The cost against fixed centers strictly decreases when the assignment
changes: every point's term is `≤` its old term, and at least one moved
point's term is `<`. -/
theorem cost_step_lt (S : Finset (EuclideanSpace ℝ (Fin n))) [NeZero k]
    (f : S → Fin k) (hne : step S f ≠ f) :
    cost S (centers S f) (step S f) < cost S (centers S f) f := by
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hne
  apply Finset.sum_lt_sum
  · intro x _
    exact pow_le_pow_left₀ (norm_nonneg _) (step_dist_le S f x) 2
  · exact ⟨x₀, Finset.mem_univ x₀,
      pow_lt_pow_left₀ (step_dist_lt_of_ne S f x₀ hx₀) (norm_nonneg _)
        (by norm_num : (2 : ℕ) ≠ 0)⟩

/-- Strict decrease (step (b)): a Lloyd step that changes the assignment
strictly decreases the objective. -/
theorem obj_step_lt (S : Finset (EuclideanSpace ℝ (Fin n))) [NeZero k]
    (f : S → Fin k) (hne : step S f ≠ f) :
    obj S (step S f) < obj S f :=
  lt_of_le_of_lt (obj_step_le_cost S f) (cost_step_lt S f hne)

/-! ### Termination and the fixed point (steps (c)–(e)) -/

theorem orbit_zero (S : Finset (EuclideanSpace ℝ (Fin n))) [NeZero k]
    (f₀ : S → Fin k) : orbit S f₀ 0 = f₀ :=
  rfl

theorem orbit_succ (S : Finset (EuclideanSpace ℝ (Fin n))) [NeZero k]
    (f₀ : S → Fin k) (t : ℕ) : orbit S f₀ (t + 1) = step S (orbit S f₀ t) :=
  Function.iterate_succ_apply' _ _ _

/-- Termination (steps (c)+(d)): the iteration reaches a fixed point within
`k ^ S.card` steps. Proof: if it never fixed within the bound, the first
`k ^ S.card + 1` orbit values would be pairwise distinct (the objective
strictly decreases along the orbit), but there are only `k ^ S.card`
assignments. -/
theorem exists_fixed_point (S : Finset (EuclideanSpace ℝ (Fin n))) [NeZero k]
    (f₀ : S → Fin k) :
    ∃ T : ℕ, T ≤ k ^ S.card ∧ step S (orbit S f₀ T) = orbit S f₀ T := by
  classical
  set N := k ^ S.card with hN
  by_contra hcon
  push Not at hcon
  -- hcon : ∀ T, T ≤ N → step S (orbit S f₀ T) ≠ orbit S f₀ T
  have hdec : ∀ t, t < N → obj S (orbit S f₀ (t + 1)) < obj S (orbit S f₀ t) := by
    intro t ht
    rw [orbit_succ]
    exact obj_step_lt S _ (hcon t (Nat.le_of_lt ht))
  have hlt : ∀ j, ∀ i, i < j → j ≤ N →
      obj S (orbit S f₀ j) < obj S (orbit S f₀ i) := by
    intro j
    induction j with
    | zero => intro i hij _; exact absurd hij (Nat.not_lt_zero i)
    | succ j ih =>
      intro i hij hj
      by_cases hji : i = j
      · subst hji
        exact hdec i (Nat.lt_of_succ_le hj)
      · exact lt_trans (hdec j (Nat.lt_of_succ_le hj))
          (ih i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hij) hji)
            (Nat.le_of_succ_le hj))
  -- The map `Fin (N+1) → (↥S → Fin k)` sending `i ↦ orbit i` is injective.
  have hinj : Function.Injective
      (fun i : Fin (N + 1) => orbit S f₀ (i : ℕ)) := by
    intro i j hij
    by_contra hne
    have hij' : orbit S f₀ (i : ℕ) = orbit S f₀ (j : ℕ) := hij
    rcases lt_trichotomy i j with h | h | h
    · have hlt' := hlt j i (by exact_mod_cast h) (by
        have := j.isLt; omega)
      rw [hij'] at hlt'
      exact lt_irrefl _ hlt'
    · exact hne h
    · have hlt' := hlt i j (by exact_mod_cast h) (by
        have := i.isLt; omega)
      rw [hij'] at hlt'
      exact lt_irrefl _ hlt'
  have hcard := Fintype.card_le_of_injective
    (fun i : Fin (N + 1) => orbit S f₀ (i : ℕ)) hinj
  rw [Fintype.card_fin] at hcard
  have hcard2 : Fintype.card (S → Fin k) = k ^ S.card := by
    simp [Fintype.card_pi]
  rw [hcard2, ← hN] at hcard
  exact Nat.not_succ_le_self N hcard

/-- Fixed-point characterization (step (e)): at a fixed point, every point is
already at a nearest centroid. (Centroids are cluster means by definition of
`centers`.) -/
theorem step_eq_self_stable (S : Finset (EuclideanSpace ℝ (Fin n))) [NeZero k]
    (f : S → Fin k) (hfix : step S f = f) (x : S) (j : Fin k) :
    ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f (f x)‖
      ≤ ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f j‖ := by
  by_contra hlt
  push Not at hlt
  have harg : ‖(x : EuclideanSpace ℝ (Fin n))
        - centers S f (argminDist (centers S f) x)‖
        < ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f (f x)‖ :=
    lt_of_le_of_lt (argminDist_le _ _ j) hlt
  have hstep : step S f x = argminDist (centers S f) x := by
    rw [step_apply, if_pos harg]
  have hne : step S f x ≠ f x := by
    rw [hstep]
    intro heq
    rw [heq] at harg
    exact lt_irrefl _ harg
  exact hne (congrFun hfix x)

/-- Main theorem: Lloyd's algorithm converges in finitely many steps to a
Lloyd fixed point — a stable assignment whose centroids are the cluster means.
The number of steps is at most `k ^ S.card`, the number of assignments. -/
theorem lloyd_converges_centers (S : Finset (EuclideanSpace ℝ (Fin n))) [NeZero k]
    (f₀ : S → Fin k) :
    ∃ T : ℕ, T ≤ k ^ S.card ∧
      (∀ x : S, ∀ j : Fin k,
        ‖(x : EuclideanSpace ℝ (Fin n))
          - centers S (orbit S f₀ T) ((orbit S f₀ T) x)‖
          ≤ ‖(x : EuclideanSpace ℝ (Fin n))
            - centers S (orbit S f₀ T) j‖) := by
  obtain ⟨T, hT, hfix⟩ := exists_fixed_point S f₀
  exact ⟨T, hT, fun x j => step_eq_self_stable S _ hfix x j⟩

/-! ### Connection to the platform's objective -/

theorem centroid_part (S : Finset (EuclideanSpace ℝ (Fin n))) (f : S → Fin k)
    (i : Fin k) :
    UnderstandingML.centroid (part S f i) = centers S f i := by
  unfold part centers centroidS UnderstandingML.centroid
  rw [Finset.sum_image (fun x _ y _ h => Subtype.val_injective h),
    Finset.card_image_of_injective _ Subtype.val_injective]

/-- `kmeansObjective` is the platform's `UnderstandingML.kmeansObjective`,
imported above. -/

theorem obj_eq_kmeansObjective (S : Finset (EuclideanSpace ℝ (Fin n)))
    (f : S → Fin k) :
    obj S f = kmeansObjective (part S f) := by
  unfold obj kmeansObjective centerCost
  rw [sum_fiber_eq]
  apply Finset.sum_congr rfl
  intro i _
  have h1 : ∑ x ∈ fiber S f i,
        ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f (f x)‖ ^ 2
      = ∑ x ∈ fiber S f i,
        ‖(x : EuclideanSpace ℝ (Fin n)) - centers S f i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨_, hx2⟩ := Finset.mem_filter.mp hx
    rw [hx2]
  rw [h1]
  simp only [centroid_part]
  unfold part
  rw [Finset.sum_image (fun x _ y _ h => Subtype.val_injective h)]

/-- Main theorem restated with the platform's objective vocabulary: at the
fixed point, every point is at a nearest centroid of its cluster. -/
theorem lloyd_converges_kmeansObjective (S : Finset (EuclideanSpace ℝ (Fin n)))
    [NeZero k] (f₀ : S → Fin k) :
    ∃ T : ℕ, T ≤ k ^ S.card ∧
      (∀ x : S, ∀ j : Fin k,
        ‖(x : EuclideanSpace ℝ (Fin n))
          - UnderstandingML.centroid (part S (orbit S f₀ T) ((orbit S f₀ T) x))‖
          ≤ ‖(x : EuclideanSpace ℝ (Fin n))
            - UnderstandingML.centroid (part S (orbit S f₀ T) j)‖) := by
  obtain ⟨T, hT, hstab⟩ := lloyd_converges_centers S f₀
  refine ⟨T, hT, fun x j => ?_⟩
  simp only [centroid_part]
  exact hstab x j

end LloydConvergence

/-- Submission-shaped main theorem: Lloyd's algorithm converges in finitely
many steps to a Lloyd fixed point. -/
theorem solution {n k : ℕ} (S : Finset (UnderstandingML.Vec n)) [NeZero k]
    (f₀ : S → Fin k) :
    ∃ T : ℕ, T ≤ k ^ S.card ∧
      (∀ x : S, ∀ j : Fin k,
        ‖(x : UnderstandingML.Vec n)
          - UnderstandingML.centroid (LloydConvergence.part S (LloydConvergence.orbit S f₀ T) ((LloydConvergence.orbit S f₀ T) x))‖
          ≤ ‖(x : UnderstandingML.Vec n)
            - UnderstandingML.centroid (LloydConvergence.part S (LloydConvergence.orbit S f₀ T) j)‖) := by
  exact LloydConvergence.lloyd_converges_kmeansObjective S f₀
