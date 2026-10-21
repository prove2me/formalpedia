-- Prove2me | solution 1 for GeometryOfGraphs.Clique.disjoint_interiors
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:40:27.027258+00:00
-- url     : https://prove2.me/submissions/620d878f-2aa8-4d83-924c-e55ff7cbed52

import Mathlib
import Definitions.Def_GeometryOfGraphs_Clique_isoDim

set_option autoImplicit false
open GeometryOfGraphs.Clique

theorem diff_body_aux {n d : ℕ} (hn : 0 < n) (N : (Fin d → ℝ) → ℝ)
    (hN : IsNormFun N) (x : Fin n → (Fin d → ℝ))
    (hx : ∀ i j, i ≠ j → N (x i - x j) = 1)
    (u v : Fin d → ℝ)
    (hu : u ∈ convexHull ℝ (Set.range x))
    (hv : v ∈ convexHull ℝ (Set.range x)) :
    N (u - v) ≤ 1 := by
  obtain ⟨h0, hsep, hhom, htri⟩ := hN
  have hN0 : N 0 = 0 := by simpa using hhom 0 0
  have hneg : ∀ y, N (-y) = N y := fun y => by
    have := hhom (-1) y
    simpa using this
  have hball : ∀ c : Fin d → ℝ, Convex ℝ {y | N (y - c) ≤ 1} := by
    intro c y hy z hz a b ha hb hab
    simp only [Set.mem_setOf_eq] at *
    have e : a • y + b • z - c = a • (y - c) + b • (z - c) := by
      have hc : c = (a + b) • c := by rw [hab, one_smul]
      conv_lhs => rw [hc]
      simp only [smul_sub, add_smul]
      abel
    rw [e]
    calc N (a • (y - c) + b • (z - c)) ≤ N (a • (y - c)) + N (b • (z - c)) := htri _ _
      _ = a * N (y - c) + b * N (z - c) := by
          rw [hhom, hhom, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := by gcongr
      _ = 1 := by rw [mul_one, mul_one, hab]
  have hxx : ∀ i j, N (x i - x j) ≤ 1 := by
    intro i j
    by_cases h : i = j
    · subst h
      simp [hN0]
    · exact (hx i j h).le
  have step1 : ∀ i, ∀ w ∈ convexHull ℝ (Set.range x), N (w - x i) ≤ 1 := by
    intro i w hw
    have : convexHull ℝ (Set.range x) ⊆ {y | N (y - x i) ≤ 1} :=
      convexHull_min (by rintro _ ⟨j, rfl⟩; exact hxx j i) (hball _)
    exact this hw
  have step2 : convexHull ℝ (Set.range x) ⊆ {y | N (y - v) ≤ 1} := by
    refine convexHull_min ?_ (hball v)
    rintro _ ⟨j, rfl⟩
    have := step1 j v hv
    have h2 : x j - v = -(v - x j) := by abel
    show N (x j - v) ≤ 1
    rw [h2, hneg]
    exact this
  exact step2 hu

theorem solution {n d : ℕ} (hn : 0 < n) (N : (Fin d → ℝ) → ℝ)
    (hN : IsNormFun N) (x : Fin n → (Fin d → ℝ))
    (hx : ∀ i j, i ≠ j → N (x i - x j) = 1)
    (i j : Fin n) (hij : i ≠ j) :
    interior (((fun y => y + x i) '' convexHull ℝ (Set.range x)) ∩
      ((fun y => y + x j) '' convexHull ℝ (Set.range x))) = ∅ := by
  have hhom := hN.2.2.1
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨I, hI⟩ : ∃ I : Set _, I = ((fun y => y + x i) '' convexHull ℝ (Set.range x)) ∩
      ((fun y => y + x j) '' convexHull ℝ (Set.range x)) := ⟨_, rfl⟩
  rw [← hI] at hz
  set e : Fin d → ℝ := x i - x j with he
  have hg : Continuous (fun t : ℝ => z + t • e) := by fun_prop
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_interior.preimage hg) 0 (by simpa using hz)
  have h1 : z + (ε / 2) • e ∈ interior I := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith)
  have h2 : z + (-(ε / 2)) • e ∈ interior I := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]
    linarith)
  have h1m : z + (ε / 2) • e ∈ I := interior_subset h1
  have h2m : z + (-(ε / 2)) • e ∈ I := interior_subset h2
  rw [hI] at h1m h2m
  have h1' := h1m.2
  have h2' := h2m.1
  obtain ⟨v, hvD, hv⟩ := h1'
  obtain ⟨u, huD, hu⟩ := h2'
  have hvu : v - u = (2 * (ε / 2) + 1) • e := by
    funext k
    have a := congrFun hv k
    have b := congrFun hu k
    simp only [he, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
    linear_combination a - b
  have := diff_body_aux hn N hN x hx v u hvD huD
  rw [hvu, hhom, he, hx i j hij, abs_of_pos (by positivity)] at this
  linarith
