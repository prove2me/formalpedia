-- Prove2me | solution 1 for KServer.manhattan_bounding_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T17:26:11.381853+00:00
-- url     : https://prove2.me/submissions/76dc7332-1ccb-4583-8f9a-f8b71c23cca3

import Mathlib
import Definitions.Def_KServer_model

open KServer

private abbrev E := PiLp 1 fun _ : Fin 2 => ℝ

private noncomputable def mk2 (u v : ℝ) : E := (WithLp.toLp 1 ![u, v] : E)

private theorem mk2_0 (u v : ℝ) : (mk2 u v).ofLp 0 = u := rfl
private theorem mk2_1 (u v : ℝ) : (mk2 u v).ofLp 1 = v := rfl

private theorem dist2 (x y : E) :
    dist x y = |x.ofLp 0 - y.ofLp 0| + |x.ofLp 1 - y.ofLp 1| := by
  simp [PiLp.dist_eq_of_L1, Fin.sum_univ_two, Real.dist_eq]

/-- Every finite set of points of the city-block plane sits inside an axis-parallel
rectangle whose corners dominate it. -/
theorem solution (S : Finset (PiLp 1 fun _ : Fin 2 => ℝ)) :
    ∃ (T : Finset (PiLp 1 fun _ : Fin 2 => ℝ))
      (x z y t : PiLp 1 fun _ : Fin 2 => ℝ),
      S ⊆ T ∧ x ∈ T ∧ z ∈ T ∧ y ∈ T ∧ t ∈ T
      ∧ dist x y = dist z t
      ∧ (∀ w ∈ T, dist x w + dist w y = dist x y ∧ dist z w + dist w t = dist z t)
      ∧ (∀ p ∈ T, ∀ b ∈ T, ∃ u : PiLp 1 fun _ : Fin 2 => ℝ,
          (u = x ∨ u = z ∨ u = y ∨ u = t) ∧ dist p b + dist b u = dist p u) := by
  classical
  obtain ⟨A, hA0, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧ ∀ w ∈ S, |w.ofLp 0| ≤ A ∧ |w.ofLp 1| ≤ A := by
    obtain ⟨A0, hA0⟩ := (S.image fun w => |w.ofLp 0| + |w.ofLp 1|).exists_le
    refine ⟨max A0 0, le_max_right _ _, ?_⟩
    intro w hw
    have h : |w.ofLp 0| + |w.ofLp 1| ≤ A0 := hA0 _ (Finset.mem_image_of_mem _ hw)
    have hm : A0 ≤ max A0 0 := le_max_left _ _
    have h0 := abs_nonneg (w.ofLp 0)
    have h1 := abs_nonneg (w.ofLp 1)
    exact ⟨by linarith, by linarith⟩
  refine ⟨insert (mk2 (-A) (-A)) (insert (mk2 A (-A)) (insert (mk2 A A)
      (insert (mk2 (-A) A) S))), mk2 (-A) (-A), mk2 A (-A), mk2 A A, mk2 (-A) A,
    ?_, by simp, by simp, by simp, by simp, ?_, ?_, ?_⟩
  · intro w hw; simp [hw]
  · -- the two diagonals have the same length
    have e1 : |(-A) - A| = -((-A) - A) := abs_of_nonpos (by linarith)
    have e2 : |A - (-A)| = A - (-A) := abs_of_nonneg (by linarith)
    simp only [dist2, mk2_0, mk2_1]
    linarith
  all_goals
    have hbound : ∀ w ∈ insert (mk2 (-A) (-A)) (insert (mk2 A (-A)) (insert (mk2 A A)
        (insert (mk2 (-A) A) S))), -A ≤ w.ofLp 0 ∧ w.ofLp 0 ≤ A
          ∧ -A ≤ w.ofLp 1 ∧ w.ofLp 1 ≤ A := by
      intro w hw
      simp only [Finset.mem_insert] at hw
      rcases hw with rfl | rfl | rfl | rfl | hw
      · simp only [mk2_0, mk2_1]; exact ⟨le_refl _, by linarith, le_refl _, by linarith⟩
      · simp only [mk2_0, mk2_1]; exact ⟨by linarith, le_refl _, le_refl _, by linarith⟩
      · simp only [mk2_0, mk2_1]; exact ⟨by linarith, le_refl _, by linarith, le_refl _⟩
      · simp only [mk2_0, mk2_1]; exact ⟨le_refl _, by linarith, by linarith, le_refl _⟩
      · obtain ⟨g0, g1⟩ := hA w hw
        obtain ⟨u0, u1⟩ := abs_le.mp g0
        obtain ⟨v0, v1⟩ := abs_le.mp g1
        exact ⟨u0, u1, v0, v1⟩
  · -- every point of the box lies on both diagonals
    intro w hw
    obtain ⟨c0, c1, c2, c3⟩ := hbound w hw
    have e1 : |(-A) - w.ofLp 0| = -((-A) - w.ofLp 0) := abs_of_nonpos (by linarith)
    have e2 : |(-A) - w.ofLp 1| = -((-A) - w.ofLp 1) := abs_of_nonpos (by linarith)
    have e3 : |w.ofLp 0 - A| = -(w.ofLp 0 - A) := abs_of_nonpos (by linarith)
    have e4 : |w.ofLp 1 - A| = -(w.ofLp 1 - A) := abs_of_nonpos (by linarith)
    have e5 : |A - w.ofLp 0| = A - w.ofLp 0 := abs_of_nonneg (by linarith)
    have e6 : |w.ofLp 0 - (-A)| = w.ofLp 0 - (-A) := abs_of_nonneg (by linarith)
    have e7 : |w.ofLp 1 - (-A)| = w.ofLp 1 - (-A) := abs_of_nonneg (by linarith)
    have e8 : |(-A) - A| = -((-A) - A) := abs_of_nonpos (by linarith)
    have e9 : |A - (-A)| = A - (-A) := abs_of_nonneg (by linarith)
    simp only [dist2, mk2_0, mk2_1]
    constructor <;> linarith
  · -- for any two points of the box, some corner completes a geodesic
    intro p hp b hb
    obtain ⟨p0, p1, p2, p3⟩ := hbound p hp
    obtain ⟨b0, b1, b2, b3⟩ := hbound b hb
    by_cases h0 : p.ofLp 0 ≤ b.ofLp 0 <;> by_cases h1 : p.ofLp 1 ≤ b.ofLp 1
    · refine ⟨mk2 A A, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
      have f1 : |p.ofLp 0 - b.ofLp 0| = -(p.ofLp 0 - b.ofLp 0) := abs_of_nonpos (by linarith)
      have f2 : |p.ofLp 1 - b.ofLp 1| = -(p.ofLp 1 - b.ofLp 1) := abs_of_nonpos (by linarith)
      have f3 : |b.ofLp 0 - A| = -(b.ofLp 0 - A) := abs_of_nonpos (by linarith)
      have f4 : |b.ofLp 1 - A| = -(b.ofLp 1 - A) := abs_of_nonpos (by linarith)
      have f5 : |p.ofLp 0 - A| = -(p.ofLp 0 - A) := abs_of_nonpos (by linarith)
      have f6 : |p.ofLp 1 - A| = -(p.ofLp 1 - A) := abs_of_nonpos (by linarith)
      simp only [dist2, mk2_0, mk2_1]
      linarith
    · refine ⟨mk2 A (-A), Or.inr (Or.inl rfl), ?_⟩
      have f1 : |p.ofLp 0 - b.ofLp 0| = -(p.ofLp 0 - b.ofLp 0) := abs_of_nonpos (by linarith)
      have f2 : |p.ofLp 1 - b.ofLp 1| = p.ofLp 1 - b.ofLp 1 := abs_of_nonneg (by linarith)
      have f3 : |b.ofLp 0 - A| = -(b.ofLp 0 - A) := abs_of_nonpos (by linarith)
      have f4 : |b.ofLp 1 - (-A)| = b.ofLp 1 - (-A) := abs_of_nonneg (by linarith)
      have f5 : |p.ofLp 0 - A| = -(p.ofLp 0 - A) := abs_of_nonpos (by linarith)
      have f6 : |p.ofLp 1 - (-A)| = p.ofLp 1 - (-A) := abs_of_nonneg (by linarith)
      simp only [dist2, mk2_0, mk2_1]
      linarith
    · refine ⟨mk2 (-A) A, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
      have f1 : |p.ofLp 0 - b.ofLp 0| = p.ofLp 0 - b.ofLp 0 := abs_of_nonneg (by linarith)
      have f2 : |p.ofLp 1 - b.ofLp 1| = -(p.ofLp 1 - b.ofLp 1) := abs_of_nonpos (by linarith)
      have f3 : |b.ofLp 0 - (-A)| = b.ofLp 0 - (-A) := abs_of_nonneg (by linarith)
      have f4 : |b.ofLp 1 - A| = -(b.ofLp 1 - A) := abs_of_nonpos (by linarith)
      have f5 : |p.ofLp 0 - (-A)| = p.ofLp 0 - (-A) := abs_of_nonneg (by linarith)
      have f6 : |p.ofLp 1 - A| = -(p.ofLp 1 - A) := abs_of_nonpos (by linarith)
      simp only [dist2, mk2_0, mk2_1]
      linarith
    · refine ⟨mk2 (-A) (-A), Or.inl rfl, ?_⟩
      have f1 : |p.ofLp 0 - b.ofLp 0| = p.ofLp 0 - b.ofLp 0 := abs_of_nonneg (by linarith)
      have f2 : |p.ofLp 1 - b.ofLp 1| = p.ofLp 1 - b.ofLp 1 := abs_of_nonneg (by linarith)
      have f3 : |b.ofLp 0 - (-A)| = b.ofLp 0 - (-A) := abs_of_nonneg (by linarith)
      have f4 : |b.ofLp 1 - (-A)| = b.ofLp 1 - (-A) := abs_of_nonneg (by linarith)
      have f5 : |p.ofLp 0 - (-A)| = p.ofLp 0 - (-A) := abs_of_nonneg (by linarith)
      have f6 : |p.ofLp 1 - (-A)| = p.ofLp 1 - (-A) := abs_of_nonneg (by linarith)
      simp only [dist2, mk2_0, mk2_1]
      linarith
