-- Prove2me | solution 1 for GeomDL.Cotangent.isometry_invariance
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:55:10.813439+00:00
-- url     : https://prove2.me/submissions/1658c3be-40ed-4399-b616-43e7b72763e7

import Mathlib
import Definitions.Def_GeomDL_Cotangent_Defs

open EuclideanGeometry GeomDL.Cotangent

theorem angle_eq_of_dists_aux {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (a b c a' b' c' : P)
    (h1 : dist a c = dist a' c') (h2 : dist b c = dist b' c') (h3 : dist a b = dist a' b') :
    ∠ a c b = ∠ a' c' b' := by
  by_cases hac : a = c
  · have : a' = c' := dist_eq_zero.mp (by rw [← h1, hac, dist_self])
    subst hac; subst this
    rw [angle_self_left, angle_self_left]
  by_cases hbc : b = c
  · have : b' = c' := dist_eq_zero.mp (by rw [← h2, hbc, dist_self])
    subst hbc; subst this
    rw [angle_self_right, angle_self_right]
  have hac' : dist a c ≠ 0 := dist_ne_zero.2 hac
  have hbc' : dist b c ≠ 0 := dist_ne_zero.2 hbc
  have l1 := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
    a c b
  have l2 := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
    a' c' b'
  rw [← h1, ← h2, ← h3] at l2
  have hcos : Real.cos (∠ a c b) = Real.cos (∠ a' c' b') := by
    have hne : 2 * dist a c * dist b c ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    linarith
  exact Real.injOn_cos ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
    ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩ hcos

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {n : ℕ} (M : TriMesh n) (x x' : Fin n → P)
    (hmesh : IsManifoldMesh M) (hℓ : ∀ t ∈ M.faces,
      edgeLength x t.1 t.2.1 = edgeLength x' t.1 t.2.1 ∧
      edgeLength x t.2.1 t.2.2 = edgeLength x' t.2.1 t.2.2 ∧
      edgeLength x t.1 t.2.2 = edgeLength x' t.1 t.2.2) :
    cotLaplacian M x = cotLaplacian M x' := by
  have hopp : ∀ t ∈ M.faces, ∀ u v, cotOpp x t u v = cotOpp x' t u v := by
    intro t ht u v
    obtain ⟨e1, e2, e3⟩ := hℓ t ht
    simp only [edgeLength] at e1 e2 e3
    have A1 : ∠ (x t.1) (x t.2.2) (x t.2.1) = ∠ (x' t.1) (x' t.2.2) (x' t.2.1) :=
      angle_eq_of_dists_aux _ _ _ _ _ _ e3 (by simpa [dist_comm] using e2) e1
    have A2 : ∠ (x t.2.1) (x t.1) (x t.2.2) = ∠ (x' t.2.1) (x' t.1) (x' t.2.2) :=
      angle_eq_of_dists_aux _ _ _ _ _ _ (by simpa [dist_comm] using e1)
        (by simpa [dist_comm] using e3) e2
    have A3 : ∠ (x t.1) (x t.2.1) (x t.2.2) = ∠ (x' t.1) (x' t.2.1) (x' t.2.2) :=
      angle_eq_of_dists_aux _ _ _ _ _ _ e1 (by simpa [dist_comm] using e2) e3
    simp only [cotOpp, A1, A2, A3]
  have harea : ∀ t ∈ M.faces, triArea (x t.1) (x t.2.1) (x t.2.2) =
      triArea (x' t.1) (x' t.2.1) (x' t.2.2) := by
    intro t ht
    obtain ⟨e1, e2, e3⟩ := hℓ t ht
    simp only [edgeLength] at e1 e2 e3
    have A1 : ∠ (x t.1) (x t.2.2) (x t.2.1) = ∠ (x' t.1) (x' t.2.2) (x' t.2.1) :=
      angle_eq_of_dists_aux _ _ _ _ _ _ e3 (by simpa [dist_comm] using e2) e1
    simp only [triArea, A1, e3]
    have e2' : dist (x t.2.1) (x t.2.2) = dist (x' t.2.1) (x' t.2.2) := e2
    rw [e2']
  have hw : ∀ u v, cotWeight M x u v = cotWeight M x' u v := by
    intro u v
    simp only [cotWeight, vertexArea]
    rw [Finset.sum_congr rfl (fun t ht => hopp t ht u v)]
    rw [Finset.sum_congr rfl (fun t ht => harea t (Finset.mem_filter.mp ht).1)]
  simp only [cotLaplacian, laplacianOf, hw]
