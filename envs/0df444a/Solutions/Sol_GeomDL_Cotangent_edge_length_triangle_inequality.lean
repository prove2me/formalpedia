-- Prove2me | solution 1 for GeomDL.Cotangent.edge_length_triangle_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:41:39.841641+00:00
-- url     : https://prove2.me/submissions/089abe3d-4f6d-47ac-80a5-c8066546661f

import Mathlib
import Definitions.Def_GeomDL_Cotangent_Defs

open EuclideanGeometry GeomDL.Cotangent

theorem solution {P : Type*} [MetricSpace P] {n : ℕ} (M : TriMesh n) (x : Fin n → P)
    (hmesh : IsManifoldMesh M) {u v q : Fin n} (hF : (u, v, q) ∈ M.faces) :
    edgeLength x u v ≤ edgeLength x u q + edgeLength x v q ∧
    edgeLength x u q ≤ edgeLength x u v + edgeLength x q v ∧
    edgeLength x v q ≤ edgeLength x v u + edgeLength x q u := by
  simp only [edgeLength]
  exact ⟨dist_triangle_right _ _ _, dist_triangle_right _ _ _, dist_triangle_right _ _ _⟩
