-- Prove2me | solution 1 for LinearOptimization.convex_hull_finite_is_polyhedron
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T16:41:40.421944+00:00
-- url     : https://prove2.me/submissions/6f5ca37f-696f-435c-8daa-f03847b6ad67

import Theorems.Thm_LinearOptimization_polyhedron_linear_image
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Fin

open Matrix Set

namespace LinearOptimization

def vertexMatrix {n k : ℕ} (v : Fin k → (Fin n → ℝ)) :
    Matrix (Fin n) (Fin k) ℝ := fun i j => v j i

def vertexLinearMap {n k : ℕ} (v : Fin k → (Fin n → ℝ)) :
    (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := (vertexMatrix v).mulVec
  map_add' x y := by
    ext i
    simp [vertexMatrix, Matrix.mulVec, dotProduct, Finset.sum_add_distrib, mul_add]
  map_smul' c x := by
    ext i
    simp [vertexMatrix, Matrix.mulVec, dotProduct, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]

theorem vertexLinearMap_basis {n k : ℕ} (v : Fin k → (Fin n → ℝ)) (j : Fin k) :
    vertexLinearMap v (fun q => if j = q then 1 else 0) = v j := by
  ext i
  simp [vertexLinearMap, vertexMatrix, Matrix.mulVec, dotProduct]

theorem convexHull_eq_vertex_image_simplex {n k : ℕ} (v : Fin k → (Fin n → ℝ)) :
    convexHull ℝ (Set.range v) = vertexLinearMap v '' stdSimplex ℝ (Fin k) := by
  calc
    convexHull ℝ (Set.range v) =
        convexHull ℝ (vertexLinearMap v ''
          Set.range (fun j q : Fin k => if j = q then (1 : ℝ) else 0)) := by
      congr 1
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨_, ⟨j, rfl⟩, vertexLinearMap_basis v j⟩
      · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
        exact ⟨j, (vertexLinearMap_basis v j).symm⟩
    _ = vertexLinearMap v ''
        convexHull ℝ (Set.range (fun j q : Fin k => if j = q then (1 : ℝ) else 0)) := by
      rw [LinearMap.image_convexHull]
    _ = vertexLinearMap v '' stdSimplex ℝ (Fin k) := by
      rw [convexHull_basis_eq_stdSimplex]

def simplexMatrix (k : ℕ) : Matrix (Fin (k + 2)) (Fin k) ℝ :=
  fun i j => Fin.lastCases (-1)
    (fun q => Fin.lastCases 1 (fun r => if r = j then 1 else 0) q) i

def simplexRhs (k : ℕ) : Fin (k + 2) → ℝ :=
  fun i => Fin.lastCases (-1) (fun q => Fin.lastCases 1 (fun _ => 0) q) i

theorem simplex_mulVec_coord (k : ℕ) (x : Fin k → ℝ) (r : Fin k) :
    (simplexMatrix k).mulVec x r.castSucc.castSucc = x r := by
  simp [simplexMatrix, Matrix.mulVec, dotProduct]

theorem simplex_mulVec_sum (k : ℕ) (x : Fin k → ℝ) :
    (simplexMatrix k).mulVec x (Fin.last k).castSucc = ∑ i, x i := by
  simp [simplexMatrix, Matrix.mulVec, dotProduct]

theorem simplex_mulVec_neg_sum (k : ℕ) (x : Fin k → ℝ) :
    (simplexMatrix k).mulVec x (Fin.last (k + 1)) = -(∑ i, x i) := by
  simp [simplexMatrix, Matrix.mulVec, dotProduct, ← Finset.sum_neg_distrib]

theorem stdSimplex_eq_polyhedron (k : ℕ) :
    stdSimplex ℝ (Fin k) = polyhedron (simplexMatrix k) (simplexRhs k) := by
  ext x
  constructor
  · rintro ⟨hx, hsum⟩ i
    refine Fin.lastCases
      (motive := fun i => simplexRhs k i ≤ (simplexMatrix k).mulVec x i)
      (by
        change simplexRhs k (Fin.last (k + 1)) ≤
          (simplexMatrix k).mulVec x (Fin.last (k + 1))
        rw [simplex_mulVec_neg_sum]
        simp [simplexRhs, hsum])
      (fun q => by
        refine Fin.lastCases
          (motive := fun q => simplexRhs k q.castSucc ≤
            (simplexMatrix k).mulVec x q.castSucc)
          (by
            change simplexRhs k (Fin.last k).castSucc ≤
              (simplexMatrix k).mulVec x (Fin.last k).castSucc
            rw [simplex_mulVec_sum]
            simp [simplexRhs, hsum])
          (fun r => by
            change simplexRhs k r.castSucc.castSucc ≤
              (simplexMatrix k).mulVec x r.castSucc.castSucc
            rw [simplex_mulVec_coord]
            simpa [simplexRhs] using hx r) q)
      i
  · intro h
    constructor
    · intro r
      have hr := h r.castSucc.castSucc
      simpa [simplexRhs, simplex_mulVec_coord] using hr
    · have hlo := h (Fin.last k).castSucc
      have hhi := h (Fin.last (k + 1))
      simp [simplexRhs, simplex_mulVec_sum] at hlo
      simp [simplexRhs, simplex_mulVec_neg_sum] at hhi
      linarith

end LinearOptimization

theorem solution {n k : ℕ}
    (v : Fin k → (Fin n → ℝ)) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
      convexHull ℝ (Set.range v) = LinearOptimization.polyhedron A' b' := by
  obtain ⟨m', A', b', himage⟩ :=
    LinearOptimization.polyhedron_linear_image
      (LinearOptimization.simplexMatrix k) (LinearOptimization.simplexRhs k)
      (LinearOptimization.vertexMatrix v)
  refine ⟨m', A', b', ?_⟩
  rw [LinearOptimization.convexHull_eq_vertex_image_simplex]
  change (LinearOptimization.vertexMatrix v).mulVec '' stdSimplex ℝ (Fin k) =
    LinearOptimization.polyhedron A' b'
  rw [LinearOptimization.stdSimplex_eq_polyhedron]
  exact himage
