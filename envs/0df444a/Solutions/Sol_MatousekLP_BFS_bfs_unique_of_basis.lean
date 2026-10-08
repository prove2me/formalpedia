-- Prove2me | solution 1 for MatousekLP.BFS.bfs_unique_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T03:56:06.029807+00:00
-- url     : https://prove2.me/submissions/f5ce6bfc-db57-4c1d-a3d8-bc9841f35f75

import Definitions.Def_MatousekLP_BFS_EquationalForm
import Mathlib

open Matrix MatousekLP.BFS

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (hmn : m ≤ n) (hrank : A.rank = m) (B : Finset (Fin n))
    (hB : IsBasis A B) (x y : Fin n → ℝ)
    (hx : IsFeasible A b x) (hxB : ∀ j, j ∉ B → x j = 0)
    (hy : IsFeasible A b y) (hyB : ∀ j, j ∉ B → y j = 0) :
    x = y := by
  obtain ⟨-, hli⟩ := hB
  set d : Fin n → ℝ := x - y
  have hdB : ∀ j, j ∉ B → d j = 0 := fun j hj => by simp [d, hxB j hj, hyB j hj]
  have hAd : A *ᵥ d = 0 := by simp [d, mulVec_sub, hx.1, hy.1]
  -- `A d` is the combination of the basic columns with coefficients `d`
  have hcomb : ∑ j : B, d j • (fun i : Fin m => A i (j : Fin n)) = 0 := by
    funext i
    have h := congrFun hAd i
    simp only [mulVec, dotProduct, Pi.zero_apply] at h
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc ∑ j : B, d j * A i j = ∑ j ∈ B, d j * A i j := Finset.sum_coe_sort B (fun j => d j * A i j)
      _ = ∑ j, d j * A i j :=
          Finset.sum_subset (Finset.subset_univ B) (fun j _ hj => by simp [hdB j hj])
      _ = 0 := by rw [← h]; exact Finset.sum_congr rfl fun j _ => by ring
  have hzero := (Fintype.linearIndependent_iff.mp hli) (fun j => d j) hcomb
  funext j
  by_cases hj : j ∈ B
  · have := hzero ⟨j, hj⟩
    simpa [d, sub_eq_zero] using this
  · rw [hxB j hj, hyB j hj]
