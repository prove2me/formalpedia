-- Prove2me | solution 1 for JaggiFW.Sparsity.support_simplex
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:46:25.375731+00:00
-- url     : https://prove2.me/submissions/92678ea6-38f1-4008-be13-abd99b6f0833

import Mathlib
import Definitions.Def_JaggiFW_Sparsity_Setting

open JaggiFW.Sparsity

theorem solution {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) :
    stdSimplex ℝ (Fin n) = convexHull ℝ (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → ℝ)) ∧
    ∃ i : Fin n, (∀ j, y j ≤ y i) ∧
      IsGreatest ((fun s => ∑ j, s j * y j) '' stdSimplex ℝ (Fin n)) (y i) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨(convexHull_rangle_single_eq_stdSimplex ℝ (Fin n)).symm, ?_⟩
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ y Finset.univ_nonempty
  refine ⟨i, fun j => hmax j (Finset.mem_univ j), ?_⟩
  constructor
  · refine ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, ?_⟩
    simp [Pi.single_apply]
  · rintro r ⟨s, hs, rfl⟩
    calc
      ∑ j, s j * y j ≤ ∑ j, s j * y i :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j)) (hs.1 j)
      _ = y i := by rw [← Finset.sum_mul, hs.2, one_mul]
