-- Prove2me | solution 1 for KellyReversibility.Allocation.multiplier_choice
-- status  : ACCEPTED   (prove)
-- author  : @techtao
-- created : 2026-10-05T03:43:27.246313+00:00
-- url     : https://prove2.me/submissions/a4925332-a0aa-4939-89d7-d1e94266e7be

import Definitions.Def_KellyReversibility_Allocation_CapacityAllocation
set_option autoImplicit false

-- Exact target: https://prove2.me/theorems/8bc3ef13-7aef-410e-8edc-dd9221d14337
-- Every helper is closed locally; no target theorem or open lemma is imported.


open KellyReversibility.Allocation

namespace CapacityWork

theorem multiplier_choice {J : ℕ} (hJ : 0 < J) (a f : Fin J → ℝ) (F : ℝ)
    (ha : ∀ j, 0 < a j) (hf : ∀ j, 0 < f j) (hF : ∑ k, a k * f k < F) :
    let y : ℝ := ((∑ k, Real.sqrt (a k * f k)) / (F - ∑ k, a k * f k)) ^ 2
    0 < y ∧ 1 / Real.sqrt y = (F - ∑ k, a k * f k) / ∑ k, Real.sqrt (a k * f k) ∧
      (∀ j, a j + Real.sqrt (a j / (y * f j)) = optimalAllocation a f F j) ∧
      ∑ j, f j * (a j + Real.sqrt (a j / (y * f j))) = F := by
  classical
  let A : ℝ := ∑ k : Fin J, a k * f k
  let S : ℝ := ∑ k : Fin J, Real.sqrt (a k * f k)
  let T : ℝ := F - A
  let y : ℝ := (S / T) ^ 2
  change 0 < y ∧ 1 / Real.sqrt y = T / S ∧
    (∀ j, a j + Real.sqrt (a j / (y * f j)) = optimalAllocation a f F j) ∧
    ∑ j, f j * (a j + Real.sqrt (a j / (y * f j))) = F

  have hprod : ∀ j : Fin J, 0 < a j * f j := fun j => mul_pos (ha j) (hf j)
  have hS : 0 < S := by
    dsimp [S]
    apply Finset.sum_pos
    · intro j hj
      exact Real.sqrt_pos.2 (hprod j)
    · apply Finset.card_pos.mp
      simpa using hJ
  have hA_lt_F : A < F := by simpa [A] using hF
  have hT : 0 < T := by
    dsimp [T]
    exact sub_pos.mpr hA_lt_F
  have hS_ne : S ≠ 0 := ne_of_gt hS
  have hT_ne : T ≠ 0 := ne_of_gt hT

  have hy : 0 < y := by
    dsimp [y]
    positivity
  have hroot : Real.sqrt y = S / T := by
    dsimp [y]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (div_pos hS hT)]
  have hrecip : 1 / Real.sqrt y = T / S := by
    rw [hroot]
    field_simp [hS_ne, hT_ne]

  have hpoint : ∀ j : Fin J,
      a j + Real.sqrt (a j / (y * f j)) = optimalAllocation a f F j := by
    intro j
    have haf : 0 < a j * f j := hprod j
    have hrad : a j / (y * f j) =
        ((T / S) * (Real.sqrt (a j * f j) / f j)) ^ 2 := by
      dsimp [y]
      field_simp [hS_ne, hT_ne, ne_of_gt (hf j)]
      rw [Real.sq_sqrt (le_of_lt haf)]
    have hfactor_pos : 0 < (T / S) * (Real.sqrt (a j * f j) / f j) :=
      mul_pos (div_pos hT hS)
        (div_pos (Real.sqrt_pos.2 haf) (hf j))
    change a j + Real.sqrt (a j / (y * f j)) =
      a j + (Real.sqrt (a j * f j) / S) * (T / f j)
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_pos hfactor_pos]
    congr 1
    field_simp [hS_ne, ne_of_gt (hf j)]

  have hbudget_term : ∀ j : Fin J,
      f j * (a j + Real.sqrt (a j / (y * f j))) =
        f j * a j + (T / S) * Real.sqrt (a j * f j) := by
    intro j
    rw [hpoint j]
    change f j * (a j + (Real.sqrt (a j * f j) / S) * (T / f j)) =
      f j * a j + (T / S) * Real.sqrt (a j * f j)
    field_simp [hS_ne, ne_of_gt (hf j)]

  have hsum_fa : (∑ j : Fin J, f j * a j) = A := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro j hj
    ring

  have hbudget : ∑ j : Fin J,
      f j * (a j + Real.sqrt (a j / (y * f j))) = F := by
    calc
      ∑ j, f j * (a j + Real.sqrt (a j / (y * f j))) =
          ∑ j, (f j * a j + (T / S) * Real.sqrt (a j * f j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hbudget_term j
      _ = (∑ j, f j * a j) + (T / S) * S := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = F := by
        rw [hsum_fa]
        dsimp [T]
        rw [div_mul_cancel₀ _ hS_ne]
        ring

  exact ⟨hy, hrecip, hpoint, hbudget⟩

end CapacityWork

theorem solution {J : ℕ} (hJ : 0 < J) (a f : Fin J → ℝ) (F : ℝ)
    (ha : ∀ j, 0 < a j) (hf : ∀ j, 0 < f j) (hF : ∑ k, a k * f k < F) :
    let y : ℝ := ((∑ k, Real.sqrt (a k * f k)) / (F - ∑ k, a k * f k)) ^ 2
    0 < y ∧ 1 / Real.sqrt y = (F - ∑ k, a k * f k) / ∑ k, Real.sqrt (a k * f k) ∧
      (∀ j, a j + Real.sqrt (a j / (y * f j)) = optimalAllocation a f F j) ∧
      ∑ j, f j * (a j + Real.sqrt (a j / (y * f j))) = F := by
  exact CapacityWork.multiplier_choice hJ a f F ha hf hF

#print axioms solution
