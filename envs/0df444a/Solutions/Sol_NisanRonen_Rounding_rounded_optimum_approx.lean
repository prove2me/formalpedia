-- Prove2me | solution 1 for NisanRonen.Rounding.rounded_optimum_approx
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:46:51.796858+00:00
-- url     : https://prove2.me/submissions/7b76929a-e82a-4923-8a35-6e851b0711aa

import Mathlib
import Definitions.Def_NisanRonen_Rounding_roundedMakespan
import Definitions.Def_NisanRonen_Rounding_corrStar

open NisanRonen.Rounding in
theorem solution {n k : ℕ} [NeZero n] {a b δ : ℝ} (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (t : Fin n → Fin k → ℝ) (ht : ∀ i j, a ≤ t i j ∧ t i j ≤ b)
    (x : Fin k → Fin n)
    (hx : ∀ y : Fin k → Fin n, roundedMakespan δ x (corrStar x t) ≤ roundedMakespan δ y (corrStar y t)) :
    ∀ y : Fin k → Fin n, makespan x (corrStar x t) ≤ (1 + δ / a) * makespan y (corrStar y t) := by
  intro y
  have hda : 0 < δ / a := div_pos hδ ha
  have hc : 0 < 1 + δ / a := by linarith
  have r1 : ∀ v, v ≤ roundUp δ v := by
    intro v
    unfold roundUp
    have h1 := Int.le_ceil (v / δ)
    have h2 := mul_le_mul_of_nonneg_left h1 hδ.le
    rwa [mul_div_cancel₀ v hδ.ne'] at h2
  have r2 : ∀ v, a ≤ v → roundUp δ v ≤ (1 + δ / a) * v := by
    intro v hv
    unfold roundUp
    have h1 := (Int.ceil_lt_add_one (v / δ)).le
    have h2 := mul_le_mul_of_nonneg_left h1 hδ.le
    rw [mul_add, mul_div_cancel₀ v hδ.ne', mul_one] at h2
    have h3 : δ ≤ δ / a * v := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      exact mul_le_mul_of_nonneg_left hv hδ.le
    nlinarith
  have step1 : makespan x (corrStar x t) ≤ roundedMakespan δ x (corrStar x t) := by
    unfold roundedMakespan makespan
    apply Finset.sup'_le
    intro i _
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ i))
    unfold load
    exact Finset.sum_le_sum fun j _ => r1 _
  have step3 : roundedMakespan δ y (corrStar y t) ≤ (1 + δ / a) * makespan y (corrStar y t) := by
    unfold roundedMakespan makespan
    apply Finset.sup'_le
    intro i _
    calc load y (fun j => roundUp δ (corrStar y t j)) i
        ≤ (1 + δ / a) * load y (corrStar y t) i := by
          unfold load
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun j _ => r2 _ (ht _ _).1
      _ ≤ (1 + δ / a) * Finset.univ.sup' Finset.univ_nonempty (load y (corrStar y t)) :=
          mul_le_mul_of_nonneg_left (Finset.le_sup' _ (Finset.mem_univ i)) hc.le
  linarith [hx y]
