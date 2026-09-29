-- Prove2me | solution 1 for LogRegretOCO.EWOO.shrunk_set_volume
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:52:32.172302+00:00
-- url     : https://prove2.me/submissions/f7ea3055-e0f2-4194-bb76-1bfd1533a2b9

import Mathlib
import Definitions.Def_LogRegretOCO_EWOO_shrunkSet

open MeasureTheory
open LogRegretOCO.EWOO

theorem solution (n : ℕ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (xstar : EuclideanSpace ℝ (Fin n)) (T : ℕ) :
    volume (shrunkSet P xstar T) = volume P / ((T : ENNReal) + 1) ^ n := by
  have hT : ((T : ℝ) + 1) ≠ 0 := by positivity
  have hTpos : (0 : ℝ) < 1 / ((T : ℝ) + 1) := by positivity
  have hset : shrunkSet P xstar T
      = AffineMap.homothety xstar (1 / ((T : ℝ) + 1)) '' P := by
    ext x
    simp only [shrunkSet, Set.mem_setOf_eq, Set.mem_image, AffineMap.homothety_apply,
      vsub_eq_sub, vadd_eq_add]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      have hcoef : ((T : ℝ) / ((T : ℝ) + 1)) = 1 - 1 / ((T : ℝ) + 1) := by field_simp; ring
      rw [hcoef]
      module
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      have hcoef : ((T : ℝ) / ((T : ℝ) + 1)) = 1 - 1 / ((T : ℝ) + 1) := by field_simp; ring
      rw [hcoef]
      module
  rw [hset, Measure.addHaar_image_homothety]
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    simp
  rw [hfr, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / ((T : ℝ) + 1)) ^ n)]
  have h1 : ENNReal.ofReal (1 / ((T : ℝ) + 1)) = ((T : ENNReal) + 1)⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  rw [ENNReal.ofReal_pow (le_of_lt hTpos), h1, div_eq_mul_inv, ← ENNReal.inv_pow]
  ring
