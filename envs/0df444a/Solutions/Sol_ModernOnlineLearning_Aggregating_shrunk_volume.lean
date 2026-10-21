-- Prove2me | solution 1 for ModernOnlineLearning.Aggregating.shrunk_volume
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:58:15.43984+00:00
-- url     : https://prove2.me/submissions/47273ee3-bd32-4c72-97de-ae5b465c5d55

import Mathlib
import Definitions.Def_ModernOnlineLearning_Aggregating_ShrunkSet
set_option autoImplicit false
open MeasureTheory ModernOnlineLearning.Aggregating

theorem solution {d : ℕ} (hd : 0 < d) (T : ℕ) (hT : 0 < T)
    (V : Set (EuclideanSpace ℝ (Fin d)))
    (hconv : Convex ℝ V) (hclosed : IsClosed V) (hbounded : Bornology.IsBounded V)
    (hvol_pos : 0 < volume V) (hvol_fin : volume V < ⊤)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ V) :
    volume (shrunkSet V u T) / volume V =
      ENNReal.ofReal (1 / (((T : ℝ) / (d : ℝ) + 1) ^ d)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  set t : ℝ := 1 / ((T : ℝ) / (d : ℝ) + 1) with ht
  have hpos : 0 < (T : ℝ) / (d : ℝ) + 1 := by positivity
  have hset : shrunkSet V u T = AffineMap.homothety u t '' V := by
    unfold shrunkSet
    congr 1
    funext w
    have hc : ((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1) = 1 - t := by
      rw [ht]; field_simp; ring
    rw [hc, AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  rw [hset, Measure.addHaar_image_homothety, finrank_euclideanSpace_fin,
    ENNReal.mul_div_cancel_right hvol_pos.ne' hvol_fin.ne]
  congr 1
  rw [abs_of_pos (by positivity), ht, one_div, inv_pow, one_div]
