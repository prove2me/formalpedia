-- Prove2me | solution 1 for OAI.LipschitzCounterexample.WeightedGraph.lipschitz_lift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T19:44:01.084292+00:00
-- url     : https://prove2.me/submissions/bb46eaf4-7149-4f6f-8130-8dffa10a9a8a

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeightedGraph
universe uA uH uB uJ
open scoped ENNReal NNReal Topology
open Filter
variable {A : Type uA} {H : Type uH} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (Q : A →L[ℝ] H)
variable {B : Type uB} {J : Type uJ} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup J] [NormedSpace ℝ J]
variable (R : B →L[ℝ] J) (F : A → B) (g : H → J)
  {K L : ℝ≥0} (hF : LipschitzWith K F) (hg : LipschitzWith L g)
  (hF0 : F 0 = 0) (hg0 : g 0 = 0) (hdiag : ∀ x, R (F x) = g (Q x))


theorem solution : LipschitzWith (max K L) (lift Q R F g hF hg hF0 hg0 hdiag) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm, dist_eq_norm, norm_eq R]
  have hst := norm_eq Q (s - t)
  have hsum1 := summable_weighted_norm R
    (lift Q R F g hF hg hF0 hg0 hdiag s - lift Q R F g hF hg hF0 hg0 hdiag t)
  have hsum2 := summable_weighted_norm Q (s - t)
  have hA : ∑' i, weight i * ‖coord Q (s - t) i‖ ≤ ‖s - t‖ := by
    rw [hst]; exact le_max_left _ _
  have hB : ‖output Q (s - t)‖ ≤ ‖s - t‖ := norm_output_le Q (s - t)
  have hKm : (K:ℝ) ≤ ((max K L : ℝ≥0) : ℝ) := by exact_mod_cast le_max_left K L
  have hLm : (L:ℝ) ≤ ((max K L : ℝ≥0) : ℝ) := by exact_mod_cast le_max_right K L
  have hn : 0 ≤ ‖s - t‖ := norm_nonneg _
  apply max_le
  · calc ∑' i, weight i * ‖coord R (lift Q R F g hF hg hF0 hg0 hdiag s -
            lift Q R F g hF hg hF0 hg0 hdiag t) i‖
          ≤ ∑' i, (K:ℝ) * (weight i * ‖coord Q (s - t) i‖) := by
            apply Summable.tsum_le_tsum _ hsum1 (hsum2.mul_left _)
            intro i
            rw [coord_sub, coord_lift, coord_lift, coord_sub]
            have h1 := hF.norm_sub_le (coord Q s i) (coord Q t i)
            have h2 := weight_nonneg i
            calc weight i * ‖F (coord Q s i) - F (coord Q t i)‖
                ≤ weight i * ((K:ℝ) * ‖coord Q s i - coord Q t i‖) :=
                  mul_le_mul_of_nonneg_left h1 h2
              _ = _ := by ring
        _ = (K:ℝ) * ∑' i, weight i * ‖coord Q (s - t) i‖ := tsum_mul_left
        _ ≤ (K:ℝ) * ‖s - t‖ := mul_le_mul_of_nonneg_left hA K.coe_nonneg
        _ ≤ _ := mul_le_mul_of_nonneg_right hKm hn
  · rw [NullSequences.norm_le (by positivity)]
    intro i
    rw [← map_coord R, coord_sub, coord_lift, coord_lift, map_sub, hdiag, hdiag, map_coord,
      map_coord]
    calc _ ≤ (L:ℝ) * ‖output Q s i - output Q t i‖ := hg.norm_sub_le _ _
      _ = (L:ℝ) * ‖output Q (s - t) i‖ := by rw [map_sub]; rfl
      _ ≤ (L:ℝ) * ‖s - t‖ :=
        mul_le_mul_of_nonneg_left ((NullSequences.norm_apply_le _ i).trans hB) L.coe_nonneg
      _ ≤ _ := mul_le_mul_of_nonneg_right hLm hn

