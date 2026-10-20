-- Prove2me | solution 2 for OAI.LipschitzCounterexample.WeightedGraph.lipschitz_lift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:46:45.127693+00:00
-- url     : https://prove2.me/submissions/7043e8b8-af65-481e-931e-fd1d9115bb48

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/WeightedGraph.lean:L199-L234
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.WeightedGraph.lipschitz_lift. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph

-- ---- from OAI.Analysis.LipschitzEquivalence.WeightedGraph ----
namespace OAI

universe uA uH uB uJ

noncomputable section
namespace LipschitzCounterexample

namespace WeightedGraph
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

 theorem lipschitz_lift : LipschitzWith (max K L) (lift Q R F g hF hg hF0 hg0 hdiag) := by
  apply lipschitzWith_iff_norm_sub_le.2
  intro s t
  rw [norm_eq]
  apply max_le
  · calc
      (∑' i, weight i * ‖coord R (lift Q R F g hF hg hF0 hg0 hdiag s -
        lift Q R F g hF hg hF0 hg0 hdiag t) i‖) ≤
          ∑' i, (K : ℝ) * (weight i * ‖coord Q (s - t) i‖) := by
            apply Summable.tsum_le_tsum
            · intro i
              simp only [coord_sub, coord_lift]
              calc
                _ ≤ weight i * (K * ‖coord Q s i - coord Q t i‖) :=
                  mul_le_mul_of_nonneg_left (hF.norm_sub_le _ _) (weight_nonneg i)
                _ = _ := by ring
            · exact summable_weighted_norm R _
            · exact (summable_weighted_norm Q _).mul_left _
      _ = K * (∑' i, weight i * ‖coord Q (s - t) i‖) := tsum_mul_left
      _ ≤ K * ‖s - t‖ := by
        apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
        rw [norm_eq]
        exact le_max_left _ _
      _ ≤ (max K L : ℝ≥0) * ‖s - t‖ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left K L) (norm_nonneg _)
  · apply le_trans _ (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_right K L) (norm_nonneg (s - t)))
    apply (NullSequences.norm_le (mul_nonneg L.coe_nonneg (norm_nonneg (s - t)))).2
    intro i
    rw [← map_coord, coord_sub, map_sub, coord_lift, coord_lift, hdiag, hdiag]
    apply (hg.norm_sub_le _ _).trans
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    rw [map_coord, map_coord]
    change ‖(output Q s - output Q t) i‖ ≤ ‖s - t‖
    rw [← map_sub]
    exact (NullSequences.norm_apply_le _ i).trans (norm_output_le Q _)

end WeightedGraph

end LipschitzCounterexample
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeightedGraph
open scoped ENNReal NNReal Topology
open Filter


theorem solution.{uA,uH,uB,uJ} : type_of% @_root_.OAI.LipschitzCounterexample.WeightedGraph.lipschitz_lift.{uA,uH,uB,uJ} := @_root_.OAI.LipschitzCounterexample.WeightedGraph.lipschitz_lift.{uA,uH,uB,uJ}
