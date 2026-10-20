-- Prove2me | solution 2 for OAI.LipschitzCounterexample.LocalizedLinearization.disjointOperator_coord
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:04:31.737456+00:00
-- url     : https://prove2.me/submissions/922b5ee4-ed3c-433e-969c-a90d599964e9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/Localization.lean:L245-L259
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.LocalizedLinearization.disjointOperator_coord. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_linearize_unique

-- ---- from OAI.Analysis.LipschitzEquivalence.Localization ----
namespace OAI

universe uM uV

noncomputable section
namespace LipschitzCounterexample

namespace LocalizedLinearization
open Filter Topology
open scoped NNReal ENNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

omit [Zero M] [MetricSpace M] in
theorem activeIndex_spec {h : ℕ → M → ℝ} (hd : DisjointTests h) (x : M) :
    ∀ j, j ≠ activeIndex hd x → h j x = 0 := (hd.exists_index x).choose_spec

omit [Zero M] [MetricSpace M] in
theorem disjointMap_apply {h : ℕ → M → ℝ} (hd : DisjointTests h) (x : M) (i : ℕ) :
    disjointMap hd x i = h i x := by
  classical
  by_cases hi : i = activeIndex hd x
  · subst i
    simp [disjointMap]
  · simp [disjointMap, lp.single_apply, hi, activeIndex_spec hd x i hi]

omit [Zero M] in
theorem disjointMap_lipschitz {h : ℕ → M → ℝ} (hd : DisjointTests h)
    {K : ℝ≥0} (hh : ∀ i, LipschitzWith K (h i)) :
    LipschitzWith (2 * K) (disjointMap hd) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  by_cases hi : activeIndex hd x = activeIndex hd y
  · unfold disjointMap
    rw [← hi, ← lp.single_sub, lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞))]
    calc
      ‖h (activeIndex hd x) x - h (activeIndex hd x) y‖ ≤ K * dist x y :=
        (hh _).dist_le_mul x y
      _ ≤ (2 * K : ℝ≥0) * dist x y := by
        simp only [NNReal.coe_mul, NNReal.coe_ofNat]
        nlinarith [K.coe_nonneg, dist_nonneg (x := x) (y := y)]
  · have hxy := activeIndex_spec hd y (activeIndex hd x) hi
    have hyx := activeIndex_spec hd x (activeIndex hd y) (Ne.symm hi)
    have hx : ‖disjointMap hd x‖ ≤ K * dist x y := by
      rw [disjointMap, lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞))]
      simpa only [hxy, dist_zero_right] using (hh (activeIndex hd x)).dist_le_mul x y
    have hy : ‖disjointMap hd y‖ ≤ K * dist x y := by
      rw [disjointMap, lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞))]
      have ht := (hh (activeIndex hd y)).dist_le_mul y x
      rw [hyx, dist_zero_right, dist_comm] at ht
      exact ht
    calc
      _ ≤ ‖disjointMap hd x‖ + ‖disjointMap hd y‖ := norm_sub_le _ _
      _ ≤ (2 * K : ℝ≥0) * dist x y := by
        simp only [NNReal.coe_mul, NNReal.coe_ofNat]
        linarith

theorem disjointOperator_point {h : ℕ → M → ℝ} (hd : DisjointTests h)
    {K : ℝ≥0} (hh : ∀ i, LipschitzWith K (h i)) (x : M) :
    disjointOperator hd (FreeSpace.point x) = disjointMap hd x - disjointMap hd 0 := by
  apply FreeSpace.linearize_point _ (lipschitz_sub_const _ (disjointMap_lipschitz hd hh) _)
  simp

theorem disjointOperator_coord {h : ℕ → M → ℝ} (hd : DisjointTests h)
    {K : ℝ≥0} (hh : ∀ i, LipschitzWith K (h i)) (μ : FreeSpace.Space M) (i : ℕ) :
    disjointOperator hd μ i = test (normalized (h i) (hh i)) μ := by
  have eqc : (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 i).comp (disjointOperator hd) =
      test (normalized (h i) (hh i)) := by
    have h₁ := FreeSpace.linearize_unique (fun x => h i x - h i 0)
      (lipschitz_sub_const _ (hh i) _) (by simp)
      ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 i).comp (disjointOperator hd))
      (by intro x; simp only [ContinuousLinearMap.comp_apply, disjointOperator_point hd hh]
          change (disjointMap hd x) i - (disjointMap hd 0) i = _
          rw [disjointMap_apply, disjointMap_apply])
    have h₂ := FreeSpace.linearize_unique (fun x => h i x - h i 0)
      (lipschitz_sub_const _ (hh i) _) (by simp) (test (normalized (h i) (hh i))) (fun x => rfl)
    exact h₁.symm.trans h₂
  exact congrArg (fun T : FreeSpace.Space M →L[ℝ] ℝ => T μ) eqc

end LocalizedLinearization

end LipschitzCounterexample
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalizedLinearization
open Filter Topology
open scoped NNReal ENNReal


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.LocalizedLinearization.disjointOperator_coord.{uM} := @_root_.OAI.LipschitzCounterexample.LocalizedLinearization.disjointOperator_coord.{uM}
