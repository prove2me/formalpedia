-- Prove2me | solution 1 for OAI.LipschitzCounterexample.LocalizedLinearization.disjointOperator_coord
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T19:45:58.149927+00:00
-- url     : https://prove2.me/submissions/94b7a760-8ca2-4959-8e3c-97795a98ca87

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalizedLinearization
universe uM uV
open Filter Topology
open scoped NNReal ENNReal
variable {M : Type uM} [MetricSpace M] [Zero M]
theorem h50_spec {h : ℕ → M → ℝ} (hd : DisjointTests h) (x : M) :
    ∀ j, j ≠ activeIndex hd x → h j x = 0 := (hd.exists_index x).choose_spec

theorem h50_dm_apply {h : ℕ → M → ℝ} (hd : DisjointTests h) (x : M) (i : ℕ) :
    disjointMap hd x i = h i x := by
  unfold disjointMap
  rw [lp.single_apply]
  by_cases hi : i = activeIndex hd x
  · rw [hi, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hi, h50_spec hd x i hi]

theorem h50_dm_lip {h : ℕ → M → ℝ} (hd : DisjointTests h) {K : ℝ≥0}
    (hh : ∀ i, LipschitzWith K (h i)) : LipschitzWith (2 * K) (disjointMap hd) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have ex : disjointMap hd x = lp.single 1 (activeIndex hd x) (h (activeIndex hd x) x) := rfl
  have ey : disjointMap hd y = lp.single 1 (activeIndex hd y) (h (activeIndex hd y) y) := rfl
  have sx0 := h50_spec hd x
  have sy0 := h50_spec hd y
  generalize activeIndex hd x = i at ex sx0
  generalize activeIndex hd y = j at ey sy0
  rw [ex, ey]
  have hdecomp : lp.single 1 i (h i x) - lp.single (E := fun _ : ℕ => ℝ) 1 j (h j y) =
      lp.single 1 i (h i x - h i y) + (lp.single 1 i (h i y) - lp.single (E := fun _ : ℕ => ℝ) 1 j (h j y)) := by
    rw [lp.single_sub]; abel
  rw [hdecomp]
  have hp : (0:ℝ≥0∞) < 1 := by norm_num
  have t1 : ‖lp.single (E := fun _ : ℕ => ℝ) 1 i (h i x - h i y)‖ ≤ K * dist x y := by
    rw [lp.norm_single hp, ← dist_eq_norm]; exact (hh i).dist_le_mul x y
  have t2 : ‖lp.single (E := fun _ : ℕ => ℝ) 1 i (h i y) - lp.single (E := fun _ : ℕ => ℝ) 1 j (h j y)‖ ≤ K * dist x y := by
    by_cases hij : i = j
    · subst hij; rw [sub_self, norm_zero]; positivity
    · rw [sy0 i hij, lp.single_zero, zero_sub, norm_neg, lp.norm_single hp]
      have e : h j y = h j y - h j x := by rw [sx0 j (Ne.symm hij), sub_zero]
      rw [e, ← dist_eq_norm, dist_comm x y]
      exact (hh j).dist_le_mul y x
  have t3 := norm_add_le (lp.single (E := fun _ : ℕ => ℝ) 1 i (h i x - h i y))
    (lp.single (E := fun _ : ℕ => ℝ) 1 i (h i y) - lp.single (E := fun _ : ℕ => ℝ) 1 j (h j y))
  push_cast
  linarith

theorem solution {h : ℕ → M → ℝ} (hd : DisjointTests h)
    {K : ℝ≥0} (hh : ∀ i, LipschitzWith K (h i)) (μ : FreeSpace.Space M) (i : ℕ) :
    disjointOperator hd μ i = test (normalized (h i) (hh i)) μ := by
  have hD : LipschitzWith (2*K) (fun x => disjointMap hd x - disjointMap hd 0) :=
    lipschitz_sub_const _ (h50_dm_lip hd hh) _
  have h0 : (fun x => disjointMap hd x - disjointMap hd 0) 0 = 0 := sub_self _
  have key : (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 i).comp (disjointOperator hd) =
      test (normalized (h i) (hh i)) := by
    have hdn := FreeSpace.dense_combinations (M := M)
    apply DFunLike.coe_injective
    refine hdn.equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
      (funext fun a => ?_)
    simp only [Function.comp_apply]
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single x r =>
      simp only [Finsupp.linearCombination_single, map_smul]
      congr 1
      change (disjointOperator hd (FreeSpace.point x)) i =
        test (normalized (h i) (hh i)) (FreeSpace.point x)
      rw [disjointOperator, FreeSpace.linearize_point _ hD h0, test_point]
      change (disjointMap hd x - disjointMap hd 0) i = h i x - h i 0
      rw [lp.coeFn_sub, Pi.sub_apply, h50_dm_apply, h50_dm_apply]
  exact congrArg (fun T => T μ) key

