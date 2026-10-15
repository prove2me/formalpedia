-- Prove2me | solution 2 for OAI.PiExponent.LiteralAnalytic.actualRowCount_eventually_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-14T21:09:58.709697+00:00
-- url     : https://prove2.me/submissions/7622c052-800d-4f66-b2f2-ff61180ad26c

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actualRowCount_pos

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.LiteralAnalytic

-- The simplex is contained in its defining coordinate box. Each side of that
-- box has at most (1 / w i + 1) * H entries once H ≥ 1.
theorem solution
    {nu : ℝ} (d : FixedData nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop,
      0 < H ∧ 1 ≤ actualRowCount d H ∧
        (actualRowCount d H : ℝ) ≤ C * H ^ (d.m + 1 : ℕ) := by
  classical
  let w : Fin (d.m + 1) → ℝ :=
    InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d))
  have hw : ∀ i, 0 < w i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact d.v0_pos
    · change 0 < MatrixArithmetic.logWeights (finiteDenominators d) j / (d.base.theta : ℝ)
      apply div_pos ?_ d.base.theta_pos
      have hx := d.x_one_le (j.val + 1)
      rw [d.x_log] at hx
      exact lt_of_lt_of_le zero_lt_one hx
  have hK : (0 : ℝ) < d.K := by
    exact_mod_cast (show 0 < d.K from d.K_pos)
  refine ⟨(d.K : ℝ) * ∏ i, (1 / w i + 1), ?_, ?_⟩
  · exact mul_pos hK (Finset.prod_pos fun i _ => add_pos (one_div_pos.mpr (hw i)) zero_lt_one)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  refine ⟨hHpos, actualRowCount_pos d hHpos, ?_⟩
  have hcard : actualRowCount d H ≤ d.K * ∏ i, (⌊H / w i⌋₊ + 1) := by
    change Fintype.card (Fin d.K × ↥(strictWeightedSimplex w H)) ≤ _
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
    apply Nat.mul_le_mul_left
    calc
      (strictWeightedSimplex w H).card ≤ (realWeightedSimplex w H).card :=
        Finset.card_filter_le _ _
      _ ≤ (Fintype.piFinset (fun i => Finset.range (⌊H / w i⌋₊ + 1))).card :=
        Finset.card_filter_le _ _
      _ = ∏ i, (⌊H / w i⌋₊ + 1) := by simp
  have hside : ∀ i, ((⌊H / w i⌋₊ + 1 : ℕ) : ℝ) ≤ (1 / w i + 1) * H := by
    intro i
    push_cast
    calc
      (⌊H / w i⌋₊ : ℝ) + 1 ≤ H / w i + H :=
        add_le_add (Nat.floor_le (div_nonneg hHpos.le (hw i).le)) hH
      _ = (1 / w i + 1) * H := by ring
  have hprod : ((∏ i, (⌊H / w i⌋₊ + 1) : ℕ) : ℝ) ≤
      (∏ i, (1 / w i + 1)) * H ^ (d.m + 1) := by
    rw [Nat.cast_prod]
    calc
      (∏ i, ((⌊H / w i⌋₊ + 1 : ℕ) : ℝ)) ≤ ∏ i, ((1 / w i + 1) * H) :=
        Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hside i)
      _ = (∏ i, (1 / w i + 1)) * H ^ (d.m + 1) := by
        rw [Finset.prod_mul_distrib]
        simp
  calc
    (actualRowCount d H : ℝ) ≤ (d.K : ℝ) * ((∏ i, (⌊H / w i⌋₊ + 1) : ℕ) : ℝ) := by
      exact_mod_cast hcard
    _ ≤ (d.K : ℝ) * ((∏ i, (1 / w i + 1)) * H ^ (d.m + 1)) :=
      mul_le_mul_of_nonneg_left hprod hK.le
    _ = ((d.K : ℝ) * ∏ i, (1 / w i + 1)) * H ^ (d.m + 1) := by ring
