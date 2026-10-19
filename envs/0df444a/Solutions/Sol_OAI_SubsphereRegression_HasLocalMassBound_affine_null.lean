-- Prove2me | solution 1 for OAI.SubsphereRegression.HasLocalMassBound.affine_null
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:33:43.565521+00:00
-- url     : https://prove2.me/submissions/71caed06-a13d-491a-baec-037f597fff82

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Geometry.lean:L367-L392
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.HasLocalMassBound.affine_null. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Theorems.Thm_OAI_SubsphereRegression_HasLocalMassBound_affine_tube

-- ---- from OAI.Probability.Subsphere.Regression.Geometry ----
namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereRegression
open scoped Topology
section InverseMoments

variable {X : Type*} [MeasurableSpace X]

end InverseMoments

section FrostmanGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end FrostmanGeometry

section FiniteNets

variable {E : Type*} [PseudoMetricSpace E]

end FiniteNets

section EuclideanNets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end EuclideanNets

section AffineTubes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open EuclideanGeometry

/-- Collecting the radius factors in the packing estimate. -/
lemma tube_radius_factors (ℓ : ℕ) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    (3 / r) ^ ℓ * (4 * r) ^ a =
      (3 : ℝ) ^ ℓ * (4 : ℝ) ^ a * r ^ (a - ℓ) := by
  rw [div_pow, Real.mul_rpow (by norm_num) hr.le,
    Real.rpow_sub_natCast hr.ne']
  ring

/-- An explicit positive margin reduces the tube estimate to an integer power. -/
theorem HasLocalMassBound.affine_tube_pow {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L] (k : ℕ)
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + k ≤ a)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ν {t | Metric.infDist t L ≤ r} ≤
      ENNReal.ofReal ((3 : ℝ) ^ Module.finrank ℝ L.direction * (4 : ℝ) ^ a) *
        ENNReal.ofReal (r ^ k) := by
  refine (hν.affine_tube hsupport L hr hr1).trans ?_
  rw [tube_radius_factors _ _ hr, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)

/-- Positive tube margin forces the affine plane itself to be null. -/
theorem HasLocalMassBound.affine_null {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L]
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + 1 ≤ a) : ν L = 0 := by
  let C : ℝ := (3 : ℝ) ^ Module.finrank ℝ L.direction * (4 : ℝ) ^ a
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb (n : ℕ) : ν L ≤ ENNReal.ofReal (C * (1 / 2 : ℝ) ^ n) := by
    have hn : 0 < (1 / 2 : ℝ) ^ n := by positivity
    have hn1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc
      ν L ≤ ν {t | Metric.infDist t L ≤ (1 / 2 : ℝ) ^ n} := by
        apply measure_mono
        intro t ht
        simp only [mem_ofPred_eq, Metric.infDist_zero_of_mem ht]
        exact hn.le
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ 1) :=
        hν.affine_tube_pow hsupport L 1 (by simpa using hmargin) hn hn1
      _ = _ := by rw [pow_one, ENNReal.ofReal_mul hC]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (C * (1 / 2 : ℝ) ^ n))
      atTop (𝓝 0) := by
    convert ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := C)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))) using 1
    simp
  exact le_antisymm (ge_of_tendsto' hlim hb) (by positivity)

end AffineTubes

open InnerProductSpace

end SubsphereRegression
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open scoped Topology
open EuclideanGeometry


theorem solution : type_of% @_root_.OAI.SubsphereRegression.HasLocalMassBound.affine_null := @_root_.OAI.SubsphereRegression.HasLocalMassBound.affine_null
