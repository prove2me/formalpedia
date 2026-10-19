-- Prove2me | solution 1 for OAI.NoiselessRegression.replicaConstant_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:00:24.208662+00:00
-- url     : https://prove2.me/submissions/27bbf4e1-d811-49d1-ae1c-ab594c269d7a

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Blocks.lean:L89-L112
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.replicaConstant_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments

-- ---- from OAI.Probability.GaussianRegression.Blocks ----
namespace OAI

/-!
Localization, finite selection, and block mass propagation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section Block
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma replicaConstant_le {ν : Measure E} (hν : ν univ ≤ 1) {a m : ℕ}
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E) (hm : m ≤ Module.finrank ℝ E) :
    replicaConstant ν (a : ℝ) m ≤ (128 : ℝ≥0∞) ^ Module.finrank ℝ E := by
  let d := Module.finrank ℝ E
  have h2 : (2 : ℝ≥0∞) ≤ 2^d := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) hd
  have hp : (2 : ℝ≥0∞)^(m+1) ≤ 4^d := by
    rw [pow_succ]
    calc
      _ ≤ (2 : ℝ≥0∞)^d * 2^d := mul_le_mul' (pow_le_pow_right₀ (by norm_num) hm) h2
      _ = _ := by rw [← mul_pow]; norm_num
  calc
    replicaConstant ν (a : ℝ) m ≤ 1 + (4 : ℝ≥0∞)^d * 4^d * 4^d := by
      unfold replicaConstant
      rw [Real.rpow_natCast, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_pow (by norm_num)]
      norm_num only [ENNReal.ofReal_ofNat]
      gcongr <;> norm_num
    _ = 1 + (64 : ℝ≥0∞)^d := by rw [mul_assoc, ← mul_pow, ← mul_pow]; norm_num
    _ ≤ (2 : ℝ≥0∞) * 64^d := by
      rw [two_mul]
      exact add_le_add (one_le_pow₀ (by norm_num)) le_rfl
    _ ≤ (2 : ℝ≥0∞)^d * 64^d := mul_le_mul' h2 le_rfl
    _ = _ := by rw [← mul_pow]; norm_num; rfl

end Block

end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise


theorem solution : type_of% @_root_.OAI.NoiselessRegression.replicaConstant_le := @_root_.OAI.NoiselessRegression.replicaConstant_le
