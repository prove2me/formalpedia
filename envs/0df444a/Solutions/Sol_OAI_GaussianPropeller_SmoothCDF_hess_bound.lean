-- Prove2me | solution 1 for OAI.GaussianPropeller.SmoothCDF.hess_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:05:57.281186+00:00
-- url     : https://prove2.me/submissions/8ddfbabf-eb98-4e33-9f77-d937dafeaaa5

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/QuantileCalculus.lean:L117-L133
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.SmoothCDF.hess_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus

-- ---- from OAI.Probability.GaussianPropeller.Quantile ----
namespace OAI

universe uX

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace GaussianPropeller.Quantile

lemma φ_le_zero (x : ℝ) : φ x ≤ φ 0 := by
  unfold φ
  simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
  exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))

section Integration
variable {X : Type uX} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

end Integration
end GaussianPropeller.Quantile

end OAI

-- ---- from OAI.Probability.GaussianPropeller.QuantileCalculus ----
namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

open scoped RealInnerProductSpace
namespace GaussianPropeller.QuantilePDE
open GaussianPropeller.Quantile

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end GaussianPropeller.QuantilePDE

namespace GaussianPropeller.SmoothCDF
open GaussianPropeller.Quantile
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma abs_mul_φ_le (a : ℝ) : |a| *φ a ≤ φ 0 := by
  have hsq : |a| ≤ 1+a^2/2 := by nlinarith [sq_nonneg (|a|-1), sq_abs a]
  have he : |a| ≤ Real.exp (a^2/2) := hsq.trans (by nlinarith [Real.add_one_le_exp (a^2/2)])
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (-a^2/2)).le
  rw [← Real.exp_add] at hh
  have heq : a^2/2 + -a^2/2 = 0 := by ring
  rw [heq, Real.exp_zero] at hh
  unfold φ
  simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
  nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (Real.sqrt (2*Real.pi))⁻¹)]

lemma hess_bound {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E} {L D : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ x, ‖g x‖ ≤ L) (hD : ∀ x, ‖K x‖ ≤ D) (x : E) :
    ‖hess f g K x‖ ≤ φ 0*(D+L^2) := by
  have hD0 : 0 ≤ D := (norm_nonneg (K x)).trans (hD x)
  calc
    ‖hess f g K x‖ ≤ ‖φ (f x) • K x‖ +
        ‖(f x*φ (f x)) • ((innerSL ℝ (g x)).smulRight (g x))‖ := norm_sub_le _ _
    _ = φ (f x)*‖K x‖ + (|f x| *φ (f x))*‖g x‖^2 := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (φ_pos _), abs_mul, abs_of_pos (φ_pos _),
        ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
      ring
    _ ≤ φ 0*D + φ 0*L^2 := add_le_add
      (mul_le_mul (φ_le_zero _) (hD x) (norm_nonneg _) (φ_pos _).le)
      (mul_le_mul (abs_mul_φ_le _) ((sq_le_sq₀ (norm_nonneg _) hL0).2 (hL x))
        (sq_nonneg _) (φ_pos _).le)
    _ = _ := by ring

end GaussianPropeller.SmoothCDF

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.SmoothCDF
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open GaussianPropeller.Quantile


theorem solution.{uE} : type_of% @_root_.OAI.GaussianPropeller.SmoothCDF.hess_bound.{uE} := @_root_.OAI.GaussianPropeller.SmoothCDF.hess_bound.{uE}
