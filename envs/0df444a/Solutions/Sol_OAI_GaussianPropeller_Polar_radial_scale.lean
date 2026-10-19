-- Prove2me | solution 1 for OAI.GaussianPropeller.Polar.radial_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:57:12.799445+00:00
-- url     : https://prove2.me/submissions/15f9c72a-50e3-4aa1-940e-18b5131d792f

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Polar.lean:L135-L151
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Polar.radial_scale. The node keeps its source
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
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_ResidualBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Polar

-- ---- from OAI.Probability.GaussianPropeller.Polar ----
namespace OAI

universe uι

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
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

open Metric
namespace GaussianPropeller.Polar
open Translation

variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "S" => sphere (0 : E) 1
local notation "V" => (volume : Measure E)

end GaussianPropeller.Polar

namespace GaussianPropeller.Polar
open Real
lemma radial_scale (n : ℕ) {b : ℝ} (hb : 0<b) :
    radial n b = (sqrt (2*b))⁻¹ ^ (n+1) * radial n (1/2) := by
  have hp : 0<sqrt (2*b) := by positivity
  have hs := sq_sqrt (show 0≤2*b by positivity)
  have hh := integral_comp_mul_left_Ioi (fun r : ℝ => r^n*exp (-(1/2:ℝ)*r^2)) 0 hp
  rw [mul_zero] at hh
  have heq : (fun r : ℝ => (sqrt (2*b)*r)^n * exp (-(1/2:ℝ)*(sqrt (2*b)*r)^2)) =
      fun r => sqrt (2*b)^n * (r^n*exp (-b*r^2)) := by
    funext r
    rw [mul_pow, show -(1/2:ℝ)*(sqrt (2*b)*r)^2 = -b*r^2 by rw [mul_pow,hs]; ring]
    ring
  change (∫ r in Ioi (0:ℝ), (sqrt (2*b)*r)^n * exp (-(1/2:ℝ)*(sqrt (2*b)*r)^2)) = _ at hh
  rw [heq, integral_const_mul] at hh
  change sqrt (2*b)^n*radial n b = (sqrt (2*b))⁻¹*radial n (1/2) at hh
  apply (mul_left_cancel₀ (pow_ne_zero n hp.ne'))
  rw [hh, pow_succ, mul_assoc, ← mul_assoc (sqrt (2*b)^n)]
  simp only [inv_pow, mul_inv_cancel₀ (pow_ne_zero n hp.ne'), one_mul]

variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "S" => Metric.sphere (0:E) 1

end GaussianPropeller.Polar

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Polar
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
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open Real


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Polar.radial_scale := @_root_.OAI.GaussianPropeller.Polar.radial_scale
