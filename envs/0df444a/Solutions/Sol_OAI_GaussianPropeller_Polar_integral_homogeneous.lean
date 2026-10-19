-- Prove2me | solution 1 for OAI.GaussianPropeller.Polar.integral_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:06:11.038538+00:00
-- url     : https://prove2.me/submissions/164cc93b-5170-4866-82e2-8d8139f8f28e

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Polar.lean:L90-L111
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Polar.integral_homogeneous. The node keeps its source
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
import Theorems.Thm_OAI_GaussianPropeller_Polar_integral_stdGaussian_polar

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

lemma integral_volumeIoiPow (d : ℕ) (g : ℝ → ℝ) :
    (∫ r : Ioi (0:ℝ), g r.1 ∂Measure.volumeIoiPow d) =
      ∫ r in Ioi (0:ℝ), r^d * g r := by
  rw [Measure.volumeIoiPow]
  simp_rw [ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
    (measurable_subtype_coe.pow_const d).real_toNNReal]
  have heq : (fun r : Ioi (0:ℝ) => (r.1^d).toNNReal • g r.1) =
      fun r => r.1^d * g r.1 := by
    funext r
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg r.2.le d), smul_eq_mul]
  rw [heq]
  exact integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r^d * g r)

lemma integral_homogeneous (f : E → ℝ) (q : ℕ)
    (hf : ∀ (r : ℝ), 0 < r → ∀ x, f (r • x) = r^q * f x) :
    ∫ x, f x ∂stdGaussian E =
      ((Real.sqrt (2*Real.pi))⁻¹ ^ Fintype.card ι *
      ∫ r in Ioi (0:ℝ), r^(Fintype.card ι - 1 + q) * Real.exp (-r^2/2)) *
      ∫ θ : S, f θ.1 ∂(V).toSphere := by
  rw [integral_stdGaussian_polar]
  have heq : (fun p : S × Ioi (0:ℝ) => Real.exp (-p.2.1^2/2) * f (p.2.1 • p.1.1)) =
      fun p => f p.1.1 * (p.2.1^q * Real.exp (-p.2.1^2/2)) := by
    funext p
    rw [hf _ p.2.2]
    ring
  rw [heq, integral_prod_mul (fun θ : S => f θ.1)
    (fun r : Ioi (0:ℝ) => r.1^q * Real.exp (-r.1^2/2)), integral_volumeIoiPow (Fintype.card ι - 1)
      (fun r : ℝ => r^q * Real.exp (-r^2/2))]
  have heq' : (fun r : ℝ => r^(Fintype.card ι-1) * (r^q * Real.exp (-r^2/2))) =
      fun r => r^(Fintype.card ι-1+q) * Real.exp (-r^2/2) := by
    funext r
    rw [pow_add]
    ring
  rw [heq']
  ring

end GaussianPropeller.Polar

namespace GaussianPropeller.Polar
open Real
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
open Translation


theorem solution.{uι} : type_of% @_root_.OAI.GaussianPropeller.Polar.integral_homogeneous.{uι} := @_root_.OAI.GaussianPropeller.Polar.integral_homogeneous.{uι}
