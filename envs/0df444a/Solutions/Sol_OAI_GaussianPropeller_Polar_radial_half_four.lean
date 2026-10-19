-- Prove2me | solution 1 for OAI.GaussianPropeller.Polar.radial_half_four
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:00:12.544986+00:00
-- url     : https://prove2.me/submissions/5a38bb05-eb5f-42fb-86c8-f1f8ff2818ac

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Polar.lean:L179-L190
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Polar.radial_half_four. The node keeps its source
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
import Theorems.Thm_OAI_GaussianPropeller_Polar_radial_half_two

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
lemma radial_eq (n : ℕ) {b : ℝ} (hb : 0<b) :
    radial n b = b ^ (-((n:ℝ)+1)/2) * (1/2) * Gamma (((n:ℝ)+1)/2) := by
  have hh := integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=n) (b:=b)
    (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) n]) hb
  simpa only [Real.rpow_natCast, Real.rpow_two, neg_mul, radial] using hh

lemma radial_half_four : radial 4 (1/2) = 3*sqrt (2*Real.pi)/2 := by
  have h2 := radial_half_two
  rw [radial_eq 2 (by norm_num)] at h2
  rw [radial_eq 4 (by norm_num)]
  have hg := Gamma_add_one (s:=(3/2:ℝ)) (by norm_num)
  norm_num at hg h2 ⊢
  rw [hg]
  have he : (1/2:ℝ)^(-((5:ℝ)/2)) = 2*(1/2:ℝ)^(-((3:ℝ)/2)) := by
    rw [show (-((5:ℝ)/2))=-(1:ℝ)+(-((3:ℝ)/2)) by ring, rpow_add (by norm_num : (0:ℝ)<1/2)]
    norm_num
  rw [he]
  nlinarith only [h2]

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


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Polar.radial_half_four := @_root_.OAI.GaussianPropeller.Polar.radial_half_four
