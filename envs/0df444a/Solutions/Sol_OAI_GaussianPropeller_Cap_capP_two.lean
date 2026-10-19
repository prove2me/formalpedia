-- Prove2me | solution 1 for OAI.GaussianPropeller.Cap.capP_two
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:06:59.796998+00:00
-- url     : https://prove2.me/submissions/fc962a0e-99dc-4222-9a28-16ab45ccb25d

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/CapIntegral.lean:L125-L139
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Cap.capP_two. The node keeps its source
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
import Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral
import Theorems.Thm_OAI_GaussianPropeller_Cap_hasDerivAt_capP
import Theorems.Thm_OAI_GaussianPropeller_Polar_integral_norm_pow_exp
import Theorems.Thm_OAI_GaussianPropeller_Polar_radial_half_two
import Theorems.Thm_OAI_GaussianPropeller_Polar_radial_scale

-- ---- from OAI.Probability.GaussianPropeller.OneCell ----
namespace OAI

universe uE

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

namespace GaussianPropeller.OneCell

lemma tail_zero : gaussianConst*tail 0 = 1/2 := by
  have h : tail 0 = Real.sqrt (2*Real.pi)/2 := by
    simpa only [tail, density, show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring,
      show Real.pi/(1/2:ℝ) = 2*Real.pi by ring] using integral_gaussian_Ioi (1/2)
  rw [h, gaussianConst]
  field_simp

section GeneralCell
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GeneralCell
end GaussianPropeller.OneCell

end OAI

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

lemma radial_half_one : radial 1 (1/2) = 1 := by
  rw [radial_eq 1 (by norm_num)]
  norm_num

variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "S" => Metric.sphere (0:E) 1

end GaussianPropeller.Polar

end OAI

-- ---- from OAI.Probability.GaussianPropeller.CapIntegral ----
namespace OAI

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

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

variable {n : ℕ}
lemma capP_zero (n : ℕ) : capP n 0 = 1/2 := by
  simp [capP,p,tail_zero]

lemma capP_deriv_two (a : ℝ) : HasDerivAt (capP 2)
    (-(1/2:ℝ)*(Real.sqrt (1+a^2))⁻¹^3) a := by
  have hh := integral_norm_pow_exp (ι:=Fin 2) 1 (a:=a^2/2) (by positivity)
  have hs := radial_scale 2 (b:=a^2/2+1/2) (by positivity)
  norm_num only [Fintype.card_fin, Nat.reduceSub, Nat.reduceAdd, pow_one, radial_half_one] at hh
  have hd := hasDerivAt_capP (n:=2) a
  have he : (fun y : CE 2 => ‖y‖*density (a*‖y‖)) = fun y => ‖y‖*Real.exp (-(a^2/2)*‖y‖^2) := by
    funext y; unfold density; congr 2; ring
  rw [he,hh,div_one,hs,show 2*(a^2/2+1/2)=1+a^2 by ring,radial_half_two] at hd
  convert hd using 1
  dsimp [gaussianConst]
  field_simp

lemma capP_two (a : ℝ) : capP 2 a = (1-a/Real.sqrt (1+a^2))/2 := by
  have hp (x : ℝ) : 0 < 1+x^2 := by positivity
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => (1-x/Real.sqrt (1+x^2))/2)
      (-(1/2:ℝ)*(Real.sqrt (1+x^2))⁻¹^3) x := by
    convert ((hasDerivAt_const x 1).sub ((hasDerivAt_id x).div
      (((hasDerivAt_pow 2 x).const_add 1).sqrt (hp x).ne') (Real.sqrt_pos.mpr (hp x)).ne')).div_const 2 using 1 <;> first | rfl | (dsimp; field_simp; nlinarith only [Real.sq_sqrt (hp x).le])
  have he := is_const_of_deriv_eq_zero (fun x => ((hasDerivAt_capP (n:=2) x).sub (hd x)).differentiableAt)
  have he' : ∀ x, deriv (fun x => capP 2 x-(1-x/Real.sqrt (1+x^2))/2) x=0 := by
    intro x
    have hx := ((capP_deriv_two x).fun_sub (hd x)).deriv
    rw [sub_self] at hx
    exact hx
  have hg := he he' a 0
  simp only [Pi.sub_apply, capP_zero,zero_div,sub_zero,one_div] at hg
  linarith

end GaussianPropeller.Cap

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Cap
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
open OneCell ProbabilityBounds Polar
open scoped Topology


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Cap.capP_two := @_root_.OAI.GaussianPropeller.Cap.capP_two
