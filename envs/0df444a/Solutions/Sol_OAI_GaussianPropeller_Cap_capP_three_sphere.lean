-- Prove2me | solution 1 for OAI.GaussianPropeller.Cap.capP_three_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:15:55.36437+00:00
-- url     : https://prove2.me/submissions/ca662910-9fbf-49ab-ae9b-a9d28f7134a6

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/CapBounds.lean:L269-L286
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Cap.capP_three_sphere. The node keeps its source
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
import Definitions.Def_OAI_Probability_GaussianPropeller_Coordinates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapBounds
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

lemma radial_half_three : radial 3 (1/2) = 2 := by
  rw [radial_eq 3 (by norm_num)]
  norm_num [Gamma_nat_eq_factorial, rpow_neg, rpow_natCast]

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

end GaussianPropeller.Cap

end OAI

-- ---- from OAI.Probability.GaussianPropeller.CapBounds ----
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
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Cap
open Coords OneCell ProbabilityBounds Polar
open scoped Topology
variable {n : ℕ}

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

lemma capP_deriv_three (a : ℝ) : HasDerivAt (capP 3)
    (-(2/Real.pi:ℝ)*(Real.sqrt (1+a^2))⁻¹^4) a := by
  have hh := integral_norm_pow_exp (ι:=Fin 3) 1 (a:=a^2/2) (by positivity)
  have hs := radial_scale 3 (b:=a^2/2+1/2) (by positivity)
  norm_num only [Fintype.card_fin, Nat.reduceSub, Nat.reduceAdd, pow_one] at hh
  have hd := hasDerivAt_capP (n:=3) a
  have he : (fun y : CE 3 => ‖y‖*density (a*‖y‖)) = fun y => ‖y‖*Real.exp (-(a^2/2)*‖y‖^2) := by
    funext y; unfold density; congr 2; ring
  rw [he,hh,hs,show 2*(a^2/2+1/2)=1+a^2 by ring,radial_half_three,radial_half_two] at hd
  convert hd using 1
  have hp : 0<Real.sqrt (2*Real.pi) := by positivity
  have hsq := Real.sq_sqrt (show 0≤2*Real.pi by positivity)
  dsimp [gaussianConst]
  field_simp
  nlinarith only [hsq]

lemma sphereTail_zero : sphereTail 0 = Real.pi/4 := by
  have hi : IntervalIntegrable (fun u:ℝ=>Real.sqrt (1-u^2)) volume (-1) 0 := by
    exact (by fun_prop : Continuous (fun u:ℝ=>Real.sqrt (1-u^2))).intervalIntegrable _ _
  have hj : IntervalIntegrable (fun u:ℝ=>Real.sqrt (1-u^2)) volume 0 1 := by
    exact (by fun_prop : Continuous (fun u:ℝ=>Real.sqrt (1-u^2))).intervalIntegrable _ _
  have he := intervalIntegral.integral_add_adjacent_intervals hi hj
  have hn := intervalIntegral.integral_comp_neg (f:=fun u:ℝ=>Real.sqrt (1-u^2)) (a:=(0:ℝ)) (b:=1)
  simp only [neg_zero,neg_sq] at hn
  rw [integral_sqrt_one_sub_sq] at he
  dsimp [sphereTail]
  linarith only [he,hn]

lemma hasDerivAt_sphereTail (b:ℝ) : HasDerivAt sphereTail (-Real.sqrt (1-b^2)) b := by
  apply intervalIntegral.integral_hasDerivAt_left
  · exact (by fun_prop : Continuous (fun u:ℝ=>Real.sqrt (1-u^2))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun u:ℝ=>Real.sqrt (1-u^2))).stronglyMeasurable.stronglyMeasurableAtFilter
  · fun_prop

lemma cap_parameter' {b:ℝ} (hb:b^2<1) :
    Real.sqrt (1+(b/Real.sqrt (1-b^2))^2) = (Real.sqrt (1-b^2))⁻¹ := by
  have hp : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr (by linarith only [hb])
  have hs := Real.sq_sqrt (show 0≤1-b^2 by linarith only [hb])
  have he : 1+(b/Real.sqrt (1-b^2))^2 = ((Real.sqrt (1-b^2))⁻¹)^2 := by
    field_simp; nlinarith only [hs]
  rw [he,Real.sqrt_sq (by positivity)]

lemma capP_three_sphere {b:ℝ} (hb:b∈Ioo (-1:ℝ) 1) :
    capP 3 (b/Real.sqrt (1-b^2)) = 2/Real.pi*sphereTail b := by
  have hd (x:ℝ) (hx:x∈Ioo (-1:ℝ) 1) :
      HasDerivAt (fun x=>capP 3 (x/Real.sqrt (1-x^2)))
        (-(2/Real.pi)*Real.sqrt (1-x^2)) x := by
    have hxs : x^2<1 := by nlinarith only [hx.1,hx.2]
    have hp : 0<Real.sqrt (1-x^2) := Real.sqrt_pos.mpr (by linarith only [hxs])
    have hs' := Real.sq_sqrt (show 0≤1-x^2 by linarith only [hxs])
    have hh := (capP_deriv_three (x/Real.sqrt (1-x^2))).comp x
      ((hasDerivAt_id x).div (((hasDerivAt_id x).pow 2).const_sub 1 |>.sqrt (by change 1-x^2≠0; linarith only [hxs])) hp.ne')
    rw [cap_parameter' hxs,inv_inv] at hh
    convert hh using 1 <;> first | rfl | (dsimp; field_simp; ring_nf; try simp only [hs']; ring)
  have he := isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (-1:ℝ) 1).isPreconnected
    (fun x hx=>(hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx=>((hasDerivAt_sphereTail x).const_mul (2/Real.pi)).differentiableAt.differentiableWithinAt)
    (fun x hx=>by rw [(hd x hx).deriv,((hasDerivAt_sphereTail x).const_mul (2/Real.pi)).deriv]; ring)
    (x:=0) (by norm_num) (by rw [zero_div,capP_zero,sphereTail_zero]; field_simp; ring)
  exact he hb

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
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open OneCell ProbabilityBounds Polar
open scoped Topology


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Cap.capP_three_sphere := @_root_.OAI.GaussianPropeller.Cap.capP_three_sphere
