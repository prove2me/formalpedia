-- Prove2me | solution 1 for OAI.GaussianPropeller.Cap.cone_three
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:14:04.739427+00:00
-- url     : https://prove2.me/submissions/933d4e7b-4dd8-47ee-a17b-3ae861f49489

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/CapBounds.lean:L199-L217
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Cap.cone_three. The node keeps its source
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
import Theorems.Thm_OAI_GaussianPropeller_Cap_capP_two
import Theorems.Thm_OAI_GaussianPropeller_Cap_moment_rearrange
import Theorems.Thm_OAI_GaussianPropeller_Polar_integral_norm_pow_exp
import Theorems.Thm_OAI_GaussianPropeller_Polar_radial_scale

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

lemma radial_pos (n : ℕ) {b : ℝ} (hb : 0<b) : 0<radial n b := by
  rw [radial_eq n hb]
  exact mul_pos (mul_pos (rpow_pos_of_pos hb _) (by norm_num))
    (Gamma_pos_of_pos (by positivity))

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
lemma capM_eq (hn : 0<n) (a : ℝ) :
    capM n a = gaussianConst * (Real.sqrt (1+a^2))⁻¹^n := by
  let : NeZero n := ⟨by omega⟩
  have hh := integral_norm_pow_exp (ι:=Fin n) 0 (a:=a^2/2) (by positivity)
  have hs := radial_scale (n-1) (b:=a^2/2+1/2) (by positivity)
  simp only [Fintype.card_fin, add_zero, pow_zero, one_mul] at hh
  unfold capM
  have he : (fun y : CE n => density (a*‖y‖)) = fun y => Real.exp (-(a^2/2)*‖y‖^2) := by
    funext y; unfold density; congr 1; ring
  rw [he,hh,hs,show 2*(a^2/2+1/2)=1+a^2 by ring,
    show n-1+1=n by omega, mul_div_cancel_right₀ _ (radial_pos _ (by norm_num)).ne']

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

lemma cap_parameter {b : ℝ} (hb : 0≤b) (hb1 : b<1) :
    Real.sqrt (1+(b/Real.sqrt (1-b^2))^2) = (Real.sqrt (1-b^2))⁻¹ ∧
    (b/Real.sqrt (1-b^2))/Real.sqrt (1+(b/Real.sqrt (1-b^2))^2)=b := by
  have hpos : 0<1-b^2 := by nlinarith only [hb,hb1]
  have hp : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr hpos
  have hs := Real.sq_sqrt hpos.le
  have he : 1+(b/Real.sqrt (1-b^2))^2 = ((Real.sqrt (1-b^2))⁻¹)^2 := by
    field_simp
    nlinarith only [hs]
  refine ⟨?_,?_⟩
  · rw [he,Real.sqrt_sq (by positivity)]
  · rw [he,Real.sqrt_sq (by positivity)]
    field_simp

lemma cone_three (K : Set (CE 3)) (hK : MeasurableSet K)
    (hcone : ∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K)
    (hP : (stdGaussian (CE 3)).real K ∈ Ioo (0:ℝ) 1)
    (hPh : (stdGaussian (CE 3)).real K ≤ 1/2) :
    (∫ x : CE 3, K.indicator (fun x=>x 0) x ∂stdGaussian (CE 3)) ≤
      4*gaussianConst*(stdGaussian (CE 3)).real K*(1-(stdGaussian (CE 3)).real K) := by
  let P := (stdGaussian (CE 3)).real K
  let b := 1-2*P
  have hb : 0≤b := by dsimp [b,P]; linarith only [hPh]
  have hb1 : b<1 := by dsimp [b,P]; linarith only [hP.1]
  have hh := cap_parameter hb hb1
  have hr := moment_rearrange (n:=2) K hK hcone (a:=b/Real.sqrt (1-b^2)) (by positivity)
  rw [capP_two,hh.2,capM_eq (by omega),hh.1,inv_inv] at hr
  have hs : 0≤1-b^2 := by nlinarith only [hb,hb1]
  rw [Real.sq_sqrt hs] at hr
  have he : (1-b)/2=P := by dsimp [b]; ring
  rw [he,show (stdGaussian (CE (2+1))).real K=P from rfl,sub_self,mul_zero,add_zero] at hr
  dsimp [b,P] at hr
  nlinarith only [hr]

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

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


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Cap.cone_three := @_root_.OAI.GaussianPropeller.Cap.cone_three
