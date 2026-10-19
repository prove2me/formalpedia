-- Prove2me | solution 1 for OAI.GaussianPropeller.Polar.integral_norm_pow_exp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:03:09.278372+00:00
-- url     : https://prove2.me/submissions/2a44940f-1f70-4e9d-87f0-57a745a3472e

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Polar.lean:L226-L239
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Polar.integral_norm_pow_exp. The node keeps its source
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

lemma integral_radial (f : ℝ → ℝ) :
    ∫ x : E, f ‖x‖ ∂stdGaussian E =
      ((sqrt (2*Real.pi))⁻¹ ^ Fintype.card ι * ∫ _ : S, (1:ℝ) ∂(volume : Measure E).toSphere) *
      ∫ r in Ioi (0:ℝ), r^(Fintype.card ι-1)*exp (-r^2/2)*f r := by
  rw [integral_stdGaussian_polar]
  have heq : (fun p : S × Ioi (0:ℝ) => exp (-p.2.1^2/2)*f ‖p.2.1•p.1.1‖) =
      fun p => (1:ℝ)*(exp (-p.2.1^2/2)*f p.2.1) := by
    funext p
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos (show 0<p.2.1 from p.2.2),
      mem_sphere_zero_iff_norm.mp p.1.2]
  rw [heq, integral_prod_mul (fun θ : S => (1:ℝ))
    (fun r : Ioi (0:ℝ) => exp (-r.1^2/2)*f r.1), integral_volumeIoiPow (Fintype.card ι-1) (fun r => exp (-r^2/2)*f r)]
  simp_rw [mul_assoc]

lemma integral_radial_normalized (f : ℝ → ℝ) :
    ∫ x : E, f ‖x‖ ∂stdGaussian E =
      (∫ r in Ioi (0:ℝ), r^(Fintype.card ι-1)*exp (-r^2/2)*f r) /
      radial (Fintype.card ι-1) (1/2) := by
  have h1 := integral_radial (ι:=ι) (fun _ => (1:ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
  have hi : (∫ r in Ioi (0:ℝ), r^(Fintype.card ι-1)*exp (-r^2/2)) = radial (Fintype.card ι-1) (1/2) := by
    unfold radial
    congr 1; funext r; congr 2; ring
  rw [hi] at h1
  rw [integral_radial]
  rw [← one_div_mul_eq_div]
  congr 1
  apply (eq_div_iff (radial_pos _ (by norm_num)).ne').mpr
  simpa using h1.symm

lemma integral_norm_pow_exp (q : ℕ) {a : ℝ} (_ha : 0≤a) :
    ∫ x : E, ‖x‖^q*exp (-a*‖x‖^2) ∂stdGaussian E =
      radial (Fintype.card ι-1+q) (a+1/2)/radial (Fintype.card ι-1) (1/2) := by
  rw [integral_radial_normalized (fun r => r^q*exp (-a*r^2))]
  congr 1
  unfold radial
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [pow_add]
  rw [show r^(Fintype.card ι-1)*exp (-r^2/2)*(r^q*exp (-a*r^2)) =
    r^(Fintype.card ι-1)*r^q*(exp (-r^2/2)*exp (-a*r^2)) by ring, ← exp_add]
  congr 2
  ring

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


theorem solution.{uι} : type_of% @_root_.OAI.GaussianPropeller.Polar.integral_norm_pow_exp.{uι} := @_root_.OAI.GaussianPropeller.Polar.integral_norm_pow_exp.{uι}
