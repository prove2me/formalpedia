-- Prove2me | solution 1 for OAI.SubsphereRegression.withDensity_apply_le_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:46:52.642263+00:00
-- url     : https://prove2.me/submissions/2e1cbb49-3178-4ed6-8dcd-9938b39fc91a

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Gaussian.lean:L374-L388
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.withDensity_apply_le_moment. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian

-- ---- from OAI.Probability.Subsphere.Regression.Gaussian ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
section GaussianDomination
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianDomination

section ReplicaKernel
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

end ReplicaKernel

section GaussianKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianKernel

section SmoothingMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SmoothingMoments

section ProductDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

end ProductDensity

section GaussianNoise
end GaussianNoise

section HolderSet
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
lemma withDensity_apply_le_moment (f : X → ℝ≥0∞) (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (hC : ∫⁻ x, f x ^ p ∂μ ≤ C) (S : Set X) (hS : MeasurableSet S) :
    μ.withDensity f S ≤ C^(1/p) * (μ S)^(1 - 1/p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict S) hpq
    hf.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have he : 1 / (Real.conjExponent p) = 1 - 1/p := by
    have hh := hpq.inv_add_inv_eq_one
    simpa only [one_div] using (eq_sub_of_add_eq' hh)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul, he] at h
  rw [withDensity_apply _ hS]
  exact h.trans (mul_le_mul' (ENNReal.rpow_le_rpow
    ((lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans hC) (by positivity)) le_rfl)
end HolderSet

section LimitSet
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Y] [BorelSpace Y]
  (ρ : Measure X) (τ : Measure Y)

end LimitSet

variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]

end SubsphereRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open scoped Topology
open InnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereRegression.withDensity_apply_le_moment := @_root_.OAI.SubsphereRegression.withDensity_apply_le_moment
