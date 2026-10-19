-- Prove2me | solution 1 for OAI.SubsphereRegression.projectionLaw_set_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:51:05.538185+00:00
-- url     : https://prove2.me/submissions/201ae4b0-3f73-4f44-8dbf-43364ed50b92

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Projection.lean:L95-L131
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.projectionLaw_set_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Theorems.Thm_OAI_SubsphereRegression_gaussianCoupling_map_noisyObservation
import Theorems.Thm_OAI_SubsphereRegression_map_apply_open_le_of_tendsto
import Theorems.Thm_OAI_SubsphereRegression_projectionSmoothing_moment
import Theorems.Thm_OAI_SubsphereRegression_withDensity_apply_le_moment

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

lemma measurable_projectionSmoothing (ν : Measure E) [SFinite ν]
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (m : ℕ) :
    Measurable (projectionSmoothing ν φ m) := by
  apply Measurable.lintegral_prod_right
  fun_prop

end SmoothingMoments

section ProductDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

end ProductDensity

section GaussianNoise
end GaussianNoise

section HolderSet
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
end HolderSet

section LimitSet
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Y] [BorelSpace Y]
  (ρ : Measure X) (τ : Measure Y)

end LimitSet

variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]

lemma ennreal_rpow_iInf {ι : Sort*} (f : ι → ℝ≥0∞) {α : ℝ} (hα : 0 < α) :
    (⨅ i, f i)^α = ⨅ i, (f i)^α :=
  (ENNReal.orderIsoRpow α hα).map_iInf f

lemma measure_apply_le_of_isOpen (μ τ : Measure Y) [τ.OuterRegular]
    {C : ℝ≥0∞} (hC : C ≠ ∞) {α : ℝ} (hα : 0 < α)
    (hbound : ∀ U, IsOpen U → μ U ≤ C * (τ U)^α) (S : Set Y) :
    μ S ≤ C * (τ S)^α := by
  by_cases hC0 : C = 0
  · simp only [hC0, zero_mul] at hbound ⊢
    exact (measure_mono (Set.subset_univ S)).trans (hbound Set.univ isOpen_univ)
  rw [S.measure_eq_iInf_isOpen τ]
  simp_rw [ennreal_rpow_iInf _ hα, ENNReal.mul_iInf_of_ne hC0 hC]
  exact le_iInf fun U => le_iInf fun hSU => le_iInf fun hU =>
    (measure_mono hSU).trans (hbound U hU)

end SubsphereRegression

end

end OAI

-- ---- from OAI.Probability.Subsphere.Regression.Projection ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
section ProjectionCoupling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_noisyObservation (m : ℕ) (δ : ℝ) :
    Measurable (noisyObservation (E := E) m δ) := by
  unfold noisyObservation
  fun_prop

lemma gaussianCoupling_map_noisyObservation_zero (ν : Measure E) [SigmaFinite ν] (m : ℕ) :
    (gaussianCoupling ν m).map (noisyObservation m 0) = projectionLaw ν m := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_noisyObservation m 0),
    projectionLaw, lintegral_map hf (by fun_prop)]
  dsimp [gaussianCoupling, noisyObservation]
  simp only [zero_mul, add_zero]
  rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro A
  rw [lintegral_prod _ (by fun_prop)]
  simp

lemma matrixLabelReference_outerRegular (m : ℕ) :
    (matrixLabelReference (E := E) m).OuterRegular := by
  unfold matrixLabelReference
  exact (Measure.WeaklyRegular.of_pseudoMetrizableSpace_secondCountable_of_locallyFinite
    ((Measure.pi (fun _ : Fin m => stdGaussian E)).prod volume)).toOuterRegular

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tendsto_noisyObservation (m : ℕ)
    (z : (Fin m → E) × (E × (Fin m → ℝ))) :
    Tendsto (fun k : ℕ => noisyObservation m (1 / ((k : ℝ) + 1)) z)
      atTop (𝓝 (noisyObservation m 0 z)) := by
  apply Filter.Tendsto.prodMk_nhds tendsto_const_nhds
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_const_nhds.add
    (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _)

theorem projectionLaw_set_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m n : ℕ) (hn : 1 ≤ n) (hmargin : (n : ℝ) + m ≤ a)
    (S : Set ((Fin m → E) × (Fin m → ℝ))) :
    projectionLaw ν m S ≤
      (ν Set.univ * (replicaConstant ν a m)^n)^(1 / ((n : ℝ) + 1)) *
      (matrixLabelReference (E := E) m S)^(1 - 1 / ((n : ℝ) + 1)) := by
  have hp : 1 < (n : ℝ) + 1 := by exact_mod_cast (by omega : 1 < n + 1)
  have hα : 0 < 1 - 1 / ((n : ℝ) + 1) := by
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hp)
  have hC : ν Set.univ * (replicaConstant ν a m)^n ≠ ∞ := by
    unfold replicaConstant
    finiteness
  have := matrixLabelReference_outerRegular (E := E) m
  apply measure_apply_le_of_isOpen _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) hC) hα
  intro U hU
  rw [← gaussianCoupling_map_noisyObservation_zero ν m]
  apply map_apply_open_le_of_tendsto (gaussianCoupling ν m)
    (matrixLabelReference (E := E) m) (noisyObservation m 0)
    (fun k => noisyObservation m (1 / ((k : ℝ) + 1)))
    (measurable_noisyObservation m 0) (fun k => measurable_noisyObservation m _)
    (tendsto_noisyObservation m) _ _ (U := U) (hU := hU)
  intro k V hV
  have hδ : (1 / ((k : ℝ) + 1)) ≠ 0 := by positivity
  rw [gaussianCoupling_map_noisyObservation ν m _ hδ]
  apply withDensity_apply_le_moment _ _
    (measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _) hp _ _ hV.measurableSet
  have hv : (NNReal.mk ((1 / ((k : ℝ) + 1)) ^ 2)
      (sq_nonneg (1 / ((k : ℝ) + 1)))) ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    exact pow_ne_zero 2 hδ
  simpa only [← ENNReal.rpow_natCast, Nat.cast_add, Nat.cast_one, matrixLabelReference]
    using projectionSmoothing_moment hν hsupport
      (gaussianPDF 0 (NNReal.mk ((1 / ((k : ℝ) + 1)) ^ 2)
        (sq_nonneg (1 / ((k : ℝ) + 1))))) (measurable_gaussianPDF _ _)
      (lintegral_gaussianPDF_eq_one _ hv) m n hmargin

end ProjectionCoupling

open scoped Pointwise

section Rows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Rows

section NetNorm
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
end NetNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SubsphereRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open scoped Topology
open InnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereRegression.projectionLaw_set_bound := @_root_.OAI.SubsphereRegression.projectionLaw_set_bound
