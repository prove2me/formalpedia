-- Prove2me | solution 1 for K24.Global.uniform_holder_shifted_remaining
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T05:51:54.994344+00:00
-- url     : https://prove2.me/submissions/b247d700-1289-431e-927b-14218c59be89
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_K24_Global_actual_holder_vector_operators
import Theorems.Thm_K24_Global_uniform_holder_shifted_estimates_remaining
import Definitions.Def_K24HolderEstimatesRemaining

set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal Manifold ContDiff Matrix.Norms.Elementwise
namespace K24.Global.HolderIntegration
universe u

/-- Exact public vector-operator boundary, used as an explicit premise here. -/
def VectorResult : Prop :=
∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [CompactSpace M]
    (C : BoundedLocalCover M) (b : MetricCoefficientNumerics) (k : ℕ),
    k + 2 ≤ b.order →
    ∀ (H : ℝ≥0) (rho : CircleAction M),
      HolderActionControl C b.exponent.value H (k + 2) rho →
    ∀ (ghat g : RawCov2 M),
      MetricAdmissible C b ghat → MetricAdmissible C b g →
      (∀ Y : RawVector M, C.VectorHolder (k + 2) b.exponent.value Y →
        C.Cov2Holder (k + 1) b.exponent.value (lieTensor Y g) ∧
        C.CovectorHolder k b.exponent.value (vectorOperator ghat g Y) ∧
        CovectorHaarIntegrable rho (vectorOperator ghat g Y)) ∧
      Set.MapsTo (projectedVectorOperator rho ghat g)
        (vectorHolderPerp C (k + 2) b.exponent.value rho)
        (covectorHolderPerp C k b.exponent.value rho) ∧
      SectionLinearOn (vectorHolderPerp C (k + 2) b.exponent.value rho)
        (projectedVectorOperator rho ghat g) ∧
      SectionBoundedOn (vectorHolderPerp C (k + 2) b.exponent.value rho)
        (C.vectorENorm (k + 2) b.exponent.value) (C.covectorENorm k b.exponent.value)
        (projectedVectorOperator rho ghat g)

/-- Exact public Bianchi and tensor-defect regularity boundary. -/
def TensorResult : Prop :=
∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [CompactSpace M],
    ∀ (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
      (rho : CircleAction M) (ghat z : RawCov2 M),
      MetricAdmissible C b ghat → MetricAdmissible C b z →
      (∀ u : RawCov2 M, C.Cov2Holder 2 b.exponent.value u →
        C.CovectorHolder 1 b.exponent.value (bianchi ghat u) ∧
        C.CovectorHolder 1 b.exponent.value (bianchi z u) ∧
        CovectorHaarIntegrable rho (bianchi ghat u) ∧
        CovectorHaarIntegrable rho (bianchi z u)) ∧
      (∀ u ∈ tensorHolderSpace C 2 b.exponent.value,
        C.Cov2Holder 0 b.exponent.value (tensorDefect ghat z u))

/-- Previously accepted numerical-only symbol bound. -/
def SymbolResult : Prop :=
∀ b : MetricCoefficientNumerics, ∃ CT : ℝ≥0, 0 < CT ∧
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M],
    ∀ (C : BoundedLocalCover M) (ghat z : RawCov2 M),
      MetricAdmissible C b ghat → MetricAdmissible C b z →
      ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
      ∀ (xi : Fin 4 → ℝ) (A : Mat4),
        metricTensorPointNorm z c x (tensorDefectPrincipalSymbol ghat z c x xi A) ≤
          (CT : ℝ) * metricTensorPointNorm z c x (cov2InChart (ghat-z) c x) *
            (metricCovectorPointNorm z c x xi)^2 * metricTensorPointNorm z c x A 

/-- A faithful reconstruction: seven retained natural fields imply the original
12-field residual when the five closed fields are supplied. Constants remain
numerical-only, with a maximum joining the tensor and symbol constants. -/
theorem natural_remaining_of_estimates
    (hV : VectorResult.{u}) (hT : TensorResult.{u}) (hS : SymbolResult.{u})
    (h : UniformHolderNaturalEstimatesRemaining.{u}) :
    UniformHolderNaturalRemaining.{u} := by
  intro cb b H hH
  obtain ⟨CT, CV, hCT, hCV, hrest⟩ := h cb b H hH
  obtain ⟨CS, hCS, hsymbol⟩ := hS b
  refine ⟨max CT CS, CV, lt_of_lt_of_le hCT (le_max_left CT CS), hCV, ?_⟩
  intro M _ _ _ _ _ C hC rho hact lam ghat z g hh hz hg hIhat hIz
  have hr := hrest M C hC rho hact lam ghat z g hh hz hg hIhat hIz
  have hreg := hT M C b rho ghat z hh hz
  have hv := hV M C b 0 b.order_ge_two H rho hact ghat g hh hg
  have hzv := hV M C b 0 b.order_ge_two H rho hact z z hz hz
  refine {
    exact_identities := hr.exact_identities
    bianchi_regularity := hreg.1
    vector_regularity := ?_
    defect_regularity := hreg.2
    fixed_frechet := hr.fixed_frechet
    reanchored_frechet := hr.reanchored_frechet
    tensor_estimate := ?_
    symbol_estimate := ?_
    vector_center_estimate := hr.vector_center_estimate
    vector_actual_estimate := hr.vector_actual_estimate
    tensor_operator := hr.tensor_operator
    vector_operator := hv.2 }
  · intro Y hY
    obtain ⟨hLie, hActual, hHaar⟩ := hv.1 Y hY
    obtain ⟨_, hCenter, hCenterHaar⟩ := hzv.1 Y hY
    exact ⟨hLie, hActual, hCenter, hHaar, hCenterHaar⟩
  · intro v hv
    apply (hr.tensor_estimate v hv).trans
    exact mul_le_mul_left (mul_le_mul_left
      (ENNReal.coe_le_coe.mpr (le_max_left CT CS)) _) _
  · intro c x hx xi a
    apply (hsymbol M C ghat z hh hz c x hx xi a).trans
    have hc : (CS : ℝ) ≤ (max CT CS : ℝ≥0) := by exact_mod_cast le_max_right CT CS
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) (sq_nonneg _))
      (Real.sqrt_nonneg _)

/-- The original shifted residual needs exactly its two numerical difference
estimates once the genuine vector regularity/operator result is supplied. -/
theorem shifted_remaining_of_estimates
    (hV : VectorResult.{u}) (h : UniformHolderShiftedEstimatesRemaining.{u}) :
    UniformHolderShiftedRemaining.{u} := by
  intro cb b hb H hH
  obtain ⟨CV, hCV, hrest⟩ := h cb b hb H hH
  refine ⟨CV, hCV, ?_⟩
  intro M _ _ _ _ _ C hC rho hact ghat z g hh hz hg hIhat hIz
  have hr := hrest M C hC rho hact ghat z g hh hz hg hIhat hIz
  have hv := hV M C b 1 hb H rho hact ghat g hh hg
  have hzv := hV M C b 1 hb H rho hact z z hz hz
  refine {
    vector_regularity := ?_
    center_estimate := hr.center_estimate
    actual_estimate := hr.actual_estimate
    vector_operator := hv.2 }
  intro Y hY
  obtain ⟨hLie, hActual, hHaar⟩ := hv.1 Y hY
  obtain ⟨_, hCenter, hCenterHaar⟩ := hzv.1 Y hY
  exact ⟨hLie, hActual, hCenter, hHaar, hCenterHaar⟩

end K24.Global.HolderIntegration


open K24.Global
universe v
theorem solution : K24.Global.UniformHolderShiftedRemaining.{v} := by
  exact HolderIntegration.shifted_remaining_of_estimates actual_holder_vector_operators uniform_holder_shifted_estimates_remaining
#print axioms solution
