-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_rooted_spectral_linear_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:24:07.725944+00:00
-- url     : https://prove2.me/submissions/3710fed1-2e2d-4a00-b98c-3b0a8410a19f

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Theorems.Thm_OAI_InvariantIsing_cavity_rooted_quadratic_gaussian

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The noncommuting resolvent identities in the quadratic cavity tilt.
These finite matrix statements include the zero-dimensional convention. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

private lemma cavity_inverse_pushThrough {d : ℕ} (C K J R : Matrix (Fin d) (Fin d) ℝ)
    (hJ : J * (1 - C * K) = 1) (hR : (1 - K * C) * R = 1) :
    J * C = C * R := by
  calc
    J * C = J * C * ((1 - K * C) * R) := by rw [hR, mul_one]
    _ = (J * (1 - C * K)) * C * R := by noncomm_ring
    _ = C * R := by rw [hJ, one_mul]

private lemma cavity_inverse_difference {d : ℕ}
    (B C K J R : Matrix (Fin d) (Fin d) ℝ)
    (hJ : J * (1 - B * K) = 1) (hR : (1 - K * C) * R = 1) :
    J * B - C * R = J * (B - C) * R := by
  calc
    J * B - C * R = J * B * ((1 - K * C) * R) - (J * (1 - B * K)) * C * R := by
      rw [hR, hJ, mul_one, one_mul]
    _ = J * (B - C) * R := by noncomm_ring

lemma cavityResolvent_pushThrough {d : ℕ} (K C : Matrix (Fin d) (Fin d) ℝ)
    (hC : IsUnit (1 - C * K).det) :
    cavityResolvent K C = C * (1 - K * C)⁻¹ := by
  have hR : IsUnit (1 - K * C).det := by
    rwa [Matrix.det_one_sub_mul_comm]
  exact cavity_inverse_pushThrough C K _ _
    (Matrix.nonsing_inv_mul _ hC) (Matrix.mul_nonsing_inv _ hR)

/-- Equation `cav:q-resolvent-difference`, with the matrix factors in their
required order. No commutation hypothesis is used. -/
theorem cavityResolvent_difference {d : ℕ} (K B C : Matrix (Fin d) (Fin d) ℝ)
    (hB : IsUnit (1 - B * K).det) (hC : IsUnit (1 - C * K).det) :
    cavityResolvent K B - cavityResolvent K C =
      (1 - B * K)⁻¹ * (B - C) * (1 - K * C)⁻¹ := by
  have hR : IsUnit (1 - K * C).det := by
    rwa [Matrix.det_one_sub_mul_comm]
  rw [cavityResolvent_pushThrough K C hC]
  exact cavity_inverse_difference B C K _ _
    (Matrix.nonsing_inv_mul _ hB) (Matrix.mul_nonsing_inv _ hR)

theorem cavityResolvent_difference_symmetric {d : ℕ}
    (K B C : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K) (hC : C.transpose = C)
    (hBdet : IsUnit (1 - B * K).det) (hCdet : IsUnit (1 - C * K).det) :
    cavityResolvent K B - cavityResolvent K C =
      (1 - B * K)⁻¹ * (B - C) * ((1 - C * K)⁻¹).transpose := by
  rw [cavityResolvent_difference K B C hBdet hCdet]
  congr 1
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hK, hC]

/-- The quadratic tilt replaces the original spectral block by the full
block in its resolvent, exactly as in `cav:q-transform`. -/
theorem cavityResolvent_spectral_transform {d : ℕ}
    (A A0 : Matrix (Fin d) (Fin d) ℝ) (b : ℝ)
    (h0 : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A0).det)
    (hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det) :
    cavityResolvent (A - A0) ((b • (1 : Matrix (Fin d) (Fin d) ℝ) - A0)⁻¹) =
      (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A)⁻¹ := by
  let D0 := b • (1 : Matrix (Fin d) (Fin d) ℝ) - A0
  let D := b • (1 : Matrix (Fin d) (Fin d) ℝ) - A
  have hD0 : IsUnit D0.det := h0
  have hD : IsUnit D.det := hA
  have hd : D = D0 - (A - A0) := by dsimp only [D, D0]; abel
  have hf : 1 - D0⁻¹ * (A - A0) = D0⁻¹ * D := by
    rw [hd]
    calc
      _ = D0⁻¹ * D0 - D0⁻¹ * (A - A0) := by rw [Matrix.nonsing_inv_mul D0 hD0]
      _ = _ := (mul_sub D0⁻¹ D0 (A - A0)).symm
  have hi : (1 - D0⁻¹ * (A - A0))⁻¹ = D⁻¹ * D0 := by
    apply Matrix.inv_eq_right_inv
    rw [hf]
    calc
      (D0⁻¹ * D) * (D⁻¹ * D0) = D0⁻¹ * (D * D⁻¹) * D0 := by simp only [mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv D hD, mul_one, Matrix.nonsing_inv_mul D0 hD0]
  change (1 - D0⁻¹ * (A - A0))⁻¹ * D0⁻¹ = D⁻¹
  rw [hi, mul_assoc, Matrix.mul_nonsing_inv D0 hD0, mul_one]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional algebra in `cav:q-factor` and the backward
quadratic recursion.  The factors retain their order: neither the two
covariances nor the quadratic coefficient need commute. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

theorem cavity_quadratic_factor {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hC : IsUnit (1 - C * K).det) :
    1 - (P - C) * cavityBackwardQuadratic K C =
      (1 - P * K) * (1 - C * K)⁻¹ := by
  unfold cavityBackwardQuadratic
  calc
    1 - (P - C) * (K * (1 - C * K)⁻¹) =
        (1 - C * K) * (1 - C * K)⁻¹ -
          (P - C) * (K * (1 - C * K)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hC]
    _ = (1 - P * K) * (1 - C * K)⁻¹ := by noncomm_ring

theorem cavityStepTransition_eq {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det) :
    cavityStepTransition K P C = (1 - C * K) * (1 - P * K)⁻¹ := by
  unfold cavityStepTransition
  apply Matrix.inv_eq_right_inv
  rw [cavity_quadratic_factor K P C hC]
  calc
    ((1 - P * K) * (1 - C * K)⁻¹) *
        ((1 - C * K) * (1 - P * K)⁻¹) =
        (1 - P * K) * ((1 - C * K)⁻¹ * (1 - C * K)) * (1 - P * K)⁻¹ := by
      simp only [mul_assoc]
    _ = 1 := by
      rw [Matrix.nonsing_inv_mul _ hC, mul_one, Matrix.mul_nonsing_inv _ hP]

/-- The identity `J_i T_i = J_{i-1}` used in square completion. -/
theorem cavity_quadratic_backward_inverse {d : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det) :
    (1 - C * K)⁻¹ * cavityStepTransition K P C = (1 - P * K)⁻¹ := by
  rw [cavityStepTransition_eq K P C hP hC, ← mul_assoc,
    Matrix.nonsing_inv_mul _ hC, one_mul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityScalarResolventBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform scalar resolvent bounds, including the extension at zero.
The comparison uses any alphabet point above the compressed eigenvalue. -/

noncomputable section
open Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma cavityScalarResolvent_denominator_pos (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α x : ℝ} (hα : α ≤ eig a) (hx : 0 ≤ x) :
    0 < 1 + x * (finiteR ρ eig hρ hρsum x - α) := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num
  · have hgap : 0 < finiteInverse ρ eig hρ hρsum x - α :=
      sub_pos.mpr (hα.trans_lt ((finiteInverse_spec ρ eig hρ hρsum hx).1 a))
    have he : 1 + x * (finiteR ρ eig hρ hρsum x - α) =
        x * (finiteInverse ρ eig hρ hρsum x - α) := by
      simp only [finiteR, ite_eq_left hx]
      field_simp [hx.ne']
      ring
    rw [he]
    exact mul_pos hx hgap

lemma cavityScalarResolvent_pos_eq (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α x : ℝ} (hα : α ≤ eig a) (hx : 0 < x) :
    cavityScalarResolvent ρ eig hρ hρsum α x =
      (finiteInverse ρ eig hρ hρsum x - α)⁻¹ := by
  have hg : finiteInverse ρ eig hρ hρsum x - α ≠ 0 :=
    (sub_pos.mpr (hα.trans_lt ((finiteInverse_spec ρ eig hρ hρsum hx).1 a))).ne'
  have hden : 1 + x * (finiteR ρ eig hρ hρsum x - α) =
      x * (finiteInverse ρ eig hρ hρsum x - α) := by
    simp only [finiteR, ite_eq_left hx]
    field_simp [hx.ne']
    ring
  rw [cavityScalarResolvent, hden, div_mul_eq_div_div, div_self hx.ne', one_div]

lemma continuousOn_cavityScalarResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α : ℝ} (hα : α ≤ eig a) :
    ContinuousOn (cavityScalarResolvent ρ eig hρ hρsum α) (Ici 0) := by
  apply continuousOn_id.div
    (continuousOn_const.add (continuousOn_id.mul
      ((continuous_finiteR ρ eig hρ hρsum).continuousOn.sub continuousOn_const)))
  intro x hx
  exact (cavityScalarResolvent_denominator_pos ρ eig hρ hρsum a hα hx).ne'

lemma hasDerivAt_cavityScalarResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α x : ℝ} (hα : α ≤ eig a) (hx : 0 < x) :
    HasDerivAt (cavityScalarResolvent ρ eig hρ hρsum α)
      (1 / (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) *
        (finiteInverse ρ eig hρ hρsum x - α)^2)) x := by
  have hg : finiteInverse ρ eig hρ hρsum x - α ≠ 0 :=
    (sub_pos.mpr (hα.trans_lt ((finiteInverse_spec ρ eig hρ hρsum hx).1 a))).ne'
  have hM := (finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum
    (finiteInverse_spec ρ eig hρ hρsum hx).1).ne'
  have hd := ((hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx).hasDerivAt.sub_const α).inv hg
  have he : (fun y => (finiteInverse ρ eig hρ hρsum y - α)⁻¹) =ᶠ[𝓝 x]
      cavityScalarResolvent ρ eig hρ hρsum α := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (cavityScalarResolvent_pos_eq ρ eig hρ hρsum a hα hy).symm
  convert hd.congr_of_eventuallyEq he.symm using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [hM, hg]

lemma cavityScalarResolvent_derivative_bound (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α x : ℝ} (hα : α ≤ eig a) (hx : 0 < x) :
    0 ≤ 1 / (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) *
        (finiteInverse ρ eig hρ hρsum x - α)^2) ∧
    1 / (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) *
        (finiteInverse ρ eig hρ hρsum x - α)^2) ≤ (ρ a)⁻¹ := by
  classical
  let b := finiteInverse ρ eig hρ hρsum x
  let M := finiteSecondResolvent ρ eig b
  have hs : ∀ j, eig j < b := (finiteInverse_spec ρ eig hρ hρsum hx).1
  have hM : 0 < M := finiteSecondResolvent_pos (fun j => (hρ j).le) hρsum hs
  have hga : 0 < b - eig a := sub_pos.mpr (hs a)
  have hg : 0 < b - α := sub_pos.mpr (hα.trans_lt (hs a))
  have hpart : ρ a / (b - eig a)^2 ≤ M := by
    exact Finset.single_le_sum (f := fun j => ρ j / (b - eig j)^2)
      (fun j _ => div_nonneg (hρ j).le (sq_nonneg _)) (Finset.mem_univ a)
  have hsq : (b - eig a)^2 ≤ (b - α)^2 := by nlinarith
  have hprod : ρ a ≤ M * (b - α)^2 := by
    calc
      ρ a = (ρ a / (b - eig a)^2) * (b - eig a)^2 := by field_simp
      _ ≤ M * (b - eig a)^2 := mul_le_mul_of_nonneg_right hpart (sq_nonneg _)
      _ ≤ M * (b - α)^2 := mul_le_mul_of_nonneg_left hsq hM.le
  refine ⟨by positivity, ?_⟩
  simpa only [one_div, M, b] using one_div_le_one_div_of_le (hρ a) hprod

theorem cavityScalarResolvent_lipschitz (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α : ℝ} (hα : α ≤ eig a)
    {x y : ℝ} (hx : 0 ≤ x) (hy : x ≤ y) :
    |cavityScalarResolvent ρ eig hρ hρsum α y - cavityScalarResolvent ρ eig hρ hρsum α x| ≤
      (ρ a)⁻¹ * (y - x) := by
  rcases hy.eq_or_lt with rfl | hxy
  · simp
  let D := fun z => 1 / (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum z) *
    (finiteInverse ρ eig hρ hρsum z - α)^2)
  obtain ⟨z, hz, hd⟩ := exists_hasDerivAt_eq_slope
    (cavityScalarResolvent ρ eig hρ hρsum α) D hxy
    ((continuousOn_cavityScalarResolvent ρ eig hρ hρsum a hα).mono
      (fun t ht => hx.trans ht.1))
    (fun t ht => hasDerivAt_cavityScalarResolvent ρ eig hρ hρsum a hα (hx.trans_lt ht.1))
  have hbound := cavityScalarResolvent_derivative_bound ρ eig hρ hρsum a hα (hx.trans_lt hz.1)
  have he : cavityScalarResolvent ρ eig hρ hρsum α y -
      cavityScalarResolvent ρ eig hρ hρsum α x = D z * (y - x) :=
    ((eq_div_iff (sub_pos.mpr hxy).ne').mp hd).symm
  rw [he, abs_mul, abs_of_nonneg hbound.1, abs_of_pos (sub_pos.mpr hxy)]
  exact mul_le_mul_of_nonneg_right hbound.2 (sub_pos.mpr hxy).le

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMatrixResolventBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth resolvent path of a compressed finite-alphabet matrix.
Its norm bounds depend on the alphabet mass, not on the number of cascade levels. -/

noncomputable section
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator MatrixOrder

namespace InvariantIsing

variable {ι : Type*} [Fintype ι] {d : ℕ}

private lemma cavity_conjugate_diagonal_norm {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (f : Fin d → ℝ) :
    ‖Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary (Matrix.diagonal f)‖ = ‖f‖ := by
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]

lemma cavitySpectralMatrixPath_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) :
    cavitySpectralMatrixPath ρ eig hρ hρsum A hA 0 = 0 := by
  simp [cavitySpectralMatrixPath, cavityScalarResolvent]

theorem cavitySpectralMatrixPath_lipschitz (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖cavitySpectralMatrixPath ρ eig hρ hρsum A hA y -
      cavitySpectralMatrixPath ρ eig hρ hρsum A hA x‖ ≤ (ρ a)⁻¹ * (y - x) := by
  rw [cavitySpectralMatrixPath, cavitySpectralMatrixPath, ← map_sub, Matrix.diagonal_sub,
    cavity_conjugate_diagonal_norm]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (inv_nonneg.mpr (hρ a).le)
    (sub_nonneg.mpr hxy))).mpr
  intro i
  exact cavityScalarResolvent_lipschitz ρ eig hρ hρsum a (heig i) hx hxy

theorem cavitySpectralMatrixDensity_norm_le (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    ‖cavitySpectralMatrixDensity ρ eig hρ hρsum A hA x‖ ≤ (ρ a)⁻¹ := by
  rw [cavitySpectralMatrixDensity, cavity_conjugate_diagonal_norm]
  apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr (hρ a).le)).mpr
  intro i
  have h := cavityScalarResolvent_derivative_bound ρ eig hρ hρsum a (heig i) hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

theorem hasDerivAt_cavitySpectralMatrixPath (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (cavitySpectralMatrixPath ρ eig hρ hρsum A hA)
      (cavitySpectralMatrixDensity ρ eig hρ hρsum A hA x) x := by
  let diag : (Fin d → ℝ) →L[ℝ] Matrix (Fin d) (Fin d) ℝ :=
    ({ toFun := Matrix.diagonal
       map_add' := fun f g => (Matrix.diagonal_add f g).symm
       map_smul' := fun c f => Matrix.diagonal_smul c f } :
      (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ).toContinuousLinearMap
  have hc := hasDerivAt_pi.mpr (fun i =>
    hasDerivAt_cavityScalarResolvent ρ eig hρ hρsum a (heig i) hx)
  have hd := diag.hasFDerivAt.comp_hasDerivAt x hc
  have hm := (hd.const_mul (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)).mul_const
    (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ))
  convert! hm using 1
  all_goals try with_reducible_and_instances rfl

theorem cavitySpectralMatrixPath_pos_eq (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    cavitySpectralMatrixPath ρ eig hρ hρsum A hA x =
      (finiteInverse ρ eig hρ hρsum x • (1 : Matrix (Fin d) (Fin d) ℝ) - A)⁻¹ := by
  let U := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ) hA.eigenvectorUnitary
  let b := finiteInverse ρ eig hρ hρsum x
  have hb : ∀ i, b - hA.eigenvalues i ≠ 0 := fun i =>
    (sub_pos.mpr ((heig i).trans_lt ((finiteInverse_spec ρ eig hρ hρsum hx).1 a))).ne'
  have hdiag : b • (1 : Matrix (Fin d) (Fin d) ℝ) - A =
      U (Matrix.diagonal (fun i => b - hA.eigenvalues i)) := by
    have ha : U (Matrix.diagonal hA.eigenvalues) = A := by
      simpa [U] using hA.spectral_theorem.symm
    have hc : (Matrix.diagonal fun _ : Fin d => b) = b • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [← Matrix.diagonal_sub, hc, map_sub, map_smul, map_one, ha]
  have he : cavitySpectralMatrixPath ρ eig hρ hρsum A hA x =
      U (Matrix.diagonal (fun i => (b - hA.eigenvalues i)⁻¹)) := by
    simp only [cavitySpectralMatrixPath, cavityScalarResolvent_pos_eq ρ eig hρ hρsum a,
      heig, hx, U, b]
  rw [he]
  symm
  apply Matrix.inv_eq_right_inv
  rw [hdiag, ← map_mul, Matrix.diagonal_mul_diagonal]
  simp [hb]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCovariancePartitionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common root, all positive levels, and the residual have total
covariance mass one. This estimate is independent of the number of steps. -/

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_covariance_partition_bound {d n : ℕ}
    (T : ℝ → Matrix (Fin d) (Fin d) ℝ) (G : Matrix (Fin d) (Fin d) ℝ)
    (q x : Fin (n + 1) → ℝ) (b : Fin n → ℝ) {C : ℝ}
    (hT0 : T 0 = 0)
    (hT : ∀ u v, 0 ≤ u → u ≤ v → ‖T v - T u‖ ≤ C * (v - u))
    (hG : ‖G‖ ≤ C) (hq : Monotone q) (hq0 : 0 ≤ q 0)
    (hx : ∀ i, 0 ≤ x i)
    (hb : ∀ i, 0 < b i)
    (hgap : ∀ i, x i.castSucc - x i.succ = b i * (q i.succ - q i.castSucc))
    (hlast : x (Fin.last n) = 1 - q (Fin.last n)) :
    ‖q 0 • G + (∑ i : Fin n, (b i)⁻¹ • (T (x i.castSucc) - T (x i.succ))) +
      T (x (Fin.last n))‖ ≤ C := by
  have hqstep (i : Fin n) : 0 ≤ q i.succ - q i.castSucc :=
    sub_nonneg.mpr (hq (Fin.castSucc_le_succ i))
  have hstep (i : Fin n) :
      ‖(b i)⁻¹ • (T (x i.castSucc) - T (x i.succ))‖ ≤ C * (q i.succ - q i.castSucc) := by
    have horder : x i.succ ≤ x i.castSucc := by
      have := mul_nonneg (hb i).le (hqstep i)
      linarith [hgap i]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hb i))]
    calc
      _ ≤ (b i)⁻¹ * (C * (x i.castSucc - x i.succ)) :=
        mul_le_mul_of_nonneg_left (hT _ _ (hx i.succ) horder) (inv_pos.mpr (hb i)).le
      _ = C * (q i.succ - q i.castSucc) := by rw [hgap i]; field_simp [(hb i).ne']
  have hroot : ‖q 0 • G‖ ≤ C * q 0 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hG hq0
  have htail : ‖T (x (Fin.last n))‖ ≤ C * (1 - q (Fin.last n)) := by
    simpa only [hT0, sub_zero, hlast] using hT 0 (x (Fin.last n)) le_rfl (hx _)
  have htel : (∑ i : Fin n, (q i.succ - q i.castSucc)) = q (Fin.last n) - q 0 := by
    rw [Finset.sum_sub_distrib]
    have h0 := Fin.sum_univ_succ q
    have h1 := Fin.sum_univ_castSucc q
    linarith
  calc
    _ ≤ ‖q 0 • G‖ + ‖∑ i : Fin n, (b i)⁻¹ • (T (x i.castSucc) - T (x i.succ))‖ +
        ‖T (x (Fin.last n))‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C * q 0 + (∑ i : Fin n, C * (q i.succ - q i.castSucc)) + C * (1 - q (Fin.last n)) := by
      exact add_le_add (add_le_add hroot ((norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun i _ => hstep i)))) htail
    _ = C := by rw [← Finset.mul_sum, htel]; ring

theorem cavity_spectral_covariance_partition_bound {ι : Type*} [Fintype ι] {d n : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (q x : Fin (n + 1) → ℝ) (b : Fin n → ℝ)
    (hq : Monotone q) (hq0 : 0 ≤ q 0) (hx : ∀ i, 0 ≤ x i) (hx0 : 0 < x 0)
    (hb : ∀ i, 0 < b i)
    (hgap : ∀ i, x i.castSucc - x i.succ = b i * (q i.succ - q i.castSucc))
    (hlast : x (Fin.last n) = 1 - q (Fin.last n)) :
    let T := cavitySpectralMatrixPath ρ eig hρ hsum A hA
    ‖q 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A hA (x 0) +
      (∑ i : Fin n, (b i)⁻¹ • (T (x i.castSucc) - T (x i.succ))) +
      T (x (Fin.last n))‖ ≤ (ρ a)⁻¹ := by
  intro T
  exact cavity_covariance_partition_bound T
    (cavitySpectralMatrixDensity ρ eig hρ hsum A hA (x 0)) q x b
    (cavitySpectralMatrixPath_zero ρ eig hρ hsum A hA)
    (fun _ _ hu huv => cavitySpectralMatrixPath_lipschitz ρ eig hρ hsum A hA a heig hu huv)
    (cavitySpectralMatrixDensity_norm_le ρ eig hρ hsum A hA a heig hx0)
    hq hq0 hx hb hgap hlast

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_PartitionPowLe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition Pow Le. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron



lemma exp_integral_le_partition {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ}
    (hH : Integrable H ν) (he : Integrable (fun x => Real.exp (H x)) ν) :
    Real.exp (∫ x, H x ∂ν) ≤ ∫ x, Real.exp (H x) ∂ν := by
  exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => mem_univ _)) hH he

 

lemma partition_inv_pow_le {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ} (p : ℕ)
    (hH : Integrable H ν)
    (h1 : Integrable (fun x => Real.exp (H x)) ν)
    (hp : Integrable (fun x => Real.exp (-(p:ℝ)*H x)) ν) :
    ((∫ x, Real.exp (H x) ∂ν)^p)⁻¹ ≤ ∫ x, Real.exp (-(p:ℝ)*H x) ∂ν := by
  have hj := exp_integral_le_partition hH h1
  have hz : 0 < ∫ x, Real.exp (H x) ∂ν := (Real.exp_pos _).trans_le hj
  calc
    _ ≤ (Real.exp (∫ x, H x ∂ν)^p)⁻¹ :=
      (inv_le_inv₀ (pow_pos hz _) (pow_pos (Real.exp_pos _) _)).mpr
        (pow_le_pow_left₀ (Real.exp_pos _).le hj _)
    _ = Real.exp (∫ x, -(p:ℝ)*H x ∂ν) := by
      rw [integral_const_mul, ← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      ring
    _ ≤ _ := exp_integral_le_partition (hH.const_mul _) hp



end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ConvexDerivativeFluctuation
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex Derivative Fluctuation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma integral_tilted_ratio {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H F : X → ℝ) :
    (∫ x, F x ∂ν.tilted H) = (∫ x, Real.exp (H x)*F x ∂ν)/(∫ x, Real.exp (H x) ∂ν) := by
  rw [integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]

lemma measurable_random_tilted_integral {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H F : Ω × X → ℝ} (hH : Measurable H) (hF : Measurable F) :
    Measurable (fun ω => ∫ x, F (ω,x) ∂(ν ω).tilted (fun x => H (ω,x))) := by
  let κ : Kernel Ω X := ⟨ν,hν⟩
  have : IsMarkovKernel κ := ⟨fun ω => by change IsProbabilityMeasure (ν ω); infer_instance⟩
  simp_rw [integral_tilted_ratio]
  exact ((hH.exp.mul hF).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable.div
    ((hH.exp).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFactorBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quadratic growth bound for the actual cavity exponent. The bound
does not require the special-coordinate block matrices to commute. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_bilinear_abs_bound {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (x : Fin d → ℝ) (y : Fin n → ℝ) {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ b) :
    |∑ i, ∑ j, x i * A i j * y j| ≤ cavityMatrixMass A * (a * b) := by
  calc
    _ ≤ ∑ i, |∑ j, x i * A i j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x i * A i j * y j| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |A i j| * (a * b) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      calc
        _ = |A i j| * (|x i| * |y j|) := by simp only [abs_mul]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul (hx i) (hy j) (abs_nonneg _) ha)
          (abs_nonneg _)
    _ = _ := by simp only [cavityMatrixMass, Finset.sum_mul]

lemma cavity_spin_quadratic_abs_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ε : Spin n) :
    |cavityQuadratic A (fun j => spinValue (ε j))| ≤ cavityMatrixMass A := by
  have h := cavity_bilinear_abs_bound A (fun j => spinValue (ε j)) (fun j => spinValue (ε j))
    zero_le_one zero_le_one (fun i => (abs_spinValue (ε i)).le) (fun i => (abs_spinValue (ε i)).le)
  rw [cavityQuadratic, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hm := cavityMatrixMass_nonneg A
  simp only [mul_one] at h
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianEnvelope
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial-exponential moments for the finite Gaussian marks
after the quadratic tilt. Only the norm of the covariance factor matters. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

lemma cavity_standardGaussian_exp_norm_integrable (d : ℕ) (c : ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => Real.exp (c * ‖z‖)) (stdGaussian _) := by
  obtain ⟨a, ha, hi⟩ := IsGaussian.exists_integrable_exp_sq (stdGaussian (EuclideanSpace ℝ (Fin d)))
  let b := c^2 / (4 * a)
  have hb : 4 * a * b = c^2 := mul_div_cancel₀ _ (by positivity)
  apply (hi.const_mul (Real.exp b)).mono' (by fun_prop)
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hs := sq_nonneg (2 * a * ‖z‖ - c)
    nlinarith

lemma cavity_polynomial_exp_bound (p : ℕ) (c r : ℝ) (hr : 0 ≤ r) :
    r^p * Real.exp (c * r) ≤ Real.exp ((p + c) * r) := by
  have he : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  have hp := pow_le_pow_left₀ hr he p
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (c * r)).le
  rw [← Real.exp_nat_mul, ← Real.exp_add] at hm
  simpa only [add_mul] using hm

theorem cavity_gaussian_linear_polynomial_exp_bound {d q : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin q))
    {M c : ℝ} (_hM : 0 ≤ M) (hL : ‖L‖ ≤ M) (hc : 0 ≤ c) (p : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => ‖L z‖^p * Real.exp (c * ‖L z‖))
      (stdGaussian _) ∧
    (∫ z : EuclideanSpace ℝ (Fin d), ‖L z‖^p * Real.exp (c * ‖L z‖) ∂stdGaussian _) ≤
      ∫ z : EuclideanSpace ℝ (Fin d), Real.exp (((p : ℝ) + c) * M * ‖z‖) ∂stdGaussian _ := by
  have hi := cavity_standardGaussian_exp_norm_integrable d (((p : ℝ) + c) * M)
  have hb z : ‖L z‖^p * Real.exp (c * ‖L z‖) ≤ Real.exp (((p : ℝ) + c) * M * ‖z‖) := by
    have hn : ‖L z‖ ≤ M * ‖z‖ := (L.le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg z))
    apply (cavity_polynomial_exp_bound p c ‖L z‖ (norm_nonneg _)).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hn (add_nonneg (Nat.cast_nonneg p) hc)]
  have hif : Integrable (fun z : EuclideanSpace ℝ (Fin d) => ‖L z‖^p * Real.exp (c * ‖L z‖))
      (stdGaussian _) := by
    apply hi.mono' (by fun_prop)
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hb z
  exact ⟨hif, integral_mono hif hi hb⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianFactorAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite matrix identities connecting standard-Gaussian square
completion with the original, possibly singular, covariance `B Bᵀ`. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

theorem cavity_factor_det {d : ℕ} (K B : Matrix (Fin d) (Fin d) ℝ) :
    (cavityFactorPrecision K B).det = (1 - (B * B.transpose) * K).det := by
  unfold cavityFactorPrecision
  rw [Matrix.det_one_sub_mul_comm (B.transpose * K) B, ← mul_assoc]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityQuadraticCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix covariance identities of `cav:q-innovations`.  These
identities apply also to zero covariance increments. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

/-- Rescaling a tilted-step covariance by `J_i` gives the innovation
covariance with the previous inverse on the left. -/
theorem cavity_rescaled_step_covariance {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det) :
    (1 - C * K)⁻¹ * (cavityStepTransition K P C * S) *
        ((1 - C * K)⁻¹).transpose =
      (1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose := by
  rw [← mul_assoc, cavity_quadratic_backward_inverse K P C hP hC]

/-- The covariance increment transforms by the resolvent difference.
This multiplication form does not require a nonzero cascade exponent. -/
theorem cavity_innovation_covariance_mul {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ)
    (hK : K.transpose = K) (hC : C.transpose = C)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S) :
    ζ • ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) =
      cavityResolvent K P - cavityResolvent K C := by
  rw [cavityResolvent_difference_symmetric K P C hK hC hPdet hCdet, hΔ]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMultivariateGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quadratic integral for the actual multivariate Gaussian law.
The covariance is allowed to be singular. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_covariance_sqrt_factor {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) :
    CFC.sqrt S * (CFC.sqrt S).transpose = S := by
  have hs : (CFC.sqrt S).transpose = CFC.sqrt S := by
    have hs' : (CFC.sqrt S).PosSemidef :=
      (Matrix.nonneg_iff_posSemidef).mp (CFC.sqrt_nonneg S)
    exact Matrix.isHermitian_iff_isSymm.mp hs'.isHermitian
  rw [hs]
  exact CFC.sqrt_mul_sqrt_self S hS.nonneg

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTiltCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive covariance of a quadratic Gaussian tilt. -/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_inverse_push_factor {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsUnit (cavityFactorPrecision K B).det) :
    (1 - (B * B.transpose) * K)⁻¹ * B = B * (cavityFactorPrecision K B)⁻¹ := by
  have hA : IsUnit (1 - (B * B.transpose) * K).det := by
    rwa [← cavity_factor_det]
  have hf : (1 - (B * B.transpose) * K) * B = B * cavityFactorPrecision K B := by
    unfold cavityFactorPrecision
    noncomm_ring
  have hc : (1 - (B * B.transpose) * K) * (B * (cavityFactorPrecision K B)⁻¹) = B := by
    rw [← mul_assoc, hf, mul_assoc, Matrix.mul_nonsing_inv _ hQ, mul_one]
  calc
    _ = (1 - (B * B.transpose) * K)⁻¹ *
        ((1 - (B * B.transpose) * K) * (B * (cavityFactorPrecision K B)⁻¹)) := by rw [hc]
    _ = _ := Matrix.nonsing_inv_mul_cancel_left _ _ hA

theorem cavity_tilt_covariance_factor {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsUnit (cavityFactorPrecision K B).det) :
    cavityResolvent K (B * B.transpose) =
      B * (cavityFactorPrecision K B)⁻¹ * B.transpose := by
  unfold cavityResolvent
  rw [← mul_assoc, cavity_inverse_push_factor K B hQ]

theorem cavity_tilt_covariance_posSemidef {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt S)).PosDef) :
    (cavityResolvent K S).PosSemidef := by
  rw [← cavity_covariance_sqrt_factor S hS,
    cavity_tilt_covariance_factor K (CFC.sqrt S) (isUnit_iff_ne_zero.mpr hQ.det_pos.ne')]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hQ.inv.posSemidef.mul_mul_conjTranspose_same (CFC.sqrt S)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityInnovationCovariancePositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of the noncommuting innovation covariance. -/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_innovation_covariance_posSemidef {d : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (ζ : ℝ)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hQ : (cavityFactorPrecision (ζ • cavityBackwardQuadratic K C)
      (CFC.sqrt S)).PosDef) :
    ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose).PosSemidef := by
  have hcov : cavityStepTransition K P C * S =
      cavityResolvent (ζ • cavityBackwardQuadratic K C) S := by
    unfold cavityStepTransition cavityResolvent
    rw [hΔ]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [← cavity_rescaled_step_covariance K P C S hPdet hCdet, hcov]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (cavity_tilt_covariance_posSemidef (ζ • cavityBackwardQuadratic K C) S hS hQ).mul_mul_conjTranspose_same
      (1 - C * K)⁻¹

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLinearTiltMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moments after the remaining linear tilt can be bounded using only
one-replica Gaussian moments, by Jensen and the elementary product bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_linear_tilt_moment_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (V f : X → ℝ)
    (hV : Integrable V ν) (he : Integrable (fun x => Real.exp (V x)) ν)
    (heNeg : Integrable (fun x => Real.exp (-V x)) ν) (hf0 : ∀ x, 0 ≤ f x)
    (hfe : Integrable (fun x => f x * Real.exp (V x)) ν)
    (hfe2 : Integrable (fun x => (f x * Real.exp (V x))^2) ν)
    (heNeg2 : Integrable (fun x => Real.exp (-V x)^2) ν) :
    (∫ x, f x ∂ν.tilted V) ≤
      ((∫ x, (f x * Real.exp (V x))^2 ∂ν) + (∫ x, Real.exp (-V x)^2 ∂ν)) / 2 := by
  have hJ := partition_inv_pow_le (ν := ν) (H := V) 1 hV he (by
    simpa only [Nat.cast_one, neg_mul, one_mul] using heNeg)
  simp only [pow_one, Nat.cast_one, neg_mul, one_mul] at hJ
  have hA0 : 0 ≤ ∫ x, f x * Real.exp (V x) ∂ν := integral_nonneg
    (fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le)
  have hA := (convexOn_pow 2 (𝕜 := ℝ)).map_integral_le (by fun_prop) isClosed_Ici
    (ae_of_all _ (fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le)) hfe hfe2
  have hB := (convexOn_pow 2 (𝕜 := ℝ)).map_integral_le (by fun_prop) isClosed_Ici
    (ae_of_all _ (fun x => (Real.exp_pos (-V x)).le)) heNeg heNeg2
  have hbound := mul_le_mul_of_nonneg_left hJ hA0
  rw [integral_tilted_eq_div]
  have hswap : (∫ x, Real.exp (V x) * f x ∂ν) = ∫ x, f x * Real.exp (V x) ∂ν := by
    apply integral_congr_ae
    exact ae_of_all _ (fun x => mul_comm _ _)
  rw [hswap, div_eq_mul_inv]
  nlinarith [sq_nonneg ((∫ x, f x * Real.exp (V x) ∂ν) - ∫ x, Real.exp (-V x) ∂ν)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLinearEnvelope
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform moments of the remaining linear cavity tilt. The estimate uses
only the one-replica exponential radial moment after the quadratic tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Topology

namespace InvariantIsing

lemma cavity_linear_logFactor_growth {d n : ℕ}
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin d)) (ε : Spin n) :
    |cavityLogFactor 0 L C y ε| ≤
      (cavityMatrixMass L + cavityMatrixMass C) * (1 + ‖y‖) := by
  have hy i : |y i| ≤ ‖y‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
  have hL := cavity_bilinear_abs_bound L y (fun j => spinValue (ε j))
    (norm_nonneg y) zero_le_one hy (fun j => (abs_spinValue (ε j)).le)
  have hC := cavity_spin_quadratic_abs_bound C ε
  have hz : cavityQuadratic (0 : Matrix (Fin d) (Fin d) ℝ) y = 0 := by
    simp [cavityQuadratic]
  simp only [mul_one] at hL
  simp only [cavityLogFactor, hz, zero_add]
  apply (abs_add_le _ _).trans
  nlinarith [cavityMatrixMass_nonneg L, cavityMatrixMass_nonneg C, norm_nonneg y,
    mul_nonneg (cavityMatrixMass_nonneg C) (norm_nonneg y)]

lemma cavity_linear_envelope_bounds (p : ℕ) {c r v : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hv : |v| ≤ c * (1 + r)) :
    |v| ≤ c * cavityLinearMomentEnvelope p c r ∧
    Real.exp v ≤ cavityLinearMomentEnvelope p c r ∧
    Real.exp (-v) ≤ cavityLinearMomentEnvelope p c r ∧
    r^p * Real.exp v ≤ cavityLinearMomentEnvelope p c r ∧
    (r^p * Real.exp v)^2 ≤ cavityLinearMomentEnvelope p c r ∧
    Real.exp (-v)^2 ≤ cavityLinearMomentEnvelope p c r := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hve := abs_le.mp hv
  have hexp : Real.exp r ≤ cavityLinearMomentEnvelope p c r := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlin : |v| ≤ c * cavityLinearMomentEnvelope p c r :=
    hv.trans (mul_le_mul_of_nonneg_left (by simpa only [add_comm] using (Real.add_one_le_exp r).trans hexp) hc)
  have hev : Real.exp v ≤ cavityLinearMomentEnvelope p c r := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hneg : Real.exp (-v) ≤ cavityLinearMomentEnvelope p c r := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hprod : r^p * Real.exp v ≤ Real.exp ((p : ℝ) * r + v) := by
    have h := cavity_polynomial_exp_bound p 0 r hr
    simp only [zero_mul, Real.exp_zero, mul_one, add_zero] at h
    calc
      _ ≤ Real.exp ((p : ℝ) * r) * Real.exp v :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hprod1 : r^p * Real.exp v ≤ cavityLinearMomentEnvelope p c r :=
    hprod.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hprod2 : (r^p * Real.exp v)^2 ≤ cavityLinearMomentEnvelope p c r := by
    apply (pow_le_pow_left₀ (mul_nonneg (pow_nonneg hr p) (Real.exp_pos _).le) hprod 2).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hneg2 : Real.exp (-v)^2 ≤ cavityLinearMomentEnvelope p c r := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith
  exact ⟨hlin, hev, hneg, hprod1, hprod2, hneg2⟩

theorem cavity_linear_tilt_radial_moment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (V R : X → ℝ)
    (hV : Measurable V) (hR : Measurable R) (p : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hR0 : ∀ x, 0 ≤ R x) (hv : ∀ x, |V x| ≤ c * (1 + R x))
    (hi : Integrable (fun x => cavityLinearMomentEnvelope p c (R x)) ν) :
    Integrable (fun x => Real.exp (V x)) ν ∧
    Integrable (fun x => R x ^ p) (ν.tilted V) ∧
    (∫ x, R x ^ p ∂ν.tilted V) ≤
      ∫ x, cavityLinearMomentEnvelope p c (R x) ∂ν := by
  have hb x := cavity_linear_envelope_bounds p hc (hR0 x) (hv x)
  have hiV : Integrable V ν := (hi.const_mul c).mono' hV.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact (hb x).1)
  have hie : Integrable (fun x => Real.exp (V x)) ν := hi.mono' hV.exp.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact (hb x).2.1)
  have hin : Integrable (fun x => Real.exp (-V x)) ν := hi.mono' hV.neg.exp.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact (hb x).2.2.1)
  have hif : Integrable (fun x => R x^p * Real.exp (V x)) ν :=
    hi.mono' ((hR.pow_const p).mul hV.exp).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (hR0 x) p) (Real.exp_pos _).le)]
        exact (hb x).2.2.2.1)
  have hif2 : Integrable (fun x => (R x^p * Real.exp (V x))^2) ν :=
    hi.mono' (((hR.pow_const p).mul hV.exp).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact (hb x).2.2.2.2.1)
  have hin2 : Integrable (fun x => Real.exp (-V x)^2) ν :=
    hi.mono' ((hV.neg.exp).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact (hb x).2.2.2.2.2)
  have hit : Integrable (fun x => R x^p) (ν.tilted V) := by
    rw [integrable_tilted_iff hie]
    simpa only [smul_eq_mul, mul_comm] using hif
  refine ⟨hie, hit, (cavity_linear_tilt_moment_bound ν V (fun x => R x^p) hiV hie hin
    (fun x => pow_nonneg (hR0 x) p) hif hif2 hin2).trans ?_⟩
  have ha := integral_mono hif2 hi (fun x => (hb x).2.2.2.2.1)
  have hn := integral_mono hin2 hi (fun x => (hb x).2.2.2.2.2)
  linarith

theorem cavity_linear_tilt_mean_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω X) [IsMarkovKernel κ]
    (V : Ω × X → ℝ) (R : X → ℝ) (hV : Measurable V) (hR : Measurable R)
    (p : ℕ) {c : ℝ} (hc : 0 ≤ c) (hR0 : ∀ x, 0 ≤ R x)
    (hv : ∀ ω x, |V (ω, x)| ≤ c * (1 + R x))
    (hi : Integrable (fun x => cavityLinearMomentEnvelope p c (R x)) (κ ∘ₘ P)) :
    (∀ᵐ ω ∂P, Integrable (fun x => Real.exp (V (ω, x))) (κ ω) ∧
      Integrable (fun x => R x^p) ((κ ω).tilted (fun x => V (ω, x)))) ∧
    Integrable (fun ω => ∫ x, R x^p ∂(κ ω).tilted (fun x => V (ω, x))) P ∧
    (∫ ω, ∫ x, R x^p ∂(κ ω).tilted (fun x => V (ω, x)) ∂P) ≤
      ∫ x, cavityLinearMomentEnvelope p c (R x) ∂(κ ∘ₘ P) := by
  have hia := Measure.ae_integrable_of_integrable_comp hi
  have hpoint := hia.mono fun ω hω => cavity_linear_tilt_radial_moment (κ ω)
    (fun x => V (ω, x)) R (hV.comp measurable_prodMk_left) hR p hc hR0 (hv ω) hω
  have hE : Integrable (fun ω => ∫ x, cavityLinearMomentEnvelope p c (R x) ∂κ ω) P := by
    have hn := Measure.integrable_integral_norm_of_integrable_comp hi
    simpa only [Real.norm_eq_abs, cavityLinearMomentEnvelope, abs_of_pos (Real.exp_pos _)] using hn
  have hm : Measurable (fun ω => ∫ x, R x^p ∂(κ ω).tilted (fun x => V (ω, x))) :=
    measurable_random_tilted_integral κ.measurable hV
      ((hR.comp measurable_snd).pow_const p)
  have hmi : Integrable (fun ω => ∫ x, R x^p ∂(κ ω).tilted (fun x => V (ω, x))) P :=
    hE.mono' hm.aestronglyMeasurable (hpoint.mono fun ω hω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => pow_nonneg (hR0 x) p)]
      exact hω.2.2)
  refine ⟨hpoint.mono (fun _ h => ⟨h.1, h.2.1⟩), hmi, ?_⟩
  calc
    _ ≤ ∫ ω, ∫ x, cavityLinearMomentEnvelope p c (R x) ∂κ ω ∂P :=
      integral_mono_ae hmi hE (hpoint.mono fun _ h => h.2.2)
    _ = _ := by
      rw [Measure.comp_eq_comp_const_apply] at hi ⊢
      simpa only [Kernel.const_apply] using (Kernel.integral_comp hi).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityLinearGaussianMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A covariance bound gives a step-independent moment bound for the
remaining cavity tilt, including singular Gaussian covariance matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_gaussian_linear_envelope {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosSemidef) {M c : ℝ} (hSM : ‖S‖ ≤ M) (hc : 0 ≤ c) (p : ℕ) :
    Integrable (fun y : EuclideanSpace ℝ (Fin d) => cavityLinearMomentEnvelope p c ‖y‖)
      (multivariateGaussian 0 S) ∧
    (∫ y : EuclideanSpace ℝ (Fin d), cavityLinearMomentEnvelope p c ‖y‖
      ∂multivariateGaussian 0 S) ≤ cavityGaussianLinearMomentBound d p c M := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  have hL : ‖L‖ ≤ Real.sqrt M := by
    rw [Matrix.l2_opNorm_toEuclideanCLM, CFC.norm_sqrt S hS.nonneg]
    exact Real.sqrt_le_sqrt hSM
  have ha : 0 ≤ (2 : ℝ) * p + 2 * c + 1 := by positivity
  have hG := cavity_gaussian_linear_polynomial_exp_bound L (Real.sqrt_nonneg M) hL ha 0
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add] at hG
  have hi := hG.1.const_mul (Real.exp (2 * c))
  have he (z : EuclideanSpace ℝ (Fin d)) :
      cavityLinearMomentEnvelope p c ‖L z‖ =
        Real.exp (2 * c) * Real.exp ((2 * p + 2 * c + 1) * ‖L z‖) := Real.exp_add _ _
  have his : Integrable (fun y : EuclideanSpace ℝ (Fin d) =>
      cavityLinearMomentEnvelope p c ‖y‖) (multivariateGaussian 0 S) := by
    rw [multivariateGaussian, integrable_map_measure (by unfold cavityLinearMomentEnvelope; fun_prop) (by fun_prop)]
    simpa only [zero_add, Function.comp_def, cavityLinearMomentEnvelope, Real.exp_add, L] using hi
  refine ⟨his, ?_⟩
  rw [multivariateGaussian, integral_map (by fun_prop) (by unfold cavityLinearMomentEnvelope; fun_prop)]
  simp only [zero_add]
  change (∫ z : EuclideanSpace ℝ (Fin d), cavityLinearMomentEnvelope p c ‖L z‖ ∂stdGaussian _) ≤ _
  simp_rw [he]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hG.2 (Real.exp_pos _).le

theorem cavity_linear_tilt_gaussian_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω X) [IsMarkovKernel κ]
    (V : Ω × X → ℝ) (Y : X → EuclideanSpace ℝ (Fin d))
    (hV : Measurable V) (hY : Measurable Y)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hLaw : (κ ∘ₘ P).map Y = multivariateGaussian 0 S)
    {M c : ℝ} (hSM : ‖S‖ ≤ M) (hc : 0 ≤ c) (p : ℕ)
    (hv : ∀ ω x, |V (ω, x)| ≤ c * (1 + ‖Y x‖)) :
    (∀ᵐ ω ∂P, Integrable (fun x => Real.exp (V (ω, x))) (κ ω) ∧
      Integrable (fun x => ‖Y x‖^p) ((κ ω).tilted (fun x => V (ω, x)))) ∧
    Integrable (fun ω => ∫ x, ‖Y x‖^p ∂(κ ω).tilted (fun x => V (ω, x))) P ∧
    (∫ ω, ∫ x, ‖Y x‖^p ∂(κ ω).tilted (fun x => V (ω, x)) ∂P) ≤
      cavityGaussianLinearMomentBound d p c M := by
  have hG := cavity_gaussian_linear_envelope S hS hSM hc p
  have hi : Integrable (fun x => cavityLinearMomentEnvelope p c ‖Y x‖) (κ ∘ₘ P) := by
    rw [← hLaw, integrable_map_measure (by unfold cavityLinearMomentEnvelope; fun_prop) hY.aemeasurable] at hG
    exact hG.1
  have h := cavity_linear_tilt_mean_moment P κ V (fun x => ‖Y x‖) hV hY.norm p hc
    (fun x => norm_nonneg _) hv hi
  refine ⟨h.1, h.2.1, h.2.2.trans ?_⟩
  rw [← hLaw, integral_map hY.aemeasurable (by unfold cavityLinearMomentEnvelope; fun_prop)] at hG
  exact hG.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityResolventDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating the noncommuting quadratic resolvent. The resulting
compression identifies the common root covariance from the same scalar
Schur identity used at the positive levels. -/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator Topology
open Filter

namespace InvariantIsing

lemma hasDerivAt_cavityMatrixInverse {d : ℕ}
    (H : ℝ → Matrix (Fin d) (Fin d) ℝ) (H' : Matrix (Fin d) (Fin d) ℝ)
    (x : ℝ) (hH : HasDerivAt H H' x) (hdet : IsUnit (H x).det) :
    HasDerivAt (fun t => (H t)⁻¹) (-(H x)⁻¹ * H' * (H x)⁻¹) x := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hi : (↑u⁻¹ : Matrix (Fin d) (Fin d) ℝ) = (H x)⁻¹ := by
    rw [← hu, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
  have hd := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hi, hu] at hd
  have hc := hd.comp_hasDerivAt x hH
  simpa only [Function.comp_def, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, Matrix.nonsing_inv_eq_ringInverse,
    neg_mul] using hc

private lemma cavityResolvent_identity_add {d : ℕ}
    (K H : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K)
    (hH : H.transpose = H) (hdet : IsUnit (1 - H * K).det) :
    1 + K * cavityResolvent K H = ((1 - H * K)⁻¹).transpose := by
  have ht : ((1 - H * K)⁻¹).transpose = (1 - K * H)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv]
    simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hK, hH]
  have hdet' : IsUnit (1 - K * H).det := by rwa [Matrix.det_one_sub_mul_comm]
  rw [ht, cavityResolvent_pushThrough K H hdet]
  have he := Matrix.mul_nonsing_inv (1 - K * H) hdet'
  rw [Matrix.sub_mul, Matrix.one_mul] at he
  calc
    1 + K * (H * (1 - K * H)⁻¹) =
        ((1 - K * H)⁻¹ - K * H * (1 - K * H)⁻¹) +
          K * (H * (1 - K * H)⁻¹) := by rw [he]
    _ = (1 - K * H)⁻¹ := by simp only [Matrix.mul_assoc]; abel

/-- The root covariance identity `cav:q-root-covariance` holds without
commuting the covariance path with the quadratic coefficient. -/
theorem hasDerivAt_cavityResolvent {d : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (H' : Matrix (Fin d) (Fin d) ℝ) (x : ℝ)
    (hK : K.transpose = K) (hHx : (H x).transpose = H x)
    (hH : HasDerivAt H H' x) (hdet : IsUnit (1 - H x * K).det) :
    HasDerivAt (fun t => cavityResolvent K (H t))
      ((1 - H x * K)⁻¹ * H' * ((1 - H x * K)⁻¹).transpose) x := by
  have hD : HasDerivAt (fun t => 1 - H t * K) (-(H' * K)) x := by
    simpa only [zero_sub] using (hH.mul_const K).const_sub 1
  have hi := hasDerivAt_cavityMatrixInverse _ _ x hD hdet
  have hf := hi.mul hH
  change HasDerivAt (fun t => cavityResolvent K (H t))
    (-(1 - H x * K)⁻¹ * -(H' * K) * (1 - H x * K)⁻¹ * H x +
      (1 - H x * K)⁻¹ * H') x at hf
  convert! hf using 1
  all_goals try with_reducible_and_instances rfl
  rw [← cavityResolvent_identity_add K (H x) hK hHx hdet]
  unfold cavityResolvent
  noncomm_ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual quadratic change from the base spectral matrix to the full
spectral matrix, including the derivative which transports the common root. -/

noncomputable section
open Filter
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

variable {ι : Type*} [Fintype ι] {d : ℕ}

lemma cavitySpectralMatrixDensity_posSemidef (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    (cavitySpectralMatrixDensity ρ eig hρ hsum A hA x).PosSemidef := by
  have hp : (Matrix.diagonal (fun i : Fin d => 1 /
      (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hsum x) *
        (finiteInverse ρ eig hρ hsum x - hA.eigenvalues i)^2))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i =>
      (cavityScalarResolvent_derivative_bound ρ eig hρ hsum a (heig i) hx).1)
  simpa only [cavitySpectralMatrixDensity, Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose] using
      hp.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)

lemma cavity_spectral_shift_isUnit (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hsum : ∑ a, ρ a = 1) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    IsUnit (finiteInverse ρ eig hρ hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det := by
  let U := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ) hA.eigenvectorUnitary
  let b := finiteInverse ρ eig hρ hsum x
  have ha : U (Matrix.diagonal hA.eigenvalues) = A := by
    simpa [U] using hA.spectral_theorem.symm
  have hc : (Matrix.diagonal fun _ : Fin d => b) = b • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hd : b • (1 : Matrix (Fin d) (Fin d) ℝ) - A =
      U (Matrix.diagonal (fun i => b - hA.eigenvalues i)) := by
    rw [← Matrix.diagonal_sub, hc, map_sub, map_smul, map_one, ha]
  have hp := Matrix.PosDef.diagonal (fun i =>
    sub_pos.mpr ((heig i).trans_lt ((finiteInverse_spec ρ eig hρ hsum hx).1 a)))
  have hu : IsUnit (Matrix.diagonal (fun i => b - hA.eigenvalues i)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hp.det_pos.ne')
  change IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det
  rw [hd]
  exact (Matrix.isUnit_iff_isUnit_det _).mp (hu.map U.toRingHom)

theorem cavity_spectral_transform (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hsum : ∑ a, ρ a = 1) (A A₀ : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (hA₀ : A₀.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (heig₀ : ∀ i, hA₀.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    cavityResolvent (A - A₀) (cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ x) =
      cavitySpectralMatrixPath ρ eig hρ hsum A hA x := by
  rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A₀ hA₀ a heig₀ hx,
    cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A hA a heig hx]
  exact cavityResolvent_spectral_transform A A₀ _
    (cavity_spectral_shift_isUnit ρ eig hρ hsum A₀ hA₀ a heig₀ hx)
    (cavity_spectral_shift_isUnit ρ eig hρ hsum A hA a heig hx)

lemma cavity_spectral_tilt_isUnit (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hsum : ∑ a, ρ a = 1) (A A₀ : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (hA₀ : A₀.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (heig₀ : ∀ i, hA₀.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    IsUnit (1 - cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ x * (A - A₀)).det := by
  let b := finiteInverse ρ eig hρ hsum x
  let D₀ := b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀
  let D := b • (1 : Matrix (Fin d) (Fin d) ℝ) - A
  have h₀ : IsUnit D₀.det := cavity_spectral_shift_isUnit ρ eig hρ hsum A₀ hA₀ a heig₀ hx
  have h : IsUnit D.det := cavity_spectral_shift_isUnit ρ eig hρ hsum A hA a heig hx
  rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A₀ hA₀ a heig₀ hx]
  change IsUnit (1 - D₀⁻¹ * (A - A₀)).det
  have he : 1 - D₀⁻¹ * (A - A₀) = D₀⁻¹ * D := by
    calc
      _ = D₀⁻¹ * D₀ - D₀⁻¹ * (A - A₀) := by rw [Matrix.nonsing_inv_mul _ h₀]
      _ = _ := by dsimp only [D, D₀]; noncomm_ring
  rw [he, Matrix.det_mul]
  exact (Matrix.isUnit_nonsing_inv_det_iff.mpr h₀).mul h

theorem cavity_spectral_root_transform (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hsum : ∑ a, ρ a = 1) (A A₀ : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (hA₀ : A₀.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (heig₀ : ∀ i, hA₀.eigenvalues i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    let H := cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀
    (1 - H x * (A - A₀))⁻¹ * cavitySpectralMatrixDensity ρ eig hρ hsum A₀ hA₀ x *
      ((1 - H x * (A - A₀))⁻¹).transpose =
        cavitySpectralMatrixDensity ρ eig hρ hsum A hA x := by
  intro H
  have hK : (A - A₀).transpose = A - A₀ := by
    rw [Matrix.transpose_sub, Matrix.isHermitian_iff_isSymm.mp hA,
      Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hH : (H x).transpose = H x := by
    dsimp only [H]
    rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A₀ hA₀ a heig₀ hx,
      Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hd := hasDerivAt_cavityResolvent (A - A₀) H
    (cavitySpectralMatrixDensity ρ eig hρ hsum A₀ hA₀ x) x hK hH
    (hasDerivAt_cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ a heig₀ hx)
    (cavity_spectral_tilt_isUnit ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀ hx)
  have he : (fun t => cavityResolvent (A - A₀) (H t)) =ᶠ[𝓝 x]
      cavitySpectralMatrixPath ρ eig hρ hsum A hA := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact cavity_spectral_transform ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀ ht
  exact (hd.congr_of_eventuallyEq he.symm).unique
    (hasDerivAt_cavitySpectralMatrixPath ρ eig hρ hsum A hA a heig hx)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bound on the covariance in the actual quadratic Gibbs marginal.
The innovation covariances are identified from their defining increments;
their sum is controlled by the overlap partition, not by its number of cells. -/

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_spectral_total_covariance_bound {ι : Type*} [Fintype ι] {d n : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A A₀ : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (hA₀ : A₀.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (heig₀ : ∀ i, hA₀.eigenvalues i ≤ eig a)
    (q x b : ℕ → ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hq : Monotone q) (hq0 : 0 ≤ q 0) (hx : ∀ i ≤ n, 0 < x i)
    (hb : ∀ i < n, 0 < b i)
    (hgap : ∀ i < n, x i - x (i + 1) = b i * (q (i + 1) - q i))
    (hlast : x n = 1 - q n)
    (hΔ : ∀ i < n,
      cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i) -
        cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x (i + 1)) = b i • S i) :
    let K := A - A₀
    let H := fun i => cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i)
    let S₀ := q 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A₀ hA₀ (x 0)
    ‖((1 - H 0 * K)⁻¹ * S₀ * ((1 - H 0 * K)⁻¹).transpose) +
      ((∑ i : Fin n, (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) +
        cavityResolvent K (H n))‖ ≤ (ρ a)⁻¹ := by
  intro K H S₀
  let T := cavitySpectralMatrixPath ρ eig hρ hsum A hA
  have hK : K.transpose = K := by
    dsimp only [K]
    rw [Matrix.transpose_sub, Matrix.isHermitian_iff_isSymm.mp hA,
      Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hH (i : ℕ) (hi : i ≤ n) : (H i).transpose = H i := by
    dsimp only [H]
    rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A₀ hA₀ a heig₀ (hx i hi),
      Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hdet (i : ℕ) (hi : i ≤ n) : IsUnit (1 - H i * K).det :=
    cavity_spectral_tilt_isUnit ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀ (hx i hi)
  have htransform (i : ℕ) (hi : i ≤ n) : cavityResolvent K (H i) = T (x i) :=
    cavity_spectral_transform ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀ (hx i hi)
  have hroot : (1 - H 0 * K)⁻¹ * S₀ * ((1 - H 0 * K)⁻¹).transpose =
      q 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A hA (x 0) := by
    dsimp only [S₀]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    exact cavity_spectral_root_transform ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀
      (hx 0 (Nat.zero_le n))
  have hstep (i : Fin n) :
      (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose =
        (b i)⁻¹ • (T (x i) - T (x (i + 1))) := by
    have he := cavity_innovation_covariance_mul K (H i) (H (i + 1)) (S i) (b i)
      hK (hH (i + 1) (by omega)) (hdet i (by omega)) (hdet (i + 1) (by omega))
      (hΔ i i.isLt)
    rw [htransform i (by omega), htransform (i + 1) (by omega)] at he
    rw [← he, smul_smul, inv_mul_cancel₀ (hb i i.isLt).ne', one_smul]
  rw [hroot, htransform n le_rfl]
  simp_rw [hstep]
  rw [← add_assoc]
  exact cavity_spectral_covariance_partition_bound ρ eig hρ hsum A hA a heig
    (fun i : Fin (n + 1) => q i) (fun i : Fin (n + 1) => x i)
    (fun i : Fin n => b i) (fun _ _ hij => hq hij) hq0
    (fun i => (hx i (by omega)).le) (hx 0 (Nat.zero_le n))
    (fun i => hb i i.isLt) (fun i => hgap i i.isLt) hlast

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinLinearMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining linear/spin tilt preserves uniform Gaussian radial moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_independent_spin_marginal {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {d k : ℕ}
    (P : Measure Ω) (κ : Kernel Ω X) [IsMarkovKernel κ]
    (Y : X → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    ((κ ×ₖ Kernel.const Ω π) ∘ₘ P).map (fun x => Y x.1) = (κ ∘ₘ P).map Y := by
  change ((κ ×ₖ Kernel.const Ω π) ∘ₘ P).map (Y ∘ Prod.fst) = _
  rw [← Measure.map_map hY measurable_fst, Measure.map_comp P _ measurable_fst]
  rw [← Kernel.fst_eq, Kernel.fst_prod]

theorem cavity_spin_linear_tilt_gaussian_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {d k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω X) [IsMarkovKernel κ]
    (Y : X → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hLaw : (κ ∘ₘ P).map Y = multivariateGaussian 0 S)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    {M : ℝ} (hSM : ‖S‖ ≤ M) (p : ℕ) :
    let ν := κ ×ₖ Kernel.const Ω π
    let V := fun x : X × Spin k => cavityLogFactor 0 L C (Y x.1) x.2
    (∀ᵐ ω ∂P, Integrable (fun x => Real.exp (V x)) (ν ω) ∧
      Integrable (fun x => ‖Y x.1‖^p) ((ν ω).tilted V)) ∧
    Integrable (fun ω => ∫ x, ‖Y x.1‖^p ∂(ν ω).tilted V) P ∧
    (∫ ω, ∫ x, ‖Y x.1‖^p ∂(ν ω).tilted V ∂P) ≤
      cavityGaussianLinearMomentBound d p (cavityMatrixMass L + cavityMatrixMass C) M := by
  intro ν V
  have hv : Measurable V := by
    unfold V cavityLogFactor cavityQuadratic
    have hy : ∀ i, Measurable (fun x : X × Spin k => Y x.1 i) :=
      fun i => (EuclideanSpace.proj i).measurable.comp (hY.comp measurable_fst)
    have he : ∀ i, Measurable (fun x : X × Spin k => spinValue (x.2 i)) := by
      intro i
      exact (measurable_of_countable (spinValue : Bool → ℝ)).comp
        ((measurable_pi_apply i).comp measurable_snd)
    fun_prop
  exact cavity_linear_tilt_gaussian_moment P ν (fun x => V x.2) (fun x => Y x.1)
    (hv.comp measurable_snd) (hY.comp measurable_fst) S hS
    ((cavity_independent_spin_marginal P κ Y hY π).trans hLaw) hSM
    (add_nonneg (cavityMatrixMass_nonneg L) (cavityMatrixMass_nonneg C)) p
    (fun _ x => cavity_linear_logFactor_growth L C (Y x.1) x.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRootedPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform radial moments for the actual spectral quadratic cavity law,
after its remaining spin-linear tilt. No Gaussian marginal or norm bound
is assumed: both are derived from the spectral data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_rooted_spectral_linear_moment_oai {ι : Type*} [Fintype ι] {d k n : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A A₀ : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (hA₀ : A₀.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (heig₀ : ∀ i, hA₀.eigenvalues i ≤ eig a)
    (q x b : ℕ → ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hq : Monotone q) (hq0 : 0 ≤ q 0) (hx : ∀ i, 0 < x i)
    (hbCascade : CascadeExponents n b) (hb : ∀ i, 0 < b i)
    (hgap : ∀ i < n, x i - x (i + 1) = b i * (q (i + 1) - q i))
    (hlast : x n = 1 - q n)
    (hS : ∀ i, (S i).PosSemidef)
    (hΔ : ∀ i,
      cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i) -
        cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x (i + 1)) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic (A - A₀)
        (cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x (i + 1))))
      (CFC.sqrt (S i))).PosDef)
    (hR : (cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x n)).PosSemidef)
    (hQR : (cavityFactorPrecision (A - A₀)
      (CFC.sqrt (cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x n)))).PosDef)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ) (p : ℕ) :
    let K := A - A₀
    let H := fun i => cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i)
    let S₀ := q 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A₀ hA₀ (x 0)
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)
    let κ := cavityRootedResidualKernel n K (H n)
    let ν := κ ×ₖ Kernel.const _ π
    let V := fun z => cavityLogFactor 0 L C (cavityRootedField n z.1) z.2
    (∀ᵐ ω ∂P, Integrable (fun z => Real.exp (V z)) (ν ω) ∧
      Integrable (fun z => ‖cavityRootedField n z.1‖^p) ((ν ω).tilted V)) ∧
    Integrable (fun ω => ∫ z, ‖cavityRootedField n z.1‖^p ∂(ν ω).tilted V) P ∧
    (∫ ω, ∫ z, ‖cavityRootedField n z.1‖^p ∂(ν ω).tilted V ∂P) ≤
      cavityGaussianLinearMomentBound d p (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ := by
  intro K H S₀ P κ ν V
  let J := fun i => (1 - H i * K)⁻¹
  let Sfull := J 0 * S₀ * (J 0).transpose +
    ((∑ i : Fin n, J i * S i * (J (i + 1)).transpose) + cavityResolvent K (H n))
  have hS₀ : S₀.PosSemidef :=
    (cavitySpectralMatrixDensity_posSemidef ρ eig hρ hsum A₀ hA₀ a heig₀ (hx 0)).smul hq0
  have hK : K.transpose = K := by
    dsimp only [K]
    rw [Matrix.transpose_sub, Matrix.isHermitian_iff_isSymm.mp hA,
      Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hH (i : ℕ) : (H i).transpose = H i := by
    dsimp only [H]
    rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A₀ hA₀ a heig₀ (hx i),
      Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hdet (i : ℕ) : IsUnit (1 - H i * K).det :=
    cavity_spectral_tilt_isUnit ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀ (hx i)
  have hSfull : Sfull.PosSemidef := by
    apply Matrix.PosSemidef.add
    · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hS₀.mul_mul_conjTranspose_same (J 0)
    · exact (Matrix.posSemidef_sum Finset.univ (fun (i : Fin n) _ =>
        cavity_innovation_covariance_posSemidef K (H i) (H (i + 1)) (S i) (hS i)
          (b i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i))).add
            (cavity_tilt_covariance_posSemidef K (H n) hR hQR)
  have hnorm : ‖Sfull‖ ≤ (ρ a)⁻¹ :=
    cavity_spectral_total_covariance_bound ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀
      q x b S hq hq0 (fun i _ => hx i) (fun i _ => hb i) hgap hlast (fun i _ => hΔ i)
  have hlaw : (κ ∘ₘ P).map (cavityRootedField n) = multivariateGaussian 0 Sfull :=
    cavity_rooted_quadratic_gaussian n K H S b S₀ hS₀ hbCascade hK hH hS hb hdet hΔ hQ hR hQR
  exact cavity_spin_linear_tilt_gaussian_moment P κ (cavityRootedField n)
    (measurable_cavityRootedField n) π Sfull hSfull hlaw L C hnorm p

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.cavity_rooted_spectral_linear_moment_oai.{u_1} := @OAI.InvariantIsing.cavity_rooted_spectral_linear_moment_oai.{u_1}
