-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_finite_spin_test
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:34:17.86204+00:00
-- url     : https://prove2.me/submissions/ad2b692e-1f5e-42c9-a266-d180e401dc4d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_cavityFiniteLevel_monotone
import Theorems.Thm_OAI_InvariantIsing_cavity_full_spin_test_evaluation

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDeficitGap
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a gap in the finite overlap support, the deficit is affine with
slope equal to minus the mass below the gap. Endpoints may be atoms. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma deficit_antitone_argument (p : OverlapPath) : Antitone (deficit p) := by
  intro a b hab
  rw [deficit_eq_integral, deficit_eq_integral]
  apply integral_mono (p.integrable_complement_max b) (p.integrable_complement_max a)
  intro s
  exact sub_le_sub_left (max_le_max_left (p s) hab) 1

lemma deficit_lower_of_ae_le (p : OverlapPath) {M r : ℝ}
    (hM : ∀ᵐ s ∂pathMeasure, p s ≤ M) (hr : r ≤ M) :
    1 - M ≤ deficit p r := by
  rw [deficit_eq_integral]
  calc
    1 - M = ∫ _s : ℝ, (1 - M) ∂pathMeasure := by simp
    _ ≤ ∫ s, 1 - max (p s) r ∂pathMeasure := by
      apply integral_mono_ae (integrable_const _) (p.integrable_complement_max r)
      filter_upwards [hM] with s hs
      exact sub_le_sub_left (max_le hs hr) 1

lemma deficit_constant_below_ae_lower (p : OverlapPath) {a r : ℝ}
    (ha : ∀ᵐ s ∂pathMeasure, a ≤ p s) (hr : r ≤ a) :
    deficit p r = deficit p a := by
  rw [deficit_eq_integral, deficit_eq_integral]
  apply integral_congr_ae
  filter_upwards [ha] with s hs
  rw [max_eq_left (hr.trans hs), max_eq_left hs]

theorem deficit_affine_on_gap (p : OverlapPath) {a b : ℝ}
    (hgap : ∀ᵐ s ∂pathMeasure, p s ≤ a ∨ b ≤ p s)
    {r : ℝ} (hr : r ∈ Icc a b) :
    deficit p r = deficit p a - pathMeasure.real {s | p s ≤ a} * (r - a) := by
  let A : Set ℝ := {s | p s ≤ a}
  have hA : MeasurableSet A := measurableSet_le p.measurable measurable_const
  have he : (fun s => (1 - max (p s) r) - (1 - max (p s) a)) =ᵐ[pathMeasure]
      A.indicator (fun _ => a - r) := by
    filter_upwards [hgap] with s hs
    by_cases hsa : p s ≤ a
    · rw [max_eq_right (hsa.trans hr.1), max_eq_right hsa,
        indicator_of_mem (show s ∈ A from hsa)]
      ring
    · have hbs : b ≤ p s := hs.resolve_left hsa
      rw [max_eq_left (hr.2.trans hbs), max_eq_left (hr.1.trans (hr.2.trans hbs)),
        indicator_of_notMem (show s ∉ A from hsa)]
      ring
  have hi : deficit p r - deficit p a = pathMeasure.real A * (a - r) := by
    rw [deficit_eq_integral, deficit_eq_integral,
      ← integral_sub (p.integrable_complement_max r) (p.integrable_complement_max a),
      integral_congr_ae he, integral_indicator_const (a - r) hA]
    rfl
  change deficit p r = deficit p a - pathMeasure.real A * (r - a)
  linarith

theorem hasDerivAt_deficit_on_gap (p : OverlapPath) {a b r : ℝ}
    (hgap : ∀ᵐ s ∂pathMeasure, p s ≤ a ∨ b ≤ p s) (hr : r ∈ Ioo a b) :
    HasDerivAt (deficit p) (-pathMeasure.real {s | p s ≤ a}) r := by
  have hd : HasDerivAt
      (fun t => deficit p a - pathMeasure.real {s | p s ≤ a} * (t - a))
      (-pathMeasure.real {s | p s ≤ a}) r := by
    convert! (((hasDerivAt_id r).sub_const a).const_mul
      (pathMeasure.real {s | p s ≤ a})).const_sub (deficit p a) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
  exact deficit_affine_on_gap p hgap ⟨ht.1.le, ht.2.le⟩

end InvariantIsing

end

end OAI
end

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

theorem cavity_quadratic_step_isUnit {d : ℕ} (K P C : Matrix (Fin d) (Fin d) ℝ)
    (hP : IsUnit (1 - P * K).det) (hC : IsUnit (1 - C * K).det) :
    IsUnit (1 - (P - C) * cavityBackwardQuadratic K C).det := by
  rw [cavity_quadratic_factor K P C hC, Matrix.det_mul]
  exact hP.mul (Matrix.isUnit_nonsing_inv_det _ hC)

theorem cavityBackwardQuadratic_transpose {d : ℕ}
    (K H : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K) (hH : H.transpose = H)
    (hHdet : IsUnit (1 - H * K).det) :
    (cavityBackwardQuadratic K H).transpose = cavityBackwardQuadratic K H := by
  have hKH : IsUnit (1 - K * H).det := by
    rwa [Matrix.det_one_sub_mul_comm]
  unfold cavityBackwardQuadratic
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hH, hK]
  exact cavityResolvent_pushThrough H K hKH

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square completion for an arbitrary positive definite real precision
matrix, expressed against the standard finite-dimensional Gaussian. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace InvariantIsing

lemma cavity_eigenbasis_action {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (i : Fin d) :
    Q.toEuclideanLin (hQ.eigenvectorBasis i) =
      hQ.eigenvalues i • hQ.eigenvectorBasis i := by
  ext j
  exact congrFun (hQ.mulVec_eigenvectorBasis i) j

lemma cavity_eigenbasis_coordinate {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    hQ.eigenvectorBasis.repr (Q.toEuclideanLin x) i =
      hQ.eigenvalues i * hQ.eigenvectorBasis.repr x i := by
  rw [hQ.eigenvectorBasis.repr_apply_apply, hQ.eigenvectorBasis.repr_apply_apply,
    ← Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ (hQ.eigenvectorBasis i) x,
    cavity_eigenbasis_action Q hQ i, real_inner_smul_left]

lemma cavity_eigenbasis_quadratic {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪x, Q.toEuclideanLin x⟫ =
      ∑ i, hQ.eigenvalues i * (hQ.eigenvectorBasis.repr x i) ^ 2 := by
  rw [← hQ.eigenvectorBasis.sum_inner_mul_inner x (Q.toEuclideanLin x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (hQ.eigenvectorBasis i) x, ← hQ.eigenvectorBasis.repr_apply_apply,
    ← hQ.eigenvectorBasis.repr_apply_apply, cavity_eigenbasis_coordinate]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPrecisionPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The affine precision homotopy in `cav:q-precision`.  Since the
eigenvectors of its fixed symmetric coefficient do not change, path
nonsingularity rules out eigenvalues at or above one directly. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_precision_eigenvalues_lt_one {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - t • M).det) (i : Fin d) :
    hM.eigenvalues i < 1 := by
  by_contra! hEig
  have hEigenPos : 0 < hM.eigenvalues i := lt_of_lt_of_le zero_lt_one hEig
  let t := (hM.eigenvalues i)⁻¹
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨(inv_pos.mpr hEigenPos).le, ?_⟩
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hEig
  have hz : (1 - t • M) *ᵥ (fun j => hM.eigenvectorBasis i j) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      hM.mulVec_eigenvectorBasis, smul_smul]
    simp [t, inv_mul_cancel₀ hEigenPos.ne']
  have hinj : Function.Injective (1 - t • M).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (hpath t ht))
  have hvzero : (fun j => hM.eigenvectorBasis i j) = 0 := by
    apply hinj
    simpa only [Matrix.mulVec_zero] using hz
  apply hM.eigenvectorBasis.orthonormal.ne_zero i
  ext j
  exact congrFun hvzero j

lemma cavity_precision_inner_pos {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (hEig : ∀ i, hM.eigenvalues i < 1)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ≠ 0) :
    0 < ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - M) x⟫ := by
  have he : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - M) x⟫ =
      ∑ i, (1 - hM.eigenvalues i) * (hM.eigenvectorBasis.repr x i) ^ 2 := by
    simp only [map_sub, map_one, sub_apply,
      one_apply_eq_self, inner_sub_right, real_inner_self_eq_norm_sq]
    have hq : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) M x⟫ =
        ∑ i, hM.eigenvalues i * (hM.eigenvectorBasis.repr x i) ^ 2 :=
      cavity_eigenbasis_quadratic M hM x
    rw [hq]
    have hn : ‖x‖ ^ 2 = ∑ i, (hM.eigenvectorBasis.repr x i) ^ 2 := by
      simpa only [hM.eigenvectorBasis.repr_apply_apply] using
        (hM.eigenvectorBasis.sum_sq_inner_right x).symm
    rw [hn, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  obtain ⟨i, hi⟩ : ∃ i, hM.eigenvectorBasis.repr x i ≠ 0 := by
    by_contra! h
    apply hx
    apply hM.eigenvectorBasis.repr.injective
    ext i
    simpa only [map_zero, PiLp.zero_apply] using h i
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (sub_pos.mpr (hEig j)).le (sq_nonneg _)
  · exact ⟨i, Finset.mem_univ i, mul_pos (sub_pos.mpr (hEig i)) (sq_pos_of_ne_zero hi)⟩

/-- The source's precision-continuation argument specialized to its actual
affine path. No continuity-of-eigenvalues input is needed. -/
theorem cavity_precision_posDef_of_path {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - t • M).det) :
    (1 - M).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨Matrix.isHermitian_one.sub hM, ?_⟩
  intro v hv
  have hx : WithLp.toLp 2 v ≠ (0 : EuclideanSpace ℝ (Fin d)) := by
    intro h
    apply hv
    ext i
    exact congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) h
  have hp := cavity_precision_inner_pos M hM
    (cavity_precision_eigenvalues_lt_one M hM hpath) (WithLp.toLp 2 v) hx
  simpa only [Matrix.inner_toEuclideanCLM, PiLp.toLp_apply, star_trivial] using hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDiagonalGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-gap comparison for the diagonal covariances in the
finite-alphabet cavity recursion. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavity_diagonal_inverse_gap {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (p s : Fin d → ℝ) (hs : ∀ i, 0 < s i) (hsp : ∀ i, s i ≤ p i)
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef) :
    (Matrix.diagonal (fun i => (s i)⁻¹) - K).PosDef := by
  have hd : (Matrix.diagonal (fun i => (s i)⁻¹ - (p i)⁻¹)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    apply sub_nonneg.mpr
    simpa only [one_div] using one_div_le_one_div_of_le (hs i) (hsp i)
  have he : Matrix.diagonal (fun i => (s i)⁻¹) - K =
      (Matrix.diagonal (fun i => (p i)⁻¹) - K) +
        Matrix.diagonal (fun i => (s i)⁻¹ - (p i)⁻¹) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [he]
  exact hgap.add_posSemidef hd

lemma cavity_diagonal_gap_isUnit {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (p s : Fin d → ℝ) (hs : ∀ i, 0 < s i) (hsp : ∀ i, s i ≤ p i)
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef) :
    IsUnit (1 - Matrix.diagonal s * K).det := by
  have hg := cavity_diagonal_inverse_gap K p s hs hsp hgap
  have he : 1 - Matrix.diagonal s * K =
      Matrix.diagonal s * (Matrix.diagonal (fun i => (s i)⁻¹) - K) := by
    rw [mul_sub, Matrix.diagonal_mul_diagonal]
    have hone : Matrix.diagonal (fun i => s i * (s i)⁻¹) = 1 := by
      simp [funext fun i => mul_inv_cancel₀ (hs i).ne']
    rw [hone]
  rw [he, Matrix.det_mul]
  apply IsUnit.mul
  · exact isUnit_iff_ne_zero.mpr (Matrix.PosDef.diagonal hs).det_pos.ne'
  · exact isUnit_iff_ne_zero.mpr hg.det_pos.ne'

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStepPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Precision positivity for a finite-alphabet covariance step.  The
upper covariance is positive diagonal; the lower one is either positive
diagonal or zero, as at the terminal endpoint of the cavity recursion. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavity_diagonal_interpolation_isUnit {d : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (p c : Fin d → ℝ)
    (hp : ∀ i, 0 < p i) (hc0 : ∀ i, 0 ≤ c i) (hcp : ∀ i, c i ≤ p i)
    (hc : (∀ i, c i = 0) ∨ (∀ i, 0 < c i))
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsUnit (1 - Matrix.diagonal (fun i => c i + t * (p i - c i)) * K).det := by
  by_cases ht0 : t = 0
  · subst t
    simp only [zero_mul, add_zero]
    rcases hc with hc | hc
    · have hz : c = 0 := funext hc
      simp [hz]
    · exact cavity_diagonal_gap_isUnit K p c hc hcp hgap
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  apply cavity_diagonal_gap_isUnit K p _ _ _ hgap
  · intro i
    have hpi := hp i
    have hci := hc0 i
    nlinarith [mul_pos htpos hpi, mul_nonneg (sub_nonneg.mpr ht.2) hci]
  · intro i
    have hi := hcp i
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hi)]

/-- Positivity of `I-Bᵀ K_i B` from the actual diagonal covariance
ordering and the upper spectral gap.  `B Bᵀ = P-C` may be singular. -/
theorem cavity_step_precision_posDef {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K)
    (p c : Fin d → ℝ) (hp : ∀ i, 0 < p i) (hc0 : ∀ i, 0 ≤ c i)
    (hcp : ∀ i, c i ≤ p i) (hc : (∀ i, c i = 0) ∨ (∀ i, 0 < c i))
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef)
    (hB : Matrix.diagonal p - Matrix.diagonal c = B * B.transpose) :
    (cavityFactorPrecision (cavityBackwardQuadratic K (Matrix.diagonal c)) B).PosDef := by
  let P := Matrix.diagonal p
  let C := Matrix.diagonal c
  let L := cavityBackwardQuadratic K C
  have hC : IsUnit (1 - C * K).det := by
    simpa only [C, zero_mul, add_zero] using
      cavity_diagonal_interpolation_isUnit K p c hp hc0 hcp hc hgap 0 (by constructor <;> norm_num)
  have hL : L.transpose = L := by
    exact cavityBackwardQuadratic_transpose K C hK (by simp [C]) hC
  have hM : (B.transpose * L * B).IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    change (B.transpose * L * B).transpose = B.transpose * L * B
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hL, mul_assoc]
  apply cavity_precision_posDef_of_path (B.transpose * L * B) hM
  intro t ht
  let S := C + t • (P - C)
  have hS : IsUnit (1 - S * K).det := by
    have he : S = Matrix.diagonal (fun i => c i + t * (p i - c i)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [S, C, P]
      · simp [S, C, P, Matrix.diagonal_apply_ne _ hij]
    rw [he]
    exact cavity_diagonal_interpolation_isUnit K p c hp hc0 hcp hc hgap t ht
  have hstep := cavity_quadratic_step_isUnit K S C hS hC
  have hSC : S - C = t • (P - C) := by dsimp only [S]; abel
  rw [hSC] at hstep
  have hdet : (1 - t • (B.transpose * L * B)).det =
      (1 - (t • (P - C)) * L).det := by
    calc
      _ = (1 - (t • (B.transpose * L)) * B).det := by rw [Matrix.smul_mul]
      _ = (1 - B * (t • (B.transpose * L))).det := Matrix.det_one_sub_mul_comm _ _
      _ = _ := by
        rw [Matrix.mul_smul, ← mul_assoc, ← hB, Matrix.smul_mul]
  rw [hdet]
  exact hstep

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaling the covariance step by its positive cascade exponent. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_scaled_sqrt_factor {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (ζ : ℝ) (hζ : 0 ≤ ζ) :
    (Real.sqrt ζ • CFC.sqrt S) * (Real.sqrt ζ • CFC.sqrt S).transpose = ζ • S := by
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt hζ, cavity_covariance_sqrt_factor S hS]

lemma cavity_scaled_factor_precision {d : ℕ}
    (K B : Matrix (Fin d) (Fin d) ℝ) (ζ : ℝ) (hζ : 0 ≤ ζ) :
    cavityFactorPrecision K (Real.sqrt ζ • B) = cavityFactorPrecision (ζ • K) B := by
  simp only [cavityFactorPrecision, Matrix.transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hζ]

/-- The exact precision required by the Gaussian law, obtained from the
diagonal covariance ordering, including zero covariance increments. -/
theorem cavity_scaled_step_precision {d : ℕ}
    (K S : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K)
    (hS : S.PosSemidef) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (p c : Fin d → ℝ) (hp : ∀ i, 0 < p i) (hc0 : ∀ i, 0 ≤ c i)
    (hcp : ∀ i, c i ≤ p i) (hc : (∀ i, c i = 0) ∨ (∀ i, 0 < c i))
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef)
    (hΔ : Matrix.diagonal p - Matrix.diagonal c = ζ • S) :
    (cavityFactorPrecision (ζ • cavityBackwardQuadratic K (Matrix.diagonal c))
      (CFC.sqrt S)).PosDef := by
  rw [← cavity_scaled_factor_precision _ _ ζ hζ]
  apply cavity_step_precision_posDef K (Real.sqrt ζ • CFC.sqrt S) hK
    p c hp hc0 hcp hc hgap
  rw [cavity_scaled_sqrt_factor S hS ζ hζ]
  exact hΔ

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The upper spectral gap supplies the diagonal inverse-gap hypothesis
used by the quadratic cavity recursion. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavity_upper_spectral_gap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (L b : ℝ) (hA : (L • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    (hb : L < b) : (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosDef := by
  have hp : ((b - L) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
    Matrix.PosDef.one.smul (sub_pos.mpr hb)
  have he : b • (1 : Matrix (Fin d) (Fin d) ℝ) - A =
      (b - L) • (1 : Matrix (Fin d) (Fin d) ℝ) + (L • 1 - A) := by module
  rw [he]
  exact hp.add_posSemidef hA

lemma cavity_resolvent_diagonal_gap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (eig : Fin d → ℝ) (L b : ℝ)
    (hA : (L • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef) (hb : L < b) :
    (Matrix.diagonal (fun i => (((b - eig i)⁻¹)⁻¹)) -
      (A - Matrix.diagonal eig)).PosDef := by
  have he : Matrix.diagonal (fun i => (((b - eig i)⁻¹)⁻¹)) -
      (A - Matrix.diagonal eig) = b • (1 : Matrix (Fin d) (Fin d) ℝ) - A := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [inv_inv, Matrix.sub_apply, Matrix.diagonal_apply_eq,
        Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      ring
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [he]
  exact cavity_upper_spectral_gap A L b hA hb

/-- The residual endpoint has lower covariance zero. -/
theorem cavity_resolvent_terminal_precision {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) (eig : Fin d → ℝ) (L b : ℝ)
    (hK : (A - Matrix.diagonal eig).transpose = A - Matrix.diagonal eig)
    (hA : (L • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    (heig : ∀ i, eig i ≤ L) (hb : L < b)
    (hB : Matrix.diagonal (fun i => (b - eig i)⁻¹) = B * B.transpose) :
    (cavityFactorPrecision (A - Matrix.diagonal eig) B).PosDef := by
  have hp : ∀ i, 0 < (b - eig i)⁻¹ := fun i =>
    inv_pos.mpr (sub_pos.mpr (lt_of_le_of_lt (heig i) hb))
  have h := cavity_step_precision_posDef (A - Matrix.diagonal eig) B hK
    (fun i => (b - eig i)⁻¹) (fun _ => 0) hp (by intro i; exact le_rfl)
    (by intro i; exact (hp i).le) (Or.inl (by intro i; rfl))
    (cavity_resolvent_diagonal_gap A eig L b hA hb) (by simpa using hB)
  simpa only [Matrix.diagonal_zero, cavityBackwardQuadratic_zero] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Differentiation of the finite spectral inverse. The inverse function
theorem is applied to the already constructed inverse; no regularity of
that inverse is assumed.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem hasStrictDerivAt_finiteInverseDerivative (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt
      (fun y => -1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum y))
      (2 * finiteThirdResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) /
        finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) ^ 3) x := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hpos := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  have hb := hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx
  have hm := (hasStrictDerivAt_finiteSecondResolvent ρ eig hs.1).comp x hb
  convert (hasStrictDerivAt_const x (-1 : ℝ)).fun_div hm hpos.ne' using 1
  all_goals first | rfl | (simp only [Function.comp_apply]; field_simp [hpos.ne']; ring) | (field_simp [hpos.ne']; ring)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous nonnegative right derivative of the finite spectral
R-transform. Its extension at zero is the spectral variance; the constant
extension of `finiteR` to negative arguments is not differentiated there. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem cavityRDerivative_eq_deriv (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) {x : ℝ} (hx : 0 < x) :
    cavityRDerivative rho lam hrho hsum x = deriv (finiteR rho lam hrho hsum) x := by
  let b := finiteInverse rho lam hrho hsum x
  let M := finiteSecondResolvent rho lam b
  have hspec := finiteInverse_spec rho lam hrho hsum hx
  have hM : M ≠ 0 := (finiteSecondResolvent_pos (fun a => (hrho a).le) hsum hspec.1).ne'
  have hgap (a : ι) : b - lam a ≠ 0 := (sub_pos.mpr (hspec.1 a)).ne'
  have hterm (a : ι) : projectedResolventDerivative rho lam hrho hsum a x *
      (lam a - finiteR rho lam hrho hsum x) ^ 2 =
        ((rho a / (b - lam a) ^ 2) / x ^ 2 -
          (2 / x) * (rho a / (b - lam a)) + rho a) / M := by
    simp only [projectedResolventDerivative, finiteR, ite_eq_left hx]
    change rho a / (M * (b - lam a) ^ 2) * (lam a - (b - 1 / x)) ^ 2 = _
    field_simp [hM, hgap a, hx.ne']
    ring
  calc
    cavityRDerivative rho lam hrho hsum x =
        (M / x ^ 2 - (2 / x) * x + 1) / M := by
      unfold cavityRDerivative
      simp_rw [hterm]
      rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_div, ← Finset.mul_sum, hsum]
      change (M / x ^ 2 - (2 / x) * finiteResolvent rho lam b + 1) / M = _
      rw [hspec.2]
    _ = -1 / M + 1 / x ^ 2 := by field_simp [hM, hx.ne'] <;> ring
    _ = deriv (finiteR rho lam hrho hsum) x :=
      (hasStrictDerivAt_finiteR rho lam hrho hsum hx).hasDerivAt.deriv.symm

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
-- module Solutions.OAIQ258_II.IsingPerceptron_ArrayGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Geometry. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace IsingPerceptron

lemma unitUniform_Iic {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    unitUniform (Iic a) = ENNReal.ofReal a := by
  rw [unitUniform,Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume)),
    Measure.restrict_apply measurableSet_Iic,inter_comm,Set.Ioc_inter_Iic]
  simp only [inf_eq_right.mpr ha.2,Real.volume_Ioc,sub_zero]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MomentLogLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moment Log Limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Polynomial





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finite_partition_cell {k : ℕ} (ζ : Fin (k+1) → ℝ)
    {s : ℝ} (hs0 : ζ 0 ≤ s) (hs1 : s < ζ (Fin.last k)) :
    ∃ i : Fin k, ζ i.castSucc ≤ s ∧ s < ζ i.succ := by
  classical
  let T := Finset.univ.filter (fun i => s < ζ i)
  have hT : T.Nonempty := ⟨Fin.last k,by simp [T,hs1]⟩
  let d := T.min' hT
  have hd : s < ζ d := (Finset.mem_filter.mp (Finset.min'_mem T hT)).2
  have hd0 : 0 < d.val := by
    by_contra h
    have he : d=0 := Fin.ext (by change d.val=0; omega)
    rw [he] at hd
    linarith
  let i : Fin k := ⟨d.val-1,by have := d.isLt; omega⟩
  have he : i.succ=d := Fin.ext (by dsimp [i]; omega)
  refine ⟨i,?_,by simpa only [he] using hd⟩
  by_contra! h
  have hm : i.castSucc∈T := by simp [T,h]
  have H := Finset.min'_le T i.castSucc hm
  change d.val ≤ i.val at H
  dsimp [i] at H
  omega

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralStack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity column stack formed from square roots of spectral
compressions. Its columns are orthonormal when the compressions sum to
the identity, and it has the required deterministic limit. -/

noncomputable section
open Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_sqrt_scalar_identity {n : ℕ} (ρ : ℝ) (hρ : 0 ≤ ρ) :
    CFC.sqrt (ρ • (1 : Matrix (Fin n) (Fin n) ℝ)) = Real.sqrt ρ • 1 := by
  apply CFC.sqrt_unique
    (hb := (Matrix.PosSemidef.one.smul (Real.sqrt_nonneg ρ)).nonneg)
  rw [smul_mul_smul_comm, Matrix.one_mul, Real.mul_self_sqrt hρ]

theorem cavitySpectralStack_gram {m n : ℕ}
    (M : Fin m → Matrix (Fin n) (Fin n) ℝ) (hM : ∀ a, (M a).PosSemidef) :
    (cavitySpectralStack M).transpose * cavitySpectralStack M = ∑ a, M a := by
  ext i j
  change (∑ k : Fin (m * n),
      CFC.sqrt (M (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 i *
      CFC.sqrt (M (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 j) = _
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  have hs : (CFC.sqrt (M a)).transpose = CFC.sqrt (M a) :=
    Matrix.isHermitian_iff_isSymm.mp
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M a))).isHermitian
  have he := CFC.sqrt_mul_sqrt_self (M a) (hM a).nonneg
  have he' : (CFC.sqrt (M a)).transpose * CFC.sqrt (M a) = M a := by
    rw [hs, he]
  have hentry := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) he'
  exact hentry

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectedInnovation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Schur field identity identifies the covariance of each projected
quadratic innovation with a scalar increment. This is the finite matrix
step in the identification of the cavity field path. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal

namespace InvariantIsing

theorem cavity_projected_resolvent_difference {d n : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C₀ : Matrix (Fin n) (Fin n) ℝ) (rP rC : ℝ)
    (hP : C₀ + L.transpose * cavityResolvent K P * L = rP • 1)
    (hC : C₀ + L.transpose * cavityResolvent K C * L = rC • 1) :
    L.transpose * (cavityResolvent K P - cavityResolvent K C) * L =
      (rP - rC) • 1 := by
  calc
    _ = L.transpose * cavityResolvent K P * L -
        L.transpose * cavityResolvent K C * L := by rw [Matrix.mul_sub, Matrix.sub_mul]
    _ = (C₀ + L.transpose * cavityResolvent K P * L) -
        (C₀ + L.transpose * cavityResolvent K C * L) := by abel
    _ = (rP - rC) • 1 := by rw [hP, hC, sub_smul]

/-- The independent innovation covariance from `cav:q-innovations`,
after projection to the cavity sites, is a scalar resolvent difference. -/
theorem cavity_projected_innovation_covariance {d n : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C₀ : Matrix (Fin n) (Fin n) ℝ) (rP rC ζ : ℝ) (hζ : ζ ≠ 0)
    (hK : K.transpose = K) (hCsym : C.transpose = C)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hP : C₀ + L.transpose * cavityResolvent K P * L = rP • 1)
    (hC : C₀ + L.transpose * cavityResolvent K C * L = rC • 1) :
    L.transpose * ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) * L =
      ((rP - rC) / ζ) • 1 := by
  have hcov : (1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose =
      ζ⁻¹ • (cavityResolvent K P - cavityResolvent K C) := by
    rw [← cavity_innovation_covariance_mul K P C S ζ hK hCsym hPdet hCdet hΔ,
      smul_smul, inv_mul_cancel₀ hζ, one_smul]
  rw [hcov, Matrix.mul_smul, Matrix.smul_mul,
    cavity_projected_resolvent_difference K P C L C₀ rP rC hP hC, smul_smul]
  congr 1
  ring

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

/-- Differentiating the scalar Schur field identifies the projected
common-root covariance. The local scalar identity is supplied by the
proved finite spectral Schur evaluation. -/
theorem cavity_projected_root_covariance {d n : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (H' : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C₀ : Matrix (Fin n) (Fin n) ℝ) (R : ℝ → ℝ) (R' x : ℝ)
    (hK : K.transpose = K) (hHx : (H x).transpose = H x)
    (hH : HasDerivAt H H' x) (hdet : IsUnit (1 - H x * K).det)
    (hR : HasDerivAt R R' x)
    (hscalar : (fun t => C₀ + L.transpose * cavityResolvent K (H t) * L) =ᶠ[𝓝 x]
      (fun t => R t • (1 : Matrix (Fin n) (Fin n) ℝ))) :
    L.transpose * ((1 - H x * K)⁻¹ * H' * ((1 - H x * K)⁻¹).transpose) * L =
      R' • 1 := by
  let P : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    { toFun := fun M => L.transpose * M * L
      map_add' := by intro M N; rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c M; simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  have hf := hasDerivAt_cavityResolvent K H H' x hK hHx hH hdet
  have hp := (P.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt x hf
  have hs := hp.const_add C₀
  have hr := hR.smul_const (1 : Matrix (Fin n) (Fin n) ℝ)
  have he := (hs.congr_of_eventuallyEq hscalar.symm).unique hr
  exact he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDiagonalSpectralPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precision assumptions in the rooted Gaussian calculation follow
from the actual upper spectral gap when the base matrix is diagonal. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma finiteInverse_antitone_pos {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    finiteInverse ρ eig hρ hsum x ≤ finiteInverse ρ eig hρ hsum y := by
  have hx := hy.trans_le hyx
  by_contra! h
  have hh := finiteResolvent_strictAnti (fun a => (hρ a).le) hsum
    (finiteInverse_spec ρ eig hρ hsum hy).1 h
  rw [(finiteInverse_spec ρ eig hρ hsum hx).2,
    (finiteInverse_spec ρ eig hρ hsum hy).2] at hh
  exact (not_lt_of_ge hyx) hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFieldIncrement
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar field increments prescribed by the quadratic cavity
calculation are exactly the integrals defining the manuscript field path. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma continuousAt_deriv_finiteR_pos (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (deriv (finiteR rho lam hrho hsum)) x := by
  have h1 := (hasStrictDerivAt_finiteInverseDerivative rho lam hrho hsum hx).hasDerivAt.continuousAt
  have h2 : ContinuousAt (fun y : ℝ => 1 / y ^ 2) x :=
    continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx.ne')
  apply (h1.add h2).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact (hasStrictDerivAt_finiteR rho lam hrho hsum hy).hasDerivAt.deriv

/-- Positive-level covariance increments; no assumption about endpoint
atoms is needed, only that the open interval is a gap in the support. -/
theorem integral_finiteR_deriv_deficit_gap (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) {a b : ℝ} (hab : a < b)
    (hgap : ∀ᵐ s ∂pathMeasure, p s ≤ a ∨ b ≤ p s)
    (hpos : 0 < deficit p b) (hmass : pathMeasure.real {s | p s ≤ a} ≠ 0) :
    (∫ r in a..b, deriv (finiteR rho lam hrho hsum) (deficit p r)) =
      (finiteR rho lam hrho hsum (deficit p a) -
        finiteR rho lam hrho hsum (deficit p b)) / pathMeasure.real {s | p s ≤ a} := by
  let R := finiteR rho lam hrho hsum
  let ζ := pathMeasure.real {s | p s ≤ a}
  have hp (r : ℝ) (hr : r ∈ Icc a b) : 0 < deficit p r :=
    hpos.trans_le (deficit_antitone_argument p hr.2)
  have hc : ContinuousOn (fun r => deriv R (deficit p r)) (Icc a b) := by
    intro r hr
    exact ((continuousAt_deriv_finiteR_pos rho lam hrho hsum (hp r hr)).comp
      (continuous_deficit p).continuousAt).continuousWithinAt
  have hi : IntervalIntegrable (fun r => deriv R (deficit p r)) volume a b :=
    ((uIcc_of_le hab.le).symm ▸ hc).intervalIntegrable
  have hcomp : ContinuousOn (fun r => R (deficit p r)) (Icc a b) := by
    intro r hr
    exact (((hasStrictDerivAt_finiteR rho lam hrho hsum (hp r hr)).hasDerivAt.continuousAt).comp
      (continuous_deficit p).continuousAt).continuousWithinAt
  have hd : ∀ r ∈ Ioo a b, HasDerivAt (fun r => R (deficit p r))
      ((-ζ) * deriv R (deficit p r)) r := by
    intro r hr
    have hR := (hasStrictDerivAt_finiteR rho lam hrho hsum
      (hp r ⟨hr.1.le, hr.2.le⟩)).hasDerivAt
    have hD := hasDerivAt_deficit_on_gap p hgap hr
    rw [← hR.deriv] at hR
    convert! hR.comp r hD using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [R, ζ]
    ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hcomp hd
    (hi.const_mul (-ζ))
  rw [intervalIntegral.integral_const_mul] at hf
  apply (eq_div_iff hmass).mpr
  change (∫ r in a..b, deriv R (deficit p r)) * ζ = R (deficit p a) - R (deficit p b)
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficit
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deficit and cumulative masses of a genuine finite overlap
quantile, with atoms retained at all cell values. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma ae_finite_overlap_cell {n : ℕ} (cut : Fin (n + 2) → ℝ)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1) :
    ∀ᵐ s ∂pathMeasure, ∃ j : Fin (n + 1), s ∈ Ioo (cut j.castSucc) (cut j.succ) := by
  let : NullSingletonClass pathMeasure := by unfold pathMeasure; infer_instance
  have hne : ∀ᵐ s ∂pathMeasure, ∀ j, s ≠ cut j :=
    ae_all_iff.mpr (fun j => Measure.ae_ne pathMeasure (cut j))
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hne] with s hs hns
  obtain ⟨j, hlo, hhi⟩ := IsingPerceptron.finite_partition_cell cut
    (by simpa only [hfirst] using hs.1.le) (by simpa only [hlast] using hs.2)
  exact ⟨j, lt_of_le_of_ne hlo (hns j.castSucc).symm, hhi⟩

lemma finite_overlap_ae_bounds {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0)
    (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j) :
    ∀ᵐ s ∂pathMeasure, q 0 ≤ p s ∧ p s ≤ q (Fin.last n) := by
  filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with s hs
  obtain ⟨j, hj⟩ := hs
  rw [hp j s hj]
  exact ⟨hq (Fin.zero_le _), hq (Fin.le_last _)⟩

lemma finite_overlap_deficit_pos {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0)
    (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) {r : ℝ} (hr : r ≤ q (Fin.last n)) :
    0 < deficit p r := by
  have hbound := (finite_overlap_ae_bounds p cut hfirst hlast q hq hp).mono (fun _ h => h.2)
  exact (sub_pos.mpr htop).trans_le (deficit_lower_of_ae_le p hbound hr)

theorem finite_overlap_cumulative_mass {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (j : Fin (n + 1)) :
    pathMeasure.real {s | p s ≤ q j} = cut j.succ := by
  have he : {s | p s ≤ q j} =ᵐ[pathMeasure] Iic (cut j.succ) := by
    filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with s hs
    obtain ⟨k, hk⟩ := hs
    apply propext
    change p s ≤ q j ↔ s ≤ cut j.succ
    rw [hp k s hk]
    by_cases hkj : k ≤ j
    · exact iff_of_true (hq.monotone hkj)
        (hk.2.le.trans (hcut.monotone (by simpa using hkj)))
    · have hjk : j < k := lt_of_not_ge hkj
      have hindex : j.succ ≤ k.castSucc := by
        change j.val + 1 ≤ k.val
        exact hjk
      exact iff_of_false (not_le.mpr (hq hjk))
        (not_le.mpr ((hcut.monotone hindex).trans_lt hk.1))
  have hb : cut j.succ ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← hfirst]
      exact hcut.monotone (Fin.zero_le _)
    · rw [← hlast]
      exact hcut.monotone (Fin.le_last _)
  rw [measureReal_def, measure_congr he]
  change (IsingPerceptron.unitUniform (Iic (cut j.succ))).toReal = cut j.succ
  rw [IsingPerceptron.unitUniform_Iic hb, ENNReal.toReal_ofReal hb.1]

theorem finite_overlap_value_gap {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0)
    (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (i : Fin n) :
    ∀ᵐ s ∂pathMeasure, p s ≤ q i.castSucc ∨ q i.succ ≤ p s := by
  filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with s hs
  obtain ⟨j, hj⟩ := hs
  rw [hp j s hj]
  by_cases hji : j ≤ i.castSucc
  · exact Or.inl (hq hji)
  · change ¬j.val ≤ i.val at hji
    exact Or.inr (hq (by change i.val + 1 ≤ j.val; omega))

/-- The actual finite-level deficit increment, including the atoms at
both neighboring overlap values. -/
theorem finite_overlap_deficit_increment {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (i : Fin n) {r : ℝ} (hr : r ∈ Icc (q i.castSucc) (q i.succ)) :
    deficit p r = deficit p (q i.castSucc) -
      cut i.succ.castSucc * (r - q i.castSucc) := by
  rw [deficit_affine_on_gap p
    (finite_overlap_value_gap p cut hfirst hlast q hq.monotone hp i) hr,
    finite_overlap_cumulative_mass p cut hcut hfirst hlast q hq hp i.castSucc]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the root and all positive-level field covariance
increments for the finite trial quantile used in the cavity argument. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finite_overlap_field_increment (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {n : ℕ} (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (i : Fin n) :
    (∫ r in q i.castSucc..q i.succ, deriv (finiteR rho lam hrho hsum) (deficit p r)) =
      (finiteR rho lam hrho hsum (deficit p (q i.castSucc)) -
        finiteR rho lam hrho hsum (deficit p (q i.succ))) / cut i.castSucc.succ := by
  have hmass := finite_overlap_cumulative_mass p cut hcut hfirst hlast q hq hp i.castSucc
  have hc : 0 < cut i.castSucc.succ := by
    rw [← hfirst]
    apply hcut
    exact Fin.succ_pos _
  have hm : pathMeasure.real {s | p s ≤ q i.castSucc} ≠ 0 := by
    rw [hmass]
    exact hc.ne'
  have h := integral_finiteR_deriv_deficit_gap rho lam hrho hsum p
    (hq (Fin.castSucc_lt_succ (i := i)))
    (finite_overlap_value_gap p cut hfirst hlast q hq.monotone hp i)
    (finite_overlap_deficit_pos p cut hfirst hlast q hq.monotone hp htop
      (hq.monotone (Fin.le_last _))) hm
  rwa [hmass] at h

theorem finite_overlap_field_root (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {n : ℕ} (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j) :
    (∫ r in 0..q 0, deriv (finiteR rho lam hrho hsum) (deficit p r)) =
      q 0 * deriv (finiteR rho lam hrho hsum) (deficit p (q 0)) := by
  have hbound := (finite_overlap_ae_bounds p cut hfirst hlast q hq hp).mono (fun _ h => h.1)
  have hq0 := (finite_overlap_value_mem_unit p cut hcut q hp 0).1
  calc
    _ = ∫ _r in 0..q 0, deriv (finiteR rho lam hrho hsum) (deficit p (q 0)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hq0
      intro r hr
      dsimp only
      rw [deficit_constant_below_ae_lower p hbound hr.2.le]
    _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFieldPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite field path reconstructed by the cavity covariance.
Its covariance density has the continuous right-derivative value at zero. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma cavityFieldPrimitive_sub (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) (a b : ℝ) :
    cavityFieldPrimitive rho lam hrho hsum p b - cavityFieldPrimitive rho lam hrho hsum p a =
      ∫ r in a..b, cavityFieldDensity rho lam hrho hsum p r := by
  have hc := continuous_cavityFieldDensity rho lam hrho hsum p
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a b)
  unfold cavityFieldPrimitive
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySchurEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Schur-complement evaluation in `cav:compression` and
`cav:scalar-field`. All block inverses are ordinary nonsingular inverses. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

private lemma cavity_block_inverse_bottom {d n : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin d) ℝ) (D : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det) (hM : IsUnit (Matrix.fromBlocks A B C D).det) :
    ((Matrix.fromBlocks A B C D)⁻¹).toBlocks₂₂ = (D - C * A⁻¹ * B)⁻¹ := by
  let := Matrix.invertibleOfIsUnitDet A hA
  let := Matrix.invertibleOfIsUnitDet (Matrix.fromBlocks A B C D) hM
  let := Matrix.invertibleOfFromBlocks₁₁Invertible A B C D
  simpa only [Matrix.invOf_eq_nonsing_inv, Matrix.toBlocks_fromBlocks₂₂] using
    congrArg Matrix.toBlocks₂₂ (Matrix.invOf_fromBlocks₁₁_eq A B C D)

lemma cavity_block_shift {d n : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (b : ℝ) :
    b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
        Matrix.fromBlocks A L L.transpose C =
      Matrix.fromBlocks (b • 1 - A) (-L) (-L.transpose) (b • 1 - C) := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.one_apply, Matrix.fromBlocks, Matrix.smul_apply]

/-- Compressing the full resolvent onto the cavity block gives the inverse
of the Schur complement; no commutation of the special blocks is needed. -/
theorem cavity_schur_resolvent_compression {d n : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (b : ℝ)
    (hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det)
    (hM : IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det) :
    ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C)⁻¹).toBlocks₂₂ =
        (b • 1 - C - L.transpose * (b • 1 - A)⁻¹ * L)⁻¹ := by
  rw [cavity_block_shift] at hM ⊢
  simpa only [Matrix.neg_mul, Matrix.mul_neg, neg_neg] using
    cavity_block_inverse_bottom (b • 1 - A) (-L) (-L.transpose) (b • 1 - C) hA hM

/-- The scalar compression `x I` forces the cavity field to be
`(b - 1/x) I`, the finite identity `cav:scalar-field`. -/
theorem cavity_schur_scalar_field {d n : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (b x : ℝ) (hx : x ≠ 0)
    (hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det)
    (hM : IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det)
    (hcompression : ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C)⁻¹).toBlocks₂₂ = x • 1) :
    C + L.transpose * (b • 1 - A)⁻¹ * L = (b - x⁻¹) • 1 := by
  let D := b • (1 : Matrix (Fin d) (Fin d) ℝ) - A
  let E := b • (1 : Matrix (Fin n) (Fin n) ℝ) - C
  let := Matrix.invertibleOfIsUnitDet D hA
  have hMD : IsUnit (Matrix.fromBlocks D (-L) (-L.transpose) E).det := by
    simpa only [D, E, cavity_block_shift] using hM
  let := Matrix.invertibleOfIsUnitDet (Matrix.fromBlocks D (-L) (-L.transpose) E) hMD
  let := Matrix.invertibleOfFromBlocks₁₁Invertible D (-L) (-L.transpose) E
  have hS : IsUnit (b • (1 : Matrix (Fin n) (Fin n) ℝ) - C -
      L.transpose * (b • 1 - A)⁻¹ * L).det := by
    simpa only [D, E, Matrix.invOf_eq_nonsing_inv, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg] using
        Matrix.isUnit_det_of_invertible (E - (-L.transpose) * ⅟D * (-L))
  let := Matrix.invertibleOfIsUnitDet _ hS
  have hi : (b • (1 : Matrix (Fin n) (Fin n) ℝ) - C -
      L.transpose * (b • 1 - A)⁻¹ * L)⁻¹ = x • 1 := by
    rw [← cavity_schur_resolvent_compression A L C b hA hM]
    exact hcompression
  have hscalar : (x • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = x⁻¹ • 1 := by
    apply Matrix.inv_eq_right_inv
    simp only [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ hx, one_smul]
  have hs := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹) hi
  rw [Matrix.inv_inv_of_invertible, hscalar] at hs
  rw [sub_smul]
  calc
    C + L.transpose * (b • 1 - A)⁻¹ * L =
        b • 1 - (b • 1 - C - L.transpose * (b • 1 - A)⁻¹ * L) := by abel
    _ = b • 1 - x⁻¹ • 1 := by rw [hs]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpecialBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The special/cavity block matrix and its continuous limit. -/

noncomputable section
open Filter
open scoped BigOperators Topology Matrix

namespace InvariantIsing

theorem cavityLimitingStack_gram {m n : ℕ} (ρ : Fin m → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) (hsum : ∑ a, ρ a = 1) :
    (cavityLimitingStack (n := n) ρ).transpose * cavityLimitingStack (n := n) ρ =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have he : cavityLimitingStack (n := n) ρ =
      cavitySpectralStack (fun a => ρ a • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    ext i j
    simp only [cavityLimitingStack, cavitySpectralStack,
      cavity_sqrt_scalar_identity _ (hρ _), Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  rw [he, cavitySpectralStack_gram _ (fun a => Matrix.PosSemidef.one.smul (hρ a)),
    ← Finset.sum_smul, hsum, one_smul]

theorem cavityLimitingStack_cavity_block {m n : ℕ} (ρ lam : Fin m → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) :
    (cavityLimitingStack (n := n) ρ).transpose * cavityRepeatedSpectrum (n := n) lam *
      cavityLimitingStack (n := n) ρ = (∑ a, ρ a * lam a) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  change (∑ k : Fin (m * n), (∑ t : Fin (m * n),
    cavityLimitingStack (n := n) ρ t i *
      (if t = k then lam (finProdFinEquiv.symm t).1 else 0)) *
      cavityLimitingStack (n := n) ρ k j) = _
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  simp only [cavityLimitingStack, Equiv.symm_apply_apply]
  change (∑ a : Fin m, ∑ b : Fin n,
    Real.sqrt (ρ a) * (if b = i then 1 else 0) * lam a *
      (Real.sqrt (ρ a) * (if b = j then 1 else 0))) =
    (∑ a, ρ a * lam a) * (if i = j then 1 else 0)
  have hs (a : Fin m) :
      (∑ b : Fin n, Real.sqrt (ρ a) * (if b = i then 1 else 0) * lam a *
        (Real.sqrt (ρ a) * (if b = j then 1 else 0))) =
      (ρ a * lam a) * (if i = j then 1 else 0) := by
    by_cases hij : i = j
    · subst j
      simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
      rw [mul_right_comm, Real.mul_self_sqrt (hρ a)]
    · have hji : j ≠ i := Ne.symm hij
      simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
      simp [hij, hji]
  simp_rw [hs]
  exact (Finset.sum_mul _ _ _).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySchurSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resolvent compression for the actual finite repeated spectrum. The
complete special/cavity basis gives the Schur compression directly. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

private lemma cavity_complete_basis_gram {r d n : ℕ}
    (B : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ)
    (hB : B.transpose * B = 1) (hE : E.transpose * E = 1)
    (hBE : B.transpose * E = 0) :
    (Matrix.fromCols B E).transpose * Matrix.fromCols B E = 1 := by
  have hEB : E.transpose * B = 0 := by
    have h := congrArg Matrix.transpose hBE
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero] using h
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols,
    hB, hE, hBE, hEB, Matrix.fromBlocks_one]

private lemma cavity_complete_basis_blocks {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin d) ℝ)
    (E : Matrix (Fin r) (Fin n) ℝ) :
    (Matrix.fromCols B E).transpose * D * Matrix.fromCols B E =
      cavitySpecialBlocks D B E := by
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
  rfl

/-- The resolvent of the full special/cavity block is the same complete
orthogonal compression of the original spectral resolvent. -/
theorem cavity_complete_blocks_inverse {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin d) ℝ)
    (E : Matrix (Fin r) (Fin n) ℝ) (b : ℝ)
    (hB : B.transpose * B = 1) (hE : E.transpose * E = 1)
    (hBE : B.transpose * E = 0) (hcomplete : B * B.transpose + E * E.transpose = 1)
    (hD : IsUnit (b • (1 : Matrix (Fin r) (Fin r) ℝ) - D).det) :
    (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks D B E)⁻¹ = cavitySpecialBlocks (b • 1 - D)⁻¹ B E := by
  let Q := Matrix.fromCols B E
  have hQ : Q.transpose * Q = 1 := cavity_complete_basis_gram B E hB hE hBE
  have hQQ : Q * Q.transpose = 1 := by
    simpa only [Q, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows] using hcomplete
  have hshift : b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks D B E = Q.transpose * (b • 1 - D) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hQ, cavity_complete_basis_blocks]
  rw [hshift, ← cavity_complete_basis_blocks]
  apply Matrix.inv_eq_right_inv
  calc
    (Q.transpose * (b • 1 - D) * Q) * (Q.transpose * (b • 1 - D)⁻¹ * Q) =
        Q.transpose * (b • 1 - D) * (Q * Q.transpose) * (b • 1 - D)⁻¹ * Q := by
      simp only [Matrix.mul_assoc]
    _ = Q.transpose * ((b • 1 - D) * (b • 1 - D)⁻¹) * Q := by
      rw [hQQ, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.mul_nonsing_inv _ hD, Matrix.mul_one, hQ]

private lemma cavityRepeatedSpectrum_shift {m n : ℕ} (lam : Fin m → ℝ) (b : ℝ) :
    b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam =
        Matrix.diagonal (fun i => b - lam (finProdFinEquiv.symm i).1) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [cavityRepeatedSpectrum]
  · simp [cavityRepeatedSpectrum, hij]

private lemma cavityRepeatedSpectrum_inverse_mul {m n : ℕ}
    (lam : Fin m → ℝ) (b : ℝ) (hb : ∀ a, b - lam a ≠ 0) :
    (b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam) *
        cavityRepeatedSpectrum (n := n) (fun a => (b - lam a)⁻¹) = 1 := by
  rw [cavityRepeatedSpectrum_shift]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [cavityRepeatedSpectrum, hb]
  · simp [cavityRepeatedSpectrum, hij]

lemma cavityRepeatedSpectrum_resolvent {m n : ℕ} (lam : Fin m → ℝ) (b : ℝ)
    (hb : ∀ a, b - lam a ≠ 0) :
    (b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam)⁻¹ =
        cavityRepeatedSpectrum (n := n) (fun a => (b - lam a)⁻¹) := by
  exact Matrix.inv_eq_right_inv (cavityRepeatedSpectrum_inverse_mul lam b hb)

/-- Exact `cav:compression`: the limiting cavity columns produce the
scalar finite-law Stieltjes transform, for every complete complement. -/
theorem cavity_limiting_blocks_compression {m d n : ℕ}
    (rho lam : Fin m → ℝ) (b : ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (hb : ∀ a, b - lam a ≠ 0) :
    ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks (cavityRepeatedSpectrum (n := n) lam) B
        (cavityLimitingStack (n := n) rho))⁻¹).toBlocks₂₂ =
      (∑ a, rho a / (b - lam a)) • 1 := by
  have hD := Matrix.isUnit_det_of_right_inverse
    (cavityRepeatedSpectrum_inverse_mul (n := n) lam b hb)
  rw [cavity_complete_blocks_inverse _ B _ b hB
    (cavityLimitingStack_gram rho hrho hsum) hBE hcomplete hD,
    cavityRepeatedSpectrum_resolvent lam b hb]
  change (cavityLimitingStack (n := n) rho).transpose *
    cavityRepeatedSpectrum (n := n) (fun a => (b - lam a)⁻¹) *
      cavityLimitingStack (n := n) rho = _
  simpa only [div_eq_mul_inv] using
    cavityLimitingStack_cavity_block rho (fun a => (b - lam a)⁻¹) hrho

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySchurMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact multiplicities in the cavity Schur determinant and the finite
spectral inverse used to evaluate the scalar cavity field. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

private lemma cavity_complete_conjugate_det {r s : Type*} [Fintype r] [Fintype s]
    [DecidableEq r] [DecidableEq s]
    (X : Matrix r r ℝ) (Q : Matrix r s ℝ)
    (hQ : Q.transpose * Q = 1) (hQQ : Q * Q.transpose = 1) :
    (Q.transpose * X * Q).det = X.det := by
  have hleft : Q.transpose * X * Q = 1 + Q.transpose * ((X - 1) * Q) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, hQ]
    rw [← Matrix.mul_assoc]
    abel
  have hright : 1 + ((X - 1) * Q) * Q.transpose = X := by
    rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
    abel
  rw [hleft, Matrix.det_one_add_mul_comm, hright]

/-- Determinants are preserved by the complete special/cavity basis,
even though its two index types need not be definitionally equal. -/
theorem cavity_complete_blocks_determinant {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin d) ℝ)
    (E : Matrix (Fin r) (Fin n) ℝ) (b : ℝ)
    (hB : B.transpose * B = 1) (hE : E.transpose * E = 1)
    (hBE : B.transpose * E = 0) (hcomplete : B * B.transpose + E * E.transpose = 1) :
    (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks D B E).det =
        (b • (1 : Matrix (Fin r) (Fin r) ℝ) - D).det := by
  let Q := Matrix.fromCols B E
  have hEB : E.transpose * B = 0 := by
    have h := congrArg Matrix.transpose hBE
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hQ : Q.transpose * Q = 1 := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols,
      hB, hE, hBE, hEB, Matrix.fromBlocks_one]
  have hQQ : Q * Q.transpose = 1 := by
    simpa only [Q, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows] using hcomplete
  have hblock : Q.transpose * D * Q = cavitySpecialBlocks D B E := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
    rfl
  have heq : b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks D B E = Q.transpose * (b • 1 - D) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hQ, hblock]
  rw [heq]
  exact cavity_complete_conjugate_det _ Q hQ hQQ

lemma cavityRepeatedSpectrum_shift_eq {m n : ℕ} (lam : Fin m → ℝ) (b : ℝ) :
    b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam =
        cavityRepeatedSpectrum (n := n) (fun a => b - lam a) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [cavityRepeatedSpectrum]
  · simp [cavityRepeatedSpectrum, hij]

/-- Every eigenvalue in the full limiting block occurs once for each
cavity coordinate. -/
theorem cavityRepeatedSpectrum_determinant {m n : ℕ} (lam : Fin m → ℝ) (b : ℝ) :
    (b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam).det = ∏ a, (b - lam a) ^ n := by
  rw [cavityRepeatedSpectrum_shift_eq, cavityRepeatedSpectrum, Matrix.det_diagonal]
  rw [← Equiv.prod_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.prod_prod_type, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem cavity_limiting_blocks_determinant {m d n : ℕ}
    (rho lam : Fin m → ℝ) (b : ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1) :
    (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks (cavityRepeatedSpectrum (n := n) lam) B
        (cavityLimitingStack (n := n) rho)).det = ∏ a, (b - lam a) ^ n := by
  rw [cavity_complete_blocks_determinant _ B _ b hB
    (cavityLimitingStack_gram rho hrho hsum) hBE hcomplete,
    cavityRepeatedSpectrum_determinant]

/-- The actual inverse-transform argument realizes the compression `x I`
without assuming a separate scalar resolvent identity. -/
theorem cavity_finiteInverse_blocks_compression {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (x : ℝ) (hx : 0 < x) :
    ((finiteInverse rho lam hrho hsum x •
        (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks (cavityRepeatedSpectrum (n := n) lam) B
        (cavityLimitingStack (n := n) rho))⁻¹).toBlocks₂₂ = x • 1 := by
  have hs := finiteInverse_spec rho lam hrho hsum hx
  rw [cavity_limiting_blocks_compression rho lam _ (fun a => (hrho a).le)
    hsum B hB hBE hcomplete (fun a => ne_of_gt (sub_pos.mpr (hs.1 a)))]
  exact congrArg (fun y : ℝ => y • (1 : Matrix (Fin n) (Fin n) ℝ)) hs.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySchurFiniteR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar Schur field of the actual limiting cavity block is the
finite spectral R-transform, including its prescribed value at zero. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

private lemma cavity_compressed_shift_posDef {r d : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin d) ℝ) (b : ℝ)
    (hB : B.transpose * B = 1) (hD : (b • (1 : Matrix (Fin r) (Fin r) ℝ) - D).PosDef) :
    (b • (1 : Matrix (Fin d) (Fin d) ℝ) - B.transpose * D * B).PosDef := by
  have hBinj : Function.Injective B.mulVec := by
    intro x y hxy
    have h := congrArg (fun z => B.transpose *ᵥ z) hxy
    simpa only [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] using h
  have h := hD.conjTranspose_mul_mul_same hBinj
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hB] using h

private lemma cavitySpecialBlocks_symmetric_fromBlocks {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin d) ℝ)
    (E : Matrix (Fin r) (Fin n) ℝ) (hD : D.transpose = D) :
    cavitySpecialBlocks D B E = Matrix.fromBlocks (B.transpose * D * B)
      (B.transpose * D * E) (B.transpose * D * E).transpose (E.transpose * D * E) := by
  unfold cavitySpecialBlocks
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hD]
  simp only [Matrix.mul_assoc]

/-- The source field identity at its true finite-law inverse argument.
Both required determinant hypotheses are derived from spectral positivity. -/
theorem cavity_limiting_field_eq_finiteR {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (x : ℝ) (hx : 0 < x) :
    let D := cavityRepeatedSpectrum (n := n) lam
    let E := cavityLimitingStack (n := n) rho
    let b := finiteInverse rho lam hrho hsum x
    E.transpose * D * E + (B.transpose * D * E).transpose *
      (b • (1 : Matrix (Fin d) (Fin d) ℝ) - B.transpose * D * B)⁻¹ *
        (B.transpose * D * E) = finiteR rho lam hrho hsum x • 1 := by
  dsimp only
  let D := cavityRepeatedSpectrum (n := n) lam
  let E := cavityLimitingStack (n := n) rho
  let b := finiteInverse rho lam hrho hsum x
  let A := B.transpose * D * B
  let L := B.transpose * D * E
  let C := E.transpose * D * E
  have hb : ∀ a, lam a < b := (finiteInverse_spec rho lam hrho hsum hx).1
  have hDsym : D.transpose = D := Matrix.diagonal_transpose _
  have hD : (b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) - D).PosDef := by
    rw [show D = cavityRepeatedSpectrum (n := n) lam from rfl,
      cavityRepeatedSpectrum_shift_eq]
    exact Matrix.PosDef.diagonal (fun i => sub_pos.mpr (hb (finProdFinEquiv.symm i).1))
  have hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det :=
    isUnit_iff_ne_zero.mpr (cavity_compressed_shift_posDef D B b hB hD).det_pos.ne'
  have hblocks : Matrix.fromBlocks A L L.transpose C = cavitySpecialBlocks D B E :=
    (cavitySpecialBlocks_symmetric_fromBlocks D B E hDsym).symm
  have hM : IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det := by
    rw [hblocks]
    change IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks (cavityRepeatedSpectrum (n := n) lam) B
        (cavityLimitingStack (n := n) rho)).det
    rw [cavity_limiting_blocks_determinant rho lam b (fun a => (hrho a).le)
      hsum B hB hBE hcomplete]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
      (fun a _ => pow_ne_zero n (ne_of_gt (sub_pos.mpr (hb a)))))
  have hcomp : ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C)⁻¹).toBlocks₂₂ = x • 1 := by
    rw [hblocks]
    exact cavity_finiteInverse_blocks_compression rho lam hrho hsum B hB hBE hcomplete x hx
  have hf := cavity_schur_scalar_field A L C b x hx.ne' hA hM hcomp
  simpa only [finiteR, ite_eq_left hx, one_div, A, L, C, D, E, b] using hf

theorem cavity_limiting_cavityBlock_eq_finiteR_zero {m n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) :
    (cavityLimitingStack (n := n) rho).transpose * cavityRepeatedSpectrum (n := n) lam *
      cavityLimitingStack (n := n) rho = finiteR rho lam hrho hsum 0 • 1 := by
  simpa only [finiteR, lt_self_iff_false, ite_false, if_false] using
    cavityLimitingStack_cavity_block rho lam (fun a => (hrho a).le)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The projected root covariance for the actual finite spectral cavity
blocks. All determinant conditions follow from the positive spectral gap. -/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
open Filter

namespace InvariantIsing

private lemma cavity_finite_base_shift_isUnit {m d : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (x : ℝ) (hx : 0 < x) :
    IsUnit (finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => lam (g i))).det := by
  have he : finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => lam (g i)) =
      Matrix.diagonal (fun i => finiteInverse rho lam hrho hsum x - lam (g i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [he]
  exact isUnit_iff_ne_zero.mpr
    (Matrix.PosDef.diagonal (fun i => sub_pos.mpr
      ((finiteInverse_spec rho lam hrho hsum hx).1 (g i)))).det_pos.ne'

private lemma cavity_finite_compressed_shift_isUnit {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (x : ℝ) (hx : 0 < x) :
    IsUnit (finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      B.transpose * cavityRepeatedSpectrum (n := n) lam * B).det := by
  have hBinj : Function.Injective B.mulVec := by
    intro u v huv
    have he := congrArg (fun w => B.transpose *ᵥ w) huv
    simpa only [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] using he
  have hp : (finiteInverse rho lam hrho hsum x •
      (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
        cavityRepeatedSpectrum (n := n) lam).PosDef := by
    rw [cavityRepeatedSpectrum_shift_eq]
    exact Matrix.PosDef.diagonal (fun i => sub_pos.mpr
      ((finiteInverse_spec rho lam hrho hsum hx).1 (finProdFinEquiv.symm i).1))
  have hc := hp.conjTranspose_mul_mul_same hBinj
  have he : (finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      B.transpose * cavityRepeatedSpectrum (n := n) lam * B).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hB] using hc
  exact isUnit_iff_ne_zero.mpr he.det_pos.ne'

/-- The finite cavity tilt is invertible at every positive deficit. -/
lemma cavity_finite_tilt_isUnit {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (g : Fin d → Fin m) (x : ℝ) (hx : 0 < x) :
    let A := B.transpose * cavityRepeatedSpectrum (n := n) lam * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let H := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    IsUnit (1 - H * (A - A₀)).det := by
  dsimp only
  let A := B.transpose * cavityRepeatedSpectrum (n := n) lam * B
  let A₀ := Matrix.diagonal (fun i => lam (g i))
  let b := finiteInverse rho lam hrho hsum x
  have h₀ : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀).det :=
    cavity_finite_base_shift_isUnit rho lam hrho hsum g x hx
  have hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det :=
    cavity_finite_compressed_shift_isUnit rho lam hrho hsum B hB x hx
  have he : 1 - (b • 1 - A₀)⁻¹ * (A - A₀) =
      (b • 1 - A₀)⁻¹ * (b • 1 - A) := by
    calc
      _ = (b • 1 - A₀)⁻¹ * (b • 1 - A₀) - (b • 1 - A₀)⁻¹ * (A - A₀) := by
        rw [Matrix.nonsing_inv_mul _ h₀]
      _ = _ := by noncomm_ring
  change IsUnit (1 - (b • 1 - A₀)⁻¹ * (A - A₀)).det
  rw [he, Matrix.det_mul]
  exact (Matrix.isUnit_nonsing_inv_det_iff.mpr h₀).mul hA

/-- The projected resolvent of the finite cavity tilt has the prescribed
finite-law scalar field value. -/
lemma cavity_finite_projected_resolvent {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (x : ℝ) (hx : 0 < x) :
    let D := cavityRepeatedSpectrum (n := n) lam
    let E := cavityLimitingStack (n := n) rho
    let A := B.transpose * D * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * D * E
    let H := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    E.transpose * D * E + L.transpose * cavityResolvent (A - A₀) H * L =
      finiteR rho lam hrho hsum x • 1 := by
  dsimp only
  rw [cavityResolvent_spectral_transform _ _ _
    (cavity_finite_base_shift_isUnit rho lam hrho hsum g x hx)
    (cavity_finite_compressed_shift_isUnit rho lam hrho hsum B hB x hx)]
  exact cavity_limiting_field_eq_finiteR rho lam hrho hsum B hB hBE hcomplete x hx

/-- The source root derivative evaluated on the actual repeated-spectrum
special/cavity blocks. The base multiplicity map is arbitrary, so this
also applies after deleting the cavity eigenvectors from each group. -/
theorem cavity_finite_projected_root_covariance {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (x : ℝ) (hx : 0 < x) :
    let A := B.transpose * cavityRepeatedSpectrum (n := n) lam * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := n) lam *
      cavityLimitingStack (n := n) rho
    let K := A - A₀
    let H := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    let H' := (1 / finiteSecondResolvent rho lam (finiteInverse rho lam hrho hsum x)) • (H * H)
    L.transpose * ((1 - H * K)⁻¹ * H' * ((1 - H * K)⁻¹).transpose) * L =
      deriv (finiteR rho lam hrho hsum) x • 1 := by
  let D := cavityRepeatedSpectrum (n := n) lam
  let E := cavityLimitingStack (n := n) rho
  let A := B.transpose * D * B
  let A₀ := Matrix.diagonal (fun i => lam (g i))
  let L := B.transpose * D * E
  let C₀ := E.transpose * D * E
  let K := A - A₀
  let b := finiteInverse rho lam hrho hsum
  let H := fun t => (b t • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀)⁻¹
  let v := -1 / finiteSecondResolvent rho lam (b x)
  have h0 (t : ℝ) (ht : 0 < t) : IsUnit (b t • 1 - A₀).det :=
    cavity_finite_base_shift_isUnit rho lam hrho hsum g t ht
  have hA (t : ℝ) (ht : 0 < t) : IsUnit (b t • 1 - A).det :=
    cavity_finite_compressed_shift_isUnit rho lam hrho hsum B hB t ht
  have hAs : A.transpose = A := by
    dsimp only [A, D, cavityRepeatedSpectrum]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose]
    simp only [Matrix.mul_assoc]
  have hKs : K.transpose = K := by
    simp only [K, A₀, Matrix.transpose_sub, hAs, Matrix.diagonal_transpose]
  have hHs : (H x).transpose = H x := by
    simp only [H, A₀, Matrix.transpose_nonsing_inv, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.diagonal_transpose]
  have hdet : IsUnit (1 - H x * K).det := by
    have he : 1 - H x * K = H x * (b x • 1 - A) := by
      have hinv := Matrix.nonsing_inv_mul (b x • 1 - A₀) (h0 x hx)
      change H x * (b x • 1 - A₀) = 1 at hinv
      calc
        1 - H x * K = H x * (b x • 1 - A₀) - H x * K := by rw [hinv]
        _ = H x * (b x • 1 - A) := by dsimp only [K]; noncomm_ring
    rw [he, Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det_iff.mpr (h0 x hx)).mul (hA x hx)
  have hb : HasDerivAt b v x :=
    (hasStrictDerivAt_finiteInverse rho lam hrho hsum hx).hasDerivAt
  have hshift := (hb.smul_const (1 : Matrix (Fin d) (Fin d) ℝ)).sub_const A₀
  have hH := hasDerivAt_cavityMatrixInverse _ _ x hshift (h0 x hx)
  have hH' : HasDerivAt H ((-v) • (H x * H x)) x := by
    convert! hH using 1
    all_goals try with_reducible_and_instances rfl
    simp only [H, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      neg_smul, smul_neg]
  have hscalar : (fun t => C₀ + L.transpose * cavityResolvent K (H t) * L) =ᶠ[𝓝 x]
      (fun t => finiteR rho lam hrho hsum t • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    rw [show cavityResolvent K (H t) = (b t • 1 - A)⁻¹ from
      cavityResolvent_spectral_transform A A₀ (b t) (h0 t ht) (hA t ht)]
    exact cavity_limiting_field_eq_finiteR rho lam hrho hsum B hB hBE hcomplete t ht
  have hr := (hasStrictDerivAt_finiteR rho lam hrho hsum hx).hasDerivAt
  have he := cavity_projected_root_covariance K H ((-v) • (H x * H x)) L C₀
    (finiteR rho lam hrho hsum) _ x hKs hHs hH' hdet hr hscalar
  rw [hr.deriv]
  simpa only [v, neg_div, neg_neg] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteInnovation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar projections of the innovations and the ordinary residual for
the actual finite spectral cavity blocks. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

theorem cavity_finite_projected_innovation {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (x y ζ : ℝ) (hx : 0 < x) (hy : 0 < y) (hζ : ζ ≠ 0)
    (S : Matrix (Fin d) (Fin d) ℝ)
    (hΔ : (finiteInverse rho lam hrho hsum x • 1 - Matrix.diagonal (fun i => lam (g i)))⁻¹ -
      (finiteInverse rho lam hrho hsum y • 1 - Matrix.diagonal (fun i => lam (g i)))⁻¹ = ζ • S) :
    let D := cavityRepeatedSpectrum (n := n) lam
    let E := cavityLimitingStack (n := n) rho
    let A := B.transpose * D * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * D * E
    let K := A - A₀
    let P := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    let C := (finiteInverse rho lam hrho hsum y • 1 - A₀)⁻¹
    L.transpose * ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) * L =
      ((finiteR rho lam hrho hsum x - finiteR rho lam hrho hsum y) / ζ) • 1 := by
  intro D E A A₀ L K P C
  have hK : K.transpose = K := by
    dsimp only [K, A, A₀, D, cavityRepeatedSpectrum]
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hC : C.transpose = C := by
    simp only [C, A₀, Matrix.transpose_nonsing_inv, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.diagonal_transpose]
  exact cavity_projected_innovation_covariance K P C S L (E.transpose * D * E)
    (finiteR rho lam hrho hsum x) (finiteR rho lam hrho hsum y) ζ hζ hK hC
    (cavity_finite_tilt_isUnit rho lam hrho hsum B hB g x hx)
    (cavity_finite_tilt_isUnit rho lam hrho hsum B hB g y hy) hΔ
    (cavity_finite_projected_resolvent rho lam hrho hsum B hB hBE hcomplete g x hx)
    (cavity_finite_projected_resolvent rho lam hrho hsum B hB hBE hcomplete g y hy)

theorem cavity_finite_projected_residual {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (x : ℝ) (hx : 0 < x) :
    let D := cavityRepeatedSpectrum (n := n) lam
    let E := cavityLimitingStack (n := n) rho
    let A := B.transpose * D * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * D * E
    let H := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    L.transpose * cavityResolvent (A - A₀) H * L =
      (finiteR rho lam hrho hsum x - finiteR rho lam hrho hsum 0) • 1 := by
  intro D E A A₀ L H
  have hp := cavity_finite_projected_resolvent rho lam hrho hsum B hB hBE hcomplete g x hx
  change E.transpose * D * E + L.transpose * cavityResolvent (A - A₀) H * L = _ at hp
  rw [cavity_limiting_cavityBlock_eq_finiteR_zero rho lam hrho hsum] at hp
  rw [sub_smul]
  exact eq_sub_of_add_eq' hp

theorem cavity_finite_projected_scaled_root {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (x q₀ : ℝ) (hx : 0 < x) :
    let A := B.transpose * cavityRepeatedSpectrum (n := n) lam * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := n) lam *
      cavityLimitingStack (n := n) rho
    let K := A - A₀
    let H := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    let H' := (1 / finiteSecondResolvent rho lam (finiteInverse rho lam hrho hsum x)) • (H * H)
    L.transpose * ((1 - H * K)⁻¹ * (q₀ • H') * ((1 - H * K)⁻¹).transpose) * L =
      (q₀ * deriv (finiteR rho lam hrho hsum) x) • 1 := by
  intro A A₀ L K H H'
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [cavity_finite_projected_root_covariance rho lam hrho hsum B hB hBE hcomplete g x hx,
    smul_smul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity and precision of the finite-alphabet covariance used by
the cavity calculation. No dimension-dependent spectral bound is needed. -/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι] {d : ℕ}

lemma cavityFiniteCovariance_diagonal (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → ι) {x : ℝ} (hx : 0 < x) :
    cavityFiniteCovariance rho lam hrho hsum g x =
      Matrix.diagonal (fun i => (finiteInverse rho lam hrho hsum x - lam (g i))⁻¹) := by
  unfold cavityFiniteCovariance
  have he : finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => lam (g i)) =
      Matrix.diagonal (fun i => finiteInverse rho lam hrho hsum x - lam (g i)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  apply Matrix.inv_eq_right_inv
  rw [he, Matrix.diagonal_mul_diagonal]
  have hg (i : Fin d) : finiteInverse rho lam hrho hsum x - lam (g i) ≠ 0 :=
    (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hx).1 (g i))).ne'
  simp [hg]

lemma cavityFiniteCovariance_posDef (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → ι) {x : ℝ} (hx : 0 < x) :
    (cavityFiniteCovariance rho lam hrho hsum g x).PosDef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g hx]
  exact Matrix.PosDef.diagonal (fun i => inv_pos.mpr
    (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hx).1 (g i))))

lemma cavityFiniteCovariance_sub_posSemidef (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    (cavityFiniteCovariance rho lam hrho hsum g x -
      cavityFiniteCovariance rho lam hrho hsum g y).PosSemidef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g (hy.trans_le hyx),
    cavityFiniteCovariance_diagonal rho lam hrho hsum g hy, Matrix.diagonal_sub]
  apply Matrix.PosSemidef.diagonal
  intro i
  apply sub_nonneg.mpr
  exact inv_anti₀ (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum
    (hy.trans_le hyx)).1 (g i)))
    (sub_le_sub_right (finiteInverse_antitone_pos rho lam hrho hsum hy hyx) _)

lemma finiteInverse_strict_antitone_pos (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {x y : ℝ} (hy : 0 < y) (hyx : y < x) :
    finiteInverse rho lam hrho hsum x < finiteInverse rho lam hrho hsum y := by
  apply lt_of_le_of_ne (finiteInverse_antitone_pos rho lam hrho hsum hy hyx.le)
  intro he
  have h := congrArg (finiteResolvent rho lam) he
  rw [(finiteInverse_spec rho lam hrho hsum (hy.trans hyx)).2,
    (finiteInverse_spec rho lam hrho hsum hy).2] at h
  exact hyx.ne h.symm

lemma cavityFiniteCovariance_sub_posDef (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    {x y : ℝ} (hy : 0 < y) (hyx : y < x) :
    (cavityFiniteCovariance rho lam hrho hsum g x -
      cavityFiniteCovariance rho lam hrho hsum g y).PosDef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g (hy.trans hyx),
    cavityFiniteCovariance_diagonal rho lam hrho hsum g hy, Matrix.diagonal_sub]
  apply Matrix.PosDef.diagonal
  intro i
  apply sub_pos.mpr
  simpa only [one_div] using one_div_lt_one_div_of_lt
    (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum (hy.trans hyx)).1 (g i)))
    (sub_lt_sub_right (finiteInverse_strict_antitone_pos rho lam hrho hsum hy hyx) _)

lemma cavityFiniteCovariance_root_posSemidef (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    {x q₀ : ℝ} (hx : 0 < x) (hq₀ : 0 ≤ q₀) :
    (q₀ • ((1 / finiteSecondResolvent rho lam (finiteInverse rho lam hrho hsum x)) •
      (cavityFiniteCovariance rho lam hrho hsum g x *
        cavityFiniteCovariance rho lam hrho hsum g x))).PosSemidef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g hx, Matrix.diagonal_mul_diagonal]
  have hM : 0 < finiteSecondResolvent rho lam (finiteInverse rho lam hrho hsum x) :=
    finiteSecondResolvent_pos (fun a => (hrho a).le) hsum
      (finiteInverse_spec rho lam hrho hsum hx).1
  exact ((Matrix.PosSemidef.diagonal (fun i => mul_self_nonneg _)).smul
    (one_div_nonneg.mpr hM.le)).smul hq₀

theorem cavityFiniteCovariance_step_precision (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    (A : Matrix (Fin d) (Fin d) ℝ) (a : ι)
    (hK : (A - Matrix.diagonal (fun i => lam (g i))).transpose =
      A - Matrix.diagonal (fun i => lam (g i)))
    (hA : (lam a • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    {x y ζ : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hζ : 0 ≤ ζ)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hΔ : cavityFiniteCovariance rho lam hrho hsum g x -
      cavityFiniteCovariance rho lam hrho hsum g y = ζ • S) :
    (cavityFactorPrecision
      (ζ • cavityBackwardQuadratic (A - Matrix.diagonal (fun i => lam (g i)))
        (cavityFiniteCovariance rho lam hrho hsum g y)) (CFC.sqrt S)).PosDef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g hy]
  apply cavity_scaled_step_precision _ S hK hS ζ hζ
    (fun i => (finiteInverse rho lam hrho hsum x - lam (g i))⁻¹)
    (fun i => (finiteInverse rho lam hrho hsum y - lam (g i))⁻¹)
  · intro i
    exact inv_pos.mpr (sub_pos.mpr
      ((finiteInverse_spec rho lam hrho hsum (hy.trans_le hyx)).1 (g i)))
  · intro i
    exact (inv_pos.mpr (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hy).1 (g i)))).le
  · intro i
    exact inv_anti₀ (sub_pos.mpr
      ((finiteInverse_spec rho lam hrho hsum (hy.trans_le hyx)).1 (g i)))
      (sub_le_sub_right (finiteInverse_antitone_pos rho lam hrho hsum hy hyx) _)
  · right
    intro i
    exact inv_pos.mpr (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hy).1 (g i)))
  · exact cavity_resolvent_diagonal_gap A (fun i => lam (g i)) (lam a)
      (finiteInverse rho lam hrho hsum x) hA
      ((finiteInverse_spec rho lam hrho hsum (hy.trans_le hyx)).1 a)
  · simpa only [cavityFiniteCovariance_diagonal rho lam hrho hsum g (hy.trans_le hyx),
      cavityFiniteCovariance_diagonal rho lam hrho hsum g hy] using hΔ

theorem cavityFiniteCovariance_terminal_precision (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    (A : Matrix (Fin d) (Fin d) ℝ) (a : ι) (ha : ∀ i, lam (g i) ≤ lam a)
    (hK : (A - Matrix.diagonal (fun i => lam (g i))).transpose =
      A - Matrix.diagonal (fun i => lam (g i)))
    (hA : (lam a • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    {x : ℝ} (hx : 0 < x) :
    (cavityFactorPrecision (A - Matrix.diagonal (fun i => lam (g i)))
      (CFC.sqrt (cavityFiniteCovariance rho lam hrho hsum g x))).PosDef := by
  apply cavity_resolvent_terminal_precision A _ (fun i => lam (g i)) (lam a)
    (finiteInverse rho lam hrho hsum x) hK hA ha
    ((finiteInverse_spec rho lam hrho hsum hx).1 a)
  rw [cavity_covariance_sqrt_factor _ (cavityFiniteCovariance_posDef rho lam hrho hsum g hx).posSemidef,
    cavityFiniteCovariance_diagonal rho lam hrho hsum g hx]

lemma cavity_finite_spectral_upper {m n : ℕ}
    (lam : Fin m → ℝ) (a : Fin m) (ha : ∀ i, lam i ≤ lam a)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1) :
    (lam a • (1 : Matrix (Fin d) (Fin d) ℝ) -
      B.transpose * cavityRepeatedSpectrum (n := n) lam * B).PosSemidef := by
  have hD : (lam a • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam).PosSemidef := by
    rw [cavityRepeatedSpectrum_shift_eq]
    exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (ha _))
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hB] using
    hD.conjTranspose_mul_mul_same B

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldLevelPath
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded monotone representative on the field partition. Endpoint
values are immaterial to integration; the representative is defined globally. -/

noncomputable section
open MeasureTheory Set

namespace InvariantIsing

lemma fieldLevelIndex_on_cell (h : FieldStep) (i : Fin (h.depth + 1))
    {s : ℝ} (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    fieldLevelIndex h s = i := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _hj
    by_cases hj : h.cut j.castSucc ≤ s
    · simp only [hj, ite_true, if_true]
      by_contra hji
      have hij : i.succ ≤ j.castSucc := by
        change i.val + 1 ≤ j.val
        have : i < j := lt_of_not_ge hji
        exact this
      have hc := h.ordered_cut.monotone hij
      linarith [hs.2]
    · simp only [hj, ite_false, if_false]
      exact bot_le
  · have hi := Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin (h.depth + 1) => if h.cut j.castSucc ≤ s then j else 0)
      (Finset.mem_univ i)
    simpa only [fieldLevelIndex, hs.1.le, ite_true, if_true] using hi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteFieldVariance
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar variances in the published field marking input coincide
with the finite spectral cavity covariance increments. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldStepVariance_eq_height_sub (h : FieldStep) (i : Fin h.depth) :
    (fieldStepVariance h i : ℝ) = h.height i.succ - h.height i.castSucc := by
  rw [fieldStepVariance, dite_eq_left i.isLt]
  have hg : (scalarFieldIncrements h).get
      ⟨i, by simpa only [scalarFieldIncrements_length] using i.isLt⟩ =
      ((fieldIncrement h i.succ).1,
        NNReal.mk (fieldIncrement h i.succ).2 (fieldIncrement_nonneg h i.succ)) := by
    exact List.get_ofFn (fun k : Fin h.depth => ((fieldIncrement h k.succ).1,
      NNReal.mk (fieldIncrement h k.succ).2 (fieldIncrement_nonneg h k.succ))) _
  rw [hg]
  change (fieldIncrement h i.succ).2 = _
  simp only [fieldIncrement, Fin.val_succ, Nat.succ_ne_zero,
    dite_false, Nat.add_sub_cancel]
  rfl

variable {ι : Type*} [Fintype ι]

theorem cavityFieldStep_variance (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {n : ℕ} (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (i : Fin n) :
    (fieldStepVariance
      (cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0) i : ℝ) =
      (finiteR rho lam hrho hsum (deficit p (q i.castSucc)) -
        finiteR rho lam hrho hsum (deficit p (q i.succ))) / cut i.castSucc.succ := by
  rw [fieldStepVariance_eq_height_sub
    (cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0) i]
  change cavityFieldPrimitive rho lam hrho hsum p (q i.succ) -
    cavityFieldPrimitive rho lam hrho hsum p (q i.castSucc) = _
  rw [cavityFieldPrimitive_sub]
  calc
    _ = ∫ r in q i.castSucc..q i.succ,
        deriv (finiteR rho lam hrho hsum) (deficit p r) := by
      apply intervalIntegral.integral_congr_Ioo_of_le
        (hq (Fin.castSucc_lt_succ (i := i))).le
      intro r hr
      exact cavityRDerivative_eq_deriv rho lam hrho hsum
        (finite_overlap_deficit_pos p cut hfirst hlast q hq.monotone hp htop
          (hr.2.le.trans (hq.monotone (Fin.le_last _))))
    _ = _ := finite_overlap_field_increment rho lam hrho hsum p cut hcut
      hfirst hlast q hq hp htop i

theorem cavityFieldStep_root_variance (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {n : ℕ} (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) :
    (cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq hq0).height 0 =
      q 0 * deriv (finiteR rho lam hrho hsum) (deficit p (q 0)) := by
  change (∫ r in 0..q 0, cavityFieldDensity rho lam hrho hsum p r) = _
  calc
    _ = ∫ r in 0..q 0, deriv (finiteR rho lam hrho hsum) (deficit p r) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (hq0 0)
      intro r hr
      exact cavityRDerivative_eq_deriv rho lam hrho hsum
        (finite_overlap_deficit_pos p cut hfirst hlast q hq hp htop
          (hr.2.le.trans (hq (Fin.le_last _))))
    _ = _ := finite_overlap_field_root rho lam hrho hsum p cut hcut
      hfirst hlast q hq hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficitPath
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite overlap quantile, held constant beyond its last level,
and the strictly decreasing deficits on its active cascade steps. -/

noncomputable section
open MeasureTheory Set IsingPerceptron

namespace InvariantIsing

lemma cavityFiniteLevel_castSucc {n : ℕ} (i : Fin n) :
    cavityFiniteLevel n i = i.castSucc := by
  apply Fin.ext
  exact min_eq_left i.isLt.le

lemma cavityFiniteLevel_succ {n : ℕ} (i : Fin n) :
    cavityFiniteLevel n (i + 1) = i.succ := by
  apply Fin.ext
  exact min_eq_left i.isLt

lemma cavityFiniteDeficitPath_antitone {n : ℕ} (p : OverlapPath)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q) : Antitone (cavityFiniteDeficitPath p q) :=
  (deficit_antitone_argument p).comp_monotone (hq.comp (cavityFiniteLevel_monotone n))

lemma cavityFiniteDeficitPath_pos {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (i : ℕ) : 0 < cavityFiniteDeficitPath p q i :=
  finite_overlap_deficit_pos p cut hfirst hlast q hq hp htop (hq (Fin.le_last _))

lemma cavityFiniteDeficitPath_step {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (i : Fin n) :
    cavityFiniteDeficitPath p q i - cavityFiniteDeficitPath p q (i + 1) =
      chainExponent cut i * (q i.succ - q i.castSucc) := by
  have he := finite_overlap_deficit_increment p cut hcut hfirst hlast q hq hp i
    ⟨(hq (Fin.castSucc_lt_succ (i := i))).le, le_rfl⟩
  simp only [cavityFiniteDeficitPath, cavityFiniteLevel_castSucc, cavityFiniteLevel_succ,
    chainExponent_apply cut i.isLt]
  have hc : cut i.succ.castSucc = cut ⟨i + 1, by omega⟩ := congrArg cut (Fin.ext rfl)
  rw [hc] at he
  linarith

lemma cavityFiniteDeficitPath_step_strict {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (i : Fin n) : cavityFiniteDeficitPath p q (i + 1) < cavityFiniteDeficitPath p q i := by
  have hc : 0 < chainExponent cut i := by
    rw [chainExponent_apply cut i.isLt, ← hfirst]
    apply hcut
    change 0 < i.val + 1
    omega
  apply sub_pos.mp
  rw [cavityFiniteDeficitPath_step p cut hcut hfirst hlast q hq hp i]
  exact mul_pos hc (sub_pos.mpr (hq (Fin.castSucc_lt_succ (i := i))))

lemma finite_chainExponent_pos {n : ℕ} (cut : Fin (n + 2) → ℝ)
    (hcut : StrictMono cut) (hfirst : cut 0 = 0) (i : ℕ) : 0 < chainExponent cut i := by
  unfold chainExponent
  rw [← hfirst]
  apply hcut
  change 0 < min (i + 1) (n + 1)
  omega

lemma field_chainExponent_pos (h : FieldStep) (i : ℕ) : 0 < chainExponent h.cut i :=
  finite_chainExponent_pos h.cut h.ordered_cut h.first i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianMarkDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Non-atomic Gaussian coordinates identify branching in the retained
quadratic cascade. Common-level tests survive its innovation transport. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Classical Matrix

namespace InvariantIsing

lemma cavity_multivariateGaussian_nullSingleton {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (j : Fin d) (hj : 0 < S j j) :
    NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S) := by
  have hv : (S j j).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr hj)
  let _ := nullSingletonClass_gaussianReal (μ := 0) hv
  constructor
  intro x
  have hp := (measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin d)))
    hS (i := j)).map_eq
  have hz : (0 : EuclideanSpace ℝ (Fin d)) j = 0 := rfl
  rw [hz] at hp
  have hn : (gaussianReal 0 (S j j).toNNReal) {x j} = 0 := measure_singleton _
  rw [← hp, Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hn
  apply measure_mono_null _ hn
  intro y hy
  exact congrArg (fun z : EuclideanSpace ℝ (Fin d) => z j) hy

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteCovariancePath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite cascade covariance path and independent Gaussian
increments, including zero increments beyond the terminal level. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder BigOperators

namespace InvariantIsing

variable {m d n : ℕ}

variable (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
  (g : Fin d → Fin m) (p : OverlapPath) (cut : Fin (n + 2) → ℝ)
  (hcut : StrictMono cut) (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
  (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
  (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
  (htop : q (Fin.last n) < 1)

include hfirst hlast hq hp htop in
lemma cavityFiniteCovariancePath_posDef (i : ℕ) :
    (cavityFiniteCovariancePath rho lam hrho hsum g p q i).PosDef :=
  cavityFiniteCovariance_posDef rho lam hrho hsum g
    (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop i)

lemma cavityFiniteCovariancePath_symmetric (i : ℕ) :
    (cavityFiniteCovariancePath rho lam hrho hsum g p q i).transpose =
      cavityFiniteCovariancePath rho lam hrho hsum g p q i := by
  simp only [cavityFiniteCovariancePath, cavityFiniteCovariance,
    Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.diagonal_transpose]

include hcut hfirst in
lemma cavityFiniteNoiseCovariance_delta (i : ℕ) :
    cavityFiniteCovariancePath rho lam hrho hsum g p q i -
      cavityFiniteCovariancePath rho lam hrho hsum g p q (i + 1) =
        chainExponent cut i • cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i := by
  rw [cavityFiniteNoiseCovariance, smul_smul,
    mul_inv_cancel₀ (finite_chainExponent_pos cut hcut hfirst i).ne', one_smul]

include hcut hfirst hlast hq hp htop in
lemma cavityFiniteNoiseCovariance_posSemidef (i : ℕ) :
    (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact cavityFiniteCovariance_sub_posSemidef rho lam hrho hsum g
      (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop (i + 1))
      (cavityFiniteDeficitPath_antitone p q hq.monotone (Nat.le_succ i))
  · exact inv_nonneg.mpr (finite_chainExponent_pos cut hcut hfirst i).le

include hcut hfirst hlast hq hp htop in
lemma cavityFiniteNoiseCovariance_posDef (i : Fin n) :
    (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i).PosDef := by
  apply Matrix.PosDef.smul
  · exact cavityFiniteCovariance_sub_posDef rho lam hrho hsum g
      (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop (i + 1))
      (cavityFiniteDeficitPath_step_strict p cut hcut hfirst hlast q hq hp i)
  · exact inv_pos.mpr (finite_chainExponent_pos cut hcut hfirst i)

include hcut hfirst hlast hq hp htop in
lemma cavityFiniteNoiseCovariance_atomless (hd : 0 < d) (i : ℕ) (hi : i < n) :
    NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i)) := by
  have hs := cavityFiniteNoiseCovariance_posDef rho lam hrho hsum g p cut hcut hfirst hlast
    q hq hp htop ⟨i, hi⟩
  exact cavity_multivariateGaussian_nullSingleton _ hs.posSemidef ⟨0, hd⟩ hs.diag_pos

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteSpinTest
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full quadratic cavity spin test for a finite spectral law and
overlap quantile, with matrix and scalar covariances determined by the
spectral data. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

theorem cavity_finite_spin_test_oai (hpub : PanchenkoTalagrandFieldPairInput)
    {m d N n : ℕ} (hd : 0 < d) (hN : 0 < N)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (Φ : ℝ → ℝ) (j : Fin N)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    let hq0 := fun i => (finite_overlap_value_mem_unit p cut hcut q hp i).1
    let h := cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0
    let H := cavityFiniteCovariancePath rho lam hrho hsum g p q
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
    let c := finiteR rho lam hrho hsum 0
    (∫ σ, cavityRootedSpinDepthTest (fun i => Φ (q (fieldDepthLevel h i))) j σ
      ∂((probabilityReplicaKernel
        (cavityRootedFullGibbs n K (H n) L (c • 1) (uniformSpinPrior N))
        (cavityRootedFullGibbs n K (H n) L (c • 1) (uniformSpinPrior N)).measurable)
          ∘ₘ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
            (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n (chainExponent cut)
              (cavityGaussianMarks S) : Measure _))) =
      ∫ t, Φ (p t) * fieldMagnetizationPath h t ∂pathMeasure := by
  intro hq0 h H S S₀ K L c
  let x := cavityFiniteDeficitPath p q
  have hx (i : ℕ) : 0 < x i :=
    cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop i
  have hxm : Antitone x := cavityFiniteDeficitPath_antitone p q hq.monotone
  have hK : K.transpose = K := by
    dsimp only [K, cavityRepeatedSpectrum]
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hH (i : ℕ) : (H i).transpose = H i :=
    cavityFiniteCovariancePath_symmetric rho lam hrho hsum g p q i
  have hS (i : ℕ) : (S i).PosSemidef :=
    cavityFiniteNoiseCovariance_posSemidef rho lam hrho hsum g p cut hcut hfirst hlast
      q hq hp htop i
  have hS₀ : S₀.PosSemidef :=
    cavityFiniteCovariance_root_posSemidef rho lam hrho hsum g (hx 0) (hq0 0)
  have hdet (i : ℕ) : IsUnit (1 - H i * K).det :=
    cavity_finite_tilt_isUnit rho lam hrho hsum B hB g (x i) (hx i)
  have hΔ (i : ℕ) : H i - H (i + 1) = chainExponent cut i • S i :=
    cavityFiniteNoiseCovariance_delta rho lam hrho hsum g p cut hcut hfirst q i
  have hA := cavity_finite_spectral_upper lam a ha B hB
  have hQ (i : ℕ) : (cavityFactorPrecision
      (chainExponent cut i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef :=
    cavityFiniteCovariance_step_precision rho lam hrho hsum g _ a hK hA
      (hx (i + 1)) (hxm (Nat.le_succ i)) (finite_chainExponent_pos cut hcut hfirst i).le
      (S i) (hS i) (hΔ i)
  have hR : (H n).PosSemidef :=
    (cavityFiniteCovariancePath_posDef rho lam hrho hsum g p cut hfirst hlast q hq hp htop n).posSemidef
  have hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef :=
    cavityFiniteCovariance_terminal_precision rho lam hrho hsum g _ a (fun i => ha (g i)) hK hA (hx n)
  have hAtom (i : ℕ) (hi : i < n) :
      NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S i)) :=
    cavityFiniteNoiseCovariance_atomless rho lam hrho hsum g p cut hcut hfirst hlast
      q hq hp htop hd i hi
  have hcov (i : ℕ) (hi : i < n) :
      L.transpose * ((1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) * L =
        (fieldStepVariance h i : ℝ) • 1 := by
    let k : Fin n := ⟨i, hi⟩
    have he := cavity_finite_projected_innovation rho lam hrho hsum B hB hBE hcomplete g
      (x i) (x (i + 1)) (chainExponent cut i) (hx i) (hx (i + 1))
      (finite_chainExponent_pos cut hcut hfirst i).ne' (S i) (hΔ i)
    change L.transpose * ((1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) * L = _ at he
    rw [he]
    have hv := cavityFieldStep_variance rho lam hrho hsum p cut hcut hfirst hlast
      q hq hq0 hp htop k
    change (fieldStepVariance h i : ℝ) = _ at hv
    rw [hv]
    simp only [x, cavityFiniteDeficitPath, show i = (k : ℕ) from rfl,
      cavityFiniteLevel_castSucc, cavityFiniteLevel_succ]
    rw [chainExponent_apply cut k.isLt]
    rfl
  have hnonneg : 0 ≤ finiteR rho lam hrho hsum (x n) - c := by
    apply sub_nonneg.mpr
    have hc : c = ∑ a, rho a * lam a := by simp [c, finiteR]
    rw [hc]
    exact mean_le_finiteR rho lam hrho hsum (hx n)
  let v : ℝ≥0 := (finiteR rho lam hrho hsum (x n) - c).toNNReal
  have hres : L.transpose * cavityResolvent K (H n) * L = (v : ℝ) • 1 := by
    rw [show (v : ℝ) = finiteR rho lam hrho hsum (x n) - c from Real.coe_toNNReal _ hnonneg]
    exact cavity_finite_projected_residual rho lam hrho hsum B hB hBE hcomplete g (x n) (hx n)
  have hroot : L.transpose * ((1 - H 0 * K)⁻¹ * S₀ * ((1 - H 0 * K)⁻¹).transpose) * L =
      h.height 0 • 1 := by
    have hv := cavityFieldStep_root_variance rho lam hrho hsum p cut hcut hfirst hlast
      q hq.monotone hq0 hp htop
    change h.height 0 = _ at hv
    have hroot := cavity_finite_projected_scaled_root rho lam hrho hsum B hB hBE hcomplete
      g (x 0) (q 0) (hx 0)
    change L.transpose * ((1 - H 0 * K)⁻¹ * S₀ * ((1 - H 0 * K)⁻¹).transpose) * L = _ at hroot
    rw [hroot, hv]
    simp only [x, cavityFiniteDeficitPath, cavityFiniteLevel_zero]
  have he := cavity_full_spin_test_evaluation hpub hN h K H S S₀ hS₀ L c hK hH hS
    (fun i => field_chainExponent_pos h i) hdet hΔ hQ hR hQR hAtom v hcov hres hroot q Φ j hΦ
  apply he.trans
  apply integral_congr_ae
  filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with t ht
  obtain ⟨i, hi⟩ := ht
  have hindex : fieldLevelIndex h t = i := fieldLevelIndex_on_cell h i hi
  rw [hindex, hp i t hi]

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_finite_spin_test_oai := @OAI.InvariantIsing.cavity_finite_spin_test_oai
