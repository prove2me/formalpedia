-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Geometry.MetricGreenData.regularizedHessianGreen
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:42:33.536058+00:00
-- url     : https://prove2.me/submissions/8b93d550-9bea-41a9-a518-76ef83daed91

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C016
import Definitions.Def_OAIQ091C018
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_coupling_matrix_coordinates
import Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_localWeightedHessian
import Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_matrixGreen
import Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_plusCurvatureGreen
import Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_traceGreen

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientCoordinateModel
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed twelve real coordinates for the inner generators in the cost calculation. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian
set_option maxHeartbeats 1000000

/-- The fixed coordinates cover every trace-free Bianchi tensor. -/
theorem exists_costParameters (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    ∃ v : Fin 3 → Vec, costParameters v = Z := by
  refine ⟨![radialCoordinate costShape Z, secondCoordinate costShape Z, thirdCoordinate costShape Z], ?_⟩
  exact parameters_reconstruction costShape Z hz hb


end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientPairing
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bilinear compression on the actual Bianchi gradient space. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

theorem gradientCouplingKernel_symmetric (p q : GradientIndex) :
    gradientCouplingKernel p q = gradientCouplingKernel q p := by
  unfold gradientCouplingKernel
  apply Finset.sum_congr rfl
  intro s _
  rw [quaternionMatrix_skew s p.1 q.1,
    rotation_skew s p.2.1 q.2.1, rotation_skew s p.2.2 q.2.2]
  simp only [eq_comm (a := q.2.1) (b := p.2.1),
    eq_comm (a := q.2.2) (b := p.2.2)]
  split_ifs <;> ring

theorem rawCoupling_selfadjoint (Z W : RawGradient) :
    rawPairing (rawCoupling Z) W = rawPairing Z (rawCoupling W) := by
  simp only [rawPairing, rawCoupling_coordinates, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [gradientCouplingKernel_symmetric q p]
  ring

theorem rawPairing_smul_left (r : ℝ) (Z W : RawGradient) :
    rawPairing (r • Z) W = r * rawPairing Z W := by
  change (∑ p : GradientIndex, (r * rawCoordinates Z p) * rawCoordinates W p) = _
  simp only [mul_assoc, rawPairing, ← Finset.mul_sum]

theorem rawPairing_smul_right (r : ℝ) (Z W : RawGradient) :
    rawPairing Z (r • W) = r * rawPairing Z W := by
  change (∑ p : GradientIndex, rawCoordinates Z p * (r * rawCoordinates W p)) = _
  simp only [mul_left_comm, rawPairing, ← Finset.mul_sum]

theorem rawPairing_sub_left (Z W U : RawGradient) :
    rawPairing (Z - W) U = rawPairing Z U - rawPairing W U := by
  change (∑ p : GradientIndex,
    (rawCoordinates Z p - rawCoordinates W p) * rawCoordinates U p) = _
  simp only [sub_mul, rawPairing, Finset.sum_sub_distrib]

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureContraction
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quaternion contractions in the derivative-slot Green formula. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open TraceHessian Bianchi Angular

noncomputable section

theorem mixed_twoForm_pairing (s r : Fin 3) :
    (∑ i, ∑ k, quaternionMatrix s i k * oppositeMatrix r i k) = 0 := by
  simp only [Fin.sum_univ_succ]
  fin_cases s <;> fin_cases r <;>
    simp [TraceHessian.quaternionMatrix, oppositeMatrix, Geometry.oppositeQuaternion] <;>
      (try split_ifs) <;> norm_num

end

end PositiveEinsteinFour.CurvatureContraction

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OperatorGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted integration by parts retains the derivative of a varying
matrix-slot coefficient. The Weyl Hessian calculation applies the flow Green identity twice
to the nonparallel coefficient. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

variable {Ω E : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (μ : Measure Ω) [IsFiniteMeasure μ]

/-- A variable scalar tensor coefficient contributes its divergence term.
Summing this identity is the derivative-slot curvature integration step. -/
theorem weighted_scalar_coefficient_green
    (φ : ℝ → Ω ≃ᵐ Ω)
    (hφ : Continuous (fun p : ℝ × Ω => φ p.1 p.2))
    (hμ : ∀ t, MeasurePreserving (φ t) μ μ)
    (m dm a da : C(Ω, ℝ)) (f df g dg : C(Ω, E))
    (hm : ∀ t x, HasDerivAt (fun s => m (φ s x)) (dm (φ t x)) t)
    (ha : ∀ t x, HasDerivAt (fun s => a (φ s x)) (da (φ t x)) t)
    (hf : ∀ t x, HasDerivAt (fun s => f (φ s x)) (df (φ t x)) t)
    (hg : ∀ t x, HasDerivAt (fun s => g (φ s x)) (dg (φ t x)) t) :
    (∫ x, m x * a x * inner ℝ (f x) (dg x) +
      dm x * a x * inner ℝ (f x) (g x) ∂μ) =
      -(∫ x, m x * a x * inner ℝ (df x) (g x) ∂μ) -
        ∫ x, m x * da x * inner ℝ (f x) (g x) ∂μ := by
  let w : C(Ω, ℝ) := ⟨fun x => m x * a x, by fun_prop⟩
  let dw : C(Ω, ℝ) := ⟨fun x => dm x * a x + m x * da x, by fun_prop⟩
  have hw (t : ℝ) (x : Ω) :
      HasDerivAt (fun s => w (φ s x)) (dw (φ t x)) t := (hm t x).mul (ha t x)
  have h := weighted_flow_green μ φ hφ hμ w dw f df g dg hw hf hg
  have hA : Integrable (fun x => m x * a x * inner ℝ (f x) (dg x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hB : Integrable (fun x => dm x * a x * inner ℝ (f x) (g x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hJ : Integrable (fun x => m x * a x * inner ℝ (df x) (g x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hK : Integrable (fun x => m x * da x * inner ℝ (f x) (g x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (fun x => w x * inner ℝ (df x) (g x) + dw x * inner ℝ (f x) (g x)) =
      (fun x => (m x * a x * inner ℝ (df x) (g x) +
        dm x * a x * inner ℝ (f x) (g x)) + m x * da x * inner ℝ (f x) (g x)) := by
    funext x
    dsimp [w, dw]
    ring
  have hJB : Integrable (fun x => m x * a x * inner ℝ (df x) (g x) +
      dm x * a x * inner ℝ (f x) (g x)) μ := hJ.add hB
  rw [he, integral_add hJB hK, integral_add hJ hB] at h
  change _ = -(∫ x, m x * a x * inner ℝ (f x) (dg x) ∂μ) at h
  rw [integral_add hA hB]
  linarith

end

end PositiveEinsteinFour.Averages

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative-slot curvature integration. Divergence freedom removes
the differentiated coefficient, and skew-symmetry leaves exactly one half
of the covariant commutator. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

variable {Ω E : Type*} [TopologicalSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem divergence_sum_zero
    (A : CurvatureIndex → C(Ω, ℝ)) (X : Fin 4 → Fin 4 → C(Ω, E))
    (Z : Fin 4 → C(Ω, E))
    (hdiv : ∀ i j l x, (∑ k, A ((i, k), (j, l)) x) = 0) (x : Ω) :
    (∑ p : CurvatureIndex, A p x * inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) = 0 := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i _
  calc
    _ = ∑ j, ∑ k, ∑ l, A ((i, k), (j, l)) x * inner ℝ (X i j x) (Z l x) :=
      Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ k, A ((i, k), (j, l)) x * inner ℝ (X i j x) (Z l x) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = 0 := by
      simp_rw [← Finset.sum_mul, hdiv, zero_mul]
      simp

private theorem skew_commutator_sum
    (A : CurvatureIndex → C(Ω, ℝ))
    (D : Fin 4 → Fin 4 → Fin 4 → C(Ω, E)) (Z : Fin 4 → C(Ω, E))
    (hskew : ∀ i k j l x, A ((k, i), (j, l)) x = -A ((i, k), (j, l)) x)
    (x : Ω) :
    -(∑ p : CurvatureIndex, A p x *
      inner ℝ (D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x)) =
      (1 / 2 : ℝ) * (∑ p : CurvatureIndex, A p x *
        inner ℝ (D p.1.1 p.1.2 p.2.1 x - D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x)) := by
  have hs : (∑ p : CurvatureIndex, A p x *
      inner ℝ (D p.1.1 p.1.2 p.2.1 x) (Z p.2.2 x)) =
      -(∑ p : CurvatureIndex, A p x *
        inner ℝ (D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x)) := by
    calc
      _ = ∑ p : CurvatureIndex, A (outerSwap p) x *
          inner ℝ (D (outerSwap p).1.1 (outerSwap p).1.2 (outerSwap p).2.1 x)
            (Z (outerSwap p).2.2 x) := (outerSwap.sum_comp _).symm
      _ = _ := by
        change (∑ p : CurvatureIndex, A ((p.1.2, p.1.1), p.2) x *
          inner ℝ (D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x)) = _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro p _
        rw [hskew]
        ring
  simp_rw [inner_sub_left, mul_sub, Finset.sum_sub_distrib]
  rw [hs]
  ring

variable [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Integrating a divergence-free curvature coefficient leaves the precise
half-commutator term. All first-derivative weight terms are retained. -/
theorem weighted_curvature_green
    (φ : Fin 4 → ℝ → Ω ≃ᵐ Ω)
    (hφ : ∀ k, Continuous (fun p : ℝ × Ω => φ k p.1 p.2))
    (hμ : ∀ k t, MeasurePreserving (φ k t) μ μ)
    (m : C(Ω, ℝ)) (dm : Fin 4 → C(Ω, ℝ))
    (A dA : CurvatureIndex → C(Ω, ℝ))
    (Z : Fin 4 → C(Ω, E)) (X : Fin 4 → Fin 4 → C(Ω, E))
    (D : Fin 4 → Fin 4 → Fin 4 → C(Ω, E))
    (hdiv : ∀ i j l x, (∑ k, dA ((i, k), (j, l)) x) = 0)
    (hskew : ∀ i k j l x, A ((k, i), (j, l)) x = -A ((i, k), (j, l)) x)
    (hm : ∀ k t x, HasDerivAt (fun s => m (φ k s x)) (dm k (φ k t x)) t)
    (hA : ∀ p t x, HasDerivAt (fun s => A p (φ p.1.2 s x)) (dA p (φ p.1.2 t x)) t)
    (hZ : ∀ k j t x, HasDerivAt (fun s => Z j (φ k s x)) (X k j (φ k t x)) t)
    (hX : ∀ k i j t x, HasDerivAt (fun s => X i j (φ k s x)) (D k i j (φ k t x)) t) :
    (∫ x, ∑ p : CurvatureIndex,
      (m x * A p x * inner ℝ (X p.1.1 p.2.1 x) (X p.1.2 p.2.2 x) +
        dm p.1.2 x * A p x * inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) ∂μ) =
      (1 / 2 : ℝ) * (∫ x, ∑ p : CurvatureIndex, m x * A p x *
        inner ℝ (D p.1.1 p.1.2 p.2.1 x - D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x) ∂μ) := by
  have hL (p : CurvatureIndex) : Integrable (fun x =>
      m x * A p x * inner ℝ (X p.1.1 p.2.1 x) (X p.1.2 p.2.2 x) +
        dm p.1.2 x * A p x * inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hJ (p : CurvatureIndex) : Integrable (fun x => m x * A p x *
      inner ℝ (D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hK (p : CurvatureIndex) : Integrable (fun x => m x * dA p x *
      inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs : (∫ x, ∑ p : CurvatureIndex,
      (m x * A p x * inner ℝ (X p.1.1 p.2.1 x) (X p.1.2 p.2.2 x) +
        dm p.1.2 x * A p x * inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) ∂μ) =
      -(∫ x, ∑ p : CurvatureIndex, m x * A p x *
        inner ℝ (D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x) ∂μ) -
      (∫ x, ∑ p : CurvatureIndex, m x * dA p x *
        inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x) ∂μ) := by
    rw [integral_finsetSum _ (fun p _ => hL p),
      integral_finsetSum _ (fun p _ => hJ p),
      integral_finsetSum _ (fun p _ => hK p)]
    simp_rw [weighted_scalar_coefficient_green μ _ (hφ _) (hμ _) m (dm _) (A _) (dA _)
      (X _ _) (D _ _ _) (Z _) (X _ _) (hm _) (hA _) (hX _ _ _) (hZ _ _)]
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hz : (∫ x, ∑ p : CurvatureIndex, m x * dA p x *
      inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x) ∂μ) = 0 := by
    have he (x : Ω) : (∑ p : CurvatureIndex, m x * dA p x *
        inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) = 0 := by
      simp_rw [mul_assoc, ← Finset.mul_sum, divergence_sum_zero dA X Z hdiv x, mul_zero]
    simp_rw [he]
    simp
  rw [hs, hz, sub_zero, ← integral_neg, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have h := skew_commutator_sum A D Z hskew x
  have hm' := congrArg (fun z : ℝ => m x * z) h
  rw [mul_left_comm (m x) (1 / 2 : ℝ)] at hm'
  simpa only [mul_neg, Finset.mul_sum, mul_assoc] using hm'

end

end PositiveEinsteinFour.Averages

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricBianchi
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instNonemptyOrthonormalFrame _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Weyl gradient, with its derivative index treated as a tangent
vector. These changes of coordinate retain every component: neither the
Bianchi equation nor a differential estimate is built into the definition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular Bianchi TraceHessian
open scoped Manifold ContDiff

noncomputable section

/-- The tensor norm is precisely the ordinary covariant-gradient norm. -/
theorem gradientTensor_squaredNorm (Z : Gradient) (hs : ∀ i, symmetric (Z i)) :
    (gradientTensor Z).squaredNorm = gradientSquareNorm Z := by
  unfold Tensor.squaredNorm
  simp_rw [gradientTensor_matrix Z hs, EuclideanSpace.real_norm_sq_eq]
  change (∑ a, ∑ b, ∑ i, Z i a b ^ 2) = ∑ i, ∑ a, ∑ b, Z i a b ^ 2
  calc
    _ = ∑ a, ∑ i, ∑ b, Z i a b ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem plusGradientTensor_squaredNorm (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (hs : ∀ i, symmetric (plusWeylGradient g c e i)) :
    (plusGradientTensor g c e).squaredNorm =
      gradientSquareNorm (plusWeylGradient g c e) :=
  gradientTensor_squaredNorm _ hs

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricHessian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted rough-Laplacian identity for the metric's actual Weyl
gradient. Differentiation takes place in the coordinate connection before
the parallel frame is applied. The integration identity follows from
frame-flow invariance, rather than an assumed Hessian integral formula. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular TraceHessian
open scoped Manifold ContDiff

noncomputable section

theorem gradientVector_norm_sq (Z : Gradient) :
    ‖gradientVector Z‖ ^ 2 = gradientSquareNorm Z := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ p : Fin 4 × Fin 3 × Fin 3, Z p.1 p.2.1 p.2.2 ^ 2) = _
  simp only [Fintype.sum_prod_type, gradientSquareNorm, squareNorm]

theorem gradientVector_hessian_norm (X : Hessian) :
    (∑ i, ‖gradientVector (X i)‖ ^ 2) = hessianNormSq X := by
  simp_rw [gradientVector_norm_sq]
  rw [← hessianPairing_self]
  simpa only [gradientSquareNorm, squareNorm, Fintype.sum_prod_type,
    tensorCoordinates, pow_two] using tensorCoordinates_pairing X X

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Weighted integration by parts for the actual covariant Hessian. The
classical parallel-frame differentiation identities and measure-preserving
flows are explicit; no new weighted estimate is a hypothesis. -/
theorem weighted_metric_hessian_green
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (φ : Fin 4 → FrameFlow g μ)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hZ : Continuous (frameGradientVector g))
    (hX : ∀ i, Continuous (frameHessianVector g i))
    (hXX : ∀ i, Continuous (frameThirdVector g i i))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((φ i).map s e))
      (dm i ((φ i).map t e)) t)
    (hZd : ∀ i t e, HasDerivAt (fun s => frameGradientVector g ((φ i).map s e))
      (frameHessianVector g i ((φ i).map t e)) t)
    (hXd : ∀ i t e, HasDerivAt (fun s => frameHessianVector g i ((φ i).map s e))
      (frameThirdVector g i i ((φ i).map t e)) t) :
    (∫ e, m e * hessianNormSq (plusWeylHessian g e.base e.frame) +
      ∑ i, dm i e * inner ℝ (frameGradientVector g e) (frameHessianVector g i e) ∂μ) =
      -(∫ e, m e * inner ℝ (frameGradientVector g e) (frameGradientLaplacian g e) ∂μ) := by
  have h := Averages.weighted_four_direction_green μ
    (fun i => (φ i).map) (fun i => (φ i).continuous) (fun i => (φ i).preserves)
    m dm ⟨frameGradientVector g, hZ⟩
    (fun i => ⟨frameHessianVector g i, hX i⟩)
    (fun i => ⟨frameThirdVector g i i, hXX i⟩) hm hZd hXd
  simpa only [ContinuousMap.coe_mk, frameHessianVector, gradientVector_hessian_norm,
    frameGradientLaplacian] using h

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeneralMatrixCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bianchi compression for an arbitrary symmetric trace-free Weyl matrix,
with no choice of a moving diagonal frame. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- The full coefficient matrix satisfies the same coupling identity as
the diagonal specialization. The proof uses the actual twelve-dimensional
Bianchi coordinates and the five free entries of the symmetric matrix. -/
theorem rawCoupling_generalMatrixAction (A : Mat)
    (hA : symmetric A) (hAt : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    rawCoupling (generalMatrixAction A Z.matrix) =
      (-(1 / 2 : ℝ)) • generalMixedAction A Z.matrix := by
  obtain ⟨v, rfl⟩ := exists_costParameters Z hz hb
  rw [← coordinates_eq A hA hAt]
  exact coupling_matrix_coordinates _ _ _ _ _ v

theorem rawBianchiProjection_pairing (Z : RawGradient) (W : Tensor) (hbw : W.bianchi) :
    rawPairing (rawBianchiProjection Z) W.matrix = rawPairing Z W.matrix := by
  have hW : rawCoupling W.matrix = (-4 : ℝ) • W.matrix := by
    funext a b
    exact gradientCoupling_eq W hbw a b
  unfold rawBianchiProjection
  rw [rawPairing_smul_left, rawPairing_sub_left, rawPairing_smul_left,
    rawCoupling_selfadjoint, hW, rawPairing_smul_right]
  ring

/-- The uncompressed Ricci expression equals 13Z−20P(B_F(A)Z) as
an actual four-vector-valued array, for arbitrary Weyl coefficients. -/
theorem generalRicci_compression (A : Mat)
    (hA : symmetric A) (hAt : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    (13 : ℝ) • Z.matrix - (12 : ℝ) • generalMatrixAction A Z.matrix -
        generalMixedAction A Z.matrix =
      (13 : ℝ) • Z.matrix -
        (20 : ℝ) • rawBianchiProjection (generalMatrixAction A Z.matrix) := by
  unfold rawBianchiProjection
  rw [rawCoupling_generalMatrixAction A hA hAt Z hz hb]
  module

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HessianCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Curvature compression on all actual inner-Bianchi Hessian tensors. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem hessianPairing_slices (X Y : Hessian) :
    hessianPairing X Y = ∑ i, rawPairing (rawSlice X i) (rawSlice Y i) := by
  rw [← tensorCoordinates_pairing]
  simp only [Fintype.sum_prod_type, tensorCoordinates, rawPairing, rawCoordinates, rawSlice]

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HessianAssembly
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assembly of the actual weighted Hessian square and its Green contributions. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem weightedQuadratic_identity (m : ℝ) (X L : Hessian) :
    weightedQuadratic hessianNormSq m X L =
      (m * hessianNormSq X + hessianPairing X L) / 6 := by
  have hn : hessianNormSq (X + L) = hessianNormSq X + hessianNormSq L +
      2 * hessianPairing X L := by
    change (∑ a, ∑ b, ∑ i, ∑ j, (X i j a b + L i j a b) ^ 2) = _
    have hp (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by ring
    simp only [hp, hessianNormSq, hessianPairing, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  unfold weightedQuadratic
  rw [hn]
  ring

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricMinusGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The opposite curvature block acting on the plus Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory TraceHessian Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The derivative-slot Green formula on the actual metric tensors.
The third derivatives retain their order; the half factor is proved by
skewing the first two slots, before any Ricci substitution. -/
theorem weighted_metric_minus_curvature_green
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (φ : Fin 4 → FrameFlow g μ)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hA : ∀ p, Continuous (frameMinusCoefficient g p))
    (hDA : ∀ p, Continuous (frameMinusCoefficientDerivative g p))
    (hZ : ∀ j, Continuous (frameGradientSlice g j))
    (hX : ∀ i j, Continuous (frameHessianSlice g i j))
    (hD : ∀ i k j, Continuous (frameThirdSlice g i k j))
    (hdiv : ∀ i j l e, (∑ k, frameMinusCoefficientDerivative g ((i, k), (j, l)) e) = 0)
    (hskew : ∀ i k j l e, frameMinusCoefficient g ((k, i), (j, l)) e =
      -frameMinusCoefficient g ((i, k), (j, l)) e)
    (hm : ∀ k t e, HasDerivAt (fun s => m ((φ k).map s e)) (dm k ((φ k).map t e)) t)
    (hAd : ∀ p t e, HasDerivAt
      (fun s => frameMinusCoefficient g p ((φ p.1.2).map s e))
      (frameMinusCoefficientDerivative g p ((φ p.1.2).map t e)) t)
    (hZd : ∀ k j t e, HasDerivAt (fun s => frameGradientSlice g j ((φ k).map s e))
      (frameHessianSlice g k j ((φ k).map t e)) t)
    (hXd : ∀ k i j t e, HasDerivAt (fun s => frameHessianSlice g i j ((φ k).map s e))
      (frameThirdSlice g k i j ((φ k).map t e)) t) :
    (∫ e, ∑ p : Averages.CurvatureIndex,
      (m e * frameMinusCoefficient g p e *
        matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
          (plusWeylHessian g e.base e.frame p.1.2 p.2.2) +
        dm p.1.2 e * frameMinusCoefficient g p e *
          matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
            (plusWeylGradient g e.base e.frame p.2.2)) ∂μ) =
      (1 / 2 : ℝ) * (∫ e, ∑ p : Averages.CurvatureIndex,
        m e * frameMinusCoefficient g p e *
          inner ℝ (frameThirdSlice g p.1.1 p.1.2 p.2.1 e -
            frameThirdSlice g p.1.2 p.1.1 p.2.1 e)
            (frameGradientSlice g p.2.2 e) ∂μ) := by
  have h := Averages.weighted_curvature_green μ
    (fun k => (φ k).map) (fun k => (φ k).continuous) (fun k => (φ k).preserves)
    m dm (fun p => ⟨frameMinusCoefficient g p, hA p⟩)
    (fun p => ⟨frameMinusCoefficientDerivative g p, hDA p⟩)
    (fun j => ⟨frameGradientSlice g j, hZ j⟩)
    (fun i j => ⟨frameHessianSlice g i j, hX i j⟩)
    (fun i k j => ⟨frameThirdSlice g i k j, hD i k j⟩)
    hdiv hskew hm hAd hZd hXd
  simpa only [ContinuousMap.coe_mk, frameHessianSlice, frameGradientSlice,
    inner_matrixVector] using h


end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Differentiate the invariant matrix Weyl equation before choosing a
diagonal frame. The derivative of its quadratic term is exactly twice
the concrete matrix-slot operator. -/

namespace PositiveEinsteinFour.TraceHessian

open Matrix PositiveEinsteinFour.Geometry
open scoped BigOperators

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.TraceHessian.instNormedRingMat
attribute [local instance] OAI.PositiveEinsteinFour.TraceHessian.instNormedSpaceRealMat
attribute [local instance] OAI.PositiveEinsteinFour.TraceHessian.instNormedAlgebraRealMat
theorem matrixSlotAction_derivative (M Z : Mat) :
    Z * M + M * Z - (Matrix.trace (Z * M + M * Z) / 3) • (1 : Mat) =
      (2 : ℝ) • matrixSlotAction M Z := by
  rw [matrixSlotAction_eq, Matrix.trace_add, Matrix.trace_mul_comm Z M]
  ext a b
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem hasDerivAt_traceFreeSquare {T : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hT : HasDerivAt T Z t) :
    HasDerivAt (fun r => traceFreeSquare (T r))
      ((2 : ℝ) • matrixSlotAction (T t) Z) t := by
  have hP := hT.mul hT
  have htr := hasDerivAt_matrixTrace hP
  have h := hP.sub ((htr.div_const 3).smul_const (1 : Mat))
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  exact (matrixSlotAction_derivative (T t) Z).symm

/-- The differentiated weak Weyl equation is `6Z - 12 B_F(T)Z` in a
parallel frame, without differentiating eigenvectors or eigenvalues. -/
theorem hasDerivAt_weylLaplacian {T : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hT : HasDerivAt T Z t) :
    HasDerivAt (fun r => weylLaplacian (T r))
      ((6 : ℝ) • Z - (12 : ℝ) • matrixSlotAction (T t) Z) t := by
  have h := (hT.sub (hasDerivAt_traceFreeSquare hT)).const_smul (6 : ℝ)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  module

/-- Along a parallel frame, differentiate the Weyl equation derived from
Bianchi and the raw curvature commutator. The trace of the third derivative
is therefore a conclusion rather than another geometric input. -/
theorem third_trace_eq_of_bianchi_commutator
    (T : ℝ → Mat) (X : ℝ → Hessian) (D : Fin 4 → Mat) (Z : Mat) (r : ℝ)
    (hs : ∀ t, symmetric (T t)) (ht : ∀ t, traceFree (T t))
    (hm : ∀ t i j, symmetric (X t i j) ∧ traceFree (X t i j))
    (hb : ∀ t i s, HighestHessian.divergence (X t) i s = 0)
    (hc : ∀ t i j a b, X t i j a b - X t j i a b =
      bundleCurvatureAction (T t) i j (T t) a b)
    (hT : HasDerivAt T Z r)
    (hX : ∀ i, HasDerivAt (fun t => X t i i) (D i) r) :
    (∑ i, D i) = (6 : ℝ) • Z - (12 : ℝ) • matrixSlotAction (T r) Z := by
  have he : (fun t => ∑ i, X t i i) = fun t => weylLaplacian (T t) := by
    funext t
    exact weyl_trace_eq_of_bianchi_commutator (T t) (hs t) (ht t)
      (X t) (hm t) (hb t) (hc t)
  have hd : HasDerivAt (fun t => ∑ i, X t i i) (∑ i, D i) r :=
    HasDerivAt.fun_sum (fun i _ => hX i)
  rw [he] at hd
  exact hd.unique (hasDerivAt_weylLaplacian hT)

end
end PositiveEinsteinFour.TraceHessian
end


section

/-! Realize the invariant Weyl equation and its derivative on the actual
metric tensors. The inputs are the pointwise covariant Bianchi and Ricci
identities (Petersen, third edition, Section 3.1.1) and ordinary parallel
frame differentiation. No Weyl Laplacian equation is an input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local instance metricWeylNormedRing_r8d12cb_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricWeylNormedSpace_r8d12cb_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricWeylNormedAlgebra_r8d12cb_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
/-- Differentiate on parallel frames and then evaluate at any requested
frame. Surjectivity of the flow equivalence suffices; no chosen eigenframe
is differentiated. -/
theorem metric_weyl_third_trace (g : SmoothMetric M)
    (h : WeylCovariantIdentities g) {μ : Measure (FrameBundle g)}
    (φ : Fin 4 → FrameFlow g μ)
    (hT : ∀ k t e, HasDerivAt
      (fun s => plusWeyl g ((φ k).map s e).base ((φ k).map s e).frame)
      (plusWeylGradient g ((φ k).map t e).base ((φ k).map t e).frame k) t)
    (hX : ∀ k i t e, HasDerivAt
      (fun s => plusWeylHessian g ((φ k).map s e).base ((φ k).map s e).frame i i)
      (plusWeylThirdDerivative g ((φ k).map t e).base ((φ k).map t e).frame k i i) t)
    (k : Fin 4) (e : FrameBundle g) :
    (∑ i, plusWeylThirdDerivative g e.base e.frame k i i) =
      (6 : ℝ) • plusWeylGradient g e.base e.frame k -
        (12 : ℝ) • matrixSlotAction (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame k) := by
  obtain ⟨e₀, he⟩ := ((φ k).map 0).surjective e
  change (φ k).map 0 e₀ = e at he
  have hthird := third_trace_eq_of_bianchi_commutator
    (fun t => plusWeyl g ((φ k).map t e₀).base ((φ k).map t e₀).frame)
    (fun t => plusWeylHessian g ((φ k).map t e₀).base ((φ k).map t e₀).frame)
    (fun i => plusWeylThirdDerivative g ((φ k).map 0 e₀).base
      ((φ k).map 0 e₀).frame k i i)
    (plusWeylGradient g ((φ k).map 0 e₀).base ((φ k).map 0 e₀).frame k) 0
    (fun t => h.symmetric ((φ k).map t e₀))
    (fun t => h.traceFree ((φ k).map t e₀))
    (fun t => h.hessianMatrix ((φ k).map t e₀))
    (fun t => h.hessianBianchi ((φ k).map t e₀))
    (fun t => h.hessianCommutator ((φ k).map t e₀))
    (hT k 0 e₀) (fun i => hX k i 0 e₀)
  rw [he] at hthird
  exact hthird

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contract the two ordinary covariant commutation identities. These are
the slotwise Ricci identities of Petersen, Section 3.1.1; the new compressed
gradient equation is a consequence, not an assumed differential equation. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Bianchi

noncomputable section

theorem matrixRotation_slice (Z : Tensor) (s : Fin 3) (j : Fin 4) (a b : Fin 3) :
    matrixAction s (rawMatrixSlice Z.matrix j) a b = matrixRotation s Z a b j := by
  simp [rawMatrixSlice, matrixAction, matrixRotation, Fin.sum_univ_three]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The derivative of bundle curvature is divergence free by the
differential Bianchi equation for the actual Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian

noncomputable section

theorem bundleCurvatureDerivative_divergence (Z : Angular.Gradient)
    (hb : ∀ r i, gradientDivergence Z r i = 0) (j : Fin 4) (N : Mat) :
    (∑ i, bundleCurvatureDerivative (Z i) i j N) = 0 := by
  ext a b
  simp only [Matrix.sum_apply, bundleCurvatureDerivative, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum, Matrix.zero_apply]
  calc
    _ = ∑ i, ∑ s, ∑ r, (1 / 2 : ℝ) *
        (quaternionMatrix r i j * (Z i r s * matrixAction s N a b)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ s, ∑ i, ∑ r, (1 / 2 : ℝ) *
        (quaternionMatrix r i j * (Z i r s * matrixAction s N a b)) := Finset.sum_comm
    _ = ∑ s, ∑ r, ∑ i, (1 / 2 : ℝ) *
        (quaternionMatrix r i j * (Z i r s * matrixAction s N a b)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
    _ = ∑ s, -(1 / 2 : ℝ) * gradientDivergence Z s j * matrixAction s N a b := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [gradientDivergence, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      rw [quaternionMatrix_skew r i j]
      ring
    _ = 0 := by simp only [hb, mul_zero, zero_mul, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weighted tensor forms and the actual Green integrands use the same
normalization, including the unsymmetrized weight derivative. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem rawSlice_weightTensor (a : Vec) (Z : Tensor) (i : Fin 4) :
    rawSlice (weightTensor a Z) i = a i • Z.matrix := by
  funext b c
  ext j
  rfl

theorem gradientVector_rawSlice (X : Hessian) (i : Fin 4) :
    rawGradientVector (rawSlice X i) = gradientVector (X i) := rfl

theorem hessianPairing_weightTensor (X : Hessian) (a : Vec) (Z : Tensor) :
    hessianPairing X (weightTensor a Z) =
      ∑ i, a i * inner ℝ (tensorGradientVector Z) (gradientVector (X i)) := by
  rw [hessianPairing_slices]
  simp_rw [rawSlice_weightTensor, rawPairing_smul_right,
    ← inner_rawGradientVector, gradientVector_rawSlice]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm]
  rfl

/-- The identity-operator term of the local weighted square is precisely
one sixth of the actual rough-Laplacian Green integrand. -/
theorem weightedQuadratic_identity_green (X : Hessian) (a : Vec) (Z : Tensor) (m : ℝ) :
    weightedQuadratic hessianNormSq m X (weightTensor a Z) =
      (m * hessianNormSq X +
        ∑ i, a i * inner ℝ (tensorGradientVector Z) (gradientVector (X i))) / 6 := by
  rw [weightedQuadratic_identity, hessianPairing_weightTensor]

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! Contract the raw bundle and covector actions appearing in the
derivative-slot Green identity. These are finite tensor contractions,
before integration and before any estimate. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open TraceHessian Bianchi PositiveEinsteinFour.Geometry

noncomputable section

theorem matrixSlice_self_sum (Z : Tensor) :
    (∑ j, matrixPairing (rawMatrixSlice Z.matrix j) (rawMatrixSlice Z.matrix j)) =
      Z.squaredNorm := by
  calc
    _ = rawPairing Z.matrix Z.matrix := by
      simp only [matrixPairing, rawMatrixSlice, rawPairing, rawCoordinates,
        Fintype.sum_prod_type]
    _ = Z.squaredNorm := by
      simp only [rawPairing_vectors, real_inner_self_eq_norm_sq, Tensor.squaredNorm]

end
end PositiveEinsteinFour.CurvatureContraction
end


section

/-! The complete raw Ricci commutator in the derivative-slot Green
integrand. The bundle and covector contractions are both retained. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open TraceHessian Bianchi PositiveEinsteinFour.Geometry MeasureTheory

noncomputable section

theorem matrixPairing_add_left (A B N : Mat) :
    matrixPairing (A + B) N = matrixPairing A N + matrixPairing B N :=
  (matrixPairingLinear N).map_add A B

theorem matrixPairing_sub_left (A B N : Mat) :
    matrixPairing (A - B) N = matrixPairing A N - matrixPairing B N :=
  (matrixPairingLinear N).map_sub A B

end
end PositiveEinsteinFour.CurvatureContraction
end


section

/-! Polarization of the actual derivative-slot Green integrands. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Bianchi TraceHessian PositiveEinsteinFour.Geometry
open CurvatureContraction

noncomputable section

private theorem matrix_pairing_comm (X Y : Mat) : matrixPairing X Y = matrixPairing Y X := by
  simp only [matrixPairing, mul_comm]

private theorem matrix_pairing_add_left (X Y Z : Mat) :
    matrixPairing (X + Y) Z = matrixPairing X Z + matrixPairing Y Z := by
  simp only [matrixPairing, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

private theorem matrix_pairing_add_right (X Y Z : Mat) :
    matrixPairing X (Y + Z) = matrixPairing X Y + matrixPairing X Z := by
  simp only [matrixPairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem derivativePairing_add_left (A : DerivativeCoefficient) (X Y Z : Hessian) :
    derivativePairing A (X + Y) Z = derivativePairing A X Z + derivativePairing A Y Z := by
  simp only [derivativePairing, Pi.add_apply, matrix_pairing_add_left,
    mul_add, Finset.sum_add_distrib]

theorem derivativePairing_add_right (A : DerivativeCoefficient) (X Y Z : Hessian) :
    derivativePairing A X (Y + Z) = derivativePairing A X Y + derivativePairing A X Z := by
  simp only [derivativePairing, Pi.add_apply, matrix_pairing_add_right,
    mul_add, Finset.sum_add_distrib]

theorem derivativePairing_comm (A : DerivativeCoefficient)
    (hA : ∀ i k j l, A k i l j = A i k j l) (X Y : Hessian) :
    derivativePairing A X Y = derivativePairing A Y X := by
  let swap : Averages.CurvatureIndex ≃ Averages.CurvatureIndex :=
    Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _)
  unfold derivativePairing
  calc
    _ = ∑ p : Averages.CurvatureIndex,
        A (swap p).1.1 (swap p).1.2 (swap p).2.1 (swap p).2.2 *
          matrixPairing (X (swap p).1.1 (swap p).2.1) (Y (swap p).1.2 (swap p).2.2) :=
      (swap.sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      change A p.1.2 p.1.1 p.2.2 p.2.1 * matrixPairing (X p.1.2 p.2.2) (Y p.1.1 p.2.1) = _
      rw [hA, matrix_pairing_comm]

theorem weightedQuadratic_derivativePairing (A : DerivativeCoefficient)
    (hA : ∀ i k j l, A k i l j = A i k j l) (m : ℝ) (X Y : Hessian) :
    weightedQuadratic (fun W => derivativePairing A W W) m X Y =
      (m * derivativePairing A X X + derivativePairing A X Y) / 6 := by
  unfold weightedQuadratic
  dsimp only
  rw [derivativePairing_add_left, derivativePairing_add_right,
    derivativePairing_add_right, derivativePairing_comm A hA Y X]
  ring

theorem derivativePairing_weightTensor (A : DerivativeCoefficient)
    (X : Hessian) (a : Vec) (Z : Tensor) :
    derivativePairing A X (weightTensor a Z) =
      ∑ p : Averages.CurvatureIndex,
        a p.1.2 * A p.1.1 p.1.2 p.2.1 p.2.2 *
          matrixPairing (X p.1.1 p.2.1) (rawMatrixSlice Z.matrix p.2.2) := by
  apply Finset.sum_congr rfl
  intro p _
  change A p.1.1 p.1.2 p.2.1 p.2.2 *
      (∑ b, ∑ c, X p.1.1 p.2.1 b c * (a p.1.2 * Z.matrix b c p.2.2)) = _
  simp only [matrixPairing, rawMatrixSlice, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- The unsymmetrized weight tensor gives exactly the derivative-of-weight
term in the geometric Green formula, with no outer-slot symmetry premise. -/
theorem weightedQuadratic_derivative_green (A : DerivativeCoefficient)
    (hA : ∀ i k j l, A k i l j = A i k j l)
    (m : ℝ) (X : Hessian) (a : Vec) (Z : Tensor) :
    weightedQuadratic (fun W => derivativePairing A W W) m X (weightTensor a Z) =
      (∑ p : Averages.CurvatureIndex,
        (m * A p.1.1 p.1.2 p.2.1 p.2.2 *
          matrixPairing (X p.1.1 p.2.1) (X p.1.2 p.2.2) +
          a p.1.2 * A p.1.1 p.1.2 p.2.1 p.2.2 *
            matrixPairing (X p.1.1 p.2.1) (rawMatrixSlice Z.matrix p.2.2))) / 6 := by
  rw [weightedQuadratic_derivativePairing A hA, derivativePairing_weightTensor]
  simp only [derivativePairing, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The Ricci-commuted gradient equation for the actual metric. The two
classical slot identities remain explicit, while the differentiated trace
and curvature-divergence equations are derived. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance metricRicciNormedRing_r8d12cb_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricRicciNormedSpace_r8d12cb_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricRicciNormedAlgebra_r8d12cb_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem rawMatrixSlice_gradientTensor (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (j : Fin 4) :
    rawMatrixSlice (gradientTensor Z).matrix j = Z j := by
  ext a b
  simp only [rawMatrixSlice, gradientTensor_matrix Z hs]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Ricci commutation before any pointwise spectral decomposition. All
matrix and derivative slots stay in the same arbitrary orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem third_laplacian_eq_invariantRicciGradient
    (A : Mat) (Z : Angular.Gradient)
    (D V : Fin 4 → Fin 4 → Fin 4 → Mat)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hinner : ∀ i k j, D i k j - D i j k =
      V i k j + bundleCurvatureAction A k j (Z i))
    (houter : ∀ i k j, D i k j - D k i j =
      bundleCurvatureAction A i k (Z j) + ∑ a, R i k j a • Z a)
    (hdiv : ∀ j, (∑ i, V i i j) = 0)
    (hRic : ∀ j a, (∑ i, R i j i a) = if j = a then 3 else 0)
    (htrace : ∀ j, (∑ i, D j i i) =
      (6 : ℝ) • Z j - (12 : ℝ) • matrixSlotAction A (Z j)) :
    (fun j => ∑ i, D i i j) = invariantRicciGradient A Z := by
  funext j
  ext a b
  have hi (i : Fin 4) : D i i j a b = D j i i a b + V i i j a b +
      2 * bundleCurvatureAction A i j (Z i) a b +
        ∑ k, R i j i k * Z k a b := by
    have h1 := congrArg (fun N : Mat => N a b) (hinner i i j)
    have h2 := congrArg (fun N : Mat => N a b) (houter i j i)
    simp only [Matrix.sub_apply, Matrix.add_apply] at h1
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul] at h2
    linarith
  have hv := congrArg (fun N : Mat => N a b) (hdiv j)
  have ht := congrArg (fun N : Mat => N a b) (htrace j)
  simp only [Matrix.sum_apply, Matrix.zero_apply] at hv
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul] at ht
  have hr : (∑ i, ∑ k, R i j i k * Z k a b) = 3 * Z j a b := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hRic, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  simp only [Matrix.sum_apply, hi, Finset.sum_add_distrib, ← Finset.mul_sum,
    invariantRicciGradient, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [hv, hr, ht]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The actual Ricci equation uses just the ordinary covariant slot
identities and parallel differentiation. In particular it has no choice
of eigenframe among its hypotheses. -/
theorem metric_invariant_ricci_gradient
    (g : SmoothMetric M) (h : WeylCovariantIdentities g)
    {μ : Measure (FrameBundle g)} (φ : Fin 4 → FrameFlow g μ)
    (hT : ∀ k r e, HasDerivAt
      (fun s => plusWeyl g ((φ k).map s e).base ((φ k).map s e).frame)
      (plusWeylGradient g ((φ k).map r e).base ((φ k).map r e).frame k) r)
    (hX : ∀ k i r e, HasDerivAt
      (fun s => plusWeylHessian g ((φ k).map s e).base ((φ k).map s e).frame i i)
      (plusWeylThirdDerivative g ((φ k).map r e).base ((φ k).map r e).frame k i i) r)
    (e : FrameBundle g) (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hb : ∀ r i, gradientDivergence (plusWeylGradient g e.base e.frame) r i = 0)
    (hinner : ∀ i k j,
      plusWeylThirdDerivative g e.base e.frame i k j -
        plusWeylThirdDerivative g e.base e.frame i j k =
      bundleCurvatureDerivative (plusWeylGradient g e.base e.frame i) k j
        (plusWeyl g e.base e.frame) +
      bundleCurvatureAction (plusWeyl g e.base e.frame) k j
        (plusWeylGradient g e.base e.frame i))
    (houter : ∀ i k j,
      plusWeylThirdDerivative g e.base e.frame i k j -
        plusWeylThirdDerivative g e.base e.frame k i j =
      bundleCurvatureAction (plusWeyl g e.base e.frame) i k
        (plusWeylGradient g e.base e.frame j) +
      ∑ a, R i k j a • plusWeylGradient g e.base e.frame a)
    (hRic : ∀ j a, (∑ i, R i j i a) = if j = a then 3 else 0) :
    (fun j => ∑ i, plusWeylThirdDerivative g e.base e.frame i i j) =
      invariantRicciGradient (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) := by
  apply third_laplacian_eq_invariantRicciGradient _ _ _
    (fun i k j => bundleCurvatureDerivative (plusWeylGradient g e.base e.frame i)
      k j (plusWeyl g e.base e.frame)) R hinner houter
  · intro j
    exact bundleCurvatureDerivative_divergence _ hb j _
  · exact hRic
  · exact fun j => metric_weyl_third_trace g h φ hT hX j e

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth norm regularization for the actual squared Weyl weight.
The positive regularization parameter allows the Green identities to be
used at Weyl zeros as well as on the positive-norm set. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian Filter
open scoped _root_.Topology

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.smoothWeylNormedRing
local instance smoothWeylNormedSpace_r8d12cb_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.smoothWeylNormedAlgebra
theorem regularizedBlockNorm_le (ε : ℝ) (hε : 0 ≤ ε) (A : Mat) :
    regularizedBlockNorm ε A ≤ normalizedBlockNorm A + ε := by
  rw [regularizedBlockNorm, Real.sqrt_le_left (add_nonneg (normalizedBlockNorm_nonneg A) hε)]
  nlinarith [normalizedBlockNorm_nonneg A]

theorem hasDerivAt_regularizedWeylWeight {A B : ℝ → Mat} {Z V : Mat} {r ε : ℝ}
    (hA : HasDerivAt A Z r) (hB : HasDerivAt B V r)
    (hsA : ∀ t, symmetric (A t)) (hsB : ∀ t, symmetric (B t)) (hε : 0 < ε) :
    HasDerivAt (fun t => regularizedWeylWeight ε (A t) (B t))
      (regularizedWeylWeightDerivative ε (A r) (B r) Z V) r := by
  have h := ((hasDerivAt_const r (1 : ℝ)).sub
    (((hasDerivAt_regularizedBlockNorm hA hsA hε).sub
      (hasDerivAt_regularizedBlockNorm hB hsB hε)).const_mul (3 / 8 : ℝ))).pow 2
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  unfold regularizedWeylWeightDerivative
  simp only [Pi.sub_apply]
  ring

theorem regularized_weight_factor_lower (ε : ℝ) (hε : 0 ≤ ε) (he : ε ≤ 1 / 3)
    (A B : Mat) (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    1 / 8 < 1 - (3 / 8 : ℝ) * (regularizedBlockNorm ε A - regularizedBlockNorm ε B) := by
  have ha := regularizedBlockNorm_le ε hε A
  have hb := Real.sqrt_nonneg (normalizedBlockNorm B ^ 2 + ε ^ 2)
  have hnb := normalizedBlockNorm_nonneg B
  change 0 ≤ regularizedBlockNorm ε B at hb
  nlinarith

theorem regularizedWeylWeight_pos (ε : ℝ) (hε : 0 ≤ ε) (he : ε ≤ 1 / 3)
    (A B : Mat) (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    0 < regularizedWeylWeight ε A B := by
  have h := regularized_weight_factor_lower ε hε he A B hpinch
  unfold regularizedWeylWeight
  exact sq_pos_of_pos (by linarith)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The invariant Ricci equation has the actual Bianchi compression in
every orthonormal frame, without imposing a diagonal Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open Bianchi TraceHessian

noncomputable section

private theorem quaternion_skew_sum (r : Fin 3) (j : Fin 4) (q : Vec) :
    (∑ i, quaternionMatrix r i j * q i) = -quaternion r q j := by
  rw [← quaternionMatrix_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [quaternionMatrix_skew r i j]
  ring

/-- The full bundle term is the unweighted Bianchi coupling plus the
mixed action of the entire symmetric matrix. -/
theorem bundleCurvatureAction_general_sum (A : Mat) (Z : Tensor)
    (j : Fin 4) (a b : Fin 3) :
    2 * (∑ i, bundleCurvatureAction A i j (rawMatrixSlice Z.matrix i) a b) =
      -(rawCoupling Z.matrix a b j + generalMixedAction A Z.matrix a b j) := by
  have hr (r : Fin 3) :
      (∑ i, quaternionMatrix r i j *
        (matrixRotation r Z a b i + ∑ s, A r s * matrixRotation s Z a b i)) =
        -quaternion r (matrixRotation r Z a b) j -
          ∑ s, A r s * quaternion r (matrixRotation s Z a b) j := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [quaternion_skew_sum, Finset.sum_comm]
    have hpart (s : Fin 3) :
        (∑ i, quaternionMatrix r i j * (A r s * matrixRotation s Z a b i)) =
          -(A r s * quaternion r (matrixRotation s Z a b) j) := by
      calc
        _ = A r s * (∑ i, quaternionMatrix r i j * matrixRotation s Z a b i) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [quaternion_skew_sum]; ring
    simp_rw [hpart]
    rw [Finset.sum_neg_distrib]
    ring
  simp only [bundleCurvatureAction, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.add_apply, smul_eq_mul, matrixRotation_slice]
  calc
    _ = ∑ i, ∑ r, quaternionMatrix r i j *
        (matrixRotation r Z a b i + ∑ s, A r s * matrixRotation s Z a b i) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = ∑ r, ∑ i, quaternionMatrix r i j *
        (matrixRotation r Z a b i + ∑ s, A r s * matrixRotation s Z a b i) :=
      Finset.sum_comm
    _ = _ := by
      simp_rw [hr]
      simp only [rawCoupling, generalMixedAction, rawMatrixRotation_matrix,
        Finset.sum_apply, PiLp.smul_apply, WithLp.ofLp_sum,
        Finset.sum_sub_distrib, Finset.sum_neg_distrib, smul_eq_mul]
      ring

/-- The actual invariant Ricci right side is the compressed expression
13Z−20P(B_F(A)Z), as an equality of all matrix and tangent entries. -/
theorem invariantRicciGradient_compressed (A : Mat)
    (hA : symmetric A) (hAt : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    invariantRicciGradient A (fun j => rawMatrixSlice Z.matrix j) =
      fun j => rawMatrixSlice ((13 : ℝ) • Z.matrix -
        (20 : ℝ) • rawBianchiProjection (generalMatrixAction A Z.matrix)) j := by
  funext j
  ext a b
  have h := congrArg (fun W : RawGradient => W a b j)
    (generalRicci_compression A hA hAt Z hz hb)
  have hc := congrArg (fun q : Vec => q j) (gradientCoupling_eq Z hb a b)
  change rawCoupling Z.matrix a b j = -4 * Z.matrix a b j at hc
  change 13 * Z.matrix a b j - 12 * generalMatrixAction A Z.matrix a b j -
    generalMixedAction A Z.matrix a b j = _ at h
  simp only [invariantRicciGradient, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [bundleCurvatureAction_general_sum]
  change 9 * Z.matrix a b j - 12 * generalMatrixAction A Z.matrix a b j -
    (rawCoupling Z.matrix a b j + generalMixedAction A Z.matrix a b j) = _
  rw [hc]
  dsimp only [rawMatrixSlice]
  linarith only [h]

/-- The coefficient 20 holds against every genuine Bianchi test tensor
in an arbitrary frame. This is the bilinear form needed by both scalar
and varying matrix-slot Green identities. -/
theorem invariantRicciGradient_pairing (A : Mat)
    (hA : symmetric A) (hAt : traceFree A)
    (Z W : Tensor) (hz : Z.traceFree) (hbz : Z.bianchi) (hbw : W.bianchi) :
    inner ℝ (gradientVector (invariantRicciGradient A
      (fun j => rawMatrixSlice Z.matrix j))) (tensorGradientVector W) =
      13 * rawPairing Z.matrix W.matrix -
        20 * rawPairing (generalMatrixAction A Z.matrix) W.matrix := by
  rw [invariantRicciGradient_compressed A hA hAt Z hz hbz]
  change inner ℝ (rawGradientVector ((13 : ℝ) • Z.matrix -
    (20 : ℝ) • rawBianchiProjection (generalMatrixAction A Z.matrix)))
    (rawGradientVector W.matrix) = _
  rw [inner_rawGradientVector, rawPairing_sub_left, rawPairing_smul_left,
    rawPairing_smul_left, rawBianchiProjection_pairing _ W hbw]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The raw classical parallel-frame calculus used by the weighted Green
argument. Every field refers to the actual metric tensors. No compressed
Ricci equation or integral estimate is a field of this structure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem ricciGradient (d : MetricGreenData g μ) (e : FrameBundle g) :
    frameLaplacianMatrix g e = invariantRicciGradient (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame) :=
  metric_invariant_ricci_gradient g d.weyl d.flow d.derivativeWeyl
    (fun k i t e => d.derivativeHessian k i i t e) e
    (fun i k j a => frameCurvature g e.base e.frame i k a j) (d.gradientBianchi e)
    (d.innerCommutator e) (d.outerCommutator e) (d.ricci e)

end MetricGreenData

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.greenDataNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.greenDataNormedSpace
local instance greenDataNormedAlgebra_r8d12cb_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem hasDerivAt_gradientVector {Z : ℝ → Fin 4 → Mat} {X : Fin 4 → Mat} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s => Z s i) (X i) t) :
    HasDerivAt (fun s => gradientVector (Z s)) (gradientVector X) t := by
  exact gradientVectorMap.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_pi.mpr h)

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem laplacianVector (_d : MetricGreenData g μ) (e : FrameBundle g) :
    frameGradientLaplacian g e = gradientVector (frameLaplacianMatrix g e) := by
  ext p
  rcases p with ⟨j, a, b⟩
  simp only [frameGradientLaplacian, frameThirdVector, frameLaplacianMatrix,
    gradientVector, WithLp.ofLp_sum, Finset.sum_apply, Matrix.sum_apply]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.greenDataNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.greenDataNormedSpace
local instance greenDataNormedAlgebra_r8d12cb_2 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem continuousThirdVector (d : MetricGreenData g μ) (i j : Fin 4) :
    Continuous (frameThirdVector g i j) :=
  gradientVectorMap.continuous.comp (continuous_pi (d.continuousThird i j))

theorem derivativeGradientVector (d : MetricGreenData g μ) (i : Fin 4) (t : ℝ)
    (e : FrameBundle g) :
    HasDerivAt (fun s => frameGradientVector g ((d.flow i).map s e))
      (frameHessianVector g i ((d.flow i).map t e)) t :=
  hasDerivAt_gradientVector (fun j => d.derivativeGradient i j t e)

theorem derivativeHessianVector (d : MetricGreenData g μ) (i : Fin 4) (t : ℝ)
    (e : FrameBundle g) :
    HasDerivAt (fun s => frameHessianVector g i ((d.flow i).map s e))
      (frameThirdVector g i i ((d.flow i).map t e)) t :=
  hasDerivAt_gradientVector (fun j => d.derivativeHessian i i j t e)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Supply the smooth weights used by the metric Green identities from
the actual two Weyl blocks and their actual first covariant derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TraceHessian
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The derivative assumption on a Green weight follows from ordinary
parallel-frame differentiation of the two Weyl blocks. -/
theorem frameRegularizedWeight_hasDerivAt
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)} (φ : Fin 4 → FrameFlow g μ)
    (ε : ℝ) (hε : 0 < ε)
    (hT : Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame))
    (hU : Continuous (fun e : FrameBundle g => minusWeyl g e.base e.frame))
    (hZ : ∀ i, Continuous (fun e : FrameBundle g => plusWeylGradient g e.base e.frame i))
    (hV : ∀ i, Continuous (fun e : FrameBundle g => minusWeylGradient g e.base e.frame i))
    (hsT : ∀ e : FrameBundle g, symmetric (plusWeyl g e.base e.frame))
    (hsU : ∀ e : FrameBundle g, symmetric (minusWeyl g e.base e.frame))
    (hdT : ∀ i t e, HasDerivAt
      (fun s => plusWeyl g ((φ i).map s e).base ((φ i).map s e).frame)
      (plusWeylGradient g ((φ i).map t e).base ((φ i).map t e).frame i) t)
    (hdU : ∀ i t e, HasDerivAt
      (fun s => minusWeyl g ((φ i).map s e).base ((φ i).map s e).frame)
      (minusWeylGradient g ((φ i).map t e).base ((φ i).map t e).frame i) t) :
    ∀ i t e, HasDerivAt
      (fun s => frameRegularizedWeight g ε hT hU ((φ i).map s e))
      (frameRegularizedWeightDerivative g ε hε hT hU hZ hV i ((φ i).map t e)) t := by
  intro i t e
  exact hasDerivAt_regularizedWeylWeight (hdT i t e) (hdU i t e)
    (fun s => hsT ((φ i).map s e)) (fun s => hsU ((φ i).map s e)) hε

theorem frameRegularizedWeight_pos (g : SmoothMetric M) (ε : ℝ) (hε : 0 ≤ ε)
    (he : ε ≤ 1 / 3)
    (hT : Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame))
    (hU : Continuous (fun e : FrameBundle g => minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) (e : FrameBundle g) :
    0 < frameRegularizedWeight g ε hT hU e :=
  regularizedWeylWeight_pos ε hε he _ _ (hpinch e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Curvature contractions with the entire symmetric Weyl matrix.
No moving eigenframe enters these identities. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open Matrix TraceHessian Bianchi PositiveEinsteinFour.Geometry

noncomputable section

theorem generalCoefficient_eq_blockTensor (Q : Fin 3 → Mat4) (A : Mat)
    (i k j l : Fin 4) :
    generalCoefficient Q A i k j l = Angular.blockTensor A Q i k l j := by
  simp only [generalCoefficient, Angular.blockTensor, Angular.twoFormProduct,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem sum_four_swap {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h := (Equiv.prodComm (α × β) (γ × δ)).sum_comp
    (fun p : (γ × δ) × (α × β) => f p.2.1 p.2.2 p.1.1 p.1.2)
  simpa only [Fintype.sum_prod_type, Equiv.prodComm_apply, Prod.swap_prod_mk] using h

private theorem generalCoefficient_oneForm
    (Q P : Fin 3 → Mat4)
    (hQP : ∀ r t, (∑ i, ∑ k, Q r i k * P t i k) =
      if r = t then (4 : ℝ) else 0)
    (A : Mat) (t : Fin 3) (j l : Fin 4) :
    (∑ i, ∑ k, generalCoefficient Q A i k j l * P t i k) =
      2 * ∑ s, A t s * Q s j l := by
  simp only [generalCoefficient, Finset.mul_sum, Finset.sum_mul]
  rw [sum_four_swap]
  have hterm (r s : Fin 3) :
      (∑ i, ∑ k, (1 / 2 : ℝ) * (A r s * Q r i k * Q s j l) * P t i k) =
        (1 / 2 : ℝ) * A r s * Q s j l * (∑ i, ∑ k, Q r i k * P t i k) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hterm, hQP]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, if_true]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem generalCoefficient_minus_oneForm (A : Mat) (r : Fin 3) (j l : Fin 4) :
    (∑ i, ∑ k, generalCoefficient Angular.oppositeMatrix A i k j l *
      quaternionMatrix r i k) = 0 := by
  simp only [generalCoefficient, Finset.mul_sum, Finset.sum_mul]
  rw [sum_four_swap]
  have hterm (s t : Fin 3) :
      (∑ i, ∑ k, (1 / 2 : ℝ) *
        (A s t * Angular.oppositeMatrix s i k * Angular.oppositeMatrix t j l) *
        quaternionMatrix r i k) =
      (1 / 2 : ℝ) * A s t * Angular.oppositeMatrix t j l *
        (∑ i, ∑ k, quaternionMatrix r i k * Angular.oppositeMatrix s i k) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hterm, mixed_twoForm_pairing]
  simp

private theorem matrixPairing_bundle_general (A : Mat)
    (i k : Fin 4) (N P : Mat) :
    matrixPairing (bundleCurvatureAction A i k N) P =
      (1 / 2 : ℝ) * ∑ r, quaternionMatrix r i k *
        (matrixPairing (matrixAction r N) P +
          ∑ s, A r s * matrixPairing (matrixAction s N) P) := by
  change matrixPairingLinear P _ = _
  rw [bundleCurvatureAction, map_smul, map_sum]
  simp only [map_smul, map_add, map_sum, smul_eq_mul]
  rfl

/-- The two-form contraction is performed before the remaining
matrix-bundle action, so no diagonalization is used. -/
theorem weighted_bundle_general_pairing (K : Fin 4 → Fin 4 → ℝ)
    (b : Fin 3 → ℝ)
    (hK : ∀ r, (∑ i, ∑ k, K i k * quaternionMatrix r i k) = b r)
    (A : Mat) (N P : Mat) :
    (∑ i, ∑ k, K i k * matrixPairing (bundleCurvatureAction A i k N) P) =
      (1 / 2 : ℝ) * ∑ r, b r *
        (matrixPairing (matrixAction r N) P +
          ∑ s, A r s * matrixPairing (matrixAction s N) P) := by
  simp only [matrixPairing_bundle_general, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ r, ∑ k, K i k * ((1 / 2 : ℝ) * quaternionMatrix r i k *
        (matrixPairing (matrixAction r N) P +
          ∑ s, A r s * matrixPairing (matrixAction s N) P)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ r, ∑ i, ∑ k, K i k * ((1 / 2 : ℝ) * quaternionMatrix r i k *
        (matrixPairing (matrixAction r N) P +
          ∑ s, A r s * matrixPairing (matrixAction s N) P)) := Finset.sum_comm
    _ = ∑ r, (1 / 2 : ℝ) *
        (matrixPairing (matrixAction r N) P +
          ∑ s, A r s * matrixPairing (matrixAction s N) P) *
        (∑ i, ∑ k, K i k * quaternionMatrix r i k) := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp only [hK]
      apply Finset.sum_congr rfl
      intro r _
      ring


theorem generalCoefficient_minus_bundle_pairing (K A : Mat)
    (j l : Fin 4) (N P : Mat) :
    (∑ i, ∑ k, generalCoefficient Angular.oppositeMatrix K i k j l *
      matrixPairing (bundleCurvatureAction A i k N) P) = 0 := by
  rw [weighted_bundle_general_pairing _ (fun _ => 0)
    (fun r => generalCoefficient_minus_oneForm K r j l)]
  simp

theorem generalBundleGreenContraction_minus (U A : Mat) (Z : Tensor) :
    generalBundleGreenContraction (generalCoefficient Angular.oppositeMatrix U) A Z = 0 := by
  simp only [generalBundleGreenContraction, generalCoefficient_minus_bundle_pairing,
    Finset.sum_const_zero, mul_zero]

private theorem clifford_column_pairing
    (Q : Fin 3 → Mat4)
    (hskew : ∀ s, (Q s)ᵀ = -Q s)
    (hanti : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4))
    (r s : Fin 3) (l h : Fin 4) :
    (∑ j, Q r j l * Q s j h) + (∑ j, Q s j l * Q r j h) =
      (if r = s then (2 : ℝ) else 0) * (if l = h then 1 else 0) := by
  have hs (t : Fin 3) (j : Fin 4) : Q t l j = -Q t j l := by
    have hx := congrArg (fun M : Mat4 => M j l) (hskew t)
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using hx
  have ha := congrArg (fun M : Mat4 => M l h) (hanti r s)
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, hs, neg_mul, Finset.sum_neg_distrib] at ha
  by_cases hrs : r = s <;> simp only [hrs, ite_true, if_true, ite_false, if_false] at * <;> linarith

/-- A symmetric coefficient contracts the Clifford product to its trace.
This includes all off-diagonal matrix entries. -/
theorem symmetric_clifford_column_contraction
    (Q : Fin 3 → Mat4)
    (hskew : ∀ s, (Q s)ᵀ = -Q s)
    (hanti : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4))
    (C : Mat) (hC : symmetric C) (l h : Fin 4) :
    (∑ r, ∑ s, C r s * (∑ j, Q r j l * Q s j h)) =
      Matrix.trace C * (if l = h then 1 else 0) := by
  have hswap : (∑ r, ∑ s, C r s * (∑ j, Q s j l * Q r j h)) =
      ∑ r, ∑ s, C r s * (∑ j, Q r j l * Q s j h) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [hC s r]
  have hd : (∑ r, ∑ s, C r s *
      ((∑ j, Q r j l * Q s j h) + (∑ j, Q s j l * Q r j h))) =
      2 * Matrix.trace C * (if l = h then 1 else 0) := by
    simp_rw [clifford_column_pairing Q hskew hanti]
    by_cases hlh : l = h
    · simp only [hlh, ite_true, if_true, mul_one, mul_ite, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, Matrix.trace, Matrix.diag]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    · simp only [hlh, ite_false, if_false, mul_zero, Finset.sum_const_zero]
  simp only [mul_add, Finset.sum_add_distrib, hswap] at hd
  linarith

private theorem pair_generalCoefficient (K : Mat4) (Q : Fin 3 → Mat4)
    (B : Mat) (h n : Fin 4) :
    (∑ i, ∑ k, K i k * generalCoefficient Q B i k h n) =
      (1 / 2 : ℝ) * ∑ r, ∑ s, B r s * Q s h n *
        (∑ i, ∑ k, K i k * Q r i k) := by
  simp only [generalCoefficient, Finset.mul_sum]
  rw [sum_four_swap]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem generalCoefficient_pairing
    (Q : Fin 3 → Mat4)
    (hQ : ∀ r s, (∑ i, ∑ k, Q r i k * Q s i k) =
      if r = s then (4 : ℝ) else 0)
    (A B : Mat) (j l h n : Fin 4) :
    (∑ i, ∑ k, generalCoefficient Q A i k j l * generalCoefficient Q B i k h n) =
      ∑ r, ∑ s, (Aᵀ * B) r s * Q r j l * Q s h n := by
  rw [pair_generalCoefficient (fun i k => generalCoefficient Q A i k j l) Q B h n]
  simp_rw [generalCoefficient_oneForm Q Q hQ]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  ring

private theorem generalCoefficient_pairing_zero
    (Q P : Fin 3 → Mat4)
    (hQP : ∀ r s, (∑ i, ∑ k, Q r i k * P s i k) = 0)
    (A B : Mat) (j l h n : Fin 4) :
    (∑ i, ∑ k, generalCoefficient Q A i k j l * generalCoefficient P B i k h n) = 0 := by
  rw [pair_generalCoefficient (fun i k => generalCoefficient Q A i k j l) P B h n]
  have hz (r : Fin 3) :
      (∑ i, ∑ k, generalCoefficient Q A i k j l * P r i k) = 0 := by
    simp only [generalCoefficient, Finset.mul_sum, Finset.sum_mul]
    rw [sum_four_swap]
    have ht (s t : Fin 3) :
        (∑ i, ∑ k, (1 / 2 : ℝ) * (A s t * Q s i k * Q t j l) * P r i k) =
          (1 / 2 : ℝ) * A s t * Q t j l * (∑ i, ∑ k, Q s i k * P r i k) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [ht, hQP]
    simp
  simp only [hz, mul_zero, Finset.sum_const_zero]

private theorem generalCoefficient_ricci
    (Q : Fin 3 → Mat4)
    (hQ : ∀ r s, (∑ i, ∑ k, Q r i k * Q s i k) =
      if r = s then (4 : ℝ) else 0)
    (hskew : ∀ s, (Q s)ᵀ = -Q s)
    (hanti : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4))
    (A B : Mat) (hAB : symmetric (Aᵀ * B)) (l h : Fin 4) :
    (∑ j, ∑ i, ∑ k, generalCoefficient Q A i k j l * generalCoefficient Q B i k j h) =
      Matrix.trace (Aᵀ * B) * (if l = h then 1 else 0) := by
  simp_rw [generalCoefficient_pairing Q hQ]
  calc
    _ = ∑ r, ∑ j, ∑ s, (Aᵀ * B) r s * Q r j l * Q s j h := Finset.sum_comm
    _ = ∑ r, ∑ s, (Aᵀ * B) r s * (∑ j, Q r j l * Q s j h) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, mul_assoc]
    _ = _ := symmetric_clifford_column_contraction Q hskew hanti _ hAB l h

private theorem transpose_mul_one_add (A : Mat) (hs : symmetric A) :
    Aᵀ * (1 + A) = A + A * A := by
  have hAt : Aᵀ = A := by ext a b; exact hs b a
  rw [hAt, Matrix.mul_add, Matrix.mul_one]

private theorem symmetric_add_square (A : Mat) (hs : symmetric A) :
    symmetric (A + A * A) := by
  have hAt : Aᵀ = A := by ext a b; exact hs b a
  have h := show (A + A * A)ᵀ = A + A * A by
    simp only [Matrix.transpose_add, Matrix.transpose_mul, hAt]
  intro a b
  exact congrArg (fun M : Mat => M b a) h

private theorem oppositeMatrix_transpose (r : Fin 3) :
    (Angular.oppositeMatrix r)ᵀ = -Angular.oppositeMatrix r := by
  ext i j
  change Geometry.oppositeQuaternion r j i = -Geometry.oppositeQuaternion r i j
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    norm_num [Geometry.oppositeQuaternion, quaternionMatrix]

theorem minus_generalCoefficient_ricci (A U : Mat)
    (hs : symmetric U) (ht : traceFree U) (l h : Fin 4) :
    (1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k, generalCoefficient Angular.oppositeMatrix U i k j l *
      (generalCoefficient quaternionMatrix (1 + A) i k j h +
        generalCoefficient Angular.oppositeMatrix (1 + U) i k j h)) =
      (Matrix.trace (U * U) / 2) * (if l = h then 1 else 0) := by
  simp only [mul_add, Finset.sum_add_distrib]
  have hQP (r s : Fin 3) :
      (∑ i, ∑ k, Angular.oppositeMatrix r i k * quaternionMatrix s i k) = 0 := by
    simpa only [mul_comm] using mixed_twoForm_pairing s r
  have hz (j : Fin 4) := generalCoefficient_pairing_zero _ _ hQP
    U (1 + A) j l j h
  simp_rw [hz]
  simp only [Finset.sum_const_zero, mul_zero, zero_add]
  have hAB : symmetric (Uᵀ * (1 + U)) := by
    rw [transpose_mul_one_add U hs]
    exact symmetric_add_square U hs
  rw [generalCoefficient_ricci Angular.oppositeMatrix opposite_twoForm_pairing
    oppositeMatrix_transpose Angular.oppositeMatrix_anticommutator _ _ hAB,
    transpose_mul_one_add U hs, Matrix.trace_add]
  have htrace : Matrix.trace U = 0 := ht
  rw [htrace]
  ring

theorem generalEinsteinCoefficient_eq_tensor (A U : Mat) (i k j l : Fin 4) :
    generalEinsteinCoefficient A U i k j l =
      Angular.einsteinCurvatureTensor A U i k l j := by
  simp only [generalEinsteinCoefficient, generalCoefficient_eq_blockTensor,
    Angular.einsteinCurvatureTensor, Pi.add_apply]

theorem generalCovectorGreenContraction_minus (A U : Mat)
    (hs : symmetric U) (ht : traceFree U) (Z : Tensor) :
    covectorGreenContraction (generalCoefficient Angular.oppositeMatrix U)
      (generalEinsteinCoefficient A U) Z =
        (Matrix.trace (U * U) / 2) * Z.squaredNorm := by
  simp only [covectorGreenContraction, generalEinsteinCoefficient,
    minus_generalCoefficient_ricci A U hs ht]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  rw [← Finset.mul_sum, matrixSlice_self_sum]

theorem general_minus_green_polynomial (A U : Mat)
    (hs : symmetric U) (ht : traceFree U) (Z : Tensor) :
    generalBundleGreenContraction (generalCoefficient Angular.oppositeMatrix U) A Z +
      covectorGreenContraction (generalCoefficient Angular.oppositeMatrix U)
        (generalEinsteinCoefficient A U) Z =
        (Matrix.trace (U * U) / 2) * Z.squaredNorm := by
  rw [generalBundleGreenContraction_minus, zero_add,
    generalCovectorGreenContraction_minus A U hs ht]


private theorem sum_last_first_general {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  calc
    _ = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- The actual raw commutator contracts to the already computed bundle
and covector terms before any scalar estimate is applied. -/
theorem general_rawGreen_decomposition
    (K R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (A : Mat) (Z : Tensor) :
    derivativeGreenContraction K (generalRawCurvatureCommutator A R Z) Z =
      generalBundleGreenContraction K A Z + covectorGreenContraction K R Z := by
  unfold derivativeGreenContraction
  rw [sum_four_swap]
  simp only [generalRawCurvatureCommutator, matrixPairing_add_left,
    matrixPairing_sum_smul_left, mul_add, Finset.sum_add_distrib]
  change generalBundleGreenContraction K A Z + _ = _
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hs (l : Fin 4) :
      (∑ j, ∑ i, ∑ k, ∑ h, (1 / 2 : ℝ) * (K i k j l *
        (R i k j h * matrixPairing (rawMatrixSlice Z.matrix h) (rawMatrixSlice Z.matrix l)))) =
      ∑ h, ∑ j, ∑ i, ∑ k, (1 / 2 : ℝ) * (K i k j l *
        (R i k j h * matrixPairing (rawMatrixSlice Z.matrix h) (rawMatrixSlice Z.matrix l))) :=
    sum_last_first_general _
  simp only [hs, covectorGreenContraction, Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem general_minus_rawGreen (A U : Mat)
    (hs : symmetric U) (ht : traceFree U) (Z : Tensor) :
    derivativeGreenContraction (generalCoefficient Angular.oppositeMatrix U)
      (generalRawCurvatureCommutator A (generalEinsteinCoefficient A U) Z) Z =
        (Matrix.trace (U * U) / 2) * Z.squaredNorm := by
  rw [general_rawGreen_decomposition]
  exact general_minus_green_polynomial A U hs ht Z

end
end PositiveEinsteinFour.CurvatureContraction
end


section

/-! The Ricci equation and its identity and varying-matrix Green
contractions in the actual arbitrary orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance metricContractionNormedRing_r8d12cb_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricContractionNormedSpace_r8d12cb_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricContractionNormedAlgebra_r8d12cb_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem generalMatrixAction_gradientVector (A : Mat) (Z : Angular.Gradient)
    (hZ : ∀ i, symmetric (Z i)) :
    rawGradientVector (generalMatrixAction A (gradientTensor Z).matrix) =
      gradientVector (fun i => matrixSlotAction A (Z i)) := by
  ext p
  rcases p with ⟨i, a, b⟩
  change matrixSlotAction A (rawMatrixSlice (gradientTensor Z).matrix i) a b = _
  rw [rawMatrixSlice_gradientTensor Z hZ]
  rfl

theorem generalMatrixAction_gradient_pairing (A : Mat) (Z : Angular.Gradient)
    (hZ : ∀ i, symmetric (Z i)) :
    rawPairing (generalMatrixAction A (gradientTensor Z).matrix) (gradientTensor Z).matrix =
      6 * weylMatrixEnergy A Z := by
  rw [← inner_rawGradientVector, generalMatrixAction_gradientVector A Z hZ]
  change inner ℝ (gradientVector (fun i => matrixSlotAction A (Z i)))
    (tensorGradientVector (gradientTensor Z)) = _
  rw [tensorGradientVector_gradientTensor Z hZ, gradientVector_pairing]
  unfold weylMatrixEnergy
  ring

/-- The identity contraction is valid without diagonalizing the Weyl block. -/
theorem invariant_ricci_identity_scalar (A : Mat) (hA : symmetric A) (hAt : traceFree A)
    (Z L : Angular.Gradient) (hZ : ∀ i, symmetric (Z i))
    (htZ : ∀ i, traceFree (Z i)) (hbZ : ∀ a b, gradientDivergence Z a b = 0)
    (hRicci : L = invariantRicciGradient A Z) :
    inner ℝ (gradientVector Z) (gradientVector L) / 6 =
      13 * weylGradientEnergy Z - 20 * weylMatrixEnergy A Z := by
  have hc := invariantRicciGradient_pairing A hA hAt (gradientTensor Z) (gradientTensor Z)
    (gradientTensor_traceFree Z htZ) (gradientTensor_bianchi Z hZ hbZ)
    (gradientTensor_bianchi Z hZ hbZ)
  have hs : (fun i => rawMatrixSlice (gradientTensor Z).matrix i) = Z :=
    funext (rawMatrixSlice_gradientTensor Z hZ)
  rw [hs, tensorGradientVector_gradientTensor Z hZ,
    gradientTensor_pairing Z Z hZ hZ, generalMatrixAction_gradient_pairing A Z hZ] at hc
  rw [hRicci, real_inner_comm, hc]
  unfold weylGradientEnergy
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem identityScalar (d : MetricGreenData g μ) (e : FrameBundle g) :
    inner ℝ (frameGradientVector g e) (frameGradientLaplacian g e) / 6 =
      13 * weylGradientEnergy (plusWeylGradient g e.base e.frame) -
        20 * weylMatrixEnergy (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame) := by
  rw [d.laplacianVector e]
  exact invariant_ricci_identity_scalar _ (d.weyl.symmetric e) (d.weyl.traceFree e)
    _ _ (d.gradientConstraints e).1 (d.gradientConstraints e).2
    (d.gradientBianchi e) (d.ricciGradient e)

/-- The first Green integral for the metric Hessian, with the invariant
first-derivative scalar substituted. -/
theorem identityGreen (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
      (dm i ((d.flow i).map t e)) t) :
    (∫ e, weightedQuadratic hessianNormSq (m e) (plusWeylHessian g e.base e.frame)
      (weightTensor (WithLp.toLp 2 (fun i => dm i e))
        (plusGradientTensor g e.base e.frame)) ∂μ) =
    ∫ e, m e * (-13 * weylGradientEnergy (plusWeylGradient g e.base e.frame) +
      20 * weylMatrixEnergy (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame)) ∂μ := by
  have hgreen := weighted_metric_hessian_green g d.flow m dm
    d.continuousGradientVector d.continuousHessianVector
    (fun i => d.continuousThirdVector i i) hm
    d.derivativeGradientVector d.derivativeHessianVector
  calc
    _ = (1 / 6 : ℝ) * (∫ e, m e * hessianNormSq (plusWeylHessian g e.base e.frame) +
        ∑ i, dm i e * inner ℝ (frameGradientVector g e) (frameHessianVector g i e) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with e
      rw [weightedQuadratic_identity_green]
      simp only [plusGradientTensor, tensorGradientVector_gradientTensor _
        (d.gradientConstraints e).1]
      simp only [frameGradientVector, frameHessianVector]
      ring
    _ = (1 / 6 : ℝ) * (-(∫ e, m e *
        inner ℝ (frameGradientVector g e) (frameGradientLaplacian g e) ∂μ)) := by rw [hgreen]
    _ = _ := by
      rw [mul_neg, ← integral_const_mul, ← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with e
      have h := d.identityScalar e
      linear_combination -(m e) * h

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Evaluate the derivative-slot Green integral on actual metric tensors,
using the published raw curvature decomposition and Ricci commutator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian CurvatureContraction MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.curvatureIntegralNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.curvatureIntegralNormedSpace
local instance curvatureIntegralNormedAlgebra_r8d12cb_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem generalCoefficient_pair_swap (Q : Fin 3 → Mat4)
    (hQ : ∀ s i j, Q s j i = -Q s i j) (A : Mat) (i k j l : Fin 4) :
    generalCoefficient Q A k i l j = generalCoefficient Q A i k j l := by
  unfold generalCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [hQ r i k, hQ s j l]
  ring

theorem generalCoefficient_skew (Q : Fin 3 → Mat4)
    (hQ : ∀ s i j, Q s j i = -Q s i j) (A : Mat) (i k j l : Fin 4) :
    generalCoefficient Q A k i j l = -generalCoefficient Q A i k j l := by
  simp only [generalCoefficient, ← Finset.sum_neg_distrib, ← mul_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [hQ r i k]
  ring

theorem generalCoefficient_divergence (Q : Fin 3 → Mat4) (Z : Angular.Gradient)
    (hb : ∀ s i, (∑ r, ∑ k, Q r i k * Z k r s) = 0) (i j l : Fin 4) :
    (∑ k, generalCoefficient Q (Z k) i k j l) = 0 := by
  simp only [generalCoefficient, Finset.mul_sum]
  calc
    _ = ∑ s, (1 / 2 : ℝ) * Q s j l * (∑ r, ∑ k, Q r i k * Z k r s) := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ r, ∑ k, ∑ s, (1 / 2 : ℝ) * (Z k r s * Q r i k * Q s j l) :=
          Finset.sum_comm
        _ = ∑ r, ∑ s, ∑ k, (1 / 2 : ℝ) * (Z k r s * Q r i k * Q s j l) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_comm]
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s _
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = 0 := by simp only [hb, mul_zero, Finset.sum_const_zero]

theorem inner_matrixVector_sub (A B C : Mat) :
    inner ℝ (matrixVector A - matrixVector B) (matrixVector C) =
      matrixPairing (A - B) C := by
  rw [inner_sub_left, inner_matrixVector, inner_matrixVector, matrixPairing_sub_left]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.curvatureIntegralNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.curvatureIntegralNormedSpace
local instance curvatureIntegralNormedAlgebra_r8d12cb_2 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem continuousGradientSlice (d : MetricGreenData g μ) (i : Fin 4) :
    Continuous (frameGradientSlice g i) :=
  matrixVectorMap.continuous.comp (d.continuousGradient i)

theorem continuousHessianSlice (d : MetricGreenData g μ) (i j : Fin 4) :
    Continuous (frameHessianSlice g i j) :=
  matrixVectorMap.continuous.comp (d.continuousHessian i j)

theorem continuousThirdSlice (d : MetricGreenData g μ) (i j k : Fin 4) :
    Continuous (frameThirdSlice g i j k) :=
  matrixVectorMap.continuous.comp (d.continuousThird i j k)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite Weyl block acts on the derivative slots of the plus
Hessian. All derivatives of the opposite coefficient are retained. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian CurvatureContraction MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

private theorem oppositeMatrix_skew (s : Fin 3) (i j : Fin 4) :
    Angular.oppositeMatrix s j i = -Angular.oppositeMatrix s i j := by
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [Angular.oppositeMatrix, oppositeQuaternion, quaternionMatrix]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.minusIntegralNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.minusIntegralNormedSpace
local instance minusIntegralNormedAlgebra_r8d12cb_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem minusCurvatureGreen (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
      (dm i ((d.flow i).map t e)) t) :
    (∫ e, weightedQuadratic
      (fun X => derivativePairing
        (generalCoefficient Angular.oppositeMatrix (minusWeyl g e.base e.frame)) X X)
      (m e) (plusWeylHessian g e.base e.frame)
      (weightTensor (WithLp.toLp 2 (fun i => dm i e))
        (plusGradientTensor g e.base e.frame)) ∂μ) =
    ∫ e, m e * (3 * normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2 *
      weylGradientEnergy (plusWeylGradient g e.base e.frame)) ∂μ := by
  have hcoef (p : Averages.CurvatureIndex) (e : FrameBundle g) :
      frameMinusCoefficient g p e =
        generalCoefficient Angular.oppositeMatrix (minusWeyl g e.base e.frame)
          p.1.1 p.1.2 p.2.1 p.2.2 :=
    (generalCoefficient_eq_blockTensor _ _ _ _ _ _).symm
  have hdcoef (p : Averages.CurvatureIndex) (e : FrameBundle g) :
      frameMinusCoefficientDerivative g p e =
        generalCoefficient Angular.oppositeMatrix (minusWeylGradient g e.base e.frame p.1.2)
          p.1.1 p.1.2 p.2.1 p.2.2 :=
    (generalCoefficient_eq_blockTensor _ _ _ _ _ _).symm
  have hgreen := weighted_metric_minus_curvature_green g d.flow m dm
    (fun p => by
      convert! (generalCoefficientMap Angular.oppositeMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
        o.continuousWeyl using 1
      all_goals try with_reducible_and_instances rfl
      funext e
      exact hcoef p e)
    (fun p => by
      convert! (generalCoefficientMap Angular.oppositeMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
        (o.continuousGradient p.1.2) using 1
      all_goals try with_reducible_and_instances rfl
      funext e
      exact hdcoef p e)
    d.continuousGradientSlice d.continuousHessianSlice d.continuousThirdSlice
    (by
      intro i j l e
      simp only [hdcoef]
      exact generalCoefficient_divergence Angular.oppositeMatrix _ (o.gradientBianchi e) i j l)
    (by
      intro i k j l e
      simp only [hcoef]
      exact generalCoefficient_skew Angular.oppositeMatrix oppositeMatrix_skew _ i k j l)
    hm
    (by
      intro p t e
      convert! (generalCoefficientMap Angular.oppositeMatrix p.1.1 p.1.2 p.2.1 p.2.2).hasFDerivAt.comp_hasDerivAt t
        (o.derivativeWeyl p.1.2 t e) using 1
      · funext s
        exact hcoef p ((d.flow p.1.2).map s e)
      · exact hdcoef p ((d.flow p.1.2).map t e))
    (fun k j t e => hasDerivAt_matrixVector (d.derivativeGradient k j t e))
    (fun k i j t e => hasDerivAt_matrixVector (d.derivativeHessian k i j t e))
  have hp (e : FrameBundle g) :
      derivativeGreenContraction
        (generalCoefficient Angular.oppositeMatrix (minusWeyl g e.base e.frame))
        (fun i k j => plusWeylThirdDerivative g e.base e.frame i k j -
          plusWeylThirdDerivative g e.base e.frame k i j)
        (plusGradientTensor g e.base e.frame) / 6 =
      3 * normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2 *
        weylGradientEnergy (plusWeylGradient g e.base e.frame) := by
    have hr : (fun i k j => plusWeylThirdDerivative g e.base e.frame i k j -
        plusWeylThirdDerivative g e.base e.frame k i j) =
        generalRawCurvatureCommutator (plusWeyl g e.base e.frame)
          (generalEinsteinCoefficient (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
          (plusGradientTensor g e.base e.frame) := by
      funext i k j
      rw [d.outerCommutator e i k j]
      simp only [generalRawCurvatureCommutator, plusGradientTensor,
        rawMatrixSlice_gradientTensor _ (d.gradientConstraints e).1,
        generalEinsteinCoefficient_eq_tensor, ← hdecomp e]
    rw [hr, general_minus_rawGreen _ _ (o.symmetric e) (o.traceFree e),
      trace_square_eq_six_norm_sq _ (o.symmetric e),
      plusGradientTensor_squaredNorm _ _ _ (d.gradientConstraints e).1]
    have he : Angular.gradientSquareNorm (plusWeylGradient g e.base e.frame) =
        6 * weylGradientEnergy (plusWeylGradient g e.base e.frame) := by
      rw [← gradientVector_norm_sq, ← real_inner_self_eq_norm_sq, gradientVector_pairing]
      unfold weylGradientEnergy
      ring
    rw [he]
    ring
  calc
    _ = (1 / 6 : ℝ) * (∫ e, ∑ p : Averages.CurvatureIndex,
        (m e * frameMinusCoefficient g p e *
          matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
            (plusWeylHessian g e.base e.frame p.1.2 p.2.2) +
        dm p.1.2 e * frameMinusCoefficient g p e *
          matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
            (plusWeylGradient g e.base e.frame p.2.2)) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with e
      rw [weightedQuadratic_derivative_green _
        (generalCoefficient_pair_swap Angular.oppositeMatrix oppositeMatrix_skew _)]
      simp only [hcoef, plusGradientTensor,
        rawMatrixSlice_gradientTensor _ (d.gradientConstraints e).1]
      ring
    _ = _ := by
      rw [hgreen, ← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with e
      have hh := hp e
      simp only [hcoef, frameThirdSlice, frameGradientSlice, inner_matrixVector_sub] at *
      simp only [derivativeGreenContraction, plusGradientTensor,
        rawMatrixSlice_gradientTensor _ (d.gradientConstraints e).1] at hh
      simp only [Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum]
      linear_combination (m e) * hh

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! All five Green integrals for the actual Weyl Hessian. The result has
only first derivatives and the constructed orthogonal-projection cost. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian CurvatureContraction MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem invariant_green_polynomial_identity (m v b e B C E R c k : ℝ) :
    m * ((-42 - 3 * b ^ 2 - (10 / 3 : ℝ) * v ^ 2) * e +
      75 * B + (25 / 3 : ℝ) * C - (100 / 3 : ℝ) * E + 5 * R) -
        (5 / 36 : ℝ) * c + k =
      4 * (m * (-13 * e + 20 * B)) -
        (5 / 6 : ℝ) * (m * (7 * v ^ 2 * e - 4 * B - 4 * C)) -
        (5 / 3 : ℝ) * (m * (-10 * B - 3 * C + 20 * E) + c / 12) -
        m * (3 * b ^ 2 * e) + m * ((10 + (5 / 2 : ℝ) * v ^ 2) * e - 25 * B + 5 * R) + k := by
  ring

local instance hessianAssemblyNormedRing_r8d12cb_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianAssemblyNormedSpace_r8d12cb_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianAssemblyNormedAlgebra_r8d12cb_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem general_weightedQuadratic_original (A U : Mat) (m : ℝ) (X L : Hessian) :
    weightedQuadratic (generalOriginalCurvatureForm A U) m X L =
      4 * weightedQuadratic hessianNormSq m X L -
        (5 / 6 : ℝ) * weightedQuadratic
          (fun W => derivativePairing (generalCoefficient quaternionMatrix A) W W) m X L -
        (5 / 3 : ℝ) * weightedQuadratic
          (fun W => matrixHessianPairing A W W) m X L -
        weightedQuadratic
          (fun W => derivativePairing (generalCoefficient Angular.oppositeMatrix U) W W) m X L := by
  unfold weightedQuadratic generalOriginalCurvatureForm
  ring

section Integral

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

private theorem hessianIntegral_apply (f : C(Ω, ℝ)) :
    hessianIntegral μ f = ∫ x, f x ∂μ := by
  change L1.integralCLM (ContinuousMap.toLp 1 μ ℝ f) = _
  rw [← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 1) μ f)

private theorem hessianIntegral_combination (I T F U D K : C(Ω, ℝ)) :
    (∫ x, 4 * I x - (5 / 6 : ℝ) * T x - (5 / 3 : ℝ) * F x - U x + D x + K x ∂μ) =
      4 * (∫ x, I x ∂μ) - (5 / 6 : ℝ) * (∫ x, T x ∂μ) -
        (5 / 3 : ℝ) * (∫ x, F x ∂μ) - (∫ x, U x ∂μ) +
        (∫ x, D x ∂μ) + (∫ x, K x ∂μ) := by
  change (∫ x, (((4 : ℝ) • I - (5 / 6 : ℝ) • T - (5 / 3 : ℝ) • F - U + D + K) x) ∂μ) = _
  rw [← hessianIntegral_apply]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, hessianIntegral_apply]

end Integral

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

local instance hessianAssemblyNormedRing_r8d12cb_2 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianAssemblyNormedSpace_r8d12cb_2 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianAssemblyNormedAlgebra_r8d12cb_2 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
/-- The weighted Hessian estimate with every Green contribution evaluated
on the actual metric tensors. The geometric shifted-positivity condition
is kept separate; no new integral estimate is an input. -/
theorem weightedHessianGreen (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (m : C(FrameBundle g, ℝ)) (hmpos : ∀ e, 0 < m e)
    (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
      (dm i ((d.flow i).map t e)) t) :
    0 ≤ ∫ e, m e * invariantHessianForm (plusWeyl g e.base e.frame)
        (minusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) -
      (5 / 36 : ℝ) * (∑ i, dm i e * Matrix.trace (plusWeylGradient g e.base e.frame i *
        (∑ j, plusWeylGradient g e.base e.frame j * plusWeylGradient g e.base e.frame j))) +
      generalCurvaturePairing (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (highestProjection (weightTensor (WithLp.toLp 2 (fun i => dm i e))
          (plusGradientTensor g e.base e.frame)))
        (highestProjection (weightTensor (WithLp.toLp 2 (fun i => dm i e))
          (plusGradientTensor g e.base e.frame))) / (24 * m e) ∂μ := by
  let A := fun e : FrameBundle g => plusWeyl g e.base e.frame
  let U := fun e : FrameBundle g => minusWeyl g e.base e.frame
  let Z := fun e : FrameBundle g => plusWeylGradient g e.base e.frame
  let I := d.hessianIdentityField m dm
  let T := d.hessianPlusField m dm
  let F := d.hessianMatrixField m dm
  let V := d.hessianMinusField o m dm
  let D := d.hessianTraceField o m dm
  let K := d.hessianCostField o m hmpos dm
  let E := d.gradientEnergyField
  let B := d.matrixEnergyField
  let C := d.squareEnergyField
  let P := d.compressionEnergyField
  let R := d.radialEnergyField
  let v := d.plusNormField
  let b := d.minusNormField o
  let cubic := d.weightCubicField dm
  let RI : C(FrameBundle g, ℝ) := ⟨fun e => m e * (-13 * E e + 20 * B e), by fun_prop⟩
  let RT : C(FrameBundle g, ℝ) := ⟨fun e => m e * (7 * v e ^ 2 * E e - 4 * B e - 4 * C e), by fun_prop⟩
  let RF : C(FrameBundle g, ℝ) := ⟨fun e => m e * (-10 * B e - 3 * C e + 20 * P e) + cubic e / 12, by fun_prop⟩
  let RV : C(FrameBundle g, ℝ) := ⟨fun e => m e * (3 * b e ^ 2 * E e), by fun_prop⟩
  let RD : C(FrameBundle g, ℝ) := ⟨fun e => m e * ((10 + (5 / 2 : ℝ) * v e ^ 2) * E e -
    25 * B e + 5 * R e), by fun_prop⟩
  have hI : (∫ e, I e ∂μ) = ∫ e, RI e ∂μ := d.identityGreen m dm hm
  have hT : (∫ e, T e ∂μ) = ∫ e, RT e ∂μ := d.plusCurvatureGreen hdecomp m dm hm
  have hF : (∫ e, F e ∂μ) = ∫ e, RF e ∂μ := d.matrixGreen m dm hm
  have hV : (∫ e, V e ∂μ) = ∫ e, RV e ∂μ := d.minusCurvatureGreen o hdecomp m dm hm
  have hD : (∫ e, D e ∂μ) = ∫ e, RD e ∂μ := d.traceGreen m dm hm
  have hn : 0 ≤ ∫ e, 4 * I e - (5 / 6 : ℝ) * T e - (5 / 3 : ℝ) * F e - V e + D e + K e ∂μ := by
    apply integral_nonneg
    intro e
    change (0 : ℝ) ≤ 4 * I e - (5 / 6 : ℝ) * T e - (5 / 3 : ℝ) * F e - V e + D e + K e
    have hh := d.localWeightedHessian o hp e (m e) (hmpos e) (WithLp.toLp 2 (fun i => dm i e))
    simpa only [general_weightedQuadratic_original, I, T, F, V, D, K,
      hessianIdentityField, hessianPlusField, hessianMatrixField, hessianMinusField,
      hessianTraceField, hessianCostField, plusMatrixMap, minusMatrixMap, hessianMap,
      weightTensorMap, ContinuousMap.coe_mk] using hh
  rw [hessianIntegral_combination, hI, hT, hF, hV, hD,
    ← hessianIntegral_combination μ RI RT RF RV RD K] at hn
  convert hn using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with e
  change m e * invariantHessianForm (A e) (U e) (Z e) - (5 / 36 : ℝ) * cubic e + K e = _
  exact invariant_green_polynomial_identity (m e) (v e) (b e) (E e) (B e) (C e)
    (P e) (R e) (cubic e) (K e)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine smooth norm weights in the actual metric Hessian estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem MetricGreenData.regularizedHessianGreen_oai
    {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2)
    (ε : ℝ) (hε : 0 < ε) (he : ε ≤ 1 / 3) :
    0 ≤ ∫ e, regularizedHessianIntegrand g ε e ∂μ := by
  exact d.weightedHessianGreen o hp hdecomp
    (frameRegularizedWeight g ε d.continuousWeyl o.continuousWeyl)
    (frameRegularizedWeight_pos g ε hε.le he d.continuousWeyl o.continuousWeyl hpinch)
    (frameRegularizedWeightDerivative g ε hε d.continuousWeyl o.continuousWeyl
      d.continuousGradient o.continuousGradient)
    (frameRegularizedWeight_hasDerivAt g d.flow ε hε d.continuousWeyl o.continuousWeyl
      d.continuousGradient o.continuousGradient d.weyl.symmetric o.symmetric
      d.derivativeWeyl o.derivativeWeyl)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

theorem solution.{u_1} : type_of% @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.regularizedHessianGreen_oai.{u_1} := @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.regularizedHessianGreen_oai.{u_1}
