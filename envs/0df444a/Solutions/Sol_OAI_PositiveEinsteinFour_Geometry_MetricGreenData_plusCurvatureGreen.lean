-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusCurvatureGreen
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:39:35.455649+00:00
-- url     : https://prove2.me/submissions/eb0bbf69-6310-4815-af4b-9343a9059bfd

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C018
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_coupling_matrix_coordinates

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

theorem rawPairing_add_left (Z W U : RawGradient) :
    rawPairing (Z + W) U = rawPairing Z U + rawPairing W U := by
  change (∑ p : GradientIndex,
    (rawCoordinates Z p + rawCoordinates W p) * rawCoordinates U p) = _
  simp only [add_mul, rawPairing, Finset.sum_add_distrib]

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
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
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

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricHessian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
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

/-- Bilinear compression against any Bianchi test tensor. No pointwise
diagonal frame is assumed for either the Weyl coefficient or the test. -/
theorem generalMixedAction_pairing (A : Mat)
    (hA : symmetric A) (hAt : traceFree A)
    (Z W : Tensor) (hz : Z.traceFree) (hbz : Z.bianchi) (hbw : W.bianchi) :
    rawPairing (generalMixedAction A Z.matrix) W.matrix =
      8 * rawPairing (generalMatrixAction A Z.matrix) W.matrix := by
  have hW : rawCoupling W.matrix = (-4 : ℝ) • W.matrix := by
    funext a b
    exact gradientCoupling_eq W hbw a b
  have h := rawCoupling_selfadjoint (generalMatrixAction A Z.matrix) W.matrix
  rw [rawCoupling_generalMatrixAction A hA hAt Z hz hbz, hW,
    rawPairing_smul_left, rawPairing_smul_right] at h
  linarith

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricCurvatureGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivative-slot integration for the actual metric Weyl Hessian. The
coefficient and its derivative are both the concrete quaternion curvature
block. The only differential premises are parallel differentiation and
the classical divergence and skew identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory TraceHessian Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The derivative-slot Green formula on the actual metric tensors.
The third derivatives retain their order; the half factor is proved by
skewing the first two slots, before any Ricci substitution. -/
theorem weighted_metric_curvature_green
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (φ : Fin 4 → FrameFlow g μ)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hA : ∀ p, Continuous (framePlusCoefficient g p))
    (hDA : ∀ p, Continuous (framePlusCoefficientDerivative g p))
    (hZ : ∀ j, Continuous (frameGradientSlice g j))
    (hX : ∀ i j, Continuous (frameHessianSlice g i j))
    (hD : ∀ i k j, Continuous (frameThirdSlice g i k j))
    (hdiv : ∀ i j l e, (∑ k, framePlusCoefficientDerivative g ((i, k), (j, l)) e) = 0)
    (hskew : ∀ i k j l e, framePlusCoefficient g ((k, i), (j, l)) e =
      -framePlusCoefficient g ((i, k), (j, l)) e)
    (hm : ∀ k t e, HasDerivAt (fun s => m ((φ k).map s e)) (dm k ((φ k).map t e)) t)
    (hAd : ∀ p t e, HasDerivAt
      (fun s => framePlusCoefficient g p ((φ p.1.2).map s e))
      (framePlusCoefficientDerivative g p ((φ p.1.2).map t e)) t)
    (hZd : ∀ k j t e, HasDerivAt (fun s => frameGradientSlice g j ((φ k).map s e))
      (frameHessianSlice g k j ((φ k).map t e)) t)
    (hXd : ∀ k i j t e, HasDerivAt (fun s => frameHessianSlice g i j ((φ k).map s e))
      (frameThirdSlice g k i j ((φ k).map t e)) t) :
    (∫ e, ∑ p : Averages.CurvatureIndex,
      (m e * framePlusCoefficient g p e *
        matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
          (plusWeylHessian g e.base e.frame p.1.2 p.2.2) +
        dm p.1.2 e * framePlusCoefficient g p e *
          matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
            (plusWeylGradient g e.base e.frame p.2.2)) ∂μ) =
      (1 / 2 : ℝ) * (∫ e, ∑ p : Averages.CurvatureIndex,
        m e * framePlusCoefficient g p e *
          inner ℝ (frameThirdSlice g p.1.1 p.1.2 p.2.1 e -
            frameThirdSlice g p.1.2 p.1.1 p.2.1 e)
            (frameGradientSlice g p.2.2 e) ∂μ) := by
  have h := Averages.weighted_curvature_green μ
    (fun k => (φ k).map) (fun k => (φ k).continuous) (fun k => (φ k).preserves)
    m dm (fun p => ⟨framePlusCoefficient g p, hA p⟩)
    (fun p => ⟨framePlusCoefficientDerivative g p, hDA p⟩)
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

local instance metricRicciNormedRing_ra3aad3_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricRicciNormedSpace_ra3aad3_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricRicciNormedAlgebra_ra3aad3_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem rawMatrixSlice_gradientTensor (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) (j : Fin 4) :
    rawMatrixSlice (gradientTensor Z).matrix j = Z j := by
  ext a b
  simp only [rawMatrixSlice, gradientTensor_matrix Z hs]

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

theorem generalMixedAction_add (A B : Mat) (Z : RawGradient) :
    generalMixedAction (A + B) Z = generalMixedAction A Z + generalMixedAction B Z := by
  funext a b
  simp only [generalMixedAction, Matrix.add_apply, add_smul, Finset.sum_add_distrib,
    Pi.add_apply]

theorem generalMixedAction_smul (r : ℝ) (A : Mat) (Z : RawGradient) :
    generalMixedAction (r • A) Z = r • generalMixedAction A Z := by
  funext a b
  simp only [generalMixedAction, Matrix.smul_apply, smul_eq_mul, mul_smul,
    ← Finset.smul_sum, Pi.smul_apply]

theorem generalMixedAction_one (Z : RawGradient) :
    generalMixedAction 1 Z = rawCoupling Z := by
  funext a b
  simp only [generalMixedAction, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true, rawCoupling]

theorem generalMixedAction_self_pairing (A : Mat)
    (hs : symmetric A) (ht : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    rawPairing (generalMixedAction A Z.matrix) Z.matrix = 8 * generalGradientForm A Z :=
  generalMixedAction_pairing A hs ht Z Z hz hb hb

theorem rawCoupling_self_pairing (Z : Tensor) (hb : Z.bianchi) :
    rawPairing (rawCoupling Z.matrix) Z.matrix = -4 * Z.squaredNorm := by
  have hC : rawCoupling Z.matrix = (-4 : ℝ) • Z.matrix := by
    funext a b
    exact gradientCoupling_eq Z hb a b
  rw [hC, rawPairing_smul_left, rawPairing_vectors]
  simp only [real_inner_self_eq_norm_sq, Tensor.squaredNorm]

theorem generalMixedAction_square_pairing (A : Mat)
    (hs : symmetric A) (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    rawPairing (generalMixedAction (A * A) Z.matrix) Z.matrix =
      8 * generalGradientForm (traceFreeSquare A) Z -
        (4 / 3 : ℝ) * Matrix.trace (A * A) * Z.squaredNorm := by
  have he : A * A = traceFreeSquare A + (Matrix.trace (A * A) / 3) • (1 : Mat) := by
    rw [traceFreeSquare]
    abel
  conv_lhs => rw [he]
  rw [generalMixedAction_add, generalMixedAction_smul, generalMixedAction_one,
    rawPairing_add_left, rawPairing_smul_left,
    generalMixedAction_self_pairing _ (traceFreeSquare_symmetric A hs)
      (traceFreeSquare_traceFree A) Z hz hb, rawCoupling_self_pairing Z hb]
  ring

/-- This is the full bundle polynomial before adding the covector curvature.
It is an arbitrary-matrix identity on the actual Bianchi gradient. -/
theorem generalMixedAction_linear_square_pairing (A : Mat)
    (hs : symmetric A) (ht : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    -(1 / 2 : ℝ) * rawPairing (generalMixedAction (A + A * A) Z.matrix) Z.matrix =
      (2 / 3 : ℝ) * Matrix.trace (A * A) * Z.squaredNorm -
        4 * generalGradientForm A Z - 4 * generalGradientForm (traceFreeSquare A) Z := by
  rw [generalMixedAction_add, rawPairing_add_left,
    generalMixedAction_self_pairing A hs ht Z hz hb,
    generalMixedAction_square_pairing A hs Z hz hb]
  ring

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

theorem generalCoefficient_plus_oneForm (A : Mat) (r : Fin 3) (j l : Fin 4) :
    (∑ i, ∑ k, generalCoefficient quaternionMatrix A i k j l * quaternionMatrix r i k) =
      2 * ∑ s, A r s * quaternionMatrix s j l :=
  generalCoefficient_oneForm _ _ plus_twoForm_pairing A r j l

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


theorem generalCoefficient_bundle_pairing (K A : Mat)
    (j l : Fin 4) (N P : Mat) :
    (∑ i, ∑ k, generalCoefficient quaternionMatrix K i k j l *
      matrixPairing (bundleCurvatureAction A i k N) P) =
      ∑ r, ∑ s, K r s * quaternionMatrix s j l *
        (matrixPairing (matrixAction r N) P +
          ∑ t, A r t * matrixPairing (matrixAction t N) P) := by
  rw [weighted_bundle_general_pairing _
    (fun r => 2 * ∑ s, K r s * quaternionMatrix s j l)
    (fun r => generalCoefficient_plus_oneForm K r j l)]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem symmetric_product_expansion (A : Mat) (hs : symmetric A)
    (Q F : Fin 3 → ℝ) :
    (∑ r, ∑ s, A r s * Q s * (F r + ∑ t, A r t * F t)) =
      ∑ s, ∑ t, (A + A * A) s t * Q s * F t := by
  simp only [Fin.sum_univ_three, Matrix.add_apply, Matrix.mul_apply,
    hs 1 0, hs 2 0, hs 2 1]
  ring

/-- The product of the full Weyl block with the curvature connection
produces exactly A+A². -/
theorem plus_bundle_general_pairing (A : Mat) (hs : symmetric A)
    (j l : Fin 4) (N P : Mat) :
    (∑ i, ∑ k, generalCoefficient quaternionMatrix A i k j l *
      matrixPairing (bundleCurvatureAction A i k N) P) =
      ∑ r, ∑ s, (A + A * A) r s * quaternionMatrix r j l *
        matrixPairing (matrixAction s N) P := by
  rw [generalCoefficient_bundle_pairing]
  exact symmetric_product_expansion A hs (fun r => quaternionMatrix r j l)
    (fun s => matrixPairing (matrixAction s N) P)

private theorem quaternion_pairing_sum_general (r : Fin 3) (x y : Vec) :
    (∑ j, ∑ l, quaternionMatrix r j l * x j * y l) =
      -inner ℝ (quaternion r x) y := by
  rw [Finset.sum_comm]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← quaternionMatrix_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [quaternionMatrix_skew r j l]
  ring

private theorem matrixAction_mixed_slices_pairing (r s : Fin 3) (Z : Tensor) :
    (∑ j, ∑ l, quaternionMatrix r j l *
      matrixPairing (matrixAction s (rawMatrixSlice Z.matrix j))
        (rawMatrixSlice Z.matrix l)) =
      -(∑ a, ∑ b, inner ℝ (quaternion r (matrixRotation s Z a b)) (Z.matrix a b)) := by
  simp only [matrixPairing, Finset.mul_sum, rawMatrixSlice, matrixRotation_slice]
  rw [sum_four_swap]
  simp only [← mul_assoc, quaternion_pairing_sum_general, Finset.sum_neg_distrib]

theorem generalMixedAction_pairing_sum (A : Mat) (Z : Tensor) :
    rawPairing (generalMixedAction A Z.matrix) Z.matrix =
      ∑ r, ∑ s, A r s *
        (∑ a, ∑ b, inner ℝ (quaternion r (matrixRotation s Z a b)) (Z.matrix a b)) := by
  simp only [rawPairing_vectors, generalMixedAction, rawMatrixRotation_matrix,
    sum_inner, real_inner_smul_left]
  rw [sum_four_swap]
  simp only [Finset.mul_sum]

/-- The complete bundle half-commutator in an arbitrary orthonormal frame. -/
theorem generalBundleGreenContraction_plus (A : Mat) (hs : symmetric A) (Z : Tensor) :
    generalBundleGreenContraction (generalCoefficient quaternionMatrix A) A Z =
      -(1 / 2 : ℝ) * rawPairing (generalMixedAction (A + A * A) Z.matrix) Z.matrix := by
  simp only [generalBundleGreenContraction, plus_bundle_general_pairing A hs]
  rw [sum_four_swap]
  have hterm (r s : Fin 3) :
      (∑ j, ∑ l, (A + A * A) r s * quaternionMatrix r j l *
        matrixPairing (matrixAction s (rawMatrixSlice Z.matrix j))
          (rawMatrixSlice Z.matrix l)) =
      -((A + A * A) r s *
        (∑ a, ∑ b, inner ℝ (quaternion r (matrixRotation s Z a b)) (Z.matrix a b))) := by
    calc
      _ = (A + A * A) r s * (∑ j, ∑ l, quaternionMatrix r j l *
          matrixPairing (matrixAction s (rawMatrixSlice Z.matrix j))
            (rawMatrixSlice Z.matrix l)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by rw [matrixAction_mixed_slices_pairing]; ring
  simp_rw [hterm]
  simp only [Finset.sum_neg_distrib]
  rw [generalMixedAction_pairing_sum]
  ring

theorem generalBundleGreenContraction_polynomial (A : Mat)
    (hs : symmetric A) (ht : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    generalBundleGreenContraction (generalCoefficient quaternionMatrix A) A Z =
      (2 / 3 : ℝ) * Matrix.trace (A * A) * Z.squaredNorm -
        4 * generalGradientForm A Z - 4 * generalGradientForm (traceFreeSquare A) Z := by
  rw [generalBundleGreenContraction_plus A hs]
  exact generalMixedAction_linear_square_pairing A hs ht Z hz hb

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

/-- The covector contraction of the full plus block gives its squared
matrix norm, including all off-diagonal entries. -/
theorem plus_generalCoefficient_ricci (A U : Mat)
    (hs : symmetric A) (ht : traceFree A) (l h : Fin 4) :
    (1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k, generalCoefficient quaternionMatrix A i k j l *
      (generalCoefficient quaternionMatrix (1 + A) i k j h +
        generalCoefficient Angular.oppositeMatrix (1 + U) i k j h)) =
      (Matrix.trace (A * A) / 2) * (if l = h then 1 else 0) := by
  simp only [mul_add, Finset.sum_add_distrib]
  have hz (j : Fin 4) := generalCoefficient_pairing_zero _ _ mixed_twoForm_pairing
    A (1 + U) j l j h
  simp_rw [hz]
  simp only [Finset.sum_const_zero, mul_zero, add_zero]
  have hAB : symmetric (Aᵀ * (1 + A)) := by
    rw [transpose_mul_one_add A hs]
    exact symmetric_add_square A hs
  rw [generalCoefficient_ricci quaternionMatrix plus_twoForm_pairing
    Angular.quaternionMatrix_transpose Angular.quaternionMatrix_anticommutator _ _ hAB,
    transpose_mul_one_add A hs, Matrix.trace_add]
  have htrace : Matrix.trace A = 0 := ht
  rw [htrace]
  ring

theorem generalEinsteinCoefficient_eq_tensor (A U : Mat) (i k j l : Fin 4) :
    generalEinsteinCoefficient A U i k j l =
      Angular.einsteinCurvatureTensor A U i k l j := by
  simp only [generalEinsteinCoefficient, generalCoefficient_eq_blockTensor,
    Angular.einsteinCurvatureTensor, Pi.add_apply]

theorem generalCovectorGreenContraction_plus (A U : Mat)
    (hs : symmetric A) (ht : traceFree A) (Z : Tensor) :
    covectorGreenContraction (generalCoefficient quaternionMatrix A)
      (generalEinsteinCoefficient A U) Z =
        (Matrix.trace (A * A) / 2) * Z.squaredNorm := by
  simp only [covectorGreenContraction, generalEinsteinCoefficient,
    plus_generalCoefficient_ricci A U hs ht]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  rw [← Finset.mul_sum, matrixSlice_self_sum]

/-- Both actual curvature actions in the plus derivative Green term,
with the full symmetric Weyl coefficient matrix. -/
theorem general_plus_green_polynomial (A U : Mat)
    (hs : symmetric A) (ht : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    generalBundleGreenContraction (generalCoefficient quaternionMatrix A) A Z +
      covectorGreenContraction (generalCoefficient quaternionMatrix A)
        (generalEinsteinCoefficient A U) Z =
      (7 / 6 : ℝ) * Matrix.trace (A * A) * Z.squaredNorm -
        4 * generalGradientForm A Z - 4 * generalGradientForm (traceFreeSquare A) Z := by
  rw [generalBundleGreenContraction_polynomial A hs ht Z hz hb,
    generalCovectorGreenContraction_plus A U hs ht]
  ring

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

/-- The complete self-dual raw Green contraction has the invariant
polynomial required by the weighted Hessian estimate. -/
theorem general_plus_rawGreen (A U : Mat)
    (hs : symmetric A) (ht : traceFree A)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    derivativeGreenContraction (generalCoefficient quaternionMatrix A)
      (generalRawCurvatureCommutator A (generalEinsteinCoefficient A U) Z) Z =
      (7 / 6 : ℝ) * Matrix.trace (A * A) * Z.squaredNorm -
        4 * generalGradientForm A Z - 4 * generalGradientForm (traceFreeSquare A) Z := by
  rw [general_rawGreen_decomposition]
  exact general_plus_green_polynomial A U hs ht Z hz hb

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

local instance metricContractionNormedRing_ra3aad3_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricContractionNormedSpace_ra3aad3_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricContractionNormedAlgebra_ra3aad3_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
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
local instance curvatureIntegralNormedAlgebra_ra3aad3_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
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
local instance curvatureIntegralNormedAlgebra_ra3aad3_2 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem continuousGradientSlice (d : MetricGreenData g μ) (i : Fin 4) :
    Continuous (frameGradientSlice g i) :=
  matrixVectorMap.continuous.comp (d.continuousGradient i)

theorem continuousHessianSlice (d : MetricGreenData g μ) (i j : Fin 4) :
    Continuous (frameHessianSlice g i j) :=
  matrixVectorMap.continuous.comp (d.continuousHessian i j)

theorem continuousThirdSlice (d : MetricGreenData g μ) (i j k : Fin 4) :
    Continuous (frameThirdSlice g i j k) :=
  matrixVectorMap.continuous.comp (d.continuousThird i j k)

/-- The actual plus-block derivative Green integral, before selecting any
pointwise spectral coordinates. The only new premise is the classical
curvature-block decomposition. -/
theorem plusCurvatureGreen_oai (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
      (dm i ((d.flow i).map t e)) t) :
    (∫ e, weightedQuadratic
      (fun X => derivativePairing
        (generalCoefficient quaternionMatrix (plusWeyl g e.base e.frame)) X X)
      (m e) (plusWeylHessian g e.base e.frame)
      (weightTensor (WithLp.toLp 2 (fun i => dm i e))
        (plusGradientTensor g e.base e.frame)) ∂μ) =
    ∫ e, m e * (7 * normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 *
        weylGradientEnergy (plusWeylGradient g e.base e.frame) -
      4 * weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) -
      4 * weylMatrixEnergy (traceFreeSquare (plusWeyl g e.base e.frame))
        (plusWeylGradient g e.base e.frame)) ∂μ := by
  have hcoef (p : Averages.CurvatureIndex) (e : FrameBundle g) :
      framePlusCoefficient g p e =
        generalCoefficient quaternionMatrix (plusWeyl g e.base e.frame)
          p.1.1 p.1.2 p.2.1 p.2.2 :=
    (generalCoefficient_eq_blockTensor _ _ _ _ _ _).symm
  have hdcoef (p : Averages.CurvatureIndex) (e : FrameBundle g) :
      framePlusCoefficientDerivative g p e =
        generalCoefficient quaternionMatrix (plusWeylGradient g e.base e.frame p.1.2)
          p.1.1 p.1.2 p.2.1 p.2.2 :=
    (generalCoefficient_eq_blockTensor _ _ _ _ _ _).symm
  have hgreen := weighted_metric_curvature_green g d.flow m dm
    (fun p => by
      convert! (generalCoefficientMap quaternionMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
        d.continuousWeyl using 1
      all_goals try with_reducible_and_instances rfl
      funext e
      exact hcoef p e)
    (fun p => by
      convert! (generalCoefficientMap quaternionMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
        (d.continuousGradient p.1.2) using 1
      all_goals try with_reducible_and_instances rfl
      funext e
      exact hdcoef p e)
    d.continuousGradientSlice d.continuousHessianSlice d.continuousThirdSlice
    (by
      intro i j l e
      simp only [hdcoef]
      exact generalCoefficient_divergence quaternionMatrix _ (d.gradientBianchi e) i j l)
    (by
      intro i k j l e
      simp only [hcoef]
      exact generalCoefficient_skew quaternionMatrix (fun s i j => quaternionMatrix_skew s j i) _ i k j l)
    hm
    (by
      intro p t e
      convert! (generalCoefficientMap quaternionMatrix p.1.1 p.1.2 p.2.1 p.2.2).hasFDerivAt.comp_hasDerivAt t
        (d.derivativeWeyl p.1.2 t e) using 1
      · funext s
        exact hcoef p ((d.flow p.1.2).map s e)
      · exact hdcoef p ((d.flow p.1.2).map t e))
    (fun k j t e => hasDerivAt_matrixVector (d.derivativeGradient k j t e))
    (fun k i j t e => hasDerivAt_matrixVector (d.derivativeHessian k i j t e))
  have hp (e : FrameBundle g) :
      derivativeGreenContraction
        (generalCoefficient quaternionMatrix (plusWeyl g e.base e.frame))
        (fun i k j => plusWeylThirdDerivative g e.base e.frame i k j -
          plusWeylThirdDerivative g e.base e.frame k i j)
        (plusGradientTensor g e.base e.frame) / 6 =
      7 * normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 *
        weylGradientEnergy (plusWeylGradient g e.base e.frame) -
      4 * weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) -
      4 * weylMatrixEnergy (traceFreeSquare (plusWeyl g e.base e.frame))
        (plusWeylGradient g e.base e.frame) := by
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
    rw [hr]
    simp only [plusGradientTensor]
    rw [general_plus_rawGreen _ _ (d.weyl.symmetric e) (d.weyl.traceFree e) _
      (gradientTensor_traceFree _ (d.gradientConstraints e).2)
      (gradientTensor_bianchi _ (d.gradientConstraints e).1 (d.gradientBianchi e)),
      trace_square_eq_six_norm_sq _ (d.weyl.symmetric e),
      gradientTensor_squaredNorm _ (d.gradientConstraints e).1]
    simp only [generalGradientForm,
      generalMatrixAction_gradient_pairing _ _ (d.gradientConstraints e).1]
    have he : Angular.gradientSquareNorm (plusWeylGradient g e.base e.frame) =
        6 * weylGradientEnergy (plusWeylGradient g e.base e.frame) := by
      rw [← gradientVector_norm_sq, ← real_inner_self_eq_norm_sq, gradientVector_pairing]
      unfold weylGradientEnergy
      ring
    rw [he]
    ring
  calc
    _ = (1 / 6 : ℝ) * (∫ e, ∑ p : Averages.CurvatureIndex,
        (m e * framePlusCoefficient g p e *
          matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
            (plusWeylHessian g e.base e.frame p.1.2 p.2.2) +
        dm p.1.2 e * framePlusCoefficient g p e *
          matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
            (plusWeylGradient g e.base e.frame p.2.2)) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with e
      rw [weightedQuadratic_derivative_green _
        (generalCoefficient_pair_swap quaternionMatrix (fun s i j => quaternionMatrix_skew s j i) _)]
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


end OAI
end

theorem solution.{u_1} : type_of% @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusCurvatureGreen_oai.{u_1} := @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusCurvatureGreen_oai.{u_1}
