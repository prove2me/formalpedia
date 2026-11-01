-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Geometry.FrameReflectionData.jointEnergyCancellation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:33:58.352395+00:00
-- url     : https://prove2.me/submissions/7f538697-0f8e-4b76-9ee6-04e4461a755c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C016
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
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
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

local instance metricWeylNormedRing_rd22daf_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricWeylNormedSpace_rd22daf_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricWeylNormedAlgebra_rd22daf_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
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

/-! The Ricci-commuted gradient equation for the actual metric. The two
classical slot identities remain explicit, while the differentiated trace
and curvature-divergence equations are derived. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance metricRicciNormedRing_rd22daf_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricRicciNormedSpace_rd22daf_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricRicciNormedAlgebra_rd22daf_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
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
local instance smoothWeylNormedSpace_rd22daf_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.smoothWeylNormedAlgebra
theorem regularizedBlockNorm_le (ε : ℝ) (hε : 0 ≤ ε) (A : Mat) :
    regularizedBlockNorm ε A ≤ normalizedBlockNorm A + ε := by
  rw [regularizedBlockNorm, Real.sqrt_le_left (add_nonneg (normalizedBlockNorm_nonneg A) hε)]
  nlinarith [normalizedBlockNorm_nonneg A]

theorem tendsto_regularizedBlockNorm (A : Mat) :
    Tendsto (fun ε => regularizedBlockNorm ε A) (𝓝 0) (𝓝 (normalizedBlockNorm A)) := by
  have hc : Continuous (fun ε => regularizedBlockNorm ε A) := by
    unfold regularizedBlockNorm
    fun_prop
  simpa only [regularizedBlockNorm_zero] using hc.tendsto 0

theorem tendsto_regularizedRadialDerivative (A Z : Mat) :
    Tendsto (fun ε => regularizedRadialDerivative ε A Z) (𝓝 0)
      (𝓝 (Matrix.trace (A * Z) / (6 * normalizedBlockNorm A))) := by
  by_cases ha : normalizedBlockNorm A = 0
  · have hA : A = 0 := (normalizedBlockNorm_eq_zero_iff A).mp ha
    subst A
    simp [regularizedRadialDerivative]
  · exact tendsto_const_nhds.div
      (tendsto_const_nhds.mul (tendsto_regularizedBlockNorm A))
      (mul_ne_zero (by norm_num) ha)

theorem abs_trace_mul_le_norm (A Z : Mat) (hZ : symmetric Z) :
    |Matrix.trace (A * Z)| ≤ 6 * normalizedBlockNorm A * normalizedBlockNorm Z := by
  have hzt : Zᵀ = Z := by ext i j; exact hZ j i
  have hp : matrixPairing A Z = Matrix.trace (A * Z) := by
    rw [matrixPairing_eq_trace, hzt]
  have h := real_inner_mul_inner_self_le (matrixVector A) (matrixVector Z)
  simp only [inner_matrixVector, matrixPairing_self_norm, hp] at h
  apply abs_le_of_sq_le_sq _
    (mul_nonneg (mul_nonneg (by norm_num) (normalizedBlockNorm_nonneg A))
      (normalizedBlockNorm_nonneg Z))
  nlinarith only [h]

/-- The regularized derivative has a bound independent of the smoothing
parameter. This is the domination needed at Weyl zeros. -/
theorem abs_regularizedRadialDerivative_le (ε : ℝ) (hε : 0 < ε)
    (A Z : Mat) (hZ : symmetric Z) :
    |regularizedRadialDerivative ε A Z| ≤ normalizedBlockNorm Z := by
  have hn := regularizedBlockNorm_pos ε hε A
  rw [regularizedRadialDerivative, abs_div, abs_of_pos (mul_pos (by norm_num) hn),
    div_le_iff₀ (mul_pos (by norm_num) hn)]
  calc
    _ ≤ 6 * normalizedBlockNorm A * normalizedBlockNorm Z := abs_trace_mul_le_norm A Z hZ
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (norm_le_regularizedBlockNorm ε A)
        (normalizedBlockNorm_nonneg Z)
      nlinarith only [h]

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
local instance greenDataNormedAlgebra_rd22daf_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
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
local instance greenDataNormedAlgebra_rd22daf_2 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
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

/-! The Ricci equation and its identity and varying-matrix Green
contractions in the actual arbitrary orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance metricContractionNormedRing_rd22daf_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricContractionNormedSpace_rd22daf_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricContractionNormedAlgebra_rd22daf_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
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

/-! Smooth approximation of the scalar deficit δ=2-v-b used in the
energy Bochner identity. -/

namespace PositiveEinsteinFour.Geometry

open TraceHessian Filter
open scoped _root_.Topology

noncomputable section

local instance deficitNormedRing_rd22daf_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance deficitNormedSpace_rd22daf_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance deficitNormedAlgebra_rd22daf_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem hasDerivAt_regularizedDeficit {A B : ℝ → Mat} {Z V : Mat} {t ε : ℝ}
    (hA : HasDerivAt A Z t) (hB : HasDerivAt B V t)
    (hsA : ∀ t, symmetric (A t)) (hsB : ∀ t, symmetric (B t)) (hε : 0 < ε) :
    HasDerivAt (fun s => regularizedDeficit ε (A s) (B s))
      (regularizedDeficitDerivative ε (A t) (B t) Z V) t := by
  convert! ((hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_regularizedBlockNorm hA hsA hε)).sub
    (hasDerivAt_regularizedBlockNorm hB hsB hε) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [regularizedDeficitDerivative, zero_sub]

theorem abs_regularizedDeficit_le {ε : ℝ} (hε : 0 ≤ ε) (he : ε ≤ 1)
    (A B : Mat) (hpinch : normalizedBlockNorm A + normalizedBlockNorm B < 2) :
    |regularizedDeficit ε A B| ≤ 6 := by
  have ha := regularizedBlockNorm_le ε hε A
  have hb := regularizedBlockNorm_le ε hε B
  have ha0 : 0 ≤ regularizedBlockNorm ε A := Real.sqrt_nonneg _
  have hb0 : 0 ≤ regularizedBlockNorm ε B := Real.sqrt_nonneg _
  have h := (abs_sub (2 - regularizedBlockNorm ε A) (regularizedBlockNorm ε B)).trans
    (add_le_add (abs_sub (2 : ℝ) (regularizedBlockNorm ε A)) (le_refl _))
  simp only [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
    abs_of_nonneg ha0, abs_of_nonneg hb0] at h
  exact h.trans (by linarith)

theorem abs_regularizedDeficitDerivative_le {ε : ℝ} (hε : 0 < ε)
    (A B Z V : Mat) (hZ : symmetric Z) (hV : symmetric V) :
    |regularizedDeficitDerivative ε A B Z V| ≤ normalizedBlockNorm Z + normalizedBlockNorm V := by
  unfold regularizedDeficitDerivative
  exact (abs_sub _ _).trans (by
    rw [abs_neg]
    exact add_le_add (abs_regularizedRadialDerivative_le ε hε A Z hZ)
      (abs_regularizedRadialDerivative_le ε hε B V hV))

theorem tendsto_regularizedDeficit (A B : Mat) :
    Tendsto (fun ε => regularizedDeficit ε A B) (𝓝 0) (𝓝 (regularizedDeficit 0 A B)) := by
  simpa only [regularizedDeficit, regularizedBlockNorm_zero] using
    (tendsto_const_nhds.sub (tendsto_regularizedBlockNorm A)).sub (tendsto_regularizedBlockNorm B)

theorem tendsto_regularizedDeficitDerivative (A B Z V : Mat) :
    Tendsto (fun ε => regularizedDeficitDerivative ε A B Z V) (𝓝 0)
      (𝓝 (regularizedDeficitDerivative 0 A B Z V)) := by
  simpa only [regularizedDeficitDerivative, regularizedRadialDerivative, regularizedBlockNorm_zero] using
    (tendsto_regularizedRadialDerivative A Z).neg.sub (tendsto_regularizedRadialDerivative B V)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Derivatives vanish almost everywhere on a level set. Countability of
the isolated points gives the one-dimensional statement; Fubini and
preservation of frame measure transfer it to the actual Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open Filter Set MeasureTheory EinsteinFour TraceHessian
open scoped _root_.Topology Manifold ContDiff

noncomputable section

/-- At a non-isolated point of a level set, the ordinary derivative is zero. -/
theorem derivative_zero_at_level_accPt {f : ℝ → ℝ} {x c v : ℝ}
    (hd : HasDerivAt f v x) (hx : f x = c)
    (ha : AccPt x (𝓟 {y | f y = c})) : v = 0 := by
  have hc : HasDerivWithinAt f 0 {y | f y = c} x :=
    (hasDerivWithinAt_const x {y | f y = c} c).congr
      (fun y hy => hy) hx
  exact ha.uniqueDiffWithinAt.eq_deriv _ hd.hasDerivWithinAt hc

/-- Nonzero derivatives on any one level form a countable set. -/
theorem countable_nonzero_derivative_on_level (f df : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x) (c : ℝ) :
    {x | f x = c ∧ df x ≠ 0}.Countable := by
  let s : Set ℝ := {x | f x = c}
  apply (countable_setOfPred_isolated_right_within (s := s)).mono
  intro x hx
  refine ⟨hx.1, ?_⟩
  have ha : ¬AccPt x (𝓟 s) := fun ha =>
    hx.2 (derivative_zero_at_level_accPt (hd x) hx.1 ha)
  have hb : 𝓝[s \ {x}] x = ⊥ := by
    simpa only [accPt_principal_iff_clusterPt, ClusterPt, nhdsWithin, not_neBot] using ha
  apply le_bot_iff.mp
  rw [← hb]
  apply nhdsWithin_mono
  intro y hy
  exact ⟨hy.1, by simp only [mem_singleton_iff]; exact ne_of_gt hy.2⟩

/-- Lebesgue almost everywhere, an ordinary derivative vanishes whenever
its function lies on a specified level. -/
theorem ae_derivative_zero_on_level (f df : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x) (c : ℝ) :
    ∀ᵐ x, f x = c → df x = 0 := by
  rw [ae_iff]
  simpa only [_root_.not_imp, not_not] using
    (countable_nonzero_derivative_on_level f df hd c).measure_zero volume

/-- A measure-preserving flow transfers the one-dimensional level-set
statement to its base measure; no measure-zero assertion is a premise. -/
theorem ae_flow_derivative_zero_on_level
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    (μ : Measure Ω) [SFinite μ]
    (φ : ℝ → Ω ≃ᵐ Ω)
    (hφ : Continuous (fun p : ℝ × Ω => φ p.1 p.2))
    (hp : ∀ t, MeasurePreserving (φ t) μ μ)
    (f df : Ω → ℝ) (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ t x, HasDerivAt (fun s => f (φ s x)) (df (φ t x)) t)
    (c : ℝ) : ∀ᵐ x ∂μ, f x = c → df x = 0 := by
  have hfc : Continuous (fun p : Ω × ℝ => f (φ p.2 p.1)) :=
    hf.comp (hφ.comp continuous_swap)
  have hdc : Continuous (fun p : Ω × ℝ => df (φ p.2 p.1)) :=
    hdf.comp (hφ.comp continuous_swap)
  have hP : MeasurableSet {p : Ω × ℝ | f (φ p.2 p.1) = c → df (φ p.2 p.1) = 0} := by
    simp only [imp_iff_not_or]
    exact (measurableSet_eq_fun hfc.measurable measurable_const).compl.union
      (measurableSet_eq_fun hdc.measurable measurable_const)
  have hline : ∀ᵐ x ∂μ, ∀ᵐ t : ℝ, f (φ t x) = c → df (φ t x) = 0 :=
    Filter.Eventually.of_forall (fun x => ae_derivative_zero_on_level
      (fun t => f (φ t x)) (fun t => df (φ t x)) (fun t => hd t x) c)
  obtain ⟨t, ht⟩ := ((Measure.ae_ae_comm hP).mp hline).exists
  rw [ae_iff] at ht ⊢
  calc
    μ {x | ¬(f x = c → df x = 0)} =
        μ ((φ t) ⁻¹' {x | ¬(f x = c → df x = 0)}) :=
      ((hp t).measure_preimage_equiv _).symm
    _ = 0 := ht

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local instance zeroLevelNormedRing_rd22daf_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance zeroLevelNormedSpace_rd22daf_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance zeroLevelNormedAlgebra_rd22daf_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
/-- The actual covariant Weyl gradient vanishes almost everywhere on the
zero set of its block. This justifies the zero-set case in the norm-weight
limit without assuming either Weyl block is everywhere nonzero. -/
theorem MetricGreenData.gradient_zero_ae_on_zero
    {g : SmoothMetric M} {μ : Measure (FrameBundle g)} [SFinite μ]
    (d : MetricGreenData g μ) :
    ∀ᵐ e ∂μ, plusWeyl g e.base e.frame = 0 →
      ∀ i, plusWeylGradient g e.base e.frame i = 0 := by
  have hc (i : Fin 4) (a b : Fin 3) :
      ∀ᵐ e ∂μ, plusWeyl g e.base e.frame a b = 0 →
        plusWeylGradient g e.base e.frame i a b = 0 :=
    ae_flow_derivative_zero_on_level μ (fun t => (d.flow i).map t)
      (d.flow i).continuous (d.flow i).preserves
      (fun e => plusWeyl g e.base e.frame a b)
      (fun e => plusWeylGradient g e.base e.frame i a b)
      ((matrixEntryMap a b).continuous.comp d.continuousWeyl)
      ((matrixEntryMap a b).continuous.comp (d.continuousGradient i))
      (fun t e => hasDerivAt_matrixEntry (d.derivativeWeyl i t e) a b) 0
  have hall : ∀ᵐ e ∂μ, ∀ i a b, plusWeyl g e.base e.frame a b = 0 →
      plusWeylGradient g e.base e.frame i a b = 0 :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun a => ae_all_iff.mpr (fun b => hc i a b)))
  filter_upwards [hall] with e he
  intro hz i
  ext a b
  apply he i a b
  exact congrArg (fun A : Mat => A a b) hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite Weyl block has the same derived gradient constraints and
zero-set calculus, using its actual parallel-frame derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem OppositeWeylData.gradientConstraints {d : MetricGreenData g μ}
    (o : OppositeWeylData d) (e : FrameBundle g) :
    (∀ i, TraceHessian.symmetric (minusWeylGradient g e.base e.frame i)) ∧
    (∀ i, TraceHessian.traceFree (minusWeylGradient g e.base e.frame i)) := by
  have hi (i : Fin 4) : TraceHessian.symmetric (minusWeylGradient g e.base e.frame i) ∧
      TraceHessian.traceFree (minusWeylGradient g e.base e.frame i) := by
    obtain ⟨e₀, he⟩ := ((d.flow i).map 0).surjective e
    change (d.flow i).map 0 e₀ = e at he
    have hs := symmetric_of_hasDerivAt (o.derivativeWeyl i 0 e₀)
      (fun t => o.symmetric ((d.flow i).map t e₀))
    have ht := traceFree_of_hasDerivAt (o.derivativeWeyl i 0 e₀)
      (fun t => o.traceFree ((d.flow i).map t e₀))
    rw [he] at hs ht
    exact ⟨hs, ht⟩
  exact ⟨fun i => (hi i).1, fun i => (hi i).2⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite Bianchi triple becomes the positive triple after
reflecting only the derivative index. This gives the same invariant Kato
bound for the actual opposite Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem reflectedGradient_energy (Z : Angular.Gradient) :
    weylGradientEnergy (reflectedGradient Z) = weylGradientEnergy Z := by
  unfold weylGradientEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold matrixPairing
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [reflectedGradient, Matrix.smul_apply, smul_eq_mul]
  calc
    _ = orientationSign i ^ 2 * (Z i a b * Z i a b) := by ring
    _ = _ := by rw [orientationSign_sq, one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The regularized scalar Weyl equation follows from ordinary derivatives
of the actual block and its proved matrix Laplacian. Test functions are
arbitrary smooth flow weights, ready for the polynomial coupling test. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem regularizedRadialField_derivative (d : MetricGreenData g μ)
    (ε : ℝ) (hε : 0 < ε) (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => d.regularizedRadialField ε hε i ((d.flow i).map s e))
      (d.regularizedSecondField ε hε i ((d.flow i).map t e)) t :=
  hasDerivAt_regularizedRadialDerivative (d.derivativeWeyl i t e)
    (d.derivativeGradient i i t e) (fun s => d.weyl.symmetric ((d.flow i).map s e)) hε

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normEquationNormedRing
local instance normEquationNormedSpace_rd22daf_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normEquationNormedAlgebra
/-- The weak scalar norm equation at positive regularization. Its matrix
Laplacian term is fixed by the proved Bianchi commutator equation. -/
theorem testedRegularizedNormEquation (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (ε : ℝ) (hε : 0 < ε) (k : C(FrameBundle g, ℝ))
    (dk : Fin 4 → C(FrameBundle g, ℝ))
    (hk : ∀ i t e, HasDerivAt (fun s => k ((d.flow i).map s e))
      (dk i ((d.flow i).map t e)) t) :
    (∫ e, k e * ((weylGradientEnergy (plusWeylGradient g e.base e.frame) +
        Matrix.trace (plusWeyl g e.base e.frame * weylLaplacian (plusWeyl g e.base e.frame)) / 6 -
        ∑ i, (d.regularizedRadialField ε hε i e) ^ 2) / d.regularizedNormField ε e) +
      ∑ i, dk i e * d.regularizedRadialField ε hε i e ∂μ) = 0 := by
  let P := d.regularizedRadialField ε hε
  let Q := d.regularizedSecondField ε hε
  let F : Fin 4 → C(FrameBundle g, ℝ) := fun i => k * P i
  let D : Fin 4 → C(FrameBundle g, ℝ) := fun i => dk i * P i + k * Q i
  have hd (i) : (∫ e, D i e ∂μ) = 0 := by
    apply Averages.integral_flow_derivative_zero μ (d.flow i).map
      (d.flow i).continuous (d.flow i).preserves (F i) (D i)
    intro t e
    exact (hk i t e).mul (d.regularizedRadialField_derivative ε hε i t e)
  have hi (i : Fin 4) : Integrable (fun e => D i e) μ :=
    (D i).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsum : (∫ e, ∑ i, D i e ∂μ) = 0 := by
    rw [integral_finsetSum _ (fun i _ => hi i)]
    simp only [hd, Finset.sum_const_zero]
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with e
  have heq := regularizedRadialSecond_sum ε (plusWeyl g e.base e.frame)
    (plusWeylGradient g e.base e.frame) (plusWeylHessian g e.base e.frame)
    (d.gradientConstraints e).1 (metric_weyl_trace g d.weyl e)
  change k e * _ + (∑ i, dk i e * P i e) =
    ∑ i, (dk i e * P i e + k e * Q i e)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  change (∑ i, Q i e) = _ at heq
  rw [heq]
  dsimp only [regularizedNormField, regularizedRadialField, ContinuousMap.coe_mk]
  ring

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability at a zero Weyl norm is obtained from uniformly bounded
regularized energies and Fatou's lemma. No integrability of the singular
quotient is assumed in the limiting argument. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter TraceHessian
open scoped BigOperators _root_.Topology

noncomputable section

theorem integrable_of_ae_limit_norm_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : ℕ → Ω → ℝ) (f : Ω → ℝ) (C : ℝ)
    (hF : ∀ n, Integrable (F n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, (∫ x, ‖F n x‖ ∂μ) ≤ C) : Integrable f μ := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (hF n).aestronglyMeasurable) hlim, ?_⟩
  have hf : (∫⁻ x, ‖f x‖ₑ ∂μ) ≤
      liminf (fun n => ∫⁻ x, ‖F n x‖ₑ ∂μ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => ‖F n x‖ₑ) atTop ∂μ :=
        lintegral_congr_ae (hlim.mono (fun x hx => hx.enorm.liminf_eq.symm))
      _ ≤ _ := lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.enorm)
  have hb : liminf (fun n => ∫⁻ x, ‖F n x‖ₑ ∂μ) atTop ≤ ENNReal.ofReal C := by
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    apply iSup_le
    intro n
    refine (iInf₂_le n le_rfl).trans ?_
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hF n)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  exact lt_of_le_of_lt (hf.trans hb) ENNReal.ofReal_lt_top

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationFrameClass_proj
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The singular Weyl energy quotient is integrable. The refined Kato
inequality is kept as a local intermediate input, to be supplied by the
pointwise Bianchi parametrization; no weak norm equation is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

local instance normIntegrabilityNormedRing_rd22daf_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance normIntegrabilityNormedSpace_rd22daf_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance normIntegrabilityNormedAlgebra_rd22daf_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem regularized_norm_laplacian_split (ε : ℝ) (A : Mat) (e p : ℝ) :
    (e + Matrix.trace (A * weylLaplacian A) / 6 - p) / regularizedBlockNorm ε A =
      (e - p) / regularizedBlockNorm ε A +
        regularizedRadialDerivative ε A (weylLaplacian A) := by
  unfold regularizedRadialDerivative
  ring

theorem weylGradientEnergy_nonneg (Z : Fin 4 → Mat) : 0 ≤ weylGradientEnergy Z := by
  unfold weylGradientEnergy matrixPairing
  exact div_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun a _ =>
    Finset.sum_nonneg (fun b _ => mul_self_nonneg _)))) (by norm_num)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

local instance normIntegrabilityNormedRing_rd22daf_2 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance normIntegrabilityNormedSpace_rd22daf_2 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance normIntegrabilityNormedAlgebra_rd22daf_2 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem regularizedEnergyQuotient_bound (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hkato : ∀ e : FrameBundle g, (5 / 3 : ℝ) *
      ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame))
    (ε : ℝ) (hε : 0 < ε) :
    (∫ e, weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      regularizedBlockNorm ε (plusWeyl g e.base e.frame) ∂μ) ≤
      (5 / 2 : ℝ) * ∫ e, normalizedBlockNorm (weylLaplacian (plusWeyl g e.base e.frame)) ∂μ := by
  let E := d.gradientEnergyField
  let N := d.regularizedNormField ε
  let P : C(FrameBundle g, ℝ) := ⟨fun e => ∑ i, (d.regularizedRadialField ε hε i e) ^ 2,
    by fun_prop⟩
  let T : C(FrameBundle g, ℝ) :=
    ⟨fun e => regularizedRadialDerivative ε (plusWeyl g e.base e.frame)
      (weylLaplacian (plusWeyl g e.base e.frame)),
      continuous_regularizedRadialDerivative ε hε _ _ d.continuousWeyl
        (continuous_weylLaplacian.comp d.continuousWeyl)⟩
  let L := d.laplacianNormField
  have hN e : 0 < N e := regularizedBlockNorm_pos ε hε _
  let F : C(FrameBundle g, ℝ) := ⟨fun e => E e / N e,
    E.continuous.div N.continuous (fun e => (hN e).ne')⟩
  let Q : C(FrameBundle g, ℝ) := ⟨fun e => (E e - P e) / N e + T e,
    ((E.continuous.sub P.continuous).div N.continuous (fun e => (hN e).ne')).add T.continuous⟩
  have hQ : (∫ e, Q e ∂μ) = 0 := by
    have h := d.testedRegularizedNormEquation ε hε (ContinuousMap.const _ 1)
      (fun _ => ContinuousMap.const _ 0) (by intro i t e; exact hasDerivAt_const t 1)
    simpa only [Q, E, N, P, T, ContinuousMap.coe_const, Function.const_apply, one_mul, zero_mul,
      Finset.sum_const_zero, add_zero, regularizedNormField, regularizedRadialField,
      gradientEnergyField, gradientMap, ContinuousMap.coe_mk, regularized_norm_laplacian_split] using h
  have hpoint (e : FrameBundle g) : F e ≤ (5 / 2 : ℝ) * (Q e + L e) := by
    have hP := regularized_radial_energy_le ε hε (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame)
    have hK := hkato e
    change P e ≤ _ at hP
    change _ ≤ E e at hK
    have he : E e ≤ (5 / 2 : ℝ) * (E e - P e) := by linarith
    have hd := div_le_div_of_nonneg_right he (hN e).le
    have ht := (abs_le.mp (abs_regularizedRadialDerivative_le ε hε
      (plusWeyl g e.base e.frame) (weylLaplacian (plusWeyl g e.base e.frame))
      (weylLaplacian_symmetric _ (d.weyl.symmetric e)))).1
    change -L e ≤ T e at ht
    rw [mul_div_assoc] at hd
    change E e / N e ≤ (5 / 2 : ℝ) * ((E e - P e) / N e + T e + L e)
    nlinarith only [hd, ht]
  have hFi : Integrable F μ := F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hQi : Integrable Q μ := Q.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hLi : Integrable L μ := L.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ e, F e ∂μ) ≤ (5 / 2 : ℝ) * ∫ e, L e ∂μ
  calc
    _ ≤ ∫ e, (5 / 2 : ℝ) * (Q e + L e) ∂μ :=
      integral_mono hFi ((hQi.add hLi).const_mul _) hpoint
    _ = (5 / 2 : ℝ) * ∫ e, L e ∂μ := by
      rw [integral_const_mul, integral_add hQi hLi, hQ, zero_add]

theorem integrableEnergyQuotient (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hkato : ∀ e : FrameBundle g, (5 / 3 : ℝ) *
      ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame)) :
    Integrable (fun e => weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      normalizedBlockNorm (plusWeyl g e.base e.frame)) μ := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let F : ℕ → FrameBundle g → ℝ := fun n e =>
    weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      regularizedBlockNorm (ε n) (plusWeyl g e.base e.frame)
  apply integrable_of_ae_limit_norm_bound μ F _
    ((5 / 2 : ℝ) * ∫ e, d.laplacianNormField e ∂μ)
  · intro n
    exact (d.gradientEnergyField.continuous.div (d.regularizedNormField (ε n)).continuous
      (fun e => (regularizedBlockNorm_pos (ε n) (hε n) _).ne')).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · filter_upwards [d.gradient_zero_ae_on_zero] with e he
    by_cases hv : normalizedBlockNorm (plusWeyl g e.base e.frame) = 0
    · have hA := (normalizedBlockNorm_eq_zero_iff _).mp hv
      have hZ := he hA
      have hz : weylGradientEnergy (plusWeylGradient g e.base e.frame) = 0 := by
        simp only [weylGradientEnergy, hZ, matrixPairing, Matrix.zero_apply, mul_zero,
          Finset.sum_const_zero, zero_div]
      simp only [F, hz, zero_div]
      exact tendsto_const_nhds
    · exact tendsto_const_nhds.div ((tendsto_regularizedBlockNorm _).comp hεlim) hv
  · intro n
    have heq : (fun e => ‖F n e‖) = F n := by
      funext e
      apply Real.norm_of_nonneg
      exact div_nonneg (weylGradientEnergy_nonneg _) (regularizedBlockNorm_pos (ε n) (hε n) _).le
    rw [heq]
    exact d.regularizedEnergyQuotient_bound hkato (ε n) (hε n)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar Weyl equation at zero regularization. Its singular energy
term is controlled by the proved integrable energy quotient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

theorem abs_scalarNormExpression_le (ε : ℝ) (hε : 0 < ε)
    (A : Mat) (Z : Fin 4 → Mat) (hA : symmetric A)
    (hz : normalizedBlockNorm A = 0 → Z = 0)
    (hk : ‖blockRadialGradient A Z‖ ^ 2 ≤ weylGradientEnergy Z) :
    |scalarNormExpression ε A Z| ≤ weylGradientEnergy Z / normalizedBlockNorm A +
      normalizedBlockNorm (weylLaplacian A) := by
  have he := weylGradientEnergy_nonneg Z
  have hn := regularizedBlockNorm_pos ε hε A
  have hp := regularized_radial_energy_le ε hε A Z
  have hpn : 0 ≤ ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hq : 0 ≤ (weylGradientEnergy Z -
      ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) / regularizedBlockNorm ε A :=
    div_nonneg (by linarith) hn.le
  have hb : (weylGradientEnergy Z -
      ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) / regularizedBlockNorm ε A ≤
      weylGradientEnergy Z / normalizedBlockNorm A := by
    by_cases hv : normalizedBlockNorm A = 0
    · have hZ := hz hv
      subst Z
      simp [weylGradientEnergy, matrixPairing, regularizedRadialDerivative]
    · exact (div_le_div_of_nonneg_right (sub_le_self _ hpn) hn.le).trans
        (div_le_div_of_nonneg_left he
          (lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm hv))
          (norm_le_regularizedBlockNorm ε A))
  exact (abs_add_le _ _).trans (add_le_add
    (by rwa [abs_of_nonneg hq])
    (abs_regularizedRadialDerivative_le ε hε A (weylLaplacian A)
      (weylLaplacian_symmetric A hA)))

theorem tendsto_scalarNormExpression (A : Mat) (Z : Fin 4 → Mat)
    (hz : normalizedBlockNorm A = 0 → Z = 0) :
    Tendsto (fun ε => scalarNormExpression ε A Z) (𝓝 0)
      (𝓝 (scalarNormExpression 0 A Z)) := by
  have ht := tendsto_regularizedRadialDerivative A (weylLaplacian A)
  have hp (i : Fin 4) : Tendsto (fun ε => regularizedRadialDerivative ε A (Z i))
      (𝓝 0) (𝓝 (regularizedRadialDerivative 0 A (Z i))) := by
    simpa [regularizedRadialDerivative, regularizedBlockNorm_zero] using
      tendsto_regularizedRadialDerivative A (Z i)
  have ht' : Tendsto (fun ε => regularizedRadialDerivative ε A (weylLaplacian A))
      (𝓝 0) (𝓝 (regularizedRadialDerivative 0 A (weylLaplacian A))) := by
    simpa [regularizedRadialDerivative, regularizedBlockNorm_zero] using ht
  by_cases hv : normalizedBlockNorm A = 0
  · have hZ := hz hv
    subst Z
    simpa [scalarNormExpression, weylGradientEnergy, matrixPairing,
      regularizedRadialDerivative] using ht'
  · exact ((tendsto_const_nhds.sub (tendsto_finsetSum _ (fun i _ => (hp i).pow 2))).div
      (by simpa only [regularizedBlockNorm_zero] using tendsto_regularizedBlockNorm A)
      (by simpa only [regularizedBlockNorm_zero] using hv)).add ht'

end
end PositiveEinsteinFour.Geometry
end


section

/-! Pass the actual weak norm equation through bounded smooth test
approximations, including their first derivatives. This is the limit used
for the polynomial multiplier in the two-block coupling. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem testedNormEquation_of_limits (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hkato : ∀ e : FrameBundle g, (5 / 3 : ℝ) *
      ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (k : ℕ → C(FrameBundle g, ℝ)) (dk : ℕ → Fin 4 → C(FrameBundle g, ℝ))
    (hk : ∀ n i t e, HasDerivAt (fun s => k n ((d.flow i).map s e))
      (dk n i ((d.flow i).map t e)) t)
    (k₀ : FrameBundle g → ℝ) (dk₀ : Fin 4 → FrameBundle g → ℝ)
    (hklim : ∀ e, Tendsto (fun n => k n e) atTop (𝓝 (k₀ e)))
    (hdlim : ∀ i e, Tendsto (fun n => dk n i e) atTop (𝓝 (dk₀ i e)))
    (C : ℝ) (hC : 0 ≤ C) (hkbound : ∀ n e, |k n e| ≤ C)
    (B : Fin 4 → C(FrameBundle g, ℝ)) (hdbound : ∀ n i e, |dk n i e| ≤ B i e) :
    (∫ e, k₀ e * scalarNormExpression 0 (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) +
      ∑ i, dk₀ i e * regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) ∂μ) = 0 := by
  let F : ℕ → FrameBundle g → ℝ := fun n e =>
    k n e * d.scalarNormField (ε n) (hε n) e +
      ∑ i, dk n i e * d.regularizedRadialField (ε n) (hε n) i e
  let H : FrameBundle g → ℝ := fun e =>
    weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      normalizedBlockNorm (plusWeyl g e.base e.frame) + d.laplacianNormField e
  let J : C(FrameBundle g, ℝ) := ⟨fun e =>
    ∑ i, B i e * normalizedBlockNorm (plusWeylGradient g e.base e.frame i), by
      apply continuous_finsetSum
      intro i _
      exact (B i).continuous.mul (continuous_normalizedBlockNorm.comp (d.continuousGradient i))⟩
  have hF (n) : Continuous (F n) := by
    exact ((k n).continuous.mul (d.scalarNormField (ε n) (hε n)).continuous).add
      (continuous_finsetSum _ (fun i _ => (dk n i).continuous.mul
        (d.regularizedRadialField (ε n) (hε n) i).continuous))
  have hH : Integrable H μ := (d.integrableEnergyQuotient hkato).add
    (d.laplacianNormField.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hconv : Tendsto (fun n => ∫ e, F n e ∂μ) atTop
      (𝓝 (∫ e, k₀ e * scalarNormExpression 0 (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) +
        ∑ i, dk₀ i e * regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame i) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun e => C * H e + J e)
    · exact fun n => (hF n).aestronglyMeasurable
    · exact (hH.const_mul C).add (J.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    · intro n
      filter_upwards [d.gradient_zero_ae_on_zero] with e he
      have hs := abs_scalarNormExpression_le (ε n) (hε n) _ _ (d.weyl.symmetric e)
        (fun hv => funext (he ((normalizedBlockNorm_eq_zero_iff _).mp hv)))
        (by
          have h := hkato e
          have hp := sq_nonneg ‖blockRadialGradient (plusWeyl g e.base e.frame)
            (plusWeylGradient g e.base e.frame)‖
          nlinarith)
      rw [Real.norm_eq_abs]
      change |k n e * d.scalarNormField (ε n) (hε n) e +
        ∑ i, dk n i e * d.regularizedRadialField (ε n) (hε n) i e| ≤ _
      calc
        _ ≤ |k n e * d.scalarNormField (ε n) (hε n) e| +
            ∑ i, |dk n i e * d.regularizedRadialField (ε n) (hε n) i e| :=
          (abs_add_le _ _).trans (add_le_add (le_refl _) (Finset.abs_sum_le_sum_abs _ _))
        _ ≤ C * H e + J e := by
          apply add_le_add
          · rw [abs_mul]
            exact mul_le_mul (hkbound n e) hs (abs_nonneg _) hC
          · change _ ≤ ∑ i, B i e * normalizedBlockNorm (plusWeylGradient g e.base e.frame i)
            apply Finset.sum_le_sum
            intro i _
            rw [abs_mul]
            exact mul_le_mul (hdbound n i e)
              (abs_regularizedRadialDerivative_le (ε n) (hε n) _ _ ((d.gradientConstraints e).1 i))
              (abs_nonneg _) ((abs_nonneg _).trans (hdbound n i e))
    · filter_upwards [d.gradient_zero_ae_on_zero] with e he
      apply Tendsto.add
      · exact (hklim e).mul ((tendsto_scalarNormExpression _ _
          (fun hv => funext (he ((normalizedBlockNorm_eq_zero_iff _).mp hv)))).comp hlim)
      · apply tendsto_finsetSum
        intro i _
        apply (hdlim i e).mul
        simpa only [regularizedRadialField, ContinuousMap.coe_mk, regularizedRadialDerivative,
          regularizedBlockNorm_zero, Function.comp_def] using
          (tendsto_regularizedRadialDerivative (plusWeyl g e.base e.frame)
            (plusWeylGradient g e.base e.frame i)).comp hlim
  have hz (n) : (∫ e, F n e ∂μ) = 0 := by
    have h := d.testedRegularizedNormEquation (ε n) (hε n) (k n) (dk n) (hk n)
    simpa only [F, scalarNormField, scalarNormExpression, regularizedNormField, regularizedRadialField,
      ContinuousMap.coe_mk, regularized_norm_laplacian_split] using h
  simp only [hz] at hconv
  exact tendsto_nhds_unique hconv tendsto_const_nhds

theorem testedNormEquation (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hkato : ∀ e : FrameBundle g, (5 / 3 : ℝ) *
      ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame))
    (k : C(FrameBundle g, ℝ)) (dk : Fin 4 → C(FrameBundle g, ℝ))
    (hk : ∀ i t e, HasDerivAt (fun s => k ((d.flow i).map s e))
      (dk i ((d.flow i).map t e)) t) :
    (∫ e, k e * scalarNormExpression 0 (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) +
      ∑ i, dk i e * regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) ∂μ) = 0 := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn k.continuous.continuousOn
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  let B : Fin 4 → C(FrameBundle g, ℝ) := fun i =>
    ⟨fun e => |dk i e|, (dk i).continuous.abs⟩
  apply d.testedNormEquation_of_limits hkato ε hε tendsto_one_div_add_atTop_nhds_zero_nat
    (fun _ => k) (fun _ => dk) (fun _ => hk) (fun e => k e) (fun i e => dk i e)
    (fun _ => tendsto_const_nhds) (fun _ _ => tendsto_const_nhds) |C| (abs_nonneg C)
    (fun _ e => ?_) B (fun _ _ _ => le_rfl)
  have hc : |k e| ≤ C := by simpa only [Real.norm_eq_abs] using hC e (Set.mem_univ e)
  exact hc.trans (le_abs_self C)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weak Bochner equation for the actual Weyl derivative energy.
This is the identity used to prove the sign of equation (16). -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem energyDerivative (d : MetricGreenData g μ) (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => d.gradientEnergyField ((d.flow i).map s e))
      (d.energyDerivativeField i ((d.flow i).map t e)) t := by
  have h := ((d.derivativeGradientVector i t e).inner ℝ
    (d.derivativeGradientVector i t e)).div_const 6
  convert! h using 1
  · funext s
    change weylGradientEnergy _ = inner ℝ (frameGradientVector g _) (frameGradientVector g _) / 6
    rw [frameGradientVector, gradientVector_pairing]
    rfl
  · change inner ℝ (frameGradientVector g _) (frameHessianVector g i _) / 3 = _
    rw [real_inner_comm (frameHessianVector g i _)]
    ring

theorem testedEnergyEquation (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
      (dm i ((d.flow i).map t e)) t) :
    (∫ e, m e * d.energyLaplacianField e +
      ∑ i, dm i e * d.energyDerivativeField i e ∂μ) = 0 := by
  let L : C(FrameBundle g, ℝ) := d.hessianIdentityField m dm
  let R : C(FrameBundle g, ℝ) :=
    ⟨fun e => m e * (-13 * weylGradientEnergy (plusWeylGradient g e.base e.frame) +
      20 * weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)),
      m.continuous.mul ((continuous_const.mul d.gradientEnergyField.continuous).add
        (continuous_const.mul d.matrixEnergyField.continuous))⟩
  have hL : Integrable L μ := L.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hR : Integrable R μ := R.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hG : (∫ e, L e ∂μ) = ∫ e, R e ∂μ := d.identityGreen m dm hm
  have hpoint (e : FrameBundle g) :
      m e * d.energyLaplacianField e + ∑ i, dm i e * d.energyDerivativeField i e =
        2 * (L e - R e) := by
    change m e * (hessianNormSq (plusWeylHessian g e.base e.frame) / 3 +
        26 * weylGradientEnergy (plusWeylGradient g e.base e.frame) -
        40 * weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)) +
      (∑ i, dm i e * (inner ℝ (frameGradientVector g e) (frameHessianVector g i e) / 3)) =
      2 * (weightedQuadratic hessianNormSq (m e) (plusWeylHessian g e.base e.frame)
        (weightTensor (WithLp.toLp 2 (fun i => dm i e)) (plusGradientTensor g e.base e.frame)) -
        m e * (-13 * weylGradientEnergy (plusWeylGradient g e.base e.frame) +
          20 * weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)))
    rw [weightedQuadratic_identity_green]
    simp only [plusGradientTensor, tensorGradientVector_gradientTensor _ (d.gradientConstraints e).1,
      frameGradientVector, frameHessianVector]
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    ring
  calc
    _ = ∫ e, 2 * (L e - R e) ∂μ := integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = 0 := by rw [integral_const_mul, integral_sub hL hR, hG, sub_self, mul_zero]

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weak energy equation tested against the actual nonsmooth deficit
δ=2-v-b. This supplies one side of the integration by parts in (16). -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem MetricGreenData.deficitEnergyEquation (d : MetricGreenData g μ) (o : OppositeWeylData d)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
        d.energyLaplacianField e +
      ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
        d.energyDerivativeField i e ∂μ) = 0 := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have hε1 (n) : ε n ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let m : ℕ → C(FrameBundle g, ℝ) := fun n =>
    ⟨fun e => regularizedDeficit (ε n) (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame),
      (continuous_const.sub ((d.regularizedNormField (ε n)).continuous)).sub
        ((continuous_regularizedBlockNorm (ε n)).comp o.continuousWeyl)⟩
  let dm : ℕ → Fin 4 → C(FrameBundle g, ℝ) := fun n i =>
    ⟨fun e => regularizedDeficitDerivative (ε n) (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i),
      ((d.regularizedRadialField (ε n) (hε n) i).continuous.neg).sub
        (continuous_regularizedRadialDerivative (ε n) (hε n) _ _ o.continuousWeyl (o.continuousGradient i))⟩
  let F : ℕ → C(FrameBundle g, ℝ) := fun n =>
    ⟨fun e => m n e * d.energyLaplacianField e + ∑ i, dm n i e * d.energyDerivativeField i e,
      ((m n).continuous.mul d.energyLaplacianField.continuous).add
        (continuous_finsetSum _ (fun i _ => (dm n i).continuous.mul
          (d.energyDerivativeField i).continuous))⟩
  have hF (n) : (∫ e, F n e ∂μ) = 0 := by
    apply d.testedEnergyEquation (m n) (dm n)
    intro i t e
    exact hasDerivAt_regularizedDeficit (d.derivativeWeyl i t e) (o.derivativeWeyl i t e)
      (fun s => d.weyl.symmetric ((d.flow i).map s e))
      (fun s => o.symmetric ((d.flow i).map s e)) (hε n)
  let H : C(FrameBundle g, ℝ) := ⟨fun e => 6 * |d.energyLaplacianField e| +
    ∑ i, (normalizedBlockNorm (plusWeylGradient g e.base e.frame i) +
      normalizedBlockNorm (minusWeylGradient g e.base e.frame i)) * |d.energyDerivativeField i e|, by
        apply Continuous.add (continuous_const.mul d.energyLaplacianField.continuous.abs)
        apply continuous_finsetSum
        intro i _
        exact ((continuous_normalizedBlockNorm.comp (d.continuousGradient i)).add
          (continuous_normalizedBlockNorm.comp (o.continuousGradient i))).mul
            (d.energyDerivativeField i).continuous.abs⟩
  have hc : Tendsto (fun n => ∫ e, F n e ∂μ) atTop
      (𝓝 (∫ e, regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
        d.energyLaplacianField e +
        ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
          d.energyDerivativeField i e ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence H
    · exact fun n => (F n).continuous.aestronglyMeasurable
    · exact H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · intro n
      filter_upwards [] with e
      rw [Real.norm_eq_abs]
      change |m n e * d.energyLaplacianField e + ∑ i, dm n i e * d.energyDerivativeField i e| ≤ _
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_regularizedDeficit_le (hε n).le (hε1 n) _ _
          (hpinch e)) (abs_nonneg _)
      · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_regularizedDeficitDerivative_le (hε n) _ _ _ _
          ((d.gradientConstraints e).1 i) ((o.gradientConstraints e).1 i)) (abs_nonneg _)
    · filter_upwards [] with e
      apply Tendsto.add
      · exact ((tendsto_regularizedDeficit _ _).comp hlim).mul tendsto_const_nhds
      · apply tendsto_finsetSum
        intro i _
        exact ((tendsto_regularizedDeficitDerivative _ _ _ _).comp hlim).mul tendsto_const_nhds
  simp only [hF] at hc
  exact tendsto_nhds_unique hc tendsto_const_nhds

end
end PositiveEinsteinFour.Geometry
end


section

/-! The invariant Bianchi refined Kato inequality for the metric. The weak
norm equations and singular quotient integrability follow from parallel-frame
covariant calculus. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem refinedKato (d : MetricGreenData g μ) (e : FrameBundle g) :
    (5 / 3 : ℝ) * ‖blockRadialGradient (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame) :=
  QuaternionFrame.blockRadialGradient_refined_kato _ _ (d.weyl.symmetric e)
    (d.weyl.traceFree e) (d.gradientConstraints e).1 (d.gradientConstraints e).2
    (d.gradientBianchi e)

theorem energyQuotient_integrable (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] :
    Integrable (fun e => weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      normalizedBlockNorm (plusWeyl g e.base e.frame)) μ :=
  d.integrableEnergyQuotient d.refinedKato

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The raw orthogonal-frame invariance used from Brin--Karcher, §1:
the uniform frame measure is invariant under a fixed reflection, and
parallel transport intertwines reflection with reversal of the first
flow direction. This gives integral and tensor identities for reflected frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem regularizedRadialDerivative_smul (ε : ℝ) (A Z : Mat) (c : ℝ) :
    regularizedRadialDerivative ε A (c • Z) = c * regularizedRadialDerivative ε A Z := by
  simp only [regularizedRadialDerivative, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

theorem reflectedGradient_radial_sum (ε : ℝ) (A : Mat) (Z : Angular.Gradient) :
    (∑ i, regularizedRadialDerivative ε A (reflectedGradient Z i) ^ 2) =
      ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [reflectedGradient, regularizedRadialDerivative_smul, mul_pow, orientationSign_sq, one_mul]

theorem scalarNormExpression_reflected (ε : ℝ) (A : Mat) (Z : Angular.Gradient) :
    scalarNormExpression ε A (reflectedGradient Z) = scalarNormExpression ε A Z := by
  unfold scalarNormExpression
  rw [reflectedGradient_energy, reflectedGradient_radial_sum]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)

include r in
theorem integral_reflection (F : FrameBundle g → ℝ) :
    (∫ e, F (frameReflection e) ∂μ) = ∫ e, F e ∂μ := by
  have h : MeasurePreserving (frameReflectionEquiv g) μ μ := r.preserves
  exact h.integral_comp' F

theorem reflectTest_derivative (k : C(FrameBundle g, ℝ))
    (dk : Fin 4 → C(FrameBundle g, ℝ))
    (hk : ∀ i t e, HasDerivAt (fun s => k ((d.flow i).map s e))
      (dk i ((d.flow i).map t e)) t) :
    ∀ i t e, HasDerivAt (fun s => r.reflectTest k ((d.flow i).map s e))
      (r.reflectTestDerivative dk i ((d.flow i).map t e)) t := by
  intro i t e
  have h := (hk i (orientationSign i * t) (frameReflection e)).comp t
    ((hasDerivAt_id t).const_mul (orientationSign i))
  convert! h using 1
  · funext s
    exact congrArg k (r.parallel i s e)
  · change orientationSign i * dk i (frameReflection ((d.flow i).map t e)) = _
    rw [r.parallel]
    ring

include r in
theorem opposite_testedNormEquation [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (k : C(FrameBundle g, ℝ)) (dk : Fin 4 → C(FrameBundle g, ℝ))
    (hk : ∀ i t e, HasDerivAt (fun s => k ((d.flow i).map s e))
      (dk i ((d.flow i).map t e)) t) :
    (∫ e, k e * scalarNormExpression 0 (minusWeyl g e.base e.frame)
        (minusWeylGradient g e.base e.frame) +
      ∑ i, dk i e * regularizedRadialDerivative 0 (minusWeyl g e.base e.frame)
        (minusWeylGradient g e.base e.frame i) ∂μ) = 0 := by
  let F : FrameBundle g → ℝ := fun e => r.reflectTest k e *
      scalarNormExpression 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
    ∑ i, r.reflectTestDerivative dk i e * regularizedRadialDerivative 0
      (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i)
  have hF : (∫ e, F e ∂μ) = 0 :=
    d.testedNormEquation d.refinedKato (r.reflectTest k) (r.reflectTestDerivative dk)
      (r.reflectTest_derivative k dk hk)
  rw [← r.integral_reflection F] at hF
  convert! hF using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with e
  have hZ : plusWeylGradient g (frameReflection e).base (frameReflection e).frame =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  change k e * _ + _ = F (frameReflection e)
  dsimp only [F, reflectTest, reflectTestDerivative, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  rw [frameReflection_involutive g e]
  change _ = k e * scalarNormExpression 0 (plusWeyl g e.base e.frame.reflect)
    (plusWeylGradient g e.base e.frame.reflect) + _
  dsimp only [frameReflection] at hZ ⊢
  rw [plusWeyl_reflect, hZ, scalarNormExpression_reflected]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [reflectedGradient, regularizedRadialDerivative_smul]
  symm
  calc
    _ = orientationSign i ^ 2 *
        (dk i e * regularizedRadialDerivative 0 (minusWeyl g e.base e.frame)
          (minusWeylGradient g e.base e.frame i)) := by ring
    _ = _ := by rw [orientationSign_sq, one_mul]

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability of the scalar weak equation and of its radial terms.
The estimates use the actual metric Kato bound, including the zero set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

namespace MetricGreenData

theorem scalarNorm_integrable (d : MetricGreenData g μ) :
    Integrable (fun e => scalarNormExpression 0 (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame)) μ := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  let H : FrameBundle g → ℝ := fun e =>
    weylGradientEnergy (plusWeylGradient g e.base e.frame) /
      normalizedBlockNorm (plusWeyl g e.base e.frame) + d.laplacianNormField e
  have hH : Integrable H μ := d.energyQuotient_integrable.add
    (d.laplacianNormField.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hF (n) : Integrable (fun e => d.scalarNormField (ε n) (hε n) e) μ :=
    (d.scalarNormField (ε n) (hε n)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply integrable_of_ae_limit_norm_bound μ
    (fun n e => d.scalarNormField (ε n) (hε n) e) _ (∫ e, H e ∂μ) hF
  · filter_upwards [d.gradient_zero_ae_on_zero] with e he
    exact (tendsto_scalarNormExpression _ _ (fun hv =>
      funext (he ((normalizedBlockNorm_eq_zero_iff _).mp hv)))).comp
        tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    apply integral_mono_ae (hF n).norm hH
    filter_upwards [d.gradient_zero_ae_on_zero] with e he
    rw [Real.norm_eq_abs]
    apply abs_scalarNormExpression_le (ε n) (hε n) _ _ (d.weyl.symmetric e)
    · intro hv
      exact funext (he ((normalizedBlockNorm_eq_zero_iff _).mp hv))
    · have hk := d.refinedKato e
      nlinarith [sq_nonneg ‖blockRadialGradient (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame)‖]

theorem radial_integrable (d : MetricGreenData g μ) (i : Fin 4) :
    Integrable (fun e => regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i)) μ := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  let H : C(FrameBundle g, ℝ) := ⟨fun e => normalizedBlockNorm
    (plusWeylGradient g e.base e.frame i),
    continuous_normalizedBlockNorm.comp (d.continuousGradient i)⟩
  have hF (n) : Integrable (fun e => d.regularizedRadialField (ε n) (hε n) i e) μ :=
    (d.regularizedRadialField (ε n) (hε n) i).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply integrable_of_ae_limit_norm_bound μ
    (fun n e => d.regularizedRadialField (ε n) (hε n) i e) _ (∫ e, H e ∂μ) hF
  · filter_upwards [] with e
    simpa only [ε, regularizedRadialField, ContinuousMap.coe_mk, Function.comp_def,
      regularizedRadialDerivative, regularizedBlockNorm_zero] using
      (tendsto_regularizedRadialDerivative (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i)).comp tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    apply integral_mono_ae (hF n).norm
      (H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    filter_upwards [] with e
    rw [Real.norm_eq_abs]
    exact abs_regularizedRadialDerivative_le (ε n) (hε n) _ _ ((d.gradientConstraints e).1 i)

end MetricGreenData

omit [IsFiniteMeasure μ] in
theorem integrable_continuous_weight {f : FrameBundle g → ℝ} (hf : Integrable f μ)
    (k : C(FrameBundle g, ℝ)) : Integrable (fun e => k e * f e) μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn k.continuous.continuousOn
  exact hf.bdd_mul k.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => hC e (Set.mem_univ e)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transport the weak energy equation through the actual reflected
frame. The reflected energy is the energy of the opposite Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)

include r

theorem oppositeEnergy_derivative (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => d.oppositeEnergyField ((d.flow i).map s e))
      (d.oppositeEnergyDerivativeField i ((d.flow i).map t e)) t :=
  r.reflectTest_derivative d.gradientEnergyField d.energyDerivativeField d.energyDerivative i t e

theorem totalEnergy_derivative (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => d.totalEnergyField ((d.flow i).map s e))
      (d.totalEnergyDerivativeField i ((d.flow i).map t e)) t :=
  (d.energyDerivative i t e).add (r.oppositeEnergy_derivative i t e)

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Test both actual scalar Weyl equations against the total derivative
energy. This is the norm-equation half of the cancellation in (16). -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem scalarNormExpression_frameReflection (ε : ℝ) (e : FrameBundle g) :
    scalarNormExpression ε (plusWeyl g (frameReflection e).base (frameReflection e).frame)
      (plusWeylGradient g (frameReflection e).base (frameReflection e).frame) =
    scalarNormExpression ε (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame) := by
  have hZ : plusWeylGradient g (frameReflection e).base (frameReflection e).frame =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  change scalarNormExpression ε (plusWeyl g e.base e.frame.reflect) _ = _
  rw [plusWeyl_reflect, hZ, scalarNormExpression_reflected]

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem opposite_scalarNorm_integrable :
    Integrable (fun e => scalarNormExpression 0 (minusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame)) μ := by
  have h := r.preserves.integrable_comp_of_integrable d.scalarNorm_integrable
  exact h.congr (Filter.Eventually.of_forall (scalarNormExpression_frameReflection 0))

theorem opposite_radial_integrable (i : Fin 4) :
    Integrable (fun e => regularizedRadialDerivative 0 (minusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame i)) μ := by
  have h := (r.preserves.integrable_comp_of_integrable (d.radial_integrable i)).const_mul
    (orientationSign i)
  apply h.congr
  filter_upwards [] with e
  change orientationSign i * regularizedRadialDerivative 0
    (plusWeyl g e.base e.frame.reflect) (plusWeylGradient g e.base e.frame.reflect i) = _
  rw [plusWeyl_reflect, plusWeylGradient_reflect, regularizedRadialDerivative_smul,
    ← mul_assoc, ← pow_two, orientationSign_sq, one_mul]

theorem jointNormEnergyEquation :
    (∫ e, d.totalEnergyField e *
      (scalarNormExpression 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
       scalarNormExpression 0 (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)) +
      ∑ i, d.totalEnergyDerivativeField i e *
        (regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame i) +
         regularizedRadialDerivative 0 (minusWeyl g e.base e.frame)
          (minusWeylGradient g e.base e.frame i)) ∂μ) = 0 := by
  let E := d.totalEnergyField
  let D := d.totalEnergyDerivativeField
  let P : FrameBundle g → ℝ := fun e => E e *
      scalarNormExpression 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
    ∑ i, D i e * regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i)
  let Q : FrameBundle g → ℝ := fun e => E e *
      scalarNormExpression 0 (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame) +
    ∑ i, D i e * regularizedRadialDerivative 0 (minusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame i)
  have hp : (∫ e, P e ∂μ) = 0 :=
    d.testedNormEquation d.refinedKato E D r.totalEnergy_derivative
  have hq : (∫ e, Q e ∂μ) = 0 := r.opposite_testedNormEquation E D r.totalEnergy_derivative
  have hpi : Integrable P μ :=
    (integrable_continuous_weight d.scalarNorm_integrable E).add
      (integrable_finsetSum _ (fun i _ => integrable_continuous_weight (d.radial_integrable i) (D i)))
  have hqi : Integrable Q μ :=
    (integrable_continuous_weight r.opposite_scalarNorm_integrable E).add
      (integrable_finsetSum _ (fun i _ =>
        integrable_continuous_weight (r.opposite_radial_integrable i) (D i)))
  have hsum : (∫ e, P e + Q e ∂μ) = 0 := by
    rw [integral_add hpi hqi, hp, hq, add_zero]
  convert! hsum using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with e
  dsimp only [P, Q, E, D]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite and summed deficit tests, obtained from the same
proved plus-block energy identity by reflection of the actual frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem minusWeylGradient_reflect (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (i : Fin 4) :
    minusWeylGradient g c e.reflect i = orientationSign i • plusWeylGradient g c e i := by
  have h := plusWeylGradient_reflect g c e.reflect i
  rw [e.reflect_reflect] at h
  have h' := congrArg (fun A : Mat => orientationSign i • A) h
  rw [smul_smul, ← pow_two, orientationSign_sq, one_smul] at h'
  exact h'.symm

theorem regularizedDeficit_swap (ε : ℝ) (A B : Mat) :
    regularizedDeficit ε B A = regularizedDeficit ε A B := by
  unfold regularizedDeficit
  ring

theorem deficit_frameReflection (e : FrameBundle g) :
    regularizedDeficit 0 (plusWeyl g (frameReflection e).base (frameReflection e).frame)
      (minusWeyl g (frameReflection e).base (frameReflection e).frame) =
    regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) := by
  change regularizedDeficit 0 (plusWeyl g e.base e.frame.reflect)
    (minusWeyl g e.base e.frame.reflect) = _
  rw [plusWeyl_reflect, minusWeyl_reflect, regularizedDeficit_swap]

theorem deficitDerivative_frameReflection (e : FrameBundle g) (i : Fin 4) :
    regularizedDeficitDerivative 0 (plusWeyl g (frameReflection e).base (frameReflection e).frame)
      (minusWeyl g (frameReflection e).base (frameReflection e).frame)
      (plusWeylGradient g (frameReflection e).base (frameReflection e).frame i)
      (minusWeylGradient g (frameReflection e).base (frameReflection e).frame i) =
    orientationSign i * regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame)
      (minusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i)
      (minusWeylGradient g e.base e.frame i) := by
  change regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame.reflect)
    (minusWeyl g e.base e.frame.reflect) (plusWeylGradient g e.base e.frame.reflect i)
    (minusWeylGradient g e.base e.frame.reflect i) = _
  rw [plusWeyl_reflect, minusWeyl_reflect, plusWeylGradient_reflect, minusWeylGradient_reflect]
  simp only [regularizedDeficitDerivative, regularizedRadialDerivative_smul]
  ring

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem deficitEnergy_integrable (o : OppositeWeylData d)
    (L : C(FrameBundle g, ℝ)) (D : Fin 4 → C(FrameBundle g, ℝ)) :
    Integrable (fun e => regularizedDeficit 0 (plusWeyl g e.base e.frame)
      (minusWeyl g e.base e.frame) * L e +
      ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) * D i e) μ := by
  have hδ : Continuous (fun e : FrameBundle g => regularizedDeficit 0
      (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)) := by
    exact (continuous_const.sub ((continuous_regularizedBlockNorm 0).comp d.continuousWeyl)).sub
      ((continuous_regularizedBlockNorm 0).comp o.continuousWeyl)
  apply Integrable.add ((hδ.mul L.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))
  apply integrable_finsetSum
  intro i _
  have hi := integrable_continuous_weight
    ((d.radial_integrable i).neg.sub (r.opposite_radial_integrable i)) (D i)
  apply hi.congr
  filter_upwards [] with e
  change D i e * (-_ - _) = (-_ - _) * D i e
  ring

theorem opposite_deficitEnergyEquation (o : OppositeWeylData d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
        d.oppositeEnergyLaplacianField e +
      ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
        d.oppositeEnergyDerivativeField i e ∂μ) = 0 := by
  let F : FrameBundle g → ℝ := fun e =>
    regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
      d.energyLaplacianField e +
    ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
      d.energyDerivativeField i e
  have hF : (∫ e, F e ∂μ) = 0 := d.deficitEnergyEquation o hpinch
  rw [← r.integral_reflection F] at hF
  refine Eq.trans (b := ∫ e, F (frameReflection e) ∂μ) ?_ hF
  apply integral_congr_ae
  filter_upwards [] with e
  change regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
    d.energyLaplacianField (frameReflection e) +
      (∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
        (orientationSign i * d.energyDerivativeField i (frameReflection e))) =
    regularizedDeficit 0 (plusWeyl g (frameReflection e).base (frameReflection e).frame)
    (minusWeyl g (frameReflection e).base (frameReflection e).frame) *
      d.energyLaplacianField (frameReflection e) +
      (∑ i, regularizedDeficitDerivative 0 (plusWeyl g (frameReflection e).base (frameReflection e).frame)
        (minusWeyl g (frameReflection e).base (frameReflection e).frame)
        (plusWeylGradient g (frameReflection e).base (frameReflection e).frame i)
        (minusWeylGradient g (frameReflection e).base (frameReflection e).frame i) *
        d.energyDerivativeField i (frameReflection e))
  rw [deficit_frameReflection]
  simp_rw [deficitDerivative_frameReflection]
  apply congrArg (fun z : ℝ => regularizedDeficit 0 (plusWeyl g e.base e.frame)
    (minusWeyl g e.base e.frame) * d.energyLaplacianField (frameReflection e) + z)
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem jointDeficitEnergyEquation (o : OppositeWeylData d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
        (d.energyLaplacianField e + d.oppositeEnergyLaplacianField e) +
      ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
        d.totalEnergyDerivativeField i e ∂μ) = 0 := by
  let P : FrameBundle g → ℝ := fun e =>
    regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
      d.energyLaplacianField e +
    ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
      d.energyDerivativeField i e
  let Q : FrameBundle g → ℝ := fun e =>
    regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) *
      d.oppositeEnergyLaplacianField e +
    ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
      d.oppositeEnergyDerivativeField i e
  have hp : (∫ e, P e ∂μ) = 0 := d.deficitEnergyEquation o hpinch
  have hq : (∫ e, Q e ∂μ) = 0 := r.opposite_deficitEnergyEquation o hpinch
  have hsum : (∫ e, P e + Q e ∂μ) = 0 := by
    rw [integral_add (r.deficitEnergy_integrable o _ _) (r.deficitEnergy_integrable o _ _),
      hp, hq, add_zero]
  convert! hsum using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with e
  dsimp only [P, Q, MetricGreenData.totalEnergyDerivativeField, ContinuousMap.add_apply]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact cancellation of the two weak norm equations with the
deficit-weighted energy equation. All fields are the actual Weyl fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

include r

theorem jointScalarNorm_integrable : Integrable d.jointScalarNorm μ :=
  d.scalarNorm_integrable.add r.opposite_scalarNorm_integrable

theorem jointEnergyCancellation_oai (o : OppositeWeylData d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, d.deficitField o e * d.jointEnergyLaplacian e +
      d.totalEnergyField e * d.jointScalarNorm e ∂μ) = 0 := by
  let N : FrameBundle g → ℝ := fun e => d.totalEnergyField e * d.jointScalarNorm e +
    ∑ i, d.totalEnergyDerivativeField i e *
      (regularizedRadialDerivative 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i) +
       regularizedRadialDerivative 0 (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame i))
  let Q : FrameBundle g → ℝ := fun e => d.deficitField o e * d.jointEnergyLaplacian e +
    ∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
      d.totalEnergyDerivativeField i e
  have hn : (∫ e, N e ∂μ) = 0 := r.jointNormEnergyEquation
  have hq : (∫ e, Q e ∂μ) = 0 := r.jointDeficitEnergyEquation o hpinch
  have hni : Integrable N μ :=
    (integrable_continuous_weight r.jointScalarNorm_integrable d.totalEnergyField).add
      (integrable_finsetSum _ (fun i _ => integrable_continuous_weight
        ((d.radial_integrable i).add (r.opposite_radial_integrable i))
          (d.totalEnergyDerivativeField i)))
  have hqi : Integrable Q μ :=
    r.deficitEnergy_integrable o d.jointEnergyLaplacian d.totalEnergyDerivativeField
  have hsum : (∫ e, N e + Q e ∂μ) = 0 := by
    rw [integral_add hni hqi, hn, hq, add_zero]
  convert! hsum using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with e
  dsimp only [N, Q]
  have hc : (∑ i, d.totalEnergyDerivativeField i e *
      (regularizedRadialDerivative 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i) +
       regularizedRadialDerivative 0 (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame i))) +
      (∑ i, regularizedDeficitDerivative 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (minusWeylGradient g e.base e.frame i) *
        d.totalEnergyDerivativeField i e) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    unfold regularizedDeficitDerivative
    ring
  linarith only [hc]

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

theorem solution.{u_1} : type_of% @OAI.PositiveEinsteinFour.Geometry.FrameReflectionData.jointEnergyCancellation_oai.{u_1} := @OAI.PositiveEinsteinFour.Geometry.FrameReflectionData.jointEnergyCancellation_oai.{u_1}
