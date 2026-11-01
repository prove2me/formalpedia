-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Geometry.MetricGreenData.matrixGreen
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:35:28.696287+00:00
-- url     : https://prove2.me/submissions/3e8dde0f-c7f9-4191-bffe-f6c5ec61d08d

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

theorem rawPairing_comm (Z W : RawGradient) : rawPairing Z W = rawPairing W Z := by
  simp only [rawPairing, mul_comm]

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
-- module Solutions.OAIQ091_EF.EinsteinFour_MatrixSlotOperator
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_3 _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The varying matrix-slot curvature coefficient as an actual bounded
operator. The extension to all matrix arrays is self-adjoint; on trace-free
arrays it is the trace-free anticommutator used in the Weyl equation. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Bianchi

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instNormedAddCommGroupMat
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instNormedSpaceRealMat
private theorem matrixEntryKernel_symmetric (A : Mat) (hA : symmetric A)
    (p q : Fin 3 × Fin 3) : matrixEntryKernel A p q = matrixEntryKernel A q p := by
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  unfold matrixEntryKernel
  dsimp only
  rw [hA c a, hA d b, hA d c, hA b a]
  split_ifs <;> simp_all [add_comm]

theorem matrixSlotKernel_symmetric (A : Mat) (hA : symmetric A) (p q : GradientIndex) :
    matrixSlotKernel A p q = matrixSlotKernel A q p := by
  unfold matrixSlotKernel
  by_cases h : p.1 = q.1
  · rw [ite_eq_left h, ite_eq_left h.symm]
    exact matrixEntryKernel_symmetric A hA p.2 q.2
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem matrixSlotOperator_apply (A : Mat) (Z : GradientVector) (p : GradientIndex) :
    matrixSlotOperator A Z p = ∑ q, matrixSlotKernel A p q * Z q := rfl

/-- The full-space extension is self-adjoint for every symmetric coefficient.
Thus operator Green applies to its first derivatives as well. -/
theorem matrixSlotOperator_selfadjoint (A : Mat) (hA : symmetric A)
    (Z W : GradientVector) :
    inner ℝ (matrixSlotOperator A Z) W = inner ℝ Z (matrixSlotOperator A W) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    matrixSlotOperator_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [matrixSlotKernel_symmetric A hA q p]
  ring

/-- Differentiating the varying coefficient commutes with the concrete
matrix-slot construction. -/
theorem hasDerivAt_matrixSlot {T : ℝ → Mat} {dT : Mat} {t : ℝ}
    (hT : HasDerivAt T dT t) :
    HasDerivAt (fun s => matrixSlotOperator (T s)) (matrixSlotOperator dT) t := by
  convert! (matrixSlot.hasFDerivAt.comp_hasDerivAt t hT) using 1
  all_goals try with_reducible_and_instances rfl

private theorem matrixEntryKernel_action (A M : Mat) (hM : traceFree M)
    (a b : Fin 3) :
    (∑ p : Fin 3 × Fin 3, matrixEntryKernel A (a, b) p * M p.1 p.2) =
      matrixSlotAction A M a b := by
  have ht := hM
  simp only [traceFree, Fin.sum_univ_three] at ht
  have h22 : M 2 2 = -M 0 0 - M 1 1 := by linarith
  fin_cases a <;> fin_cases b <;>
    simp [matrixEntryKernel, matrixSlotAction, Fintype.sum_prod_type, Fin.sum_univ_three, h22]
  all_goals ring

/-- On actual trace-free gradient slices, the bounded operator is precisely
`B_F(A)` rather than an independently postulated coefficient. -/
theorem matrixSlotOperator_on_traceFree (A : Mat) (Z : GradientVector)
    (hZ : ∀ i, (∑ a, Z (i, a, a)) = 0) (i : Fin 4) (a b : Fin 3) :
    matrixSlotOperator A Z (i, a, b) =
      matrixSlotAction A (fun c d => Z (i, c, d)) a b := by
  rw [matrixSlotOperator_apply]
  simp only [matrixSlotKernel, Fintype.sum_prod_type, ite_mul, zero_mul]
  have hs : (∑ j : Fin 4, ∑ c : Fin 3, ∑ d : Fin 3,
      if i = j then matrixEntryKernel A (a, b) (c, d) * Z (j, c, d) else 0) =
      ∑ c : Fin 3, ∑ d : Fin 3, matrixEntryKernel A (a, b) (c, d) * Z (i, c, d) := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp
  rw [hs]
  simpa only [Fintype.sum_prod_type] using
    matrixEntryKernel_action A (fun c d => Z (i, c, d)) (hZ i) a b

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
-- module Solutions.OAIQ091_EF.EinsteinFour_MatrixSlotCubic
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The varying matrix-slot correction is the actual cubic trace in the
weighted Hessian identity. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Angular Matrix

noncomputable section

theorem matrixSlotAction_self_pairing (A M : Mat)
    (hs : symmetric M) (ht : traceFree M) :
    matrixPairing (matrixSlotAction A M) M = Matrix.trace (A * (M * M)) := by
  have hm : Mᵀ = M := by ext a b; exact hs b a
  have htr : Matrix.trace M = 0 := ht
  rw [matrixPairing_eq_trace, hm, matrixSlotAction_eq,
    Matrix.sub_mul, Matrix.smul_mul, Matrix.add_mul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_smul, htr, smul_zero, sub_zero,
    Matrix.mul_assoc M A M, Matrix.trace_mul_comm M (A * M), Matrix.mul_assoc]
  simp only [smul_eq_mul]
  ring

/-- Summing over the derivative index gives the cubic trace, with no
diagonalization assumption on the varying coefficient. -/
theorem matrixSlot_cubic_trace (A : Mat) (Z : Gradient)
    (hs : ∀ j, symmetric (Z j)) (ht : ∀ j, traceFree (Z j)) :
    inner ℝ (matrixSlotOperator A (gradientVector Z)) (gradientVector Z) =
      Matrix.trace (A * (∑ j, Z j * Z j)) := by
  have hslot (j : Fin 4) (a b : Fin 3) :
      matrixSlotOperator A (gradientVector Z) (j, a, b) =
        matrixSlotAction A (Z j) a b :=
    matrixSlotOperator_on_traceFree A (gradientVector Z) ht j a b
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fintype.sum_prod_type]
  change (∑ j, ∑ a, ∑ b,
    Z j a b * matrixSlotOperator A (gradientVector Z) (j, a, b)) = _
  calc
    _ = ∑ j, matrixPairing (matrixSlotAction A (Z j)) (Z j) := by
      simp only [matrixPairing, hslot, mul_comm]
    _ = ∑ j, Matrix.trace (A * (Z j * Z j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact matrixSlotAction_self_pairing A (Z j) (hs j) (ht j)
    _ = _ := by rw [Matrix.mul_sum, Matrix.trace_sum]

end
end PositiveEinsteinFour.Geometry

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

/-- The first and second derivatives of the varying coefficient contribute
exactly the one-half correction. No coefficient is assumed parallel. -/
theorem weighted_operator_green
    (φ : ℝ → Ω ≃ᵐ Ω)
    (hφ : Continuous (fun p : ℝ × Ω => φ p.1 p.2))
    (hμ : ∀ t, MeasurePreserving (φ t) μ μ)
    (m dm : C(Ω, ℝ)) (f df ddf : C(Ω, E))
    (A dA ddA : C(Ω, E →L[ℝ] E))
    (hself : ∀ x u v, inner ℝ (dA x u) v = inner ℝ u (dA x v))
    (hm : ∀ t x, HasDerivAt (fun s => m (φ s x)) (dm (φ t x)) t)
    (hf : ∀ t x, HasDerivAt (fun s => f (φ s x)) (df (φ t x)) t)
    (hdf : ∀ t x, HasDerivAt (fun s => df (φ s x)) (ddf (φ t x)) t)
    (hA : ∀ t x, HasDerivAt (fun s => A (φ s x)) (dA (φ t x)) t)
    (hdA : ∀ t x, HasDerivAt (fun s => dA (φ s x)) (ddA (φ t x)) t) :
    (∫ x, m x * inner ℝ (df x) (A x (df x)) +
      dm x * inner ℝ (f x) (A x (df x)) ∂μ) =
      -(∫ x, m x * inner ℝ (f x) (A x (ddf x)) ∂μ) +
        (1 / 2 : ℝ) * (∫ x, m x * inner ℝ (f x) (ddA x (f x)) +
          dm x * inner ℝ (f x) (dA x (f x)) ∂μ) := by
  let V : C(Ω, E) := ⟨fun x => A x (df x), by fun_prop⟩
  let dV : C(Ω, E) := ⟨fun x => dA x (df x) + A x (ddf x), by fun_prop⟩
  let W : C(Ω, E) := ⟨fun x => dA x (f x), by fun_prop⟩
  let dW : C(Ω, E) := ⟨fun x => ddA x (f x) + dA x (df x), by fun_prop⟩
  have hV (t : ℝ) (x : Ω) :
      HasDerivAt (fun s => V (φ s x)) (dV (φ t x)) t :=
    (hA t x).clm_apply (hdf t x)
  have hW (t : ℝ) (x : Ω) :
      HasDerivAt (fun s => W (φ s x)) (dW (φ t x)) t :=
    (hdA t x).clm_apply (hf t x)
  have h1 := weighted_flow_green μ φ hφ hμ m dm f df V dV hm hf hV
  have h2 := weighted_flow_green μ φ hφ hμ m dm f df W dW hm hf hW
  have hK : Integrable (fun x => m x * inner ℝ (f x) (dA x (df x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hJ : Integrable (fun x => m x * inner ℝ (f x) (A x (ddf x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hQ : Integrable (fun x => m x * inner ℝ (f x) (ddA x (f x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (fun x => dm x * inner ℝ (f x) (dA x (f x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs (x : Ω) : inner ℝ (df x) (dA x (f x)) =
      inner ℝ (f x) (dA x (df x)) := by
    rw [real_inner_comm (dA x (f x)) (df x)]
    exact hself x (f x) (df x)
  change (∫ x, m x * inner ℝ (df x) (A x (df x)) +
    dm x * inner ℝ (f x) (A x (df x)) ∂μ) =
      -(∫ x, m x * inner ℝ (f x) (dA x (df x) + A x (ddf x)) ∂μ) at h1
  simp_rw [inner_add_right, mul_add] at h1
  rw [integral_add hK hJ] at h1
  change (∫ x, m x * inner ℝ (df x) (dA x (f x)) +
    dm x * inner ℝ (f x) (dA x (f x)) ∂μ) =
      -(∫ x, m x * inner ℝ (f x) (ddA x (f x) + dA x (df x)) ∂μ) at h2
  simp_rw [hs, inner_add_right, mul_add] at h2
  rw [integral_add hK hR, integral_add hQ hK] at h2
  rw [integral_add hQ hR]
  linarith

/-- The nonparallel coefficient identity summed over the four tangent
directions. The correction retains both its Laplacian and the weight gradient. -/
theorem weighted_four_operator_green
    (φ : Fin 4 → ℝ → Ω ≃ᵐ Ω)
    (hφ : ∀ i, Continuous (fun p : ℝ × Ω => φ i p.1 p.2))
    (hμ : ∀ i t, MeasurePreserving (φ i t) μ μ)
    (m : C(Ω, ℝ)) (dm : Fin 4 → C(Ω, ℝ))
    (f : C(Ω, E)) (df ddf : Fin 4 → C(Ω, E))
    (A : C(Ω, E →L[ℝ] E)) (dA ddA : Fin 4 → C(Ω, E →L[ℝ] E))
    (hself : ∀ i x u v, inner ℝ (dA i x u) v = inner ℝ u (dA i x v))
    (hm : ∀ i t x, HasDerivAt (fun s => m (φ i s x)) (dm i (φ i t x)) t)
    (hf : ∀ i t x, HasDerivAt (fun s => f (φ i s x)) (df i (φ i t x)) t)
    (hdf : ∀ i t x, HasDerivAt (fun s => df i (φ i s x)) (ddf i (φ i t x)) t)
    (hA : ∀ i t x, HasDerivAt (fun s => A (φ i s x)) (dA i (φ i t x)) t)
    (hdA : ∀ i t x, HasDerivAt (fun s => dA i (φ i s x)) (ddA i (φ i t x)) t) :
    (∫ x, m x * (∑ i, inner ℝ (df i x) (A x (df i x))) +
      ∑ i, dm i x * inner ℝ (f x) (A x (df i x)) ∂μ) =
      -(∫ x, m x * inner ℝ (f x) (A x (∑ i, ddf i x)) ∂μ) +
        (1 / 2 : ℝ) * (∫ x, m x * inner ℝ (f x) (∑ i, ddA i x (f x)) +
          ∑ i, dm i x * inner ℝ (f x) (dA i x (f x)) ∂μ) := by
  have hL (i : Fin 4) : Integrable (fun x =>
      m x * inner ℝ (df i x) (A x (df i x)) +
        dm i x * inner ℝ (f x) (A x (df i x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hJ (i : Fin 4) : Integrable
      (fun x => m x * inner ℝ (f x) (A x (ddf i x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hC (i : Fin 4) : Integrable (fun x =>
      m x * inner ℝ (f x) (ddA i x (f x)) +
        dm i x * inner ℝ (f x) (dA i x (f x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum :
      (∫ x, ∑ i, (m x * inner ℝ (df i x) (A x (df i x)) +
        dm i x * inner ℝ (f x) (A x (df i x))) ∂μ) =
      -(∫ x, ∑ i, m x * inner ℝ (f x) (A x (ddf i x)) ∂μ) +
        (1 / 2 : ℝ) * (∫ x, ∑ i, (m x * inner ℝ (f x) (ddA i x (f x)) +
          dm i x * inner ℝ (f x) (dA i x (f x))) ∂μ) := by
    rw [integral_finsetSum _ (fun i _ => hL i),
      integral_finsetSum _ (fun i _ => hJ i),
      integral_finsetSum _ (fun i _ => hC i)]
    simp_rw [weighted_operator_green μ _ (hφ _) (hμ _) m (dm _) f (df _) (ddf _)
      A (dA _) (ddA _) (hself _) (hm _) (hf _) (hdf _) (hA _) (hdA _)]
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  simpa only [Finset.sum_add_distrib, Finset.mul_sum, inner_sum, map_sum] using hsum

end

end PositiveEinsteinFour.Averages

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricMatrixGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The varying-coefficient Green identity for the actual Weyl matrix slot. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory TraceHessian
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local instance instNormedAddCommGroupMat_1_r9673a0_1 : NormedAddCommGroup Mat := Matrix.frobeniusNormedAddCommGroup
local instance instNormedSpaceRealMat_1_r9673a0_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
/-- The first-derivative and Laplacian corrections in the nonparallel
matrix-slot term follow from differentiating the actual Weyl coefficient.
No derivative of a chosen eigenframe occurs. -/
theorem weighted_metric_matrix_slot_green
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (φ : Fin 4 → FrameFlow g μ)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hT : Continuous (frameWeylMatrix g))
    (hDT : ∀ i, Continuous (frameWeylGradientMatrix g i))
    (hDDT : ∀ i, Continuous (frameWeylHessianMatrix g i i))
    (hZ : Continuous (frameGradientVector g))
    (hX : ∀ i, Continuous (frameHessianVector g i))
    (hXX : ∀ i, Continuous (frameThirdVector g i i))
    (hDsym : ∀ i e, symmetric (frameWeylGradientMatrix g i e))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((φ i).map s e))
      (dm i ((φ i).map t e)) t)
    (hTd : ∀ i t e, HasDerivAt (fun s => frameWeylMatrix g ((φ i).map s e))
      (frameWeylGradientMatrix g i ((φ i).map t e)) t)
    (hDTd : ∀ i t e, HasDerivAt (fun s => frameWeylGradientMatrix g i ((φ i).map s e))
      (frameWeylHessianMatrix g i i ((φ i).map t e)) t)
    (hZd : ∀ i t e, HasDerivAt (fun s => frameGradientVector g ((φ i).map s e))
      (frameHessianVector g i ((φ i).map t e)) t)
    (hXd : ∀ i t e, HasDerivAt (fun s => frameHessianVector g i ((φ i).map s e))
      (frameThirdVector g i i ((φ i).map t e)) t) :
    (∫ e, m e * (∑ i, inner ℝ (frameHessianVector g i e)
        (matrixSlotOperator (frameWeylMatrix g e) (frameHessianVector g i e))) +
      ∑ i, dm i e * inner ℝ (frameGradientVector g e)
        (matrixSlotOperator (frameWeylMatrix g e) (frameHessianVector g i e)) ∂μ) =
      -(∫ e, m e * inner ℝ (frameGradientVector g e)
        (matrixSlotOperator (frameWeylMatrix g e) (frameGradientLaplacian g e)) ∂μ) +
      (1 / 2 : ℝ) * (∫ e, m e * inner ℝ (frameGradientVector g e)
        (∑ i, matrixSlotOperator (frameWeylHessianMatrix g i i e) (frameGradientVector g e)) +
        ∑ i, dm i e * inner ℝ (frameGradientVector g e)
          (matrixSlotOperator (frameWeylGradientMatrix g i e) (frameGradientVector g e)) ∂μ) := by
  let A : C(FrameBundle g, GradientVector →L[ℝ] GradientVector) :=
    ⟨fun e => matrixSlot (frameWeylMatrix g e), matrixSlot.continuous.comp hT⟩
  let dA (i : Fin 4) : C(FrameBundle g, GradientVector →L[ℝ] GradientVector) :=
    ⟨fun e => matrixSlot (frameWeylGradientMatrix g i e), matrixSlot.continuous.comp (hDT i)⟩
  let ddA (i : Fin 4) : C(FrameBundle g, GradientVector →L[ℝ] GradientVector) :=
    ⟨fun e => matrixSlot (frameWeylHessianMatrix g i i e), matrixSlot.continuous.comp (hDDT i)⟩
  have h := Averages.weighted_four_operator_green μ
    (fun i => (φ i).map) (fun i => (φ i).continuous) (fun i => (φ i).preserves)
    m dm ⟨frameGradientVector g, hZ⟩
    (fun i => ⟨frameHessianVector g i, hX i⟩)
    (fun i => ⟨frameThirdVector g i i, hXX i⟩) A dA ddA
    (fun i e u v => matrixSlotOperator_selfadjoint _ (hDsym i e) u v)
    hm hZd hXd
    (fun i t e => hasDerivAt_matrixSlot (hTd i t e))
    (fun i t e => hasDerivAt_matrixSlot (hDTd i t e))
  simpa only [A, dA, ddA, ContinuousMap.coe_mk, matrixSlot_apply,
    frameGradientLaplacian] using h

end

end PositiveEinsteinFour.Geometry

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

/-! Evaluate both terms of the varying matrix-slot Green formula. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Bianchi

noncomputable section

theorem matrixSlotAt_weylLaplacian (T : Mat) (Z : GradientVector) :
    matrixSlotOperator (weylLaplacian T) Z =
      (6 : ℝ) • matrixSlotOperator T Z -
        (6 : ℝ) • matrixSlotOperator (traceFreeSquare T) Z := by
  change matrixSlotAt Z ((6 : ℝ) • (T - traceFreeSquare T)) = _
  rw [map_smul, map_sub]
  change (6 : ℝ) • (matrixSlotOperator T Z - matrixSlotOperator (traceFreeSquare T) Z) = _
  module

theorem matrixSlotAt_sum_trace (X : Hessian) (Z : GradientVector) :
    (∑ i, matrixSlotOperator (X i i) Z) = matrixSlotOperator (hessianTrace X) Z := by
  change (∑ i, matrixSlotAt Z (X i i)) = matrixSlotAt Z (∑ i, X i i)
  rw [map_sum]

/-- The Laplacian correction contributes `3B - 3C`; together with the
Ricci term `-13B + 20E` this gives the matrix-slot polynomial. -/
theorem matrix_green_main_terms (T : Mat) (hT : symmetric T)
    (Z L : GradientVector) (E : ℝ)
    (hL : inner ℝ (matrixSlotOperator T Z) L =
      13 * inner ℝ (matrixSlotOperator T Z) Z - 20 * E) :
    -inner ℝ Z (matrixSlotOperator T L) +
        (1 / 2 : ℝ) * inner ℝ Z (matrixSlotOperator (weylLaplacian T) Z) =
      -10 * inner ℝ (matrixSlotOperator T Z) Z -
        3 * inner ℝ (matrixSlotOperator (traceFreeSquare T) Z) Z + 20 * E := by
  rw [← matrixSlotOperator_selfadjoint T hT, hL, matrixSlotAt_weylLaplacian,
    inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_comm Z (matrixSlotOperator T Z),
    real_inner_comm Z (matrixSlotOperator (traceFreeSquare T) Z)]
  ring

/-- The derivative of the matrix coefficient is the actual cubic trace,
with no eigenframe or parallel-coefficient premise. -/
theorem matrixSlot_weight_cubic (a : Fin 4 → ℝ) (Z : Angular.Gradient)
    (hs : ∀ j, symmetric (Z j)) (ht : ∀ j, traceFree (Z j)) :
    (∑ i, a i * inner ℝ (gradientVector Z)
      (matrixSlotOperator (Z i) (gradientVector Z))) =
      ∑ i, a i * Matrix.trace (Z i * (∑ j, Z j * Z j)) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm, matrixSlot_cubic_trace (Z i) Z hs ht]

end
end PositiveEinsteinFour.Geometry
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

local instance metricWeylNormedRing_r9673a0_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricWeylNormedSpace_r9673a0_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricWeylNormedAlgebra_r9673a0_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
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

/-! The matrix-slot Hessian quadratic form is exactly the left side of
the varying-operator Green identity, including the unsymmetrized weight. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem gradientVector_add (Z W : Angular.Gradient) :
    gradientVector (Z + W) = gradientVector Z + gradientVector W := by
  ext p
  rfl

theorem matrixHessianPairing_add_left (A : Mat) (X Y Z : Hessian) :
    matrixHessianPairing A (X + Y) Z =
      matrixHessianPairing A X Z + matrixHessianPairing A Y Z := by
  simp only [matrixHessianPairing, Pi.add_apply, gradientVector_add,
    inner_add_left, Finset.sum_add_distrib]

theorem matrixHessianPairing_add_right (A : Mat) (X Y Z : Hessian) :
    matrixHessianPairing A X (Y + Z) =
      matrixHessianPairing A X Y + matrixHessianPairing A X Z := by
  simp only [matrixHessianPairing, Pi.add_apply, gradientVector_add,
    map_add, inner_add_right, Finset.sum_add_distrib]

theorem matrixHessianPairing_comm (A : Mat) (hA : symmetric A) (X Y : Hessian) :
    matrixHessianPairing A X Y = matrixHessianPairing A Y X := by
  apply Finset.sum_congr rfl
  intro i _
  rw [← matrixSlotOperator_selfadjoint A hA, real_inner_comm]

theorem weightedQuadratic_matrixHessianPairing (A : Mat) (hA : symmetric A)
    (m : ℝ) (X Y : Hessian) :
    weightedQuadratic (fun W => matrixHessianPairing A W W) m X Y =
      (m * matrixHessianPairing A X X + matrixHessianPairing A X Y) / 6 := by
  unfold weightedQuadratic
  dsimp only
  rw [matrixHessianPairing_add_left, matrixHessianPairing_add_right,
    matrixHessianPairing_add_right, matrixHessianPairing_comm A hA Y X]
  ring

theorem gradientVector_weightTensor (a : Vec) (Z : Tensor) (i : Fin 4) :
    gradientVector (weightTensor a Z i) = a i • tensorGradientVector Z := by
  ext p
  rfl

theorem matrixHessianPairing_weightTensor (A : Mat) (hA : symmetric A)
    (X : Hessian) (a : Vec) (Z : Tensor) :
    matrixHessianPairing A X (weightTensor a Z) =
      ∑ i, a i * inner ℝ (tensorGradientVector Z)
        (matrixSlotOperator A (gradientVector (X i))) := by
  simp only [matrixHessianPairing, gradientVector_weightTensor, map_smul,
    real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [← matrixSlotOperator_selfadjoint A hA, real_inner_comm]

/-- Arbitrary-frame matrix form, before pointwise diagonalization. -/
theorem weightedQuadratic_matrix_green (A : Mat) (hA : symmetric A)
    (m : ℝ) (X : Hessian) (a : Vec) (Z : Tensor) :
    weightedQuadratic (fun W => matrixHessianPairing A W W) m X (weightTensor a Z) =
      (m * (∑ i, inner ℝ (gradientVector (X i))
          (matrixSlotOperator A (gradientVector (X i)))) +
        ∑ i, a i * inner ℝ (tensorGradientVector Z)
          (matrixSlotOperator A (gradientVector (X i)))) / 6 := by
  rw [weightedQuadratic_matrixHessianPairing A hA,
    matrixHessianPairing_weightTensor A hA]
  rfl

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

local instance metricRicciNormedRing_r9673a0_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricRicciNormedSpace_r9673a0_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricRicciNormedAlgebra_r9673a0_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
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

/-! Differentiate the actual Hessian constraints to show that its rough
Laplacian remains a symmetric trace-free Bianchi gradient. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem hasDerivAt_gradientDivergence {A : ℝ → Angular.Gradient}
    {Z : Angular.Gradient} {t : ℝ}
    (hA : ∀ j, HasDerivAt (fun r => A r j) (Z j) t) (a : Fin 3) (b : Fin 4) :
    HasDerivAt (fun r => gradientDivergence (A r) a b) (gradientDivergence Z a b) t := by
  exact HasDerivAt.fun_sum (fun s _ => HasDerivAt.fun_sum (fun j _ =>
    (hasDerivAt_matrixEntry (hA j) s a).const_mul (quaternionMatrix s b j)))

theorem gradientDivergence_of_hasDerivAt {A : ℝ → Angular.Gradient}
    {Z : Angular.Gradient} {t : ℝ}
    (hA : ∀ j, HasDerivAt (fun r => A r j) (Z j) t)
    (hb : ∀ r a b, gradientDivergence (A r) a b = 0) :
    ∀ a b, gradientDivergence Z a b = 0 := by
  intro a b
  have h := hasDerivAt_gradientDivergence hA a b
  have heq : (fun r => gradientDivergence (A r) a b) = fun _ => (0 : ℝ) :=
    funext (fun r => hb r a b)
  rw [heq] at h
  exact h.unique (hasDerivAt_const t 0)

theorem hessian_divergence_eq (X : Hessian) (i b : Fin 4) (a : Fin 3) :
    HighestHessian.divergence X i a b = gradientDivergence (X i) a b := by
  simp only [HighestHessian.divergence, WithLp.ofLp_sum, Finset.sum_apply,
    gradientDivergence]
  apply Finset.sum_congr rfl
  intro s _
  exact (quaternionMatrix_apply s (WithLp.toLp 2 (fun j => X i j s a)) b).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- All three constraints follow from differentiating the corresponding
Hessian identities along parallel frame flow; none is an extra Ricci input. -/
theorem frameLaplacianMatrix_constraints
    (g : SmoothMetric M) (h : WeylCovariantIdentities g)
    {μ : Measure (FrameBundle g)} (φ : Fin 4 → FrameFlow g μ)
    (hX : ∀ i j t e, HasDerivAt
      (fun s => plusWeylHessian g ((φ i).map s e).base ((φ i).map s e).frame i j)
      (plusWeylThirdDerivative g ((φ i).map t e).base ((φ i).map t e).frame i i j) t)
    (e : FrameBundle g) :
    (∀ j, symmetric (frameLaplacianMatrix g e j)) ∧
    (∀ j, traceFree (frameLaplacianMatrix g e j)) ∧
    (∀ a b, gradientDivergence (frameLaplacianMatrix g e) a b = 0) := by
  have hD (i : Fin 4) :
      (∀ j, symmetric (plusWeylThirdDerivative g e.base e.frame i i j)) ∧
      (∀ j, traceFree (plusWeylThirdDerivative g e.base e.frame i i j)) ∧
      (∀ a b, gradientDivergence (plusWeylThirdDerivative g e.base e.frame i i) a b = 0) := by
    obtain ⟨e₀, he⟩ := ((φ i).map 0).surjective e
    change (φ i).map 0 e₀ = e at he
    have hs (j : Fin 4) := symmetric_of_hasDerivAt (hX i j 0 e₀)
      (fun t => (h.hessianMatrix ((φ i).map t e₀) i j).1)
    have ht (j : Fin 4) := traceFree_of_hasDerivAt (hX i j 0 e₀)
      (fun t => (h.hessianMatrix ((φ i).map t e₀) i j).2)
    have hb := gradientDivergence_of_hasDerivAt (fun j => hX i j 0 e₀)
      (fun t a b => (hessian_divergence_eq _ i b a).symm.trans
        (congrArg (fun q : Bianchi.Vec => q b) (h.hessianBianchi ((φ i).map t e₀) i a)))
    rw [he] at hs ht hb
    exact ⟨hs, ht, hb⟩
  refine ⟨?_, ?_, ?_⟩
  · intro j a b
    simp only [frameLaplacianMatrix, Matrix.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => (hD i).1 j a b)
  · intro j
    change Matrix.trace (∑ i, plusWeylThirdDerivative g e.base e.frame i i j) = 0
    rw [Matrix.trace_sum]
    exact Finset.sum_eq_zero (fun i _ => (hD i).2.1 j)
  · intro a b
    simp only [gradientDivergence, frameLaplacianMatrix, Matrix.sum_apply, Finset.mul_sum]
    calc
      _ = ∑ s, ∑ i, ∑ j, quaternionMatrix s b j *
          plusWeylThirdDerivative g e.base e.frame i i j s a := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ s, ∑ j, quaternionMatrix s b j *
          plusWeylThirdDerivative g e.base e.frame i i j s a := Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero (fun i _ => (hD i).2.2 a b)

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

private theorem ricciCompressionTensor_matrix (Z L : Tensor) :
    (ricciCompressionTensor Z L).matrix =
      (1 / 20 : ℝ) • ((13 : ℝ) • Z.matrix - L.matrix) := by
  funext a b
  fin_cases a <;> fin_cases b <;> rfl

private theorem ricciCompressionTensor_bianchi (Z L : Tensor)
    (hZ : Z.bianchi) (hL : L.bianchi) : (ricciCompressionTensor Z L).bianchi := by
  intro i
  rw [Tensor.divergence_eq_sum]
  simp only [ricciCompressionTensor_matrix, sub_eq_add_neg,
    Pi.smul_apply, Pi.add_apply, Pi.neg_apply, quaternion_add, quaternion_neg, quaternion_smul,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.smul_sum,
    ← Tensor.divergence_eq_sum, hZ i, hL i, smul_zero, neg_zero, add_zero]

/-- A Bianchi rough Laplacian is enough to identify the compression energy.
No separate assertion that the projector has the desired range is needed. -/
theorem compressed_energy_of_bianchi_ricci (A : Mat) (Z L : Tensor)
    (hZ : Z.bianchi) (hL : L.bianchi)
    (hRicci : L.matrix = (13 : ℝ) • Z.matrix -
      (20 : ℝ) • rawBianchiProjection (generalMatrixAction A Z.matrix)) :
    rawPairing (generalMatrixAction A Z.matrix)
      (rawBianchiProjection (generalMatrixAction A Z.matrix)) =
        rawPairing (rawBianchiProjection (generalMatrixAction A Z.matrix))
          (rawBianchiProjection (generalMatrixAction A Z.matrix)) := by
  have hm : (ricciCompressionTensor Z L).matrix =
      rawBianchiProjection (generalMatrixAction A Z.matrix) := by
    rw [ricciCompressionTensor_matrix, hRicci]
    module
  have hp := rawBianchiProjection_pairing (generalMatrixAction A Z.matrix)
    (ricciCompressionTensor Z L) (ricciCompressionTensor_bianchi Z L hZ hL)
  rw [hm] at hp
  exact hp.symm

/-- The concrete vector-valued matrix action is the bounded matrix-slot
operator used in the metric Green identity. -/
theorem matrixSlotOperator_generalTensor (A : Mat) (Z : Tensor) (hz : Z.traceFree) :
    matrixSlotOperator A (tensorGradientVector Z) =
      rawGradientVector (generalMatrixAction A Z.matrix) := by
  have htrace (i : Fin 4) : (∑ a, tensorGradientVector Z (i, a, a)) = 0 := by
    have h := congrArg (fun v : Vec => v i) hz
    simpa [tensorGradientVector, rawGradientVector, rawCoordinates,
      Tensor.traceFree, Tensor.matrix, Fin.sum_univ_three] using h
  ext p
  rcases p with ⟨i, a, b⟩
  rw [matrixSlotOperator_on_traceFree A _ htrace]
  rfl

theorem matrixSlotOperator_general_pairing (A : Mat) (Z : Tensor) (hz : Z.traceFree) :
    inner ℝ (matrixSlotOperator A (tensorGradientVector Z)) (tensorGradientVector Z) =
      rawPairing (generalMatrixAction A Z.matrix) Z.matrix := by
  rw [matrixSlotOperator_generalTensor A Z hz]
  exact inner_rawGradientVector _ _

/-- The varying-operator Green main term has the coefficient 20 times
the true compression norm, once the actual rough Laplacian is Bianchi. -/
theorem matrixSlot_laplacian_pairing (A : Mat) (Z L : Tensor)
    (hz : Z.traceFree) (hZ : Z.bianchi) (hL : L.bianchi)
    (hRicci : L.matrix = (13 : ℝ) • Z.matrix -
      (20 : ℝ) • rawBianchiProjection (generalMatrixAction A Z.matrix)) :
    inner ℝ (tensorGradientVector L) (matrixSlotOperator A (tensorGradientVector Z)) =
      13 * rawPairing (generalMatrixAction A Z.matrix) Z.matrix -
        20 * rawPairing (rawBianchiProjection (generalMatrixAction A Z.matrix))
          (rawBianchiProjection (generalMatrixAction A Z.matrix)) := by
  rw [matrixSlotOperator_generalTensor A Z hz]
  change inner ℝ (rawGradientVector L.matrix)
    (rawGradientVector (generalMatrixAction A Z.matrix)) = _
  rw [inner_rawGradientVector, hRicci, rawPairing_sub_left,
    rawPairing_smul_left, rawPairing_smul_left,
    rawPairing_comm Z.matrix, rawPairing_comm (rawBianchiProjection _),
    compressed_energy_of_bianchi_ricci A Z L hZ hL hRicci]

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

theorem laplacianConstraints (d : MetricGreenData g μ) (e : FrameBundle g) :
    (∀ j, symmetric (frameLaplacianMatrix g e j)) ∧
    (∀ j, traceFree (frameLaplacianMatrix g e j)) ∧
    (∀ a b, gradientDivergence (frameLaplacianMatrix g e) a b = 0) :=
  frameLaplacianMatrix_constraints g d.weyl d.flow
    (fun i j t e => d.derivativeHessian i i j t e) e

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
local instance greenDataNormedAlgebra_r9673a0_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
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
local instance greenDataNormedAlgebra_r9673a0_2 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
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

local instance metricContractionNormedRing_r9673a0_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricContractionNormedSpace_r9673a0_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricContractionNormedAlgebra_r9673a0_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
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

theorem gradientTensor_ricci_compressed (A : Mat) (hA : symmetric A) (hAt : traceFree A)
    (Z L : Angular.Gradient) (hZ : ∀ i, symmetric (Z i))
    (htZ : ∀ i, traceFree (Z i)) (hbZ : ∀ a b, gradientDivergence Z a b = 0)
    (hL : ∀ i, symmetric (L i)) (hRicci : L = invariantRicciGradient A Z) :
    (gradientTensor L).matrix = (13 : ℝ) • (gradientTensor Z).matrix -
      (20 : ℝ) • rawBianchiProjection (generalMatrixAction A (gradientTensor Z).matrix) := by
  have hc := invariantRicciGradient_compressed A hA hAt (gradientTensor Z)
    (gradientTensor_traceFree Z htZ) (gradientTensor_bianchi Z hZ hbZ)
  have hs : (fun i => rawMatrixSlice (gradientTensor Z).matrix i) = Z :=
    funext (rawMatrixSlice_gradientTensor Z hZ)
  rw [hs] at hc
  have he := hRicci.trans hc
  funext a b
  ext i
  rw [gradientTensor_matrix L hL]
  exact congrArg (fun F : Angular.Gradient => F i a b) he

/-- The normalized varying-matrix main term, with its actual projected
energy and no diagonal-frame or extra compression-energy premise. -/
theorem invariant_ricci_matrix_scalar (A : Mat) (hA : symmetric A) (hAt : traceFree A)
    (Z L : Angular.Gradient) (hZ : ∀ i, symmetric (Z i))
    (htZ : ∀ i, traceFree (Z i)) (hbZ : ∀ a b, gradientDivergence Z a b = 0)
    (hL : ∀ i, symmetric (L i)) (hbL : ∀ a b, gradientDivergence L a b = 0)
    (hRicci : L = invariantRicciGradient A Z) :
    (-inner ℝ (gradientVector Z) (matrixSlotOperator A (gradientVector L)) +
      (1 / 2 : ℝ) * inner ℝ (gradientVector Z)
        (matrixSlotOperator (weylLaplacian A) (gradientVector Z))) / 6 =
      -10 * weylMatrixEnergy A Z - 3 * weylMatrixEnergy (traceFreeSquare A) Z +
        20 * weylCompressionEnergy A Z := by
  have hc := matrixSlot_laplacian_pairing A (gradientTensor Z) (gradientTensor L)
    (gradientTensor_traceFree Z htZ) (gradientTensor_bianchi Z hZ hbZ)
    (gradientTensor_bianchi L hL hbL)
    (gradientTensor_ricci_compressed A hA hAt Z L hZ htZ hbZ hL hRicci)
  rw [tensorGradientVector_gradientTensor L hL, tensorGradientVector_gradientTensor Z hZ,
    generalMatrixAction_gradient_pairing A Z hZ] at hc
  have hslot (B : Mat) :
      inner ℝ (matrixSlotOperator B (gradientVector Z)) (gradientVector Z) =
        6 * weylMatrixEnergy B Z := by
    rw [← tensorGradientVector_gradientTensor Z hZ,
      matrixSlotOperator_general_pairing B _ (gradientTensor_traceFree Z htZ),
      generalMatrixAction_gradient_pairing B Z hZ]
  have hm := matrix_green_main_terms A hA (gradientVector Z) (gradientVector L)
    (rawPairing (rawBianchiProjection (generalMatrixAction A (gradientTensor Z).matrix))
      (rawBianchiProjection (generalMatrixAction A (gradientTensor Z).matrix)))
    (by rw [real_inner_comm, hslot A]; exact hc)
  rw [hm, hslot A, hslot (traceFreeSquare A)]
  unfold weylCompressionEnergy
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

local instance metricContractionNormedRing_r9673a0_2 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricContractionNormedSpace_r9673a0_2 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricContractionNormedAlgebra_r9673a0_2 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem matrixScalar (d : MetricGreenData g μ) (e : FrameBundle g) :
    (-inner ℝ (frameGradientVector g e)
        (matrixSlotOperator (frameWeylMatrix g e) (frameGradientLaplacian g e)) +
      (1 / 2 : ℝ) * inner ℝ (frameGradientVector g e)
        (∑ i, matrixSlotOperator (frameWeylHessianMatrix g i i e)
          (frameGradientVector g e))) / 6 =
      -10 * weylMatrixEnergy (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) -
      3 * weylMatrixEnergy (traceFreeSquare (plusWeyl g e.base e.frame))
        (plusWeylGradient g e.base e.frame) +
      20 * weylCompressionEnergy (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame) := by
  rw [d.laplacianVector e]
  have hx : (∑ i, matrixSlotOperator (frameWeylHessianMatrix g i i e)
      (frameGradientVector g e)) =
      matrixSlotOperator (weylLaplacian (plusWeyl g e.base e.frame))
        (frameGradientVector g e) := by
    change (∑ i, matrixSlotOperator (plusWeylHessian g e.base e.frame i i)
      (frameGradientVector g e)) = _
    rw [matrixSlotAt_sum_trace, metric_weyl_trace g d.weyl e]
  rw [hx]
  exact invariant_ricci_matrix_scalar _ (d.weyl.symmetric e) (d.weyl.traceFree e)
    _ _ (d.gradientConstraints e).1 (d.gradientConstraints e).2
    (d.gradientBianchi e) (d.laplacianConstraints e).1
    (d.laplacianConstraints e).2.2 (d.ricciGradient e)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Assemble the varying matrix-slot Green integral using the actual
metric Ricci equation and the actual derivative of its coefficient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

private theorem integral_matrix_combination
    {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f h k : C(Ω, ℝ)) :
    (1 / 6 : ℝ) * (-(∫ x, f x ∂μ) + (1 / 2 : ℝ) * (∫ x, h x + k x ∂μ)) =
      ∫ x, (-f x + (1 / 2 : ℝ) * h x) / 6 + k x / 12 ∂μ := by
  have hf := f.continuous.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hh := h.continuous.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hk := k.continuous.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  rw [integral_add hh hk]
  calc
    _ = -(1 / 6 : ℝ) * (∫ x, f x ∂μ) +
        (1 / 12 : ℝ) * (∫ x, h x ∂μ) + (1 / 12 : ℝ) * (∫ x, k x ∂μ) := by ring
    _ = ∫ x, -(1 / 6 : ℝ) * f x + (1 / 12 : ℝ) * h x + (1 / 12 : ℝ) * k x ∂μ := by
      have h₁ := integral_add ((hf.const_mul (-(1 / 6 : ℝ))).add
        (hh.const_mul (1 / 12 : ℝ))) (hk.const_mul (1 / 12 : ℝ))
      have h₂ := integral_add (hf.const_mul (-(1 / 6 : ℝ))) (hh.const_mul (1 / 12 : ℝ))
      simp only [Pi.add_apply] at h₁ h₂
      rw [h₁, h₂, integral_const_mul, integral_const_mul, integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

local instance matrixIntegralNormedRing_r9673a0_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance matrixIntegralNormedSpace_r9673a0_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance matrixIntegralNormedAlgebra_r9673a0_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
/-- The varying-matrix term has the scalar coefficients of the Hessian
inequality, including its cubic correction. -/
theorem matrixGreen_oai (d : MetricGreenData g μ)
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((d.flow i).map s e))
      (dm i ((d.flow i).map t e)) t) :
    (∫ e, weightedQuadratic
      (fun X => matrixHessianPairing (plusWeyl g e.base e.frame) X X)
      (m e) (plusWeylHessian g e.base e.frame)
      (weightTensor (WithLp.toLp 2 (fun i => dm i e))
        (plusGradientTensor g e.base e.frame)) ∂μ) =
    ∫ e, m e * (-10 * weylMatrixEnergy (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame) -
        3 * weylMatrixEnergy (traceFreeSquare (plusWeyl g e.base e.frame))
          (plusWeylGradient g e.base e.frame) +
        20 * weylCompressionEnergy (plusWeyl g e.base e.frame)
          (plusWeylGradient g e.base e.frame)) +
      (∑ i, dm i e * Matrix.trace (plusWeylGradient g e.base e.frame i *
        (∑ j, plusWeylGradient g e.base e.frame j * plusWeylGradient g e.base e.frame j))) / 12 ∂μ := by
  have hZ := d.continuousGradientVector
  have hL : Continuous (frameGradientLaplacian g) := by
    unfold frameGradientLaplacian
    exact continuous_finsetSum _ (fun i _ => d.continuousThirdVector i i)
  have hOp : Continuous (fun e => matrixSlotOperator (frameWeylMatrix g e)
      (frameGradientLaplacian g e)) :=
    (matrixSlot.continuous.comp d.continuousWeyl).clm_apply hL
  have hTrace : Continuous (fun e => ∑ i, matrixSlotOperator (frameWeylHessianMatrix g i i e)
      (frameGradientVector g e)) :=
    continuous_finsetSum _ (fun i _ =>
      (matrixSlot.continuous.comp (d.continuousHessian i i)).clm_apply hZ)
  let f : C(FrameBundle g, ℝ) :=
    ⟨fun e => m e * inner ℝ (frameGradientVector g e)
      (matrixSlotOperator (frameWeylMatrix g e) (frameGradientLaplacian g e)),
      m.continuous.mul (hZ.inner hOp)⟩
  let h : C(FrameBundle g, ℝ) :=
    ⟨fun e => m e * inner ℝ (frameGradientVector g e)
      (∑ i, matrixSlotOperator (frameWeylHessianMatrix g i i e) (frameGradientVector g e)),
      m.continuous.mul (hZ.inner hTrace)⟩
  let k : C(FrameBundle g, ℝ) :=
    ⟨fun e => ∑ i, dm i e * inner ℝ (frameGradientVector g e)
      (matrixSlotOperator (frameWeylGradientMatrix g i e) (frameGradientVector g e)),
      continuous_finsetSum _ (fun i _ => (dm i).continuous.mul
        (hZ.inner ((matrixSlot.continuous.comp (d.continuousGradient i)).clm_apply hZ)))⟩
  have hgreen := weighted_metric_matrix_slot_green g d.flow m dm
    d.continuousWeyl d.continuousGradient (fun i => d.continuousHessian i i)
    d.continuousGradientVector d.continuousHessianVector
    (fun i => d.continuousThirdVector i i)
    (fun i e => (d.gradientConstraints e).1 i) hm d.derivativeWeyl
    (fun i t e => d.derivativeGradient i i t e)
    d.derivativeGradientVector d.derivativeHessianVector
  calc
    _ = (1 / 6 : ℝ) * (∫ e, m e * (∑ i,
        inner ℝ (frameHessianVector g i e)
          (matrixSlotOperator (frameWeylMatrix g e) (frameHessianVector g i e))) +
        ∑ i, dm i e * inner ℝ (frameGradientVector g e)
          (matrixSlotOperator (frameWeylMatrix g e) (frameHessianVector g i e)) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with e
      rw [weightedQuadratic_matrix_green _ (d.weyl.symmetric e)]
      simp only [plusGradientTensor, tensorGradientVector_gradientTensor _
        (d.gradientConstraints e).1]
      simp only [frameGradientVector, frameHessianVector, frameWeylMatrix]
      ring
    _ = (1 / 6 : ℝ) * (-(∫ e, f e ∂μ) + (1 / 2 : ℝ) * (∫ e, h e + k e ∂μ)) := by
      rw [hgreen]
      rfl
    _ = ∫ e, (-f e + (1 / 2 : ℝ) * h e) / 6 + k e / 12 ∂μ :=
      integral_matrix_combination μ f h k
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with e
      have hs := d.matrixScalar e
      have hc := matrixSlot_weight_cubic (fun i => dm i e)
        (plusWeylGradient g e.base e.frame)
        (d.gradientConstraints e).1 (d.gradientConstraints e).2
      change (-(m e * _) + (1 / 2 : ℝ) * (m e * _)) / 6 + k e / 12 = _
      have hk : k e = ∑ i, dm i e * Matrix.trace (plusWeylGradient g e.base e.frame i *
          (∑ j, plusWeylGradient g e.base e.frame j * plusWeylGradient g e.base e.frame j)) := hc
      rw [hk]
      linear_combination (m e) * hs

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

theorem solution.{u_1} : type_of% @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.matrixGreen_oai.{u_1} := @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.matrixGreen_oai.{u_1}
