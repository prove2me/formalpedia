-- Prove2me | solution 1 for OAI.CrouzeixHilbert.Boundary.densityLp_ordered
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:44:49.713898+00:00
-- url     : https://prove2.me/submissions/990eee9c-9c42-4996-bf14-893530882530

import Mathlib
import Definitions.Def_CrouzeixHilbert
import Definitions.Def_OAIQWCH000

section
-- module Solutions.OAIQW_CrouzeixHilbert.Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

open scoped Kronecker

theorem norm_matrixAmplificationCoordinates (n m : ℕ)
    (v : Amplification (EuclideanSpace ℂ (Fin n)) m) :
    ‖matrixAmplificationCoordinates n m v‖ = ‖v‖ := by
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq (matrixAmplificationCoordinates n m).continuous.norm continuous_norm) ?_
  intro a
  simp only [matrixAmplificationCoordinates, ContinuousLinearMap.fromCompletion_apply_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.norm_map,
    UniformSpace.Completion.norm_coe]

theorem matrixAmplificationCoordinates_tensorOperator {n m : ℕ}
    (M : Coeff n) (B : Coeff m) (v : Amplification (EuclideanSpace ℂ (Fin n)) m) :
    matrixAmplificationCoordinates n m (tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) M) B v) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (M ⊗ₖ B) (matrixAmplificationCoordinates n m v) := by
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq ((matrixAmplificationCoordinates n m).continuous.comp
      (tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) M) B).continuous)
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (M ⊗ₖ B)).continuous.comp
        (matrixAmplificationCoordinates n m).continuous)) ?_
  intro a
  induction a using TensorProduct.induction_on with
  | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | simp
  | tmul x y =>
    simp only [tensorOperator, ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]
    apply PiLp.ext
    rintro ⟨i, j⟩
    simp only [matrixAmplificationCoordinates_tmul, Matrix.ofLp_toEuclideanCLM,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker_apply,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  | add a b ha hb => simp only [UniformSpace.Completion.coe_add, map_add, ha, hb]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Forms. -/

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open MeasureTheory

namespace CrouzeixHilbert.Boundary

section FieldAction

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem fieldAction_apply_ae (L : α → E →L[ℝ] E) (hL : AEStronglyMeasurable L μ)
    (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ 1) (u : Lp E 2 μ) :
    fieldAction L hL hLn u =ᵐ[μ] fun t => L t (u t) := by
  unfold fieldAction
  dsimp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.coeFn_toLp _

omit [CompleteSpace E] in
theorem norm_fieldAction_le (L : α → E →L[ℝ] E) (hL : AEStronglyMeasurable L μ)
    (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ 1) : ‖fieldAction L hL hLn‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [fieldAction_apply_ae L hL hLn u, hLn] with t ht hn
  rw [ht]
  exact ThreeWaySplitting.norm_apply_le_of_norm_le_one hn _

theorem adjoint_fieldAction (L M : α → E →L[ℝ] E)
    (hL : AEStronglyMeasurable L μ) (hM : AEStronglyMeasurable M μ)
    (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ 1) (hMn : ∀ᵐ t ∂μ, ‖M t‖ ≤ 1)
    (ha : ∀ᵐ t ∂μ, ContinuousLinearMap.adjoint (L t) = M t) :
    ContinuousLinearMap.adjoint (fieldAction L hL hLn) = fieldAction M hM hMn := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldAction_apply_ae M hM hMn u, fieldAction_apply_ae L hL hLn v, ha]
    with t hu hv ht
  rw [hu, hv, ← ht, ContinuousLinearMap.adjoint_inner_left]

end FieldAction

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Density. -/

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open MeasureTheory

namespace CrouzeixHilbert.Boundary

section Equality

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem eq_of_norm_le_inner (u v : H) (hn : ‖u‖ ≤ ‖v‖)
    (hi : ⟪v, u⟫_ℂ = ⟪v, v⟫_ℂ) : u = v := by
  have he : RCLike.re ⟪u, v⟫_ℂ = ‖v‖ ^ 2 := by
    rw [inner_re_symm, hi, ← norm_sq_eq_re_inner]
  have hd := norm_sub_sq (𝕜 := ℂ) u v
  rw [he] at hd
  have hz : ‖u - v‖ = 0 := by
    nlinarith only [hd, hn, norm_nonneg u, norm_nonneg v, norm_nonneg (u - v), sq_nonneg ‖u - v‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

variable [CompleteSpace E] [CompleteSpace H]

theorem adjoint_eq_of_contraction (M : E →L[ℂ] H) (hM : ‖M‖ ≤ 1)
    (x : E) (y : H) (hxy : M x = y) (hn : ‖x‖ = ‖y‖) :
    ContinuousLinearMap.adjoint M y = x := by
  apply eq_of_norm_le_inner
  · calc
      ‖(ContinuousLinearMap.adjoint M) y‖ ≤ ‖ContinuousLinearMap.adjoint M‖ * ‖y‖ :=
        (ContinuousLinearMap.adjoint M).le_opNorm y
      _ = ‖M‖ * ‖y‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg _)
      _ = ‖x‖ := by rw [one_mul, hn]
  · rw [ContinuousLinearMap.adjoint_inner_right, hxy, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K, hn]

theorem equality_in_compression (V : E →ₗᵢ[ℂ] H) (M : H →L[ℂ] H)
    (hM : ‖M‖ ≤ 1) (x y : E) (hn : ‖x‖ = ‖y‖)
    (hxy : ContinuousLinearMap.adjoint V.toContinuousLinearMap (M (V x)) = y) :
    M (V x) = V y ∧ ContinuousLinearMap.adjoint M (V y) = V x := by
  have hf : M (V x) = V y := by
    apply eq_of_norm_le_inner
    · calc
        ‖M (V x)‖ ≤ ‖M‖ * ‖V x‖ := M.le_opNorm _
        _ ≤ 1 * ‖V x‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg _)
        _ = ‖V y‖ := by simp only [one_mul, V.norm_map, hn]
    · change ⟪V.toContinuousLinearMap y, M (V x)⟫_ℂ = ⟪V y, V y⟫_ℂ
      rw [← V.toContinuousLinearMap.adjoint_inner_right, hxy, V.inner_map_map]
  exact ⟨hf, adjoint_eq_of_contraction M hM (V x) (V y) hf (by
    simpa only [V.norm_map] using hn)⟩

end Equality

section PartialTraces

variable {n m : Type*} [Fintype n]

variable [Fintype m]

theorem crossPartialTrace_ordered (X Y : Matrix n m ℂ) (F : Matrix m m ℂ)
    (hforward : Y = X * Fᵀ) (hadjoint : X = Y * (Fᴴ)ᵀ) :
    crossPartialTrace X X = Fᴴ * crossPartialTrace X Y ∧
    crossPartialTrace X Y = F * crossPartialTrace X X ∧
    crossPartialTrace Y Y = crossPartialTrace X Y * Fᴴ := by
  refine ⟨?_, ?_, ?_⟩
  · change (Xᴴ * X)ᵀ = Fᴴ * (Xᴴ * Y)ᵀ
    nth_rw 2 [hadjoint]
    rw [← Matrix.mul_assoc, Matrix.transpose_mul, Matrix.transpose_transpose]
  · change (Xᴴ * Y)ᵀ = F * (Xᴴ * X)ᵀ
    rw [hforward, ← Matrix.mul_assoc, Matrix.transpose_mul, Matrix.transpose_transpose]
  · change (Yᴴ * Y)ᵀ = (Xᴴ * Y)ᵀ * Fᴴ
    nth_rw 1 [hforward]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.transpose_mul]
    congr 1

omit [Fintype m] in
theorem weightedPartialTrace_factor (L : Matrix n n ℂ) (X Y : Matrix n m ℂ) :
    weightedPartialTrace (Lᴴ * L) X Y = crossPartialTrace (L * X) (L * Y) := by
  simp only [weightedPartialTrace, crossPartialTrace, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end PartialTraces

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Vectorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vectorization. -/

noncomputable section

open scoped TensorProduct Matrix Matrix.Norms.L2Operator Kronecker InnerProductSpace MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Realization

theorem kronecker_toHS {n : ℕ} (A B X : Coeff n) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (A ⊗ₖ B)) (Boundary.toHS X) =
      Boundary.toHS (A * X * Bᵀ) := by
  apply PiLp.ext
  rintro ⟨i,j⟩
  simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kronecker_apply, Boundary.toHS,
    WithLp.ofLp_toLp, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorOperator_vectorization {n : ℕ} (A B X : Coeff n) :
    tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) A) B (vectorization X) =
      vectorization (A * X * Bᵀ) := by
  let e : Amplification (EuclideanSpace ℂ (Fin n)) n →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin n × Fin n) :=
    ⟨(matrixAmplificationCoordinates n n).toLinearMap, norm_matrixAmplificationCoordinates n n⟩
  apply e.injective
  change matrixAmplificationCoordinates n n _ = matrixAmplificationCoordinates n n _
  rw [matrixAmplificationCoordinates_tensorOperator, vectorization_coordinates,
    vectorization_coordinates, kronecker_toHS]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Compression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compression. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace

namespace CrouzeixHilbert.Compression

section Multiplication

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem fieldAction_apply_ae (L : α → E →L[ℂ] E) (hL : AEStronglyMeasurable L μ)
    (C : ℝ) (hC : 0 ≤ C) (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ C) (u : Lp E 2 μ) :
    fieldAction L hL C hC hLn u =ᵐ[μ] fun t => L t (u t) := by
  unfold fieldAction
  dsimp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.coeFn_toLp _

theorem norm_fieldAction_le (L : α → E →L[ℂ] E) (hL : AEStronglyMeasurable L μ)
    (C : ℝ) (hC : 0 ≤ C) (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ C) :
    ‖fieldAction L hL C hC hLn‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [fieldAction_apply_ae L hL C hC hLn u, hLn] with t ht hn
  rw [ht]
  exact ((L t).le_opNorm _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

variable [CompleteSpace E]

theorem adjoint_fieldAction (L M : α → E →L[ℂ] E)
    (hL : AEStronglyMeasurable L μ) (hM : AEStronglyMeasurable M μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ C) (hMn : ∀ᵐ t ∂μ, ‖M t‖ ≤ C)
    (ha : ∀ᵐ t ∂μ, ContinuousLinearMap.adjoint (L t) = M t) :
    ContinuousLinearMap.adjoint (fieldAction L hL C hC hLn) =
      fieldAction M hM C hC hMn := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldAction_apply_ae M hM C hC hMn u,
    fieldAction_apply_ae L hL C hC hLn v, ha] with t hu hv ht
  rw [hu, hv, ← ht, ContinuousLinearMap.adjoint_inner_left]

end Multiplication

section Isometry

variable {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [CompactSpace α] [SecondCountableTopology α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem integral_eq_compression (R L : C(α, E →L[ℂ] E))
    (hmass : ∫ t, star (R t) * R t ∂μ = 1) (C : ℝ) (hC : 0 ≤ C)
    (hLn : ∀ t, ‖L t‖ ≤ C) :
    (∫ t, star (R t) * L t * R t ∂μ) =
      (isometry R hmass).toContinuousLinearMap.adjoint.comp
        ((fieldAction L L.continuous.aestronglyMeasurable C hC
          (Filter.Eventually.of_forall hLn)).comp (isometry R hmass).toContinuousLinearMap) := by
  have hi : Integrable (fun t => star (R t) * L t * R t) μ :=
    ((R.continuous.star.mul L.continuous).mul R.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.integral_apply hi,
    ← integral_inner (𝕜 := ℂ) (f := fun t => (star (R t) * L t * R t) y)
      ((ContinuousLinearMap.apply ℂ E y).integrable_comp hi) x]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap, isometry_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lift_apply_ae R x,
    fieldAction_apply_ae L L.continuous.aestronglyMeasurable C hC
      (Filter.Eventually.of_forall hLn) (lift R y), lift_apply_ae R y] with t hx hL hy
  rw [hx, hL, hy]
  exact ContinuousLinearMap.adjoint_inner_right (R t) x (L t (R t y))

end Isometry

end CrouzeixHilbert.Compression

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.TensorDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor Density. -/

noncomputable section

open MeasureTheory Set Filter

open scoped Topology InnerProductSpace TensorProduct Matrix.Norms.L2Operator

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

attribute [local instance] OAI.CrouzeixHilbert.tensorDensityOperatorRealNormedSpace
attribute [local instance] OAI.CrouzeixHilbert.tensorDensityOperatorCompleteSpace
theorem tensorOperator_mul (A D : Operator H) {m : ℕ} (B C : Coeff m) :
    tensorOperator (A * D) (B * C) = tensorOperator A B * tensorOperator D C := by
  ext x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (tensorOperator (A * D) (B * C)).continuous
      ((tensorOperator A B).continuous.comp (tensorOperator D C).continuous)) ?_
  intro v
  simp only [tensorOperator, map_mul, mul_apply_eq_comp,
    ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_mul]

variable [CompleteSpace H]

theorem tensorOperator_star (A : Operator H) {m : ℕ} (B : Coeff m) :
    tensorOperator (star A) (star B) = star (tensorOperator A B) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq ((tensorOperator (star A) (star B)).continuous.inner continuous_const)
      (continuous_id.inner continuous_const)) ?_
  intro a
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner (tensorOperator A B).continuous)) ?_
  intro b
  simp only [tensorOperator, ContinuousLinearMap.completion_apply_coe,
    UniformSpace.Completion.inner_coe, map_star]
  induction a using TensorProduct.induction_on with
  | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | simp
  | tmul x u =>
    induction b using TensorProduct.induction_on with
    | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | simp
    | tmul y v => simp [ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    | add b c hb hc => simp only [inner_add_right, map_add, hb, hc]
  | add a c ha hc => simp only [inner_add_left, map_add, ha, hc]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.DensityCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Density Compatibility. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

namespace Boundary

theorem densityLp_apply_ae {n : ℕ} (E : C(CircleSpace, Coeff n)) (X Y : Coeff n) :
    densityLp E X Y =ᵐ[circleMeasure] fun t => toHS (weightedPartialTrace (E t) X Y) :=
  ContinuousMap.coeFn_toLp _ _

end Boundary

open Boundary

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Fibers. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Compression

section Fibres

variable {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [CompactSpace α] [SecondCountableTopology α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem fibres_of_integral_interpolation (R M : C(α, E →L[ℂ] E))
    (hmass : ∫ t, star (R t) * R t ∂μ = 1)
    (hM : ∀ t, ‖M t‖ ≤ 1) (x y : E) (hN : ‖x‖ = ‖y‖)
    (hI : (∫ t, star (R t) * M t * R t ∂μ) x = y) :
    ∀ᵐ t ∂μ, M t (R t x) = R t y ∧ (M t).adjoint (R t y) = R t x := by
  let V := isometry R hmass
  let T := fieldAction (μ := μ) M M.continuous.aestronglyMeasurable 1 zero_le_one
    (Filter.Eventually.of_forall hM)
  have hT : ‖T‖ ≤ 1 := norm_fieldAction_le _ _ _ _ _
  have hIV : V.toContinuousLinearMap.adjoint (T (V x)) = y := by
    rw [integral_eq_compression R M hmass 1 zero_le_one hM] at hI
    exact hI
  obtain ⟨hf, ha⟩ := equality_in_compression V T hT x y hN hIV
  let Ms : C(α, E →L[ℂ] E) := ⟨fun t => (M t).adjoint,
    ContinuousLinearMap.adjoint.continuous.comp M.continuous⟩
  have hMsn : ∀ t, ‖Ms t‖ ≤ 1 := fun t => by
    simpa only [Ms, ContinuousMap.coe_mk, ContinuousLinearMap.adjoint.norm_map] using hM t
  have htstar : T.adjoint = fieldAction Ms Ms.continuous.aestronglyMeasurable
      1 zero_le_one (Filter.Eventually.of_forall hMsn) :=
    adjoint_fieldAction M Ms M.continuous.aestronglyMeasurable
      Ms.continuous.aestronglyMeasurable 1 zero_le_one (Filter.Eventually.of_forall hM)
      (Filter.Eventually.of_forall hMsn) (Filter.Eventually.of_forall fun _ => rfl)
  rw [htstar] at ha
  filter_upwards [fieldAction_apply_ae M M.continuous.aestronglyMeasurable
      1 zero_le_one (Filter.Eventually.of_forall hM) (V x),
    fieldAction_apply_ae Ms Ms.continuous.aestronglyMeasurable
      1 zero_le_one (Filter.Eventually.of_forall hMsn) (V y),
    lift_apply_ae R x, lift_apply_ae R y] with t hft hat hxt hyt
  constructor
  · rw [← hxt, ← hyt]
    change M t (V x t) = V y t
    rw [← hft]
    exact congrArg (fun u => u t) hf
  · rw [← hyt, ← hxt]
    change Ms t (V y t) = V x t
    rw [← hat]
    exact congrArg (fun u => u t) ha

end Fibres

end Compression

attribute [local instance] tensorDensityOperatorCompleteSpace

@[simp] theorem matrixBaseField_star_mul {n : ℕ} (L : C(CircleSpace, Coeff n))
    (t : CircleSpace) :
    star (matrixBaseField L t) * matrixBaseField L t =
      tensorOperator (matrixOperatorMap n ((L t)ᴴ * L t)) (1 : Coeff n) := by
  change star (tensorOperator _ _) * tensorOperator _ _ = _
  rw [← tensorOperator_star, ← tensorOperator_mul, star_one, one_mul]
  congr 1
  simp only [matrixOperatorMap_apply, ← Matrix.star_eq_conjTranspose, map_mul, map_star]

theorem matrixBaseField_mass {n : ℕ} (L : C(CircleSpace, Coeff n))
    (hL : ∫ t, (L t)ᴴ * L t ∂circleMeasure = 1) :
    ∫ t, star (matrixBaseField L t) * matrixBaseField L t ∂circleMeasure = 1 := by
  let : ContinuousSMul ℂ (EuclideanSpace ℂ (Fin n)) := IsBoundedSMul.continuousSMul
  let : CompleteSpace (Operator (EuclideanSpace ℂ (Fin n))) :=
    ContinuousLinearMap.instCompleteSpace
  simp only [matrixBaseField_star_mul, ← tensorOperatorCLM_apply]
  rw [(tensorOperatorCLM (H := EuclideanSpace ℂ (Fin n)) (1 : Coeff n)).integral_comp_comm,
    (matrixOperatorMap n).integral_comp_comm, hL]
  · simpa only [matrixOperatorMap_apply, tensorOperatorCLM_apply, map_one] using
      tensorOperator_one (H := EuclideanSpace ℂ (Fin n)) n
  · exact (L.continuous.star.mul L.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (matrixOperatorMap n).integrable_comp
      ((L.continuous.star.mul L.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))

@[simp] theorem matrixBaseField_sandwich {n : ℕ} (L F : C(CircleSpace, Coeff n))
    (t : CircleSpace) :
    star (matrixBaseField L t) * coefficientField (H := EuclideanSpace ℂ (Fin n)) F t *
      matrixBaseField L t = tensorOperator (matrixOperatorMap n ((L t)ᴴ * L t)) (F t) := by
  change star (tensorOperator _ _) * tensorOperator _ _ * tensorOperator _ _ = _
  rw [← tensorOperator_star, ← tensorOperator_mul, ← tensorOperator_mul,
    star_one, one_mul, mul_one, mul_one]
  congr 1
  simp only [matrixOperatorMap_apply, ← Matrix.star_eq_conjTranspose, map_mul, map_star]

theorem norm_coefficientField_le_one {n : ℕ} (F : C(CircleSpace, Coeff n))
    (hF : ∀ t, ‖F t‖ ≤ 1) (t : CircleSpace) :
    ‖coefficientField (H := EuclideanSpace ℂ (Fin n)) F t‖ ≤ 1 := by
  change ‖tensorOperator (1 : Operator (EuclideanSpace ℂ (Fin n))) (F t)‖ ≤ 1
  exact (norm_tensorOperator_le _ _).trans (by
    calc
      ‖(1 : Operator (EuclideanSpace ℂ (Fin n)))‖ * ‖F t‖ ≤ 1 * 1 :=
        mul_le_mul ContinuousLinearMap.norm_id_le (hF t) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _)

theorem matrix_fibres_of_integral_interpolation {n : ℕ}
    (L F : C(CircleSpace, Coeff n))
    (hL : ∫ t, (L t)ᴴ * L t ∂circleMeasure = 1)
    (hF : ∀ t, ‖F t‖ ≤ 1) (X Y : Coeff n)
    (hN : ‖vectorization X‖ = ‖vectorization Y‖)
    (hI : (∫ t, tensorOperator (matrixOperatorMap n ((L t)ᴴ * L t)) (F t)
      ∂circleMeasure) (vectorization X) = vectorization Y) :
    ∀ᵐ t ∂circleMeasure,
      L t * Y = L t * X * (F t)ᵀ ∧ L t * X = L t * Y * (F t)ᴴᵀ := by
  have h := Compression.fibres_of_integral_interpolation
    (matrixBaseField L) (coefficientField (H := EuclideanSpace ℂ (Fin n)) F)
    (matrixBaseField_mass L hL) (norm_coefficientField_le_one F hF)
    (vectorization X) (vectorization Y) hN (by
      simpa only [matrixBaseField_sandwich] using hI)
  filter_upwards [h] with t ht
  obtain ⟨h1, h2⟩ := ht
  have he : (coefficientField (H := EuclideanSpace ℂ (Fin n)) F t).adjoint = coefficientField (H := EuclideanSpace ℂ (Fin n))
      ⟨fun t => (F t)ᴴ, F.continuous.star⟩ t := by
    change star (tensorOperator (1 : Operator (EuclideanSpace ℂ (Fin n))) (F t)) = _
    rw [← tensorOperator_star, star_one]
    rfl
  rw [he] at h2
  change tensorOperator (1 : Operator (EuclideanSpace ℂ (Fin n))) (F t)
      (tensorOperator (matrixOperatorMap n (L t)) (1 : Coeff n) (vectorization X)) =
      tensorOperator (matrixOperatorMap n (L t)) (1 : Coeff n) (vectorization Y) at h1
  change tensorOperator (1 : Operator (EuclideanSpace ℂ (Fin n))) (F t)ᴴ
      (tensorOperator (matrixOperatorMap n (L t)) (1 : Coeff n) (vectorization Y)) =
      tensorOperator (matrixOperatorMap n (L t)) (1 : Coeff n) (vectorization X) at h2
  have hone : (1 : Operator (EuclideanSpace ℂ (Fin n))) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (1 : Coeff n) := (map_one _).symm
  simp only [matrixOperatorMap_apply, hone, tensorOperator_vectorization,
    Matrix.transpose_one, mul_one, one_mul, vectorization_inj] at h1 h2
  exact ⟨h1.symm, h2.symm⟩

end CrouzeixHilbert

namespace CrouzeixHilbert.Boundary

theorem densityLp_ordered_oai {n : ℕ} (E F : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).PosSemidef) (hmass : ∫ t, E t ∂circleMeasure = 1)
    (hF : ∀ t, ‖F t‖ ≤ 1) (X Y : Coeff n)
    (hN : ‖vectorization X‖ = ‖vectorization Y‖)
    (hI : (∫ t, tensorOperator (matrixOperatorMap n (E t)) (F t)
      ∂circleMeasure) (vectorization X) = vectorization Y) :
    ∀ᵐ t ∂circleMeasure,
      ofHS (densityLp E X X t) = (F t)ᴴ * ofHS (densityLp E X Y t) ∧
      ofHS (densityLp E X Y t) = F t * ofHS (densityLp E X X t) ∧
      ofHS (densityLp E Y Y t) = ofHS (densityLp E X Y t) * (F t)ᴴ := by
  let L := matrixDensityRoot E hE
  have hf := matrix_fibres_of_integral_interpolation L F
    (by simpa only [L, matrixDensityRoot_star_mul] using hmass) hF X Y hN
    (by simpa only [L, matrixDensityRoot_star_mul] using hI)
  filter_upwards [hf, densityLp_apply_ae E X X, densityLp_apply_ae E X Y,
    densityLp_apply_ae E Y Y] with t ht hp hr hq
  simp only [hp, hq, hr, ofHS_toHS]
  have hL : (L t)ᴴ * L t = E t := matrixDensityRoot_star_mul E hE t
  rw [← hL, weightedPartialTrace_factor, weightedPartialTrace_factor,
    weightedPartialTrace_factor]
  exact crossPartialTrace_ordered (L t * X) (L t * Y) (F t) ht.1 ht.2

end CrouzeixHilbert.Boundary

end

end OAI
end

theorem solution : type_of% @OAI.CrouzeixHilbert.Boundary.densityLp_ordered_oai := @OAI.CrouzeixHilbert.Boundary.densityLp_ordered_oai
