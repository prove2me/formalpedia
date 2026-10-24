-- Prove2me | solution 1 for OAI.SharpLiebThirring.ActionProof.regularized_action_upper_test
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T14:01:09.571803+00:00
-- url     : https://prove2.me/submissions/9018cde9-fa99-4b4e-9cb7-63a836bfe5d8

import Mathlib
import Definitions.Def_OAIQWSLT000
import Theorems.Thm_OAI_SharpLiebThirring_ActionProof_matrix_compact_penalty
import Theorems.Thm_OAI_SharpLiebThirring_MatrixFlow_terminal_matching
import Theorems.Thm_OAI_SharpLiebThirring_MatrixProof_hilbertSchmidt_cfc_sub_le

section
-- module Solutions.OAIQW_LiebThirring.MatrixOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
namespace SharpLiebThirring


/-! ## The matrix field and action -/


open Matrix Unitary
namespace MatrixProof
variable {n : Type u1} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma trace_star_mul_sum (A B : Matrix n n ℂ) :
    (trace (star A * B)).re = ∑ i, ∑ j, (star (A i j) * B i j).re := by
  simp only [trace, diag, mul_apply, star_eq_conjTranspose, conjTranspose_apply,
    Complex.re_sum, Complex.star_def]
  exact Finset.sum_comm

lemma trace_star_mul_change (U V : unitary (Matrix n n ℂ)) (A B : Matrix n n ℂ) :
    trace (star (star (U : Matrix n n ℂ) * A * (V : Matrix n n ℂ)) *
      (star (U : Matrix n n ℂ) * B * (V : Matrix n n ℂ))) = trace (star A * B) := by
  have hu : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 :=
    Unitary.mul_star_self_of_mem U.property
  have hv : (V : Matrix n n ℂ) * star (V : Matrix n n ℂ) = 1 :=
    Unitary.mul_star_self_of_mem V.property
  simp only [star_mul, star_star]
  calc
    _ = trace (star (V : Matrix n n ℂ) * (star A *
          ((U : Matrix n n ℂ) * star (U : Matrix n n ℂ))) * B * (V : Matrix n n ℂ)) := by
      congr 1
      noncomm_ring
    _ = trace (star (V : Matrix n n ℂ) * (star A * B) * (V : Matrix n n ℂ)) := by simp [hu, mul_assoc]
    _ = trace ((V : Matrix n n ℂ) * star (V : Matrix n n ℂ) * (star A * B)) :=
      trace_mul_cycle _ _ _
    _ = trace (star A * B) := by rw [hv, one_mul]

lemma mixed_diagonal_sub (U V : unitary (Matrix n n ℂ)) (a b : n → ℝ) :
    star (U : Matrix n n ℂ) *
      (conjStarAlgAut ℂ (Matrix n n ℂ) U (diagonal (fun i ↦ (a i : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) V (diagonal (fun i ↦ (b i : ℂ)))) * (V : Matrix n n ℂ) =
      diagonal (fun i ↦ (a i : ℂ)) * (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) -
        (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) * diagonal (fun i ↦ (b i : ℂ)) := by
  simp only [conjStarAlgAut_apply]
  calc
    _ = (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) * diagonal (fun i ↦ (a i : ℂ)) *
          (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) -
          (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) * diagonal (fun i ↦ (b i : ℂ)) *
          (star (V : Matrix n n ℂ) * (V : Matrix n n ℂ)) := by noncomm_ring
    _ = _ := by simp only [Unitary.coe_star_mul_self, one_mul, mul_one]

lemma mixed_diagonal_sub_apply (U V : unitary (Matrix n n ℂ)) (a b : n → ℝ)
    (i j : n) :
    (star (U : Matrix n n ℂ) *
      (conjStarAlgAut ℂ (Matrix n n ℂ) U (diagonal (fun i ↦ (a i : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) V (diagonal (fun i ↦ (b i : ℂ)))) * (V : Matrix n n ℂ)) i j =
      ((a i - b j : ℝ) : ℂ) * (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j := by
  rw [mixed_diagonal_sub]
  simp only [Matrix.sub_apply, diagonal_mul, mul_diagonal, Complex.ofReal_sub]
  ring

lemma functional_unitary_conjugate {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (U : unitary (Matrix n n ℂ)) (f : ℝ → ℝ) :
    (hermitian_unitary_conjugate hA U).cfc f = conjStarAlgAut ℂ (Matrix n n ℂ) U (hA.cfc f) := by
  rw [← IsHermitian.cfc_eq, ← hA.cfc_eq]
  symm
  exact StarAlgHomClass.map_cfc (conjStarAlgAut ℂ (Matrix n n ℂ) U) f A
    (A.finite_real_spectrum.continuousOn f) (by
      change Continuous (fun X : Matrix n n ℂ ↦ conjStarAlgAut ℂ (Matrix n n ℂ) U X)
      simp only [conjStarAlgAut_apply]
      fun_prop) hA
    (hermitian_unitary_conjugate hA U)

omit [DecidableEq n] in
lemma hsSquared_eq_trace (A : Matrix n n ℂ) :
    hsSquared A = (trace (star A * A)).re := by
  rw [trace_star_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

lemma hsSquared_change (U V : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    hsSquared (star (U : Matrix n n ℂ) * A * (V : Matrix n n ℂ)) = hsSquared A := by
  rw [hsSquared_eq_trace, trace_star_mul_change, hsSquared_eq_trace]

lemma hsSquared_cfc_sub {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ i j, |f (hA.eigenvalues i) - f (hB.eigenvalues j)| ≤
      L * |hA.eigenvalues i - hB.eigenvalues j|) :
    hsSquared (hA.cfc f - hB.cfc f) ≤ L ^ 2 * hsSquared (A - B) :=
  hilbertSchmidt_cfc_sub_le hA hB f L hL hf

open MeasureTheory
open scoped Matrix.Norms.L2Operator NNReal

end MatrixProof

open MeasureTheory Set Filter
open scoped Topology
namespace ScalarProof

lemma primitive_deriv (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    deriv (regularizedPrimitive σ δ) y = (max y 0 + δ) ^ (σ - 3 / 2) :=
  (primitive_hasDerivAt σ hδ y).deriv

lemma primitive_concave {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) :
    ConcaveOn ℝ univ (regularizedPrimitive σ δ) := by
  apply Antitone.concaveOn_univ_of_deriv (primitive_differentiable σ hδ)
  intro x y hxy
  rw [primitive_deriv σ hδ, primitive_deriv σ hδ]
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (add_le_add (max_le_max hxy le_rfl) le_rfl) (by linarith)

lemma normalization_integral_pos {σ : ℝ} (hσ : σ < 1) :
    0 < ∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2) := by
  apply integral_pos_iff_support_of_nonneg
    (fun s ↦ Real.rpow_nonneg (by positivity) _)
    (normalization_integrable hσ) |>.2
  have hs : Function.support (fun s : ℝ ↦ (1 + s ^ 2) ^ (σ - 3 / 2)) = univ := by
    ext s
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [hs]
  simp

lemma normalization_pos {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) :
    0 < fieldNormalization σ :=
  div_pos hσ₀ (normalization_integral_pos hσ₁)


/-- A global comparison with the Japanese-bracket integrable majorant, including
negative shifts. It supplies all scalar dominated-convergence bounds. -/
lemma shifted_base_lower {δ : ℝ} (hδ : 0 < δ) (z s : ℝ) :
    (δ / (δ + |z| + 1)) * (1 + s ^ 2) ≤ max (s ^ 2 + z) 0 + δ := by
  have hd : 0 < δ + |z| + 1 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  have hm : 0 ≤ max (s ^ 2 + z) 0 := le_max_right _ _
  have hh : s ^ 2 ≤ max (s ^ 2 + z) 0 + |z| := by
    have := le_max_left (s ^ 2 + z) 0
    have := neg_le_abs z
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hh hδ.le,
    mul_nonneg (abs_nonneg z) hm, mul_nonneg (abs_nonneg z) hδ.le]

lemma shifted_derivative_integrable {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    Integrable (fun s : ℝ ↦ (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) := by
  have ha : 0 < δ / (δ + |z| + 1) := by positivity
  refine ((normalization_integrable hσ).const_mul
    ((δ / (δ + |z| + 1)) ^ (σ - 3 / 2))).mono' ?_ ?_
  · exact ((derivative_continuous σ hδ).comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    rw [← Real.mul_rpow ha.le (by positivity : 0 ≤ 1 + s ^ 2)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (shifted_base_lower hδ z s) (by linarith)

lemma primitive_difference_bound {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z s : ℝ) :
    ‖regularizedPrimitive σ δ (s ^ 2 + z) - regularizedPrimitive σ δ (s ^ 2)‖ ≤
      (max (s ^ 2 - |z|) 0 + δ) ^ (σ - 3 / 2) * |z| := by
  have hd : ∀ y ∈ Ici (s ^ 2 - |z|),
      ‖(max y 0 + δ) ^ (σ - 3 / 2)‖ ≤
        (max (s ^ 2 - |z|) 0 + δ) ^ (σ - 3 / 2) := by
    intro y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (add_le_add (max_le_max hy le_rfl) le_rfl) (by linarith)
  have hs : s ^ 2 ∈ Ici (s ^ 2 - |z|) := by
    simp only [mem_Ici]
    have := abs_nonneg z
    linarith
  have hsz : s ^ 2 + z ∈ Ici (s ^ 2 - |z|) := by
    simp only [mem_Ici]
    have := neg_le_abs z
    linarith
  simpa only [add_sub_cancel_left, Real.norm_eq_abs] using
    (convex_Ici (s ^ 2 - |z|)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y _ ↦ (primitive_hasDerivAt σ hδ y).hasDerivWithinAt) hd hs hsz

lemma mu_integrand_integrable {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    Integrable (fun s : ℝ ↦ regularizedPrimitive σ δ (s ^ 2 + z) -
      regularizedPrimitive σ δ (s ^ 2)) := by
  have hi := (shifted_derivative_integrable hσ hδ (-|z|)).mul_const |z|
  refine hi.mono' ?_ (Filter.Eventually.of_forall ?_)
  · exact (((primitive_differentiable σ hδ).continuous.comp (by fun_prop)).sub
      ((primitive_differentiable σ hδ).continuous.comp (by fun_prop))).aestronglyMeasurable
  · intro s
    simpa only [sub_eq_add_neg] using primitive_difference_bound hσ hδ z s

lemma mu_hasDerivAt_integral {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    HasDerivAt (scalarMu σ δ)
      (fieldNormalization σ * ∫ s : ℝ, (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) z := by
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Ioi (z - 1)) (x₀ := z)
    (F := fun y s : ℝ ↦ regularizedPrimitive σ δ (s ^ 2 + y) -
      regularizedPrimitive σ δ (s ^ 2))
    (F' := fun y s : ℝ ↦ (max (s ^ 2 + y) 0 + δ) ^ (σ - 3 / 2))
    (bound := fun s : ℝ ↦ (max (s ^ 2 + (z - 1)) 0 + δ) ^ (σ - 3 / 2))
    (Ioi_mem_nhds (by linarith))
    (Filter.Eventually.of_forall (fun y ↦ (mu_integrand_integrable hσ hδ y).aestronglyMeasurable))
    (mu_integrand_integrable hσ hδ z)
    (shifted_derivative_integrable hσ hδ z).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s y hy ↦ ?_))
    (shifted_derivative_integrable hσ hδ (z - 1))
    (Filter.Eventually.of_forall (fun s y _ ↦ ?_))
  · exact hh.2.const_mul (fieldNormalization σ)
  · change z - 1 < y at hy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (add_le_add (max_le_max (by linarith) le_rfl) le_rfl) (by linarith)
  · simpa using ((primitive_hasDerivAt σ hδ (s ^ 2 + y)).comp y
      ((hasDerivAt_id y).const_add (s ^ 2))).sub_const (regularizedPrimitive σ δ (s ^ 2))

lemma mu_strictMono {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ) :
    StrictMono (scalarMu σ δ) := by
  apply strictMono_of_deriv_pos
  intro z
  rw [(mu_hasDerivAt_integral hσ₁ hδ z).deriv]
  apply mul_pos (normalization_pos hσ₀ hσ₁)
  apply (integral_pos_iff_support_of_nonneg
    (fun s ↦ Real.rpow_nonneg (by positivity) _)
    (shifted_derivative_integrable hσ₁ hδ z)).2
  have hs : Function.support (fun s : ℝ ↦ (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) = univ := by
    ext s
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [hs]
  simp

end ScalarProof

open scoped MatrixOrder ComplexOrder


end SharpLiebThirring

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.ResolventCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u6 u7 u8 u9 u10 u11

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix


open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
namespace SharpLiebThirring.MatrixProof
variable {n : Type u10} [Fintype n] [DecidableEq n]

lemma cfc_diagonal_real (f : ℝ → ℝ) (x : n → ℝ) (hf : Continuous f) :
    cfc f (diagonal (fun i ↦ (x i : ℂ))) = diagonal (fun i ↦ (f (x i) : ℂ)) := by
  have : ContinuousFunctionalCalculus ℝ (n → ℂ) IsSelfAdjoint :=
    (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := n → ℂ)).toContinuousFunctionalCalculus
  have hself : IsSelfAdjoint (fun i ↦ (x i : ℂ)) := by ext i; simp
  change cfc f (diagonalStarAlgHom (fun i ↦ (x i : ℂ))) = _
  erw [← (diagonalStarAlgHom (n := n)).map_cfc f (fun i ↦ (x i : ℂ)) hf.continuousOn
    (by change Continuous (diagonal : (n → ℂ) → Matrix n n ℂ); fun_prop) hself
    (isHermitian_diagonal_iff.2 fun i ↦ by simp [IsSelfAdjoint])]
  rw [cfc_map_pi (S := ℝ) f _ hf.continuousOn hself (fun i ↦ by simp [IsSelfAdjoint])]
  change diagonal (fun i ↦ cfc f (x i : ℂ)) = diagonal (fun i ↦ (f (x i) : ℂ))
  apply congrArg diagonal
  funext i
  exact cfc_algebraMap (R := ℝ) (A := ℂ) (x i) f

end SharpLiebThirring.MatrixProof


namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u11} [Fintype n] [DecidableEq n]

omit [Fintype n] in
lemma diagonal_real_posSemidef (x : n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (diagonal (fun i ↦ (x i : ℂ))).PosSemidef :=
  posSemidef_diagonal_iff.2 (fun i ↦ by exact_mod_cast hx i)

end SharpLiebThirring.MatrixProof


end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.MatrixTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u12 u13 u14 u15

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra


namespace SharpLiebThirring.ScalarProof

lemma primitive_le_tangent {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (x y : ℝ) :
    regularizedPrimitive σ δ y ≤ regularizedPrimitive σ δ x +
      (max x 0 + δ) ^ (σ - 3 / 2) * (y - x) := by
  have hc := (primitive_concave hσ hδ).neg
  have hd := (primitive_hasDerivAt σ hδ x).neg
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hs := hc.le_slope_of_hasDerivAt (mem_univ x) (mem_univ y) hxy hd
    rw [slope_def_field] at hs
    have := (le_div_iff₀ (sub_pos.2 hxy)).1 hs
    dsimp at this
    nlinarith
  · simp
  · have hs := hc.slope_le_of_hasDerivAt (mem_univ y) (mem_univ x) hyx hd
    rw [slope_def_field] at hs
    have := (div_le_iff₀ (sub_pos.2 hyx)).1 hs
    dsimp at this
    nlinarith

end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u15} [Fintype n] [DecidableEq n]

/-- Scalar Jensen inequality for every positive unital real-linear matrix state.
No assertion of operator concavity on the whole line is used. -/
lemma primitive_state_jensen {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (φ : Matrix n n ℂ →ₗ[ℝ] ℝ) (hφ : ∀ A, A.PosSemidef → 0 ≤ φ A)
    (hφ₁ : φ 1 = 1) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    φ (cfc (regularizedPrimitive σ δ) A) ≤ regularizedPrimitive σ δ (φ A) := by
  let f := regularizedPrimitive σ δ
  let x := φ A
  let d := (max x 0 + δ) ^ (σ - 3 / 2)
  have ht : cfc f A ≤ cfc (fun y : ℝ ↦ f x + d * (y - x)) A :=
    cfc_mono (fun y _ ↦ primitive_le_tangent hσ hδ x y)
      (primitive_differentiable σ hδ).continuous.continuousOn (by fun_prop)
  have he : cfc (fun y : ℝ ↦ f x + d * (y - x)) A =
      f x • 1 + d • (A - x • 1) := by
    erw [cfc_const_add (f x) (fun y : ℝ ↦ d * (y - x)) A (by fun_prop) hA,
      cfc_const_mul d (fun y : ℝ ↦ y - x) A (by fun_prop),
      cfc_sub id (fun _ : ℝ ↦ x) A (by fun_prop) (by fun_prop),
      cfc_id ℝ A hA, cfc_const x A hA,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  rw [he] at ht
  have hp := hφ _ (Matrix.nonneg_iff_posSemidef.1 (sub_nonneg.2 ht))
  simp only [map_sub, map_add, map_smul, hφ₁, smul_eq_mul, mul_one] at hp
  dsimp [x] at hp
  linarith

end SharpLiebThirring.MatrixProof

end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FieldLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u16 u17 u18

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra


noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SharpLiebThirring.ScalarProof

lemma symmetric_shift_boundary {g : ℝ → ℝ} (hg : Continuous g) (he : Function.Even g)
    (R b : ℝ) :
    (∫ s in -R..R, g (s - b) - g s) =
      ∫ t in 0..b, g (R + t) - g (R - b + t) := by
  have hc1 : Continuous (fun s : ℝ ↦ g (s - b)) := by fun_prop
  have hc2 : Continuous (fun t : ℝ ↦ g (R + t)) := by fun_prop
  have hc3 : Continuous (fun t : ℝ ↦ g (R - b + t)) := by fun_prop
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), intervalIntegral.integral_comp_sub_right]
  rw [intervalIntegral.integral_interval_sub_interval_comm
    (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  have hn : (∫ s in -R - b..-R, g s) = ∫ t in R..R + b, g t := by
    have h := intervalIntegral.integral_comp_neg (f := g) (a := R) (b := R + b)
    calc
      _ = ∫ x in R..R + b, g (-x) := by
        simpa only [show -(R + b) = -R - b by ring] using h.symm
      _ = _ := intervalIntegral.integral_congr (fun x _ ↦ he x)
  rw [hn, intervalIntegral.integral_sub (hc2.intervalIntegrable _ _)
    (hc3.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_comp_add_left, add_zero, sub_add_cancel]

lemma symmetric_shift_norm_le {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : Function.Even g) (R b C T : ℝ) (hR : T + 2 * |b| ≤ R)
    (hbound : ∀ x, T ≤ x → ‖g' x‖ ≤ C) :
    ‖∫ s in -R..R, g (s - b) - g s‖ ≤ C * |b| ^ 2 := by
  rw [symmetric_shift_boundary (continuous_iff_continuousAt.2 (fun x ↦ (hg x).continuousAt)) he]
  apply le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := C * |b|) (fun t ht ↦ ?_)) (by simp [pow_two, mul_assoc])
  have ht' : -|b| ≤ t := by
    have := ht.1
    have hmin : -|b| ≤ min 0 b := le_min (by linarith [abs_nonneg b]) (neg_abs_le b)
    linarith
  have hx : R - b + t ∈ Ici T := by
    have := le_abs_self b
    change T ≤ _
    linarith
  have hy : R + t ∈ Ici T := by change T ≤ _; linarith [abs_nonneg b]
  have hm := (convex_Ici T).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ ↦ (hg x).hasDerivWithinAt) (fun x hx ↦ hbound x hx) hx hy
  simpa only [show R + t - (R - b + t) = b by ring, Real.norm_eq_abs] using hm

lemma symmetric_shift_tendsto_zero {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : Function.Even g) (hlim : Tendsto g' atTop (𝓝 0)) (b : ℝ) :
    Tendsto (fun R : ℝ ↦ ∫ s in -R..R, g (s - b) - g s) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hc : 0 < ε / (|b| ^ 2 + 1) := div_pos hε (by positivity)
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hlim) _ hc
  refine ⟨T + 2 * |b|, fun R hR ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  refine lt_of_le_of_lt (symmetric_shift_norm_le hg he R b (ε / (|b| ^ 2 + 1)) T hR (fun x hx ↦ ?_)) ?_
  · simpa only [dist_zero_right] using (hT x hx).le
  · have hden : 0 < |b| ^ 2 + 1 := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith

end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.ScalarProof

lemma primitive_quadratic_hasDerivAt (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (z s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ regularizedPrimitive σ δ (t ^ 2 + z))
      (2 * s * (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) s := by
  convert! (primitive_hasDerivAt σ hδ (s ^ 2 + z)).comp s
    (((hasDerivAt_id s).pow 2).add_const z) using 1
  simp only [id_eq, Nat.cast_ofNat, mul_one]
  ring

lemma primitive_quadratic_deriv_tendsto {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    Tendsto (fun s : ℝ ↦ 2 * s * (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) atTop (𝓝 0) := by
  let a := δ / (δ + |z| + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have ht : Tendsto (fun s : ℝ ↦ (2 * a ^ (σ - 3 / 2)) * s ^ (2 * σ - 2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 2 - 2 * σ by linarith)).const_mul
      (2 * a ^ (σ - 3 / 2))
    simpa only [show -(2 - 2 * σ) = 2 * σ - 2 by ring, mul_zero] using h
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs₀ : 0 < s := by linarith
    have hb := Real.rpow_le_rpow_of_nonpos (show 0 < a * (1 + s ^ 2) by positivity)
      (shifted_base_lower hδ z s) (show σ - 3 / 2 ≤ 0 by linarith)
    have hsq := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hs₀)
      (show s ^ 2 ≤ 1 + s ^ 2 by linarith) (show σ - 3 / 2 ≤ 0 by linarith)
    rw [Real.mul_rpow ha.le (by positivity)] at hb
    calc
      _ ≤ 2 * s * (a ^ (σ - 3 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ 2 * s * (a ^ (σ - 3 / 2) * (s ^ 2) ^ (σ - 3 / 2)) := by
        gcongr
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs₀.le]
        norm_num only [Nat.cast_ofNat]
        conv_lhs => arg 1; arg 2; rw [← Real.rpow_one s]
        rw [show 2 * s ^ (1 : ℝ) * (a ^ (σ - 3 / 2) * s ^ ((2 : ℝ) * (σ - 3 / 2))) =
          (2 * a ^ (σ - 3 / 2)) * (s ^ (1 : ℝ) * s ^ (2 * (σ - 3 / 2))) by ring,
          ← Real.rpow_add hs₀]
        congr 2
        ring

lemma primitive_symmetric_shift_zero {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z b : ℝ) :
    Tendsto (fun R : ℝ ↦ ∫ s in -R..R,
      regularizedPrimitive σ δ ((s - b) ^ 2 + z) - regularizedPrimitive σ δ (s ^ 2 + z))
      atTop (𝓝 0) :=
  symmetric_shift_tendsto_zero (primitive_quadratic_hasDerivAt σ hδ z)
    (fun s ↦ by simp) (primitive_quadratic_deriv_tendsto hσ hδ z) b

/-- The symmetric shift identity, with exactly the cutoff used in the field. -/
lemma primitive_shift_limit {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z b : ℝ) :
    Tendsto (fun R : ℝ ↦ fieldNormalization σ * ∫ s in -R..R,
      regularizedPrimitive σ δ ((s - b) ^ 2 + z) - regularizedPrimitive σ δ (s ^ 2))
      atTop (𝓝 (scalarMu σ δ z)) := by
  have hc := (primitive_differentiable σ hδ).continuous
  have h₁ := primitive_symmetric_shift_zero hσ hδ z b
  have h₂ := intervalIntegral_tendsto_integral (mu_integrand_integrable hσ hδ z)
    tendsto_neg_atTop_atBot tendsto_id
  have hh := (h₁.add h₂).const_mul (fieldNormalization σ)
  simp only [zero_add] at hh
  apply hh.congr
  intro R
  congr 1
  simp only [id_eq]
  rw [← intervalIntegral.integral_add
    (show IntervalIntegrable (fun s : ℝ ↦ regularizedPrimitive σ δ ((s - b) ^ 2 + z) -
      regularizedPrimitive σ δ (s ^ 2 + z)) volume (-R) R from
      (by fun_prop : Continuous _).intervalIntegrable _ _)
    (show IntervalIntegrable (fun s : ℝ ↦ regularizedPrimitive σ δ (s ^ 2 + z) -
      regularizedPrimitive σ δ (s ^ 2)) volume (-R) R from
      (by fun_prop : Continuous _).intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro s hs
  ring

end SharpLiebThirring.ScalarProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.RankOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u19 u20 u21 u22 u23 u24

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology


namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u19} [Fintype n] [DecidableEq n]

lemma hermitianField_state_jensen {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (φ : Matrix n n ℂ →L[ℝ] ℝ) (hφ : ∀ A, A.PosSemidef → 0 ≤ φ A) (hφ₁ : φ 1 = 1)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) :
    φ (hermitianField σ δ C B) ≤ scalarMu σ δ (φ C - (φ B) ^ 2) := by
  have hlim := φ.continuous.continuousAt.tendsto.comp (hermitianField_cutoff_limit hσ₁ hδ hC hB)
  have hs := primitive_shift_limit hσ₁ hδ (φ C - (φ B) ^ 2) (φ B)
  apply le_of_tendsto_of_tendsto hlim hs
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  have hc := continuous_fieldIntegrand hδ σ hC hB
  dsimp only [Function.comp_apply]
  rw [map_smul, ← φ.intervalIntegral_comp_comm (hc.intervalIntegrable _ _), smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (normalization_pos hσ₀ hσ₁).le
  apply intervalIntegral.integral_mono (by linarith : -R ≤ R)
    ((φ.continuous.comp hc).intervalIntegrable _ _)
    ((by have hf := (primitive_differentiable σ hδ).continuous; fun_prop : Continuous
      (fun s : ℝ ↦ regularizedPrimitive σ δ ((s - φ B) ^ 2 + (φ C - (φ B) ^ 2)) -
        regularizedPrimitive σ δ (s ^ 2))).intervalIntegrable _ _)
  intro s
  have hp := primitive_state_jensen hσ₁ hδ φ.toLinearMap hφ hφ₁ (quadraticMatrix_hermitian hC hB s)
  have he : φ (quadraticMatrix C B s) = (s - φ B) ^ 2 + (φ C - (φ B) ^ 2) := by
    simp only [quadraticMatrix, map_add, map_sub, map_smul, hφ₁, smul_eq_mul, mul_one]
    ring
  change φ (cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s)) ≤
    regularizedPrimitive σ δ (φ (quadraticMatrix C B s)) at hp
  rw [he] at hp
  simpa only [Function.comp_apply, fieldIntegrand, map_sub, map_smul, hφ₁, smul_eq_mul, mul_one] using
    sub_le_sub_right hp (regularizedPrimitive σ δ (s ^ 2))

lemma unitaryState_positive (U : unitary (Matrix n n ℂ)) (i : n)
    {A : Matrix n n ℂ} (hA : A.PosSemidef) : 0 ≤ unitaryState U i A := by
  have hp := hA.mul_mul_conjTranspose_same (U : Matrix n n ℂ)
  have hd := hp.diag_nonneg (i := i)
  exact (Complex.nonneg_iff.1 hd).1

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u23} [Fintype n] [DecidableEq n]

lemma quadraticMatrix_conj (U : unitary (Matrix n n ℂ)) (C B : Matrix n n ℂ) (s : ℝ) :
    quadraticMatrix (conjStarAlgAut ℂ (Matrix n n ℂ) U C)
      (conjStarAlgAut ℂ (Matrix n n ℂ) U B) s =
        conjStarAlgAut ℂ (Matrix n n ℂ) U (quadraticMatrix C B s) := by
  have hs (r : ℝ) (A : Matrix n n ℂ) :
      conjStarAlgAut ℂ (Matrix n n ℂ) U (r • A) =
        r • conjStarAlgAut ℂ (Matrix n n ℂ) U A := (unitaryConjCLM U).map_smul r A
  simp only [quadraticMatrix, map_add, map_sub, hs, map_one]

lemma cfc_unitary_conj {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (U : unitary (Matrix n n ℂ)) (f : ℝ → ℝ) :
    cfc f (conjStarAlgAut ℂ (Matrix n n ℂ) U A) = conjStarAlgAut ℂ (Matrix n n ℂ) U (cfc f A) := by
  have h := functional_unitary_conjugate hA U f
  rwa [← IsHermitian.cfc_eq, ← hA.cfc_eq] at h

lemma pairedFieldIntegrand_conj (σ δ : ℝ) {C B : Matrix n n ℂ}
    (hC : C.IsHermitian) (hB : B.IsHermitian) (U : unitary (Matrix n n ℂ)) (s : ℝ) :
    pairedFieldIntegrand σ δ (conjStarAlgAut ℂ (Matrix n n ℂ) U C)
      (conjStarAlgAut ℂ (Matrix n n ℂ) U B) s =
        unitaryConjCLM U (pairedFieldIntegrand σ δ C B s) := by
  simp only [pairedFieldIntegrand, quadraticMatrix_conj, unitaryConjCLM_apply,
    cfc_unitary_conj (quadraticMatrix_hermitian hC hB _), map_sub, map_add, map_smul, map_one]

lemma hermitianField_conj {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (U : unitary (Matrix n n ℂ)) :
    hermitianField σ δ (conjStarAlgAut ℂ (Matrix n n ℂ) U C)
      (conjStarAlgAut ℂ (Matrix n n ℂ) U B) =
        conjStarAlgAut ℂ (Matrix n n ℂ) U (hermitianField σ δ C B) := by
  change _ = unitaryConjCLM U (hermitianField σ δ C B)
  simp only [hermitianField, pairedFieldIntegrand_conj σ δ hC hB, map_smul]
  rw [(unitaryConjCLM U).integral_comp_comm (integrable_pairedFieldIntegrand hσ hδ hC hB)]

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u24} [Fintype n] [DecidableEq n]

lemma complexify_diagonal (x : n → ℝ) :
    complexify (diagonal x) = diagonal (fun i ↦ (x i : ℂ)) := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

lemma complexify_vecMulVec (a : n → ℝ) :
    complexify (vecMulVec a a) = vecMulVec (fun i ↦ (a i : ℂ)) (star (fun i ↦ (a i : ℂ))) := by
  ext i j
  simp [vecMulVec]

lemma complexify_trace_real (A : Matrix n n ℝ) : (trace (complexify A)).re = trace A := by
  simp only [trace, diag, complexify_apply, Complex.re_sum, Complex.ofReal_re]

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FieldRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u25 u26 u27 u28 u29 u30 u31

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace SharpLiebThirring.MatrixProof
open Matrix
open scoped Matrix.Norms.L2Operator
variable {n : Type u25} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma flatten_norm_sq (A : Matrix n n ℂ) : ‖flattenCLM A‖ ^ 2 = hsSquared A := by
  rw [EuclideanSpace.norm_sq_eq, hsSquared, Fintype.sum_prod_type]
  change (∑ i, ∑ j, ‖A i j‖ ^ 2) = _
  simp only [Complex.sq_norm]


lemma cfc_lipschitz_norm {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ B, |f x - f y| ≤ L * |x - y|) :
    ‖cfc f A - cfc f B‖ ≤
      (‖(unflattenCLM : EuclideanSpace ℂ (n × n) →L[ℝ] Matrix n n ℂ)‖ *
        ‖(flattenCLM : Matrix n n ℂ →L[ℝ] EuclideanSpace ℂ (n × n))‖) * L * ‖A - B‖ := by
  have hs := hsSquared_cfc_sub hA hB f L hL
    (fun i j ↦ hf _ (hA.eigenvalues_mem_spectrum_real i) _ (hB.eigenvalues_mem_spectrum_real j))
  rw [← hA.cfc_eq, ← hB.cfc_eq, ← flatten_norm_sq, ← flatten_norm_sq] at hs
  have h1 : ‖flattenCLM (cfc f A - cfc f B)‖ ≤ L * ‖flattenCLM (A - B)‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).1
    simpa only [mul_pow] using hs
  calc
    _ = ‖unflattenCLM (flattenCLM (cfc f A - cfc f B))‖ := rfl
    _ ≤ ‖unflattenCLM (n := n)‖ * ‖flattenCLM (cfc f A - cfc f B)‖ := (unflattenCLM (n := n)).le_opNorm _
    _ ≤ ‖unflattenCLM (n := n)‖ * (L * (‖flattenCLM (n := n)‖ * ‖A - B‖)) := by
      exact mul_le_mul_of_nonneg_left (h1.trans
        (mul_le_mul_of_nonneg_left ((flattenCLM (n := n)).le_opNorm _) hL)) (norm_nonneg _)
    _ = _ := by ring

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open Matrix
open scoped Matrix.Norms.L2Operator
variable {n : Type u26} [Fintype n] [DecidableEq n]

lemma mixed_left_cfc_apply {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (V : unitary (Matrix n n ℂ)) (f : ℝ → ℝ) (i j : n) :
    (star (hA.eigenvectorUnitary : Matrix n n ℂ) * cfc f A * (V : Matrix n n ℂ)) i j =
      (f (hA.eigenvalues i) : ℂ) *
        (star (hA.eigenvectorUnitary : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j := by
  rw [hA.cfc_eq]
  change (star (hA.eigenvectorUnitary : Matrix n n ℂ) *
    ((hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i ↦ (f (hA.eigenvalues i) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ)) * (V : Matrix n n ℂ)) i j = _
  simp only [← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  rw [mul_assoc, diagonal_mul]

lemma mixed_right_cfc_apply {B : Matrix n n ℂ} (hB : B.IsHermitian)
    (U : unitary (Matrix n n ℂ)) (g : ℝ → ℝ) (i j : n) :
    (star (U : Matrix n n ℂ) * cfc g B * (hB.eigenvectorUnitary : Matrix n n ℂ)) i j =
      (g (hB.eigenvalues j) : ℂ) *
        (star (U : Matrix n n ℂ) * (hB.eigenvectorUnitary : Matrix n n ℂ)) i j := by
  rw [hB.cfc_eq]
  change (star (U : Matrix n n ℂ) *
    ((hB.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun j ↦ (g (hB.eigenvalues j) : ℂ)) *
      star (hB.eigenvectorUnitary : Matrix n n ℂ)) * (hB.eigenvectorUnitary : Matrix n n ℂ)) i j = _
  simp only [mul_assoc, Unitary.coe_star_mul_self, mul_one]
  rw [← mul_assoc, mul_diagonal, mul_comm]

lemma real_star_mul_real (x y : ℝ) (z : ℂ) :
    (star ((x : ℂ) * z) * ((y : ℂ) * z)).re = x * y * Complex.normSq z := by
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

lemma trace_cfc_product {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f g : ℝ → ℝ) :
    (trace (cfc f A * cfc g B)).re =
      ∑ i, ∑ j, f (hA.eigenvalues i) * g (hB.eigenvalues j) *
        Complex.normSq ((star (hA.eigenvectorUnitary : Matrix n n ℂ) *
          (hB.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  have hF : (cfc f A).IsHermitian := (cfc_predicate f A).isHermitian
  rw [← hF.star_eq, ← trace_star_mul_change hA.eigenvectorUnitary hB.eigenvectorUnitary,
    trace_star_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mixed_left_cfc_apply, mixed_right_cfc_apply, real_star_mul_real]

lemma trace_taylor_identity {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (F f : ℝ → ℝ) :
    (trace (cfc F B)).re - (trace (cfc F A)).re - (trace (cfc f A * (B - A))).re =
      ∑ i, ∑ j, (F (hB.eigenvalues j) - F (hA.eigenvalues i) -
        f (hA.eigenvalues i) * (hB.eigenvalues j - hA.eigenvalues i)) *
        Complex.normSq ((star (hA.eigenvectorUnitary : Matrix n n ℂ) *
          (hB.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  have h₁ := trace_cfc_product hA hB (fun _ ↦ 1) F
  have h₂ := trace_cfc_product hA hB F (fun _ ↦ 1)
  have h₃ := trace_cfc_product hA hB f id
  have h₄ := trace_cfc_product hA hB (fun x ↦ f x * x) (fun _ ↦ 1)
  have hcA : cfc (fun _ : ℝ ↦ 1) A = 1 := by
    erw [cfc_const (1 : ℝ) A hA]; simp
  have hcB : cfc (fun _ : ℝ ↦ 1) B = 1 := by
    erw [cfc_const (1 : ℝ) B hB]; simp
  rw [hcA, one_mul] at h₁
  rw [hcB, mul_one] at h₂ h₄
  erw [cfc_id ℝ B hB] at h₃
  have hm : cfc (fun x ↦ f x * x) A = cfc f A * A := by
    erw [cfc_mul f id A (A.finite_real_spectrum.continuousOn f)
      (by fun_prop), cfc_id ℝ A hA]
  rw [hm] at h₄
  rw [mul_sub, trace_sub, Complex.sub_re, h₁, h₂, h₃, h₄]
  simp only [id_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma trace_taylor_bound {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {F f : ℝ → ℝ} {L : ℝ}
    (hF : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ B,
      |F y - F x - f x * (y - x)| ≤ L * (y - x) ^ 2) :
    |(trace (cfc F B)).re - (trace (cfc F A)).re - (trace (cfc f A * (B - A))).re| ≤
      L * hsSquared (B - A) := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  have hm (i j : n) :
      (star (U : Matrix n n ℂ) * (B - A) * (V : Matrix n n ℂ)) i j =
        ((hB.eigenvalues j - hA.eigenvalues i : ℝ) : ℂ) *
          (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j := by
    have ha : A = conjStarAlgAut ℂ (Matrix n n ℂ) U
        (diagonal (fun i ↦ (hA.eigenvalues i : ℂ))) := hA.spectral_theorem
    have hb : B = conjStarAlgAut ℂ (Matrix n n ℂ) V
        (diagonal (fun i ↦ (hB.eigenvalues i : ℂ))) := hB.spectral_theorem
    have hh := mixed_diagonal_sub_apply U V hA.eigenvalues hB.eigenvalues i j
    rw [← ha, ← hb] at hh
    rw [← neg_sub A B, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, hh]
    simp only [Complex.ofReal_sub]
    ring
  rw [trace_taylor_identity hA hB, ← hsSquared_change U V (B - A)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp only [hsSquared, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  rw [hm, Complex.normSq_mul, Complex.normSq_ofReal, abs_mul,
    abs_of_nonneg (Complex.normSq_nonneg _)]
  have hh := hF _ (hA.eigenvalues_mem_spectrum_real i) _ (hB.eigenvalues_mem_spectrum_real j)
  have hp := mul_le_mul_of_nonneg_right hh
    (Complex.normSq_nonneg ((star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j))
  nlinarith [hp]

end SharpLiebThirring.MatrixProof

open scoped NNReal
namespace SharpLiebThirring.ScalarProof
open Set
lemma primitive_lipschitz {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) :
    LipschitzWith ⟨δ ^ (σ - 3 / 2), Real.rpow_nonneg hδ.le _⟩
      (regularizedPrimitive σ δ) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x ↦ (primitive_hasDerivAt σ hδ x).differentiableAt)
  intro x
  rw [(primitive_hasDerivAt σ hδ x).deriv]
  change ‖(max x 0 + δ) ^ (σ - 3 / 2)‖ ≤ δ ^ (σ - 3 / 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_rpow_of_nonpos hδ (by have := le_max_right x 0; linarith) (by linarith)

lemma scalar_trace_taylor {F f : ℝ → ℝ} {C : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (f x) x) (hf : LipschitzWith C f) (x y : ℝ) :
    |F y - F x - f x * (y - x)| ≤ (C : ℝ) * (y - x) ^ 2 := by
  have hd (t : ℝ) (_ : t ∈ uIcc x y) :
      HasDerivWithinAt (fun t ↦ F t - F x - f x * (t - x))
        (f t - f x) (uIcc x y) t := by
    convert! ((hF t).sub_const (F x) |>.sub
      (((hasDerivAt_id t).sub_const x).const_mul (f x))).hasDerivWithinAt using 1
    simp
  have hb (t : ℝ) (ht : t ∈ uIcc x y) : ‖f t - f x‖ ≤ (C : ℝ) * ‖y - x‖ := by
    exact (hf.norm_sub_le t x).trans (mul_le_mul_of_nonneg_left
      (abs_sub_left_of_mem_uIcc ht) C.coe_nonneg)
  have hh := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hb (left_mem_uIcc) (right_mem_uIcc)
  simpa only [sub_self, mul_zero, sub_zero, Real.norm_eq_abs, mul_assoc, ← sq, sq_abs] using hh

lemma secondPrimitive_hasDerivAt (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    HasDerivAt (secondPrimitive σ δ) (regularizedPrimitive σ δ y) y := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((primitive_differentiable σ hδ).continuous.intervalIntegrable 0 y)
    (primitive_differentiable σ hδ).continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    (primitive_differentiable σ hδ).continuous.continuousAt

end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof Asymptotics Filter
open scoped Matrix.Norms.L2Operator Topology
variable {n : Type u27} [Fintype n] [DecidableEq n]

lemma trace_primitive_hasFDerivAt {F f : ℝ → ℝ} {C : ℝ≥0}
    (hF : ∀ x, HasDerivAt F (f x) x) (hf : LipschitzWith C f)
    (A : selfAdjoint (Matrix n n ℂ)) :
    HasFDerivAt (fun B : selfAdjoint (Matrix n n ℂ) ↦ (trace (cfc F (B : Matrix n n ℂ))).re)
      ((tracePairCLM (cfc f (A : Matrix n n ℂ))).comp hermitianInclusion) A := by
  rw [hasFDerivAt_iff_isLittleO]
  apply IsBigO.trans_isLittleO (g := fun B : selfAdjoint (Matrix n n ℂ) ↦ ‖B - A‖ ^ 2)
    ?_ (isLittleO_pow_sub_sub A (by norm_num : 1 < (2 : ℕ)))
  apply IsBigO.of_bound ((C : ℝ) * ‖flattenCLM (n := n)‖ ^ 2)
  filter_upwards [] with B
  have hh := trace_taylor_bound A.property.isHermitian B.property.isHermitian
    (F := F) (f := f) (L := (C : ℝ))
    (fun x _ y _ ↦ scalar_trace_taylor hF hf x y)
  change |(trace (cfc F (B : Matrix n n ℂ))).re - (trace (cfc F (A : Matrix n n ℂ))).re -
    (trace (cfc f (A : Matrix n n ℂ) * ((B : Matrix n n ℂ) - (A : Matrix n n ℂ)))).re| ≤ _
  have hb := (flattenCLM (n := n)).le_opNorm ((B : Matrix n n ℂ) - (A : Matrix n n ℂ))
  have hb2 := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.2 hb
  rw [flatten_norm_sq, mul_pow] at hb2
  refine hh.trans ((mul_le_mul_of_nonneg_left hb2 C.coe_nonneg).trans_eq ?_)
  change (C : ℝ) * (‖flattenCLM (n := n)‖ ^ 2 * ‖B - A‖ ^ 2) = _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  ring

lemma trace_secondPrimitive_hasFDerivAt {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (A : selfAdjoint (Matrix n n ℂ)) :
    HasFDerivAt (fun B : selfAdjoint (Matrix n n ℂ) ↦
      (trace (cfc (secondPrimitive σ δ) (B : Matrix n n ℂ))).re)
      ((tracePairCLM (cfc (regularizedPrimitive σ δ) (A : Matrix n n ℂ))).comp hermitianInclusion) A :=
  trace_primitive_hasFDerivAt (secondPrimitive_hasDerivAt σ hδ) (primitive_lipschitz hσ hδ) A

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.ScalarProof
open Set
lemma primitive_remainder_lipschitz {σ δ a x r y z : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (ha : 0 < a) (hr : 0 ≤ r) (hxr : a ≤ x - r) (hy : |y| ≤ r) (hz : |z| ≤ r) :
    ‖(regularizedPrimitive σ δ (x + y) - regularizedPrimitive σ δ x -
        (x + δ) ^ (σ - 3 / 2) * y) -
      (regularizedPrimitive σ δ (x + z) - regularizedPrimitive σ δ x -
        (x + δ) ^ (σ - 3 / 2) * z)‖ ≤
      ((3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * r) * ‖y - z‖ := by
  have hd (t : ℝ) (ht : t ∈ Icc (-r) r) :
      HasDerivWithinAt (fun t : ℝ ↦ regularizedPrimitive σ δ (x + t) -
        regularizedPrimitive σ δ x - (x + δ) ^ (σ - 3 / 2) * t)
        ((x + t + δ) ^ (σ - 3 / 2) - (x + δ) ^ (σ - 3 / 2)) (Icc (-r) r) t := by
    have hxt : 0 ≤ x + t := by have := ht.1; linarith
    convert! (((primitive_hasDerivAt σ hδ (x + t)).comp t ((hasDerivAt_id t).const_add x)).sub_const
        (regularizedPrimitive σ δ x) |>.sub
        ((hasDerivAt_id t).const_mul ((x + δ) ^ (σ - 3 / 2)))).hasDerivWithinAt using 1
    simp [max_eq_left hxt]
  have hb (t : ℝ) (ht : t ∈ Icc (-r) r) :
      ‖(x + t + δ) ^ (σ - 3 / 2) - (x + δ) ^ (σ - 3 / 2)‖ ≤
        (3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * r := by
    have hh := derivative_lipschitz_on_positive hσ hδ ha
      (show a ≤ x + t by have := ht.1; linarith) (show a ≤ x by linarith)
    simp only [add_sub_cancel_left] at hh
    refine hh.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by linarith)
      (Real.rpow_nonneg (by linarith) _)))
    exact abs_le.2 ht
  exact (convex_Icc (-r) r).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (abs_le.1 hz) (abs_le.1 hy)
end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof
open scoped Matrix.Norms.L2Operator
variable {n : Type u28} [Fintype n] [DecidableEq n]

lemma matrixNormBridge_nonneg : 0 ≤ matrixNormBridge n := mul_nonneg (norm_nonneg _) (norm_nonneg _)

lemma cfc_remainder_eq (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (x : ℝ)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc (fun y : ℝ ↦ regularizedPrimitive σ δ (x + y) -
      regularizedPrimitive σ δ x - (x + δ) ^ (σ - 3 / 2) * y) A =
      cfc (regularizedPrimitive σ δ) (x • 1 + A) -
        regularizedPrimitive σ δ x • 1 - (x + δ) ^ (σ - 3 / 2) • A := by
  have hc := (primitive_differentiable σ hδ).continuous
  erw [cfc_sub (fun y : ℝ ↦ regularizedPrimitive σ δ (x + y) -
      regularizedPrimitive σ δ x) (fun y : ℝ ↦ (x + δ) ^ (σ - 3 / 2) * y) A
      (by fun_prop) (by fun_prop),
    cfc_sub (fun y : ℝ ↦ regularizedPrimitive σ δ (x + y))
      (fun _ : ℝ ↦ regularizedPrimitive σ δ x) A (by fun_prop) (by fun_prop),
    cfc_const (regularizedPrimitive σ δ x) A hA,
    cfc_const_mul_id ((x + δ) ^ (σ - 3 / 2)) A hA,
    Algebra.algebraMap_eq_smul_one, ← cfc_scalar_add _ hc x hA]

lemma cfc_remainder_lipschitz {σ δ a x r : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (ha : 0 < a) (hr : 0 ≤ r) (hxr : a ≤ x - r)
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hnA : ‖A‖ ≤ r) (hnB : ‖B‖ ≤ r) :
    ‖(cfc (regularizedPrimitive σ δ) (x • 1 + A) -
      regularizedPrimitive σ δ x • 1 - (x + δ) ^ (σ - 3 / 2) • A) -
      (cfc (regularizedPrimitive σ δ) (x • 1 + B) -
      regularizedPrimitive σ δ x • 1 - (x + δ) ^ (σ - 3 / 2) • B)‖ ≤
      matrixNormBridge n * ((3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * r) * ‖A - B‖ := by
  rw [← cfc_remainder_eq σ hδ x hA, ← cfc_remainder_eq σ hδ x hB]
  apply cfc_lipschitz_norm hA hB (mul_nonneg (mul_nonneg (by linarith)
    (Real.rpow_nonneg (by linarith) _)) hr)
  intro y hy z hz
  exact primitive_remainder_lipschitz hσ hδ ha hr hxr
    ((spectrum_abs_le_matrix_norm hy).trans hnA) ((spectrum_abs_le_matrix_norm hz).trans hnB)

omit [Fintype n] in
lemma quadraticMatrix_sub (C B D : Matrix n n ℂ) (s : ℝ) :
    quadraticMatrix C B s - quadraticMatrix C D s = (-2 * s) • (B - D) := by
  unfold quadraticMatrix
  module

lemma cfc_quadratic_lipschitz {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hD : D.IsHermitian) (s : ℝ) :
    ‖cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
      cfc (regularizedPrimitive σ δ) (quadraticMatrix C D s)‖ ≤
      matrixNormBridge n * δ ^ (σ - 3 / 2) * (2 * |s|) * ‖B - D‖ := by
  have hh := cfc_lipschitz_norm (quadraticMatrix_hermitian hC hB s)
    (quadraticMatrix_hermitian hC hD s) (Real.rpow_nonneg hδ.le (σ - 3 / 2))
    (fun x _ y _ ↦ (primitive_lipschitz hσ hδ).norm_sub_le x y)
  rw [quadraticMatrix_sub, norm_smul] at hh
  simpa [Real.norm_eq_abs, abs_mul, mul_assoc, matrixNormBridge] using hh

lemma pairedFieldIntegrand_lipschitz_global {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hD : D.IsHermitian) (s : ℝ) :
    ‖pairedFieldIntegrand σ δ C B s - pairedFieldIntegrand σ δ C D s‖ ≤
      (4 * matrixNormBridge n * δ ^ (σ - 3 / 2) * |s|) * ‖B - D‖ := by
  have he : pairedFieldIntegrand σ δ C B s - pairedFieldIntegrand σ δ C D s =
      (cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
        cfc (regularizedPrimitive σ δ) (quadraticMatrix C D s)) +
      (cfc (regularizedPrimitive σ δ) (quadraticMatrix C B (-s)) -
        cfc (regularizedPrimitive σ δ) (quadraticMatrix C D (-s))) := by
    unfold pairedFieldIntegrand
    abel
  rw [he]
  have h1 := cfc_quadratic_lipschitz hσ hδ hC hB hD s
  have h2 := cfc_quadratic_lipschitz hσ hδ hC hB hD (-s)
  rw [abs_neg] at h2
  linarith [norm_add_le
    (cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
      cfc (regularizedPrimitive σ δ) (quadraticMatrix C D s))
    (cfc (regularizedPrimitive σ δ) (quadraticMatrix C B (-s)) -
      cfc (regularizedPrimitive σ δ) (quadraticMatrix C D (-s)))]

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof
open scoped Matrix.Norms.L2Operator
variable {n : Type u30} [Fintype n] [DecidableEq n]

lemma quadraticRemainder_lipschitz_tail {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (hD : D.IsHermitian)
    (hBM : ‖B‖ ≤ M) (hDM : ‖D‖ ≤ M) {s : ℝ}
    (hs : max 1 (2 * (‖C‖ + 2 * M)) ≤ |s|) :
    ‖quadraticRemainder σ δ C B s - quadraticRemainder σ δ C D s‖ ≤
      (2 * matrixNormBridge n * (3 / 2 - σ) * (‖C‖ + 2 * M) *
        (1 / 4 : ℝ) ^ (σ - 5 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2)) * ‖B - D‖ := by
  have hs1 : 1 ≤ |s| := (le_max_left _ _).trans hs
  have hsA : 2 * (‖C‖ + 2 * M) ≤ |s| := (le_max_right _ _).trans hs
  have hM : 0 ≤ M := (norm_nonneg _).trans hBM
  let A := ‖C‖ + 2 * M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs2 : 0 < s ^ 2 := by nlinarith [sq_abs s]
  have hxr : s ^ 2 / 2 ≤ s ^ 2 - A * |s| := by
    dsimp [A]; nlinarith [sq_abs s]
  have hnB : ‖C - (2 * s) • B‖ ≤ A * |s| :=
    (perturbed_norm_le hs1).trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (abs_nonneg _))
  have hnD : ‖C - (2 * s) • D‖ ≤ A * |s| :=
    (perturbed_norm_le hs1).trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (abs_nonneg _))
  have hh := cfc_remainder_lipschitz hσ hδ (by linarith : 0 < s ^ 2 / 2)
    (mul_nonneg hA (abs_nonneg s)) hxr
    (hC.sub (hB.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (2 * s))))
    (hC.sub (hD.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (2 * s)))) hnB hnD
  have he : (C - (2 * s) • B) - (C - (2 * s) • D) = (-2 * s) • (B - D) := by module
  rw [he, norm_smul] at hh
  simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  have hw := quadratic_taylor_weight (A := 1) hσ hδ hs1
  simp only [one_mul, one_pow, mul_one, sq_abs] at hw
  have hp : 0 ≤ 2 * matrixNormBridge n * (3 / 2 - σ) * A * ‖B - D‖ := by
    have := matrixNormBridge_nonneg (n := n)
    have : 0 ≤ 3 / 2 - σ := by linarith
    positivity
  calc
    _ ≤ matrixNormBridge n * ((3 / 2 - σ) * (s ^ 2 / 2 + δ) ^ (σ - 5 / 2) * (A * |s|)) *
        (2 * |s| * ‖B - D‖) := hh
    _ = (2 * matrixNormBridge n * (3 / 2 - σ) * A * ‖B - D‖) *
        ((s ^ 2 / 2 + δ) ^ (σ - 5 / 2) * s ^ 2) := by rw [← sq_abs s]; ring
    _ ≤ (2 * matrixNormBridge n * (3 / 2 - σ) * A * ‖B - D‖) *
        ((1 / 4 : ℝ) ^ (σ - 5 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2)) :=
      mul_le_mul_of_nonneg_left hw hp
    _ = _ := by dsimp [A]; ring

lemma pairedFieldIntegrand_remainder_difference (σ δ : ℝ) (C B D : Matrix n n ℂ) (s : ℝ) :
    pairedFieldIntegrand σ δ C B s - pairedFieldIntegrand σ δ C D s =
      (quadraticRemainder σ δ C B s - quadraticRemainder σ δ C D s) +
      (quadraticRemainder σ δ C B (-s) - quadraticRemainder σ δ C D (-s)) := by
  unfold pairedFieldIntegrand quadraticRemainder
  simp only [neg_sq]
  module

lemma pairedFieldIntegrand_lipschitz_tail {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (hD : D.IsHermitian)
    (hBM : ‖B‖ ≤ M) (hDM : ‖D‖ ≤ M) {s : ℝ}
    (hs : max 1 (2 * (‖C‖ + 2 * M)) ≤ |s|) :
    ‖pairedFieldIntegrand σ δ C B s - pairedFieldIntegrand σ δ C D s‖ ≤
      (4 * matrixNormBridge n * (3 / 2 - σ) * (‖C‖ + 2 * M) *
        (1 / 4 : ℝ) ^ (σ - 5 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2)) * ‖B - D‖ := by
  have h1 := quadraticRemainder_lipschitz_tail hσ hδ hC hB hD hBM hDM hs
  have h2 := quadraticRemainder_lipschitz_tail hσ hδ hC hB hD hBM hDM
    (s := -s) (by rwa [abs_neg])
  rw [neg_sq] at h2
  rw [pairedFieldIntegrand_remainder_difference]
  linarith [norm_add_le (quadraticRemainder σ δ C B s - quadraticRemainder σ δ C D s)
    (quadraticRemainder σ δ C B (-s) - quadraticRemainder σ δ C D (-s))]

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory
open scoped Matrix.Norms.L2Operator NNReal
variable {n : Type u31} [Fintype n] [DecidableEq n]

lemma fieldLipEnvelope_nonneg {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hM : 0 ≤ M) (C : Matrix n n ℂ) (s : ℝ) : 0 ≤ fieldLipEnvelope σ δ M C s := by
  have h1 : 0 ≤ matrixNormBridge n := matrixNormBridge_nonneg
  have h2 : 0 ≤ 3 / 2 - σ := by linarith
  unfold fieldLipEnvelope
  apply add_nonneg
  · exact Set.indicator_nonneg (fun _ _ ↦ by positivity) _
  · positivity

lemma integrable_fieldLipEnvelope {σ δ : ℝ} (hσ : σ < 1) (M : ℝ)
    (C : Matrix n n ℂ) : Integrable (fieldLipEnvelope σ δ M C) := by
  apply Integrable.add
  · apply IntegrableOn.integrable_indicator _ measurableSet_Icc
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      4 * matrixNormBridge n * δ ^ (σ - 3 / 2) * |s|)).integrableOn_Icc
  · exact (normalization_integrable hσ).const_mul _

lemma pairedFieldIntegrand_lipschitz_envelope {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (hD : D.IsHermitian)
    (hBM : ‖B‖ ≤ M) (hDM : ‖D‖ ≤ M) (s : ℝ) :
    ‖pairedFieldIntegrand σ δ C B s - pairedFieldIntegrand σ δ C D s‖ ≤
      fieldLipEnvelope σ δ M C s * ‖B - D‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hBM
  have h1 : 0 ≤ matrixNormBridge n := matrixNormBridge_nonneg
  have h2 : 0 ≤ 3 / 2 - σ := by linarith
  let R := max 1 (2 * (‖C‖ + 2 * M))
  by_cases hs : |s| ≤ R
  · have hs' : s ∈ Set.Icc (-R) R := abs_le.mp hs
    have hh := pairedFieldIntegrand_lipschitz_global hσ hδ hC hB hD s
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    unfold fieldLipEnvelope
    rw [Set.indicator_of_mem hs']
    exact le_add_of_nonneg_right (by positivity)
  · have hh := pairedFieldIntegrand_lipschitz_tail hσ hδ hC hB hD hBM hDM
      (le_of_not_ge hs)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact le_add_of_nonneg_left (Set.indicator_nonneg (fun _ _ ↦ by positivity) _)

lemma pairedFieldIntegrand_norm_on_ball {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hM : 0 ≤ M) {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hBM : ‖B‖ ≤ M) (s : ℝ) :
    ‖pairedFieldIntegrand σ δ C B s‖ ≤
      ‖pairedFieldIntegrand σ δ C 0 s‖ + fieldLipEnvelope σ δ M C s * M := by
  have hh := pairedFieldIntegrand_lipschitz_envelope hσ hδ hC hB Matrix.isHermitian_zero
    hBM (by simpa using hM) s
  simp only [sub_zero] at hh
  have hs := hh.trans (mul_le_mul_of_nonneg_left hBM (fieldLipEnvelope_nonneg hσ hδ hM C s))
  have ht := norm_le_norm_add_norm_sub' (pairedFieldIntegrand σ δ C B s)
    (pairedFieldIntegrand σ δ C 0 s)
  linarith

lemma hermitianField_lipschitz_bound {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (hD : D.IsHermitian)
    (hBM : ‖B‖ ≤ M) (hDM : ‖D‖ ≤ M) :
    ‖hermitianField σ δ C B - hermitianField σ δ C D‖ ≤
      (|fieldNormalization σ / 2| * ∫ s : ℝ, fieldLipEnvelope σ δ M C s) * ‖B - D‖ := by
  have hiB := integrable_pairedFieldIntegrand hσ hδ hC hB
  have hiD := integrable_pairedFieldIntegrand hσ hδ hC hD
  unfold hermitianField
  rw [← smul_sub, ← integral_sub hiB hiD, norm_smul, Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le (integrable_fieldLipEnvelope hσ M C |>.mul_const ‖B - D‖)
    (Filter.Eventually.of_forall (pairedFieldIntegrand_lipschitz_envelope hσ hδ hC hB hD hBM hDM))
  rw [integral_mul_const] at hh
  exact (mul_le_mul_of_nonneg_left hh (abs_nonneg _)).trans_eq (mul_assoc _ _ _).symm

lemma hermitianField_locallyLipschitz {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C : Matrix n n ℂ} (hC : C.IsHermitian) :
    LocallyLipschitz (fun B : selfAdjoint (Matrix n n ℂ) ↦ hermitianField σ δ C B) := by
  intro B
  let M : ℝ := ‖B‖ + 1
  let L : ℝ := |fieldNormalization σ / 2| * ∫ s : ℝ, fieldLipEnvelope σ δ M C s
  have hL : 0 ≤ L := mul_nonneg (abs_nonneg _) (integral_nonneg (fun s ↦
    fieldLipEnvelope_nonneg hσ hδ (by dsimp [M]; positivity) C s))
  refine ⟨⟨L, hL⟩, Metric.ball B 1, Metric.ball_mem_nhds B (by norm_num), ?_⟩
  change @LipschitzOnWith _ _ (PseudoMetricSpace.toPseudoEMetricSpace)
    (PseudoMetricSpace.toPseudoEMetricSpace) _ _ _
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro A hA D hD
  have hAM : ‖(A : Matrix n n ℂ)‖ ≤ M := by
    change ‖A‖ ≤ ‖B‖ + 1
    exact norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hA).le
  have hDM : ‖(D : Matrix n n ℂ)‖ ≤ M := by
    change ‖D‖ ≤ ‖B‖ + 1
    exact norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hD).le
  exact hermitianField_lipschitz_bound hσ hδ hC A.prop D.prop hAM hDM

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FieldPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u32 u33 u34

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {n : Type u32} [Fintype n] [DecidableEq n]

attribute [local instance] OAI.SharpLiebThirring.MatrixProof.instSeminormedAddCommGroupSubtypeMatrixComplexMemAddSubgroupSelfAdjoint_solutions
attribute [local instance] OAI.SharpLiebThirring.MatrixProof.instNormedSpaceRealSubtypeMatrixComplexMemAddSubgroupSelfAdjoint_solutions
lemma traceGradientNorm_nonneg : 0 ≤ traceGradientNorm (n := n) :=
  (traceGradientMap (n := n)).opNorm_nonneg

lemma traceGradientMap_bound (M : Matrix n n ℂ) :
    ‖traceGradientMap M‖ ≤ traceGradientNorm (n := n) * ‖M‖ := by
  have hh := (traceGradientMap (n := n)).le_opNorm M
  convert! hh

lemma quadraticSelfAdjoint_hasFDerivAt (C B : selfAdjoint (Matrix n n ℂ)) (s : ℝ) :
    HasFDerivAt (quadraticSelfAdjoint C s) ((-2 * s) • ContinuousLinearMap.id ℝ _) B := by
  convert! (((hasFDerivAt_id (𝕜 := ℝ) B).const_smul (2 * s)).const_sub C).add_const ((s ^ 2) • 1) using 1
  ext H : 1
  change (-2 * s) • H = -((2 * s) • H)
  module

lemma pairedTracePotential_zero (σ δ : ℝ) (C : selfAdjoint (Matrix n n ℂ)) (s : ℝ) :
    pairedTracePotential σ δ C 0 s = 0 := by
  simp [pairedTracePotential, quadraticMatrix]

lemma pairedTracePotential_hasFDerivAt {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (C B : selfAdjoint (Matrix n n ℂ)) {s : ℝ} (hs : s ≠ 0) :
    HasFDerivAt (fun B ↦ pairedTracePotential σ δ C B s)
      (traceGradientMap (pairedFieldIntegrand σ δ C B s)) B := by
  have h1 := (trace_secondPrimitive_hasFDerivAt hσ hδ (quadraticSelfAdjoint C s B)).comp B
    (quadraticSelfAdjoint_hasFDerivAt C B s)
  have h2 := (trace_secondPrimitive_hasFDerivAt hσ hδ (quadraticSelfAdjoint C (-s) B)).comp B
    (quadraticSelfAdjoint_hasFDerivAt C B (-s))
  have h3 := (traceGradientMap (1 : Matrix n n ℂ)).hasFDerivAt (x := B)
  have hh := ((h1.sub h2).neg.const_mul (2 * s)⁻¹).sub (h3.const_mul
    (2 * regularizedPrimitive σ δ (s ^ 2)))
  convert! hh using 1
  · funext D
    simp [pairedTracePotential, Function.comp_def, traceGradientMap_apply, div_eq_mul_inv, mul_comm]
  · ext H
    simp only [_root_.sub_apply, _root_.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      _root_.neg_apply, traceGradientMap_apply, tracePairCLM_apply,
      quadraticSelfAdjoint_coe]
    change (trace (pairedFieldIntegrand σ δ C B s * (H : Matrix n n ℂ))).re = _
    simp only [pairedFieldIntegrand, sub_mul, add_mul, smul_mul_assoc, one_mul,
      trace_sub, trace_add, trace_smul, Complex.sub_re, Complex.add_re, Complex.real_smul,
      hermitianInclusion, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
      AddHom.coe_mk, selfAdjoint.val_smul, mul_smul_comm, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    simp only [smul_eq_mul]
    field_simp [hs]
    ring

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {n : Type u33} [Fintype n] [DecidableEq n]

attribute [local instance] OAI.SharpLiebThirring.MatrixProof.instSeminormedAddCommGroupSubtypeMatrixComplexMemAddSubgroupSelfAdjoint_solutions_1
attribute [local instance] OAI.SharpLiebThirring.MatrixProof.instNormedSpaceRealSubtypeMatrixComplexMemAddSubgroupSelfAdjoint_solutions_1
lemma measurable_pairedTracePotential {δ : ℝ} (hδ : 0 < δ) (σ : ℝ)
    (C B : selfAdjoint (Matrix n n ℂ)) : Measurable (pairedTracePotential σ δ C B) := by
  have hc : Continuous (fun s : ℝ ↦ cfc (secondPrimitive σ δ)
      (quadraticMatrix (C : Matrix n n ℂ) (B : Matrix n n ℂ) s)) :=
    Continuous.cfc_of_mem_nhdsSet (s := Set.univ) _ (Filter.univ_mem)
      (by unfold quadraticMatrix; fun_prop)
      (fun s ↦ quadraticMatrix_hermitian C.prop B.prop s)
      (continuous_iff_continuousAt.mpr (fun y ↦ (secondPrimitive_hasDerivAt σ hδ y).continuousAt)).continuousOn
  have ht : Continuous (fun s : ℝ ↦ (trace (cfc (secondPrimitive σ δ)
      (quadraticMatrix (C : Matrix n n ℂ) (B : Matrix n n ℂ) s))).re) := by fun_prop
  unfold pairedTracePotential
  exact (((ht.measurable.sub (ht.comp continuous_neg).measurable).neg).div
    (by fun_prop)).sub (((continuous_const.mul
      ((primitive_differentiable σ hδ).continuous.comp (continuous_pow 2))).mul
        continuous_const).measurable)

lemma integrable_fieldGradientEnvelope {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (M : ℝ) {C : Matrix n n ℂ} (hC : C.IsHermitian) :
    Integrable (fieldGradientEnvelope σ δ M (C : Matrix n n ℂ)) :=
  ((integrable_pairedFieldIntegrand hσ hδ hC Matrix.isHermitian_zero).norm.add
    ((integrable_fieldLipEnvelope hσ M C).mul_const M)).const_mul _

lemma fieldGradientEnvelope_bound {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hM : 0 ≤ M) (C B : selfAdjoint (Matrix n n ℂ)) (hB : ‖B‖ ≤ M) (s : ℝ) :
    ‖traceGradientMap (pairedFieldIntegrand σ δ (C : Matrix n n ℂ) (B : Matrix n n ℂ) s)‖ ≤ fieldGradientEnvelope σ δ M (C : Matrix n n ℂ) s := by
  have hnorm := pairedFieldIntegrand_norm_on_ball hσ hδ hM C.prop B.prop hB s
  have hscaled := mul_le_mul_of_nonneg_left hnorm (traceGradientNorm_nonneg (n := n))
  have hop := traceGradientMap_bound (n := n)
    (pairedFieldIntegrand σ δ (C : Matrix n n ℂ) (B : Matrix n n ℂ) s)
  have hr := le_trans hop hscaled
  convert! hr using 1


lemma pairedTracePotential_bound {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hM : 0 ≤ M) (C B : selfAdjoint (Matrix n n ℂ)) (hB : ‖B‖ ≤ M)
    {s : ℝ} (hs : s ≠ 0) :
    ‖pairedTracePotential σ δ C B s‖ ≤ fieldGradientEnvelope σ δ M (C : Matrix n n ℂ) s * ‖B‖ := by
  have hh := (convex_closedBall (0 : selfAdjoint (Matrix n n ℂ)) M).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (x := 0) (y := B)
    (fun A _ ↦ (pairedTracePotential_hasFDerivAt hσ hδ C A hs).hasFDerivWithinAt)
    (fun A hA ↦ fieldGradientEnvelope_bound hσ hδ hM C A (by simpa using hA) s)
    (by simpa using hM) (by simpa using hB)
  simpa only [pairedTracePotential_zero, sub_zero] using hh

lemma integrable_pairedTracePotential {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (C B : selfAdjoint (Matrix n n ℂ)) : Integrable (pairedTracePotential σ δ C B) := by
  apply ((integrable_fieldGradientEnvelope hσ hδ ‖B‖ C.prop).mul_const ‖B‖).mono'
    (measurable_pairedTracePotential hδ σ C B).aestronglyMeasurable
  filter_upwards [volume.ae_ne (0 : ℝ)] with s hs
  exact pairedTracePotential_bound hσ hδ (norm_nonneg _) C B le_rfl hs

lemma hermitianPotential_hasFDerivAt {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (C B : selfAdjoint (Matrix n n ℂ)) :
    HasFDerivAt (hermitianPotential σ δ C)
      (traceGradientMap (hermitianField σ δ C B)) B := by
  let M : ℝ := ‖B‖ + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun A s ↦ pairedTracePotential σ δ C A s)
    (F' := fun (A : selfAdjoint (Matrix n n ℂ)) (s : ℝ) ↦
      traceGradientMap (pairedFieldIntegrand σ δ (C : Matrix n n ℂ) (A : Matrix n n ℂ) s))
    (bound := fieldGradientEnvelope σ δ M (C : Matrix n n ℂ))
    (Metric.ball_mem_nhds B (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (fun A ↦ (measurable_pairedTracePotential hδ σ C A).aestronglyMeasurable))
    (integrable_pairedTracePotential hσ hδ C B)
    ((traceGradientMap.continuous.comp (continuous_pairedFieldIntegrand hδ σ C.prop B.prop)).aestronglyMeasurable)
    (Eventually.of_forall (fun s A hA ↦ fieldGradientEnvelope_bound hσ hδ hM C A
      (norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hA).le) s))
    (integrable_fieldGradientEnvelope hσ hδ M C.prop)
    (by filter_upwards [volume.ae_ne (0 : ℝ)] with s hs using fun A _ ↦
      pairedTracePotential_hasFDerivAt hσ hδ C A hs)
  have hi := (traceGradientMap (n := n)).integral_comp_comm (𝕜 := ℝ)
    (Fₗ := selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ)
    (integrable_pairedFieldIntegrand hσ hδ C.prop B.prop)
  have he : (∫ s : ℝ, traceGradientMap (pairedFieldIntegrand σ δ (C : Matrix n n ℂ) (B : Matrix n n ℂ) s)) =
      traceGradientMap (∫ s : ℝ, pairedFieldIntegrand σ δ (C : Matrix n n ℂ) (B : Matrix n n ℂ) s) := by
    convert! hi
  rw [he] at hh
  convert! hh.const_smul (fieldNormalization σ / 2) using 1
  simp [hermitianField]

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {n : Type u34} [Fintype n] [DecidableEq n]

attribute [local instance] OAI.SharpLiebThirring.MatrixProof.instSeminormedAddCommGroupSubtypeMatrixComplexMemAddSubgroupSelfAdjoint_solutions_2
attribute [local instance] OAI.SharpLiebThirring.MatrixProof.instNormedSpaceRealSubtypeMatrixComplexMemAddSubgroupSelfAdjoint_solutions_2
@[simp] lemma hermitianPotential_zero (σ δ : ℝ) (C : selfAdjoint (Matrix n n ℂ)) :
    hermitianPotential σ δ C 0 = 0 := by
  simp [hermitianPotential, pairedTracePotential_zero]

lemma hermitianPotential_radial_hasDerivAt {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (C B : selfAdjoint (Matrix n n ℂ)) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ hermitianPotential σ δ C (t • B))
      (traceGradientMap (hermitianField σ δ C (t • B)) B) t := by
  convert! (hermitianPotential_hasFDerivAt hσ hδ C (t • B)).comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const B) using 1
  simp

lemma hermitianPotential_radial {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (C B : selfAdjoint (Matrix n n ℂ)) :
    hermitianPotential σ δ C B =
      ∫ t in (0 : ℝ)..1, (trace ((B : Matrix n n ℂ) * hermitianField σ δ C (t • B))).re := by
  have hc : Continuous (fun t : ℝ ↦ hermitianField σ δ (C : Matrix n n ℂ) (t • B)) := by
    have hcf := (hermitianField_locallyLipschitz hσ hδ C.prop).continuous
    have hsm : Continuous (fun t : ℝ ↦ t • B) := by fun_prop
    have hh := hcf.comp hsm
    convert! hh
  have ht : Continuous (fun t : ℝ ↦ traceGradientMap (hermitianField σ δ C (t • B)) B) := by
    simp only [traceGradientMap_apply]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hermitianPotential_radial_hasDerivAt hσ hδ C B t)
    (ht.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, hermitianPotential_zero, sub_zero] at hi
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro t _
  change traceGradientMap (hermitianField σ δ C (t • B)) B = _
  rw [traceGradientMap_apply, trace_mul_comm]

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

lemma matrixField_eq_realPart {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian) :
    matrixField σ δ k B = realPartCLM (hermitianField σ δ
      (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B)) := by
  rw [← complexify_matrixField hσ hδ k hB, realPartCLM_complexify]

lemma matrixField_continuous {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ) :
    Continuous (fun B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) ↦ matrixField σ δ k B) := by
  have hc := (hermitianField_locallyLipschitz hσ hδ
    (complexify_hermitian (isHermitian_diagonal (fun i ↦ k i ^ 2)))).continuous
  have hh := realPartCLM.continuous.comp (hc.comp realHermitianComplexify_continuous)
  convert! hh using 1
  funext B
  exact matrixField_eq_realPart hσ hδ k B.prop

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.ActionPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u35

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

lemma constraintDefect_continuous {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ) :
    Continuous (constraintDefect σ δ k) := by
  have hc : Continuous (fun z : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ) ↦
      matrixField σ δ k z.1) := (matrixField_continuous hσ hδ k).comp continuous_fst
  unfold constraintDefect
  fun_prop

end SharpLiebThirring.ActionProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.BoundaryValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u36

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {n : Type u36} [Fintype n] [DecidableEq n]

omit [Fintype n] in
lemma quadraticMatrix_diagonal (c b : n → ℝ) (s : ℝ) :
    quadraticMatrix (diagonal (fun i ↦ (c i : ℂ))) (diagonal (fun i ↦ (b i : ℂ))) s =
      diagonal (fun i ↦ (((s - b i) ^ 2 + (c i - b i ^ 2) : ℝ) : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [quadraticMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      diagonal_apply_eq, one_apply_eq, Complex.real_smul]
    push_cast
    ring
  · simp [quadraticMatrix, hij]

lemma fieldIntegrand_diagonal {δ : ℝ} (hδ : 0 < δ) (σ : ℝ) (c b : n → ℝ) (s : ℝ) :
    fieldIntegrand σ δ (diagonal (fun i ↦ (c i : ℂ))) (diagonal (fun i ↦ (b i : ℂ))) s =
      diagonal (fun i ↦ ((regularizedPrimitive σ δ ((s - b i) ^ 2 + (c i - b i ^ 2)) -
        regularizedPrimitive σ δ (s ^ 2) : ℝ) : ℂ)) := by
  rw [fieldIntegrand, quadraticMatrix_diagonal,
    cfc_diagonal_real _ _ (primitive_differentiable σ hδ).continuous]
  ext i j
  by_cases hij : i = j <;> simp [hij, Complex.real_smul]

lemma hermitianField_diagonal {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (c b : n → ℝ) :
    hermitianField σ δ (diagonal (fun i ↦ (c i : ℂ))) (diagonal (fun i ↦ (b i : ℂ))) =
      diagonal (fun i ↦ (scalarMu σ δ (c i - b i ^ 2) : ℂ)) := by
  have hC : (diagonal (fun i ↦ (c i : ℂ))).IsHermitian := isHermitian_diagonal_iff.2 (fun i ↦ by simp [IsSelfAdjoint])
  have hB : (diagonal (fun i ↦ (b i : ℂ))).IsHermitian := isHermitian_diagonal_iff.2 (fun i ↦ by simp [IsSelfAdjoint])
  apply tendsto_nhds_unique (hermitianField_cutoff_limit hσ hδ hC hB)
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  have hc := continuous_fieldIntegrand hδ σ hC hB
  have he (R : ℝ) := (entryCLM i j).intervalIntegral_comp_comm (μ := volume)
    (hc.intervalIntegrable (-R) R)
  simp only [entryCLM_apply] at he
  have he' (R : ℝ) :
      (fieldNormalization σ • ∫ s in -R..R, fieldIntegrand σ δ
        (diagonal (fun i ↦ (c i : ℂ))) (diagonal (fun i ↦ (b i : ℂ))) s) i j =
      fieldNormalization σ • ∫ s in -R..R, fieldIntegrand σ δ
        (diagonal (fun i ↦ (c i : ℂ))) (diagonal (fun i ↦ (b i : ℂ))) s i j := by
    simp only [Matrix.smul_apply]
    rw [← he R]
  suffices ht : Tendsto (fun R : ℝ ↦ fieldNormalization σ • ∫ s in -R..R,
      fieldIntegrand σ δ (diagonal (fun i ↦ (c i : ℂ)))
        (diagonal (fun i ↦ (b i : ℂ))) s i j) atTop
      (𝓝 ((diagonal (fun i ↦ (scalarMu σ δ (c i - b i ^ 2) : ℂ))) i j)) by
    apply ht.congr
    intro R
    exact (he' R).symm
  simp only [fieldIntegrand_diagonal hδ]
  by_cases hij : i = j
  · subst j
    simp only [diagonal_apply_eq]
    have hs := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (primitive_shift_limit hσ hδ (c i - b i ^ 2) (b i))
    convert! hs using 1
    funext R
    rw [intervalIntegral.integral_ofReal]
    simp [Complex.real_smul]
  · simp only [diagonal_apply_ne _ hij, intervalIntegral.integral_zero, smul_zero]
    exact tendsto_const_nhds

lemma matrixField_diagonal {N : ℕ} {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k b : Fin N → ℝ) :
    matrixField σ δ k (diagonal b) = diagonal (fun i ↦ scalarMu σ δ (k i ^ 2 - b i ^ 2)) := by
  rw [matrixField_eq_realPart hσ hδ k (isHermitian_diagonal b),
    complexify_diagonal, complexify_diagonal, hermitianField_diagonal hσ hδ]
  ext i j
  by_cases hij : i = j <;> simp [realPartCLM, hij]

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

attribute [local instance] OAI.SharpLiebThirring.MatrixProof.instSeminormedAddCommGroupSubtypeMatrixFinComplexMemAddSubgroupSelfAdjoint_solutions
attribute [local instance] OAI.SharpLiebThirring.MatrixProof.instNormedSpaceRealSubtypeMatrixFinComplexMemAddSubgroupSelfAdjoint_solutions
lemma fieldPrimitive_eq_hermitianPotential {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) (B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) :
    fieldPrimitive σ δ k B =
      -hermitianPotential σ δ (realK2SelfAdjoint k) (realHermitianComplexify B) := by
  rw [hermitianPotential_radial hσ hδ]
  unfold fieldPrimitive
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← realHermitianComplexify_smul]
  change trace ((B : Matrix (Fin N) (Fin N) ℝ) * matrixField σ δ k (t • B)) =
    (trace (complexify B * hermitianField σ δ (complexify (diagonal (fun i ↦ k i ^ 2)))
      (complexify (t • (B : Matrix (Fin N) (Fin N) ℝ))))).re
  have hf := complexify_matrixField hσ hδ k (t • B).prop
  change complexify (matrixField σ δ k (t • (B : Matrix (Fin N) (Fin N) ℝ))) =
    hermitianField σ δ (complexify (diagonal (fun i ↦ k i ^ 2)))
      (complexify (t • (B : Matrix (Fin N) (Fin N) ℝ))) at hf
  rw [← hf, ← map_mul, complexify_trace_real]

lemma fieldPrimitive_hasFDerivAt {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) (B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) :
    HasFDerivAt (fun B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) ↦ fieldPrimitive σ δ k B)
      ((-traceGradientMap (complexify (matrixField σ δ k B))).comp realHermitianComplexifyCLM) B := by
  have hh := ((hermitianPotential_hasFDerivAt hσ hδ (realK2SelfAdjoint k)
    (realHermitianComplexify B)).neg).comp B realHermitianComplexifyCLM.hasFDerivAt
  convert! hh using 1
  · funext A
    exact fieldPrimitive_eq_hermitianPotential hσ hδ k A
  · rw [complexify_matrixField hσ hδ k B.prop]
    rfl

lemma fieldPrimitive_path_derivative {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) {B : ℝ → selfAdjoint (Matrix (Fin N) (Fin N) ℝ)}
    {B' : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)} {x : ℝ} (hB : HasDerivAt B B' x) :
    HasDerivAt (fun x ↦ fieldPrimitive σ δ k (B x))
      (-trace (matrixField σ δ k (B x) * (B' : Matrix (Fin N) (Fin N) ℝ))) x := by
  convert! (fieldPrimitive_hasFDerivAt hσ hδ k (B x)).comp_hasDerivAt x hB using 1
  change -trace (matrixField σ δ k (B x) * (B' : Matrix (Fin N) (Fin N) ℝ)) =
    -(trace (complexify (matrixField σ δ k (B x)) * complexify (B' : Matrix (Fin N) (Fin N) ℝ))).re
  rw [← map_mul, complexify_trace_real]

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.ActionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

lemma trace_square_real {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    trace (H * H) = ∑ i, ∑ j, H i j ^ 2 := by
  simp only [trace, diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : H j i = H i j := by simpa only [conjTranspose_apply, star_trivial] using congrFun (congrFun hH i) j
  rw [he, pow_two]

lemma quadratic_swap {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian)
    (a b : Fin N → ℝ) :
    (∑ i, a i * (B *ᵥ b) i) = ∑ i, b i * (B *ᵥ a) i := by
  simp only [mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : B j i = B i j := by simpa only [conjTranspose_apply, star_trivial] using congrFun (congrFun hB i) j
  rw [he]
  ring

lemma trace_rankone_mul (a : Fin N → ℝ) (H : Matrix (Fin N) (Fin N) ℝ) :
    trace (vecMulVec a a * H) = ∑ i, a i * (H *ᵥ a) i := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma quadratic_hasDerivAt {a a' : ℝ → Fin N → ℝ}
    {B B' : ℝ → Matrix (Fin N) (Fin N) ℝ} {x : ℝ}
    (ha : ∀ i, HasDerivAt (fun t ↦ a t i) (a' x i) x)
    (hB : ∀ i j, HasDerivAt (fun t ↦ B t i j) (B' x i j) x)
    (hBx : (B x).IsHermitian) :
    HasDerivAt (fun t ↦ ∑ i, a t i * (B t *ᵥ a t) i)
      (2 * (∑ i, a' x i * (B x *ᵥ a x) i) +
        trace (vecMulVec (a x) (a x) * B' x)) x := by
  have hh := HasDerivAt.sum (u := Finset.univ) (fun i _ ↦
    (ha i).mul (HasDerivAt.sum (u := Finset.univ) (fun j _ ↦ (hB i j).mul (ha j))))
  simp only [Finset.sum_apply, Pi.mul_apply] at hh
  convert! hh using 1
  · funext t
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.mul_apply]
  · rw [trace_rankone_mul]
    have hs := quadratic_swap hBx (a x) (a' x)
    change 2 * (∑ i, a' x i * (∑ j, B x i j * a x j)) +
        (∑ i, a x i * (∑ j, B' x i j * a x j)) =
      ∑ i, (a' x i * (∑ j, B x i j * a x j) +
        a x i * ∑ j, (B' x i j * a x j + B x i j * a' x j))
    simp_rw [Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib]
    change (∑ i, a x i * (∑ j, B x i j * a' x j)) =
      (∑ i, a' x i * (∑ j, B x i j * a x j)) at hs
    linarith

end SharpLiebThirring.ActionProof

namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

lemma realSelfAdjoint_entry_derivative
    {B : ℝ → selfAdjoint (Matrix (Fin N) (Fin N) ℝ)}
    {B' : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)} {x : ℝ}
    (hB : HasDerivAt B B' x) (i j : Fin N) :
    HasDerivAt (fun t ↦ (B t : Matrix (Fin N) (Fin N) ℝ) i j)
      ((B' : Matrix (Fin N) (Fin N) ℝ) i j) x :=
  (realSelfAdjointEntryCLM i j).hasFDerivAt.comp_hasDerivAt x hB

lemma real_rankone_isHermitian (a : Fin N → ℝ) : (vecMulVec a a).IsHermitian := by
  ext i j
  simp [vecMulVec, conjTranspose_apply, mul_comm]

/-- The exact penalized action identity, pointwise wherever the amplitude is
  differentiable. Hence it applies to the a.e. derivative of H¹ amplitudes. -/
lemma action_ode_identity {σ δ ε : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (hε : 0 < ε)
    (k : Fin N → ℝ) {a a' : ℝ → Fin N → ℝ}
    {B : ℝ → selfAdjoint (Matrix (Fin N) (Fin N) ℝ)}
    {B' : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)} {x : ℝ}
    (ha : ∀ i, HasDerivAt (fun t ↦ a t i) (a' x i) x)
    (hB : HasDerivAt B B' x)
    (hode : ε • (B' : Matrix (Fin N) (Fin N) ℝ) =
      matrixField σ δ k (B x) - vecMulVec (a x) (a x)) :
    HasDerivAt (fun t ↦ fieldPrimitive σ δ k (B t) +
      ∑ i, a t i * ((B t : Matrix (Fin N) (Fin N) ℝ) *ᵥ a t) i)
      (2 * (∑ i, a' x i * ((B x : Matrix (Fin N) (Fin N) ℝ) *ᵥ a x) i) -
        constraintDefect σ δ k (B x, a x) / ε) x := by
  let D := matrixField σ δ k (B x) - vecMulVec (a x) (a x)
  have hD : D.IsHermitian :=
    (matrixField_isHermitian hσ hδ k (B x).prop).sub (real_rankone_isHermitian _)
  have hb' : (B' : Matrix (Fin N) (Fin N) ℝ) = ε⁻¹ • D := by
    rw [show D = ε • (B' : Matrix (Fin N) (Fin N) ℝ) from hode.symm,
      smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
  have ht : trace (D * (B' : Matrix (Fin N) (Fin N) ℝ)) =
      constraintDefect σ δ k (B x, a x) / ε := by
    rw [hb', Matrix.mul_smul, trace_smul, trace_square_real hD]
    simp only [smul_eq_mul, constraintDefect, D, Matrix.sub_apply, vecMulVec_apply,
      div_eq_mul_inv, mul_comm]
  have hq := quadratic_hasDerivAt (B := fun t ↦ (B t : Matrix (Fin N) (Fin N) ℝ))
    (B' := fun _ ↦ (B' : Matrix (Fin N) (Fin N) ℝ)) ha
    (fun i j ↦ realSelfAdjoint_entry_derivative hB i j) (B x).prop
  have hj := fieldPrimitive_path_derivative hσ hδ k hB
  convert! hj.add hq using 1
  dsimp only [D] at ht
  rw [Matrix.sub_mul, trace_sub] at ht
  linarith

lemma quadratic_square_real {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian)
    (a : Fin N → ℝ) :
    (∑ i, a i * (B ^ 2 *ᵥ a) i) = ∑ i, (B *ᵥ a) i ^ 2 := by
  rw [pow_two, ← Matrix.mulVec_mulVec, quadratic_swap hB]
  simp [pow_two]

lemma action_pointwise_square_bound {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian)
    (a v : Fin N → ℝ) :
    2 * (∑ i, v i * (B *ᵥ a) i) ≤
      (∑ i, v i ^ 2) + ∑ i, a i * (B ^ 2 *ᵥ a) i := by
  rw [quadratic_square_real hB]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (v i - (B *ᵥ a) i)]

lemma action_penalty_pointwise {σ δ ε : ℝ} (k : Fin N → ℝ)
    (B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) (a v : Fin N → ℝ) :
    2 * (∑ i, v i * ((B : Matrix (Fin N) (Fin N) ℝ) *ᵥ a) i) -
        constraintDefect σ δ k (B, a) / ε ≤
      (∑ i, v i ^ 2) + (∑ i, k i ^ 2 * a i ^ 2) - (∑ i, a i ^ 2) ^ (1 + 1 / σ) +
        (actionDefect σ k (B, a) - constraintDefect σ δ k (B, a) / ε) := by
  have hh := action_pointwise_square_bound B.prop a v
  have hK : (∑ i, a i * ((diagonal (fun i ↦ k i ^ 2) -
      (B : Matrix (Fin N) (Fin N) ℝ) ^ 2) *ᵥ a) i) =
      (∑ i, k i ^ 2 * a i ^ 2) - ∑ i, a i * ((B : Matrix (Fin N) (Fin N) ℝ) ^ 2 *ᵥ a) i := by
    rw [sub_mulVec]
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, mulVec_diagonal]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold actionDefect
  dsimp only
  rw [hK]
  linarith

end SharpLiebThirring.ActionProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.MatrixFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u148 u149 u150 u151 u152 u153 u154 u155 u156 u157

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
namespace SharpLiebThirring.ODEProof

lemma derivative_right_of_Icc {E : Type u149} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l r t : ℝ} {f : ℝ → E} {v : E} (ht : t ∈ Ico l r)
    (h : HasDerivWithinAt f v (Icc l r) t) : HasDerivWithinAt f v (Ici t) t :=
  h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

end SharpLiebThirring.ODEProof
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology
namespace SharpLiebThirring.MatrixFlow
lemma symConj_val {N : ℕ} (s : Fin N → ℝ) (A : Sym N) :
    (symConj s A).val = diagonal s * A.val * diagonal s := by
  ext i j; simp [diagonal_mul,mul_diagonal]
lemma norm_symConj {N : ℕ} (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) (A : Sym N) :
    ‖symConj s A‖ = ‖A‖ := by
  change ‖(symConj s A).val‖ = ‖A.val‖
  rw [symConj_val,CStarRing.norm_mul_mem_unitary _ (sign_diagonal_unitary s hs),
    CStarRing.norm_mem_unitary_mul _ (sign_diagonal_unitary s hs)]
lemma symConj_diag {N : ℕ} (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (k : Fin N → ℝ) : symConj s (symDiag k) = symDiag k := by
  apply Subtype.ext
  ext i j
  by_cases hij : i=j
  · subst j
    change s i * diagonal k i i * s i = diagonal k i i
    rw [diagonal_apply_eq]
    rcases hs i with h|h <;> rw [h] <;> ring
  · change s i * diagonal k i j * s j = diagonal k i j
    simp only [diagonal_apply_ne _ hij,mul_zero,zero_mul]

lemma matrix_norm_entry {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    |B i j| ≤ ‖B‖ := by
  let T : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N) B
  have h := T.le_opNorm (toLp 2 (Pi.single j (1 : ℝ)))
  have hh := PiLp.norm_apply_le (T (toLp 2 (Pi.single j (1 : ℝ)))) i
  simpa [T, Matrix.toEuclideanCLM_toLp, Matrix.l2_opNorm_toEuclideanCLM] using hh.trans h

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open Matrix Set MeasureTheory
variable {N : ℕ}

lemma gram_entry_bound (C : Matrix (Fin N) (Fin N) ℝ) {D : ℝ}
    (hD : ‖C * C.transpose‖ ≤ D) (i j : Fin N) : |C i j| ≤ max D 0 + 1 := by
  have hsq : (C i j)^2 ≤ (C*C.transpose) i i := by
    simpa only [mul_apply,transpose_apply,pow_two] using
      (Finset.single_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin N))) ↦ mul_self_nonneg (C i a))
        (Finset.mem_univ j))
  have hh := hsq.trans ((le_abs_self _).trans ((matrix_norm_entry _ i i).trans hD))
  have hm := le_max_left D 0
  have hn := le_max_right D 0
  have hs := sq_abs (C i j)
  nlinarith [abs_nonneg (C i j)]

end SharpLiebThirring.MatrixFlow

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FlowContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology

namespace SharpLiebThirring.ODEProof
open Set Metric Filter

/-- An upper barrier needs the derivative sign only strictly outside the barrier. -/
lemma upper_barrier {l r κ : ℝ} {h h' : ℝ → ℝ}
    (hd : ∀ t ∈ Icc l r, HasDerivWithinAt h (h' t) (Icc l r) t)
    (hi : h l ≤ κ)
    (hs : ∀ t ∈ Icc l r, κ < h t → h' t ≤ 0) :
    ∀ t ∈ Icc l r, h t ≤ κ := by
  intro t ht
  have hη : ∀ η > (0 : ℝ), h t ≤ κ + η*(1+t-l) := by
    intro η hη
    apply image_le_of_deriv_right_lt_deriv_boundary
      (HasDerivWithinAt.continuousOn hd)
      (fun x hx ↦ derivative_right_of_Icc hx (hd x (Ico_subset_Icc_self hx)))
      (B := fun x ↦ κ + η*(1+x-l)) (B' := fun _ ↦ η)
    · simpa only [add_sub_cancel_right,mul_one] using hi.trans (le_add_of_nonneg_right hη.le)
    · intro x
      simpa only [mul_one,id_eq] using
        (((hasDerivAt_id x).const_add 1).sub_const l |>.const_mul η |>.const_add κ)
    · intro x hx he
      have hpos : κ < h x := by rw [he]; have := hx.1; nlinarith
      exact (hs x (Ico_subset_Icc_self hx) hpos).trans_lt hη
    · exact ht
  have hc : ContinuousWithinAt (fun η : ℝ ↦ κ + η*(1+t-l)) (Ioi 0) 0 := by fun_prop
  have hh := continuousWithinAt_const.closure_le (by simp : (0 : ℝ) ∈ closure (Ioi 0)) hc hη
  simpa only [zero_mul,add_zero] using hh

lemma two_sided_barrier {l r κ : ℝ} {h h' : ℝ → ℝ}
    (hd : ∀ t ∈ Icc l r, HasDerivWithinAt h (h' t) (Icc l r) t)
    (hi : h l ≤ κ) (hf : -κ ≤ h r)
    (hs : ∀ t ∈ Icc l r, κ < |h t| → h' t ≤ 0) :
    ∀ t ∈ Icc l r, |h t| ≤ κ := by
  have hup := upper_barrier hd hi (fun t ht h ↦ hs t ht (h.trans_le (le_abs_self _)))
  have hrev : ∀ t ∈ Icc (-r) (-l), HasDerivWithinAt (fun t ↦ -h (-t)) (h' (-t))
      (Icc (-r) (-l)) t := by
    intro t ht
    have hm : -t ∈ Icc l r := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    have hh := (hd (-t) hm).comp t (hasDerivWithinAt_id t (Icc (-r) (-l)) |>.neg)
      (fun x hx ↦ ⟨by linarith [hx.2],by linarith [hx.1]⟩)
    convert! hh.neg using 1
    simp
  have hlo := upper_barrier hrev (by simpa only [neg_neg] using neg_le_neg hf)
    (fun t ht h ↦ hs (-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
      (h.trans_le (neg_le_abs _)))
  intro t ht
  apply abs_le.mpr
  constructor
  · have hh := hlo (-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
    simp only [neg_neg] at hh
    linarith
  · exact hup t ht

end SharpLiebThirring.ODEProof
namespace SharpLiebThirring.MatrixFlow
open Matrix Set ContinuationGap
variable {N : ℕ}

lemma isClosed_lower : IsClosed {C : Matrix (Fin N) (Fin N) ℝ | ∀ i j, i < j → C i j = 0} := by
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  exact isClosed_eq (by fun_prop) continuous_const

lemma compact_lower_box (R : ℝ) : IsCompact {C : LowerSpace N | ∀ i j, |C.val i j| ≤ R} := by
  have hh := (isClosed_lower (N := N)).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_Icc : IsCompact (Icc (fun _ _ : Fin N ↦ -R) (fun _ _ : Fin N ↦ R)))
  convert! hh using 1
  ext C
  change (∀ i j, |C.val i j| ≤ R) ↔ ((∀ i j, -R ≤ C.val i j) ∧ (∀ i j, C.val i j ≤ R))
  constructor
  · intro h
    exact ⟨fun i j ↦ (abs_le.mp (h i j)).1,fun i j ↦ (abs_le.mp (h i j)).2⟩
  · rintro ⟨hl,hu⟩ i j
    exact abs_le.mpr ⟨hl i j,hu i j⟩

end SharpLiebThirring.MatrixFlow

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FieldFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u158 u159 u160 u161 u162 u163 u164 u165

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology

noncomputable section
open Set Metric
open scoped NNReal
namespace SharpLiebThirring.ODEProof

lemma radialCutoff_nonneg {E : Type u159} [NormedAddCommGroup E] (R : ℝ) (x : E) :
    0 ≤ radialCutoff R x := le_max_left _ _
lemma radialCutoff_le_one {E : Type u160} [NormedAddCommGroup E] (R : ℝ) (x : E) :
    radialCutoff R x ≤ 1 := max_le zero_le_one (min_le_left _ _)
lemma radialCutoff_eq_one {E : Type u161} [NormedAddCommGroup E] {R : ℝ} {x : E}
    (hx : ‖x‖ ≤ R) : radialCutoff R x = 1 := by
  unfold radialCutoff
  rw [min_eq_left (by linarith),max_eq_right zero_le_one]
lemma radialCutoff_eq_zero {E : Type u162} [NormedAddCommGroup E] {R : ℝ} {x : E}
    (hx : R+1 ≤ ‖x‖) : radialCutoff R x = 0 := by
  unfold radialCutoff
  exact max_eq_left ((min_le_right _ _).trans (by linarith))
lemma radialCutoff_lipschitz {E : Type u163} [NormedAddCommGroup E] (R : ℝ) :
    LipschitzWith 1 (radialCutoff R : E → ℝ) := by
  have h : LipschitzWith 1 (fun x : E ↦ R+1-‖x‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,sub_sub_sub_cancel_left,Real.norm_eq_abs,abs_sub_comm,NNReal.coe_one,one_mul,dist_eq_norm]
      using abs_norm_sub_norm_le x y
  exact (h.const_min 1).const_max 0

lemma bounded_lipschitz_radial_cutoff {E : Type u164} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (M : E → E) (hM : LocallyLipschitz M) (R : ℝ) :
    ∃ K B : ℝ≥0, LipschitzWith K (fun x ↦ radialCutoff R x • M x) ∧
      ∀ x, ‖radialCutoff R x • M x‖ ≤ B := by
  obtain ⟨L,hL⟩ := hM.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : E) (R+2))
  obtain ⟨b,hb⟩ := (isCompact_closedBall (0 : E) (R+2)).bddAbove_image
    hM.continuous.norm.continuousOn
  let B : ℝ≥0 := ⟨max b 0, le_max_right _ _⟩
  have hB (x : E) (hx : ‖x‖ ≤ R+2) : ‖M x‖ ≤ B :=
    (hb (mem_image_of_mem _ (by simpa only [mem_closedBall,dist_zero_right] using hx))).trans
      (le_max_left b 0)
  let F := fun x ↦ radialCutoff R x • M x
  have hzero (x : E) (hx : R+1 ≤ ‖x‖) : F x = 0 := by
    simp only [F,radialCutoff_eq_zero hx,zero_smul]
  have hbound (x : E) : ‖F x‖ ≤ B := by
    by_cases hx : ‖x‖ ≤ R+2
    · dsimp only [F]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (radialCutoff_nonneg R x)]
      exact (mul_le_mul_of_nonneg_right (radialCutoff_le_one R x) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hB x hx)
    · rw [hzero x (by linarith [lt_of_not_ge hx]),norm_zero]; exact B.prop
  have hlocal : LipschitzOnWith (L+B) F (closedBall (0 : E) (R+2)) := by
    apply lipschitzOnWith_iff_norm_sub_le.mpr
    intro x hx y hy
    have hyd : ‖y‖ ≤ R+2 := by simpa only [mem_closedBall,dist_zero_right] using hy
    have hid : F x - F y = radialCutoff R x • (M x-M y) +
        (radialCutoff R x-radialCutoff R y) • M y := by dsimp [F]; module
    rw [hid]
    apply (norm_add_le _ _).trans
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (radialCutoff_nonneg R x)]
    have hh := hL.dist_le_mul x hx y hy
    rw [dist_eq_norm,dist_eq_norm] at hh
    have hχ := (radialCutoff_lipschitz (E := E) R).dist_le_mul x y
    simp only [dist_eq_norm,Real.norm_eq_abs,NNReal.coe_one,one_mul] at hχ
    calc
      _ ≤ 1 * ((L : ℝ)*‖x-y‖) + ‖x-y‖ * (B : ℝ) := by
        exact add_le_add
          (mul_le_mul (radialCutoff_le_one R x) hh (norm_nonneg _) zero_le_one)
          (mul_le_mul hχ (hB y hyd) (norm_nonneg _) (norm_nonneg _))
      _ = _ := by push_cast; ring
  have hfar (x y : E) (hx : ‖x‖ < R+1) (hy : R+2 < ‖y‖) :
      ‖F x - F y‖ ≤ (L+B : ℝ≥0) * ‖x-y‖ := by
    rw [hzero y (by linarith),sub_zero]
    have hd : 1 ≤ ‖x-y‖ := by
      have hh := norm_le_norm_add_norm_sub x y
      linarith
    calc
      _ ≤ (B : ℝ) := hbound x
      _ ≤ (L : ℝ) + B := le_add_of_nonneg_left L.prop
      _ ≤ ((L : ℝ) + B) * ‖x-y‖ := le_mul_of_one_le_right (add_nonneg L.prop B.prop) hd
      _ = _ := rfl
  refine ⟨L+B,B,?_,hbound⟩
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  change ‖F x - F y‖ ≤ (L+B : ℝ≥0) * ‖x-y‖
  by_cases hx : ‖x‖ ≤ R+2
  · by_cases hy : ‖y‖ ≤ R+2
    · exact lipschitzOnWith_iff_norm_sub_le.mp hlocal
        (by simpa only [mem_closedBall,dist_zero_right] using hx)
        (by simpa only [mem_closedBall,dist_zero_right] using hy)
    · by_cases hx' : R+1 ≤ ‖x‖
      · rw [hzero x hx',hzero y (by linarith [lt_of_not_ge hy]),sub_self,norm_zero]
        positivity
      · exact hfar x y (lt_of_not_ge hx') (lt_of_not_ge hy)
  · by_cases hy : R+1 ≤ ‖y‖
    · rw [hzero x (by linarith [lt_of_not_ge hx]),hzero y hy,sub_self,norm_zero]; positivity
    · simpa only [norm_sub_rev] using hfar y x (lt_of_not_ge hy) (lt_of_not_ge hx)

end SharpLiebThirring.ODEProof
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace SharpLiebThirring.MatrixFlow
variable {n : Type u165} [Fintype n] [DecidableEq n]

lemma cfc_isolated_row {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n)
    (hi : ∀ j, i ≠ j → A i j = 0) (f : ℝ → ℝ) (j : n) :
    cfc f A i j = f (A i i) * (1 : Matrix n n ℝ) i j := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  have hU : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hAU : A * U = U * diagonal hA.eigenvalues := by
    conv_lhs => rw [hA.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    change U * diagonal hA.eigenvalues * star U * U = _
    rw [mul_assoc,mul_assoc,Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.prop,mul_one]
  have hspec (l : n) : U i l = 0 ∨ hA.eigenvalues l = A i i := by
    have he := congrFun (congrFun hAU i) l
    rw [mul_diagonal] at he
    have hr : (A * U) i l = A i i * U i l := by
      rw [mul_apply]
      apply Finset.sum_eq_single i
      · intro b _ hbi
        rw [hi b (Ne.symm hbi),zero_mul]
      · simp
    rw [hr] at he
    by_cases hz : U i l = 0
    · exact Or.inl hz
    · exact Or.inr (mul_right_cancel₀ hz (by nlinarith : hA.eigenvalues l * U i l = A i i * U i l))
  rw [hA.cfc_eq,IsHermitian.cfc,Unitary.conjStarAlgAut_apply]
  change (U * diagonal (f ∘ hA.eigenvalues) * star U) i j = _
  rw [← hU]
  conv_rhs => rw [Matrix.mul_apply,Finset.mul_sum]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [mul_diagonal]
  rcases hspec l with h|h
  · simp only [h,zero_mul,mul_zero]
  · simp only [Function.comp_apply,h]
    ring

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open MatrixProof ScalarProof Matrix
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

lemma sourceField_locallyLipschitz {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ) :
    LocallyLipschitz (sourceField σ δ hσ hδ k) := by
  have h := (realPartCLM.lipschitz.locallyLipschitz).comp
    ((hermitianField_locallyLipschitz hσ hδ (realK2SelfAdjoint k).prop).comp
      realHermitianComplexifyCLM.lipschitz.locallyLipschitz)
  have hh : LocallyLipschitz (fun A : Sym N ↦ matrixField σ δ k A.val) := by
    convert! h using 1
    funext A
    exact matrixField_eq_realPart hσ hδ k A.prop
  intro A
  obtain ⟨L,s,hs,hL⟩ := hh A
  refine ⟨L,s,hs,?_⟩
  intro x hx y hy
  exact hL hx hy

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open MatrixProof ScalarProof Matrix MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

lemma complexify_conj (U : unitary (Matrix (Fin N) (Fin N) ℝ))
    (A : Matrix (Fin N) (Fin N) ℝ) :
    complexify (Unitary.conjStarAlgAut ℝ _ U A) =
      Unitary.conjStarAlgAut ℂ _ (complexUnitary U) (complexify A) := by
  simp only [Unitary.conjStarAlgAut_apply,map_mul,map_star]
  rfl

lemma complexify_symConj (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) (A : Sym N) :
    complexify (symConj s A).val = Unitary.conjStarAlgAut ℂ _
      (complexUnitary ⟨diagonal s,sign_diagonal_unitary s hs⟩) (complexify A.val) := by
  rw [← complexify_conj]
  congr 1
  rw [Unitary.conjStarAlgAut_apply,symConj_val]
  congr 1
  exact (isHermitian_diagonal s).symm

lemma sourceField_equivariant {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ)
    (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) (A : Sym N) :
    sourceField σ δ hσ hδ k (symConj s A) = symConj s (sourceField σ δ hσ hδ k A) := by
  let U := complexUnitary ⟨diagonal s,sign_diagonal_unitary s hs⟩
  have hK := complexify_symConj s hs (symDiag (fun i ↦ k i ^ 2))
  rw [symConj_diag s hs] at hK
  have hh := hermitianField_conj hσ hδ (realK2SelfAdjoint k).prop (complexify_hermitian A.prop) U
  change complexify (diagonal (fun i ↦ k i^2)) = Unitary.conjStarAlgAut ℂ _ U (complexify (diagonal (fun i ↦ k i^2))) at hK
  change hermitianField σ δ (Unitary.conjStarAlgAut ℂ _ U (complexify (diagonal (fun i ↦ k i^2)))) _ = Unitary.conjStarAlgAut ℂ _ U (hermitianField σ δ (complexify (diagonal (fun i ↦ k i^2))) (complexify A.val)) at hh
  rw [← hK,← complexify_symConj s hs A,← complexify_matrixField hσ hδ k (symConj s A).prop,
    ← complexify_matrixField hσ hδ k A.prop] at hh
  have hf := complexify_symConj s hs (sourceField σ δ hσ hδ k A)
  change complexify (symConj s (sourceField σ δ hσ hδ k A)).val = _ at hf
  change complexify (symConj s (sourceField σ δ hσ hδ k A)).val =
    Unitary.conjStarAlgAut ℂ _ U (complexify (matrixField σ δ k A.val)) at hf
  rw [← hf] at hh
  apply Subtype.ext
  simpa only [realPartCLM_complexify,sourceField] using congrArg realPartCLM hh

lemma matrixField_tendsto {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    Tendsto (truncatedField σ δ k A) atTop (𝓝 (matrixField σ δ k A)) := by
  have ht : Tendsto (fun R ↦ complexify (truncatedField σ δ k A R)) atTop
      (𝓝 (hermitianField σ δ (complexify (diagonal (fun i ↦ k i^2))) (complexify A))) := by
    have h := hermitianField_cutoff_limit hσ hδ (realK2SelfAdjoint k).prop (complexify_hermitian hA)
    change Tendsto (fun R ↦ fieldNormalization σ • ∫ s in -R..R, fieldIntegrand σ δ (complexify (diagonal (fun i ↦ k i^2))) (complexify A) s) atTop (𝓝 _) at h
    simpa only [complexify_truncatedField hδ k hA,realK2SelfAdjoint] using h
  have hh := realPartCLM.continuous.continuousAt.tendsto.comp ht
  rw [matrixField_eq_realPart hσ hδ k hA]
  change Tendsto (fun R ↦ realPartCLM (complexify (truncatedField σ δ k A R))) atTop (𝓝 _) at hh
  simpa only [realPartCLM_complexify] using hh

lemma matrixField_isolated_coordinate {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ)
    (A : Sym N) (i : Fin N) (hi : ∀ j, i ≠ j → A.val i j = 0) :
    (sourceField σ δ hσ hδ k A).val i i = scalarMu σ δ (k i ^ 2 - A.val i i ^ 2) := by
  have hx (s : ℝ) : (cfc (regularizedPrimitive σ δ) (matrixX k A.val s)) i i =
      regularizedPrimitive σ δ ((s-A.val i i)^2+(k i^2-A.val i i^2)) := by
    rw [cfc_isolated_row (matrixX_hermitian k A.prop s) i (fun j hij ↦ ?_) _ i]
    · simp only [one_apply_eq,mul_one]
      congr 1
      simp only [matrixX,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
        diagonal_apply_eq,one_apply_eq,mul_one]
      ring
    · simp only [matrixX,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
        diagonal_apply_ne _ hij,one_apply_ne hij,hi j hij,mul_zero,sub_zero,add_zero]
  have hc : Continuous (fun s : ℝ ↦ cfc (regularizedPrimitive σ δ) (matrixX k A.val s) -
      regularizedPrimitive σ δ (s^2) • (1 : Matrix (Fin N) (Fin N) ℝ)) := by
    have hx : Continuous (fun s ↦ cfc (regularizedPrimitive σ δ) (matrixX k A.val s)) :=
      Continuous.cfc_of_mem_nhdsSet (s := Set.univ) _ Filter.univ_mem
        (by unfold matrixX; fun_prop) (matrixX_hermitian k A.prop)
        (primitive_differentiable σ hδ).continuous.continuousOn
    exact hx.sub (((primitive_differentiable σ hδ).continuous.comp (continuous_pow 2)).smul continuous_const)
  have he (R : ℝ) : truncatedField σ δ k A.val R i i = fieldNormalization σ * ∫ s in -R..R,
      regularizedPrimitive σ δ ((s-A.val i i)^2+(k i^2-A.val i i^2)) - regularizedPrimitive σ δ (s^2) := by
    have h := (matrixEntry i i).intervalIntegral_comp_comm (μ := volume) (hc.intervalIntegrable (-R) R)
    simp only [matrixEntry_apply] at h
    rw [truncatedField,Matrix.smul_apply,smul_eq_mul,← h]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,one_apply_eq,mul_one,hx]
  have hl := (matrixEntry i i).continuous.continuousAt.tendsto.comp (matrixField_tendsto hσ hδ k A.prop)
  change Tendsto (fun R ↦ truncatedField σ δ k A.val R i i) atTop (𝓝 _) at hl
  simp only [he] at hl
  exact tendsto_nhds_unique hl (primitive_shift_limit hσ hδ (k i^2-A.val i i^2) (A.val i i))

lemma coordinate_mu_locallyLipschitz {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) (i : Fin N) : LocallyLipschitz (fun x : ℝ ↦ scalarMu σ δ (k i ^ 2-x^2)) := by
  have hh := (symEntry i i).lipschitz.locallyLipschitz.comp
    ((sourceField_locallyLipschitz hσ hδ k).comp scalarDiag.lipschitz.locallyLipschitz)
  convert! hh using 1
  funext x
  change _ = matrixField σ δ k (diagonal (fun _ ↦ x)) i i
  rw [matrixField_diagonal hσ hδ,diagonal_apply_eq]

end SharpLiebThirring.MatrixFlow

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.ConnectingPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
open Set Metric
open scoped NNReal
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace SharpLiebThirring.MatrixFlow
open ODEProof MatrixProof ScalarProof Matrix Set
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
variable {N : ℕ}

lemma state_diagonal_le (φ : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ)
    (hφ : ∀ A, A.PosSemidef → 0 ≤ φ A) (hφ₁ : φ 1 = 1)
    (f : Fin N → ℝ) (b : ℝ) (hf : ∀ i, f i ≤ b) :
    φ (complexify (diagonal f)) ≤ b := by
  have hp := hφ (diagonal (fun i ↦ ((b-f i : ℝ) : ℂ)))
    (diagonal_real_posSemidef _ (fun i ↦ sub_nonneg.mpr (hf i)))
  have he : diagonal (fun i ↦ ((b-f i : ℝ) : ℂ)) = b • (1 : Matrix (Fin N) (Fin N) ℂ) - complexify (diagonal f) := by
    rw [complexify_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j
      simp
    · simp [diagonal_apply_ne _ hij,one_apply_ne hij]
  rw [he,map_sub,map_smul,hφ₁,smul_eq_mul,mul_one] at hp
  linarith

lemma sourceField_state_nonpos {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) (A : Sym N)
    (φ : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ)
    (hφ : ∀ A, A.PosSemidef → 0 ≤ φ A) (hφ₁ : φ 1 = 1)
    (h : ‖k‖ < |φ (complexify A.val)|) :
    φ (complexify (sourceField σ δ hσ₁ hδ k A).val) ≤ 0 := by
  have hC : φ (complexify (diagonal (fun i ↦ k i^2))) ≤ ‖k‖^2 :=
    state_diagonal_le φ hφ hφ₁ _ _ (fun i ↦ by
      have hh : |k i| ≤ ‖k‖ := norm_le_pi_norm k i
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hh)
  have hj := hermitianField_state_jensen hσ₀ hσ₁ hδ φ hφ hφ₁
    (realK2SelfAdjoint k).prop (complexify_hermitian A.prop)
  change φ (hermitianField σ δ (complexify (diagonal (fun i ↦ k i^2))) (complexify A.val)) ≤ _ at hj
  rw [← complexify_matrixField hσ₁ hδ k A.prop] at hj
  apply hj.trans
  have hz : φ (complexify (diagonal (fun i ↦ k i^2))) - (φ (complexify A.val))^2 ≤ 0 := by
    nlinarith [sq_abs (φ (complexify A.val)),norm_nonneg k]
  exact (mu_strictMono hσ₀ hσ₁ hδ).monotone hz |>.trans_eq (mu_zero σ δ)

lemma source_path_state_barrier {σ δ ε l r : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (hε : 0 < ε) (k : Fin N → ℝ) (a : ℝ → Fin N → ℝ)
    (q : Sym N → ℝ) (hq : ∀ A, 0 ≤ q A) (X : ℝ → Sym N)
    (hXi : X l = symDiag k) (hXf : X r = -symDiag k)
    (hXd : ∀ t ∈ Icc l r, HasDerivWithinAt X
      (ε⁻¹ • (q (X t) • sourceField σ δ hσ₁ hδ k (X t) - symOuter (a t))) (Icc l r) t)
    (φ : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ)
    (hφ : ∀ A, A.PosSemidef → 0 ≤ φ A) (hφ₁ : φ 1 = 1) :
    ∀ t ∈ Icc l r, |φ (complexify (X t).val)| ≤ ‖k‖ := by
  let ψ := φ.comp (complexifyCLM.comp symInclude.toContinuousLinearMap)
  have hψ (A : Sym N) : ψ A = φ (complexify A.val) := rfl
  have hK : ψ (symDiag k) ≤ ‖k‖ := state_diagonal_le φ hφ hφ₁ _ _
    (fun i ↦ (le_abs_self _).trans (norm_le_pi_norm k i))
  apply two_sided_barrier (h := fun t ↦ ψ (X t))
    (h' := fun t ↦ ψ (ε⁻¹ • (q (X t) • sourceField σ δ hσ₁ hδ k (X t) - symOuter (a t))))
  · intro t ht
    exact ψ.hasFDerivAt.comp_hasDerivWithinAt t (hXd t ht)
  · rw [hXi]; exact hK
  · rw [hXf,map_neg]; exact neg_le_neg hK
  · intro t ht h
    have hF := sourceField_state_nonpos hσ₀ hσ₁ hδ k (X t) φ hφ hφ₁ h
    have hA : 0 ≤ ψ (symOuter (a t)) := by
      change 0 ≤ φ (complexify (vecMulVec (a t) (a t)))
      rw [complexify_vecMulVec]
      exact hφ _ (posSemidef_vecMulVec_self_star _)
    rw [map_smul,map_sub,map_smul,smul_eq_mul,smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hε.le)
      (sub_nonpos.mpr (le_trans (mul_nonpos_of_nonneg_of_nonpos (hq _) hF) hA))

lemma sym_norm_le_of_states (A : Sym N) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ (φ : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ),
      (∀ B, B.PosSemidef → 0 ≤ φ B) → φ 1 = 1 → |φ (complexify A.val)| ≤ R) :
    ‖A‖ ≤ R := by
  have hA : A.val.IsHermitian := A.prop
  have he (i : Fin N) : |hA.eigenvalues i| ≤ R := by
    have hh := h (unitaryState (complexUnitary (star hA.eigenvectorUnitary)) i)
      (fun B hB ↦ unitaryState_positive _ _ hB) (unitaryState_one _ _)
    rw [unitaryState_apply,← complexify_conj,hA.conjStarAlgAut_star_eigenvectorUnitary] at hh
    simpa only [complexify_apply,Function.comp_apply,RCLike.ofReal_real_eq_id,id_eq,
      diagonal_apply_eq,Complex.ofReal_re] using hh
  have hd := hA.conjStarAlgAut_star_eigenvectorUnitary
  have hn := congrArg (fun B : Matrix (Fin N) (Fin N) ℝ ↦ ‖B‖) hd
  simp only [Unitary.conjStarAlgAut_apply,CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul,← Unitary.coe_star,Matrix.l2_opNorm_diagonal,
    RCLike.ofReal_real_eq_id,Function.id_comp] at hn
  change ‖A.val‖ ≤ R
  rw [hn]
  exact (pi_norm_le_iff_of_nonneg hR).mpr he

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open ODEProof MatrixProof ScalarProof Matrix Set ContinuationGap
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The connecting path, with one coefficient box for all small penalties.
The radial cutoff has been removed by the two endpoint barriers. -/
lemma source_connecting_path {σ δ l r : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (hlr : l ≤ r) (k : Fin N → ℝ) (hk : ∀ i, 0 < k i)
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (ho : ∀ i j, (∫ t in l..r, u t i * u t j) = if i=j then 1 else 0) :
    ∃ R : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (C : LowerSpace N) (X : ℝ → Sym N),
        (∀ i j, |C.val i j| ≤ R) ∧ X l = symDiag k ∧ X r = -symDiag k ∧
        (∀ t ∈ Icc l r, ‖X t‖ ≤ ‖k‖) ∧
        (∀ t ∈ Icc l r, HasDerivWithinAt X
          (ε⁻¹ • (sourceField σ δ hσ₁ hδ k (X t) - symOuter (C.val *ᵥ u t))) (Icc l r) t) := by
  let χ : Sym N → ℝ := radialCutoff ‖k‖
  let M := fun A ↦ χ A • sourceField σ δ hσ₁ hδ k A
  obtain ⟨L,B,hL,hB⟩ := bounded_lipschitz_radial_cutoff
    (sourceField σ δ hσ₁ hδ k) (sourceField_locallyLipschitz hσ₁ hδ k) ‖k‖
  refine ⟨max (2*‖k‖+(r-l)*B) 0+1,?_⟩
  intro ε hε hε₁
  have hχ (A : Sym N) : |χ A| ≤ (1 : ℝ≥0) := by
    rw [abs_of_nonneg (radialCutoff_nonneg _ _)]
    exact radialCutoff_le_one _ _
  have hg (i : Fin N) : LocallyLipschitz (fun x ↦ scalarMu σ δ (k i^2-x^2)) :=
    coordinate_mu_locallyLipschitz hσ₁ hδ k i
  have hc (i : Fin N) (A : Sym N) (hi : ∀ j, i ≠ j → A.val i j = 0) :
      (M A).val i i = χ A * scalarMu σ δ (k i^2-A.val i i^2) := by
    change χ A * (sourceField σ δ hσ₁ hδ k A).val i i = _
    rw [matrixField_isolated_coordinate hσ₁ hδ k A i hi]
  have he (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) (A : Sym N) :
      M (symConj s A) = symConj s (M A) := by
    dsimp only [M]
    rw [sourceField_equivariant hσ₁ hδ k s hs,map_smul]
    congr 1
    unfold χ radialCutoff
    rw [norm_symConj s hs]
  obtain ⟨C,X,hXi,hXf,hXd,hC⟩ := terminal_matching hlr hε M L B 1 hL hB χ hχ
    (fun i x ↦ scalarMu σ δ (k i^2-x^2)) hg k hk
    (fun i ↦ by simp only [sub_self,mu_zero]) hc he u hu ho
  have hX (t : ℝ) (ht : t ∈ Icc l r) : ‖X t‖ ≤ ‖k‖ := by
    apply sym_norm_le_of_states (X t) (norm_nonneg _)
    intro φ hφ hφ₁
    exact source_path_state_barrier hσ₀ hσ₁ hδ hε k (fun t ↦ C.val *ᵥ u t) χ
      (radialCutoff_nonneg _) X hXi hXf hXd φ hφ hφ₁ t ht
  refine ⟨C,X,?_,hXi,hXf,hX,?_⟩
  · apply gram_entry_bound
    apply hC.trans
    rw [abs_of_pos hε]
    nlinarith [norm_nonneg k]
  · intro t ht
    have hh := hXd t ht
    change HasDerivWithinAt X (ε⁻¹ • (χ (X t) • sourceField σ δ hσ₁ hδ k (X t) - _)) _ t at hh
    rw [show χ (X t) = 1 from radialCutoff_eq_one (hX t ht),one_smul] at hh
    exact hh

end SharpLiebThirring.MatrixFlow

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.IntervalAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
open Set Metric
open scoped NNReal
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof MatrixFlow MeasureTheory Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

lemma actionDensity_continuous {σ : ℝ} (hσ : 0 < σ) (k : Fin N → ℝ) :
    Continuous (fun z : (Fin N → ℝ) × (Fin N → ℝ) ↦ actionDensity σ k z.1 z.2) := by
  unfold actionDensity
  apply Continuous.sub
  · fun_prop
  · exact (by fun_prop : Continuous (fun z : (Fin N → ℝ) × (Fin N → ℝ) ↦ ∑ i, z.1 i^2)).rpow_const
      (fun _ ↦ Or.inr (by positivity))

lemma penalized_action_integral {σ δ ε l r η : ℝ}
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ) (hε : 0 < ε) (hlr : l ≤ r)
    (k : Fin N → ℝ) (a v : ℝ → Fin N → ℝ)
    (ha : ContinuousOn a (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (had : ∀ t ∈ Ioo l r, ∀ i, HasDerivAt (fun t ↦ a t i) (v t i) t)
    (hal : a l = 0) (har : a r = 0) (X : ℝ → Sym N)
    (hXi : X l = symDiag k) (hXf : X r = -symDiag k)
    (hXd : ∀ t ∈ Icc l r, HasDerivWithinAt X
      (ε⁻¹ • (sourceField σ δ hσ₁ hδ k (X t) - symOuter (a t))) (Icc l r) t)
    (hp : ∀ t ∈ Icc l r, actionDefect σ k (X t,a t) - constraintDefect σ δ k (X t,a t)/ε ≤ η) :
    fieldPrimitive σ δ k (-diagonal k) - fieldPrimitive σ δ k (diagonal k) ≤
      (∫ t in l..r, actionDensity σ k (a t) (v t)) + (r-l)*η := by
  have hX := HasDerivWithinAt.continuousOn hXd
  have hXval := continuous_subtype_val.comp_continuousOn hX
  let G := fun t ↦ fieldPrimitive σ δ k (X t) + ∑ i, a t i * ((X t).val *ᵥ a t) i
  let G' := fun t ↦ 2*(∑ i, v t i * ((X t).val *ᵥ a t) i) - constraintDefect σ δ k (X t,a t)/ε
  have hJ : Continuous (fun A : Sym N ↦ fieldPrimitive σ δ k A) :=
    continuous_iff_continuousAt.mpr (fun A ↦ (fieldPrimitive_hasFDerivAt hσ₁ hδ k A).continuousAt)
  have hMV : ContinuousOn (fun t ↦ (X t).val *ᵥ a t) (Icc l r) :=
    (show Continuous (fun z : Matrix (Fin N) (Fin N) ℝ × (Fin N → ℝ) ↦ z.1 *ᵥ z.2)
      by fun_prop).comp_continuousOn (hXval.prodMk ha)
  have hdot : Continuous (fun z : (Fin N → ℝ) × (Fin N → ℝ) ↦ ∑ i, z.1 i * z.2 i) := by
    fun_prop
  have hG : ContinuousOn G (Icc l r) :=
    (hJ.comp_continuousOn hX).add (hdot.comp_continuousOn (ha.prodMk hMV))
  have hG' : ContinuousOn G' (Icc l r) :=
    ((hdot.comp_continuousOn (hv.prodMk hMV)).const_mul 2).sub
      (((constraintDefect_continuous hσ₁ hδ k).comp_continuousOn (hX.prodMk ha)).div_const ε)
  have hd (t : ℝ) (ht : t ∈ Ioo l r) : HasDerivAt G (G' t) t := by
    apply action_ode_identity hσ₁ hδ hε k (had t ht)
      ((hXd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    change ε • (ε⁻¹ • (matrixField σ δ k (X t).val - vecMulVec (a t) (a t))) = _
    rw [smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr hG hd
    (hG'.intervalIntegrable_of_Icc (μ := volume) hlr)
  have hlim : G r - G l = fieldPrimitive σ δ k (-diagonal k) - fieldPrimitive σ δ k (diagonal k) := by
    simp only [G,har,hal,hXi,hXf,Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero]
    rfl
  rw [hlim] at hi
  have hec := (actionDensity_continuous hσ₀ k).comp_continuousOn (ha.prodMk hv)
  have hbound := intervalIntegral.integral_mono_on hlr
    (hG'.intervalIntegrable_of_Icc (μ := volume) hlr)
    ((hec.add (continuousOn_const (c := η))).intervalIntegrable_of_Icc (μ := volume) hlr)
    (fun t ht ↦ (action_penalty_pointwise k (X t) (a t) (v t)).trans
      (add_le_add (le_refl (actionDensity σ k (a t) (v t))) (hp t ht)))
  change (∫ t in l..r, G' t) ≤ (∫ t in l..r, actionDensity σ k (a t) (v t) + η) at hbound
  change ContinuousOn (fun t ↦ actionDensity σ k (a t) (v t)) (Icc l r) at hec
  rw [hi,intervalIntegral.integral_add (hec.intervalIntegrable_of_Icc (μ := volume) hlr)
    (intervalIntegrable_const),intervalIntegral.integral_const,smul_eq_mul] at hbound
  exact hbound

end SharpLiebThirring.ActionProof
namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof MatrixFlow MeasureTheory Set Filter ContinuationGap
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

lemma mulVec_hasDerivAt (C : Matrix (Fin N) (Fin N) ℝ)
    {u v : ℝ → Fin N → ℝ} {t : ℝ} (hu : ∀ i, HasDerivAt (fun t ↦ u t i) (v t i) t) (i : Fin N) :
    HasDerivAt (fun t ↦ (C *ᵥ u t) i) ((C *ᵥ v t) i) t := by
  simpa only [mulVec,dotProduct] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ (hu j).const_mul (C i j))

lemma compact_amplitudes {l r R : ℝ} {u : ℝ → Fin N → ℝ}
    (hu : ContinuousOn u (Icc l r)) :
    IsCompact ((fun z : LowerSpace N × ℝ ↦ z.1.val *ᵥ u z.2) ''
      ({C : LowerSpace N | ∀ i j, |C.val i j| ≤ R} ×ˢ Icc l r)) := by
  apply ((compact_lower_box R).prod isCompact_Icc).image_of_continuousOn
  have hu' : ContinuousOn (fun z : LowerSpace N × ℝ ↦ u z.2)
      ({C : LowerSpace N | ∀ i j, |C.val i j| ≤ R} ×ˢ Icc l r) :=
    hu.comp continuousOn_snd (fun _ hz ↦ hz.2)
  have hC : Continuous (fun z : LowerSpace N × ℝ ↦ z.1.val) := continuous_subtype_val.comp continuous_fst
  exact (show Continuous (fun z : Matrix (Fin N) (Fin N) ℝ × (Fin N → ℝ) ↦ z.1 *ᵥ z.2)
    by fun_prop).comp_continuousOn (hC.continuousOn.prodMk hu')

/-- An arbitrary finite upper bound on all triangular actions bounds the endpoint
jump. This avoids imposing a finiteness convention on a real-valued supremum. -/
lemma regularized_action_upper_test_oai {σ δ l r S : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (hlr : l ≤ r) (k : Fin N → ℝ) (hk : ∀ i, 0 < k i)
    (u v : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (hud : ∀ t ∈ Ioo l r, ∀ i, HasDerivAt (fun t ↦ u t i) (v t i) t)
    (hul : u l = 0) (hur : u r = 0)
    (ho : ∀ i j, (∫ t in l..r, u t i*u t j) = if i=j then 1 else 0)
    (hS : ∀ C : LowerSpace N,
      (∫ t in l..r, actionDensity σ k (C.val *ᵥ u t) (C.val *ᵥ v t)) ≤ S) :
    fieldPrimitive σ δ k (-diagonal k) - fieldPrimitive σ δ k (diagonal k) ≤ S := by
  obtain ⟨R,hpath⟩ := source_connecting_path hσ₀ hσ₁ hδ hlr k hk u hu ho
  let A := (fun z : LowerSpace N × ℝ ↦ z.1.val *ᵥ u z.2) ''
    ({C : LowerSpace N | ∀ i j, |C.val i j| ≤ R} ×ˢ Icc l r)
  let K : Set (Sym N × (Fin N → ℝ)) := Metric.closedBall 0 ‖k‖ ×ˢ A
  have hK : IsCompact K := (isCompact_closedBall (0 : Sym N) ‖k‖).prod (compact_amplitudes hu)
  have hη (η : ℝ) (hη : 0 < η) :
      fieldPrimitive σ δ k (-diagonal k) - fieldPrimitive σ δ k (diagonal k) ≤ S+(r-l)*η := by
    obtain ⟨ε₀,hε₀,hpen⟩ := matrix_compact_penalty hσ₀ hσ₁ hδ k hK hη
    let ε := min ε₀ 1
    have hε : 0 < ε := lt_min hε₀ zero_lt_one
    obtain ⟨C,X,hC,hXi,hXf,hX,hXd⟩ := hpath ε hε (min_le_right _ _)
    have ha : ContinuousOn (fun t ↦ C.val *ᵥ u t) (Icc l r) :=
      (show Continuous (fun a : Fin N → ℝ ↦ C.val *ᵥ a) by fun_prop).comp_continuousOn hu
    have ha' : ContinuousOn (fun t ↦ C.val *ᵥ v t) (Icc l r) :=
      (show Continuous (fun a : Fin N → ℝ ↦ C.val *ᵥ a) by fun_prop).comp_continuousOn hv
    have hh := penalized_action_integral hσ₀ hσ₁ hδ hε hlr k
      (fun t ↦ C.val *ᵥ u t) (fun t ↦ C.val *ᵥ v t) ha ha'
      (fun t ht ↦ mulVec_hasDerivAt C.val (hud t ht))
      (by rw [hul,mulVec_zero]) (by rw [hur,mulVec_zero]) X hXi hXf hXd
      (fun t ht ↦ hpen ε hε (min_le_left _ _) (X t,C.val *ᵥ u t)
        ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hX t ht,
          ⟨(C,t),⟨hC,ht⟩,rfl⟩⟩)
    exact hh.trans (add_le_add (hS C) (le_refl _))
  have ht : Tendsto (fun η : ℝ ↦ S+(r-l)*η) (𝓝[>] 0) (𝓝 S) := by
    have hc : Continuous (fun η : ℝ ↦ S+(r-l)*η) := by fun_prop
    simpa only [mul_zero,add_zero] using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with η h using hη η h)

end SharpLiebThirring.ActionProof

end

end

end

end

end

end

end

end OAI
end

theorem solution : type_of% @OAI.SharpLiebThirring.ActionProof.regularized_action_upper_test_oai := @OAI.SharpLiebThirring.ActionProof.regularized_action_upper_test_oai
