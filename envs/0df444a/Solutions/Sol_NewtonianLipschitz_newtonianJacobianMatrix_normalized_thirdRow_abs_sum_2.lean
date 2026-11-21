-- Prove2me | solution 2 for NewtonianLipschitz.newtonianJacobianMatrix_normalized_thirdRow_abs_sum
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:52:32.946318+00:00
-- url     : https://prove2.me/submissions/adfe673b-19b4-4551-a476-36ffbd5c7d0d

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz


theorem solution
    (μ u v : ℝ) (hμ : 0 ≤ μ)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) :
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector u v) 2 j|) =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        lateralRowNumerator v u := by
  have hc : 0 ≤ μ / euclideanRadius (normalizedVector u v) ^ 5 := by
    apply div_nonneg hμ
    unfold euclideanRadius
    positivity
  have hr : euclideanRadius (normalizedVector u v) ^ 2 = 1 + u ^ 2 + v ^ 2 := by
    unfold euclideanRadius
    norm_num [normalizedVector]
    apply Real.sq_sqrt
    positivity
  simp only [Fin.sum_univ_three, newtonianJacobianMatrix, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul, Matrix.one_apply]
  set R := euclideanRadius (normalizedVector u v)
  have h0 : normalizedVector u v (0 : Fin 3) = 1 := rfl
  have h1 : normalizedVector u v (1 : Fin 3) = u := rfl
  have h2 : normalizedVector u v (2 : Fin 3) = v := rfl
  norm_num [h0, h1, h2, Fin.ext_iff]
  simp only [hr, lateralRowNumerator, abs_mul, abs_of_nonneg hc, abs_of_nonneg hu0,
    abs_of_nonneg hv0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  ring_nf
