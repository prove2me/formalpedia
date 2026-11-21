-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_entry_abs_coordinateAbs
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:39:33.289525+00:00
-- url     : https://prove2.me/submissions/5f93b076-0744-42a5-b4a1-2ed316c976b4

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

private theorem numerator_abs (x : Vec3) (i j : Fin 3) :
    |3 * coordinateAbs x i * coordinateAbs x j - euclideanRadius x ^ 2 * (if i = j then 1 else 0)| =
    |3 * x i * x j - euclideanRadius x ^ 2 * (if i = j then 1 else 0)| := by
  by_cases hij : i = j
  · subst j
    have he : 3 * |x i| * |x i| = 3 * x i * x i := by nlinarith [sq_abs (x i)]
    simp [coordinateAbs, he]
  · simp [coordinateAbs, hij, abs_mul]
private theorem entry_abs (μ : ℝ) (x : Vec3) (i j : Fin 3) :
    |newtonianJacobianMatrix μ (coordinateAbs x) i j| = |newtonianJacobianMatrix μ x i j| := by
  have hr : euclideanRadius (coordinateAbs x) = euclideanRadius x := by
    simp [euclideanRadius, coordinateAbs, sq_abs]
  simp only [newtonianJacobianMatrix, Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
    Matrix.one_apply, smul_eq_mul, hr]
  rw [abs_mul, abs_mul]
  congr 1
  simpa only [mul_assoc] using numerator_abs x i j

theorem solution
    (μ : ℝ) (x : Vec3) (i j : Fin 3) :
    |newtonianJacobianMatrix μ (coordinateAbs x) i j| =
      |newtonianJacobianMatrix μ x i j| := by
  exact entry_abs μ x i j
