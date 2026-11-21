-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianNumerator_coordinateAbs
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:39:33.171912+00:00
-- url     : https://prove2.me/submissions/61a96924-ea7a-446e-849e-9f222e6b1fc6

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

theorem solution (x : Vec3)
    (i j : Fin 3) :
    |3 * coordinateAbs x i * coordinateAbs x j -
      euclideanRadius x ^ 2 * (if i = j then 1 else 0)| =
    |3 * x i * x j -
      euclideanRadius x ^ 2 * (if i = j then 1 else 0)| := by
  exact numerator_abs x i j
