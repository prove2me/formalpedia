-- Prove2me | solution 2 for NewtonianLipschitz.newtonianJacobianMatrix_rowSum_coordinateAbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:50:46.896648+00:00
-- url     : https://prove2.me/submissions/a4ec58ba-5faa-43b3-82fe-44f6ccaa617e

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_entry_abs_coordinateAbs

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (μ : ℝ) (x : Vec3) (i : Fin 3) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ (coordinateAbs x) i j|) =
      ∑ j : Fin 3, |newtonianJacobianMatrix μ x i j| := by
  apply Finset.sum_congr rfl
  intro j hj
  exact newtonianJacobianMatrix_entry_abs_coordinateAbs μ x i j
end NewtonianLipschitz
