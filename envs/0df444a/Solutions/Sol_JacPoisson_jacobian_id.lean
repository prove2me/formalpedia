-- Prove2me | solution 1 for JacPoisson.jacobian_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:51:12.524021+00:00
-- url     : https://prove2.me/submissions/22ba530b-92a4-46b2-ba0f-fb5e85c036df

module
public import Definitions.Def_JacPoisson_Defs
public import Definitions.Def_JacPoisson_Main

set_option autoImplicit false
@[expose] public section
public section
open JacPoisson
open MvPolynomial Matrix JacobianConjecture
variable {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
omit [Fintype l]
namespace JacPoisson
theorem _root_.solution : (RegularFunction.id R (l ⊕ l)).Jacobian = 1 := by
  ext a b
  simp only [RegularFunction.Jacobian, RegularFunction.id, Matrix.of_apply, pderiv_X,
    Matrix.one_apply, Pi.single_apply, eq_comm]
end JacPoisson
