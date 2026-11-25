-- Prove2me | solution 1 for JacPoisson.poissonBracket_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:51:01.788338+00:00
-- url     : https://prove2.me/submissions/94ffa200-1dea-48af-9419-bf052d974a32

module
public import Definitions.Def_JacPoisson_Defs
public import Definitions.Def_JacPoisson_Main

set_option autoImplicit false
@[expose] public section
public section
open JacPoisson
open MvPolynomial Matrix JacobianConjecture
variable {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
namespace JacPoisson
theorem _root_.solution (F : RegularFunction R (l ⊕ l) (l ⊕ l)) (v w : l ⊕ l) :
    poissonBracket (F v) (F w) =
      (F.Jacobianᵀ * (-Matrix.J l (MvPolynomial (l ⊕ l) R)) * F.Jacobian) v w := by
  simp only [poissonBracket, RegularFunction.Jacobian, Matrix.J, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.transpose_apply, Matrix.of_apply, Matrix.neg_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply, neg_zero, mul_zero,
    Finset.sum_const_zero, zero_add, add_zero]
  simp only [neg_neg, mul_ite, mul_neg, mul_one, mul_zero, Finset.sum_neg_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, neg_mul,
    Finset.sum_sub_distrib]
  ring
end JacPoisson
