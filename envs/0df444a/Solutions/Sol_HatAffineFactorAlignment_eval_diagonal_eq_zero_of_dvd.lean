-- Prove2me | solution 1 for HatAffineFactorAlignment.eval_diagonal_eq_zero_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:54.267361+00:00
-- url     : https://prove2.me/submissions/500fb3d4-2777-42de-980d-309b333b8232

import Definitions.Def_HatAffineGenericCore_G3A
import Definitions.Def_HatAffineFactorAlignment_FactorShape

set_option autoImplicit true
open scoped BigOperators
open HatAffineFactorAlignment
universe u
open Finset
open MvPolynomial
open HatAffineGenericCore
namespace HatAffineFactorAlignment
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    {a lambda : Fin m → K}
    (hdiv : linearForm a ∣ diagonalForm lambda)
    {y : Fin m → K}
    (hy : MvPolynomial.eval y (linearForm a) = 0) :
    MvPolynomial.eval y (diagonalForm lambda) = 0 := by
  obtain ⟨Q, hQ⟩ := hdiv
  rw [hQ, map_mul, hy, zero_mul]
end HatAffineFactorAlignment
