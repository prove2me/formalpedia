-- Prove2me | solution 1 for HatAffineGenericCore.puncturedGrid_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:14:02.30486+00:00
-- url     : https://prove2.me/submissions/6534c001-0dd9-4e8a-914f-76cbf0f44b4c

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2
section
open scoped BigOperators MonomialOrder
namespace HatAffineGenericCore
universe u
open Finset
open MvPolynomial
private lemma X_sub_C_ne_zero_mv {K : Type u} [Field K] {m : Nat}
    (j : Fin m) (x : K) : (X j - C x : MvPolynomial (Fin m) K) ≠ 0 := by
  exact (MonomialOrder.degLex.monic_X_sub_C j x).ne_zero
end HatAffineGenericCore
end

set_option autoImplicit true
open scoped BigOperators MonomialOrder
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial
namespace HatAffineGenericCore
theorem _root_.solution {K : Type u} [Field K] [Fintype K] {m : Nat}
    (g : Fin m → K) (j : Fin m) :
    puncturedGrid g j ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr fun x hx => X_sub_C_ne_zero_mv j x
end HatAffineGenericCore
