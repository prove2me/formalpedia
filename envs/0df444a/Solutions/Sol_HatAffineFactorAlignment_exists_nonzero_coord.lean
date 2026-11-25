-- Prove2me | solution 1 for HatAffineFactorAlignment.exists_nonzero_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:14:29.57077+00:00
-- url     : https://prove2.me/submissions/a551606a-4596-41b5-a10a-38ec1df5685d

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
    {K : Type*} [Zero K] {m : Nat} (a : Fin m → K) (ha : a ≠ 0) :
    ∃ j, a j ≠ 0 := by
  classical
  by_contra h
  apply ha
  funext j
  have hj : ¬a j ≠ 0 := by
    exact fun hj => h ⟨j, hj⟩
  exact not_ne_iff.mp hj
end HatAffineFactorAlignment
