-- Prove2me | solution 1 for HatAffineConstantRows.linearForm_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:15:23.226007+00:00
-- url     : https://prove2.me/submissions/6207c270-9d0a-4d98-b9fa-84074b9f20c1

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Theorems.Thm_HatAffineConstantRows_linearForm_eq_zero_iff

set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial
namespace HatAffineConstantRows
theorem _root_.solution
    {K : Type u} [Field K] {m : Nat} (a : Fin m → K) :
    linearForm a ≠ 0 ↔ a ≠ 0 := by
  exact not_congr (linearForm_eq_zero_iff a)
end HatAffineConstantRows
