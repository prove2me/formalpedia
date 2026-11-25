-- Prove2me | solution 1 for HatAffineGenericCore.eval_linearForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:46.064166+00:00
-- url     : https://prove2.me/submissions/ff6b0eb0-ac51-4353-9f88-2b795b14165b

import Mathlib
import Definitions.Def_HatAffineGenericCore_G3A
import Theorems.Thm_HatAffineGenericCore_mem_coeffSupport
attribute [local simp] HatAffineGenericCore.mem_coeffSupport

set_option autoImplicit true
open scoped BigOperators
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial
namespace HatAffineGenericCore
theorem _root_.solution {K : Type u} [CommRing K] {m : Nat}
    (a y : Fin m → K) :
    MvPolynomial.eval y (linearForm a) = ∑ j, a j * y j := by
  simp [linearForm]
end HatAffineGenericCore
