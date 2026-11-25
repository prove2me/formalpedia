-- Prove2me | solution 1 for HatAffineGenericCore.eval_diagonalForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:46.80352+00:00
-- url     : https://prove2.me/submissions/5627301f-5e70-4da5-ba8e-b9016917f12c

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
theorem _root_.solution {K : Type u} [CommRing K] [Fintype K] {m : Nat}
    (lambda y : Fin m → K) :
    MvPolynomial.eval y (diagonalForm lambda) =
      ∑ j, lambda j * y j ^ (Fintype.card K - 1) := by
  simp [diagonalForm]
end HatAffineGenericCore
