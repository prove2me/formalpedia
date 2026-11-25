-- Prove2me | solution 1 for HatAffineGenericCore.puncturedSet_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:13:59.52481+00:00
-- url     : https://prove2.me/submissions/ccaebc02-f18e-40ab-98e3-ada2f3eee27e

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2
import Theorems.Thm_HatAffineGenericCore_puncturedSet_card

set_option autoImplicit true
open scoped BigOperators MonomialOrder
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial
namespace HatAffineGenericCore
theorem _root_.solution {K : Type u} [Field K] [Fintype K] {m : Nat}
    (g : Fin m → K) (j : Fin m) :
    (puncturedSet g j).Nonempty := by
  rw [← Finset.card_pos, puncturedSet_card]
  have hcard : 1 < Fintype.card K := Fintype.one_lt_card
  omega
end HatAffineGenericCore
