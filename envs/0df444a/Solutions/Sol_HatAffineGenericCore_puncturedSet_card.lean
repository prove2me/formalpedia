-- Prove2me | solution 1 for HatAffineGenericCore.puncturedSet_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:10:58.568406+00:00
-- url     : https://prove2.me/submissions/241e2ff6-69a2-4760-8eee-bf8f098d79c4

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card

set_option autoImplicit true
open scoped BigOperators MonomialOrder
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial
namespace HatAffineGenericCore
theorem _root_.solution {K : Type u} [Field K] [Fintype K] {m : Nat}
    (g : Fin m → K) (j : Fin m) :
    (puncturedSet g j).card = Fintype.card K - 1 := by
  classical
  simp [puncturedSet]
end HatAffineGenericCore
