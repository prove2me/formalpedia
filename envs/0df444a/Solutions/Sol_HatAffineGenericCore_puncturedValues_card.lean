-- Prove2me | solution 1 for HatAffineGenericCore.puncturedValues_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:09:11.340666+00:00
-- url     : https://prove2.me/submissions/3efa83d1-49aa-4304-a600-3fd110f1e426

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
attribute [local simp] HatAffineGenericCore.mem_puncturedValues

set_option autoImplicit true
open scoped BigOperators MonomialOrder
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial
namespace HatAffineGenericCore
theorem _root_.solution {K : Type u} [Field K] [Fintype K]
    (g : K) : (puncturedValues g).card = Fintype.card K - 1 := by
  classical
  simp [puncturedValues]
end HatAffineGenericCore
