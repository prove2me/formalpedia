-- Prove2me | solution 1 for HatAffineGenericCore.mem_puncturedValues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:28.319581+00:00
-- url     : https://prove2.me/submissions/3b97e2e3-5381-4c2c-a8c8-4206eb730267

import Mathlib
import Definitions.Def_HatAffineGenericCore_G2

set_option autoImplicit true
open scoped BigOperators MonomialOrder
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial
namespace HatAffineGenericCore
theorem _root_.solution {K : Type u} [Fintype K]
    (g x : K) : x ∈ puncturedValues g ↔ x ≠ g := by
  classical
  simp [puncturedValues]
end HatAffineGenericCore
