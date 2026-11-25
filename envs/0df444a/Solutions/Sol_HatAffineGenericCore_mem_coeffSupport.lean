-- Prove2me | solution 1 for HatAffineGenericCore.mem_coeffSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:55.054436+00:00
-- url     : https://prove2.me/submissions/1cd91e84-81da-41a4-8319-9c7761baa9d5

import Mathlib
import Definitions.Def_HatAffineGenericCore_G3A

set_option autoImplicit true
open scoped BigOperators
open HatAffineGenericCore
universe u
open Finset
open MvPolynomial
namespace HatAffineGenericCore
theorem _root_.solution {K : Type u} [Zero K] {m : Nat}
    (a : Fin m → K) (j : Fin m) :
    j ∈ coeffSupport a ↔ a j ≠ 0 := by
  classical
  simp [coeffSupport]
end HatAffineGenericCore
