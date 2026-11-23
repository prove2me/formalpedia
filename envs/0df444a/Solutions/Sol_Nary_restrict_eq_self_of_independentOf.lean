-- Prove2me | solution 1 for Nary.restrict_eq_self_of_independentOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:40:32.944511+00:00
-- url     : https://prove2.me/submissions/87757859-26f8-4af4-802d-9898dae9becb

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_Nary
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const

set_option autoImplicit true
open Nary
namespace Nary
theorem _root_.solution : IndependentOf f i → (restrict f c i) = f := by
  intro h
  ext I
  symm
  simp_all only [IndependentOf, restrict]
  apply h
end Nary
