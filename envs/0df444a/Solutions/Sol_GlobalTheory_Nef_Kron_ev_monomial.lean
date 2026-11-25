-- Prove2me | solution 1 for GlobalTheory.Nef.Kron.ev_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:57.772941+00:00
-- url     : https://prove2.me/submissions/f4fc8820-29e7-45b5-8e67-75fc896a0c02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatOfHankelEventuallyZero
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.Kron
open Polynomial
variable {F : Type} [Field F] (c : ℕ → F)
namespace GlobalTheory.Nef.Kron
theorem _root_.solution (n : ℕ) (a : F) : ev c (monomial n a) = c n * a := by
  simp [ev, Polynomial.lsum_apply]
end GlobalTheory.Nef.Kron
