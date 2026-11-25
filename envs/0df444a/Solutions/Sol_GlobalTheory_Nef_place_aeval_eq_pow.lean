-- Prove2me | solution 1 for GlobalTheory.Nef.place_aeval_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:29.67464+00:00
-- url     : https://prove2.me/submissions/8a77714b-26d5-45df-adb0-5c051a121ecf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniquePlaceOrdEqOne
import Theorems.Thm_GlobalTheory_Nef_place_aeval_eq_one
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
open GlobalTheory GlobalTheory.Nef
open Polynomial
variable {k L : Type} [Field k] [Field L] [Algebra k L]
namespace GlobalTheory.Nef
theorem _root_.solution (x : L) (u : Place k L) (hx : u.1 x < 1) (p : k[X]) (hp : p ≠ 0) :
    u.1 (aeval x p) = u.1 x ^ p.rootMultiplicity 0 := by
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
  have hq0 : q.coeff 0 ≠ 0 := by
    intro h; apply hq; simpa [X_dvd_iff] using h
  conv_lhs => rw [hpq]
  simp [map_mul, map_pow, place_aeval_eq_one x u hx q hq0]
end GlobalTheory.Nef
