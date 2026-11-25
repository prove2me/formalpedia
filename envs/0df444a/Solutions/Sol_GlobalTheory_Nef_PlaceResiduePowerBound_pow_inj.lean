-- Prove2me | solution 1 for GlobalTheory.Nef.PlaceResiduePowerBound.pow_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:02:55.060077+00:00
-- url     : https://prove2.me/submissions/b90abf2b-60ba-4cd9-9e5b-7c6113d2c15b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceRestrictionExistsPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PlaceResiduePowerBound
open WithZero
variable {F : Type} [Field F]
namespace GlobalTheory.Nef.PlaceResiduePowerBound
theorem _root_.solution {e : ℕ} (he : e ≠ 0) {a b : ℤᵐ⁰} (h : a ^ e = b ^ e) : a = b :=
  le_antisymm ((pow_le_pow_iff_left₀ zero_le' zero_le' he).1 h.le)
    ((pow_le_pow_iff_left₀ zero_le' zero_le' he).1 h.ge)
end GlobalTheory.Nef.PlaceResiduePowerBound
