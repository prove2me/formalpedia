-- Prove2me | solution 1 for GlobalTheory.UnramOrder.exists_double_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:08:22.283319+00:00
-- url     : https://prove2.me/submissions/c8b64121-4310-484c-a5ae-18a751aecdc2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnramOrder
open IsLocalRing Polynomial
namespace GlobalTheory.UnramOrder
theorem _root_.solution {k : Type*} [Field k] [Finite k] {t n : k} (h : t ^ 2 - 4 * n = 0) :
    ∃ a, t = 2 * a ∧ n = a ^ 2 := by
  by_cases h2 : ringChar k = 2
  · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two h2 n
    have h0 : (2 : k) = 0 := by
      have := ringChar.Nat.cast_ringChar (R := k)
      rw [h2] at this
      exact_mod_cast this
    have ht : t ^ 2 = 0 := by linear_combination h + 2 * n * h0
    exact ⟨r, by rw [pow_eq_zero_iff two_ne_zero |>.1 ht, h0, zero_mul], by rw [hr, sq]⟩
  · have h2' : (2 : k) ≠ 0 := Ring.two_ne_zero h2
    refine ⟨t / 2, by field_simp, ?_⟩
    field_simp
    linear_combination -h
end GlobalTheory.UnramOrder
