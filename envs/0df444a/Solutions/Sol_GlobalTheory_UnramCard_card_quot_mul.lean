-- Prove2me | solution 1 for GlobalTheory.UnramCard.card_quot_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:21.167468+00:00
-- url     : https://prove2.me/submissions/37e2695e-6959-41eb-b6bd-83ccb15f5ee1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotEqPow

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
open GlobalTheory GlobalTheory.UnramCard
namespace GlobalTheory.UnramCard
theorem _root_.solution {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) (b : R) :
    Nat.card (R ⧸ Ideal.span {a * b}) =
      Nat.card (R ⧸ Ideal.span {a}) * Nat.card (R ⧸ Ideal.span {b}) := by
  have h : Ideal.span {a * b} = a • Ideal.span {b} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Submodule.ideal_span_singleton_smul,
      smul_eq_mul]
  rw [h]
  have hi := Ideal.mulQuot_injective (Ideal.span {b}) ha
  have hs := Ideal.quotOfMul_surjective (a := a) (Ideal.span {b})
  have he := Ideal.exact_mulQuot_quotOfMul (a := a) (Ideal.span {b})
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (Ideal.quotOfMul a (Ideal.span {b}))),
    Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ hs).toEquiv, he.linearMap_ker_eq,
    ← Nat.card_congr (LinearEquiv.ofInjective _ hi).toEquiv, mul_comm]
end GlobalTheory.UnramCard
