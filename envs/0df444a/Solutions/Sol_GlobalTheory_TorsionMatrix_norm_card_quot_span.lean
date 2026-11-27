-- Prove2me | solution 1 for GlobalTheory.TorsionMatrix.norm_card_quot_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:51.891643+00:00
-- url     : https://prove2.me/submissions/91a1b32d-fcb0-411e-934c-2614ac6fc7b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MatrixPolynomialDetNormFixedPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TorsionMatrix
open Matrix
namespace GlobalTheory.TorsionMatrix
theorem _root_.solution (l : ℕ) [Fact l.Prime] {a : ℤ_[l]} (ha : a ≠ 0) :
    ‖((Nat.card (ℤ_[l] ⧸ Ideal.span {a}) : ℕ) : ℚ_[l])‖ = ‖a‖ := by
  have h1 : Ideal.span {a} = RingHom.ker (PadicInt.toZModPow (p := l) a.valuation) := by
    rw [PadicInt.ker_toZModPow]
    conv_lhs => rw [PadicInt.unitCoeff_spec ha]
    exact Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff ha).isUnit _
  have h2 : Nat.card (ℤ_[l] ⧸ Ideal.span {a}) = l ^ a.valuation := by
    rw [h1, Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow (p := l) a.valuation))).toEquiv, Nat.card_zmod]
  rw [h2, PadicInt.norm_eq_zpow_neg_valuation ha]
  push_cast
  rw [Padic.norm_p_pow]
end GlobalTheory.TorsionMatrix
