-- Prove2me | solution 1 for GlobalTheory.HL.ncard_image_mk_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:43:10.05295+00:00
-- url     : https://prove2.me/submissions/abdf38d9-4d60-43e8-9364-0ecbbc2cc50d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonneg
import Theorems.Thm_GlobalTheory_HL_image_mk_eq_preimage_of_le

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
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution {W : Type} [AddCommGroup W] {A A' : AddSubgroup W} {S : Set W}
    (hle : A' ≤ A) (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    ((QuotientAddGroup.mk : W → W ⧸ A') '' S).ncard =
      ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard * A'.relIndex A := by
  rw [image_mk_eq_preimage_of_le hle hS,
    Set.ncard_preimage_of_injective_subset_range (Equiv.injective _)
      (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _), Set.ncard_prod, Set.ncard_univ]
  rfl
end GlobalTheory.HL
