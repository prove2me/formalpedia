-- Prove2me | solution 1 for GlobalTheory.T.exists_primitive_addChar_involution_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:53.073512+00:00
-- url     : https://prove2.me/submissions/7f30ddfc-4eef-4ec6-9e0d-24dc0e526894

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimitiveAddCharInvolutionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimitiveAddCharInvolutionInvariantStatement
import Theorems.Thm_GlobalTheory_GramCount_exists_isPrimitive_invol_invariant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∃ χ : AddChar B ℂ, χ.IsPrimitive ∧ ∀ u, χ (c u) = χ u := by
  first | exact @GlobalTheory.GramCount.exists_isPrimitive_invol_invariant | exact GlobalTheory.GramCount.exists_isPrimitive_invol_invariant | (intros; apply GlobalTheory.GramCount.exists_isPrimitive_invol_invariant <;> assumption)
end _root_.GlobalTheory.T
