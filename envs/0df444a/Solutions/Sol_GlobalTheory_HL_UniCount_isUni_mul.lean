-- Prove2me | solution 1 for GlobalTheory.HL.UniCount.isUni_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:17:40.181845+00:00
-- url     : https://prove2.me/submissions/3b000240-fe10-4284-a199-8506a2d38ebe

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotEqPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUniCosetsLe
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.UniCount
variable {E : Type} [CommRing E] {N : ℕ}
namespace GlobalTheory.HL.UniCount
theorem _root_.solution {s t : Matrix (Fin N) (Fin N) E} (hs : IsUni s) (ht : IsUni t) :
    IsUni (s * t) := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h1 | h1
    · rw [hs.1 i l h1, zero_mul]
    · rw [ht.1 l j (lt_of_lt_of_le h h1), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hs.2, ht.2, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h1 | h1
      · rw [hs.1 i l h1, zero_mul]
      · rw [ht.1 l i h1, mul_zero]
    · simp
end GlobalTheory.HL.UniCount
