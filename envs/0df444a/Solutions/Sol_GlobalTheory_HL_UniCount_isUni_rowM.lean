-- Prove2me | solution 1 for GlobalTheory.HL.UniCount.isUni_rowM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:17:44.444351+00:00
-- url     : https://prove2.me/submissions/b2bf6ef5-5706-462f-bc9a-92d4988939ee

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
theorem _root_.solution (k : Fin N) (c : Fin N → E) (hc : ∀ j, j ≤ k → c j = 0) :
    IsUni (rowM k c) := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp only [rowM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne h.ne']
    split_ifs with h1
    · rw [hc j (h1 ▸ h.le), add_zero]
    · simp
  · simp only [rowM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_eq]
    split_ifs with h1
    · rw [hc i h1.le, add_zero]
    · simp
end GlobalTheory.HL.UniCount
