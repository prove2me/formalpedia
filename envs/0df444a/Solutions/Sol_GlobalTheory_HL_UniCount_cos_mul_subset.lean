-- Prove2me | solution 1 for GlobalTheory.HL.UniCount.cos_mul_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:58:33.461875+00:00
-- url     : https://prove2.me/submissions/b0199890-caf8-403f-9aa5-bbc8bd7a0202

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotEqPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUniCosetsLe
import Theorems.Thm_GlobalTheory_HL_UniCount_isUni_mul
import Theorems.Thm_GlobalTheory_HL_UniCount_isIntM_mul

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.UniCount
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {N : ℕ}
namespace GlobalTheory.HL.UniCount
theorem _root_.solution (L : LocE F E) (u B : Matrix (Fin N) (Fin N) E) (h1 : IsUni B)
    (h2 : IsIntM L B) : cos L (u * B) ⊆ cos L u := by
  rintro v ⟨A, hA, hA', rfl⟩
  exact ⟨B * A, isUni_mul h1 hA, isIntM_mul L h2 hA', Matrix.mul_assoc _ _ _⟩
end GlobalTheory.HL.UniCount
