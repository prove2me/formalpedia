-- Prove2me | solution 1 for GlobalTheory.HL.FrameChange.sum_mem_spanTo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:43:08.188622+00:00
-- url     : https://prove2.me/submissions/a15a43b3-7b9e-407b-9f29-83c14c1b8eb2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermFramesCongrModThetaUnitriangular
import Theorems.Thm_GlobalTheory_HL_TermBasic_spanTo_mono


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameChange
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FrameChange
theorem _root_.solution (g g' : Fin (r + 1) → S.V) (hg' : ∀ a : Fin (r + 1), g' a ∈ S.spanTo g (a + 1))
    (c : Fin (r + 1) → E) (j : ℕ) (hc : ∀ a : Fin (r + 1), j ≤ (a : ℕ) → c a = 0) :
    ∑ a, c a • g' a ∈ S.spanTo g j :=
  Submodule.sum_mem _ fun a _ => by
    by_cases h : (a : ℕ) < j
    · exact Submodule.smul_mem _ _ (TermBasic.spanTo_mono S g (by omega) (hg' a))
    · rw [hc a (by omega), zero_smul]; exact Submodule.zero_mem _
end GlobalTheory.HL.FrameChange
