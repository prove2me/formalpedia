-- Prove2me | solution 1 for GlobalTheory.HL.CoordTermWt.unitri_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:35:00.275169+00:00
-- url     : https://prove2.me/submissions/1eaaf495-c19a-44a9-83a1-fe4f5bfda035

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameCoordinatesTransportInnerLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverFrameCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermsCorrespond
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordTermWt
open GlobalTheory.HL.CoordTerm
namespace GlobalTheory.HL.CoordTermWt
theorem _root_.solution {E W : Type} [CommRing E] [AddCommGroup W] [Module E W] {m : ℕ} (g g' : Fin m → W)
    (s : Matrix (Fin m) (Fin m) E) (h0 : ∀ i j, j < i → s i j = 0) (h1 : ∀ i, s i i = 1)
    (hs : ∀ j, g' j = ∑ i, s i j • g i) (A : Submodule E W) :
    (∀ b, g' b ∈ A) ↔ ∀ b, g b ∈ A := by
  constructor
  · intro h j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      have h2 : g j = g' j - ∑ i ∈ Finset.univ.erase j, s i j • g i := by
        rw [hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), h1, one_smul, add_sub_cancel_right]
      rw [h2]
      refine sub_mem (h j) (Submodule.sum_mem _ fun i hi => ?_)
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h3 | h3
      · exact A.smul_mem _ (ih i h3)
      · rw [h0 i j h3, zero_smul]; exact zero_mem _
  · intro h j
    rw [hs]
    exact Submodule.sum_mem _ fun i _ => A.smul_mem _ (h i)
end GlobalTheory.HL.CoordTermWt
