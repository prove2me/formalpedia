-- Prove2me | solution 1 for GlobalTheory.HL.MoveFacts.iso_spanTo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:25:14.736986+00:00
-- url     : https://prove2.me/submissions/07af04d2-7d07-4cda-9821-f2a941fff279

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMoveProperties
import Theorems.Thm_GlobalTheory_HL_MoveFacts_form_zero_of_span
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveFacts
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveFacts
theorem _root_.solution (g : Fin (r + 1) → S.V) (c : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then c else 0)
    (x : S.V) (hx : x ∈ S.spanTo g r) : S.h x x = 0 := by
  have hH : IsHerm L S.Hm := S.herm.1
  show hf L S.Hm x x = 0
  refine form_zero_of_span hH (g '' {i | (i : ℕ) < r}) ?_ x hx x hx
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have ha' : (a : ℕ) < r := ha
  have hne : a ≠ Fin.last r := fun e => by subst e; simp at ha'
  rw [hg, if_neg (fun hc => hne hc.1)]
end GlobalTheory.HL.MoveFacts
