-- Prove2me | solution 1 for GlobalTheory.HL.RatExt.single_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:40:04.505519+00:00
-- url     : https://prove2.me/submissions/2ed0f52d-e491-4c25-a3e7-06f15d4f93a7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RatExt
variable {E R : Type} [Field E] [CommRing R] (ι : E →+* R)
namespace GlobalTheory.HL.RatExt
theorem _root_.solution {n : ℕ} (i : Fin n) :
    (fun j => ι ((Pi.single i 1 : Fin n → E) j)) = (Pi.single i 1 : Fin n → R) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]
end GlobalTheory.HL.RatExt
