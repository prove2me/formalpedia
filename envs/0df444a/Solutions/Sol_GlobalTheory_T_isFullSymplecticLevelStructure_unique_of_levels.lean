-- Prove2me | solution 1 for GlobalTheory.T.isFullSymplecticLevelStructure_unique_of_levels
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:02.723659+00:00
-- url     : https://prove2.me/submissions/767aa7b6-497a-4c21-8cd0-a76530701248

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullSymplecticLevelStructureUniqueOfLevels
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullSymplecticLevelStructureUniqueOfLevelsStatement
import Theorems.Thm_GlobalTheory_FullLevel_isSympLevel_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H) {k : Type} [Field k]
    {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop},
    (∀ (g g' : Q) (c c' : kˣ), e l.M' g g' c → e l.M' g g' c' → c = c') →
    ∀ {z : kˣ}, IsPrimitiveRoot z l.M' → ∀ {etaA eta ev ev' : D.La → Q},
    IsSympLevel D act e l.M' z ev → Induces l etaA eta ev →
    IsSympLevel D act e l.M' z ev' → Induces l etaA eta ev' → ev = ev' := by
  first | exact @GlobalTheory.FullLevel.isSympLevel_unique | exact GlobalTheory.FullLevel.isSympLevel_unique | (intros; apply GlobalTheory.FullLevel.isSympLevel_unique <;> assumption)
end _root_.GlobalTheory.T
