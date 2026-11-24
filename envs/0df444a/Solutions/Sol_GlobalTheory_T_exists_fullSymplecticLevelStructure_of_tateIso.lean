-- Prove2me | solution 1 for GlobalTheory.T.exists_fullSymplecticLevelStructure_of_tateIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:28.845207+00:00
-- url     : https://prove2.me/submissions/cf9093d8-1519-4b16-bf45-302eb5f0958a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFullSymplecticLevelStructureOfTateIso
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFullSymplecticLevelStructureOfTateIsoStatement
import Theorems.Thm_GlobalTheory_FullLevel_exists_sympLevel_of_tate


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
    {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)
    {z : kˣ}, IsPrimitiveRoot z l.M' → z ^ (l.M' / l.A) = I.ζ l.A →
    ∃ ev : D.La → Q, IsSympLevel D act e l.M' z ev ∧ Induces l (I.ev l.A) (I.ev l.M) ev := by
  first | exact @GlobalTheory.FullLevel.exists_sympLevel_of_tate | exact GlobalTheory.FullLevel.exists_sympLevel_of_tate | (intros; apply GlobalTheory.FullLevel.exists_sympLevel_of_tate <;> assumption)
end _root_.GlobalTheory.T
