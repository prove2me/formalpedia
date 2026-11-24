-- Prove2me | solution 1 for GlobalTheory.FullLevel.Uniq.ev_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:37:28.928287+00:00
-- url     : https://prove2.me/submissions/0a6406ff-3953-4a0b-8b3e-f14ce193fb51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullSymplecticLevelStructureUniqueOfLevels

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel
open GlobalTheory GlobalTheory.FullLevel GlobalTheory.FullLevel.Uniq
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
  {N : ℕ} {z : kˣ} {ev : D.La → Q}
namespace GlobalTheory.FullLevel.Uniq
theorem _root_.solution (h : IsSympLevel D act e N z ev) : ev 0 = 1 := (h.2.2.1 0).2 ⟨0, by simp⟩
end GlobalTheory.FullLevel.Uniq
