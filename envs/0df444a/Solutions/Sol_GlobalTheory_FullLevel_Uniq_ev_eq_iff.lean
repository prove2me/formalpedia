-- Prove2me | solution 1 for GlobalTheory.FullLevel.Uniq.ev_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:37:19.643907+00:00
-- url     : https://prove2.me/submissions/b0a091ca-2667-417c-bb77-d13f36196f0a

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
theorem _root_.solution (h : IsSympLevel D act e N z ev) (x y : D.La) : ev x = ev y ↔ ∃ b, x - y = N • b := by
  rw [← h.2.2.1]
  have h1 : ev x = ev (x - y) * ev y := by rw [← h.1, sub_add_cancel]
  rw [h1]
  exact mul_eq_right
end GlobalTheory.FullLevel.Uniq
