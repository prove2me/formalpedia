-- Prove2me | solution 1 for GlobalTheory.FullLevel.Uniq.ev_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:07:42.78483+00:00
-- url     : https://prove2.me/submissions/c18c47c6-6006-447e-b1ce-7aaac266fd59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullSymplecticLevelStructureUniqueOfLevels
import Theorems.Thm_GlobalTheory_FullLevel_Uniq_ev_zero

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
theorem _root_.solution (h : IsSympLevel D act e N z ev) (n : ℕ) (a : D.La) : ev (n • a) = ev a ^ n := by
  induction n with
  | zero => simp [ev_zero h]
  | succ n ih => rw [succ_nsmul, h.1, ih, pow_succ]
end GlobalTheory.FullLevel.Uniq
