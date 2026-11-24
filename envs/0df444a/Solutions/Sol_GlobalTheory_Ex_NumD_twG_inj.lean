-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.twG_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:30:00.299553+00:00
-- url     : https://prove2.me/submissions/03f9e0b5-43a1-4196-bbd2-ad3bef7e7e84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.NumD
theorem _root_.solution {k : ℕ} (β : N.Form k) (u : Oˣ) (g g' : N.Gt) (l : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (h : N.twG β u g l hl = N.twG β u g' l hl) : g = g' :=
  NumD.Gt.ext (congrArg (fun x : (N.twist β u).Gt => x.b) h)
    (funext fun z => mul_right_cancel (congrArg (fun x : (N.twist β u).Gt => x.s z) h))
end GlobalTheory.Ex.NumD
