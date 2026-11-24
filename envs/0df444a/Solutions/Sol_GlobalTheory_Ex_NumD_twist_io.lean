-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.twist_io
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:30:06.077052+00:00
-- url     : https://prove2.me/submissions/46f73121-8bf7-473a-adf4-89c5b881ed9a

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
theorem _root_.solution {k : ℕ} (β : N.Form k) (u : Oˣ) (y : N.X) :
    (N.twist β u).io y = N.twG β u (N.io y) (fun z => β.be y z) (fun a b => map_add _ a b) :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => N.twist_τ β u y z)
end GlobalTheory.Ex.NumD
