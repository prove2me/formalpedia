-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.triv_of_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:49:47.163751+00:00
-- url     : https://prove2.me/submissions/a9f24e28-fef1-44ec-8a6d-030e4930f179

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_adj
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [CommGroup Q] {ρ : 𝓞 E → Q →* Q} {e : ℕ → Q → Q → kˣ → Prop}
  (I : TateIso D k Q (fun a x => ρ a x) e)
variable (hu : Uniq e)
include hu
include I
namespace GlobalTheory.HeckeCompare
theorem _root_.solution {n : ℕ} (hn : 0 < n) {x y : Q} (hx : x ^ n = 1) (hy : y ^ n = 1) {c : 𝓞 E}
    (h : ρ (H.bar c) y = 1) : e n (ρ c x) y 1 := by
  rw [triv_adj I hu hn hx hy, h]
  exact triv_one I hu hn hx
end GlobalTheory.HeckeCompare
