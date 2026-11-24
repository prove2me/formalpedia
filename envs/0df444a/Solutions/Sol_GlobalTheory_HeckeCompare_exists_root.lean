-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.exists_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:15:56.54684+00:00
-- url     : https://prove2.me/submissions/64a209cc-ed44-451f-b7ba-f6d9fbca1629

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj

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
omit hu
namespace GlobalTheory.HeckeCompare
theorem _root_.solution {p : ℕ} (hp : 0 < p) {c : Q} (hc : c ^ p = 1) : ∃ y, y ^ p = c := by
  obtain ⟨b, rfl⟩ := (I.onto _ hp _).1 hc
  exact ⟨_, I.tower p p hp hp b⟩
end GlobalTheory.HeckeCompare
