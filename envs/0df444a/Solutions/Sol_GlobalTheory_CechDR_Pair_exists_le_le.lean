-- Prove2me | solution 1 for GlobalTheory.CechDR.Pair.exists_le_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:03:37.948555+00:00
-- url     : https://prove2.me/submissions/b5502b71-ee1f-41ac-b300-6fefc6d7cb50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.CechDR
variable {X X' : Scheme.{0}}
namespace GlobalTheory.CechDR
namespace Pair
theorem _root_.solution (φ : X' ⟶ X) (p q : Pair φ) {x : X'} (hx : x ∈ p.1.1.1 ⊓ q.1.1.1) :
    ∃ r : Pair φ, r ≤ p ∧ r ≤ q ∧ x ∈ r.1.1.1 := by
  have hy : φ.base x ∈ p.1.2.1 ⊓ q.1.2.1 := ⟨p.2 hx.1, q.2 hx.2⟩
  obtain ⟨U, hU, hxU, hUle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hy
  obtain ⟨U', hU', hxU', hU'le⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X'.isBasis_affineOpens
    (show x ∈ p.1.1.1 ⊓ q.1.1.1 ⊓ φ ⁻¹ᵁ U from ⟨hx, hxU⟩)
  refine ⟨⟨(⟨U', hU'⟩, ⟨U, hU⟩), hU'le.trans inf_le_right⟩, ?_, ?_, hxU'⟩
  · exact ⟨hU'le.trans (inf_le_left.trans inf_le_left), hUle.trans inf_le_left⟩
  · exact ⟨hU'le.trans (inf_le_left.trans inf_le_right), hUle.trans inf_le_right⟩
end Pair
end GlobalTheory.CechDR
