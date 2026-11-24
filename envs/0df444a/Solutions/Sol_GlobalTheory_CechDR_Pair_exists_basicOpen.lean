-- Prove2me | solution 1 for GlobalTheory.CechDR.Pair.exists_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:17:09.408637+00:00
-- url     : https://prove2.me/submissions/3c41a430-bf9a-4ce0-9ad1-b647cf5481dd

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
theorem _root_.solution (φ : X' ⟶ X) (W : X'.affineOpens) {x : X'} (hx : x ∈ W.1) :
    ∃ (p : Pair φ) (f : Γ(X', W.1)), p.1.1.1 = X'.basicOpen f ∧ x ∈ p.1.1.1 := by
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show φ.base x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨f, hf, hxf⟩ := W.2.exists_basicOpen_le (V := W.1 ⊓ φ ⁻¹ᵁ U) ⟨x, hx, hxU⟩ hx
  exact ⟨⟨(⟨X'.basicOpen f, W.2.basicOpen f⟩, ⟨U, hU⟩), hf.trans inf_le_right⟩, f, rfl, hxf⟩
end Pair
end GlobalTheory.CechDR
