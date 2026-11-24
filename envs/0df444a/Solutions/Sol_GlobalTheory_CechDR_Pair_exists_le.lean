-- Prove2me | solution 1 for GlobalTheory.CechDR.Pair.exists_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:36:32.947963+00:00
-- url     : https://prove2.me/submissions/228f7117-424e-4508-a2d0-937f422c1f3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
import Theorems.Thm_GlobalTheory_CechDR_Pair_exists_basicOpen

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
open Opposite
variable {R' : Type} [CommRing R'] {X X' : Scheme.{0}}
namespace GlobalTheory.CechDR
namespace Pair
theorem _root_.solution (φ : X' ⟶ X) (W : X'.affineOpens) {x : X'} (hx : x ∈ W.1) :
    ∃ (p : Pair φ) (hp : p.1.1 ≤ W), x ∈ p.1.1.1 := by
  obtain ⟨p, f, e, hxp⟩ := Pair.exists_basicOpen φ W hx
  exact ⟨p, show p.1.1.1 ≤ W.1 from e ▸ X'.basicOpen_le f, hxp⟩
end Pair
end GlobalTheory.CechDR
