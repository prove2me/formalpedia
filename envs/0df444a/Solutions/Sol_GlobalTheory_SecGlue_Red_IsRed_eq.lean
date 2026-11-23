-- Prove2me | solution 1 for GlobalTheory.SecGlue.Red.IsRed.eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:53.121845+00:00
-- url     : https://prove2.me/submissions/ac4e884b-c586-4870-a000-5b1e76b8ca24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Red
variable {R R₀ : Type} [CommRing R] [CommRing R₀]
namespace GlobalTheory.SecGlue.Red
namespace IsRed
theorem _root_.solution {π : R →+* R₀} {hπ : Function.Surjective π} {Y : Scheme.{0}} {g₀ : Sp R₀ ⟶ Y}
    {S : Type} [CommRing S] [Algebra R S] {u v : Sp S ⟶ Y} (hu : IsRed π hπ g₀ S u)
    (hv : IsRed π hπ g₀ S v) :
    spMap (Ideal.Quotient.mk (redI π S)) ≫ u = spMap (Ideal.Quotient.mk (redI π S)) ≫ v :=
  hu.trans hv.symm
end IsRed
end GlobalTheory.SecGlue.Red
