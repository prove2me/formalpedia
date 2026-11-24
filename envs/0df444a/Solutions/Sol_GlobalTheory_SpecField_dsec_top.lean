-- Prove2me | solution 1 for GlobalTheory.SpecField.dsec_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:53:38.530722+00:00
-- url     : https://prove2.me/submissions/074a2e63-e18c-4d0e-977e-a14cd87ab968

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpecVectorFieldOfDualNumberSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS
noncomputable section
open GlobalTheory GlobalTheory.SpecField
open AlgebraicGeometry
variable {A : Type} [CommRing A]
variable (σ : A →+* DualNumber A) (hσ : ∀ a, (σ a).fst = a) (S : Submonoid A)
namespace GlobalTheory.SpecField
theorem _root_.solution (a : A) :
    dsec σ hσ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd :=
  Subtype.ext (funext fun x => dloc_algebraMap σ hσ _ a)
end GlobalTheory.SpecField
