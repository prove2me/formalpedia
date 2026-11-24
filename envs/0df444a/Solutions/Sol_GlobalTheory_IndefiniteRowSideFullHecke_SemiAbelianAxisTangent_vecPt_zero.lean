-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent.vecPt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:56:15.925601+00:00
-- url     : https://prove2.me/submissions/8222a53a-5590-49da-8a2e-94f3887ffcc8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SemiAbelianAxisTangent
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SemiAbelianAxisTangent_vecEquiv_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) (d : ℕ)
namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent
theorem _root_.solution {A : Type} [CommRing A] [Algebra S A] : vecPt x0 d (0 : Fin d → A) = 1 := by
  apply (vecEquiv _).injective
  rw [vecEquiv_one, vecPt, Equiv.apply_symm_apply]
  exact funext fun j => map_zero (toΓ A)
end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent
