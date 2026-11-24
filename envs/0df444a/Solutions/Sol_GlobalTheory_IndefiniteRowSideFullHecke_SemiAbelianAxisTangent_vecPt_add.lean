-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent.vecPt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:40:15.034609+00:00
-- url     : https://prove2.me/submissions/117ef723-fd76-4769-bd13-fadf089fe5f6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SemiAbelianAxisTangent

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
theorem _root_.solution {A : Type} [CommRing A] [Algebra S A] (v w : Fin d → A) :
    vecPt x0 d (v + w) = vecPt x0 d v * vecPt x0 d w := by
  apply (vecEquiv _).injective
  rw [vecEquiv_mul, vecPt, vecPt, vecPt, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact funext fun j => map_add (toΓ A) (v j) (w j)
end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent
