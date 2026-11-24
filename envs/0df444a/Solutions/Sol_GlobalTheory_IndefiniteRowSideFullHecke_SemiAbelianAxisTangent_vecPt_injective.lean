-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent.vecPt_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:40:16.708712+00:00
-- url     : https://prove2.me/submissions/ccc2e047-7ffd-4ac5-a0f1-e9aae4127b22

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
theorem _root_.solution {A : Type} [CommRing A] [Algebra S A] :
    Function.Injective (vecPt x0 d : (Fin d → A) → _) := fun v w h => by
  have h' := (vecEquiv (overAt x0 A)).symm.injective h
  funext j
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1 (congrFun h' j)
end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent
