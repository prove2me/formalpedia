-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen.lieMult_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:53:04.122066+00:00
-- url     : https://prove2.me/submissions/d75995a1-fd90-4344-b924-3c71303f7d36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_RamifiedPlacesSplitEigen

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen
variable {S : Scheme.{0}} {R : Type} [CommRing R]
variable {O : Type} [CommRing O] {G : Over S} [GrpObj G]
namespace GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen
theorem _root_.solution {k : Type} [Field k] (act : OAct O G) (t : Sp k ⟶ S) (χ : O →+* k) (n : ℕ) :
    LieMult act t χ n ↔ ∃ v : Fin n → (epsAt t ⟶ G), IsEigBasis act t χ v := Iff.rfl
end GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen
