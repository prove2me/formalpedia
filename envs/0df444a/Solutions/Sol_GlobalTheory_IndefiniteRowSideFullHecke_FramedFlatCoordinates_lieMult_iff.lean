-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.lieMult_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:04:58.173351+00:00
-- url     : https://prove2.me/submissions/72c211cc-fb8d-4790-928b-c6f33cbfb546

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_FramedFlatCoordinates

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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R]
namespace GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates
theorem _root_.solution {k : Type} [Field k] {O : Type} [CommRing O] (act : OAct O G) (x : Sp k ⟶ S)
    (χ : O →+* k) (n : ℕ) :
    LieMult act x χ n ↔ ∃ v : Fin n → (epsAt x ⟶ G), IsEigenBasis act x χ v := Iff.rfl
end GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates
