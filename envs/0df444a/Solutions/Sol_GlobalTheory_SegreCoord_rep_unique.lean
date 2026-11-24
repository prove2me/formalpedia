-- Prove2me | solution 1 for GlobalTheory.SegreCoord.rep_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:57.095838+00:00
-- url     : https://prove2.me/submissions/2f2e5027-da17-4a9c-a027-25d52b75866f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Theorems.Thm_GlobalTheory_SegreCoord_secCoord_of_loc
import Theorems.Thm_GlobalTheory_SegreCoord_Loc_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SegreCoord
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']
variable {R : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {s : X ⟶ Sp R} (H : ProjRep I s M th)
include H
namespace GlobalTheory.SegreCoord
theorem _root_.solution {β : R →+* T} {x x' : Sp T ⟶ X} (hx : x ≫ s = spMap β) (hx' : x' ≫ s = spMap β) {v : σ → T}
    (hv : Ideal.span (Set.range v) = ⊤) (h : Loc M th x v) (h' : Loc M th x' v) : x = x' :=
  (H.2.2 T β v hv (H.2.1 T β x v hx (secCoord_of_loc hv h)).2).unique ⟨hx, secCoord_of_loc hv h⟩
    ⟨hx', secCoord_of_loc hv h'⟩
end GlobalTheory.SegreCoord
