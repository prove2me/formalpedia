-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism.toGen_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:40:01.888263+00:00
-- url     : https://prove2.me/submissions/b5397b19-0c1a-417d-a92c-5770a068170e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_UniformTorsionIsomorphism
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UniformTorsionIsomorphism_toGen_fst

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {R : Type} [CommRing R] [IsDomain R]
attribute [instance] OData.mod
variable {H : Host E} {I : Ideal R}
variable {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism
theorem _root_.solution {G : Over (Spec (CommRingCat.of R))} :
    Function.Injective (toGen (R := R) (F := F) (G := G)) := fun x y h => by
  ext
  rw [← toGen_fst x, ← toGen_fst y, h]
end GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism
