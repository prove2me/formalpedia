-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism.OUnif.ptA_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:07.306018+00:00
-- url     : https://prove2.me/submissions/f62cffb4-67fe-463f-aa29-dcbcf9d76ed5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_UniformTorsionIsomorphism
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UniformTorsionIsomorphism_toGen_injective

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
open GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism.OUnif
variable {t : SAB H (Spec (CommRingCat.of R))} {Δ : OData H I} (u : OUnif t Δ)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism.OUnif
theorem _root_.solution : Function.Injective (u.ptA F) := fun _ _ h =>
  toGen_injective ((cancel_mono u.U.gen.hom).1 h)
end GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism.OUnif
