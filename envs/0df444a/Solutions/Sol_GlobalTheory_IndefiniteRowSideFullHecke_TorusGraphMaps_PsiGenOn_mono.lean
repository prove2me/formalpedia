-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps.PsiGenOn.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:00:27.497967+00:00
-- url     : https://prove2.me/submissions/39ebcfc7-659e-4644-856f-158b2a7e711f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps

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
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
namespace PsiGenOn
theorem _root_.solution {D : DegPre R} {χ : D.X} {U U' : Set (Spec (CommRingCat.of R))}
    (h : PsiGenOn D χ U) (hU : U' ⊆ U) : PsiGenOn D χ U' := fun x hx => h x (hU hx)
end PsiGenOn
end GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
