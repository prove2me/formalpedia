-- Prove2me | solution 1 for GlobalTheory.DegActCheck.psiUnitOn_iff_interior
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:27.65873+00:00
-- url     : https://prove2.me/submissions/7a28f6a1-2c34-4719-b8e1-3e510f73a40d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_PsiUnitOnIffInterior

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DegActCheck
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.DegActCheck
theorem _root_.solution (D : Out.DegPre R) (χ : D.X) (U : Set (Sp R)) :
    PsiUnitOn D χ U ↔ PsiUnitOn D χ (interior U) :=
  ⟨fun h j V hV hU => h j V hV (hU.trans interior_subset),
   fun h j V hV hU => h j V hV (interior_maximal hU V.isOpen)⟩
end GlobalTheory.DegActCheck
