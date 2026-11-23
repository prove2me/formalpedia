-- Prove2me | solution 1 for GlobalTheory.SS.IsoAt.defAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:06.532307+00:00
-- url     : https://prove2.me/submissions/217dc383-03d9-41f2-80fb-a55c8bc11a04

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SS
variable (R : Type) [CommRing R] {K : Type} [Field K] [Algebra R K]
variable {R} {A A' : Over (Sp K)}
namespace GlobalTheory.SS
namespace IsoAt
theorem _root_.solution {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {y : M.Y.left} (h : IsoAt M N f y) :
    DefAt M N f y := by
  obtain ⟨U, g, hy, he, -⟩ := h
  exact ⟨U, g, hy, he⟩
end IsoAt
end GlobalTheory.SS
