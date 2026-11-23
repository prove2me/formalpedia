-- Prove2me | solution 1 for GlobalTheory.SS.Model.j_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:04.088385+00:00
-- url     : https://prove2.me/submissions/3b5e3b2d-85bb-4c09-a04f-01248f707cd7

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
namespace Model
theorem _root_.solution (M : Model R A) : M.j ≫ M.Y.hom = A.hom ≫ spMap (algebraMap R K) := by
  unfold Model.j
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  congr 1
  exact Over.w M.e.inv
end Model
end GlobalTheory.SS
