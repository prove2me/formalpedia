-- Prove2me | solution 1 for GlobalTheory.SS.polyPt_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:07:49.488892+00:00
-- url     : https://prove2.me/submissions/bcddcff3-936c-445f-8639-166e249f211d

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
theorem _root_.solution {S : Scheme.{0}} {G Z : Over S} [GrpObj G] (F : End G) (x : Z ⟶ G) :
    polyPt F Polynomial.X x = x ≫ (show G ⟶ G from F) := by
  simp [polyPt, List.range_succ, Polynomial.coeff_X]
end GlobalTheory.SS
