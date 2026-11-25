-- Prove2me | solution 1 for GlobalTheory.SS.unr_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:08:03.163259+00:00
-- url     : https://prove2.me/submissions/f82e0b81-5f68-4368-b0f6-03c330f4824b

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
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R} (h : Irreducible π) :
    Unr π R := ⟨inferInstance, inferInstance, h⟩
end GlobalTheory.SS
