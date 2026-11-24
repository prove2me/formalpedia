-- Prove2me | solution 1 for GlobalTheory.SS.VF.ofDerivation_fnOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:24:36.823785+00:00
-- url     : https://prove2.me/submissions/3df89e50-9227-4b15-8290-3e761a1baf85

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
variable {B : Type} [CommRing B] [Algebra K B]
namespace GlobalTheory.SS
namespace VF
theorem _root_.solution (d : Derivation K B B) (U : (Sp B).Opens) (b : B) :
    (VF.ofDerivation d).D U (fnOn B U b) = fnOn B U (d b) := secDer_fnOn d U b
end VF
end GlobalTheory.SS
