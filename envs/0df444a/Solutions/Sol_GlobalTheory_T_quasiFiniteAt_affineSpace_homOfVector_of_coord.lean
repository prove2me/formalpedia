-- Prove2me | solution 1 for GlobalTheory.T.quasiFiniteAt_affineSpace_homOfVector_of_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:18.066145+00:00
-- url     : https://prove2.me/submissions/187866f0-e672-4235-9a9f-affaf2f332c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiFiniteAtAffineSpaceHomOfVectorOfCoord
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiFiniteAtAffineSpaceHomOfVectorOfCoordStatement
import Theorems.Thm_GlobalTheory_quasiFiniteAt_homOfVector_of_coord


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
open GlobalTheory.ZJ
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : Core) (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), IsClosed ({w} : Set C.G.toScheme) → C.Coord w W hw u → (AffineSpace.homOfVector (W.ι ≫ C.GG.hom) (fun i => W.topIso.inv.hom (u i))).QuasiFiniteAt ⟨w, hw⟩ := by
  first | exact @GlobalTheory.quasiFiniteAt_homOfVector_of_coord | exact GlobalTheory.quasiFiniteAt_homOfVector_of_coord | (intros; apply GlobalTheory.quasiFiniteAt_homOfVector_of_coord <;> assumption)
end _root_.GlobalTheory.T
