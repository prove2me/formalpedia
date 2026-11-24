-- Prove2me | solution 1 for GlobalTheory.GrpFlatDesc.hom_ext_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:55:04.443876+00:00
-- url     : https://prove2.me/submissions/fcded3d3-4ce9-48af-ad6f-bde33f83add6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupSchemeMorphismDescends

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GrpFlatDesc
open GrpDense MorphismProperty
variable {Z U : Scheme.{0}}
namespace GlobalTheory.GrpFlatDesc
theorem _root_.solution (j : U ⟶ Z) [Flat j] [Surjective j] {X Y : Over Z} {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have := Flat.epi_of_flat_of_surjective (pullback.fst X.hom j)
  apply Over.OverMorphism.ext
  rw [← cancel_epi (pullback.fst X.hom j)]
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom j))
    (Over.homMk (pullback.fst X.hom j) (by simpa using pullback.condition)))
end GlobalTheory.GrpFlatDesc
