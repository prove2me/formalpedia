-- Prove2me | solution 1 for GlobalTheory.GrpDescent.hom_ext_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:25:35.706798+00:00
-- url     : https://prove2.me/submissions/f0b14ec1-24ec-47cb-8149-6f28f4fd2e10

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MorphismsDescendToLargeSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjDescendsToLargeSubfield

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.GrpDescent
open GrpDense
variable {Z U : Scheme.{0}} {j : U ⟶ Z}
namespace GlobalTheory.GrpDescent
theorem _root_.solution (j : U ⟶ Z) [Flat j] [Surjective j] {X Y : Over Z} {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have : Epi (pullback.fst X.hom j) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  rw [← cancel_epi (pullback.fst X.hom j)]
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom j))
    (Over.homMk (pullback.fst X.hom j) (by simpa using pullback.condition)))
end GlobalTheory.GrpDescent
