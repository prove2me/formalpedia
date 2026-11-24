-- Prove2me | solution 1 for GlobalTheory.ExtDescent.hom_ext_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:56:14.065942+00:00
-- url     : https://prove2.me/submissions/db7c87b1-302e-4996-8092-5e78ece046b0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusExtensionDescends

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
open GlobalTheory GlobalTheory.ExtDescent
variable {S S₀ : Scheme.{0}} {f : S ⟶ S₀}
namespace GlobalTheory.ExtDescent
theorem _root_.solution [Flat f] [Surjective f] {X Y : Over S₀} {a b : X ⟶ Y}
    (h : ∀ (T : Over S) (t : Over.mk (T.hom ≫ f) ⟶ X), t ≫ a = t ≫ b) : a = b := by
  apply Over.OverMorphism.ext
  haveI := Flat.epi_of_flat_of_surjective (pullback.fst X.hom f)
  rw [← cancel_epi (pullback.fst X.hom f)]
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom f))
    (Over.homMk (pullback.fst X.hom f) (by simpa using pullback.condition)))
end GlobalTheory.ExtDescent
