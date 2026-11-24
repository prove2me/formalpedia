-- Prove2me | solution 1 for GlobalTheory.GrpDense.hom_ext_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:20:40.765152+00:00
-- url     : https://prove2.me/submissions/d05cd222-6e0e-4f1e-b617-cc0fc2421769

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Theorems.Thm_GlobalTheory_GrpDense_exists_generic
import Theorems.Thm_GlobalTheory_ExtUnique_hom_ext_of_dominant


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
open GlobalTheory GlobalTheory.GrpDense
variable {Z U : Scheme.{0}} {j : U ⟶ Z}
namespace GlobalTheory.GrpDense
theorem _root_.solution [IsIntegral Z] [Nonempty U] (j : U ⟶ Z) [IsOpenImmersion j] {X Y : Over Z} [Flat X.hom]
    [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  obtain ⟨W, k, hqc, hstd⟩ := exists_generic j
  have := hqc
  have := hstd
  apply Over.OverMorphism.ext
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant Y.hom (by simp) (pullback.fst X.hom (k ≫ j)) ?_
  have := h (Over.mk (pullback.snd X.hom (k ≫ j) ≫ k))
    (Over.homMk (pullback.fst X.hom (k ≫ j)) (by simpa using pullback.condition))
  simpa using congrArg (fun t => t.left) this
end GlobalTheory.GrpDense
