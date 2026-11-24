-- Prove2me | solution 1 for GlobalTheory.GroupGlue.of_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:53:28.371545+00:00
-- url     : https://prove2.me/submissions/a02efed9-92ea-4201-965a-da0f1eece097

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.GroupGlue
variable {X : Scheme.{0}} (𝒰 : X.OpenCover.{0})
variable {𝒰} {G : Over X} {H : ∀ i, Over (𝒰.X i)} {ψ : ∀ i, (H i).left ⟶ G.left}
variable [∀ i, GrpObj (H i)]
variable [GrpObj G]
omit [∀ i, GrpObj (H i)] [GrpObj G]
namespace GlobalTheory.GroupGlue
theorem _root_.solution (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) (hP : ∀ i, P (H i).hom) : P G.hom := by
  refine IsZariskiLocalAtTarget.of_openCover (P := P) (𝒰 := 𝒰) (f := G.hom) fun i => ?_
  have e0 : (hψ i).isoPullback.hom ≫ pullback.snd G.hom (𝒰.f i) = (H i).hom := (hψ i).isoPullback_hom_snd
  have h1 : P (pullback.snd G.hom (𝒰.f i)) := by
    rw [← P.cancel_left_of_respectsIso (hψ i).isoPullback.hom, e0]
    exact hP i
  exact h1
end GlobalTheory.GroupGlue
