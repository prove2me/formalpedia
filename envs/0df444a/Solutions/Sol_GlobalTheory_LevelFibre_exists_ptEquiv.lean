-- Prove2me | solution 1 for GlobalTheory.LevelFibre.exists_ptEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:42.886541+00:00
-- url     : https://prove2.me/submissions/4e687b99-1c83-44fb-b342-d1430e701512

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFibreSimplyTransitive
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LevelFibre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {S S' T : Scheme.{0}}
namespace GlobalTheory.LevelFibre
theorem _root_.solution {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (x : T ⟶ S') (z : T ⟶ S) (hz : x ≫ f = z) :
    ∃ e : (Over.mk x ⟶ G') ≃* (Over.mk z ⟶ G), ∀ p, (e p).left = p.left ≫ φ := by
  subst hz
  let F : (Over.mk x ⟶ G') →* (Over.mk (x ≫ f) ⟶ G) := MonoidHom.mk' (fun p => pushPt h.1.w p) fun p q =>
    Over.OverMorphism.ext (h.2 _ p q (pushPt h.1.w p) (pushPt h.1.w q) rfl rfl).symm
  refine ⟨MulEquiv.ofBijective F ⟨fun p q hpq => ?_, fun q => ?_⟩, fun p => rfl⟩
  · apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact congrArg (fun w => w.left) hpq
    · rw [Over.w, Over.w]
  · refine ⟨Over.homMk (h.1.lift q.left x (Over.w q)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext ?_⟩
    exact h.1.lift_fst _ _ _
end GlobalTheory.LevelFibre
