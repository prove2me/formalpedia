-- Prove2me | solution 1 for GlobalTheory.ZJ.exists_sectionHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:31:56.954876+00:00
-- url     : https://prove2.me/submissions/b4ad8cf5-3ae5-40e0-ac59-bfe040a12e11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusPointEqOneOfAxes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FibreLawOfTestCartesian

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
open GlobalTheory GlobalTheory.ZJ
namespace GlobalTheory.ZJ
theorem _root_.solution {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (a : T.left ⟶ S) (ha : a = T.hom ≫ f) :
    ∃ ρ : (T ⟶ G') →* (Over.mk a ⟶ G), (∀ x, (ρ x).left = x.left ≫ φ) ∧ Function.Surjective ρ := by
  subst ha
  refine ⟨pushHom h T, fun _ => rfl, fun c => ?_⟩
  exact ⟨Over.homMk (h.1.lift c.left T.hom (Over.w c)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
end GlobalTheory.ZJ
