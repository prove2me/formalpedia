-- Prove2me | solution 1 for GlobalTheory.UU.RelModel.existsUnique_samePt_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:58.324201+00:00
-- url     : https://prove2.me/submissions/8c816e4b-8e17-493f-8b05-0fe82eccd4c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RelModel
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UU.RelModel
theorem _root_.solution (U : PreU I D A G) (y : TF (R := R) F ⟶ G) : ∃! x, U.SamePt x y := by
  let l : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G :=
    Over.homMk (pullback.lift y.left (jFK (R := R) F) (Over.w y)) (pullback.lift_snd _ _ _)
  have e : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id]; rfl
  refine ⟨l ≫ U.gen.hom, ?_, fun x h => ?_⟩
  · show (l.left ≫ U.gen.hom.left) ≫ _ = _
    rw [Category.assoc, ← Category.assoc U.gen.hom.left, e, Category.id_comp]
    exact pullback.lift_fst _ _ _
  · rw [← Iso.comp_inv_eq]
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · exact ((Category.assoc _ _ _).trans h).trans (pullback.lift_fst _ _ _).symm
    · exact (Over.w (x ≫ U.gen.inv)).trans (pullback.lift_snd _ _ _).symm
end GlobalTheory.UU.RelModel
