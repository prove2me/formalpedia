-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeGen.exists_cube_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:52:21.275569+00:00
-- url     : https://prove2.me/submissions/3c08a2ab-15f3-4453-9d74-682ed087abd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
omit [GrpObj A]
namespace GlobalTheory.AbLaw.CubeGen
theorem _root_.solution {T : Scheme.{0}} (j : T ⟶ A.left) :
    ∃ q : ((Over.pullback (j ≫ A.hom)).obj A ⊗ (Over.pullback (j ≫ A.hom)).obj A).left ⟶ (G3 A).left,
      IsPullback q ((Over.pullback (j ≫ A.hom)).obj A ⊗ (Over.pullback (j ≫ A.hom)).obj A).hom (x3 A 2).left j ∧
      q ≫ (x3 A 0).left = (fst _ _ : _ ⟶ (Over.pullback (j ≫ A.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ A.hom) ∧
      q ≫ (x3 A 1).left = (snd _ _ : _ ⟶ (Over.pullback (j ≫ A.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ A.hom) := by
  set B := (Over.pullback (j ≫ A.hom)).obj A
  have hB : IsPullback (pullback.fst A.hom (j ≫ A.hom)) B.hom A.hom (j ≫ A.hom) := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  have h3 : IsPullback (fst A (A ⊗ A)).left (snd A (A ⊗ A)).left A.hom (A ⊗ A).hom := IsPullback.of_hasPullback _ _
  have hBB : IsPullback (fst B B).left (snd B B).left B.hom B.hom := IsPullback.of_hasPullback _ _
  obtain ⟨m, m₁, m₂⟩ : ∃ m : B.left ⟶ (A ⊗ A).left, m ≫ (fst A A).left = pullback.fst A.hom (j ≫ A.hom) ∧
      m ≫ (snd A A).left = B.hom ≫ j :=
    ⟨h2.lift _ _ (by rw [hB.w, Category.assoc]), h2.lift_fst _ _ _, h2.lift_snd _ _ _⟩
  have hm : IsPullback m B.hom (snd A A).left j := IsPullback.of_right (by rw [m₁]; exact hB) m₂ h2
  have mw : m ≫ (A ⊗ A).hom = B.hom ≫ j ≫ A.hom := by
    rw [← Over.w (snd A A), ← Category.assoc, m₂, Category.assoc]
  have ho : IsPullback ((fst B B).left ≫ pullback.fst A.hom (j ≫ A.hom)) (snd B B).left A.hom (m ≫ (A ⊗ A).hom) := by
    rw [mw]; exact hBB.paste_horiz hB
  obtain ⟨q, q₁, q₂⟩ : ∃ q : (B ⊗ B).left ⟶ (G3 A).left,
      q ≫ (fst A (A ⊗ A)).left = (fst B B).left ≫ pullback.fst A.hom (j ≫ A.hom) ∧
      q ≫ (snd A (A ⊗ A)).left = (snd B B).left ≫ m :=
    ⟨h3.lift _ _ (by rw [ho.w, Category.assoc]), h3.lift_fst _ _ _, h3.lift_snd _ _ _⟩
  have hq : IsPullback q (snd B B).left (snd A (A ⊗ A)).left m := IsPullback.of_right (by rw [q₁]; exact ho) q₂ h3
  refine ⟨q, ?_, q₁, ?_⟩
  · rw [← Over.w (snd B B)]
    exact hq.paste_vert hm
  · show q ≫ (snd A (A ⊗ A)).left ≫ (fst A A).left = _
    rw [← Category.assoc, q₂, Category.assoc, m₁]
end GlobalTheory.AbLaw.CubeGen
