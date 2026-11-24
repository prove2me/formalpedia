-- Prove2me | solution 1 for GlobalTheory.exists_pull_sec_sval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:57.264241+00:00
-- url     : https://prove2.me/submissions/1296f7a7-57b1-42c0-91e1-fda5c167d6da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsGenTranslDiffComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_KernelPolarisationTrivialOfSectionsVanishZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_appLE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (F : Y ⟶ X) :
    ∃ s : (L.pull F).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval s r z J = gs (r ≫ F) z (L.U (J (r ≫ F))) (θ.f (J (r ≫ F))) := by
  have le : ∀ J, (L.pull F).U J ≤ F ⁻¹ᵁ L.U (J PUnit.unit) := fun J => LB.wchart_le L _ J PUnit.unit
  have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) z J, r z ∈ (L.pull F).U J →
      gs r z _ ((F.appLE _ _ (le J)).hom (θ.f _)) = gs (r ≫ F) z _ (θ.f (J PUnit.unit)) :=
    fun Z r z J h => gs_appLE F _ _ (le J) r z h _
  refine ⟨⟨fun J => (F.appLE _ _ (le J)).hom (θ.f _), fun J J' => fn_ext fun y hy => ?_⟩,
    fun Z r z J hJ => ev Z r z _ (hJ.mem _ r)⟩
  have hm : (𝟙 Y ≫ F) y ∈ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) := ⟨le J hy.1, le J' hy.2⟩
  have e := congrArg (gs (𝟙 Y ≫ F) y _) (θ.compat (J PUnit.unit) (J' PUnit.unit))
  rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_unit _ y _ hm] at e
  refine ((gs_res (𝟙 Y) y _ hy _).trans ((ev _ _ y J hy.1).trans e)).trans
    (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y J J' hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans (ev _ _ y J' hy.2)))).symm)
  simp
end GlobalTheory
