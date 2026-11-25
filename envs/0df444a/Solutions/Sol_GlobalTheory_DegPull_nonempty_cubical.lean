-- Prove2me | solution 1 for GlobalTheory.DegPull.nonempty_cubical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:08:31.048747+00:00
-- url     : https://prove2.me/submissions/1d8c868c-397d-430e-b5b6-263c43242a86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__944b82dcaa95
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DegPull
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.DegPull
theorem _root_.solution (L : RigLB G) (t : LB.Gen (LB.LinComb L.L (thφ G (x3 G)) thε)) (ht : t.IsGen)
    (h : ∀ (T : Over S) (z : T.left) (J), Good L.L z J →
      IsCub (fun x x' y : T ⟶ G => val t (lift x (lift x' y)).left z J)) : Nonempty (CubicalStr G L) := by
  have v : ∀ (T : Over S) (z : T.left) (J), Good L.L z J → ∀ a : T ⟶ G3 G,
      val (LB.pullGen L.L (thφ G (x3 G)) thε t a.left) (𝟙 T.left) z J = val t a.left z J := fun T z J hJ a =>
    (val_pull hJ _ _ _).trans (by rw [Category.id_comp])
  have i3 : 𝟙 (G3 G).left = (lift (x3 G 0) (lift (x3 G 1) (x3 G 2))).left := by
    rw [← Over.id_left]; congr 1
    ext <;> simp [x3]
  refine ⟨⟨t, ht, fun i => corr_of_val L.isLB fun y J hJ => ?_, corr_of_val L.isLB fun y J hJ => ?_,
    corr_of_val L.isLB fun y J hJ => ?_, corr_of_val L.isLB fun y J hJ => ?_⟩⟩
  · refine (v (G2 G) y J hJ _).trans (Eq.trans ?_ (val_one _).symm)
    fin_cases i
    · exact (h (G2 G) y J hJ).face _ _
    · exact (h (G2 G) y J hJ).face₂ _ _
    · exact (h (G2 G) y J hJ).face₃ _ _
  · refine Eq.trans ?_ (v (G3 G) y J hJ _).symm
    exact (congrArg (fun r => val t r y J) i3).trans ((h (G3 G) y J hJ).s01 _ _ _)
  · refine Eq.trans ?_ (v (G3 G) y J hJ _).symm
    exact (congrArg (fun r => val t r y J) i3).trans ((h (G3 G) y J hJ).s12 _ _ _)
  · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v (G4 G) y J hJ _) (v (G4 G) y J hJ _))).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v (G4 G) y J hJ _) (v (G4 G) y J hJ _))).symm)
    exact (h (G4 G) y J hJ).coc _ _ _ _
end GlobalTheory.DegPull
