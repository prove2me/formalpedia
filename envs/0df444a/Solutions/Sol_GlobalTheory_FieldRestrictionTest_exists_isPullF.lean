-- Prove2me | solution 1 for GlobalTheory.FieldRestrictionTest.exists_isPullF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:58:14.2458+00:00
-- url     : https://prove2.me/submissions/6152b7e3-49db-43b1-b0dc-354792626f8f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsUniquePairIff
import Theorems.Thm_GlobalTheory_FieldRestrictionTest_isPullF_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cubAt
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldRestrictionTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.FieldRestrictionTest
theorem _root_.solution (σ : TF (R := R) F ⟶ T) (ξ : GtPt D T) : ∃ g, GtPt.IsPullF F σ.left ξ g := by
  have e := GlobalTheory.TorusCoord.comp_eq_of_left ξ.b (σ ≫ ξ.b) σ.left (𝟙 _) (Category.id_comp _).symm
  have vp : ∀ χ y J, Good D.P.L y J →
      val (LB.pullGen D.P.L _ _ (ξ.s χ) σ.left) (𝟙 _) y J = val (ξ.s χ) σ.left y J := fun χ y J hJ => by
    rw [val_pull hJ, Category.id_comp]
  obtain ⟨g, hb, hv⟩ := exists_gt (σ ≫ ξ.b) (fun χ => LB.pullGen D.P.L _ _ (ξ.s χ) σ.left)
    (fun χ => DVR.pullGen_isGen _ _ _ _ (ξ.isGen χ) _)
    (fun χ U _ f => Finset.prod_congr rfl fun k _ => congrArg (fun q => f q ^ DegPre.gtε k)
      ((e.1 χ k).trans ((Category.id_comp _).trans (congrFun (GlobalTheory.TorusCoord.gtφT_eq (σ ≫ ξ.b) χ) k).symm)))
    (fun y J hJ => (vp 0 y J hJ).trans ((val_corr hJ ξ.s_zero _).trans (val_one _)))
    (fun χ χ' y J hJ => by
      rw [vp _ y J hJ, vp _ y J hJ, vp _ y J hJ, ← GlobalTheory.TorusCoord.val_s_mul ξ σ.left χ χ' y J hJ, e.2 χ χ',
        ← val_cubAt hJ]
      exact congrArg (_ * ·) (val_pull hJ _ _ _))
  exact ⟨g, (isPullF_iff σ ξ g).2 ⟨hb, fun χ y J hJ => (hv χ y J hJ).trans (vp χ y J hJ)⟩⟩
end GlobalTheory.FieldRestrictionTest
