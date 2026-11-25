-- Prove2me | solution 1 for GlobalTheory.CompletePoint.exists_gen_of_thick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:04:29.191727+00:00
-- url     : https://prove2.me/submissions/d9bcbb50-9711-4bf0-b5df-9a0156f56fe0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueTorusExtensionPointOfGroupPoint
import Theorems.Thm_GlobalTheory_CompletePoint_exists_unit_of_thick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_gen_of_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_scaleGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompletePoint
variable {R : Type} [CommRing R] (I : Ideal R) {X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Spec (CommRingCat.of R) ⟶ X)} {ε : K → ℤ} {φ' : K' → (Spec (CommRingCat.of R) ⟶ X)} {ε' : K' → ℤ}
namespace GlobalTheory.CompletePoint
theorem _root_.solution [IsLocalRing R] [IsAdicComplete I R] (hL : L.IsLB)
    {ψ : ∀ e, K' → (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ X)}
    (h : ∀ e, FormEq (fun k => thick R I e ≫ φ k) ε (ψ e) ε') (t : ∀ e, LB.Gen (LB.LinComb L (ψ e) ε'))
    (ht : ∀ e, (t e).IsGen)
    (hc : ∀ e z J, Good L z J → val (t (e + 1)) (thickTrans R I e) z J = val (t e) (𝟙 _) z J) :
    ∃ s : LB.Gen (LB.LinComb L φ ε), s.IsGen ∧
      ∀ e z J, Good L z J → val s (thick R I e) z J = val (t e) (𝟙 _) z J := by
  obtain ⟨g, hg⟩ := DVR.exists_gen_of_local L hL φ ε
  choose a ha using fun e => TorusCoord.exists_ratio hL (fun U _ f => (h e U f).symm) (t e) (ht e)
    (LB.pullGen L _ _ g (thick R I e)) (DVR.pullGen_isGen _ _ _ _ hg _)
  obtain ⟨b, hb⟩ := exists_unit_of_thick I a fun e => unit_ext fun z _ => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hL z
    have e₁ := hc e z J hJ
    rw [ha _ _ _ z J hJ, ha _ _ _ z J hJ, val_pull hJ, val_pull hJ, thickTrans_comp, Category.id_comp] at e₁
    rw [gm_pull (𝟙 _) (thickTrans R I e) z ⊤ trivial, Category.id_comp]
    exact mul_right_cancel e₁
  refine ⟨DVR.scaleGen b g, DVR.scaleGen_isGen b g hg, fun e z J hJ => ?_⟩
  rw [ha _ _ _ z J hJ, val_pull hJ, Category.id_comp, ← hb e]
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z le_top (hJ.mem φ _) b).trans ?_) rfl)
  refine Eq.trans ?_ (gm_pull (𝟙 _) (thick R I e) z ⊤ trivial b).symm
  rw [Category.id_comp]
end GlobalTheory.CompletePoint
