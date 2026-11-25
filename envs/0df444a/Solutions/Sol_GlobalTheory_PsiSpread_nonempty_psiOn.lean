-- Prove2me | solution 1 for GlobalTheory.PsiSpread.nonempty_psiOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:05:41.397782+00:00
-- url     : https://prove2.me/submissions/b11db79d-4207-4254-8728-abb43d71c78f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteCubeInduction
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PsiSpread
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.PsiSpread
theorem _root_.solution {W : (Spec (CommRingCat.of R)).Opens} (κ : TK R ⟶ TW W) (h : ∀ χ, Extends D κ χ) :
    Nonempty (PsiOn D W) := by
  choose t gt vt using h
  refine ⟨⟨t, gt, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  have c : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (t χ) κ.left) (D.psi χ) :=
    corr_of_val D.P.isLB fun z J hJ => (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; exact vt χ z J hJ)
  have q : (jK R ⁻¹ᵁ W).ι ≫ κ.left = jK R ∣_ W := by
    have hκ : κ.left ≫ W.ι = jK R := Over.w κ
    rw [← cancel_mono W.ι, morphismRestrict_ι, Category.assoc, hκ]
  have e := (val_pull hJ _ _ _).symm.trans (val_corr hJ c (jK R ⁻¹ᵁ W).ι)
  rw [q] at e
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  rw [Category.id_comp, Category.id_comp]
  exact e
end GlobalTheory.PsiSpread
