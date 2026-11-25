-- Prove2me | solution 1 for GlobalTheory.ToricData.sec_f_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:54:43.441027+00:00
-- url     : https://prove2.me/submissions/39f478c7-d2de-41ef-8602-cef8942d2f1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit
import Theorems.Thm_GlobalTheory_ToricData_map_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_InhTate_map_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ToricData
variable {Z Y : Scheme.{0}} {J J₁ J₂ J₃ : Type} [Fintype J] [Fintype J₁] [Fintype J₂] [Fintype J₃]
namespace GlobalTheory.ToricData
theorem _root_.solution {φ : J → (Y ⟶ Z)} {ε : J → ℤ} (s : LB.Sec (LB.LinComb (Inh.trivLB Z) φ ε))
    (j : J → (Inh.trivLB Z).ι) :
    s.f j = (Y.presheaf.map (homOfLE le_top).op).hom (secVal s) := by
  obtain rfl : j = fun _ => PUnit.unit := rfl
  exact ((map_map _ _ _).trans (map_self _ _)).symm
end GlobalTheory.ToricData
