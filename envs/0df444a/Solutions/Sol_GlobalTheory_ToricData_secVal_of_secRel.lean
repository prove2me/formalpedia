-- Prove2me | solution 1 for GlobalTheory.ToricData.secVal_of_secRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:13:51.750031+00:00
-- url     : https://prove2.me/submissions/93518d0b-1deb-4c89-a032-08469c37d334

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit
import Theorems.Thm_GlobalTheory_ToricData_sec_f_eq
import Theorems.Thm_GlobalTheory_ToricData_map_top_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_InhTate_app_res
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
theorem _root_.solution {φ₁ : J₁ → (Y ⟶ Z)} {ε₁ : J₁ → ℤ} {s₁ : LB.Sec (LB.LinComb (Inh.trivLB Z) φ₁ ε₁)}
    {φ₂ : J₂ → (Y ⟶ Z)} {ε₂ : J₂ → ℤ} {s₂ : LB.Sec (LB.LinComb (Inh.trivLB Z) φ₂ ε₂)} {h : Y ⟶ Y}
    (hh : h = 𝟙 Y) {φ₃ : J₃ → (Y ⟶ Z)} {ε₃ : J₃ → ℤ} {u : LB.Gen (LB.LinComb (Inh.trivLB Z) φ₃ ε₃)}
    {a : Γ(Y, ⊤)ˣ} (hu : IsConst u a)
    (H : GeneratorPullback.SecRel (Inh.trivLB Z) φ₁ ε₁ s₁ φ₂ ε₂ s₂ h φ₃ ε₃ u) : secVal s₁ = secVal s₂ * a := by
  have := H (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ _ _ => rfl)
  subst hh
  refine map_top_inj (top_unique (le_inf (le_inf (wchart_triv φ₁ _).ge (wchart_triv _ _).ge)
    (wchart_triv φ₃ _).ge)) (Eq.trans ?_ (this.trans ?_))
  · exact (map_map _ _ _).symm.trans (congrArg _ (sec_f_eq s₁ _).symm)
  · rw [map_mul]
    refine congrArg₂ (· * ·) ?_ ?_
    · exact (congrArg _ (congrArg _ (sec_f_eq s₂ _))).trans (app_res _ _ _ _ _)
    · exact (congrArg _ (congrArg Units.val (hu _))).trans (map_map _ _ _)
end GlobalTheory.ToricData
