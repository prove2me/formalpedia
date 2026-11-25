-- Prove2me | solution 1 for GlobalTheory.WeilNoncomm.loc_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:34:05.144548+00:00
-- url     : https://prove2.me/submissions/e435b47b-6626-4f60-b306-a540ab1276ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NotWeilIsGrpPullbackNoncomm
import Theorems.Thm_GlobalTheory_WeilNoncomm_lift_translT
import Theorems.Thm_GlobalTheory_WeilNoncomm_val_eq_loc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_val_constGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.WeilNoncomm
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
namespace GlobalTheory.WeilNoncomm
theorem _root_.solution {L : LB G.left} {k : ℤ} {T : Over S} (z : T.left) {θx θy : ThetaGrp G L k T} {c : Γ(T.left, ⊤)ˣ}
    (H : CommIsOf G L k θx θy c) (J : (T.left ⟶ G.left) → L.ι) (hJ : Good L z J) :
    loc G z θx 1 (J (1 : T ⟶ G).left) (J θx.pt.left) * loc G z θy θx.pt (J θx.pt.left) (J (θy.pt * θx.pt).left) =
      loc G z θy 1 (J (1 : T ⟶ G).left) (J θy.pt.left) * loc G z θx θy.pt (J θy.pt.left) (J (θx.pt * θy.pt).left) *
        gm ((lift (𝟙 T) (1 : T ⟶ G)).left ≫ (fst T G).left) z ⊤ c := by
  have a₁ := val_eq_loc G z θx 1 J
  have a₂ := val_eq_loc G z θy θx.pt J
  have a₃ := val_eq_loc G z θy 1 J
  have a₄ := val_eq_loc G z θx θy.pt J
  rw [_root_.mul_one] at a₁ a₃
  rw [← lift_translT] at a₂ a₄
  rw [← a₁, ← a₂, ← a₃, ← a₄]
  exact ((val_mul hJ _ _ _).trans (congrArg (val θx.φ (lift (𝟙 T) (1 : T ⟶ G)).left z J * ·)
    (val_pull hJ _ _ _))).symm.trans ((val_corr hJ H (lift (𝟙 T) (1 : T ⟶ G)).left).trans
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg (val θy.φ (lift (𝟙 T) (1 : T ⟶ G)).left z J * ·) (val_pull hJ _ _ _))) (val_constGen _ _ _ _ _))))
end GlobalTheory.WeilNoncomm
