-- Prove2me | solution 1 for GlobalTheory.CubeLift.exists_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:13:12.611803+00:00
-- url     : https://prove2.me/submissions/1da12433-5bad-4891-b4f2-5dd608336b4b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEvenCubicalTrivialisationLiftNilpotent
import Theorems.Thm_GlobalTheory_CubeLift_prod_triv
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (bcMap)
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] {i : H ⟶ G}
variable [IsCommMonObj G] [GrpObj H] [IsMonHom i]
namespace GlobalTheory.CubeLift
theorem _root_.solution (P : CP G)
    (t : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![i.left, (1 : H ⟶ G).left] ![1, -1])) (ht : t.IsGen) :
    ∃ E : Γ(H.left, ⊤)ˣ, ∀ (T : Over S) (x : T ⟶ H) (z : T.left) (J), Good P.L.L z J →
      val t (x⁻¹).left z J = gm x.left z ⊤ E * (val P.sym (x ≫ i).left z J * val t x.left z J) := by
  obtain ⟨E, hE⟩ := TorusCoord.exists_ratio P.L.isLB (fun U _ k => by
      refine (prod_triv (𝟙 H)⁻¹ k).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (prod_sym i k) (prod_triv (𝟙 H) k)).symm)
      rw [GrpObj.inv_comp, Category.id_comp, ← _root_.mul_assoc, inv_mul_cancel_right])
    (LB.pullGen P.L.L _ _ t ((𝟙 H)⁻¹ : H ⟶ H).left) (DVR.pullGen_isGen _ _ _ _ ht _)
    (LB.mulGen P.L.L _ _ _ _ (LB.pullGen P.L.L _ _ P.sym i.left) (LB.pullGen P.L.L _ _ t (𝟙 H : H ⟶ H).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.sym_gen _) (DVR.pullGen_isGen _ _ _ _ ht _))
  refine ⟨E, fun T x z J hJ => ?_⟩
  have e := hE _ x.left z J hJ
  rw [val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left,
    GrpObj.comp_inv, Category.comp_id] at e
  exact e
end GlobalTheory.CubeLift
