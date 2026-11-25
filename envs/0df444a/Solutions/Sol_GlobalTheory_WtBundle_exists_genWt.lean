-- Prove2me | solution 1 for GlobalTheory.WtBundle.exists_genWt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:24:14.393401+00:00
-- url     : https://prove2.me/submissions/01369a88-e190-4f55-ba2a-55eab2377534

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CommGroupCommonFactorQuotientCancel
import Theorems.Thm_GlobalTheory_WtBundle_exists_bundle
import Theorems.Thm_GlobalTheory_WtBundle_exists_gen_lam
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
open GlobalTheory GlobalTheory.WtBundle
variable {S : Scheme.{0}}
variable {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X] (Q : TQ G X)
namespace GlobalTheory.WtBundle
theorem _root_.solution (χ : X) : ∃ (N : LB Q.B.left) (t : LB.Gen (N.pull Q.q.left)), N.IsLB ∧ Q.GenWt N t χ ∧
    ∃ u : LB.Gen (abelian₂ Q.B N), u.IsGen := by
  obtain ⟨N, u, hN, hw, hu⟩ := exists_bundle Q χ
  have le : ∀ J : PUnit → N.ι, (N.pull Q.q.left).U J ≤ Q.q.left ⁻¹ᵁ N.U (J PUnit.unit) := fun J _ h => mem_pull.1 h
  refine ⟨N, ⟨fun J => res (le J) (u _)⟩, hN, ⟨fun J J' => unit_ext fun y hy => ?_, fun J => (hw _).res (le J)⟩,
    exists_gen_lam Q χ N hN u hw hu⟩
  exact ((gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans
    (hu _ (𝟙 _) y _ _ (le J hy.1) (le J' hy.2)))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_pull_g N Q.q.left (𝟙 _) y J J' hy.1 hy.2) ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm
end GlobalTheory.WtBundle
