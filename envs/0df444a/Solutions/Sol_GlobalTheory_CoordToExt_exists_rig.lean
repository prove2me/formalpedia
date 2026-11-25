-- Prove2me | solution 1 for GlobalTheory.CoordToExt.exists_rig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:36:52.782507+00:00
-- url     : https://prove2.me/submissions/fd53a791-5f02-4f0f-8856-26372cf8cca4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAbelianSchemeThick
import Theorems.Thm_GlobalTheory_TorusCoord_IsPointOf_pull
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull__6a8fb3a1b1a4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
open GlobalTheory
open GlobalTheory.CoordToExt
variable {S : Scheme.{0}}
namespace GlobalTheory.CoordToExt
theorem _root_.solution {G B T : Scheme.{0}} (q : G ⟶ B) (eG : T ⟶ G) (eB : T ⟶ B) (e : eG ≫ q = eB) (M : LB B)
    (s : ∀ a : M.ι, Γ(G, q ⁻¹ᵁ M.U a)ˣ)
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) (a a' : M.ι), q (r z) ∈ M.U a → q (r z) ∈ M.U a' →
      gm r z _ (s a') = gm (r ≫ q) z _ (M.g a a') * gm r z _ (s a)) :
    ∃ ρ : LB.Gen (M.pull eB), ρ.IsGen ∧ ∀ (a : M.ι) (y : T), q (eG y) ∈ M.U a →
      gm eG y _ (s a) * gm (𝟙 _) y _ (ρ.s fun _ => a) = 1 := by
  subst e
  have le : ∀ J : PUnit → M.ι, (M.pull (eG ≫ q)).U J ≤ eG ⁻¹ᵁ (q ⁻¹ᵁ M.U (J PUnit.unit)) :=
    fun J y hy => mem_pull₂.1 hy
  have v : ∀ (J : PUnit → M.ι) y, y ∈ (M.pull (eG ≫ q)).U J →
      gm (𝟙 T) y ((M.pull (eG ≫ q)).U J) (res (le J) (pullU eG _ (s (J PUnit.unit))))⁻¹ =
        (gm eG y _ (s (J PUnit.unit)))⁻¹ :=
    fun J y hy => (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res _ y (le J) hy _).trans
      ((gm_pull _ eG y (q ⁻¹ᵁ M.U (J PUnit.unit)) (le J hy) _).trans (by rw [Category.id_comp]))))
  refine ⟨⟨fun J => (res (le J) (pullU eG _ (s (J PUnit.unit))))⁻¹⟩, fun J J' => unit_ext fun y hy => ?_,
    fun a y hy => ?_⟩
  · refine ((gm_res _ y _ hy _).trans (v J y hy.1)).trans (Eq.symm ?_)
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g M (eG ≫ q) (𝟙 _) y J J' hy.1 hy.2)
      ((gm_res _ y _ hy _).trans (v J' y hy.2)))).trans ?_
    rw [hs _ eG y _ _ (le J hy.1) (le J' hy.2), Category.id_comp, mul_inv, mul_inv_cancel_left]
  · exact (congrArg (_ * ·) (v (fun _ => a) y (mem_pull₂.2 hy))).trans (mul_inv_cancel _)
end GlobalTheory.CoordToExt
