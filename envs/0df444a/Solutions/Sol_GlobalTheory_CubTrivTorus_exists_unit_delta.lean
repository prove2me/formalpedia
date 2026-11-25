-- Prove2me | solution 1 for GlobalTheory.CubTrivTorus.exists_unit_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:11:26.676176+00:00
-- url     : https://prove2.me/submissions/2a22dc1d-f2b1-4d18-a69a-d632b38d25d0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Theorems.Thm_GlobalTheory_CubTrivTorus_prod_cubTriv
import Theorems.Thm_GlobalTheory_CubTrivTorus_prod_biTriv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubTrivTorus
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] (i : H ⟶ G)
variable {i} [IsMonHom i] {L : RigLB G} {c : CubicalStr G L}
namespace GlobalTheory.CubTrivTorus
theorem _root_.solution (s : BiTriv c i) (σ : CubTriv c i) : ∃ a : Γ((H ⊗ H).left, ⊤)ˣ,
    ∀ (T : Over S) (t t' : T ⟶ H) (z : T.left) (J), Good L.L z J → val σ.s (t * t').left z J =
      gm (lift t t').left z ⊤ a * (val s.s (lift t (t' ≫ i)).left z J * val σ.s t.left z J * val σ.s t'.left z J) := by
  classical
  have hu := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L.L _ _ σ.s σ.gen (fst H H * snd H H).left
  have hu' := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen L.L _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen L.L _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L.L _ _ s.s s.gen (lift (fst H H) (snd H H ≫ i)).left)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L.L _ _ σ.s σ.gen (fst H H).left))
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L.L _ _ σ.s σ.gen (snd H H).left)
  obtain ⟨a, ha⟩ := GlobalTheory.TorusCoord.exists_ratio L.isLB (fun U _ h => by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [prod_cubTriv i (fst H H * snd H H) h, prod_biTriv i (fst H H) (snd H H ≫ i) h,
      prod_cubTriv i (fst H H) h, prod_cubTriv i (snd H H) h, MonObj.mul_comp]
    have key : ∀ A F N O : U, A * O⁻¹ = A * F⁻¹ * N⁻¹ * O * (F * O⁻¹) * (N * O⁻¹) := fun A F N O => by
      calc A * O⁻¹ = A * O⁻¹ * (F * F⁻¹) * (N * N⁻¹) * (O * O⁻¹) := by simp
        _ = A * F⁻¹ * N⁻¹ * O * (F * O⁻¹) * (N * O⁻¹) := by ac_rfl
    exact key _ _ _ _) _ hu _ hu'
  refine ⟨a, fun T t t' z J hJ => ?_⟩
  have key := ha T.left (lift t t').left z J hJ
  rw [val_pull hJ, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ] at key
  have e1 : (lift t t').left ≫ (fst H H * snd H H).left = (t * t').left := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
  have e2 : (lift t t').left ≫ (lift (fst H H) (snd H H ≫ i)).left = (lift t (t' ≫ i)).left := by
    rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
  have e3 : (lift t t').left ≫ (fst H H).left = t.left := by rw [← Over.comp_left, lift_fst]
  have e4 : (lift t t').left ≫ (snd H H).left = t'.left := by rw [← Over.comp_left, lift_snd]
  rw [e1, e2, e3, e4] at key
  exact key
end GlobalTheory.CubTrivTorus
