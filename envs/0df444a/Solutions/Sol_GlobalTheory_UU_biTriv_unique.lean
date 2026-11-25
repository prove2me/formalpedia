-- Prove2me | solution 1 for GlobalTheory.UU.biTriv_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:43:18.910828+00:00
-- url     : https://prove2.me/submissions/63fcb001-48c2-4e08-9266-7d4b94090272

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Theorems.Thm_GlobalTheory_UU_BiTrivUniq_exists_unit_ratio
import Theorems.Thm_GlobalTheory_UU_BiTrivUniq_gen_eq_of_val
import Theorems.Thm_GlobalTheory_UU_BiTriv_val_one_right
import Theorems.Thm_GlobalTheory_existsUnique_character_of_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_over_appTop_comp


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
open GlobalTheory GlobalTheory.UU
open BiTrivUniq
namespace GlobalTheory.UU
theorem _root_.solution : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    [ConnectedSpace G.left] (L : RigLB G) (c : CubicalStr G L) (i : splitTorus S X ⟶ G), IsMonHom i →
    ∀ s s' : BiTriv c i, s = s' := by
  intro S X _ G _ _ _ L c i _ s s'
  obtain ⟨ρ, hρ⟩ := exists_unit_ratio L.isLB s.gen s'.gen
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.existsUnique_character_of_mul S X G ρ fun Z t t' y => by
    have e : Units.map (lift (t * t') y).left.appTop.hom.toMonoidHom ρ =
        Units.map (lift t y).left.appTop.hom.toMonoidHom ρ * Units.map (lift t' y).left.appTop.hom.toMonoidHom ρ := by
      refine unit_ext fun z _ => ?_
      obtain ⟨J, hJ⟩ := exists_good_pt L.isLB z
      have a := s.law1 Z t t' y z J hJ
      rw [hρ _ _ z J hJ, hρ _ _ z J hJ, hρ _ _ z J hJ, s'.law1 Z t t' y z J hJ] at a
      rw [map_mul, ← gm_top, ← gm_top, ← gm_top]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      simp only [ofMul_mul] at a' ⊢
      linear_combination (norm := abel) a'
    exact congrArg Units.val e
  have key : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (x : Z ⟶ G) (z : Z.left),
      gm (lift t x).left z ⊤ ρ = gm (𝟙 Z.left) z ⊤ (chV t χ) := fun Z t x z => by
    rw [gm_top]
    congr 1
    refine Units.ext ?_
    rw [chV_val]
    show (lift t x).left.appTop.hom ρ.val = _
    rw [hχ, Rosenlicht.over_appTop_comp, lift_fst]
  have hs : s.s = s'.s := gen_eq_of_val L.isLB s.gen s'.gen fun y J hJ => by
    have a := hρ _ (lift (fst (splitTorus S X) G) (1 : _ ⟶ G)).left y J hJ
    rw [s.val_one_right hJ, s'.val_one_right hJ, key, _root_.mul_one, ← key _ _ (snd _ _), lift_fst_snd,
      Over.id_left] at a
    rw [hρ _ _ y J hJ, ← a, _root_.one_mul]
  obtain ⟨s, _, _, _⟩ := s
  obtain ⟨s', _, _, _⟩ := s'
  obtain rfl : s = s' := hs
  rfl
end GlobalTheory.UU
