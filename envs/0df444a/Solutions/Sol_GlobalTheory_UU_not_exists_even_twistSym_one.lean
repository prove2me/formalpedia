-- Prove2me | solution 1 for GlobalTheory.UU.not_exists_even_twistSym_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:57:26.397306+00:00
-- url     : https://prove2.me/submissions/eda9a798-f460-4427-a926-86fa49dc52cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_NotExistsEvenTwistSymOne
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_val_sym_triv
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
private theorem stalk_neg_one_ne_one_of_over_rat {Z : Scheme.{0}} (z : Z) (f : Z ⟶ Spec (CommRingCat.of ℚ)) :
    (-1 : Z.presheaf.stalk z) ≠ 1 := by
  intro h
  let φ : ℚ →+* Z.presheaf.stalk z := (Z.presheaf.germ ⊤ z trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom)
  have h2 : φ 2 = φ 0 := by
    rw [map_ofNat, map_zero]
    linear_combination -h
  exact absurd (φ.injective h2) (by norm_num)
end GlobalTheory.UU
end
end

set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
namespace GlobalTheory.UU
theorem _root_.solution :
    ¬ ∃ σ : CubTriv ((CP.triv (splitTorus (Spec (CommRingCat.of ℚ)) ℤ)).twistSym 1).c (𝟙 _), σ.Even := by
  rintro ⟨σ, hσ⟩
  let e := splitTorusPointsEquiv (Spec (CommRingCat.of ℚ)) ℤ (𝟙_ (Over (Spec (CommRingCat.of ℚ))))
  let t := e.symm (zpowersHom _ (-1))
  have ht : t⁻¹ = t := by
    apply e.injective
    rw [map_inv, MulEquiv.apply_symm_apply]
    ext
    simp [t]
  have hc : (chV t 1).val = -1 := by simp [chV, t, e]
  obtain ⟨z⟩ : Nonempty (𝟙_ (Over (Spec (CommRingCat.of ℚ)))).left := ⟨IsLocalRing.closedPoint ℚ⟩
  obtain ⟨J, hJ⟩ := exists_good_pt (((CP.triv (splitTorus (Spec (CommRingCat.of ℚ)) ℤ)).twistSym 1).L.isLB) z
  have h1 := hσ _ t z J hJ
  rw [ht] at h1
  have hb : val ((CP.triv (splitTorus (Spec (CommRingCat.of ℚ)) ℤ)).twistSym 1).sym (t ≫ 𝟙 _).left z J = 1 :=
    mul_right_cancel (h1.symm.trans (_root_.one_mul _).symm)
  have hb2 := val_scaleGen (charUnit (Spec (CommRingCat.of ℚ)) ℤ 1)
    (CP.triv (splitTorus (Spec (CommRingCat.of ℚ)) ℤ)).sym (t ≫ 𝟙 _).left hJ
  erw [val_sym_triv, _root_.mul_one] at hb2
  have hb3 : gm (t ≫ 𝟙 _).left z ⊤ (charUnit (Spec (CommRingCat.of ℚ)) ℤ 1) = 1 := hb2.symm.trans hb
  rw [Category.comp_id, gm_charUnit] at hb3
  have hv := congrArg Units.val hb3
  rw [gm_val (𝟙 (𝟙_ (Over (Spec (CommRingCat.of ℚ)))).left) z ⊤ (by simp), Units.val_one, hc] at hv
  simp only [map_neg, map_one] at hv
  exact stalk_neg_one_ne_one_of_over_rat z (𝟙_ (Over (Spec (CommRingCat.of ℚ)))).hom hv
end GlobalTheory.UU
