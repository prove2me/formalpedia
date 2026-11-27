-- Prove2me | solution 1 for GlobalTheory.psi_zero_mul_rigV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:41:15.225562+00:00
-- url     : https://prove2.me/submissions/cb706b5d-7148-41b5-98b2-e3a1291c691d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalNeZeroOfIsIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValuesNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIntegralTensorLeftOfSmoothGrpObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiZeroMulRigV
import Theorems.Thm_GlobalTheory_isIntegral_tensor_left_of_smooth_grpObj
import Theorems.Thm_GlobalTheory_sval_ne_zero_of_isIso
import Theorems.Thm_GlobalTheory_values_natural
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1), PsiRel D (TF (R := R) F) s₀ → (∃ j, (s₀ 0).f j ≠ 0) → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J * rigV D z J = 1 := by
  intro R _ _ D F _ _ s₀ H hs z J hJ
  have hc : cT D (DegPre.BF D F) 0 = 1 := by
    have h := DVR.cPoint_add D (DegPre.BF D F) 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (DegPre.BF D F).left :=
    isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  let ζ : (TF (R := R) F).left ⟶ (DegPre.BF D F).left := (DegPre.zF D F).left
  let p : DegPre.BF D F ⟶ TF (R := R) F := fst _ _
  have hζ : ζ ≫ p.left = 𝟙 _ := by
    show (DegPre.zF D F ≫ p).left = _
    rw [show DegPre.zF D F ≫ p = 𝟙 _ from lift_fst _ _]
    rfl
  let κ₀ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  let J' : ((DegPre.BF D F).left ⟶ D.P.A.left) → D.P.L.ι := fun ψ => J (ζ ≫ ψ)
  have hJ' : Good D.P.L (ζ z) J' := fun ψ => hJ (ζ ≫ ψ)
  have e := H 0 (DegPre.BF D F) p (p ≫ κ₀) (snd _ _) (ζ z) J' hJ'
  rw [hc, _root_.mul_one, show lift p (snd _ _) = 𝟙 (DegPre.BF D F) from lift_fst_snd] at e
  have hne : sval (s₀ 0) (𝟙 (DegPre.BF D F).left) (ζ z) J' ≠ 0 :=
    sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s₀ 0) hs _ (𝟙 _) (ζ z) J' hJ'
  have e1 : (val (D.psi 0) (p ≫ κ₀).left (ζ z) J' * rigV D (ζ z) J').val = 1 :=
    (mul_eq_right₀ hne).1 e.symm
  have n1 := (values_natural _ _ _ _ D.P.L _ _ _ (p ≫ κ₀).left ζ z J hJ).2.2.1 (D.psi 0)
  have n2 := (values_natural _ _ _ _ D.P.L PUnit (fun _ => eSec D.P.A) (fun _ => 1)
    (DegPre.BF D F).hom ζ z J hJ).2.2.1 D.rig
  have a1 : ζ ≫ (p ≫ κ₀).left = jFK (R := R) F := by
    show ζ ≫ p.left ≫ jFK (R := R) F = _
    rw [← Category.assoc, hζ, Category.id_comp]
  have a2 : ζ ≫ (DegPre.BF D F).hom = (TF (R := R) F).hom := Over.w (DegPre.zF D F)
  rw [a1] at n1
  rw [a2] at n2
  apply Units.ext
  have e2 := congrArg (ζ.stalkMap z).hom e1
  rw [map_one, Units.val_mul, map_mul] at e2
  rw [Units.val_mul, Units.val_one]
  exact (congrArg₂ (· * ·) n1 n2).trans e2
end GlobalTheory
