-- Prove2me | solution 1 for GlobalTheory.AddGeneric.exists_additionFactor_generator_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:11:14.007548+00:00
-- url     : https://prove2.me/submissions/80751825-25af-4eba-9a08-5d795297da0f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsAdditionFactorGeneratorTransported
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
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
open GlobalTheory GlobalTheory.AddGeneric
namespace GlobalTheory.AddGeneric
theorem _root_.solution {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) {T : Over S}
    (x y : T ⟶ G) :
    ∃ t : LB.Gen (LB.LinComb P.L.L (K := Fin 4) ![x.left, y.left, (x * y).left, (x * y⁻¹).left] ![2, 2, -1, -1]),
      t.IsGen ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P.L.L z J →
        val t ρ.left z J = kap0 P.c P.sym z J (ρ ≫ x) (ρ ≫ y) := by
  let r₀ := LB.pullGen P.L.L (fun _ : PUnit => eSec G) (fun _ => 1) P.L.rig T.hom
  have hr₀ : r₀.IsGen := DVR.pullGen_isGen _ _ _ _ P.L.rigGen _
  obtain ⟨t, ht, hv⟩ := exists_gen P.L.isLB (φ' := ![x.left, y.left, (x * y).left, (x * y⁻¹).left])
    (ε' := ![2, 2, -1, -1]) (fun U _ h => by
      have o : ∏ _k : PUnit, h (T.hom ≫ eSec G) ^ (1 : ℤ) = h (1 : T ⟶ G).left := by
        rw [Fintype.prod_unique, zpow_one, one_left]
      refine (DVR.prod_sum₂ (U := U) (K := thK ⊕ Fin 2) (K' := PUnit ⊕ PUnit) _
        (DVR.prod_sum₂ (U := U) (K := thK) (K' := Fin 2) _ (prod_cub x y y⁻¹ h) (DVR.prod_neg _ _ (prod_sym y h)))
        (DVR.prod_sum₂ (U := U) (K := PUnit) (K' := PUnit) _ o o)).trans ?_
      rw [mul_inv_cancel_right, mul_inv_cancel]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen P.L.L _ _ _ _
      (LB.mulGen P.L.L _ _ _ _ (LB.pullGen P.L.L (thφ G (x3 G)) thε P.c.t (lift x (lift y y⁻¹)).left)
        (LB.invGen P.L.L _ _ (LB.pullGen P.L.L _ _ P.sym y.left)))
      (LB.mulGen P.L.L _ _ _ _ r₀ r₀))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.c.isGen _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.sym_gen _))) (DVR.mulGen_isGen _ _ _ _ _ _ _ hr₀ hr₀))
  refine ⟨t, ht, fun T' ρ z J hJ => ?_⟩
  have e₀ : val r₀ ρ.left z J =
      val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig T'.hom z J :=
    (val_pull hJ _ _ _).trans (by rw [Over.w ρ])
  refine ((hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_cub P.c ρ hJ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e₀ e₀))))).trans ?_
  rw [kap0, sq, GrpObj.comp_inv, Over.comp_left]
end GlobalTheory.AddGeneric
