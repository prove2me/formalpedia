-- Prove2me | solution 1 for GlobalTheory.UU.exists_cubical_addition_factor_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:57:22.376342+00:00
-- url     : https://prove2.me/submissions/a565c8cc-78c3-4253-ab12-cebf42e1e3bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCubicalAdditionFactorGenerator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) {Y : Over S}
    (a b : Y ⟶ G) :
    ∃ κ : LB.Gen (LB.LinComb P.L.L (K := Fin 4) ![a.left, b.left, (a * b).left, (a * b⁻¹).left] ![2, 2, -1, -1]),
      κ.IsGen ∧ ∀ (T : Over S) (ρ : T ⟶ Y) (z : T.left) (J), Good P.L.L z J →
        val κ ρ.left z J = kap0 P.c P.sym z J (ρ ≫ a) (ρ ≫ b) := by
  let cu := LB.pullGen P.L.L (thφ G (x3 G)) thε P.c.t (lift a (lift b b⁻¹)).left
  let sy := LB.invGen P.L.L _ _ (LB.pullGen P.L.L _ _ P.sym b.left)
  let rg := LB.pullGen P.L.L (fun _ : PUnit => eSec G) (fun _ => 1) P.L.rig Y.hom
  have gc : cu.IsGen := DVR.pullGen_isGen _ _ _ _ P.c.isGen _
  have gy : sy.IsGen := DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.sym_gen _)
  have gr : rg.IsGen := DVR.pullGen_isGen _ _ _ _ P.L.rigGen _
  obtain ⟨κ, hκ, hv⟩ := exists_gen P.L.isLB (K' := Fin 4)
    (φ' := ![a.left, b.left, (a * b).left, (a * b⁻¹).left]) (ε' := ![2, 2, -1, -1]) (fun U _ h => by
      have e₂ : ∏ k : Fin 2, h (b.left ≫ ![(ι[G]).left, 𝟙 G.left] k) ^ (-(![1, -1] : Fin 2 → ℤ) k) =
          (h (b⁻¹).left * (h b.left)⁻¹)⁻¹ := by
        rw [← prod_sym b h]; simp only [zpow_neg, Finset.prod_inv_distrib]
      have e₃ : ∏ _k : PUnit, h (Y.hom ≫ eSec G) ^ (1 : ℤ) = h (1 : Y ⟶ G).left := by
        rw [Fintype.prod_unique, zpow_one, one_left]
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans
        (congrArg₂ (· * ·) (prod_cub a b b⁻¹ h) e₂)) ((Fintype.prod_sum_type _).trans
        (congrArg₂ (· * ·) e₃ e₃)))).trans ?_
      rw [mul_inv_cancel_right, mul_inv_cancel b]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen P.L.L _ _ _ _ (LB.mulGen P.L.L _ _ _ _ cu sy) (LB.mulGen P.L.L _ _ _ _ rg rg))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ gc gy) (DVR.mulGen_isGen _ _ _ _ _ _ _ gr gr))
  refine ⟨κ, hκ, fun T ρ z J hJ => (hv _ _ z J hJ).trans ?_⟩
  have vr : val rg ρ.left z J =
      val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig T.hom z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Over.w ρ]
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    (val_cub P.c ρ hJ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) vr vr)))).trans ?_
  rw [kap0, GrpObj.comp_inv, pow_two]
  rfl
end GlobalTheory.UU
