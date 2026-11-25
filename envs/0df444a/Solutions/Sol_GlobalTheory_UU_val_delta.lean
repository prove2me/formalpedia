-- Prove2me | solution 1 for GlobalTheory.UU.val_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:10:29.031939+00:00
-- url     : https://prove2.me/submissions/8dbfaf55-62d0-4b41-bf11-89754ce0b7cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ChainVal
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_nsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_u
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_fam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_trF_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_pr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val


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
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UU
theorem _root_.solution (hG : GlobalFnsSt) (k : ℕ) (α mu : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val u ρ.left z J = uVal D F k α (cP D _ mu) ρ z J *
      val (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (ρ ≫ fst _ _).left z J := by
  have z₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
  have z₃ : (DegPre.zF D F ≫ DegPre.trF D F mu) ≫ DegPre.prB D F = cP D _ mu := by
    rw [trF_eq, Category.assoc, tr_pr, MonObj.comp_mul, z₂, ← Category.assoc, z₁, Category.id_comp, _root_.one_mul]
  have H := gen_u D F hG k α (α + k • mu) (cP D _ mu) (by rw [cPoint_add, cPoint_nsmul])
    (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (pullGen_isGen _ _ _ _ hu _) (fun U _ h => by
      have p₃ := prod_fam D F (DegPre.zF D F) (α + k • mu) k h
      have p₄ := prod_fam D F (DegPre.zF D F ≫ DegPre.trF D F mu) α k h
      rw [z₂, _root_.mul_one] at p₃
      rw [z₃] at p₄
      simp only [Over.comp_left, Category.assoc] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)) ?_
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
  rw [← trF_eq] at H
  exact H.2 u hu (corr_of_val D.P.isLB fun _ _ _ => rfl) T ρ z J hJ
end GlobalTheory.UU
