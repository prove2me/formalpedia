-- Prove2me | solution 1 for GlobalTheory.FamPull.exists_feGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:38:38.154303+00:00
-- url     : https://prove2.me/submissions/359c2d51-2373-483e-8450-5bd8b99152d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg
import Theorems.Thm_GlobalTheory_FamPull_prod_famB
import Theorems.Thm_GlobalTheory_TauPull_val_tauW
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_nsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_powGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.FamPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}
namespace GlobalTheory.FamPull
theorem _root_.solution (ψW : PsiOn D W) (k : ℕ) (mu α : D.X) :
    ∃ (K : Type) (_ : Fintype K) (φ : K → ((TW W ⊗ D.P.A).left ⟶ D.P.A.left)) (ε : K → ℤ)
      (u : LB.Gen (LB.LinComb D.P.L φ ε)), u.IsGen ∧
      FormEq (Sum.elim (fun i => (snd (TW W) D.P.A * cP D _ mu).left ≫ D.famφB α i) φ) (Sum.elim (DegPre.famε k) ε)
        (fun i => (snd (TW W) D.P.A).left ≫ D.famφB (α + k • mu) i) (DegPre.famε k) ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ TW W ⊗ D.P.A) (z : T.left) (J), Good D.P.L z J →
        val u ρ.left z J = feUnit D k mu α (ρ ≫ snd _ _) z J (fun χ => val (ψW.psi χ) (ρ ≫ fst _ _).left z J)
          (val (D.rigW W) (ρ ≫ fst _ _).left z J) := by
  let a : TW W ⊗ D.P.A ⟶ D.P.A := cP D _ α
  let m : TW W ⊗ D.P.A ⟶ D.P.A := cP D _ mu
  let x : TW W ⊗ D.P.A ⟶ D.P.A := snd _ _
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a m x k
  have hρ : (D.rigW W).IsGen := pullGen_isGen _ _ _ _ D.rig_gen _
  refine ⟨_, inferInstance, _, _, LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift x m)).left)))
      (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (ψW.tau mu α) (LB.mulGen D.P.L _ _ _ _
        (GeneratorPullback.powGen D.P.L _ _ (ψW.psi mu) k) (GeneratorPullback.powGen D.P.L _ _ (D.rigW W) k))) (fst (TW W) D.P.A).left),
    mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _)))
      (pullGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
        (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (ψW.psi_gen _)
          (invGen_isGen _ _ _ _ (ψW.psi_gen _))) (invGen_isGen _ _ _ _ (ψW.psi_gen _))) (invGen_isGen _ _ _ _ hρ))
        (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (ψW.psi_gen mu) k) (powGen_isGen _ _ _ _ hρ k))) _),
    fun U _ h => ?_, fun T ρ z J hJ => ?_⟩
  · have p₁ := prod_cub a x m h
    have p₃ := prod_famB D x (α + k • mu) k h
    have p₄ := prod_famB D (x * m) α k h
    have a₁ : ∀ χ, (fst (TW W) D.P.A).left ≫ (toUnit (TW W) ≫ D.c χ).left = (cP D (TW W ⊗ D.P.A) χ).left := fun χ =>
      congrArg (fun q => q.left) (comp_cP D (fst (TW W) D.P.A) χ)
    have a₂ : (fst (TW W) D.P.A).left ≫ (toUnit (TW W)).left ≫ eSec D.P.A = (1 : TW W ⊗ D.P.A ⟶ D.P.A).left :=
      congrArg (fun q : TW W ⊗ D.P.A ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (fst (TW W) D.P.A))
    refine Eq.trans (prod_sum₂ (K := Fin 4) (U := U) _ p₄ (prod_sum₂ (K := Fin 8 ⊕ thK) (U := U) _
      (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) rfl)) (Eq.trans ?_ p₃.symm)
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
    rw [add_comm mu α, cPoint_add, cPoint_add, cPoint_nsmul, ← _root_.mul_assoc (cP D _ α), mul_comm x m]
    apply Additive.ofMul.injective
    simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, m, x]
    module
  · refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      ((congrArg₂ (· * ·) (vN T ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _)))).trans ?_))
      ((val_pull hJ _ _ _).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (TauPull.val_tauW ψW _ hJ _ _)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (map_pow _ _ _) (map_pow _ _ _)))))))
    rw [comp_cP, comp_cP]
end GlobalTheory.FamPull
