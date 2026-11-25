-- Prove2me | solution 1 for GlobalTheory.FamIntAt.exists_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:52:00.472298+00:00
-- url     : https://prove2.me/submissions/3710228d-57ec-4cde-8f21-575bce41095c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrime
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_cQ_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_cQ_nsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_comp_cQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_prod_famB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_sval_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_mulSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_pullSec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FamIntAt
variable {R : Type} [CommRing R] [IsDomain R]
open SectionScalarValuation
namespace GlobalTheory.FamIntAt
theorem _root_.solution (D : DegPre R) (k : ℕ) (α mu : D.X) {Ix : Type} [Fintype Ix]
    {φV : Ix → (Spec (CommRingCat.of R) ⟶ D.P.A.left)} {εV : Ix → ℤ} (w : LB.Sec (LB.LinComb D.P.L φV εV))
    (hC : ∀ (U : Type) [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U), ∏ i, h (D.P.A.hom ≫ φV i) ^ εV i =
      (h (cQ D D.P.A α * cQ D D.P.A mu).left)⁻¹ * h (cQ D D.P.A α).left * h (cQ D D.P.A mu).left *
        (h (1 : D.P.A ⟶ D.P.A).left)⁻¹ * (h (cQ D D.P.A mu).left ^ k)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left ^ k)
    (s : D.SecB k α) : ∃ f : D.SecB k (α + k • mu),
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
        sval f ρ.left z J = sval s (ρ * cQ D T mu).left z J * (cubN (cubV D.cub z J) k (cQ D T α) (cQ D T mu) ρ *
          (cubV D.cub z J (cQ D T α) ρ (cQ D T mu))⁻¹).val * sval w (ρ.left ≫ D.P.A.hom) z J := by
  set a : D.P.A ⟶ D.P.A := cQ D _ α with ha
  set m : D.P.A ⟶ D.P.A := cQ D _ mu with hm
  have hα' : cQ D D.P.A (α + k • mu) = a * m ^ k := by rw [cQ_add, cQ_nsmul]
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a m (𝟙 D.P.A) k
  have hu := mulGen_isGen _ _ _ _ _ _ _ hN
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen (lift a (lift (𝟙 D.P.A) m)).left))
  obtain ⟨f, vf⟩ := exists_sec D.P.isLB (φ' := D.famφB (α + k • mu)) (ε' := DegPre.famε k) (fun U _ h => by
      have p₁ := prod_cub a (𝟙 D.P.A) m h
      have p₂ := hC U h
      have p₃ := prod_famB D (𝟙 _) (α + k • mu) k h
      have p₄ := prod_famB D (𝟙 D.P.A * m) α k h
      have e₃ : ∀ i, Over.Hom.left (𝟙 D.P.A) ≫ D.famφB (α + k • mu) i = D.famφB (α + k • mu) i := fun i => by simp
      simp only [e₃] at p₃
      rw [hα'] at p₃
      rw [← ha] at p₄
      have q₁ : 𝟙 D.P.A * (a * m ^ k) = a * m ^ k * 𝟙 D.P.A := mul_comm _ _
      have q₂ : 𝟙 D.P.A * m * a = a * 𝟙 D.P.A * m := by rw [mul_comm _ a, ← _root_.mul_assoc]
      have q₃ : m * 𝟙 D.P.A = 𝟙 D.P.A * m := mul_comm _ _
      rw [q₁] at p₃
      rw [q₂] at p₄
      have p₀ : ∏ i : Fin 8, h ((![(a * m ^ k * 𝟙 D.P.A).left, (a * m ^ k).left, (a * 𝟙 D.P.A).left, a.left,
          (m * 𝟙 D.P.A).left, m.left, Over.Hom.left (𝟙 D.P.A), (1 : D.P.A ⟶ D.P.A).left] : Fin 8 → _) i) ^
            (![1, -1, -1, 1, -k, k, k, -k] : Fin 8 → ℤ) i =
          h (a * m ^ k * 𝟙 D.P.A).left * (h (a * m ^ k).left)⁻¹ * (h (a * 𝟙 D.P.A).left)⁻¹ * h a.left *
            (h (𝟙 D.P.A * m).left ^ k)⁻¹ * h m.left ^ k * h (Over.Hom.left (𝟙 D.P.A)) ^ k *
            (h (1 : D.P.A ⟶ D.P.A).left ^ k)⁻¹ := by
        simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, q₃,
          zpow_neg, zpow_one, zpow_natCast, _root_.mul_one, _root_.mul_assoc]
      refine Eq.trans (prod_sum₂ (K := Fin 4 ⊕ (Fin 8 ⊕ thK)) (K' := Ix) (U := U) _
        (prod_sum₂ (K := Fin 4) (K' := Fin 8 ⊕ thK) (U := U) _ p₄
          (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ p₀ (prod_neg _ _ p₁))) p₂) (Eq.trans ?_ p₃.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (SectionArithmetic.mulSec (pullMulSec s (𝟙 D.P.A * m).left _ hu) (SectionArithmetic.pullSec w D.P.A.hom))
  refine ⟨f, fun T ρ z J hJ => ?_⟩
  refine (vf _ _ z J hJ).trans ((SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    ((sval_pullMulSec _ _ _ hu _ z hJ).trans (congrArg₂ (· * ·) ?_ (congrArg Units.val ?_)))
    (SectionArithmetic.sval_pullSec _ _ _ z hJ)))
  · rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, hm, comp_cQ]
  · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vN T ρ z J hJ)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _))))).trans ?_
    rw [ha, hm, comp_cQ, comp_cQ, Category.comp_id]
end GlobalTheory.FamIntAt
