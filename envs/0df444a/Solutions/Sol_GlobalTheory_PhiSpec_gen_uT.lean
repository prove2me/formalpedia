-- Prove2me | solution 1 for GlobalTheory.PhiSpec.gen_uT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:51:56.083883+00:00
-- url     : https://prove2.me/submissions/fef98acf-ac6f-4910-886a-b53e8789fc48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiSpecialises
import Theorems.Thm_GlobalTheory_PhiSpec_trT_snd
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_prod_famB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PhiSpec
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.PhiSpec
theorem _root_.solution (k : ℕ) (α α' : D.X) (m : T ⟶ D.P.A)
    (hα : cP D _ α' = cP D _ α * m ^ k) {K : Type} [Fintype K]
    {φ : K → (T.left ⟶ D.P.A.left)} {ε : K → ℤ}
    (vO : LB.Gen (LB.LinComb D.P.L φ ε)) (hvO : vO.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
      (h (cP D _ α * m).left)⁻¹ * h (cP D _ α).left * h m.left * (h (1 : T ⟶ D.P.A).left)⁻¹ *
        (h m.left ^ k)⁻¹ * h (1 : T ⟶ D.P.A).left ^ k) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (fun i => (snd T D.P.A).left ≫ D.famφB α' i)
        (fun i => (trT D m ≫ snd _ _).left ≫ D.famφB α i)) (DegPre.deltaε k)), u.IsGen ∧
      ∀ (T₁ : Over (Spec (CommRingCat.of R))) (ρ : T₁ ⟶ T ⊗ D.P.A) (z : T₁.left) (J), Good D.P.L z J →
        val u ρ.left z J = uT D k α m ρ z J * val vO (ρ ≫ fst _ _).left z J := by
  let a : T ⊗ D.P.A ⟶ D.P.A := cP D _ α
  let mm : T ⊗ D.P.A ⟶ D.P.A := fst _ _ ≫ m
  let x : T ⊗ D.P.A ⟶ D.P.A := snd _ _
  have hα' : cP D (T ⊗ D.P.A) α' = a * mm ^ k := by
    rw [← comp_cP D (fst T D.P.A), hα]
    exact (map_mul (preHom (fst T D.P.A)) _ _).trans
      (congrArg₂ (· * ·) (comp_cP D _ α) (map_pow (preHom (fst T D.P.A)) _ _))
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a mm x k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.P.isLB (φ' := Sum.elim (fun i => (snd T D.P.A).left ≫ D.famφB α' i)
      (fun i => (trT D m ≫ snd _ _).left ≫ D.famφB α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a x mm h
      have p₂ := hF U (fun q => h ((fst T D.P.A).left ≫ q))
      have p₃ := SectionScalarValuation.prod_famB D (snd T D.P.A) α' k h
      have p₄ := SectionScalarValuation.prod_famB D (trT D m ≫ snd _ _) α k h
      have q₁ : (fst T D.P.A).left ≫ (cP D _ α * m).left = (a * mm).left :=
        congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left)
          ((MonObj.comp_mul (fst T D.P.A) (cP D _ α) m).trans
            (congrArg (· * mm) (comp_cP D (fst T D.P.A) α)))
      have q₂ : (fst T D.P.A).left ≫ (cP D _ α).left = a.left :=
        congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left) (comp_cP D (fst T D.P.A) α)
      have q₃ : (fst T D.P.A).left ≫ (1 : T ⟶ D.P.A).left = (1 : T ⊗ D.P.A ⟶ D.P.A).left :=
        congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (fst T D.P.A))
      have q₄ : (fst T D.P.A).left ≫ m.left = mm.left := rfl
      rw [q₁, q₂, q₃, q₄] at p₂
      have c₁ : SectionScalarValuation.cQ D (T ⊗ D.P.A) α' = a * mm ^ k := hα'
      have c₂ : SectionScalarValuation.cQ D (T ⊗ D.P.A) α = a := rfl
      rw [c₁] at p₃
      rw [c₂] at p₄
      conv at p₄ => rhs; rw [trT_snd]
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := K) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)
      have r1 : x * (a * mm ^ k) = a * mm ^ k * x := mul_comm _ _
      have r2 : x * mm * a = a * x * mm := by rw [mul_comm, ← _root_.mul_assoc]
      have r3 : mm * x = x * mm := mul_comm _ _
      rw [r1, r2, r3]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift x mm)).left)))
      (LB.pullGen D.P.L _ _ vO (fst T D.P.A).left))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _
      (pullGen_isGen _ _ _ _ D.cub.isGen _))) (pullGen_isGen _ _ _ _ hvO _))
  refine ⟨u₀, hu₀, fun T₁ ρ z J hJ => ?_⟩
  refine (vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (vN T₁ ρ z J hJ) ((val_inv _ _).trans
      (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _)))).trans ?_)) (val_pull hJ _ _ _)))
  rw [uT, ← comp_cP D ρ α]
end GlobalTheory.PhiSpec
