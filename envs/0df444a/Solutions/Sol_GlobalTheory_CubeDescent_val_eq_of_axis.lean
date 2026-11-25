-- Prove2me | solution 1 for GlobalTheory.CubeDescent.val_eq_of_axis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:17:02.679004+00:00
-- url     : https://prove2.me/submissions/babaca24-a086-44d4-bed3-e6e73407217f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Theorems.Thm_GlobalTheory_CubeDescent_val_eq_of_section
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.CubeDescent
variable {S X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {Q : Over S}
  {φ : K → (Q.left ⟶ X)} {ε : K → ℤ}
variable {A : Over S} [GrpObj A]
namespace GlobalTheory.CubeDescent
theorem _root_.solution (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (σ : A ⊗ A ⊗ A ⟶ Q)
    (H₁ : FormEq (fun k => (lift (1 : A ⟶ A) (lift 1 1) ≫ σ).left ≫ φ k) ε
      (fun k => (lift (𝟙 A) (lift 1 1) ≫ σ).left ≫ φ k) ε)
    {T : Over S} (x x' : T ⟶ A)
    (H₂ : ∀ (T' : Over S) (ρ : T' ⟶ T) (y w : T' ⟶ A) (k : K),
      (lift (ρ ≫ x') (lift y w) ≫ σ).left ≫ φ k = (lift (ρ ≫ x) (lift y w) ≫ σ).left ≫ φ k)
    (y w : T ⟶ A) (z : T.left) (J) (hJ : Good L z J) :
    val u (lift x (lift y w) ≫ σ).left z J = val u (lift x' (lift y w) ≫ σ).left z J := by
  have face : ∀ (v : T ⟶ A) (z : T.left) (J), Good L z J →
      val u (lift v (lift 1 1) ≫ σ).left z J = val u (lift (1 : T ⟶ A) (lift 1 1) ≫ σ).left z J := by
    intro v z J hJ
    have := val_eq_of_section hL hu (toUnit A) η[A] (toUnit_unique _ _) (hG _ _ hA).2
      (lift (𝟙 A) (lift 1 1) ≫ σ) (lift (1 : A ⟶ A) (lift 1 1) ≫ σ) H₁ (fun y J _ => by
        congr 2
        simp [comp_lift_assoc, Hom.one_def]) v z J hJ
    simpa only [comp_lift_assoc, comp_lift, Category.comp_id, MonObj.comp_one] using this
  have := val_eq_of_section hL hu (snd A (A ⊗ T) ≫ snd A T) (lift 1 (lift 1 (𝟙 T))) (by simp)
    (surj_comp (surj_snd hG hA _) (surj_snd hG hA _))
    (lift ((snd A (A ⊗ T) ≫ snd A T) ≫ x) (lift (fst _ _) (snd _ _ ≫ fst _ _)) ≫ σ)
    (lift ((snd A (A ⊗ T) ≫ snd A T) ≫ x') (lift (fst _ _) (snd _ _ ≫ fst _ _)) ≫ σ)
    (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ ε k) (H₂ _ _ _ _ k))
    (fun z J hJ => by
      have e := (face x z J hJ).trans (face x' z J hJ).symm
      simpa only [comp_lift_assoc, comp_lift, lift_fst, lift_snd_assoc, lift_snd, Category.assoc,
        Category.id_comp] using e)
    (lift y (lift w (𝟙 T))) z J hJ
  simpa only [comp_lift_assoc, comp_lift, lift_fst, lift_snd_assoc, lift_snd, Category.assoc,
    Category.id_comp] using this
end GlobalTheory.CubeDescent
