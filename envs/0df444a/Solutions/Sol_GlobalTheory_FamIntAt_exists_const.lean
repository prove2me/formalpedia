-- Prove2me | solution 1 for GlobalTheory.FamIntAt.exists_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:42:51.733087+00:00
-- url     : https://prove2.me/submissions/5b04f5a5-00ce-43bb-8cb7-7f8cb68a8661

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
import Theorems.Thm_GlobalTheory_FamIntAt_exists_psi
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_UUA_val_powGen__89687e20c37b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_cQ_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_psi_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_val_famMult
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_genSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_mulSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_powSec


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
theorem _root_.solution {I : Ideal R} (D : DegData R I) (k : ℕ) (ρ mu : D.toPre.X) (r : R)
    (Φ : LB.Sec (LB.LinComb D.toPre.P.L (Y := Spec (CommRingCat.of R)) (K := PUnit) (fun _ => (D.toPre.c ρ).left)
      (fun _ => - -1)))
    (hΦ : ∀ (T : Scheme.{0}) (τ : T ⟶ (TK R).left) (z : T) (J), Good D.toPre.P.L z J →
      sval Φ (τ ≫ jK R) z J = gs (τ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) *
        ((val (D.toPre.psi ρ) τ z J)⁻¹).val) :
    ∃ (Ix : Type) (_ : Fintype Ix) (φV : Ix → (Spec (CommRingCat.of R) ⟶ D.toPre.P.A.left)) (εV : Ix → ℤ)
      (w : LB.Sec (LB.LinComb D.toPre.P.L φV εV)),
      (∀ (U : Type) [CommGroup U] (h : (D.toPre.P.A.left ⟶ D.toPre.P.A.left) → U),
        ∏ i, h (D.toPre.P.A.hom ≫ φV i) ^ εV i =
          (h (cQ D.toPre D.toPre.P.A ρ * cQ D.toPre D.toPre.P.A mu).left)⁻¹ * h (cQ D.toPre D.toPre.P.A ρ).left *
            h (cQ D.toPre D.toPre.P.A mu).left * (h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left)⁻¹ *
            (h (cQ D.toPre D.toPre.P.A mu).left ^ (k + 1))⁻¹ * h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left ^ (k + 1)) ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) (FractionRing R)) (z : T.left) (J),
        Good D.toPre.P.L z J → sval w ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z J =
          gs ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) *
            (val (DegPre.famMult D.toPre (FractionRing R) (k + 1) mu ρ) σ.left z J).val := by
  choose Ψ hΨ using exists_psi D
  refine ⟨_, inferInstance, _, _, SectionArithmetic.mulSec (SectionArithmetic.mulSec (Ψ (mu + ρ)) Φ) (SectionArithmetic.mulSec (SectionArithmetic.powSec fun _ : Fin k => Ψ mu)
    (SectionArithmetic.powSec (L := D.toPre.P.L) (Y := Spec (CommRingCat.of R)) (K := PUnit) (φ := fun _ => eSec D.toPre.P.A)
      (ε := fun _ => 1) fun _ : Fin k => Geo.Tor.genSec D.toPre.rig D.toPre.rig_gen)), fun U _ h => ?_,
    fun T σ z J hJ => ?_⟩
  · have hc : ∀ χ, D.toPre.P.A.hom ≫ (D.toPre.c χ).left = (cQ D.toPre D.toPre.P.A χ).left := fun χ => by simp [cQ]
    have he : D.toPre.P.A.hom ≫ eSec D.toPre.P.A = (1 : D.toPre.P.A ⟶ D.toPre.P.A).left := by
      rw [Hom.one_def]; simp [eSec]
    simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, hc, he,
      cQ_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_punit, Fintype.card_prod,
      _root_.mul_one]
    rw [mul_comm (cQ D.toPre D.toPre.P.A mu)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module
  · have e : val D.toPre.rigK (σ.left ≫ jFK (R := R) (FractionRing R)) z J =
      val D.toPre.rig ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z J := val_pull hJ _ _ _
    refine ((SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
      ((SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·) (hΨ _ T σ z J hJ) (hΦ _ _ z J hJ)))
      ((SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
        ((SectionArithmetic.sval_powSec _ _ z hJ).trans (Finset.prod_congr rfl fun _ _ => hΨ _ T σ z J hJ))
        ((SectionArithmetic.sval_powSec _ _ z hJ).trans (Finset.prod_congr rfl fun _ _ =>
          (sval_genSec _ _ _ z hJ).trans (congrArg Units.val e.symm))))))).trans ?_
    rw [val_famMult σ hJ, UUA.val_powGen', UUA.val_powGen', UUA.psi_add σ hJ, Finset.prod_const, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination (gs ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) *
      (val (D.toPre.tau mu ρ) (σ.left ≫ jFK (R := R) (FractionRing R)) z J).val *
      (val (D.toPre.psi mu) (σ.left ≫ jFK (R := R) (FractionRing R)) z J).val ^ (k + 1) *
      (val D.toPre.rigK (σ.left ≫ jFK (R := R) (FractionRing R)) z J).val ^ (k + 1)) *
      (val (D.toPre.psi ρ) (σ.left ≫ jFK (R := R) (FractionRing R)) z J).mul_inv
end GlobalTheory.FamIntAt
