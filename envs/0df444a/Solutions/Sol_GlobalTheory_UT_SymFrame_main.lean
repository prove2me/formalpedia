-- Prove2me | solution 1 for GlobalTheory.UT.SymFrame.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:57:18.294803+00:00
-- url     : https://prove2.me/submissions/a9a020dc-a190-45d1-911a-633b8c8a0221

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_mul
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_inv
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_pow
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_congr
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_out
import Theorems.Thm_GlobalTheory_UT_SymFrame_grep_gen
import Theorems.Thm_GlobalTheory_UT_SymFrame_normd_unique
import Theorems.Thm_GlobalTheory_UT_SymFrame_grep_kap
import Theorems.Thm_GlobalTheory_UT_SymFrame_grep_nu
import Theorems.Thm_GlobalTheory_UT_SymFrame_exists_kap
import Theorems.Thm_GlobalTheory_UT_SymFrame_exists_nu
import Theorems.Thm_GlobalTheory_UT_SymFrame_univ_identity
import Theorems.Thm_GlobalTheory_UT_SymFrame_tau_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_chain_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_gt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.SymFrame
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Y : Over (Spec (CommRingCat.of R))}
variable {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UT.SymFrame
theorem _root_.solution : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (N : ℕ), Odd N → ∀ p : QkPt D.toPre F N, (∃ w, TXFrame N p w) ∧ ∀ w w', TXFrame N p w → TXFrame N p w' → ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J := by
  rintro ⟨hL, -⟩ R _ _ _ I hI D F _ _ _ N ⟨k, hk⟩ p
  haveI : IsNoetherianRing R := hI.1
  obtain ⟨ν, hν⟩ := exists_nu (D := D.toPre) hL.mulPull N
  obtain ⟨κ, hκ⟩ := exists_kap (D := D.toPre) hL.mulPull N
  have alg : ∀ {U : Type} [CommGroup U] (x y : U), x ^ 2 = y ^ 2 → x ^ N = y ^ N → x = y := fun x y h₂ hN => by
    rw [hk, pow_succ, pow_succ, pow_mul, pow_mul, h₂] at hN
    exact mul_left_cancel hN
  refine ⟨?_, fun w w' hw hw' z J hJ => alg _ _ ((hw.2.1 ν hν z J hJ).trans (hw'.2.1 ν hν z J hJ).symm)
    (mul_right_cancel ((hw.2.2 κ hκ z J hJ).trans (hw'.2.2 κ hκ z J hJ).symm))⟩
  let ρ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  have hy : cP D.toPre _ p.y = p.g.b ^ N := cPoint_y p
  have rs : GRep D.toPre.P.L (TF (R := R) F) (fun _ _ h => (h (p.g.b ^ N * p.g.b).left)⁻¹ * h (p.g.b ^ N).left *
      h p.g.b.left * (h (1 : TF (R := R) F ⟶ D.toPre.P.A).left)⁻¹) (fun _ r z J => val (p.g.s p.y) r.left z J) :=
    ⟨_, inferInstance, _, _, p.g.s p.y, p.g.isGen _, fun U _ h => by rw [prod_gt, hy], fun _ _ _ _ _ => rfl⟩
  have rψ : GRep D.toPre.P.L (TF (R := R) F) (fun _ _ h => (h (p.g.b ^ N).left)⁻¹)
      (fun _ r z J => val (D.toPre.psi p.y) (r.left ≫ ρ.left) z J) :=
    (grep_gen (D.toPre.psi p.y) (D.toPre.psi_gen _) ρ.left).congr (fun U _ h => by
      rw [Fintype.prod_unique, zpow_neg_one, ← hy, ← comp_cP D.toPre ρ]; rfl) (fun _ _ _ _ _ => rfl)
  have rr : GRep D.toPre.P.L (TF (R := R) F) (fun _ _ h => h (1 : TF (R := R) F ⟶ D.toPre.P.A).left)
      (fun T r z J => rigV D.toPre (r.left ≫ (TF (R := R) F).hom) z J) :=
    (grep_gen (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1) D.toPre.rig D.toPre.rig_gen
      (TF (R := R) F).hom).congr (fun U _ h => by rw [Fintype.prod_unique, zpow_one]; rfl) (fun _ _ _ _ _ => rfl)
  obtain ⟨w, hw, vw⟩ := (((rψ.mul rr).mul (grep_kap κ hκ.1 p.g.b).inv).mul
    ((rs.mul (grep_nu ν hν.1 p.g.b)).pow k).inv).out D.toPre.P.isLB (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε N)
    (fun U _ h => by
      rw [Fin.prod_univ_two]
      show _ = h (1 : TF (R := R) F ⟶ D.toPre.P.A).left ^ (N : ℤ) * h p.g.b.left ^ (-(N : ℤ))
      have hk' : (N : ℤ) = 2 * k + 1 := by exact_mod_cast hk
      rw [hk']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
  have key : ∀ z J, Good D.toPre.P.L z J →
      val w (𝟙 _) z J ^ 2 = val (p.g.s p.y) (𝟙 _) z J * val ν p.g.b.left z J ∧
      val w (𝟙 _) z J ^ N * val κ p.g.b.left z J =
        @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.toPre.psi p.y) (jFK (R := R) F) z J) *
          rigV D.toPre (TF (R := R) F).hom z J := fun z J hJ => by
    have e₀ := vw _ (𝟙 _) z J hJ
    beta_reduce at e₀
    rw [Over.id_left, Category.id_comp, Category.id_comp, Category.id_comp] at e₀
    have e₁ := (congrArg₂ (· * ·) (tau_self D.psi_even D.tau_bimult p.y hJ) rfl).symm.trans
      (chain_val (𝟙 (TF (R := R) F)) hJ p p.y)
    rw [Category.id_comp, hy] at e₁
    have e₂ := univ_identity hL.globalFns hν hκ p.g.b z J hJ
    have alg₂ : ∀ {U : Type} [CommGroup U] (w ψ r κ s ν c σ c' : U), w = ψ * r * κ⁻¹ * ((s * ν) ^ k)⁻¹ →
        c * σ * (ψ * r) ^ 2 * c' = s ^ N → c * σ * c' * ν ^ N * κ ^ 2 = 1 → w ^ 2 = s * ν ∧ w ^ N * κ = ψ * r := by
      intro U _ w ψ r κ s ν c σ c' h₀ h₁ h₂
      have a₁ := congrArg Additive.ofMul h₁
      have a₂ := congrArg Additive.ofMul h₂
      subst h₀ hk
      constructor <;> apply Additive.ofMul.injective <;>
        simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at a₁ a₂ ⊢
      · linear_combination (norm := module) a₁ - a₂
      · linear_combination (norm := module) k • a₁ - k • a₂
    exact alg₂ _ _ _ _ _ _ _ _ _ e₀ e₁ e₂
  exact ⟨w, hw, fun ν' hν' z J hJ => (key z J hJ).1.trans
      (congrArg _ (normd_unique hL.globalFns hν hν' _ z J hJ)),
    fun κ' hκ' z J hJ => (congrArg _ (normd_unique hL.globalFns hκ' hκ _ z J hJ)).trans (key z J hJ).2⟩
end GlobalTheory.UT.SymFrame
