-- Prove2me | solution 1 for GlobalTheory.integralFamily_at_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:44:35.131314+00:00
-- url     : https://prove2.me/submissions/b62ec357-8529-4dd6-9c8c-e6dd6aa6baea

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
import Theorems.Thm_GlobalTheory_FamIntAt_sval_secScale
import Theorems.Thm_GlobalTheory_FamIntAt_exists_inv
import Theorems.Thm_GlobalTheory_FamIntAt_exists_move
import Theorems.Thm_GlobalTheory_FamIntAt_exists_const
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam__eq_3a137bedd551
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_secScal_of_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_sval_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_exists_fam_rep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_sval_zero_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_uVal_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_exists_const


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
open FamIntAt SectionScalarValuation
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (PsiOn D.toPre W) → ∀ p : (Spec (CommRingCat.of R)), p ∈ W → ∀ (k : ℕ), 1 ≤ k → ∀ (ρ : D.toPre.X) (s : D.toPre.SecB k ρ), ∃ r : R, r ∉ p.asIdeal ∧ ∃ (F : Fam D.toPre (FractionRing R) k) (f : ∀ α, D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ j, (f ρ).f j = resTop _ (scal D.toPre.P.A.hom r) * (s).f j) ∧ ∀ β, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (f β).f j = 0 := by
  intro hG R _ _ I _ D W ⟨ψ⟩ p hp k hk ρ s
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨r, hr, Φ₀, hΦ₀⟩ := exists_inv ψ ρ p hp
  let β : D.toPre.SecB (k + 1) ρ := SecOps.secScale (scal D.toPre.P.A.hom r) s
  obtain ⟨σ, hσ⟩ := exists_sec hL (φ' := DegPre.famφ D.toPre (FractionRing R) ρ) (ε' := DegPre.famε (k + 1))
    (fun U _ g => Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq])
    (SectionArithmetic.pullSec β (DegPre.prB D.toPre (FractionRing R)).left)
  obtain ⟨Φ, hΦ, hΦ0⟩ := UUA.exists_fam_rep (F := FractionRing R) hG D.tau_bimult (k + 1) ρ (fun a b h => by
    have h' : ((k + 1 : ℕ) : ℤ) • a = ((k + 1 : ℕ) : ℤ) • b := by
      rw [natCast_zsmul, natCast_zsmul]; exact add_left_cancel h
    exact smul_right_injective D.toPre.X (by omega : ((k + 1 : ℕ) : ℤ) ≠ 0) h') σ
  have key : ∀ α : D.toPre.X, ∃ f : D.toPre.SecB (k + 1) α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε (k + 1)) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε (k + 1)) f (DegPre.prB D.toPre (FractionRing R)).left 1 ∧
      (∀ h : ρ = α, f = h ▸ β) ∧ ((∀ mu, ρ + (k + 1) • mu ≠ α) → ∀ j, f.f j = 0) := by
    intro α
    by_cases hα : ρ = α
    · subst hα
      refine ⟨β, secScal_of_sval hL fun y J hJ => ?_, fun _ => rfl, fun h => absurd (by simp) (h 0)⟩
      rw [hΦ]
      exact ((hσ _ _ y J hJ).trans (SectionArithmetic.sval_pullSec _ _ _ y hJ)).symm
    by_cases hc : ∃ mu, ρ + (k + 1) • mu = α
    · obtain ⟨mu, rfl⟩ := hc
      obtain ⟨Ix, _, φV, εV, w, hC, hw⟩ := exists_const D k ρ mu r Φ₀ hΦ₀
      obtain ⟨f, hf⟩ := exists_move D.toPre (k + 1) ρ mu w hC s
      refine ⟨f, secScal_of_sval hL fun y J hJ => ?_, fun h => absurd h hα, fun h => absurd rfl (h mu)⟩
      obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D.toPre) (F := FractionRing R) hG (k + 1) mu ρ
      have e₁ := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (Φ.fe mu ρ u hu hc) _ (𝟙 _) y J hJ
      have e₂ := hv u hu hc _ (𝟙 _) y J hJ
      rw [uVal_id, Over.id_left, Category.id_comp, comp_cP] at e₂
      have e₃ := hf _ (DegPre.prB D.toPre (FractionRing R)) y J hJ
      have e₄ := hw _ (fst (TF (R := R) (FractionRing R)) D.toPre.P.A) y J hJ
      have a₁ : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom =
          ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
        rw [Over.w, Category.assoc]
        exact (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm
      have a₂ : (DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.prB D.toPre (FractionRing R)).left =
          (DegPre.prB D.toPre (FractionRing R) * cQ D.toPre _ mu).left := by
        rw [← Over.comp_left, DegPre.trF, DegPre.prB, lift_snd]
        rfl
      have a₃ : (DegPre.prB D.toPre (FractionRing R) * cQ D.toPre _ mu).left ≫ D.toPre.P.A.hom =
          ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R :=
        (Over.w _).trans ((Over.w _).symm.trans a₁)
      have e₅ : sval σ (DegPre.trF D.toPre (FractionRing R) mu).left y J =
          gs (((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) y ⊤
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) *
          sval s (DegPre.prB D.toPre (FractionRing R) * cQ D.toPre _ mu).left y J := by
        refine (hσ _ _ y J hJ).trans ((SectionArithmetic.sval_pullSec _ _ _ y hJ).trans ?_)
        rw [a₂, ← a₃]
        exact (sval_secScale _ _ _ y hJ).trans (congrArg₂ (· * ·) (gs_pull _ D.toPre.P.A.hom y ⊤ trivial _) rfl)
      rw [a₁, e₄] at e₃
      rw [Category.id_comp, hΦ, e₅, e₂, Units.val_mul] at e₁
      rw [Category.id_comp, e₃, e₁]
      exact (mul_left_comm _ _ _).trans (by rw [_root_.mul_assoc, _root_.mul_assoc]; rfl)
    · refine ⟨SecOps.secZero, secScal_of_sval hL fun y J hJ => ?_, fun h => absurd h hα, fun _ _ => rfl⟩
      rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
        UUA.sval_zero_of (hΦ0 α fun mu e => hc ⟨mu, e⟩) _ y J (hJ.mem _ _)]
  choose f h1 h2 h3 using key
  exact ⟨r, hr, Φ, f, h1, fun j => congrArg (fun t => t.f j) (h2 ρ rfl), h3⟩
end GlobalTheory
