-- Prove2me | solution 1 for GlobalTheory.SS.ArcInf.TwoVarSetup.exists_twoVar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:02:39.736309+00:00
-- url     : https://prove2.me/submissions/1f17d157-3427-4dec-a005-bc469e02959a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasicOpenFactorFieldPointAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsArcQuotientTwoVariableCoords
import Theorems.Thm_GlobalTheory_SS_ArcInf_TwoVarSetup_exists_liftAway
import Theorems.Thm_GlobalTheory_SS_ArcInf_TwoVarSetup_laurent_ext
import Theorems.Thm_GlobalTheory_SS_ArcInf_TwoVarSetup_diag_var
import Theorems.Thm_GlobalTheory_SS_ArcInf_TwoVarSetup_diag_subst
import Theorems.Thm_GlobalTheory_SS_ArcInf_TwoVarSetup_exists_diag
import Theorems.Thm_GlobalTheory_SS_ArcInf_TwoVarSetup_exists_copy
import Theorems.Thm_GlobalTheory_SS_ArcInf_TwoVarSetup_point_one
import Theorems.Thm_GlobalTheory_SS_ArcInf_algOverHom_comp
import Theorems.Thm_GlobalTheory_SS_ArcInf_eq_of_comp_eq
import Theorems.Thm_GlobalTheory_SS_ArcInf_exists_basicOpen_factor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ArcInf GlobalTheory.SS.ArcInf.TwoVarSetup
variable {k : Type} [Field k]
namespace GlobalTheory.SS.ArcInf.TwoVarSetup
theorem _root_.solution : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f → ∀ a : algOver k (FractionRing (PowerSeries k)) ⟶ G, ∃ (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) d ≠ 0 ∧ (∀ i, MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) (h i) = 0) ∧ TwoVar j f a h d := by
  intro k _ G _ A _ _ j ε r f hc a
  obtain ⟨τ₀, hτ₀⟩ := exists_diag (k := k)
  obtain ⟨s₀, hs₀⟩ := exists_copy (k := k) 0
  obtain ⟨s₁, hs₁⟩ := exists_copy (k := k) 1
  have hinj := IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k))
  have hX : ∀ i, τ₀ (MvPowerSeries.X i) ≠ 0 := fun i => by
    rw [hτ₀, diag_var]
    exact (map_ne_zero_iff _ hinj).2 PowerSeries.X_ne_zero
  have hx : τ₀ (MvPowerSeries.X 0 * MvPowerSeries.X 1) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero (hX 0) (hX 1)
  generalize (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) = x at s₀ s₁ hs₀ hs₁ hx
  obtain ⟨δ, hδ⟩ := exists_liftAway x τ₀ hx.isUnit
  have hδ₀ : δ.comp s₀ = AlgHom.id k _ := laurent_ext fun y => by
    rw [AlgHom.comp_apply, hs₀, hδ, hτ₀, diag_subst]; rfl
  have hδ₁ : δ.comp s₁ = AlgHom.id k _ := laurent_ext fun y => by
    rw [AlgHom.comp_apply, hs₁, hδ, hτ₀, diag_subst]; rfl
  obtain ⟨e, he, hfac⟩ := GlobalTheory.SS.ArcInf.exists_basicOpen_factor k G A _ (FractionRing (PowerSeries k)) j
    ((algOverHom s₁ ≫ a) * (algOverHom s₀ ≫ a)⁻¹) δ ((Algebra.ofId k _).comp ε) hc.1 (by
      rw [point_one hc.2.1, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
        ← algOverHom_comp, ← algOverHom_comp, hδ₀, hδ₁, mul_inv_cancel])
  obtain ⟨n, e₀, he₀⟩ := IsLocalization.Away.surj x e
  have hτe : τ₀ e₀ ≠ 0 := by
    rw [← hδ, ← he₀, map_mul, map_pow, hδ]
    exact mul_ne_zero he (pow_ne_zero _ hx)
  have hu := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (x * e₀)) (x * e₀)
  rw [map_mul] at hu
  obtain ⟨ρ, hρ⟩ := exists_liftAway x
    (IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k) (Localization.Away (x * e₀)))
    (isUnit_of_mul_isUnit_left hu)
  simp only [IsScalarTower.coe_toAlgHom'] at hρ
  have hρe : IsUnit (ρ e) := by
    have h1 := isUnit_of_mul_isUnit_right hu
    rw [← hρ, ← he₀, map_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  obtain ⟨χ, hχ⟩ := hfac _ ρ hρe
  obtain ⟨⟨b, M, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (x * e₀)) (fun i => χ (f i))
  choose h hh using hb
  simp only [Algebra.smul_def] at hh
  have hd : τ₀ ((x * e₀) * (x * e₀) ^ M) ≠ 0 := by
    rw [← pow_succ', map_pow, map_mul]
    exact pow_ne_zero _ (mul_ne_zero hx hτe)
  have htv : TwoVar j f a (fun i => (x * e₀) * h i) ((x * e₀) * (x * e₀) ^ M) := by
    intro F _ _ τ σ₀ σ₁ hτ hσ₀ hσ₁
    have h0 : τ (x * e₀) ≠ 0 := by
      rw [map_mul] at hτ; exact left_ne_zero_of_mul hτ
    obtain ⟨τ', hτ'⟩ := exists_liftAway (x * e₀) τ h0.isUnit
    have e0 : τ'.comp (ρ.comp s₀) = σ₀ := laurent_ext fun y => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hs₀, hρ, hτ', hσ₀]
    have e1 : τ'.comp (ρ.comp s₁) = σ₁ := laurent_ext fun y => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hs₁, hρ, hτ', hσ₁]
    refine ⟨τ'.comp χ, fun i => ?_, ?_⟩
    · rw [map_mul τ (x * e₀) (h i), ← hτ' (h i), hh, map_mul τ', hτ', map_mul τ (x * e₀),
        AlgHom.comp_apply]
      ring
    · rw [algOverHom_comp, Category.assoc, hχ, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
        GrpObj.comp_inv]
      simp only [← Category.assoc, ← algOverHom_comp]
      rw [e0, e1, inv_mul_cancel_right]
  refine ⟨_, _, ?_, fun i => ?_, htv⟩
  · intro h0
    apply hd
    rw [hτ₀, h0, map_zero]
  · obtain ⟨χ', h1, h2⟩ := htv _ τ₀ (AlgHom.id k _) (AlgHom.id k _) hd
      (fun y => by rw [hτ₀, diag_subst]; rfl) (fun y => by rw [hτ₀, diag_subst]; rfl)
    have h3 : χ' = (Algebra.ofId k _).comp ε := by
      apply eq_of_comp_eq hc.1
      rw [point_one hc.2.1]
      exact right_eq_mul.1 h2
    apply hinj
    rw [← hτ₀, map_zero, ← h1 i, h3, AlgHom.comp_apply, hc.2.2.2 i, map_zero, zero_mul]
end GlobalTheory.SS.ArcInf.TwoVarSetup
