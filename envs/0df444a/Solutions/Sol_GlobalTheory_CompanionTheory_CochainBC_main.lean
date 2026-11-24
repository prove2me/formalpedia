-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CochainBC.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:19:54.169036+00:00
-- url     : https://prove2.me/submissions/14a3df0f-19d8-4992-a3bb-5788e86605ce

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_D2Apply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CochainBaseChangeEquivalences
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_bc_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_ext0
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_ext1
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_ext2
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CochainBC
namespace GlobalTheory.CompanionTheory.CochainBC
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C]
    [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (m : BC F F'),
    ∃ (E₀ : R' ⊗[R] C0 F ≃ₗ[R'] C0 F') (E₁ : R' ⊗[R] C1 F ≃ₗ[R'] C1 F') (E₂ : R' ⊗[R] C2 F ≃ₗ[R'] C2 F'),
      (∀ c, E₀ (1 ⊗ₜ c) = fun T ↦ m.α T (c T)) ∧ (∀ c, E₁ (1 ⊗ₜ c) = fun T T' φ ↦ m.α T' (c T T' φ)) ∧
      (∀ c, E₂ (1 ⊗ₜ c) = fun T T' T'' φ ψ ↦ m.α T'' (c T T' T'' φ ψ)) ∧
      (∀ x, E₁ ((d0 F).baseChange R' x) = d0 F' (E₀ x)) ∧ ∀ x, E₂ ((d1 F).baseChange R' x) = d1 F' (E₁ x) := by
  intro R R' _ _ _ C _ _ _ F F' m
  obtain ⟨E₀, hE₀⟩ := GlobalTheory.CompanionTheory.PerfExt.ext0 m
  obtain ⟨E₁, hE₁⟩ := GlobalTheory.CompanionTheory.PerfExt.ext1 m
  obtain ⟨E₂, hE₂⟩ := GlobalTheory.CompanionTheory.PerfExt.ext2 m
  refine ⟨E₀, E₁, E₂, hE₀, hE₁, hE₂, fun x => ?_, fun x => ?_⟩
  · have h := GlobalTheory.CompanionTheory.PerfExt.bc_ext (E₁.toLinearMap ∘ₗ (d0 F).baseChange R') ((d0 F') ∘ₗ E₀.toLinearMap) (by
      intro n
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul, hE₁, LinearMap.comp_apply,
        LinearEquiv.coe_coe, hE₀]
      funext T T' φ
      dsimp only
      rw [amitsur_d0_apply, amitsur_d0_apply, map_sub, m.naturality])
    exact LinearMap.congr_fun h x
  · have h := GlobalTheory.CompanionTheory.PerfExt.bc_ext (E₂.toLinearMap ∘ₗ (d1 F).baseChange R') ((d1 F') ∘ₗ E₁.toLinearMap) (by
      intro n
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul, hE₂, LinearMap.comp_apply,
        LinearEquiv.coe_coe, hE₁]
      funext T T' T'' φ ψ
      dsimp only
      rw [d1_apply, d1_apply, map_add, map_sub, m.naturality])
    exact LinearMap.congr_fun h x
end GlobalTheory.CompanionTheory.CochainBC
