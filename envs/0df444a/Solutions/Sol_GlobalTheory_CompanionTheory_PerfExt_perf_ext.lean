-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfExt.perf_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:54:20.957994+00:00
-- url     : https://prove2.me/submissions/2568f3ec-55df-4832-b29e-ef787a2b9136

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_D2Apply
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_tw_nat
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_QIsoAt_transport
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_bc_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_d2_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_ext0
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_ext1
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_ext2
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_ext3
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfExt
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} R'} [Finite C] [∀ T T' : C, Finite (T ⟶ T')]
namespace GlobalTheory.CompanionTheory.PerfExt
theorem _root_.solution (m : BC F F') (h : Perf F) : Perf F' := by
  obtain ⟨P₀, P₁, P₂, P₃, a₀, a₁, a₂, ψ₀, ψ₁, ψ₂, ⟨f₀, p₀⟩, ⟨f₁, p₁⟩, ⟨f₂, p₂⟩, ⟨f₃, p₃⟩, h₁₀, h₂₁, s₀, s₁,
    ⟨ψ₃, s₂⟩, hM⟩ := h
  obtain ⟨E₀, e₀⟩ := ext0 m
  obtain ⟨E₁, e₁⟩ := ext1 m
  obtain ⟨E₂, e₂⟩ := ext2 m
  obtain ⟨E₃, e₃⟩ := ext3 m
  have t₀ : ∀ x, d0 F' (E₀ (1 ⊗ₜ x)) = E₁ (1 ⊗ₜ d0 F x) := fun x ↦ by
    rw [e₀, e₁]
    funext T T' φ
    simp only [amitsur_d0_apply, map_sub, m.naturality]
  have t₁ : ∀ x, d1 F' (E₁ (1 ⊗ₜ x)) = E₂ (1 ⊗ₜ d1 F x) := fun x ↦ by
    rw [e₁, e₂]
    funext T T' T'' φ ψ
    simp only [d1_apply, map_sub, map_add, m.naturality]
  have t₂ : ∀ x, d2 F' (E₂ (1 ⊗ₜ x)) = E₃ (1 ⊗ₜ d2 F x) := fun x ↦ by
    rw [e₂, e₃]
    funext T T' T'' T''' φ ψ χ
    simp only [d2_apply, map_sub, map_add, m.naturality]
  refine ⟨.of R' (R' ⊗[R] P₀), .of R' (R' ⊗[R] P₁), .of R' (R' ⊗[R] P₂), .of R' (R' ⊗[R] P₃),
    a₀.baseChange R', a₁.baseChange R', a₂.baseChange R',
    E₀.toLinearMap ∘ₗ ψ₀.baseChange R', E₁.toLinearMap ∘ₗ ψ₁.baseChange R', E₂.toLinearMap ∘ₗ ψ₂.baseChange R',
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₀)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₀))⟩,
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₁)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₁))⟩,
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₂)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₂))⟩,
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₃)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₃))⟩,
    ?_, ?_, ?_, ?_, ⟨E₃.toLinearMap ∘ₗ ψ₃.baseChange R', ?_⟩, fun M ↦ ?_⟩
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun h₁₀ n
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
    simp [LinearMap.baseChange_tmul, this]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun h₂₁ n
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
    simp [LinearMap.baseChange_tmul, this]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun s₀ n
    simp only [LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, this, t₀]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun s₁ n
    simp only [LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, this, t₁]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun s₂ n
    simp only [LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, this, t₂]
  · letI : Module R M := Module.compHom M (algebraMap R R')
    haveI : IsScalarTower R R' M := ⟨fun r s x ↦ by
      change (r • s) • x = (algebraMap R R' r) • (s • x)
      rw [Algebra.smul_def, mul_smul]⟩
    obtain ⟨q₀, q₁, q₂⟩ := hM (ModuleCat.of R M)
    let r₀ : R' ⊗[R] P₀ ≃ₗ[R'] R' ⊗[R] P₀ := .refl _ _
    let r₁ : R' ⊗[R] P₁ ≃ₗ[R'] R' ⊗[R] P₁ := .refl _ _
    let r₂ : R' ⊗[R] P₂ ≃ₗ[R'] R' ⊗[R] P₂ := .refl _ _
    let r₃ : R' ⊗[R] P₃ ≃ₗ[R'] R' ⊗[R] P₃ := .refl _ _
    have nA₀ : ∀ t, tw M r₁ (a₀.lTensor M t) = (a₀.baseChange R').lTensor M (tw M r₀ t) :=
      tw_nat r₀ r₁ a₀ _ fun n ↦ by simp [r₀, r₁, LinearMap.baseChange_tmul]
    have nA₁ : ∀ t, tw M r₂ (a₁.lTensor M t) = (a₁.baseChange R').lTensor M (tw M r₁ t) :=
      tw_nat r₁ r₂ a₁ _ fun n ↦ by simp [r₁, r₂, LinearMap.baseChange_tmul]
    have nA₂ : ∀ t, tw M r₃ (a₂.lTensor M t) = (a₂.baseChange R').lTensor M (tw M r₂ t) :=
      tw_nat r₂ r₃ a₂ _ fun n ↦ by simp [r₂, r₃, LinearMap.baseChange_tmul]
    have nD₀ : ∀ t, tw M E₁ ((d0 F).lTensor M t) = (d0 F').lTensor M (tw M E₀ t) := tw_nat E₀ E₁ _ _ t₀
    have nD₁ : ∀ t, tw M E₂ ((d1 F).lTensor M t) = (d1 F').lTensor M (tw M E₁ t) := tw_nat E₁ E₂ _ _ t₁
    have nD₂ : ∀ t, tw M E₃ ((d2 F).lTensor M t) = (d2 F').lTensor M (tw M E₂ t) := tw_nat E₂ E₃ _ _ t₂
    have nP₀ : ∀ t, tw M E₀ (ψ₀.lTensor M t) =
        (E₀.toLinearMap ∘ₗ ψ₀.baseChange R').lTensor M (tw M r₀ t) :=
      tw_nat r₀ E₀ ψ₀ _ fun n ↦ by simp [r₀, LinearMap.baseChange_tmul]
    have nP₁ : ∀ t, tw M E₁ (ψ₁.lTensor M t) =
        (E₁.toLinearMap ∘ₗ ψ₁.baseChange R').lTensor M (tw M r₁ t) :=
      tw_nat r₁ E₁ ψ₁ _ fun n ↦ by simp [r₁, LinearMap.baseChange_tmul]
    have nP₂ : ∀ t, tw M E₂ (ψ₂.lTensor M t) =
        (E₂.toLinearMap ∘ₗ ψ₂.baseChange R').lTensor M (tw M r₂ t) :=
      tw_nat r₂ E₂ ψ₂ _ fun n ↦ by simp [r₂, LinearMap.baseChange_tmul]
    exact ⟨QIsoAt.transport (tw M r₀) (tw M r₁) (tw M E₀) (tw M E₁) nA₀ nD₀ nP₀
        (fun _ ↦ ⟨0, by simp⟩) (fun _ ↦ ⟨0, by simp⟩) (fun _ ↦ ⟨0, by simp⟩) q₀,
      QIsoAt.transport (tw M r₁) (tw M r₂) (tw M E₁) (tw M E₂) nA₁ nD₁ nP₁
        (fun y ↦ ⟨tw M r₀ y, (nA₀ y).symm⟩) (fun y ↦ ⟨tw M E₀ y, (nD₀ y).symm⟩)
        (fun y ↦ ⟨(tw M E₀).symm y, by rw [nD₀, AddEquiv.apply_symm_apply]⟩) q₁,
      QIsoAt.transport (tw M r₂) (tw M r₃) (tw M E₂) (tw M E₃) nA₂ nD₂ nP₂
        (fun y ↦ ⟨tw M r₁ y, (nA₁ y).symm⟩) (fun y ↦ ⟨tw M E₁ y, (nD₁ y).symm⟩)
        (fun y ↦ ⟨(tw M E₁).symm y, by rw [nD₁, AddEquiv.apply_symm_apply]⟩) q₂⟩
end GlobalTheory.CompanionTheory.PerfExt
