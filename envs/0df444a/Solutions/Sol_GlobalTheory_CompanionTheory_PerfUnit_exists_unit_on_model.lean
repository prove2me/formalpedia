-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfUnit.exists_unit_on_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:29:05.447878+00:00
-- url     : https://prove2.me/submissions/66998d16-acf9-4e54-b9cf-6f68dd4c95b4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UniversalCoefficientDegreeZero
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
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
open TensorProduct MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfUnit
namespace GlobalTheory.CompanionTheory.PerfUnit
theorem _root_.solution : ∀ (R A₀ A₁ P₀ P₁ : Type) [CommRing R] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] (d₀ : A₀ →ₗ[R] A₁) (a₀ : P₀ →ₗ[R] P₁) (ψ₀ : P₀ →ₗ[R] A₀) (ψ₁ : P₁ →ₗ[R] A₁) (e : A₀), ψ₁ ∘ₗ a₀ = d₀ ∘ₗ ψ₀ → d₀ e = 0 → (∀ (M : Type) [AddCommGroup M] [Module R M], QIsoAt (0 : R →ₗ[R] M ⊗[R] P₀) (a₀.lTensor M) (0 : R →ₗ[R] M ⊗[R] A₀) (d₀.lTensor M) (ψ₀.lTensor M)) → (∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (fun m : M ↦ m ⊗ₜ[R] e) ∧ ∀ x : M ⊗[R] A₀, d₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] e = x) → ∃ u : P₀, a₀ u = 0 ∧ ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (fun m : M ↦ m ⊗ₜ[R] u) ∧ ∀ x : M ⊗[R] P₀, a₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] u = x := by
  intro R A₀ A₁ P₀ P₁ _ _ _ _ _ _ _ _ _ d₀ a₀ ψ₀ ψ₁ e hchain hde hq he
  have lid_nat : ∀ {X Y : Type} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
      (f : X →ₗ[R] Y) (t : R ⊗[R] X),
      f (TensorProduct.lid R X t) = TensorProduct.lid R Y (f.lTensor R t) := by
    intro X Y _ _ _ _ f t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  obtain ⟨x, y, hx, hxy⟩ := (hq R).2 ((1 : R) ⊗ₜ[R] e) (by simp [hde])
  have hxe : ψ₀.lTensor R x = (1 : R) ⊗ₜ[R] e := by
    simpa [sub_eq_zero] using hxy
  refine ⟨TensorProduct.lid R P₀ x, ?_, ?_⟩
  · rw [lid_nat, hx, map_zero]
  have hu : ψ₀ (TensorProduct.lid R P₀ x) = e := by
    rw [lid_nat, hxe]; simp
  set u := TensorProduct.lid R P₀ x with hudef
  have hu0 : a₀ u = 0 := by rw [hudef, lid_nat, hx, map_zero]
  intro M _ _
  have hψ : ∀ m : M, ψ₀.lTensor M (m ⊗ₜ[R] u) = m ⊗ₜ[R] e := by
    intro m; simp [hu]
  refine ⟨?_, ?_⟩
  · intro m m' h
    apply (he M).1
    have h' : m ⊗ₜ[R] u = m' ⊗ₜ[R] u := h
    show m ⊗ₜ[R] e = m' ⊗ₜ[R] e
    rw [← hψ, ← hψ, h']
  · intro z hz
    have hd : d₀.lTensor M (ψ₀.lTensor M z) = 0 := by
      have h1 : (d₀.lTensor M) ∘ₗ (ψ₀.lTensor M) = (ψ₁.lTensor M) ∘ₗ (a₀.lTensor M) := by
        rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hchain]
      have h2 := LinearMap.congr_fun h1 z
      simpa [hz] using h2
    obtain ⟨m, hm⟩ := (he M).2 _ hd
    refine ⟨m, ?_⟩
    have ha : a₀.lTensor M (z - m ⊗ₜ[R] u) = 0 := by
      simp [hz, hu0]
    have hp : ψ₀.lTensor M (z - m ⊗ₜ[R] u) = 0 := by
      rw [map_sub, hψ, hm, sub_self]
    obtain ⟨y', hy'⟩ := (hq M).1 _ ha ⟨0, by simp [hp]⟩
    have : z - m ⊗ₜ[R] u = 0 := by
      rw [← hy']; simp
    exact (sub_eq_zero.mp this).symm
end GlobalTheory.CompanionTheory.PerfUnit
