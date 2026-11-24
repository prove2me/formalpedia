-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KrullLocal.smul_eq_zero_of_smul_one_tmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:22:34.689795+00:00
-- url     : https://prove2.me/submissions/7a861e92-7ed5-4569-b56c-38add196b850

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorPrimeLocalizationCriterion
import Theorems.Thm_GlobalTheory_CompanionTheory_KrullLocal_map_eq_zero_of_smul_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KrullLocal
namespace GlobalTheory.CompanionTheory.KrullLocal
theorem _root_.solution : ∀ {B R C M : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M] (J : Ideal B), (∀ a ∈ J, ∀ m : M, a • m = 0) → ∀ Q₀ : Ideal (R ⊗[B] C), Q₀.IsPrime → (∀ c : C, ∃ b t : B, t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧ ∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧ v * (algebraMap B C t * c) = v * algebraMap B C b) → (∀ b : B, (∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧ v * algebraMap B C b = 0) → ∃ t : B, t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧ t * b ∈ J) → ∀ (y : M) (w : R ⊗[B] C), w ∉ Q₀ → w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 → ∃ u : R, u ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) ∧ u • y = 0 := by
  intro B R C M _ _ _ _ _ _ _ _ _ J hJ Q₀ hQ h1 h2 y w hw0 hw
  let p : Ideal R := Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C)
  haveI hp : p.IsPrime := Ideal.comap_isPrime _ _
  let A := Localization.AtPrime p
  let N := LocalizedModule p.primeCompl M
  letI : Module (A ⧸ Module.annihilator A N) N := Module.quotientAnnihilator
  haveI : IsScalarTower R (A ⧸ Module.annihilator A N) N := by
    refine ⟨fun r d n => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
    have e : ∀ (x : A) (n : N), (Ideal.Quotient.mk (Module.annihilator A N) x) • n = x • n :=
      fun _ _ => rfl
    have e2 : r • Ideal.Quotient.mk (Module.annihilator A N) a =
        Ideal.Quotient.mk (Module.annihilator A N) (r • a) := rfl
    rw [e2, e, e, smul_assoc]
  have hJ' : ∀ a ∈ J, algebraMap R (A ⧸ Module.annihilator A N) (algebraMap B R a) = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply R A (A ⧸ Module.annihilator A N),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, Module.mem_annihilator]
    intro n
    induction n using LocalizedModule.induction_on with
    | _ m s =>
      rw [algebraMap_smul, LocalizedModule.smul'_mk, algebraMap_smul, hJ a ha, LocalizedModule.zero_mk]
  have hunit : ∀ r : R, r ∉ p → IsUnit (algebraMap R (A ⧸ Module.annihilator A N) r) := by
    intro r hr
    rw [IsScalarTower.algebraMap_apply R A (A ⧸ Module.annihilator A N)]
    exact (IsLocalization.map_units A (⟨r, hr⟩ : p.primeCompl)).map _
  have hy := map_eq_zero_of_smul_tmul (D := A ⧸ Module.annihilator A N) J hJ' Q₀ hQ hunit h1 h2
    (LocalizedModule.mkLinearMap p.primeCompl M) y w hw0 hw
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)).1 hy
  exact ⟨s, s.2, hs⟩
end GlobalTheory.CompanionTheory.KrullLocal
