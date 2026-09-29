-- Prove2me | solution 1 for LocalizedModule.exists_linearMap_mk_tmul_eq_smul_of_forall_exists_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7c4f8b09-3a19-51e3-9037-5def25ba65cd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalizedModule_exists_linearMap_mk_tmul_eq_smul_of_forall_exists_eq_mk

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct
open TensorProduct

noncomputable section

namespace P2mKcSpread

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]

abbrev locT (y : PrimeSpectrum B) (M : Type) [AddCommGroup M] [Module 𝒪 M] :
    B ⊗[𝒪] M →ₗ[B] Localization.AtPrime y.asIdeal ⊗[𝒪] M :=
  AlgebraTensorModule.rTensor 𝒪 M (Algebra.linearMap B (Localization.AtPrime y.asIdeal))

scoped instance locT_isLocalizedModule (y : PrimeSpectrum B) (M : Type) [AddCommGroup M] [Module 𝒪 M] :
    IsLocalizedModule y.asIdeal.primeCompl (locT (𝒪 := 𝒪) y M) := by
  infer_instance

theorem locT_tmul (y : PrimeSpectrum B) {M : Type} [AddCommGroup M] [Module 𝒪 M] (b : B) (v : M) :
    locT y M (b ⊗ₜ[𝒪] v) = algebraMap B (Localization.AtPrime y.asIdeal) b ⊗ₜ[𝒪] v := rfl

theorem locT_one_tmul (y : PrimeSpectrum B) {M : Type} [AddCommGroup M] [Module 𝒪 M] (v : M) :
    locT y M ((1 : B) ⊗ₜ[𝒪] v) = (1 : Localization.AtPrime y.asIdeal) ⊗ₜ[𝒪] v := by
  rw [locT_tmul, map_one]

variable {M : Type} [AddCommGroup M] [Module 𝒪 M]
variable {T : Type} [AddCommGroup T] [Module B T]

theorem not_mem_of_dvd {a r : B} (y : PrimeSpectrum B) (h : a ∣ r) (hr : r ∉ y.asIdeal) : a ∉ y.asIdeal := by
  obtain ⟨c, rfl⟩ := h
  exact fun ha => hr (y.asIdeal.mul_mem_right c ha)

theorem main [Module.Free 𝒪 M] [Module.Finite 𝒪 M] [Module.Finite B T]
    (x : PrimeSpectrum B) (r₀ : B) (hr₀ : r₀ ∉ x.asIdeal)
    (u : ∀ y : PrimeSpectrum B, r₀ ∉ y.asIdeal →
      (Localization.AtPrime y.asIdeal ⊗[𝒪] M →ₗ[Localization.AtPrime y.asIdeal]
        LocalizedModule y.asIdeal.primeCompl T))
    (hcont : ∀ v : M, ∃ (f : B) (t : T), f ∉ x.asIdeal ∧
      ∀ (y : PrimeSpectrum B) (hy : r₀ ∉ y.asIdeal) (hf : f ∉ y.asIdeal),
        u y hy ((1 : Localization.AtPrime y.asIdeal) ⊗ₜ[𝒪] v) = LocalizedModule.mk t ⟨f, hf⟩)
    (hsurj : Function.Surjective (u x hr₀)) :
    ∃ r : B, r ∉ x.asIdeal ∧ r₀ ∣ r ∧ ∃ A : B ⊗[𝒪] M →ₗ[B] T,
      (∀ (y : PrimeSpectrum B) (hy : r₀ ∉ y.asIdeal), r ∉ y.asIdeal → ∀ v : M,
        LocalizedModule.mk (A ((1 : B) ⊗ₜ[𝒪] v)) 1 =
          algebraMap B (Localization.AtPrime y.asIdeal) r •
            u y hy ((1 : Localization.AtPrime y.asIdeal) ⊗ₜ[𝒪] v)) ∧
      (∀ t : T, ∃ (w : B ⊗[𝒪] M) (n : ℕ), A w = r ^ n • t) := by
  classical
  set ι := Module.Free.ChooseBasisIndex 𝒪 M
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype 𝒪 M
  let b : Module.Basis ι 𝒪 M := Module.Free.chooseBasis 𝒪 M

  choose f t hf hft using fun i : ι => hcont (b i)

  let R₀ : B := r₀ * ∏ i, f i
  let c : ι → B := fun i => r₀ * ∏ j ∈ Finset.univ.erase i, f j
  have hcf : ∀ i, f i * c i = R₀ := fun i => by
    show f i * (r₀ * ∏ j ∈ Finset.univ.erase i, f j) = r₀ * ∏ i, f i
    rw [mul_left_comm, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hR₀x : R₀ ∉ x.asIdeal := by
    have h1 : (∏ i, f i) ∈ x.asIdeal.primeCompl := prod_mem fun i _ => hf i
    exact fun h => (x.2.mem_or_mem h).elim hr₀ h1
  have hr₀R₀ : r₀ ∣ R₀ := Dvd.intro _ rfl
  have hfR₀ : ∀ i, f i ∣ R₀ := fun i => ⟨c i, (hcf i).symm⟩

  let bB : Module.Basis ι B (B ⊗[𝒪] M) := Algebra.TensorProduct.basis B b
  let A₀ : B ⊗[𝒪] M →ₗ[B] T := bB.constr B fun i => c i • t i
  have hA₀b : ∀ i, A₀ ((1 : B) ⊗ₜ[𝒪] b i) = c i • t i := fun i => by
    rw [← Algebra.TensorProduct.basis_apply (A := B) b i]
    exact bB.constr_basis B _ i

  have key : ∀ (y : PrimeSpectrum B) (hy : r₀ ∉ y.asIdeal), R₀ ∉ y.asIdeal → ∀ w : B ⊗[𝒪] M,
      LocalizedModule.mk (A₀ w) 1 =
        algebraMap B (Localization.AtPrime y.asIdeal) R₀ • u y hy (locT y M w) := by
    intro y hy hRy w
    have hfy : ∀ i, f i ∉ y.asIdeal := fun i => not_mem_of_dvd y (hfR₀ i) hRy
    let Φ : B ⊗[𝒪] M →ₗ[B] LocalizedModule y.asIdeal.primeCompl T :=
      (LocalizedModule.mkLinearMap y.asIdeal.primeCompl T) ∘ₗ A₀
    let Ψ : B ⊗[𝒪] M →ₗ[B] LocalizedModule y.asIdeal.primeCompl T :=
      ((algebraMap B (Localization.AtPrime y.asIdeal) R₀ • u y hy).restrictScalars B) ∘ₗ locT y M
    suffices h : Φ = Ψ by
      exact LinearMap.congr_fun h w
    refine bB.ext fun i => ?_
    change LocalizedModule.mk (A₀ (bB i)) 1 =
      algebraMap B (Localization.AtPrime y.asIdeal) R₀ • u y hy (locT y M (bB i))
    rw [Algebra.TensorProduct.basis_apply, hA₀b, locT_one_tmul, hft i y hy (hfy i), algebraMap_smul,
      LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    rw [one_smul, one_smul, one_smul, Submonoid.smul_def, smul_smul, hcf i]

  have hwit : ∀ τ : T, ∃ (d : B) (w : B ⊗[𝒪] M), d ∉ x.asIdeal ∧ A₀ w = d • τ := by
    intro τ
    obtain ⟨w₁, hw₁⟩ := hsurj (LocalizedModule.mk τ 1)
    obtain ⟨⟨w₀, s⟩, hs⟩ := IsLocalizedModule.surj x.asIdeal.primeCompl (locT x M) w₁
    have e := key x hr₀ hR₀x w₀
    rw [← hs, Submonoid.smul_def, ← algebraMap_smul (Localization.AtPrime x.asIdeal) (s : B) w₁, LinearMap.map_smul,
      hw₁, smul_smul, ← map_mul, algebraMap_smul, LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at e
    obtain ⟨u', hu'⟩ := e
    rw [one_smul, one_smul, Submonoid.smul_def, Submonoid.smul_def, smul_smul] at hu'
    refine ⟨(u' : B) * (R₀ * s), (u' : B) • w₀, ?_, ?_⟩
    · intro hmem
      rcases x.2.mem_or_mem hmem with h | h
      · exact u'.2 h
      · rcases x.2.mem_or_mem h with h | h
        · exact hR₀x h
        · exact s.2 h
    · rw [LinearMap.map_smul, ← hu']

  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := B) (M := T)
  choose d w hd hdw using hwit
  let D : B := ∏ τ ∈ G, d τ
  have hDx : D ∉ x.asIdeal := by
    have h1 : D ∈ x.asIdeal.primeCompl := prod_mem fun τ _ => hd τ
    exact h1
  have hDG : ∀ τ ∈ G, ∃ w' : B ⊗[𝒪] M, A₀ w' = D • τ := fun τ hτ =>
    ⟨(∏ σ ∈ G.erase τ, d σ) • w τ, by
      rw [LinearMap.map_smul, hdw, smul_smul, Finset.prod_erase_mul _ _ hτ]⟩
  have hDall : ∀ τ : T, ∃ w' : B ⊗[𝒪] M, A₀ w' = D • τ := by
    intro τ
    have hτ : τ ∈ Submodule.span B (G : Set T) := by rw [hG]; exact Submodule.mem_top
    induction hτ using Submodule.span_induction with
    | mem τ hτ => exact hDG τ hτ
    | zero => exact ⟨0, by rw [map_zero, smul_zero]⟩
    | add τ σ _ _ hτ hσ =>
      obtain ⟨w₁, h₁⟩ := hτ
      obtain ⟨w₂, h₂⟩ := hσ
      exact ⟨w₁ + w₂, by rw [map_add, h₁, h₂, smul_add]⟩
    | smul a τ _ hτ =>
      obtain ⟨w₁, h₁⟩ := hτ
      exact ⟨a • w₁, by rw [LinearMap.map_smul, h₁, smul_comm]⟩

  refine ⟨R₀ * D, ?_, dvd_mul_of_dvd_left hr₀R₀ D, D • A₀, ?_, ?_⟩
  · exact fun h => (x.2.mem_or_mem h).elim hR₀x hDx
  · intro y hy hry v
    have hRy : R₀ ∉ y.asIdeal := not_mem_of_dvd y (dvd_mul_right R₀ D) hry
    rw [LinearMap.smul_apply, ← LocalizedModule.smul'_mk, key y hy hRy, locT_one_tmul,
      ← algebraMap_smul (Localization.AtPrime y.asIdeal) D, smul_smul, ← map_mul, mul_comm D R₀]
  · intro τ
    obtain ⟨w', hw'⟩ := hDall τ
    refine ⟨(R₀ * R₀) • w', 2, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.map_smul, hw', smul_smul, smul_smul, pow_two]
    congr 1
    ring

end P2mKcSpread
p2m_reactivate "P2MW.S_LocalizedModule_exists_linearMap_mk_tmul_eq_smul_of_forall_exists_eq_mk.P2mKcSpread"

end
p2m_reactivate "P2MW.S_LocalizedModule_exists_linearMap_mk_tmul_eq_smul_of_forall_exists_eq_mk.P2mKcSpread"

open P2mKcSpread in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {M : Type} [AddCommGroup M] [Module 𝒪 M] [Module.Free 𝒪 M] [Module.Finite 𝒪 M]
    {T : Type} [AddCommGroup T] [Module B T] [Module.Finite B T]
    (x : PrimeSpectrum B) (r₀ : B) (hr₀ : r₀ ∉ x.asIdeal)
    (u : ∀ y : PrimeSpectrum B, r₀ ∉ y.asIdeal →
      (Localization.AtPrime y.asIdeal ⊗[𝒪] M →ₗ[Localization.AtPrime y.asIdeal]
        LocalizedModule y.asIdeal.primeCompl T))
    (hcont : ∀ v : M, ∃ (f : B) (t : T), f ∉ x.asIdeal ∧
      ∀ (y : PrimeSpectrum B) (hy : r₀ ∉ y.asIdeal) (hf : f ∉ y.asIdeal),
        u y hy ((1 : Localization.AtPrime y.asIdeal) ⊗ₜ[𝒪] v) = LocalizedModule.mk t ⟨f, hf⟩)
    (hsurj : Function.Surjective (u x hr₀)) :
    ∃ r : B, r ∉ x.asIdeal ∧ r₀ ∣ r ∧ ∃ A : B ⊗[𝒪] M →ₗ[B] T,
      (∀ (y : PrimeSpectrum B) (hy : r₀ ∉ y.asIdeal), r ∉ y.asIdeal → ∀ v : M,
        LocalizedModule.mk (A ((1 : B) ⊗ₜ[𝒪] v)) 1 =
          algebraMap B (Localization.AtPrime y.asIdeal) r •
            u y hy ((1 : Localization.AtPrime y.asIdeal) ⊗ₜ[𝒪] v)) ∧
      (∀ t : T, ∃ (w : B ⊗[𝒪] M) (n : ℕ), A w = r ^ n • t) :=
  main x r₀ hr₀ u hcont hsurj

end S_LocalizedModule_exists_linearMap_mk_tmul_eq_smul_of_forall_exists_eq_mk
end P2MW
export P2MW.S_LocalizedModule_exists_linearMap_mk_tmul_eq_smul_of_forall_exists_eq_mk (solution)
