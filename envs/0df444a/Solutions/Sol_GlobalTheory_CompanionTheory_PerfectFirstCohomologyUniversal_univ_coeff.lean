-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal.univ_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:07.724247+00:00
-- url     : https://prove2.me/submissions/6e8b1ede-32df-4f81-b3ff-7fa2e988ba52

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuasiIsomorphismDegreeOneKernel
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomologyUniversal_lid_lTensor_apply
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal
namespace GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal
theorem _root_.solution : ∀ (R A₀ A₁ A₂ P₀ P₁ P₂ : Type) [CommRing R] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] (d₀ : A₀ →ₗ[R] A₁) (d₁ : A₁ →ₗ[R] A₂) (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] A₀) (ψ₁ : P₁ →ₗ[R] A₁) (ψ₂ : P₂ →ₗ[R] A₂) (r : P₂ →ₗ[R] P₁) (Z : Submodule R A₁) (dZ : A₀ →ₗ[R] Z), (∀ z, z ∈ Z ↔ d₁ z = 0) → (∀ y, (dZ y : A₁) = d₀ y) → a₁ ∘ₗ a₀ = 0 → ψ₁ ∘ₗ a₀ = d₀ ∘ₗ ψ₀ → ψ₂ ∘ₗ a₁ = d₁ ∘ₗ ψ₁ → a₁ ∘ₗ r ∘ₗ a₁ = a₁ → (∀ (M : Type) [AddCommGroup M] [Module R M], QIsoAt (a₀.lTensor M) (a₁.lTensor M) (d₀.lTensor M) (d₁.lTensor M) (ψ₁.lTensor M)) → ∀ (M : Type) [AddCommGroup M] [Module R M], (∀ x : M ⊗[R] A₁, d₁.lTensor M x = 0 → ∃ (t : M ⊗[R] Z) (y : M ⊗[R] A₀), Z.subtype.lTensor M t + d₀.lTensor M y = x) ∧ (∀ (t : M ⊗[R] Z) (y : M ⊗[R] A₀), Z.subtype.lTensor M t = d₀.lTensor M y → ∃ y' : M ⊗[R] A₀, dZ.lTensor M y' = t) := by
  intro R A₀ A₁ A₂ P₀ P₁ P₂ _ _ _ _ _ _ _ _ _ _ _ _ _ d₀ d₁ a₀ a₁ ψ₀ ψ₁ ψ₂ r Z dZ hZ hdZ haa hc₀ hc₁ hr hQ M _ _
  have hr' : ∀ p, a₁ (r (a₁ p)) = a₁ p := fun p => LinearMap.congr_fun hr p
  have haa' : ∀ p, a₁ (a₀ p) = 0 := fun p => LinearMap.congr_fun haa p
  have hc₀' : ∀ p, ψ₁ (a₀ p) = d₀ (ψ₀ p) := fun p => LinearMap.congr_fun hc₀ p
  have hc₁' : ∀ p, ψ₂ (a₁ p) = d₁ (ψ₁ p) := fun p => LinearMap.congr_fun hc₁ p
  let ε : P₁ →ₗ[R] LinearMap.ker a₁ := (LinearMap.id - r ∘ₗ a₁).codRestrict (LinearMap.ker a₁) (fun p => by
    simp [LinearMap.mem_ker, hr'])
  let ψZ : LinearMap.ker a₁ →ₗ[R] Z := (ψ₁ ∘ₗ (LinearMap.ker a₁).subtype).codRestrict Z (fun p => (hZ _).2 (by
    have hp : a₁ (p : P₁) = 0 := p.2
    simp [← hc₁', hp]))
  let a₀Z : P₀ →ₗ[R] LinearMap.ker a₁ := a₀.codRestrict (LinearMap.ker a₁) (fun p => haa' p)
  have hεs : (LinearMap.ker a₁).subtype ∘ₗ ε = LinearMap.id - r ∘ₗ a₁ := by
    ext p; rfl
  have hει : ε ∘ₗ (LinearMap.ker a₁).subtype = LinearMap.id := by
    ext p
    have hp : a₁ (p : P₁) = 0 := p.2
    simp [ε, hp]
  have hιψ : Z.subtype ∘ₗ ψZ = ψ₁ ∘ₗ (LinearMap.ker a₁).subtype := by
    ext p; rfl
  have hιd : Z.subtype ∘ₗ dZ = d₀ := by
    ext y; exact hdZ y
  have hεa : ε ∘ₗ a₀ = a₀Z := by
    ext p
    show a₀ p - r (a₁ (a₀ p)) = a₀ p
    rw [haa', map_zero, sub_zero]
  have hψa : ψZ ∘ₗ a₀Z = dZ ∘ₗ ψ₀ := by
    ext p
    show ψ₁ (a₀ p) = (dZ (ψ₀ p) : A₁)
    rw [hc₀', hdZ]
  have ha₁ι : a₁ ∘ₗ (LinearMap.ker a₁).subtype = 0 := by
    ext p; exact p.2
  refine ⟨fun x hx => ?_, fun t y h => ?_⟩
  · obtain ⟨w, y, hw, hy⟩ := (hQ M).2 x hx
    have hwε : (LinearMap.ker a₁).subtype.lTensor M (ε.lTensor M w) = w := by
      rw [← LinearMap.lTensor_comp_apply, hεs, LinearMap.lTensor_sub, LinearMap.sub_apply, LinearMap.lTensor_id,
        LinearMap.id_apply, LinearMap.lTensor_comp_apply, hw, map_zero, sub_zero]
    refine ⟨ψZ.lTensor M (ε.lTensor M w), -y, ?_⟩
    rw [← LinearMap.lTensor_comp_apply, hιψ, LinearMap.lTensor_comp_apply, hwε, map_neg, ← hy]
    abel
  · have hsurj : Function.Surjective (ψZ.coprod dZ) := by
      intro z
      obtain ⟨x, y, hx, hy⟩ := (hQ R).2 ((1 : R) ⊗ₜ (z : A₁)) (by simp [(hZ z).1 z.2])
      have e₁ : a₁ (TensorProduct.lid R P₁ x) = 0 := by
        rw [← lid_lTensor_apply, hx, map_zero]
      have e₂ : ψ₁ (TensorProduct.lid R P₁ x) - z = d₀ (TensorProduct.lid R A₀ y) := by
        have := congrArg (TensorProduct.lid R A₁) hy
        rw [map_sub, lid_lTensor_apply, TensorProduct.lid_tmul, one_smul, lid_lTensor_apply] at this
        exact this
      refine ⟨(⟨TensorProduct.lid R P₁ x, e₁⟩, -TensorProduct.lid R A₀ y), Subtype.ext ?_⟩
      have e₃ : ((ψZ ⟨TensorProduct.lid R P₁ x, e₁⟩ : Z) : A₁) = ψ₁ (TensorProduct.lid R P₁ x) := rfl
      simp only [LinearMap.coprod_apply, Submodule.coe_add, e₃, map_neg, Submodule.coe_neg, hdZ, ← e₂]
      abel
    obtain ⟨u, hu⟩ := LinearMap.lTensor_surjective M hsurj t
    have hcop : ψZ.coprod dZ = ψZ ∘ₗ LinearMap.fst R _ _ + dZ ∘ₗ LinearMap.snd R _ _ := by
      ext <;> simp
    obtain ⟨t₁, y₁, ht⟩ : ∃ (t₁ : M ⊗[R] LinearMap.ker a₁) (y₁ : M ⊗[R] A₀),
        t = ψZ.lTensor M t₁ + dZ.lTensor M y₁ := by
      refine ⟨(LinearMap.fst R _ _).lTensor M u, (LinearMap.snd R _ _).lTensor M u, ?_⟩
      rw [← hu, hcop, LinearMap.lTensor_add, LinearMap.add_apply, LinearMap.lTensor_comp_apply,
        LinearMap.lTensor_comp_apply]
    have h1 : Z.subtype.lTensor M (ψZ.lTensor M t₁) = ψ₁.lTensor M ((LinearMap.ker a₁).subtype.lTensor M t₁) := by
      rw [← LinearMap.lTensor_comp_apply, hιψ, LinearMap.lTensor_comp_apply]
    have h2 : Z.subtype.lTensor M (dZ.lTensor M y₁) = d₀.lTensor M y₁ := by
      rw [← LinearMap.lTensor_comp_apply, hιd]
    have hιP : d₀.lTensor M (y - y₁) = ψ₁.lTensor M ((LinearMap.ker a₁).subtype.lTensor M t₁) := by
      rw [map_sub, ← h, ht, map_add, h1, h2]
      abel
    obtain ⟨p, hp⟩ := (hQ M).1 ((LinearMap.ker a₁).subtype.lTensor M t₁) (by
      rw [← LinearMap.lTensor_comp_apply, ha₁ι, LinearMap.lTensor_zero, LinearMap.zero_apply]) ⟨_, hιP⟩
    have ht₁ : t₁ = a₀Z.lTensor M p := by
      rw [← hεa, LinearMap.lTensor_comp_apply, hp, ← LinearMap.lTensor_comp_apply, hει, LinearMap.lTensor_id,
        LinearMap.id_apply]
    refine ⟨ψ₀.lTensor M p + y₁, ?_⟩
    have h3 : dZ.lTensor M (ψ₀.lTensor M p) = ψZ.lTensor M t₁ := by
      rw [ht₁, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply, hψa]
    rw [map_add, h3, ← ht]
end GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal
