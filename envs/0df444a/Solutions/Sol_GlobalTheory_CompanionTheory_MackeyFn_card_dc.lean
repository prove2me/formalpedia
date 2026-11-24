-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MackeyFn.card_dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:49:48.913411+00:00
-- url     : https://prove2.me/submissions/51b29a91-262c-4ae0-a778-b901c552a59e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MackeyFn
variable {Γ : Type} [Group Γ] [Fintype Γ]
namespace GlobalTheory.CompanionTheory.MackeyFn
theorem _root_.solution (A B : Subgroup Γ) (g : Γ) :
    Nat.card (dc A B g) * Nat.card (A ⊓ cj g B : Subgroup Γ) = Nat.card A * Nat.card B := by
  classical
  let φ : B × A → dc A B g := fun p => ⟨p.1 * g * p.2, p.1, p.1.2, p.2, p.2.2, rfl⟩
  have fib : ∀ x : dc A B g, Nat.card {p // φ p = x} = Nat.card (A ⊓ cj g B : Subgroup Γ) := by
    rintro ⟨x, β₀, hβ₀, α₀, hα₀, rfl⟩
    symm
    have hB' : ∀ c : (A ⊓ cj g B : Subgroup Γ), β₀ * (g * (c : Γ)⁻¹ * g⁻¹) ∈ B := fun c => by
      have h2 : g * (c : Γ) * g⁻¹ ∈ B := c.2.2
      have : g * (c : Γ)⁻¹ * g⁻¹ = (g * (c : Γ) * g⁻¹)⁻¹ := by group
      rw [this]
      exact B.mul_mem hβ₀ (B.inv_mem h2)
    have hA' : ∀ c : (A ⊓ cj g B : Subgroup Γ), (c : Γ) * α₀ ∈ A := fun c => A.mul_mem c.2.1 hα₀
    let f : (A ⊓ cj g B : Subgroup Γ) → {p // φ p = ⟨β₀ * g * α₀, β₀, hβ₀, α₀, hα₀, rfl⟩} := fun c =>
      ⟨(⟨_, hB' c⟩, ⟨_, hA' c⟩), by
        apply Subtype.ext
        show β₀ * (g * (c : Γ)⁻¹ * g⁻¹) * g * ((c : Γ) * α₀) = β₀ * g * α₀
        group⟩
    refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
    · intro c c' hcc
      have h3 : (c : Γ) * α₀ = (c' : Γ) * α₀ := by
        have := congrArg (fun p => ((p.1.2 : A) : Γ)) hcc
        exact this
      exact Subtype.ext (mul_right_cancel h3)
    · rintro ⟨⟨⟨β, hβ⟩, ⟨α, hα⟩⟩, hp⟩
      have he : β * g * α = β₀ * g * α₀ := congrArg Subtype.val hp
      have hcA : α * α₀⁻¹ ∈ A := A.mul_mem hα (A.inv_mem hα₀)
      have hβe : β = β₀ * (g * (α * α₀⁻¹)⁻¹ * g⁻¹) := by
        have : β = (β * g * α) * α⁻¹ * g⁻¹ := by group
        rw [this, he]
        group
      have hcB : g * (α * α₀⁻¹) * g⁻¹ ∈ B := by
        have : g * (α * α₀⁻¹) * g⁻¹ = (β₀⁻¹ * β)⁻¹ := by
          rw [hβe]
          group
        rw [this]
        exact B.inv_mem (B.mul_mem (B.inv_mem hβ₀) hβ)
      refine ⟨⟨α * α₀⁻¹, hcA, hcB⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · exact Subtype.ext hβe.symm
      · apply Subtype.ext
        show α * α₀⁻¹ * α₀ = α
        group
  have e : (B × A) ≃ Σ x : dc A B g, {p // φ p = x} := (Equiv.sigmaFiberEquiv φ).symm
  have h4 : Nat.card (B × A) = Nat.card (dc A B g) * Nat.card (A ⊓ cj g B : Subgroup Γ) := by
    rw [Nat.card_congr e, Nat.card_sigma]
    simp only [fib, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  rw [← h4, Nat.card_prod, mul_comm]
end GlobalTheory.CompanionTheory.MackeyFn
