-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnfoldAbs.setIntegral_eq_zero_of_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:50:33.261391+00:00
-- url     : https://prove2.me/submissions/1ee29231-1e6c-4683-b97d-fdb56dbc09f8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainFourierUnfolding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnfoldAbs
namespace GlobalTheory.CompanionTheory.UnfoldAbs
theorem _root_.solution {A : Type} [AddCommGroup A] [MeasurableSpace A]
    [MeasurableAdd A] (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A)
    [Countable Λ] (𝓖 : Set A) (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (Ψ : A → ℂ) (ν : A) (z : ℂ)
    (hz : z ≠ 1) (hΛ : ∀ (l : Λ) b, Ψ ((l : A) + b) = Ψ b) (hν : ∀ b, Ψ (ν + b) = z * Ψ b) :
    ∫ b in 𝓖, Ψ b ∂lam = 0 := by
  have h2 : IsAddFundamentalDomain Λ (ν +ᵥ 𝓖) lam := h𝓖.vadd_of_comm ν
  have e1 : ∫ b in 𝓖, Ψ b ∂lam = ∫ b in (ν +ᵥ 𝓖), Ψ b ∂lam :=
    h𝓖.setIntegral_eq h2 (fun g x => hΛ g x)
  have hpre : (fun x => ν + x) ⁻¹' (ν +ᵥ 𝓖) = 𝓖 := by
    ext x
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]
  have e2 : ∫ b in (ν +ᵥ 𝓖), Ψ b ∂lam = ∫ b in 𝓖, Ψ (ν + b) ∂lam := by
    have := (measurePreserving_add_left lam ν).setIntegral_preimage_emb
      (MeasurableEquiv.addLeft ν).measurableEmbedding Ψ (ν +ᵥ 𝓖)
    rw [hpre] at this
    exact this.symm
  have e3 : ∫ b in 𝓖, Ψ (ν + b) ∂lam = z * ∫ b in 𝓖, Ψ b ∂lam := by
    simp_rw [hν]
    exact integral_const_mul _ _
  have e4 : (1 - z) * ∫ b in 𝓖, Ψ b ∂lam = 0 := by
    have : ∫ b in 𝓖, Ψ b ∂lam = z * ∫ b in 𝓖, Ψ b ∂lam := by rw [← e3, ← e2, ← e1]
    linear_combination this
  exact (mul_eq_zero.mp e4).resolve_left (sub_ne_zero.mpr (Ne.symm hz))
end GlobalTheory.CompanionTheory.UnfoldAbs
