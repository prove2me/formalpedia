-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RootExch.exists_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:42:46.64464+00:00
-- url     : https://prove2.me/submissions/14650b8a-751b-4eea-b9b7-c8d81b5e384c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_tv_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_comm_data

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RootExch
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.RootExch
theorem _root_.solution {Φ Ψ : ι → ι → Prop} {E : ι → ι → K} (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (hΦ : IsPat Φ)
    (hsupp : ∀ i j, E i j ≠ 0 → Φ i j) (p q r t : ι)
    (hcomp : ∀ i j k, Φ i j → Φ j k → E i k ≠ 0 → i = p ∧ k = q)
    (g : GL ι K) (hg : g ∈ patSet K Φ) (hgi : g⁻¹ ∈ patSet K Φ) (hrt : Φ r t) (hΨrt : Ψ r t)
    (hΨ : ∀ i j, (i = r ∨ Φ i r) → (t = j ∨ Φ t j) → ¬ (i = r ∧ j = t) → Ψ i j)
    (hErt : E r t = 0) (hEpq : E p q ≠ 0)
    (hne : (g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q ≠ 0) :
    ∃ h ∈ patSet K Ψ, h * g * h⁻¹ * g⁻¹ ∈ patSet K Ψ ∧ patChar E ψ₀ (h * g * h⁻¹ * g⁻¹) ≠ 1 := by
  have hrne : r ≠ t := fun h' => hΦ.1 t (h' ▸ hrt)
  obtain ⟨a, ha⟩ : ∃ a, ψ₀ a ≠ 1 := by
    by_contra hc
    push_neg at hc
    exact hψ (by ext x; simpa using hc x)
  obtain ⟨s, hs⟩ : ∃ s : K, -(s * E p q * (g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q) = a := by
    refine ⟨-a / (E p q * ((g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q)), ?_⟩
    have h0 := mul_ne_zero hEpq hne
    have h3 : -a / (E p q * ((g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q)) * E p q *
        (g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q =
        -a / (E p q * ((g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q)) *
          (E p q * ((g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q)) := by ring
    rw [h3, div_mul_cancel₀ _ h0, neg_neg]
  obtain ⟨h1, h2⟩ := comm_data ψ₀ hΦ hsupp p q r t hcomp g hg hgi hrt hΨ hErt hrne s
  refine ⟨tv r t hrne s, tv_mem r t hrne s hΨrt, h1, ?_⟩
  rw [h2, hs]
  exact ha
end GlobalTheory.CompanionTheory.RootExch
