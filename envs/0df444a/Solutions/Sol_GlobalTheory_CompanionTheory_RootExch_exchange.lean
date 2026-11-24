-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RootExch.exchange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:53.498805+00:00
-- url     : https://prove2.me/submissions/10e0809e-8934-438a-bde8-eec7af18597f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_one_side

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
variable {G : Type*} [Group G] [Fintype G]
open Classical
namespace GlobalTheory.CompanionTheory.RootExch
theorem _root_.solution (P Q : Subgroup G) (lam χ : G → ℂ)
    (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g)
    (hmP : ∀ a ∈ P, ∀ b ∈ P, lam (a * b) = lam a * lam b) (hneP : ∀ a ∈ P, lam a ≠ 0)
    (hmQ : ∀ a ∈ Q, ∀ b ∈ Q, lam (a * b) = lam a * lam b) (hneQ : ∀ a ∈ Q, lam a ≠ 0)
    (hPQ : ∀ v ∈ Q, v ∉ P → ∃ h ∈ P, h * v * h⁻¹ * v⁻¹ ∈ P ∧ lam (h * v * h⁻¹ * v⁻¹) ≠ 1)
    (hQP : ∀ v ∈ P, v ∉ Q → ∃ h ∈ Q, h * v * h⁻¹ * v⁻¹ ∈ Q ∧ lam (h * v * h⁻¹ * v⁻¹) ≠ 1) :
    (∑ u, if u ∈ P then (lam u)⁻¹ * χ u else 0) = ∑ u, if u ∈ Q then (lam u)⁻¹ * χ u else 0 := by
  have h1 := one_side P Q lam χ hχ hmP hneP hPQ
  have h2 := one_side Q P lam χ hχ hmQ hneQ hQP
  have hswap : (∑ v, if v ∈ Q then (lam v)⁻¹ * (∑ u, if u ∈ P then (lam u)⁻¹ * χ (u * v) else 0) else 0) =
      ∑ v, if v ∈ P then (lam v)⁻¹ * (∑ u, if u ∈ Q then (lam u)⁻¹ * χ (u * v) else 0) else 0 := by
    have e1 : ∀ v, (if v ∈ Q then (lam v)⁻¹ * (∑ u, if u ∈ P then (lam u)⁻¹ * χ (u * v) else 0) else 0) =
        ∑ u, if v ∈ Q ∧ u ∈ P then (lam v)⁻¹ * ((lam u)⁻¹ * χ (u * v)) else 0 := by
      intro v
      by_cases hv : v ∈ Q
      · simp only [hv, if_true, true_and, Finset.mul_sum, mul_ite, mul_zero]
      · simp [hv]
    have e2 : ∀ v, (if v ∈ P then (lam v)⁻¹ * (∑ u, if u ∈ Q then (lam u)⁻¹ * χ (u * v) else 0) else 0) =
        ∑ u, if v ∈ P ∧ u ∈ Q then (lam v)⁻¹ * ((lam u)⁻¹ * χ (u * v)) else 0 := by
      intro v
      by_cases hv : v ∈ P
      · simp only [hv, if_true, true_and, Finset.mul_sum, mul_ite, mul_zero]
      · simp [hv]
    rw [Finset.sum_congr rfl fun v _ => e1 v, Finset.sum_congr rfl fun v _ => e2 v, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    have hc : χ (u * v) = χ (v * u) := by
      have := hχ v (u * v)
      rw [← this]; congr 1; group
    by_cases hh : v ∈ Q ∧ u ∈ P
    · rw [if_pos hh, if_pos ⟨hh.2, hh.1⟩, hc]; ring
    · rw [if_neg hh, if_neg (fun h' => hh ⟨h'.2, h'.1⟩)]
  have hn : ((Finset.univ.filter fun v => v ∈ P ∧ v ∈ Q).card : ℂ) ≠ 0 := by
    have : (Finset.univ.filter fun v => v ∈ P ∧ v ∈ Q).Nonempty :=
      ⟨1, by simp [P.one_mem, Q.one_mem]⟩
    exact_mod_cast this.card_pos.ne'
  have hcard : (Finset.univ.filter fun v => v ∈ Q ∧ v ∈ P) = Finset.univ.filter fun v => v ∈ P ∧ v ∈ Q := by
    ext v; simp [and_comm]
  rw [hswap, h2, hcard] at h1
  exact (mul_left_cancel₀ hn h1).symm
end GlobalTheory.CompanionTheory.RootExch
