-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RootExch.one_side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:54.512013+00:00
-- url     : https://prove2.me/submissions/ebfd04f5-2c48-435e-b754-b667555ab964

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_lam_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_sum_twist_zero

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
    (hm : ∀ a ∈ P, ∀ b ∈ P, lam (a * b) = lam a * lam b) (hne : ∀ a ∈ P, lam a ≠ 0)
    (hPQ : ∀ v ∈ Q, v ∉ P → ∃ h ∈ P, h * v * h⁻¹ * v⁻¹ ∈ P ∧ lam (h * v * h⁻¹ * v⁻¹) ≠ 1) :
    (∑ v, if v ∈ Q then (lam v)⁻¹ * (∑ u, if u ∈ P then (lam u)⁻¹ * χ (u * v) else 0) else 0) =
      ((Finset.univ.filter fun v => v ∈ P ∧ v ∈ Q).card : ℂ) *
        ∑ u, if u ∈ P then (lam u)⁻¹ * χ u else 0 := by
  have hterm : ∀ v, (if v ∈ Q then (lam v)⁻¹ * (∑ u, if u ∈ P then (lam u)⁻¹ * χ (u * v) else 0) else 0) =
      if v ∈ P ∧ v ∈ Q then ∑ u, (if u ∈ P then (lam u)⁻¹ * χ u else 0) else 0 := by
    intro v
    by_cases hvQ : v ∈ Q
    · by_cases hvP : v ∈ P
      · rw [if_pos hvQ, if_pos ⟨hvP, hvQ⟩, ← Equiv.sum_comp (Equiv.mulRight v⁻¹), Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        have hiff : u * v⁻¹ ∈ P ↔ u ∈ P := P.mul_mem_cancel_right (P.inv_mem hvP)
        rw [show (Equiv.mulRight v⁻¹) u = u * v⁻¹ from rfl]
        by_cases hu : u ∈ P
        · rw [if_pos (hiff.2 hu), if_pos hu, hm _ hu _ (P.inv_mem hvP), lam_inv P lam hm hne v hvP,
            inv_mul_cancel_right]
          have := hne v hvP
          field_simp
        · rw [if_neg (fun h' => hu (hiff.1 h')), if_neg hu, mul_zero]
      · obtain ⟨h, hh, hc, hl⟩ := hPQ v hvQ hvP
        rw [if_pos hvQ, if_neg (fun h' => hvP h'.1),
          sum_twist_zero P lam χ hχ hm hne v h hh hc hl, mul_zero]
    · rw [if_neg hvQ, if_neg (fun h' => hvQ h'.2)]
  rw [Finset.sum_congr rfl fun v _ => hterm v, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
end GlobalTheory.CompanionTheory.RootExch
