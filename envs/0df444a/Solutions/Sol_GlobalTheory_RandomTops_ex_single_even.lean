-- Prove2me | solution 1 for GlobalTheory.RandomTops.ex_single_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:50:09.551105+00:00
-- url     : https://prove2.me/submissions/b55ed7a6-35ef-4453-81b7-656a5e886e18

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ind_pos
import Theorems.Thm_GlobalTheory_RandomTops_ind_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Formalism.G0
open GlobalTheory GlobalTheory.RandomTops
variable {δ : ℝ}
namespace GlobalTheory.RandomTops
theorem _root_.solution (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (a u : ℕ) :
    ((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1) ≤
      ex δ (Finset.Ico a (a + u)) (fun V => ind (∃ x, V = {x} ∧ Even x)) := by
  have hIc : #(Ico a (a + u)) = u := by rw [Nat.card_Ico]; omega
  have hinj : Function.Injective (fun k => ({a + a % 2 + 2 * k} : Finset ℕ)) := by
    intro k₁ k₂ h
    have := singleton_inj.mp h
    omega
  have hPc : #((range (u / 2)).image (fun k => ({a + a % 2 + 2 * k} : Finset ℕ))) = u / 2 := by
    rw [card_image_of_injective _ hinj, card_range]
  have hPsub : (range (u / 2)).image (fun k => ({a + a % 2 + 2 * k} : Finset ℕ)) ⊆ (Ico a (a + u)).powerset := by
    intro V hV
    rw [mem_image] at hV
    obtain ⟨k, hk, rfl⟩ := hV
    rw [mem_powerset, singleton_subset_iff, mem_Ico]
    rw [mem_range] at hk
    omega
  have hw : ∀ V ∈ (range (u / 2)).image (fun k => ({a + a % 2 + 2 * k} : Finset ℕ)),
      δ ^ #V * (1 - δ) ^ (#(Ico a (a + u)) - #V) * ind (∃ x, V = {x} ∧ Even x) = δ * (1 - δ) ^ (u - 1) := by
    intro V hV
    rw [mem_image] at hV
    obtain ⟨k, _, rfl⟩ := hV
    rw [card_singleton, hIc, ind_pos ⟨_, rfl, Nat.even_iff.mpr (by omega)⟩]
    ring
  unfold ex
  beta_reduce
  calc ((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1)
      = ∑ V ∈ (range (u / 2)).image (fun k => ({a + a % 2 + 2 * k} : Finset ℕ)),
          δ ^ #V * (1 - δ) ^ (#(Ico a (a + u)) - #V) * ind (∃ x, V = {x} ∧ Even x) := by
        rw [sum_congr rfl hw, sum_const, hPc, nsmul_eq_mul]
        ring
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hPsub fun V _ _ =>
        mul_nonneg (mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)) (ind_nonneg _)
end GlobalTheory.RandomTops
