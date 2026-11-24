-- Prove2me | solution 1 for GlobalTheory.lattice_inequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:14:50.292279+00:00
-- url     : https://prove2.me/submissions/648e0a2c-fd94-4576-9a4b-809307afc3de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsReducedCombination
import Theorems.Thm_GlobalTheory_LatticeIneq_weighted_add_le
import Theorems.Thm_GlobalTheory_LatticeIneq_map_sum_le
import Theorems.Thm_GlobalTheory_LatticeIneq_exists_reduced_combination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open LatticeIneq
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ), (∀ x, 0 ≤ q x) → ∀ (I : Type) [Fintype I] (N N' j : ℕ), 1 ≤ N → N ∣ N' → 1 ≤ j → ∀ (yy w : I → X) (vth : I → ℝ) (αs c : X) (vf' : ℝ), (∀ x, ∃ μ, w x = yy x + N' • μ) → (∀ x, q (w x) ≤ (N' : ℝ) ^ 2 * vth x) → q αs ≤ N * vf' → c - αs ∈ AddSubgroup.closure (Set.range yy ∪ Set.range fun μ : X => N • μ) → ∃ μ : X, j * (q (c + N • μ) / N) ≤ (j + 1) * vf' + (j * (j + 1) * Fintype.card I * N * N' ^ 2 : ℕ) * ∑ x, vth x := by
  intro X _ q hq I _ N N' j hN hNN' _ yy w vth αs c vf' hw hwq hα hc
  obtain ⟨m, rfl⟩ := hNN'
  have hw' : ∀ x, ∃ μ, w x = yy x + N • μ := fun x => by
    obtain ⟨μ, hμ⟩ := hw x
    exact ⟨m • μ, by rw [hμ, mul_smul]⟩
  obtain ⟨k, μ, hk, h⟩ := exists_reduced_combination N hN yy w hw' _ hc
  refine ⟨μ, ?_⟩
  have hc' : c + N • μ = αs + ∑ x, k x • w x := by rw [← h]; abel
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := weighted_add_le q hq j αs (∑ x, k x • w x)
  have h2 := map_sum_le q hq Finset.univ (fun x => k x • w x)
  have h3 : ∑ x, q (k x • w x) ≤ (N : ℝ) ^ 2 * ((N * m : ℕ) : ℝ) ^ 2 * ∑ x, vth x := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [QuadraticMap.map_smul, zsmul_eq_mul]
    have a0 : (0 : ℝ) ≤ k x := by exact_mod_cast (hk x).1
    have a1 : (k x : ℝ) ≤ N := by exact_mod_cast (hk x).2
    have a2 : ((k x * k x : ℤ) : ℝ) ≤ (N : ℝ) ^ 2 := by push_cast; nlinarith
    calc _ ≤ (N : ℝ) ^ 2 * q (w x) := mul_le_mul_of_nonneg_right a2 (hq _)
      _ ≤ (N : ℝ) ^ 2 * (((N * m : ℕ) : ℝ) ^ 2 * vth x) :=
        mul_le_mul_of_nonneg_left (hwq x) (by positivity)
      _ = _ := by ring
  rw [Finset.card_univ] at h2
  have h4 := h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ (j : ℝ) * (j + 1))
  have h6 := mul_le_mul_of_nonneg_left hα (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1)
  rw [hc', ← mul_div_assoc, div_le_iff₀ hNpos]
  push_cast at h5 ⊢
  linarith
end GlobalTheory
