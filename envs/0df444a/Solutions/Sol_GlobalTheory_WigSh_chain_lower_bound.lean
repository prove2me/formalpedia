-- Prove2me | solution 1 for GlobalTheory.WigSh.chain_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:17.720052+00:00
-- url     : https://prove2.me/submissions/f113f433-b6ee-4fbd-9c26-a2a4ecc733a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvSqLeWignerCoeffSqRaisingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvSqLeWignerCoeffSqLoweringStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ChainLowerBound
import Theorems.Thm_GlobalTheory_T_inv_sq_le_wignerCoeffSqLowering
import Theorems.Thm_GlobalTheory_T_inv_sq_le_wignerCoeffSqRaising

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
namespace GlobalTheory.WigSh
private theorem strictAnti_of_box {n : ℕ} {L : Fin (n+1) → ℤ} {M : Fin n → ℤ}
    (h : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) : StrictAnti L :=
  Fin.strictAnti_iff_succ_lt.2 fun j => (h j).1.trans_le (h j).2
private theorem chain_prod_le {n₀ : ℕ} {D : ℝ} (hD : 1 ≤ D) (f : ℕ → ℝ)
    (hf : ∀ j < n₀, (D ^ 2)⁻¹ ≤ f j) : (D ^ (2 * n₀))⁻¹ ≤ ∏ j ∈ Finset.range n₀, f j := by
  have h1 : (D ^ (2 * n₀))⁻¹ = ∏ _j ∈ Finset.range n₀, (D ^ 2)⁻¹ := by
    rw [Finset.prod_const, Finset.card_range, pow_mul, inv_pow]
  rw [h1]
  exact Finset.prod_le_prod (fun _ _ => by positivity)
    (fun j hj => hf j (Finset.mem_range.1 hj))
end GlobalTheory.WigSh
end

set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.WigSh
namespace GlobalTheory.WigSh
theorem _root_.solution : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (i : Fin n) (n₀ : ℕ) (b : ℝ), StrictAnti L → (∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) → L i.succ + 2 * (n₀ : ℤ) + 1 ≤ L i.castSucc → 1 ≤ b → (n₀ : ℝ) ≤ b → ((L 0 : ℝ) - L (Fin.last n) ≤ 2 * b) → (((3 * b) ^ (2 * n₀))⁻¹ ≤ ∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wP (Function.update L i.succ (L i.succ + (j : ℤ))) M i.succ) ∨ (((3 * b) ^ (2 * n₀))⁻¹ ≤ ∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wM (Function.update L i.castSucc (L i.castSucc - (j : ℤ))) M i.castSucc) := by
  intro n L M i n₀ b hL hbox hgap hb hn hspan
  have hD : (1 : ℝ) ≤ 3 * b := by linarith
  have h0 : ∀ k, (L k : ℝ) ≤ L 0 := fun k => by
    exact_mod_cast hL.antitone (Fin.zero_le k)
  have hl : ∀ k, (L (Fin.last n) : ℝ) ≤ L k := fun k => by
    exact_mod_cast hL.antitone (Fin.le_last k)
  have hlt : ∀ k : Fin n, k < i → L i.castSucc < M k := fun k hk =>
    lt_of_le_of_lt (hL.antitone (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hk)) (hbox k).1
  have hgt : ∀ k : Fin n, i < k → M k ≤ L i.succ := fun k hk =>
    le_trans (hbox k).2 (hL.antitone (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hk))
  by_cases hc : L i.succ + n₀ + 1 ≤ M i
  · left
    refine chain_prod_le hD _ fun j hj => ?_
    have hjZ : (j : ℤ) < n₀ := by exact_mod_cast hj
    have hjR : (j : ℝ) ≤ b := le_trans (by exact_mod_cast hj.le) hn
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hbox' : ∀ k : Fin n, Function.update L i.succ (L i.succ + (j : ℤ)) k.succ < M k ∧
        M k ≤ Function.update L i.succ (L i.succ + (j : ℤ)) k.castSucc := by
      intro k
      constructor
      · by_cases hk : k = i
        · subst hk
          rw [Function.update_self]; omega
        · rw [Function.update_of_ne (fun h => hk (Fin.succ_injective _ h))]
          exact (hbox k).1
      · by_cases hk : k.castSucc = i.succ
        · have := (hbox k).2
          rw [hk] at this ⊢
          rw [Function.update_self]; omega
        · rw [Function.update_of_ne hk]
          exact (hbox k).2
    refine GlobalTheory.T.inv_sq_le_wignerCoeffSqRaising n _ M i.succ (3 * b) (strictAnti_of_box hbox') hbox' ?_ hD ?_ ?_
    · intro k
      rw [Function.update_self]
      rcases lt_trichotomy k i with hk | hk | hk
      · have := hlt k hk; omega
      · subst hk; omega
      · have := hgt k hk; omega
    · rw [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      push_cast
      have := hl i.succ
      linarith
    · rw [Function.update_self]
      by_cases hk : Fin.last n = i.succ
      · rw [hk, Function.update_self]; linarith
      · rw [Function.update_of_ne hk]
        push_cast
        have := h0 i.succ
        linarith
  · right
    refine chain_prod_le hD _ fun j hj => ?_
    have hjZ : (j : ℤ) < n₀ := by exact_mod_cast hj
    have hjR : (j : ℝ) ≤ b := le_trans (by exact_mod_cast hj.le) hn
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hbox' : ∀ k : Fin n,
        Function.update L i.castSucc (L i.castSucc - (j : ℤ)) k.succ < M k ∧
        M k ≤ Function.update L i.castSucc (L i.castSucc - (j : ℤ)) k.castSucc := by
      intro k
      constructor
      · by_cases hk : k.succ = i.castSucc
        · have hki : k < i := by
            have := congrArg Fin.val hk
            simp only [Fin.val_succ, Fin.val_castSucc] at this
            rw [Fin.lt_def]; omega
          have := hlt k hki
          rw [hk, Function.update_self]; omega
        · rw [Function.update_of_ne hk]
          exact (hbox k).1
      · by_cases hk : k = i
        · subst hk
          rw [Function.update_self]; omega
        · rw [Function.update_of_ne (fun h => hk (Fin.castSucc_injective _ h))]
          exact (hbox k).2
    refine GlobalTheory.T.inv_sq_le_wignerCoeffSqLowering n _ M i.castSucc (3 * b) (strictAnti_of_box hbox') hbox' ?_ hD ?_ ?_
    · intro k
      rw [Function.update_self]
      rcases lt_trichotomy k i with hk | hk | hk
      · have := hlt k hk; omega
      · subst hk; omega
      · have := hgt k hk; omega
    · rw [Function.update_self]
      by_cases hk : 0 = i.castSucc
      · rw [hk, Function.update_self]; linarith
      · rw [Function.update_of_ne hk]
        push_cast
        have := hl i.castSucc
        linarith
    · rw [Function.update_self, Function.update_of_ne (Fin.castSucc_lt_last i).ne']
      push_cast
      have := h0 i.castSucc
      linarith
end GlobalTheory.WigSh
