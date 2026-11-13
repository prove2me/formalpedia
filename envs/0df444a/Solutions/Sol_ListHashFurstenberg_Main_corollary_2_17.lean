-- Prove2me | solution 1 for ListHashFurstenberg.Main.corollary_2_17
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T19:17:40.545668+00:00
-- url     : https://prove2.me/submissions/2b2017c8-3bbe-422e-b7e3-941672f9592d

import Mathlib
import Definitions.Def_ListHashFurstenberg_Main_Furstenberg
import Theorems.Thm_ListHashFurstenberg_Main_lemma_2_16
import Theorems.Thm_ListHashFurstenberg_Main_corollary_2_14
import Theorems.Thm_ListHashFurstenberg_Main_claim_2_18

section
set_option autoImplicit false

namespace ListHashFurstenberg.Main.Dev.Cor217

open ListHashFurstenberg.Main

/-- The rich fraction is at most one. -/
theorem richFraction_le_one {F : Type*} [Field F] [Fintype F] (n r : ℕ) (T : ℝ)
    (S : Finset (Fin n → F)) : richFraction n r T S ≤ 1 := by
  have : Finite (Submodule F (Fin n → F)) :=
    Finite.of_injective (fun V : Submodule F (Fin n → F) => (V : Set (Fin n → F)))
      SetLike.coe_injective
  unfold richFraction
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  refine Nat.card_le_card_of_injective (fun V => ⟨V.1, V.2.1⟩) ?_
  intro a b hab
  apply Subtype.ext
  simpa using congrArg Subtype.val hab

/-- A `δ`-Furstenberg set yields a `1/2`-Furstenberg set at most `2/δ` times larger. -/
theorem exists_half {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n r : ℕ) (δ T : ℝ) (S : Finset (Fin n → F)) (hS : IsFurstenberg δ n r T S)
    (hδ : 0 < δ) :
    ∃ S' : Finset (Fin n → F), IsFurstenberg (1 / 2) n r T S' ∧
      δ * (S'.card : ℝ) ≤ 2 * S.card := by
  have hδ1 : δ ≤ 1 := le_trans hS (richFraction_le_one n r T S)
  rcases le_or_gt (1 / 2) δ with h | h
  · refine ⟨S, le_trans h hS, ?_⟩
    have : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    nlinarith
  · obtain ⟨S', hS', hc⟩ := lemma_2_16 n r T δ (1 / 2) hδ h (by norm_num) S hS
    refine ⟨S', hS', ?_⟩
    have hcl := claim_2_18 δ hδ (by linarith)
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hc
    have h0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    have := hc.trans (mul_le_mul_of_nonneg_right hcl h0)
    calc δ * (S'.card : ℝ) ≤ δ * (2 / δ * S.card) := mul_le_mul_of_nonneg_left this hδ.le
      _ = 2 * S.card := by field_simp

end ListHashFurstenberg.Main.Dev.Cor217

namespace ListHashFurstenberg.Main

open ListHashFurstenberg.Main.Dev.Cor217 in
theorem chk_corollary_2_17 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n r : ℕ) (δ T : ℝ) (S : Finset (Fin n → F)) (hS : IsFurstenberg δ n r T S)
    (hT : 8 * (Fintype.card F : ℝ) ≤ T) :
    δ * T / 4 * (Fintype.card F : ℝ) ^ ((n : ℤ) - r) *
        Real.exp (-(8 * (Fintype.card F : ℝ) * n) / T) ≤ (S.card : ℝ) := by
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hq2 : (2 : ℝ) ≤ q := by
    rw [hqdef]; exact_mod_cast Fintype.one_lt_card (α := F)
  have hq0 : 0 < q := by linarith
  have hT0 : 0 < T := by linarith
  have hQ : 0 < q ^ r := by positivity
  have hzn : q ^ ((n : ℤ) - r) = q ^ n / q ^ r := by
    rw [zpow_sub₀ hq0.ne', zpow_natCast, zpow_natCast]
  rw [hzn]
  set E := Real.exp (-(8 * q * n) / T) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have h0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  rcases le_or_gt δ 0 with hδ | hδ
  · have : δ * T / 4 * (q ^ n / q ^ r) * E ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ hE0.le
      apply mul_nonpos_of_nonpos_of_nonneg _ (by positivity)
      apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
      exact mul_nonpos_of_nonpos_of_nonneg hδ hT0.le
    linarith
  obtain ⟨S', hS', hc⟩ := exists_half n r δ T S hS hδ
  have hS'' : IsFurstenberg (1 / 2) n r (T / q ^ r * q ^ r) S' := by
    rwa [div_mul_cancel₀ _ hQ.ne']
  have hzr : q ^ ((r : ℤ) - 1) = q ^ r / q := by
    rw [zpow_sub_one₀ hq0.ne', zpow_natCast, div_eq_mul_inv]
  have hden : T / q ^ r * (1 / 2) * q ^ ((r : ℤ) - 1) = T / (2 * q) := by
    rw [hzr]; field_simp
  have hC2 : (2 : ℝ) ≤ T / q ^ r * (1 / 2) * q ^ ((r : ℤ) - 1) / 2 := by
    rw [hden, le_div_iff₀ (by norm_num), le_div_iff₀ (by positivity)]
    linarith
  have key := corollary_2_14 n r (1 / 2) (T / q ^ r) 2 S' hS'' (by norm_num) hC2
  have hden2 : (1 / 2 : ℝ) * (T / q ^ r) * q ^ ((r : ℤ) - 1) = T / (2 * q) := by
    rw [← hden]; ring
  rw [hden2, show -(2 * 2 * (n : ℝ)) / (T / (2 * q)) = -(8 * q * n) / T by
    field_simp; ring, ← hE] at key
  rw [le_div_iff₀ (by positivity)] at key
  calc δ * T / 4 * (q ^ n / q ^ r) * E
      = δ / 2 * (E * (1 - 1 / 2) * (T / q ^ r) * q ^ n) := by ring
    _ ≤ δ / 2 * S'.card := mul_le_mul_of_nonneg_left key (by linarith)
    _ ≤ S.card := by linarith

end ListHashFurstenberg.Main
end

theorem solution : type_of% @ListHashFurstenberg.Main.chk_corollary_2_17 := @ListHashFurstenberg.Main.chk_corollary_2_17
