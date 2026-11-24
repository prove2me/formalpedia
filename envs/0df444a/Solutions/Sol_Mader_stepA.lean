-- Prove2me | solution 1 for Mader.stepA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:55:03.982122+00:00
-- url     : https://prove2.me/submissions/a36156c0-452c-40a1-b849-7ead91a2e450

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux
public import Definitions.Def_MaderLib_MaderSteps
public import Theorems.Thm_Mader_dbl_erase
public import Theorems.Thm_Mader_dbl_le


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*} (G : SimpleGraph V)
namespace Mader
theorem _root_.solution {S : Finset V} {m n k : ℕ} (hm : 4 * k * n ≤ m)
    (hmin : ∀ S' : Finset V, S'.card < S.card → 2 * k ≤ S'.card →
       (dbl G S' : ℤ) * n ≤ (m : ℤ) * ((S'.card : ℤ) - k))
    (h2k : 2 * k ≤ S.card)
    (hP : (m : ℤ) * ((S.card : ℤ) - k) < (dbl G S : ℤ) * n) :
    ∀ v ∈ S, m < 2 * ndeg G S v * n := by
  classical
  intro v hv
  by_contra hcon
  push Not at hcon
  have hne : S.card ≠ 2 * k := by
    intro heq
    have hD := dbl_le G S
    rw [heq] at hD hP
    have hDz : (dbl G S : ℤ) ≤ 2 * k * (2 * k - 1) := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; simp at hD; simp [hD]
      have : ((2 * k * (2 * k - 1) : ℕ) : ℤ) = 2 * k * (2 * k - 1) := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]; ring
      rw [← this]; exact_mod_cast hD
    have hmz : (4 * k * n : ℤ) ≤ m := by exact_mod_cast hm
    push_cast at hP
    have h1 := mul_le_mul_of_nonneg_right hDz (show (0 : ℤ) ≤ n by positivity)
    have h2 := mul_le_mul_of_nonneg_right hmz (show (0 : ℤ) ≤ k by positivity)
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ k by positivity) (show (0 : ℤ) ≤ n by positivity)]
  have hpos := card_pos.2 ⟨v, hv⟩
  have hcard : (S.erase v).card = S.card - 1 := card_erase_of_mem hv
  have hle := hmin (S.erase v) (by rw [hcard]; omega) (by rw [hcard]; omega)
  rw [hcard] at hle
  have hE := dbl_erase G hv
  have hEz : (dbl G S : ℤ) * n ≤ (dbl G (S.erase v) : ℤ) * n + 2 * ndeg G S v * n := by
    have : (dbl G S : ℤ) ≤ dbl G (S.erase v) + 2 * ndeg G S v := by exact_mod_cast hE
    nlinarith
  have hcz : (2 * ndeg G S v * n : ℤ) ≤ m := by exact_mod_cast hcon
  push_cast [Nat.cast_sub (show 1 ≤ S.card by omega)] at hle
  linarith
end Mader
