-- Prove2me | solution 1 for ModularSchur.sumFree_min
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T22:59:02.643986+00:00
-- url     : https://prove2.me/submissions/46977dba-0c26-4ac9-9bee-ccdcc3e5e9b1

-- Generated from lean/ModularSchur/K1Theorem.lean
--   imports : 0 platform node(s), 2 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : sumFree_min -> solution, hoisted out of the namespace
import Definitions.Def_ModularSchurBasic
import Definitions.Def_ModularSchurPartition
import Mathlib

open Finset Classical
variable {m ℓ : ℕ}

open ModularSchur in
theorem solution (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) (hlm : ℓ ≤ m) :
    IsEllSumFree m ℓ (stableResidues m (min (ℓ - 1) (m / ℓ))) := by
  set N := min (ℓ - 1) (m / ℓ)
  have hN_le_ell : N ≤ ℓ - 1 := Nat.min_le_left _ _
  have hN_le_quot : N ≤ m / ℓ := Nat.min_le_right _ _
  have hN_lt_m : N < m := by
    calc N ≤ ℓ - 1 := hN_le_ell
         _ ≤ m - 1 := by omega
         _ < m := Nat.sub_lt (by linarith) one_pos
  intro f hf y hy
  have hmem : ∀ i, ∃ n, 1 ≤ n ∧ n ≤ N ∧ (n : ZMod m) = f i := by
    intro i
    simp only [stableResidues, mem_image, mem_Ioc] at hf
    obtain ⟨n, ⟨h1, h2⟩, h3⟩ := hf i; exact ⟨n, h1, h2, h3⟩
  obtain ⟨ny, hny_pos, hny_le, hny_cast⟩ : ∃ ny, 1 ≤ ny ∧ ny ≤ N ∧ (ny : ZMod m) = y := by
    simp only [stableResidues, mem_image, mem_Ioc] at hy
    obtain ⟨n, ⟨h1, h2⟩, h3⟩ := hy; exact ⟨n, h1, h2, h3⟩
  choose g hg_pos hg_le hg_cast using hmem
  have hsum_lo : ℓ ≤ ∑ i, g i := by
    calc ℓ = ∑ _i : Fin ℓ, 1 := by simp
         _ ≤ ∑ i : Fin ℓ, g i := Finset.sum_le_sum (fun i _ => hg_pos i)
  have hsum_hi : ∑ i, g i ≤ m := by
    calc ∑ i : Fin ℓ, g i
        ≤ ∑ _i : Fin ℓ, N := Finset.sum_le_sum (fun i _ => hg_le i)
      _ = ℓ * N := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ ℓ * (m / ℓ) := Nat.mul_le_mul_left ℓ hN_le_quot
      _ ≤ m := Nat.mul_div_le m ℓ
  have hsum_zmod : (∑ i : Fin ℓ, g i : ZMod m) = ∑ i : Fin ℓ, f i := by
    push_cast
    exact Finset.sum_congr rfl (fun i _ => hg_cast i)
  intro heq
  have hzmod_eq : ((∑ i : Fin ℓ, g i : ℕ) : ZMod m) = (ny : ZMod m) := by
    push_cast; rw [hsum_zmod, heq, hny_cast]
  have hmod : (∑ i : Fin ℓ, g i) % m = ny % m := by
    rwa [ZMod.natCast_eq_natCast_iff, Nat.ModEq] at hzmod_eq
  have hny_lt_m : ny < m := Nat.lt_of_le_of_lt hny_le hN_lt_m
  rw [Nat.mod_eq_of_lt hny_lt_m] at hmod
  rcases Nat.lt_or_eq_of_le hsum_hi with hlt | heqm
  · rw [Nat.mod_eq_of_lt hlt] at hmod; omega
  · rw [← heqm, Nat.mod_self] at hmod; omega
