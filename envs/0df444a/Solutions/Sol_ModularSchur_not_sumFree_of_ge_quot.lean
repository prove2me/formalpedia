-- Prove2me | solution 1 for ModularSchur.not_sumFree_of_ge_quot
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T22:53:17.75403+00:00
-- url     : https://prove2.me/submissions/977bbc25-062e-4a2c-8896-2f059824ec41

-- Generated from lean/ModularSchur/K1Theorem.lean
--   imports : 0 platform node(s), 2 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : not_sumFree_of_ge_quot -> solution, hoisted out of the namespace
import Definitions.Def_ModularSchurBasic
import Definitions.Def_ModularSchurPartition
import Mathlib

open Finset Classical
variable {m ℓ : ℕ}

open ModularSchur in
theorem solution (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) (hlm : ℓ ≤ m) {N : ℕ}
    (hN : m / ℓ + 1 ≤ N) : ¬ IsEllSumFree m ℓ (stableResidues m N) := by
  intro h
  let q := (m + 1) / ℓ
  let r := (m + 1) % ℓ
  have hq_pos : 1 ≤ q := Nat.div_pos (by linarith) (by linarith)
  have hq_le : q ≤ N := by
    have key : m + 1 ≤ (m / ℓ + 1) * ℓ := by
      have h1 : ℓ * (m / ℓ) + m % ℓ = m := Nat.div_add_mod m ℓ
      have h2 : m % ℓ < ℓ := Nat.mod_lt m (by linarith)
      have eq1 : (m / ℓ + 1) * ℓ = ℓ * (m / ℓ) + ℓ := by ring
      linarith
    show (m + 1) / ℓ ≤ N
    calc (m + 1) / ℓ ≤ (m / ℓ + 1) * ℓ / ℓ := Nat.div_le_div_right key
         _ = m / ℓ + 1 := Nat.mul_div_cancel _ (by linarith)
         _ ≤ N := hN
  let f : Fin ℓ → ZMod m := fun i => if i.val < r then (q + 1 : ℕ) else q
  have hf_mem : ∀ i : Fin ℓ, f i ∈ stableResidues m N := by
    intro i
    simp only [f, stableResidues, mem_image, mem_Ioc]
    split_ifs with hi
    · -- i.val < r, so r > 0, so q * ℓ ≤ m, so q ≤ m/ℓ, so q+1 ≤ m/ℓ+1 ≤ N
      have hr_pos : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
      have hql : q * ℓ ≤ m := by
        have h1 : ℓ * q + r = m + 1 := Nat.div_add_mod (m + 1) ℓ
        have hc : q * ℓ = ℓ * q := mul_comm q ℓ
        linarith
      have hq_le_mq : q ≤ m / ℓ := by
        have h1 : q * ℓ / ℓ ≤ m / ℓ := Nat.div_le_div_right hql
        rwa [Nat.mul_div_cancel _ (by linarith)] at h1
      exact ⟨q + 1, ⟨by omega, by omega⟩, by norm_cast⟩
    · exact ⟨q, ⟨by omega, hq_le⟩, by norm_cast⟩
  have h1_mem : (1 : ZMod m) ∈ stableResidues m N :=
    mem_image.mpr ⟨1, mem_Ioc.mpr ⟨one_pos, by linarith⟩, by norm_cast⟩
  have hsum : ∑ i : Fin ℓ, f i = (1 : ZMod m) := by
    have hr_lt : r < ℓ := Nat.mod_lt _ (by linarith)
    -- Step 1: compute the nat sum
    have hnat : ∑ i : Fin ℓ, (if i.val < r then q + 1 else q) = m + 1 := by
      simp_rw [show ∀ i : Fin ℓ, (if i.val < r then q + 1 else q) =
          q + (if i.val < r then 1 else 0) from fun i => by split_ifs <;> ring]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
                 Fintype.card_fin, smul_eq_mul, Finset.sum_boole]
      have hcard : #{i ∈ (Finset.univ : Finset (Fin ℓ)) | i.val < r} = r := by
        have heq : {i ∈ (Finset.univ : Finset (Fin ℓ)) | i.val < r} =
            Finset.Iio ⟨r, hr_lt⟩ := by
          ext i; simp [Fin.lt_def]
        rw [heq, Fin.card_Iio]
      simp only [hcard, Nat.cast_id]
      exact Nat.div_add_mod (m + 1) ℓ
    -- Step 2: each f i equals (nat_f i : ZMod m)
    have heqi : ∀ i : Fin ℓ, f i = ((if i.val < r then q + 1 else q : ℕ) : ZMod m) :=
      fun i => by simp only [f]; split_ifs <;> norm_cast
    -- Step 3: pull cast outside sum, substitute hnat, reduce (m+1 : ZMod m) = 1
    simp_rw [heqi, ← Nat.cast_sum, hnat]
    rw [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  exact absurd hsum (h f hf_mem 1 h1_mem)
