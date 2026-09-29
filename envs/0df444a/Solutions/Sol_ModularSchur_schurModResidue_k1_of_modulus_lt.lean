-- Prove2me | solution 1 for ModularSchur.schurModResidue_k1_of_modulus_lt
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T23:07:10.6255+00:00
-- url     : https://prove2.me/submissions/fcd5b5d3-0a94-478d-b73f-f0f479b7df4f

-- Generated from lean/ModularSchur/K1Theorem.lean
--   imports : 1 platform node(s), 2 definition bundle(s)
--   inlined : 6 file-scoped / sub-threshold helper(s)
--   rename  : schurModResidue_k1_of_modulus_lt -> solution, hoisted out of the namespace
import Definitions.Def_ModularSchurBasic
import Definitions.Def_ModularSchurPartition
import Theorems.Thm_ModularSchur_k1_partition_iff
import Mathlib

open Finset Classical
variable {m ℓ : ℕ}

namespace ModularSchur

/-- If `ℓ ≢ 1 (mod m)`, the singleton interval is `ℓ`-sum-free. -/
private lemma sumFree_stableResidues_one_of_mod_ne_one (m ℓ : ℕ) (hm : 2 ≤ m)
    (hmod : ℓ % m ≠ 1) : IsEllSumFree m ℓ (stableResidues m 1) := by
  intro f hf y hy
  have hf_eq : ∀ i, f i = (1 : ZMod m) := by
    intro i
    simp [stableResidues] at hf
    exact hf i
  have hy_eq : y = (1 : ZMod m) := by
    simpa [stableResidues] using hy
  intro heq
  have hcast : (ℓ : ZMod m) = (1 : ZMod m) := by
    simpa [hf_eq, hy_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using heq
  have hmod_eq : ℓ % m = 1 % m :=
    (ZMod.natCast_eq_natCast_iff' ℓ 1 m).mp (by simpa using hcast)
  rw [Nat.mod_eq_of_lt (by omega : 1 < m)] at hmod_eq
  exact hmod hmod_eq

/-- If `ℓ ≡ 1 (mod m)`, the all-ones `ℓ`-tuple obstructs every nonempty interval. -/
private lemma not_sumFree_stableResidues_of_mod_eq_one (m ℓ : ℕ) (hmod : ℓ % m = 1)
    {N : ℕ} (hN : 1 ≤ N) : ¬ IsEllSumFree m ℓ (stableResidues m N) := by
  intro h
  have h1_mem : ∀ _ : Fin ℓ, (1 : ZMod m) ∈ stableResidues m N :=
    fun _ => mem_image.mpr ⟨1, mem_Ioc.mpr ⟨one_pos, hN⟩, by norm_cast⟩
  have hsum : ∑ _ : Fin ℓ, (1 : ZMod m) = 1 := by
    rw [show ∑ _ : Fin ℓ, (1 : ZMod m) = (ℓ : ZMod m) by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
    rw [← ZMod.natCast_mod ℓ m, hmod]
    norm_num
  have h1_target : (1 : ZMod m) ∈ stableResidues m N :=
    mem_image.mpr ⟨1, mem_Ioc.mpr ⟨one_pos, hN⟩, by norm_cast⟩
  exact absurd hsum (h (fun _ => 1) h1_mem 1 h1_target)

/-- When `m < ℓ`, the residue interval through `2` is never `ℓ`-sum-free. -/
private lemma not_sumFree_stableResidues_of_two_le_of_modulus_lt (m ℓ : ℕ)
    (hm : 2 ≤ m) (hml : m < ℓ) {N : ℕ} (hN : 2 ≤ N) :
    ¬ IsEllSumFree m ℓ (stableResidues m N) := by
  intro h
  by_cases hmod : ℓ % m = 1
  · exact not_sumFree_stableResidues_of_mod_eq_one m ℓ hmod (by omega) h
  · let a := ℓ % m
    let r := if a = 0 then 1 else m + 1 - a
    have ha_lt : a < m := Nat.mod_lt _ (by omega)
    have ha_ne_one : a ≠ 1 := by simpa [a] using hmod
    have hr_pos : 1 ≤ r := by
      dsimp [r]
      split_ifs <;> omega
    have hr_lt_m : r < m := by
      dsimp [r]
      split_ifs <;> omega
    have hr_lt_ell : r < ℓ := lt_trans hr_lt_m hml
    let f : Fin ℓ → ZMod m := fun i => if i.val < r then 2 else 1
    have hf_mem : ∀ i, f i ∈ stableResidues m N := by
      intro i
      simp only [f]
      split_ifs
      · exact mem_image.mpr ⟨2, mem_Ioc.mpr ⟨by omega, hN⟩, by norm_cast⟩
      · exact mem_image.mpr ⟨1, mem_Ioc.mpr ⟨one_pos, by omega⟩, by norm_cast⟩
    have hnat : ∑ i : Fin ℓ, (if i.val < r then 2 else 1) = ℓ + r := by
      simp_rw [show ∀ i : Fin ℓ, (if i.val < r then 2 else 1) =
          1 + (if i.val < r then 1 else 0) from fun i => by split_ifs <;> omega]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, Finset.sum_boole]
      have hcard : #{i ∈ (Finset.univ : Finset (Fin ℓ)) | i.val < r} = r := by
        have heq : {i ∈ (Finset.univ : Finset (Fin ℓ)) | i.val < r} =
            Finset.Iio ⟨r, hr_lt_ell⟩ := by
          ext i
          simp [Fin.lt_def]
        rw [heq, Fin.card_Iio]
      simp only [hcard, Nat.cast_id]
      omega
    have hsum_mod : (ℓ + r) % m = 1 := by
      by_cases ha : a = 0
      · have hr : r = 1 := by simp [r, ha]
        have hell_mod : ℓ % m = 0 := by simpa [a] using ha
        rw [hr, Nat.add_mod, hell_mod]
        simp [Nat.mod_eq_of_lt (by omega : 1 < m)]
      · have hr : r = m + 1 - a := by simp [r, ha]
        have hsum : a + r = m + 1 := by omega
        rw [Nat.add_mod, show ℓ % m = a by rfl, Nat.mod_eq_of_lt hr_lt_m, hsum]
        simp [Nat.mod_eq_of_lt (by omega : 1 < m)]
    have hsum : ∑ i : Fin ℓ, f i = (1 : ZMod m) := by
      have heqi : ∀ i : Fin ℓ, f i = ((if i.val < r then 2 else 1 : ℕ) : ZMod m) :=
        fun i => by simp only [f]; split_ifs <;> norm_cast
      simp_rw [heqi, ← Nat.cast_sum, hnat, ← ZMod.natCast_mod (ℓ + r) m, hsum_mod]
      norm_num
    have h1_mem : (1 : ZMod m) ∈ stableResidues m N :=
      mem_image.mpr ⟨1, mem_Ioc.mpr ⟨one_pos, by omega⟩, by norm_cast⟩
    exact absurd hsum (h f hf_mem 1 h1_mem)

private def k1Pred (m ℓ : ℕ) : ℕ → Prop :=
  fun N => ∃ P : Fin 1 → Finset (ZMod m), IsValidPartition m ℓ 1 (stableResidues m N) P

/-- The trivial all-empty partition witnesses the predicate at N=0. -/
private lemma partition_exists_zero (m ℓ k : ℕ) :
    (fun N => ∃ P : Fin k → Finset (ZMod m),
      IsValidPartition m ℓ k (stableResidues m N) P) 0 := by
  refine ⟨fun _ => ∅, ?_, ?_, ?_, ?_⟩
  · simp [stableResidues]
  · intro i j _; simp
  · intro i; simp
  · intro i; simp [IsEllSumFree]

/-- findGreatest_spec with k1Pred, so the predicate is syntactically manifest. -/
private lemma k1Pred_at_schur (m ℓ : ℕ) : k1Pred m ℓ (schurModResidue m 1 ℓ) :=
  Nat.findGreatest_spec (Nat.zero_le _) (partition_exists_zero m ℓ 1)

end ModularSchur

open ModularSchur in
theorem solution (m ℓ : ℕ) (hm : 2 ≤ m) (hml : m < ℓ) :
    schurModResidue m 1 ℓ = if ℓ % m = 1 then 0 else 1 := by
  split_ifs with hmod
  · apply Nat.eq_zero_of_le_zero
    by_contra hpos
    have hge : 1 ≤ schurModResidue m 1 ℓ := by omega
    have hspec : IsEllSumFree m ℓ (stableResidues m (schurModResidue m 1 ℓ)) :=
      (k1_partition_iff m ℓ _).mp (k1Pred_at_schur m ℓ)
    exact not_sumFree_stableResidues_of_mod_eq_one m ℓ hmod hge hspec
  · apply le_antisymm
    · by_contra hc
      have hge : 2 ≤ schurModResidue m 1 ℓ := by omega
      have hspec : IsEllSumFree m ℓ (stableResidues m (schurModResidue m 1 ℓ)) :=
        (k1_partition_iff m ℓ _).mp (k1Pred_at_schur m ℓ)
      exact not_sumFree_stableResidues_of_two_le_of_modulus_lt m ℓ hm hml hge hspec
    · apply Nat.le_findGreatest
      · omega
      · rw [k1_partition_iff]
        exact sumFree_stableResidues_one_of_mod_ne_one m ℓ hm hmod
