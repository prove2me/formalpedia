-- Prove2me | solution 1 for GroundTheory.LocalField.natDegree_mul_addVal_eq_ramificationIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:49:31.768912+00:00
-- url     : https://prove2.me/submissions/93d2c751-4d78-4ed6-936d-49315065ca3e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Theorems.Thm_GroundTheory_LocalField_eq_zero_of_addVal_lt_of_sum_eq_zero
import Theorems.Thm_GroundTheory_LocalField_exists_addVal_eq_coe
import Theorems.Thm_GroundTheory_LocalField_addVal_algebraMap_integer
import Theorems.Thm_GroundTheory_LocalField_mem_maximalIdeal_pow_iff_le_addVal
import Theorems.Thm_GroundTheory_LocalField_addVal_eq_one_of_mem_of_notMem_sq
import Theorems.Thm_GroundTheory_LocalField_algebraMap_integer_injective
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_pos
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree)
    {α : 𝒪[L]} (hα : aeval α f = 0) :
    (f.natDegree : ℕ∞) * addVal 𝒪[L] α = ramificationIndex K L := by
  set n := f.natDegree with hn_def
  set e := ramificationIndex K L with he_def
  have he : 0 < e := ramificationIndex_pos K L
  have hinj := algebraMap_integer_injective K L
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [aeval_def, eval₂_at_zero] at hα
    have : f.coeff 0 = 0 := hinj (by rw [hα, map_zero])
    exact hf.notMem (by rw [this]; exact zero_mem _)
  obtain ⟨m, hm⟩ := exists_addVal_eq_coe hα0
  set t : ℕ → 𝒪[L] := fun i => algebraMap 𝒪[K] 𝒪[L] (f.coeff i) * α ^ i with ht
  have hsum : ∑ i ∈ Finset.range (n + 1), t i = 0 := by
    rw [← hα, aeval_eq_sum_range]
    simp [t, Algebra.smul_def, n]
  have hval : ∀ i, addVal 𝒪[L] (t i) = e * addVal 𝒪[K] (f.coeff i) + i * m := by
    intro i
    simp only [t, addVal_mul, addVal_pow, addVal_algebraMap_integer, hm, nsmul_eq_mul, e]

  have hlow : ∀ i < n, ((e + i * m : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (t i) := by
    intro i hi
    have h1 : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff i) := by
      have := hf.mem hi
      rw [← pow_one (IsLocalRing.maximalIdeal 𝒪[K]), mem_maximalIdeal_pow_iff_le_addVal] at this
      exact_mod_cast this
    rw [hval]
    push_cast
    gcongr
    calc (e : ℕ∞) = e * 1 := (mul_one _).symm
      _ ≤ e * addVal 𝒪[K] (f.coeff i) := by gcongr

  have htop : addVal 𝒪[L] (t n) = ((n * m : ℕ) : ℕ∞) := by
    have hu : IsUnit (f.coeff n) := by
      have := hf.leading
      rw [leadingCoeff] at this
      exact (IsLocalRing.notMem_maximalIdeal.mp this)
    rw [hval, addVal_eq_zero_iff.mpr hu]
    push_cast
    ring

  have hbot : addVal 𝒪[L] (t 0) = (e : ℕ∞) := by
    have h1 : f.coeff 0 ∈ IsLocalRing.maximalIdeal 𝒪[K] := hf.mem hn
    rw [hval, addVal_eq_one_of_mem_of_notMem_sq h1 hf.notMem]
    simp
  have hne_n : t n ≠ 0 := by
    intro h
    rw [h, addVal_zero] at htop
    exact ENat.top_ne_natCast _ htop
  have hne_0 : t 0 ≠ 0 := by
    intro h
    rw [h, addVal_zero] at hbot
    exact ENat.top_ne_natCast _ hbot

  have hA : e ≤ n * m := by
    by_contra hlt
    rw [not_le] at hlt
    refine hne_n (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.self_mem_range_succ n) ?_)
    intro i hi hin
    have hi' : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
    refine lt_of_lt_of_le ?_ (hlow i hi')
    rw [htop]
    exact_mod_cast (by omega : n * m < e + i * m)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hA
      omega
    · exact h

  have hB : n * m ≤ e := by
    by_contra hlt
    rw [not_le] at hlt
    refine hne_0 (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (by simp) ?_)
    intro i hi hi0
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hbot]
    rcases lt_or_eq_of_le hi' with hlt' | rfl
    · refine lt_of_lt_of_le ?_ (hlow i hlt')
      have : 1 ≤ i * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hi0 (by omega))
      exact_mod_cast (by omega : e < e + i * m)
    · rw [htop]
      exact_mod_cast hlt
  rw [hm]
  exact_mod_cast le_antisymm hB hA
end GroundTheory.LocalField
