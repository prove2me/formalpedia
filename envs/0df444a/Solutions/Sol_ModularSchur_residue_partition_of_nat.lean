-- Prove2me | solution 1 for ModularSchur.residue_partition_of_nat
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T22:56:02.598608+00:00
-- url     : https://prove2.me/submissions/a3b863ce-5b05-4911-b6f9-0bccb338d7cc

-- Generated from lean/ModularSchur/IntegerBridge.lean
--   imports : 0 platform node(s), 2 definition bundle(s)
--   inlined : 1 file-scoped / sub-threshold helper(s)
--   rename  : residue_partition_of_nat -> solution, hoisted out of the namespace
import Definitions.Def_ModularSchurIntegerBridge
import Definitions.Def_ModularSchurPartition
import Mathlib

open Finset
variable {m : ℕ}

namespace ModularSchur

/-- The cast `ℕ → ZMod m` is injective on `Ioc 0 (m-1)`. -/
lemma natCast_injOn_Ioc (hm : 2 ≤ m) :
    Set.InjOn ((↑) : ℕ → ZMod m) (Finset.Ioc 0 (m - 1) : Set ℕ) := by
  intro a ha b hb hab
  simp only [Finset.coe_Ioc, Set.mem_Ioc] at ha hb
  rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq,
      Nat.mod_eq_of_lt (by omega : a < m), Nat.mod_eq_of_lt (by omega : b < m)] at hab
  exact hab

end ModularSchur

open ModularSchur in
theorem solution (hm : 2 ≤ m) {ℓ k N : ℕ} (hN : N ≤ m - 1)
    {P : Fin k → Finset ℕ} (hP : IsValidPartitionNat m ℓ k N P) :
    ∃ Q : Fin k → Finset (ZMod m),
      IsValidPartition m ℓ k (stableResidues m N) Q := by
  refine ⟨fun i => (P i).image ((↑) : ℕ → ZMod m), ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [stableResidues, Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨i, hi⟩ := hP.covers a ha
    exact ⟨i, Finset.mem_image.mpr ⟨a, hi, rfl⟩⟩
  · intro i j hij
    rw [Finset.disjoint_iff_ne]
    rintro _ hx _ hy rfl
    simp only [Finset.mem_image] at hx hy
    obtain ⟨a, ha, hac⟩ := hx
    obtain ⟨b, hb, hbc⟩ := hy
    have ha_range : a ∈ Finset.Ioc 0 (m - 1) := by
      have := hP.subset i ha; simp only [Finset.mem_Ioc] at this ⊢; omega
    have hb_range : b ∈ Finset.Ioc 0 (m - 1) := by
      have := hP.subset j hb; simp only [Finset.mem_Ioc] at this ⊢; omega
    have hab : a = b :=
      natCast_injOn_Ioc hm ha_range hb_range (hac.trans hbc.symm)
    subst hab
    exact (Finset.disjoint_iff_ne.mp (hP.disjoint i j hij)) a ha a hb rfl
  · intro i x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact Finset.mem_image.mpr ⟨a, hP.subset i ha, rfl⟩
  · intro i f hf y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨y0, hy0, rfl⟩ := hy
    have : ∀ j : Fin ℓ, ∃ a : ℕ, a ∈ P i ∧ (a : ZMod m) = f j := by
      intro j
      have := hf j
      simp only [Finset.mem_image] at this
      exact this
    choose g hg using this
    have hg_mem : ∀ j, g j ∈ P i := fun j => (hg j).1
    have hg_cast : ∀ j, (g j : ZMod m) = f j := fun j => (hg j).2
    intro hsum
    have hg_sum : (((∑ j, g j) : ℕ) : ZMod m) = ∑ j, f j := by
      push_cast
      exact Finset.sum_congr rfl (fun j _ => hg_cast j)
    have hcast : (((∑ j, g j) : ℕ) : ZMod m) = (y0 : ZMod m) := by
      rw [hg_sum]; exact hsum
    have hmod : (∑ j, g j) % m = y0 % m := by
      rwa [ZMod.natCast_eq_natCast_iff, Nat.ModEq] at hcast
    exact hP.sumFree i g hg_mem y0 hy0 hmod
