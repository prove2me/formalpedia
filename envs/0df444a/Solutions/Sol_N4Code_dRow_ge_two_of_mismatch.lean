-- Prove2me | solution 1 for N4Code.dRow_ge_two_of_mismatch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:31.246832+00:00
-- url     : https://prove2.me/submissions/d57a2a76-7573-4cb0-8e3d-939eac9385c8

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dRow_eq_indicator_sum


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (j : Fin 4) (t₁ t₂ : Fin n)
    (htne : t₁ ≠ t₂) (y : Word n)
    (h1 : y t₁ ≠ row C j t₁) (h2 : y t₂ ≠ row C j t₂) : 2 ≤ dRow C j y := by
  rw [dRow_eq_indicator_sum]
  have hterm1 : (if colBit j (C t₁) ≠ y t₁ then 1 else 0) = 1 := by
    have : colBit j (C t₁) ≠ y t₁ := by
      simpa [row, colBit] using h1.symm
    simp [this]
  have hterm2 : (if colBit j (C t₂) ≠ y t₂ then 1 else 0) = 1 := by
    have : colBit j (C t₂) ≠ y t₂ := by
      simpa [row, colBit] using h2.symm
    simp [this]
  have hs1 := sum_split_at (fun u : Fin n => if colBit j (C u) ≠ y u then 1 else 0) t₁
  rw [hs1]
  have hs2 : (∑ u ∈ (Finset.univ.erase t₁), if colBit j (C u) ≠ y u then 1 else 0) =
      (∑ u ∈ (Finset.univ.erase t₁).erase t₂, if colBit j (C u) ≠ y u then 1 else 0) +
        (if colBit j (C t₂) ≠ y t₂ then 1 else 0) := by
    exact (Finset.sum_erase_add (Finset.univ.erase t₁)
      (fun u : Fin n => if colBit j (C u) ≠ y u then 1 else 0)
      (Finset.mem_erase.mpr ⟨htne.symm, Finset.mem_univ t₂⟩)).symm
  rw [hs2, hterm1, hterm2]
  omega
end N4Code
