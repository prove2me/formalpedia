-- Prove2me | solution 1 for N4Code.tableK_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:16.661013+00:00
-- url     : https://prove2.me/submissions/38fcf664-f3e7-444c-a3d3-3d1b8bf93b28

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_tableK_0

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (a4 a5 a6 a7 : ℕ)
    (hcnt0 : 1 ≤ count C 0) (ha4 : a4 ≤ count C 4) (ha5 : a5 ≤ count C 5)
    (ha6 : a6 ≤ count C 6) (ha7 : a7 ≤ count C 7) :
    ∀ i ∈ Finset.Icc 0 15, tableK a4 a5 a6 a7 i ≤ count C i := by
  intro i hi
  have hi7 : i ≤ 15 := (Finset.mem_Icc.mp hi).2
  by_cases hi0 : i = 0
  · rw [hi0, tableK_0]
    exact hcnt0
  · by_cases hi1 : i = 1
    · subst i
      simp [tableK]
    · by_cases hi2 : i = 2
      · subst i
        simp [tableK]
      · by_cases hi3 : i = 3
        · subst i
          simp [tableK]
        · by_cases hi4 : i = 4
          · subst i
            simp [tableK]
            exact ha4
          · by_cases hi5 : i = 5
            · subst i
              simp [tableK]
              exact ha5
            · by_cases hi6 : i = 6
              · subst i
                simp [tableK]
                exact ha6
              · by_cases hi7' : i = 7
                · subst i
                  simp [tableK]
                  exact ha7
                · have h8 : 8 ≤ i := by omega
                  have h0 : i ≠ 0 := by omega
                  have h1 : i ≠ 1 := by omega
                  have h2 : i ≠ 2 := by omega
                  have h3 : i ≠ 3 := by omega
                  have h4 : i ≠ 4 := by omega
                  have h5 : i ≠ 5 := by omega
                  have h6 : i ≠ 6 := by omega
                  have h7 : i ≠ 7 := by omega
                  simp [tableK, h0, h1, h2, h3, h4, h5, h6, h7]
end N4Code
