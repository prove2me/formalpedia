-- Prove2me | solution 1 for N4Code.tableZ_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:17.212972+00:00
-- url     : https://prove2.me/submissions/743c10e4-0839-493a-b4c3-ed7faed43697

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (a1 a2 a3 a4 a5 a6 a7 : ℕ)
    (h1 : a1 ≤ count C 1) (h2 : a2 ≤ count C 2) (h3 : a3 ≤ count C 3)
    (h4 : a4 ≤ count C 4) (h5 : a5 ≤ count C 5) (h6 : a6 ≤ count C 6)
    (h7 : a7 ≤ count C 7) :
    ∀ i ∈ Finset.Icc 0 15, tableZ a1 a2 a3 a4 a5 a6 a7 i ≤ count C i := by
  intro i hi
  by_cases hi1 : i = 1
  · subst i
    simp [tableZ, h1]
  · by_cases hi2 : i = 2
    · subst i
      simp [tableZ, h2]
    · by_cases hi3 : i = 3
      · subst i
        simp [tableZ, h3]
      · by_cases hi4 : i = 4
        · subst i
          simp [tableZ, h4]
        · by_cases hi5 : i = 5
          · subst i
            simp [tableZ, h5]
          · by_cases hi6 : i = 6
            · subst i
              simp [tableZ, h6]
            · by_cases hi7 : i = 7
              · subst i
                simp [tableZ, h7]
              · simp [tableZ, hi1, hi2, hi3, hi4, hi5, hi6, hi7]
end N4Code
