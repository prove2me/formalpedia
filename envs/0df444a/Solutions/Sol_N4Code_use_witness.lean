-- Prove2me | solution 1 for N4Code.use_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:34.918978+00:00
-- url     : https://prove2.me/submissions/5313171e-b20b-4802-876c-5aa21615df3c

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_witness_from_k
import Theorems.Thm_N4Code_tableK_0
import Theorems.Thm_N4Code_tableK_03
import Theorems.Thm_N4Code_tableK_815
import Theorems.Thm_N4Code_tableK_bounds_47

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h07 : Columns07 C) (hcnt0 : 1 ≤ count C 0)
    (a4 a5 a6 a7 : ℕ)
    (ha4 : a4 ≤ count C 4) (ha5 : a5 ≤ count C 5) (ha6 : a6 ≤ count C 6)
    (ha7 : a7 ≤ count C 7)
    (hmid : 2 * (a4 + a5 + a6 + a7) = count C 4 + count C 5 + count C 6 + count C 7)
    (hge2 : 2 * a6 + 2 * a7 ≤ count C 2 + count C 3 + count C 6 + count C 7)
    (hge3 : 2 * a5 + 2 * a7 ≤ count C 1 + count C 3 + count C 5 + count C 7) :
    ∃ t : Fin n, C t = col0 ∧ ∃ y : Word n, Y3c C col5 colZeros_col5_nonempty
      colOnes_col5_nonempty t y := by
  let k : ℕ → ℕ := tableK a4 a5 a6 a7
  have hk4 : k 4 = a4 := by simp [k, tableK]
  have hk5 : k 5 = a5 := by simp [k, tableK]
  have hk6 : k 6 = a6 := by simp [k, tableK]
  have hk7 : k 7 = a7 := by simp [k, tableK]
  exact witness_from_k C h07 k hcnt0 (tableK_0 a4 a5 a6 a7) (tableK_03 a4 a5 a6 a7)
    (by simpa [k] using tableK_bounds_47 C a4 a5 a6 a7 hcnt0 ha4 ha5 ha6 ha7)
    (tableK_815 a4 a5 a6 a7)
    (by
      rw [hk4, hk5, hk6, hk7]
      exact hmid)
    (by
      rw [hk6, hk7]
      exact hge2)
    (by
      rw [hk5, hk7]
      exact hge3)
end N4Code
