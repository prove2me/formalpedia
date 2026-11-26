-- Prove2me | solution 1 for N4Code.tableK_bounds_47
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:58.463406+00:00
-- url     : https://prove2.me/submissions/606d34ac-df24-4ea9-a6ae-09f35d618829

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_tableK_bounds

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (a4 a5 a6 a7 : ℕ)
    (hcnt0 : 1 ≤ count C 0) (ha4 : a4 ≤ count C 4) (ha5 : a5 ≤ count C 5)
    (ha6 : a6 ≤ count C 6) (ha7 : a7 ≤ count C 7) :
    ∀ i ∈ Finset.Icc 4 7, tableK a4 a5 a6 a7 i ≤ count C i := by
  intro i hi
  exact (tableK_bounds C a4 a5 a6 a7 hcnt0 ha4 ha5 ha6 ha7) i
    (by simp [Finset.mem_Icc] at hi ⊢; omega)
end N4Code
