-- Prove2me | solution 1 for N4Code.tableK_815
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:13:20.718874+00:00
-- url     : https://prove2.me/submissions/26d384f8-f721-4423-86f6-c8eb6067d527

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution (a4 a5 a6 a7 : ℕ) : ∀ i ∈ Finset.Icc 8 15, tableK a4 a5 a6 a7 i = 0 := by
  intro i hi
  have h8 : 8 ≤ i := (Finset.mem_Icc.mp hi).1
  have h15 : i ≤ 15 := (Finset.mem_Icc.mp hi).2
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
