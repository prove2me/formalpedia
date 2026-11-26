-- Prove2me | solution 1 for N4Code.onesOn_tupleWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:12.632851+00:00
-- url     : https://prove2.me/submissions/5c50143d-f245-4db5-b247-11ae27d3caab

import Definitions.Def_N4Code_Definitions
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Definitions.Def_N4Code_Basic

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (k : ℕ → ℕ) (g : Fin 16 → Finset (Fin n))
    (hg : GoodTuplePred C k g) {i : ℕ} (hi : i ∈ Finset.Icc 0 15) :
    onesOn (fiber C i) (tupleWord C g) = g ⟨i, by
      have hi' : i ≤ 15 := (Finset.mem_Icc.mp hi).2
      omega⟩ := by
  ext t
  simp [onesOn, fiber, tupleWord]
  constructor
  · intro ht
    simpa [ht.1] using ht.2
  · intro ht
    have hi' : i < 16 := by
      have hi'' : i ≤ 15 := (Finset.mem_Icc.mp hi).2
      omega
    have hg' : g ⟨i, hi'⟩ ∈ (fiber C i).powersetCard (k i) := hg ⟨i, hi'⟩
    have hsub : g ⟨i, hi'⟩ ⊆ fiber C i := (Finset.mem_powersetCard.mp hg').1
    have ht' : t ∈ fiber C i := hsub ht
    have hcol : colVal (C t) = i := (Finset.mem_filter.mp ht').2
    constructor
    · exact hcol
    · simpa [hcol] using ht
end N4Code
