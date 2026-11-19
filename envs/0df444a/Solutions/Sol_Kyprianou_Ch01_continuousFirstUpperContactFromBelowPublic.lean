-- Prove2me | solution 1 for Kyprianou.Ch01.continuousFirstUpperContactFromBelowPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:08:25.569598+00:00
-- url     : https://prove2.me/submissions/cd6ac937-be69-4aa4-853d-2306f400c299

import Mathlib.Topology.Bornology.Real
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Closure
import Mathlib.Data.NNReal.Defs
import Theorems.Thm_Kyprianou_Ch01_continuousFirstUpperContactPublic
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology Kyprianou.Ch01
open scoped NNReal
set_option autoImplicit false

/-- A continuous path starting strictly below a barrier contacts it at first crossing. -/
theorem solution
    (f : ℝ≥0 → ℝ) (hcont : Continuous f) (s : ℝ)
    (hstart : f 0 < s)
    (hcross : ∃ t : ℝ≥0, 0 < t ∧ s < f t) :
    f (sInf {t : ℝ≥0 | 0 < t ∧ s < f t}) = s := by
  classical
  let S : Set ℝ≥0 := {t | 0 < t ∧ s < f t}
  let T : ℝ≥0 := sInf S
  have hclosed : IsClosed {t : ℝ≥0 | s ≤ f t} :=
    isClosed_Ici.preimage hcont
  have hsubset : S ⊆ {t : ℝ≥0 | s ≤ f t} := by
    rintro t ⟨_, ht⟩
    exact ht.le
  have hTge : s ≤ f T :=
    (closure_minimal hsubset hclosed)
      (csInf_mem_closure (show S.Nonempty from hcross) (OrderBot.bddBelow S))
  have hTpos : 0 < T := by
    by_contra hn
    have hzero : T = 0 := le_antisymm (le_of_not_gt hn) ((by positivity))
    rw [hzero] at hTge
    exact (not_le_of_gt hstart) hTge
  exact continuousFirstUpperContactPublic
    f hcont s hstart.le hcross hTpos
