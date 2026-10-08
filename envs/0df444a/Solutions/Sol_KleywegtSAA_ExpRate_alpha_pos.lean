-- Prove2me | solution 1 for KleywegtSAA.ExpRate.alpha_pos
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:11:09.377237+00:00
-- url     : https://prove2.me/submissions/3ebfd725-25d5-40f6-892f-19c013143968

import Mathlib
import Definitions.Def_KleywegtSAA_ExpRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology KleywegtSAA.ExpRate

theorem solution {X : Type*} (S : Finset X) (hS : S.Nonempty) (g : X → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hne : (nonOptSet S hS g ε).Nonempty) :
    0 < alpha S hS g ε hne := by
  classical
  obtain ⟨x, hx, heq⟩ := Finset.exists_mem_eq_inf' hne g
  have hgap := (Finset.mem_filter.mp hx).2
  unfold alpha
  rw [heq]
  linarith

#print axioms solution
