-- Prove2me | solution 1 for MyersonBargaining.NashSolution.maximizer_strictly_dominates_conflict
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:33:31.82706+00:00
-- url     : https://prove2.me/submissions/eeccc5f3-0f83-4952-8cab-9f2110c3bd39

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Bargaining
set_option autoImplicit false
open MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

theorem solution
    (G : Problem ι A C) (cstar : C)
    (h : ∃ y ∈ FStar G, StrictlyDominates y (conflictPayoff G cstar))
    (x : (Σ i, A i) → ℝ) (hx : IsBargainingSolution G cstar x) :
    StrictlyDominates x (conflictPayoff G cstar) := by
  obtain ⟨y, hyF, hyd⟩ := h
  obtain ⟨hxP, hxmax⟩ := hx
  have hyP : y ∈ FPlus G cstar := ⟨hyF, fun k => (hyd k).le⟩
  have hypos : 0 < nashProduct G cstar y := by
    unfold nashProduct
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro a _
    exact Real.rpow_pos_of_pos (sub_pos.mpr (hyd ⟨i, a⟩)) _
  have hxpos : 0 < nashProduct G cstar x := lt_of_lt_of_le hypos (hxmax y hyP)
  rintro ⟨i, a⟩
  have hge : conflictPayoff G cstar ⟨i, a⟩ ≤ x ⟨i, a⟩ := hxP.2 ⟨i, a⟩
  rcases hge.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hm : 0 < marginal G.P i a := G.marginal_pos i a
    have h0 : (x ⟨i, a⟩ - conflictPayoff G cstar ⟨i, a⟩) ^ (marginal G.P i a) = 0 := by
      rw [← heq, sub_self]; exact Real.zero_rpow hm.ne'
    have : nashProduct G cstar x = 0 := by
      unfold nashProduct
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact Finset.prod_eq_zero (Finset.mem_univ a) h0
    linarith
