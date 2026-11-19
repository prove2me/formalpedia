-- Prove2me | solution 1 for LevyStochCalc.Analysis.le_sortedGrid_card
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:57:33.964895+00:00
-- url     : https://prove2.me/submissions/1f47b65d-9acd-4b34-85b4-801e97c99408

import Definitions.Def_LevyStochCalc_Analysis_SortedGrid_F001

open Finset
open LevyStochCalc.Analysis

theorem solution {S : Finset ℝ} {x : ℝ} (hx : x ∈ S) :
    x ≤ sortedGrid S S.card := by
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hsub : S.card - 1 < S.card := Nat.sub_lt hpos one_pos
  have hcard : S.card = (S.card - 1) + 1 := (Nat.sub_add_cancel hpos).symm
  conv_rhs => rw [hcard, sortedGrid_succ_of_lt S hsub]
  let i : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨x, hx⟩
  have hi : x = S.orderEmbOfFin rfl i := by
    have hval := congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)
    rw [Finset.coe_orderIsoOfFin_apply] at hval
    exact hval.symm
  rw [hi]
  exact (S.orderEmbOfFin rfl).monotone (Nat.le_sub_one_of_lt i.isLt)
