-- Prove2me | solution 1 for HodgeComputer.NormalChart.residue_eq_divergenceNumerator
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T01:45:20.44221+00:00
-- url     : https://prove2.me/submissions/09647254-13bc-4f7b-b0ec-69cef8212b2d

import Definitions.Def_HodgeComputerNormalChart
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open HodgeComputer HodgeComputer.NormalChart MvPolynomial
open scoped BigOperators

private theorem mixed_partials (F : AmbientPoly 5) (i j : Fin 6) :
    pderiv i (pderiv j F) = pderiv j (pderiv i F) := by
  ext m
  simp only [coeff_pderiv]
  have he : m + Finsupp.single i 1 + Finsupp.single j 1 =
      m + Finsupp.single j 1 + Finsupp.single i 1 := by ac_rfl
  rw [he]
  by_cases hij : i = j
  · subst j
    rfl
  · simp [Finsupp.add_apply, Finsupp.single_apply, hij, Ne.symm hij]
    ring

theorem solution (F A S : AmbientPoly 5) (W : Fin 5 → AmbientPoly 5) :
    residue F A S W = divergenceNumerator (denominator F S) (numerator F A S W) := by
  have hc (j : Fin 5) : pderiv 0 (pderiv j.succ F) = pderiv j.succ (normal F) :=
    mixed_partials F 0 j.succ
  -- Prove the swapped identity then symmetrize.
  have h : divergenceNumerator (denominator F S) (numerator F A S W) = residue F A S W := by
    simp only [divergenceNumerator, divergence, directional, Fin.sum_univ_succ,
      numerator, Fin.cases_zero, Fin.cases_succ, denominator, residue,
      map_sub, map_add, map_sum, pderiv_mul, hc]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    ring
  exact h.symm
