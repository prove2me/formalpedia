-- Prove2me | solution 1 for Nullstellensatz.fta_restatement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T19:40:56.73417+00:00
-- url     : https://prove2.me/submissions/08df29a0-d150-41ad-8f18-eb344b9ff2aa

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem fta_restatement_aux (P : Polynomial ℂ) :
    (∃ z : ℂ, P.IsRoot z) ↔ P.degree ≠ 0 := by
  constructor
  · rintro ⟨z, hz⟩
    intro hcon
    -- `hcon` says `P` is a constant; `hz` says `P.eval z = 0`, so `P = 0`,
    -- but then `P.degree = ⊥`, contradicting `P.degree ≠ 0`.
    have hconst : P = Polynomial.C (P.coeff 0) :=
      Polynomial.eq_C_of_degree_eq_zero hcon
    have hzero : P.coeff 0 = 0 := by
      have heval := congrArg (fun q : Polynomial ℂ => q.eval z) hconst
      rw [Polynomial.eval_C, hz] at heval
      exact heval.symm
    have hPzero : P = 0 := by
      rw [hconst]
      exact Polynomial.ext_iff.mpr fun n => by
        by_cases hn : n = 0
        · simpa [hzero]
        · exact Polynomial.coeff_C_ne_zero hn
    rw [hPzero, Polynomial.degree_zero] at hcon
    exact absurd hcon (by simp)
  · intro hdeg
    by_cases hzero : P = 0
    · refine ⟨0, ?_⟩
      rw [hzero, Polynomial.IsRoot.def]
      exact Polynomial.eval_zero
    · have hnunit : ¬ IsUnit P := by
        intro hu
        exact hdeg (Polynomial.isUnit_iff_degree_eq_zero.mp hu)
      have hpos : 0 < P.degree :=
        Polynomial.degree_pos_of_ne_zero_of_nonunit hzero hnunit
      exact Complex.exists_root hpos

end Nullstellensatz

open Nullstellensatz

theorem solution (P : Polynomial ℂ) :
    (∃ z : ℂ, P.IsRoot z) ↔ P.degree ≠ 0 :=
  fta_restatement_aux P
