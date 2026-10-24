-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_positive_exponents_have_common_multiple
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:51:18.274209+00:00
-- url     : https://prove2.me/submissions/fd4c01de-8edf-4d96-a054-94f3b49712db

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open OAI.PiExponent.FormalInterpolation

 theorem solution {ι : Type} [Fintype ι] (s : ι → Nat) (hs : ∀ i, 0 < s i) :
    ∃ S : Nat, 0 < S ∧ ∀ i, s i ∣ S := by
  classical
  refine ⟨∏ i, s i, ?_, ?_⟩
  · exact Finset.prod_pos (fun i _ => hs i)
  · intro i
    exact Finset.dvd_prod_of_mem s (Finset.mem_univ i)