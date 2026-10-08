-- Prove2me | solution 1 for MondererShapley.Participation.eq_6_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:50:12.060823+00:00
-- url     : https://prove2.me/submissions/8382aa24-4184-4995-bf4d-f8bb07da024f

import Mathlib
import Definitions.Def_MondererShapley_Participation_participationPayoff
open MondererShapley.Participation
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : Solution ι) (c : ι → ℝ)
    (v : Finset ι → ℝ) (i : ι) (ε : ι → Bool) :
    participationPayoff ψ c v i (Function.update ε i true) -
        participationPayoff ψ c v i (Function.update ε i false) =
      ψ (Finset.univ.filter (fun j => j ≠ i ∧ ε j = true) ∪ {i}) v i - c i := by
  have h : joiners (Function.update ε i true) =
      Finset.univ.filter (fun j => j ≠ i ∧ ε j = true) ∪ {i} := by
    ext j
    by_cases hj : j = i
    · subst j; simp [joiners]
    · simp [joiners, Function.update_of_ne hj, hj]
  simp [participationPayoff, h]
#print axioms solution
