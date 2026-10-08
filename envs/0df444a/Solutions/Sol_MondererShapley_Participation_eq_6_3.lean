-- Prove2me | solution 1 for MondererShapley.Participation.eq_6_3
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:23:35.571765+00:00
-- url     : https://prove2.me/submissions/fbc0c538-a3eb-44d8-8e70-73f660cfbe31

import Mathlib
import Definitions.Def_MondererShapley_Participation_Solution
import Definitions.Def_MondererShapley_Participation_profileOf
open MondererShapley.Participation


/-- (6.3): with `P(ε_S) = Q(ε_S) + ∑_{i∈S} cⁱ`, `Q` satisfies (6.2) iff `P` satisfies
`P(ε_S) − P(ε_{S∖{i}}) = ψ(v_{S∪{i}})(i)` for all `S ⊆ N` and every `i ∈ S`. -/
theorem solution {ι : Type*} [DecidableEq ι] (ψ : Solution ι) (c : ι → ℝ)
    (v : Finset ι → ℝ) (Q : (ι → Bool) → ℝ) (P : Finset ι → ℝ)
    (hP : ∀ S : Finset ι, P S = Q (profileOf S) + ∑ i ∈ S, c i) :
    (∀ S : Finset ι, ∀ i ∈ S,
        Q (profileOf S) - Q (profileOf (S \ {i})) = ψ (S ∪ {i}) v i - c i) ↔
      ∀ S : Finset ι, ∀ i ∈ S, P S - P (S \ {i}) = ψ (S ∪ {i}) v i := by
  have hs (S : Finset ι) (i : ι) (hi : i ∈ S) :
      (∑ j ∈ S, c j) = (∑ j ∈ S \ {i}, c j) + c i := by
    simpa using (Finset.sum_sdiff (f := c) (Finset.singleton_subset_iff.mpr hi)).symm
  constructor
  · intro h S i hi
    rw [hP S, hP (S \ {i})]
    have := h S i hi
    have := hs S i hi
    linarith
  · intro h S i hi
    have := h S i hi
    rw [hP S, hP (S \ {i})] at this
    have := hs S i hi
    linarith

#print axioms solution
