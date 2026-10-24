-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.finset_sum_eq_subtype_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:33:08.565091+00:00
-- url     : https://prove2.me/submissions/7261c185-b317-438b-8d0b-7b7814df5a58

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open Classical
open scoped BigOperators

theorem solution {α : Type*} [DecidableEq α] (s : Finset α) (g : α → Complex) :
    (∑ a ∈ s, g a) = ∑ c : {a // a ∈ s}, g c.1 := by
  classical
  have hs : s.attach = Finset.univ := by
    ext c
    simp
  calc
    (∑ a ∈ s, g a) = ∑ c ∈ s.attach, g c := (Finset.sum_attach s g).symm
    _ = ∑ c : {a // a ∈ s}, g c.1 := by rw [hs]