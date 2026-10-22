-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finsum_coordinate_pole_le_weighted
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:33:23.195066+00:00
-- url     : https://prove2.me/submissions/529328b1-5a26-48eb-a41a-98590800af4b

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

theorem solution {α : Type} (c : Real) (hc : 0 ≤ c) (f g : α → Real)
    (hf : Set.Finite {a | f a ≠ 0}) (hg : Set.Finite {a | g a ≠ 0})
    (hfg : ∀ a, 0 ≤ f a ∧ f a ≤ c * g a) :
    (∑ᶠ a, f a) ≤ c * (∑ᶠ a, g a) := by
  classical
  by_cases hc0 : c = 0
  · have hf0 : f = 0 := by
      ext a
      exact le_antisymm ((hfg a).2.trans (by simp [hc0])) (hfg a).1
    simp [hf0, hc0]
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    let s := hf.toFinset ∪ hg.toFinset
    have hf_sub : Function.support f ⊆ ↑s := by
      intro a ha
      simp only [Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union, s]
      left
      simpa [Function.mem_support] using ha
    have hg_sub : Function.support g ⊆ ↑s := by
      intro a ha
      simp only [Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union, s]
      right
      simpa [Function.mem_support] using ha
    have hf_sum : ∑ᶠ a, f a = ∑ a ∈ s, f a :=
      finsum_eq_finsetSum_of_support_subset f hf_sub
    have hg_sum : ∑ᶠ a, g a = ∑ a ∈ s, g a :=
      finsum_eq_finsetSum_of_support_subset g hg_sub
    rw [hf_sum, hg_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => (hfg a).2
