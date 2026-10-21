-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.exists_bounded_fintype_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:40:02.782163+00:00
-- url     : https://prove2.me/submissions/35976b65-4235-4f3d-8b6e-bd99b9fe1170

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Theorems.Thm_OAI_PiExponent_WeightedDivision_exists_sigma_subset_card
import Theorems.Thm_OAI_PiExponent_WeightedDivision_sigma_fiber_card
import Theorems.Thm_OAI_PiExponent_WeightedDivision_sum_sigma_fiber_card

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (s : ℕ)
    (hs : s ≤ ∑ i, q i) :
    ∃ k : ι → ℕ, (∀ i, k i ≤ q i) ∧ (∑ i, k i = s) := by
  classical
  obtain ⟨t, ht⟩ := OAI.PiExponent.WeightedDivision.exists_sigma_subset_card q s hs
  refine ⟨fun i => (t.filter fun x : Σ j, Fin (q j) => x.1 = i).card, ?_, ?_⟩
  · intro i
    have hsub :
        t.filter (fun x : Σ j, Fin (q j) => x.1 = i) ⊆
          Finset.univ.filter (fun x : Σ j, Fin (q j) => x.1 = i) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2⟩
    calc
      (t.filter fun x : Σ j, Fin (q j) => x.1 = i).card ≤
          (Finset.univ.filter fun x : Σ j, Fin (q j) => x.1 = i).card :=
        Finset.card_le_card hsub
      _ = q i := OAI.PiExponent.WeightedDivision.sigma_fiber_card q i
  · calc
      (∑ i, (t.filter fun x : Σ j, Fin (q j) => x.1 = i).card) = t.card :=
        OAI.PiExponent.WeightedDivision.sum_sigma_fiber_card t
      _ = s := ht