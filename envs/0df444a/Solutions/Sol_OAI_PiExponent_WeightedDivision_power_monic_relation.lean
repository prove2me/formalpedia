-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.power_monic_relation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:26:46.351813+00:00
-- url     : https://prove2.me/submissions/1b575d87-1e77-46f3-81fa-1d80fb70b7bf

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Theorems.Thm_OAI_PiExponent_WeightedDivision_choose_monic_blocks
import Theorems.Thm_OAI_PiExponent_WeightedDivision_reduce_selected_monic_blocks

open scoped BigOperators

theorem solution
    {ι : Type*} {R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (d : ι → ℝ)
    (b : ι → ℕ) (hb : ∀ i, 0 < b i)
    (F : ι → MvPolynomial ι R)
    (hbelow : ∀ i, ∀ v ∈ (MvPolynomial.X i ^ b i - F i).support,
      (∑ j, d j * (v j : ℝ)) < d i * (b i : ℝ))
    (s : ℕ) (u : ι →₀ ℕ)
    (hu : s ≤ ∑ i, u i / b i) :
    ∃ G : MvPolynomial ι R,
      G ∈ (Ideal.span (Set.range F)) ^ s ∧
      ∀ v ∈ (MvPolynomial.monomial u (1 : R) - G).support,
        (∑ i, d i * (v i : ℝ)) < (∑ i, d i * (u i : ℝ)) := by
  obtain ⟨k, hkdiv, hksum⟩ :=
    OAI.PiExponent.WeightedDivision.choose_monic_blocks b hb u s hu
  exact OAI.PiExponent.WeightedDivision.reduce_selected_monic_blocks
    d b hb F hbelow s u k hkdiv hksum