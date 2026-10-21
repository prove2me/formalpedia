-- Prove2me | solution 1 for OAI.PiExponent.weighted_monic_staircase_remainder
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T07:43:01.556976+00:00
-- url     : https://prove2.me/submissions/1d01bada-da38-41ff-8dad-0ad523c94ac3

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Theorems.Thm_OAI_PiExponent_WeightedDivision_positive_weight_wellFounded
import Theorems.Thm_OAI_PiExponent_WeightedDivision_power_monic_relation
import Theorems.Thm_OAI_PiExponent_WeightedDivision_remainder_of_wellFounded_relations

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (hd : ∀ i, 0 < d i)
    (b : ι → ℕ) (hb : ∀ i, 0 < b i)
    (F : ι → MvPolynomial ι ℂ)
    (hbelow : ∀ i, ∀ u ∈ (MvPolynomial.X i ^ b i - F i).support,
      (∑ j, d j * (u j : ℝ)) < d i * (b i : ℝ))
    (s : ℕ) (P : MvPolynomial ι ℂ) :
    ∃ Q : MvPolynomial ι ℂ,
      P - Q ∈ (Ideal.span (Set.range F)) ^ s ∧
      ∀ u ∈ Q.support, (∑ i, u i / b i) < s := by
  classical
  let r : (ι →₀ ℕ) → (ι →₀ ℕ) → Prop := fun u v =>
    (∑ i, d i * (u i : ℝ)) < (∑ i, d i * (v i : ℝ))
  have hr : WellFounded r :=
    OAI.PiExponent.WeightedDivision.positive_weight_wellFounded d hd
  refine OAI.PiExponent.WeightedDivision.remainder_of_wellFounded_relations
    r hr ((Ideal.span (Set.range F)) ^ s)
    (fun u => (∑ i, u i / b i) < s) ?_ P
  intro u hu
  exact OAI.PiExponent.WeightedDivision.power_monic_relation
    d b hb F hbelow s u (Nat.le_of_not_gt hu)