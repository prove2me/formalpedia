-- Prove2me | solution 1 for Kyprianou.Ch04.unboundedBelowOfVanishingLaplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:32:08.838444+00:00
-- url     : https://prove2.me/submissions/2b4c9a4c-0133-4f4d-8ad9-5e2499fb0510

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (g : ℕ → ℝ) (beta : ℝ)
    (hlim : Tendsto g atTop (nhds 0))
    (hbound : ∀ (K n : ℕ),
      Real.exp (-beta * (K : ℝ)) *
        (P {w | ∀ t : NNReal, -(K : ℝ) ≤ X t w}).toReal ≤ g n) :
    P {w | BddBelow (Set.range (fun t : NNReal => X t w))} = 0 := by
  let E : ℕ → Set Omega := fun K =>
    {w | ∀ t : NNReal, -(K : ℝ) ≤ X t w}
  have hz (K : ℕ) : P (E K) = 0 := by
    have hle : Real.exp (-beta * (K : ℝ)) * (P (E K)).toReal ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlim
        (Eventually.of_forall (hbound K))
    have hreal : (P (E K)).toReal = 0 := by
      have he := Real.exp_pos (-beta * (K : ℝ))
      have hnn := ENNReal.toReal_nonneg (a := P (E K))
      nlinarith
    have hh := ENNReal.ofReal_toReal (measure_ne_top P (E K))
    rw [hreal, ENNReal.ofReal_zero] at hh
    exact hh.symm
  have heq : {w | BddBelow (Set.range (fun t : NNReal => X t w))} =
      ⋃ K : ℕ, E K := by
    ext w
    constructor
    · intro hw
      obtain ⟨b, hb⟩ := hw
      obtain ⟨K, hK⟩ := exists_nat_gt (-b)
      apply mem_iUnion.2
      refine ⟨K, ?_⟩
      intro t
      have hx : b ≤ X t w := hb ⟨t, rfl⟩
      linarith
    · intro hw
      obtain ⟨K, hK⟩ := mem_iUnion.1 hw
      refine ⟨-(K : ℝ), ?_⟩
      rintro x ⟨t, rfl⟩
      exact hK t
  rw [heq]
  exact measure_iUnion_null hz
