-- Prove2me | solution 1 for Kyprianou.Ch04.locallyAffinePathMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:28:22.875821+00:00
-- url     : https://prove2.me/submissions/1f681ea3-cf18-4298-afdc-4b0f0249e54f

import Mathlib
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

/-- A path agreeing on each integer horizon with a finite affine step function is measurable. -/
theorem solution {ι : Type} (U : NNReal → ℝ)
    (hU : ∀ n : ℕ, ∃ (S : Finset ι) (r a : ι → ℝ) (c d : ℝ),
      ∀ t : NNReal, t ≤ (n : NNReal) →
        U t = c + d * (t : ℝ) + ∑ i ∈ S, if r i ≤ (t : ℝ) then a i else 0) :
    Measurable U := by
  classical
  choose S r a c d h using hU
  let V (n : ℕ) (t : NNReal) :=
    c n + d n * (t : ℝ) + ∑ i ∈ S n, if r n i ≤ (t : ℝ) then a n i else 0
  have hV (n : ℕ) : Measurable (V n) := by
    apply Measurable.add
    · exact measurable_const.add (measurable_const.mul NNReal.continuous_coe.measurable)
    · apply Finset.measurable_sum
      intro i hi
      exact Measurable.ite (measurableSet_le measurable_const
        NNReal.continuous_coe.measurable) measurable_const measurable_const
  intro B hB
  have hs : U ⁻¹' B = ⋃ n : ℕ, Iic (n : NNReal) ∩ (V n ⁻¹' B) := by
    ext t
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_Iic]
    constructor
    · intro ht
      obtain ⟨n,hn⟩ := exists_nat_ge t
      have heq : U t = V n t := h n t hn
      exact ⟨n,hn,heq ▸ ht⟩
    · rintro ⟨n,hn,ht⟩
      have heq : U t = V n t := h n t hn
      rwa [heq]
  rw [hs]
  exact MeasurableSet.iUnion fun n => measurableSet_Iic.inter (hV n hB)
