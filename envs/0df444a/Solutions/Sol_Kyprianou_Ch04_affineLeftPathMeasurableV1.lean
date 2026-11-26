-- Prove2me | solution 1 for Kyprianou.Ch04.affineLeftPathMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:39:02.988383+00:00
-- url     : https://prove2.me/submissions/126b3f8a-b740-4a7e-9606-d97ba5b28626

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_affineStepLeftLimitV1
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Any positive-time left-limit version of a locally finite affine-step path is measurable in time. -/
theorem solution {ι : Type} (U L : NNReal → ℝ)
    (hU : ∀ n : ℕ, ∃ (S : Finset ι) (r a : ι → ℝ) (c d : ℝ),
      ∀ t : NNReal, t ≤ (n : NNReal) →
        U t = c + d * (t : ℝ) + ∑ i ∈ S, if r i ≤ (t : ℝ) then a i else 0)
    (hL : ∀ t : NNReal, 0 < t → Tendsto U (𝓝[<] t) (𝓝 (L t))) :
    Measurable L := by
  classical
  choose S r a c d h using hU
  let V (n : ℕ) (t : NNReal) :=
    if t = 0 then L 0 else
      c n + d n * (t : ℝ) + ∑ i ∈ S n, if r n i < (t : ℝ) then a n i else 0
  have hV (n : ℕ) : Measurable (V n) := by
    apply Measurable.ite (measurableSet_singleton 0) measurable_const
    apply Measurable.add
    · exact measurable_const.add (measurable_const.mul NNReal.continuous_coe.measurable)
    · apply Finset.measurable_sum
      intro i hi
      exact Measurable.ite (measurableSet_lt measurable_const
        NNReal.continuous_coe.measurable) measurable_const measurable_const
  have heq (n : ℕ) (t : NNReal) (ht : t ≤ (n : NNReal)) : L t = V n t := by
    by_cases hz : t = 0
    · simp [V,hz]
    · have hp : 0 < t := pos_iff_ne_zero.mpr hz
      simp only [V, if_neg hz]
      exact Kyprianou.Ch04.affineStepLeftLimitV1 U (S n) (r n) (a n)
        (c n) (d n) t n hp ht (h n) (L t) (hL t hp)
  intro B hB
  have hs : L ⁻¹' B = ⋃ n : ℕ, Iic (n : NNReal) ∩ (V n ⁻¹' B) := by
    ext t
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_Iic]
    constructor
    · intro ht
      obtain ⟨n,hn⟩ := exists_nat_ge t
      exact ⟨n,hn,heq n t hn ▸ ht⟩
    · rintro ⟨n,hn,ht⟩
      rwa [heq n t hn]
  rw [hs]
  exact MeasurableSet.iUnion fun n => measurableSet_Iic.inter (hV n hB)
