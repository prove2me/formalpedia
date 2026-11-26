-- Prove2me | solution 1 for Kyprianou.Ch04.continuousGeneratorZeroOfPositiveIntervals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:01:47.793962+00:00
-- url     : https://prove2.me/submissions/36646bff-ddf5-4bfc-8fed-0fda7c43d6d3

import Mathlib

open MeasureTheory
set_option autoImplicit false

/-- An almost-sure generator identity for a continuous residual is
pointwise wherever the marginal charges every nonempty real interval.
This supplies the final full-support step of Exercise 4.3(iii). -/
theorem solution
    (μ : Measure ℝ)
    (hFull : ∀ a b : ℝ, a < b → 0 < μ (Set.Ioo a b))
    (G : ℝ → ℝ) (hContinuous : Continuous G)
    (hAE : ∀ᵐ y ∂μ, G y = 0) :
    ∀ y : ℝ, G y = 0 := by
  intro y
  by_contra hy
  have hOpen : IsOpen {z : ℝ | G z ≠ 0} := by
    have hClosed : IsClosed (G ⁻¹' ({0} : Set ℝ)) :=
      isClosed_singleton.preimage hContinuous
    convert hClosed.isOpen_compl using 1
    ext z
    simp
  obtain ⟨a, b, hab, hSub⟩ :=
    hOpen.exists_Ioo_subset (show {z : ℝ | G z ≠ 0}.Nonempty from ⟨y, hy⟩)
  have hNull : μ (Set.Ioo a b) = 0 := by
    have hNo : ∀ᵐ z ∂μ, z ∉ Set.Ioo a b :=
      hAE.mono (fun z hz hzMem => hSub hzMem hz)
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hNo
  exact (ne_of_gt (hFull a b hab)) hNull
