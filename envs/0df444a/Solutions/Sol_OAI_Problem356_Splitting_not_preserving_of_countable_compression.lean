-- Prove2me | solution 1 for OAI.Problem356.Splitting.not_preserving_of_countable_compression
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:21:35.973263+00:00
-- url     : https://prove2.me/submissions/ed485a34-28dd-4bf9-ad84-4fadcb50b7c5

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment

open OAI OAI.Problem356
universe uAlpha uIndex
open MeasureTheory
open scoped ENNReal
variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]


theorem solution [Countable ι]
    {μ ν : Measure α} [IsFiniteMeasure ν]
    {T : α → α} {S A : ι → Set α} {c d : ℝ≥0∞}
    (hν : ν Set.univ ≠ 0)
    (hA : ∀ i, MeasurableSet (A i))
    (hsub : ∀ i, S i ⊆ T ⁻¹' A i)
    (hsource : ∀ i, μ (S i) = c * ν (S i))
    (htarget : ∀ i, μ (A i) = d * ν (S i))
    (hdc : d < c)
    (hcover : ∀ᵐ x ∂ν, ∃ i, x ∈ S i) :
    ¬ (Measurable T ∧ Measure.map T μ = μ) := by
  rintro ⟨hT, hmap⟩
  have hzero : ∀ i, ν (S i) = 0 := by
    intro i
    by_contra h0
    have hle : c * ν (S i) ≤ d * ν (S i) := by
      rw [← hsource, ← htarget]
      calc μ (S i) ≤ μ (T ⁻¹' A i) := measure_mono (hsub i)
        _ = Measure.map T μ (A i) := (Measure.map_apply hT (hA i)).symm
        _ = μ (A i) := by rw [hmap]
    have htop : ν (S i) ≠ ⊤ := measure_ne_top ν _
    have hlt : d * ν (S i) < c * ν (S i) := ENNReal.mul_lt_mul_left h0 htop hdc
    exact absurd hle (not_le.mpr hlt)
  have hae : ∀ᵐ x ∂ν, ∀ i, x ∉ S i := by
    rw [ae_all_iff]
    intro i
    exact measure_eq_zero_iff_ae_notMem.mp (hzero i)
  have hF : ∀ᵐ x ∂ν, False := by
    filter_upwards [hcover, hae] with x ⟨i, hi⟩ h
    exact h i hi
  apply hν
  simpa using ae_iff.mp hF

