-- Prove2me | solution 1 for OAI.Problem356.Splitting.no_preserving_branch_selection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:22:03.225758+00:00
-- url     : https://prove2.me/submissions/f350d3e7-0217-4a8d-bffd-f3d966e56328

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
theorem pb_compress {α ι : Type*} [MeasurableSpace α] [Countable ι]
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

theorem solution [Countable ι] [MeasurableEq α]
    {μ ν : Measure α} [IsFiniteMeasure ν] {B : Set α}
    {H : ι → α → α} {c d : ℝ≥0∞}
    (hν : ν Set.univ ≠ 0) (hB : MeasurableSet B)
    (hfull : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i))
    (himage : ∀ i S, MeasurableSet S → S ⊆ B →
      MeasurableSet (H i '' S))
    (hsource : ∀ S, MeasurableSet S → S ⊆ B → μ S = c * ν S)
    (htarget : ∀ i S, MeasurableSet S → S ⊆ B →
      μ (H i '' S) = d * ν S)
    (hdc : d < c) :
    ¬ ∃ T : α → α, Measurable T ∧ Measure.map T μ = μ ∧
      (∀ᵐ x ∂ν, ∃ i, T x = H i x) := by
  rintro ⟨T, hT, hmap, hsel⟩
  let S : ι → Set α := fun i => B ∩ {x | T x = H i x}
  have hSm : ∀ i, MeasurableSet (S i) := fun i => hB.inter (measurableSet_eq_fun hT (hH i))
  have hSB : ∀ i, S i ⊆ B := fun i => Set.inter_subset_left
  refine pb_compress (μ := μ) (ν := ν) (T := T) (S := S) (A := fun i => H i '' S i) hν
    (fun i => himage i (S i) (hSm i) (hSB i)) ?_ (fun i => hsource (S i) (hSm i) (hSB i))
    (fun i => htarget i (S i) (hSm i) (hSB i)) hdc ?_ ⟨hT, hmap⟩
  · intro i x hx
    exact ⟨x, hx, hx.2.symm⟩
  · filter_upwards [hfull, hsel] with x hx ⟨i, hi⟩
    exact ⟨i, hx, hi⟩

