-- Prove2me | solution 1 for OAI.Problem356.Splitting.splitMeasure_apply_image
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:20:01.369405+00:00
-- url     : https://prove2.me/submissions/cddf9fc7-868f-4ff9-9925-1407bb7b8d74

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
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure

open OAI OAI.Problem356 OAI.Problem356.Splitting
universe uAlpha uIndex
open MeasureTheory Set
open scoped ENNReal
variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]
variable [Fintype ι]
theorem pb_map_image_eq {α : Type*} [MeasurableSpace α]
    (ν : Measure α) {B S : Set α} {H : α → α}
    (hν : ∀ᵐ x ∂ν, x ∈ B) (hH : Measurable H)
    (hInj : Set.InjOn H B) (hSB : S ⊆ B)
    (hImage : MeasurableSet (H '' S)) :
    (Measure.map H ν) (H '' S) = ν S := by
  rw [Measure.map_apply hH hImage]
  apply measure_congr
  filter_upwards [hν] with x hx
  apply propext
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := hInj (hSB hy) hx hxy
    show x ∈ S
    exact this ▸ hy
  · intro h
    exact ⟨x, h, rfl⟩

theorem solution
    (ν : Measure α) (a : ℝ≥0∞) (b : ι → ℝ≥0∞) (H : ι → α → α)
    {B S : Set α} (hν : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i)) (hInj : ∀ i, Set.InjOn (H i) B)
    (hSB : S ⊆ B) (hImage : ∀ i, MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B)) (j : ι) :
    splitMeasure ν a b H (H j '' S) = b j * ν S := by
  classical
  have h0 : ν (H j '' S) = 0 := by
    apply measure_mono_null_ae (t := Bᶜ)
    · filter_upwards with x hx
      exact Set.disjoint_right.mp (hCentral j) (Set.image_mono hSB hx)
    · exact ae_iff.mp hν
  have hi : ∀ i, i ≠ j → Measure.map (H i) ν (H j '' S) = 0 := by
    intro i hij
    rw [Measure.map_apply (hH i) (hImage j)]
    apply measure_mono_null_ae (t := Bᶜ)
    · filter_upwards with x hmem hx
      exact Set.disjoint_left.mp (hPair hij) ⟨x, hx, rfl⟩ (Set.image_mono hSB hmem)
    · exact ae_iff.mp hν
  simp only [splitMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul, h0, mul_zero,
    zero_add, Measure.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [hi i hij, mul_zero]) (by simp),
    pb_map_image_eq ν hν (hH j) (hInj j) hSB (hImage j)]

