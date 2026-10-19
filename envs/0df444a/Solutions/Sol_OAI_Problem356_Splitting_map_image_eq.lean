-- Prove2me | solution 1 for OAI.Problem356.Splitting.map_image_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:19:51.345276+00:00
-- url     : https://prove2.me/submissions/67ee7134-63c4-4be4-830f-e2b2b82f85b9

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


theorem solution
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

