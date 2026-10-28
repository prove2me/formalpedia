-- Prove2me | solution 1 for MarkovProcess.PiContinuousMap.coordinateSubalgebra_separatesPoints
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:14:32.852565+00:00
-- url     : https://prove2.me/submissions/fdf1a601-a29b-444d-b33d-e9dc8b313686

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_MarkovProcess_CoordinateProductAlgebras
open Topology MarkovProcess.PiContinuousMap
open scoped ZeroAtInfty
variable {I α : Type*} [TopologicalSpace α]

theorem solution [T35Space α] :
    (coordinateSubalgebra (I := I) (α := α)).SeparatesPoints := by
  intro x y hxy
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h; push_neg at h; exact hxy (funext h)
  obtain ⟨f, hfc, hf0, hf1⟩ := CompletelyRegularSpace.completely_regular (x i) {y i}
    isClosed_singleton (by simpa using hi)
  let F : C(α, ℝ) := ⟨fun a => (f a : ℝ), continuous_subtype_val.comp hfc⟩
  refine ⟨_, ⟨coordinate i F, coordinate_mem_coordinateSubalgebra i F, rfl⟩, ?_⟩
  have h1 : f (y i) = 1 := hf1 rfl
  simp [F, coordinate_apply, hf0, h1]
