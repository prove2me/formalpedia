-- Prove2me | solution 1 for MarkovProcess.PiContinuousMap.coordinateC0Subalgebra_separatesPoints
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:14:40.610954+00:00
-- url     : https://prove2.me/submissions/2c2aeb1c-9552-4e93-be11-03aa768cde55

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_MarkovProcess_CoordinateProductAlgebras
open Topology MarkovProcess.PiContinuousMap
open scoped ZeroAtInfty
variable {I α : Type*} [TopologicalSpace α]

theorem solution
    [T3Space α] [LocallyCompactSpace α] :
    (coordinateC0Subalgebra (I := I) (α := α)).SeparatesPoints := by
  intro x y hxy
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h; push_neg at h; exact hxy (funext h)
  obtain ⟨f, hf1, hf0, hfs, -⟩ := exists_continuous_one_zero_of_isCompact (X := α)
    (isCompact_singleton (x := x i)) (isClosed_singleton (x := y i))
    (Set.disjoint_singleton.2 hi)
  let F : C₀(α, ℝ) := ⟨f, HasCompactSupport.is_zero_at_infty hfs⟩
  refine ⟨_, ⟨coordinate i (F : C(α, ℝ)), coordinate_c0_mem_coordinateC0Subalgebra i F, rfl⟩, ?_⟩
  have h1 : f (x i) = 1 := hf1 rfl
  have h0 : f (y i) = 0 := hf0 rfl
  show f (x i) ≠ f (y i)
  rw [h1, h0]; norm_num
