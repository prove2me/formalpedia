-- Prove2me | solution 1 for MarkovProcess.PiContinuousMap.exists_coordinateSubalgebra_near
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:24:42.835868+00:00
-- url     : https://prove2.me/submissions/07df38a3-eded-4784-82b7-755d7b8aeea2

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_MarkovProcess_CoordinateProductAlgebras
import Theorems.Thm_MarkovProcess_PiContinuousMap_coordinateSubalgebra_separatesPoints
open Topology MarkovProcess.PiContinuousMap
open scoped ZeroAtInfty
variable {I α : Type*} [TopologicalSpace α]

theorem solution
    [Fintype I] [T35Space α] [CompactSpace α]
    (f : C(I → α, ℝ)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ g : coordinateSubalgebra (I := I) (α := α),
      ‖(g : C(I → α, ℝ)) - f‖ < epsilon :=
  ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints _
    MarkovProcess.PiContinuousMap.coordinateSubalgebra_separatesPoints f epsilon hepsilon
