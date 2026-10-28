-- Prove2me | solution 1 for MarkovProcess.PiContinuousMap.coordinateSubalgebra_topologicalClosure_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:24:39.843768+00:00
-- url     : https://prove2.me/submissions/12c56b87-ae94-425f-8492-25dbedbceb43

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
    [Fintype I] [T35Space α] [CompactSpace α] :
    (coordinateSubalgebra (I := I) (α := α)).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    MarkovProcess.PiContinuousMap.coordinateSubalgebra_separatesPoints
