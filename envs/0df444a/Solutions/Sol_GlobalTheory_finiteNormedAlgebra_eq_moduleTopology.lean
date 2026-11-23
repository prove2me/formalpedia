-- Prove2me | solution 1 for GlobalTheory.finiteNormedAlgebra_eq_moduleTopology
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:14.405956+00:00
-- url     : https://prove2.me/submissions/ca2ff047-4a0d-4088-82d2-0e82626c4b76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory
open MeasureTheory Filter Topology
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] (R : Type) [N : NormedCommRing R] [NormedAlgebra F R]
    [Module.Finite F R] :
    N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      = moduleTopology F R := by
  haveI : IsModuleTopology F R := isModuleTopologyOfFiniteDimensional
  exact eq_moduleTopology F R
end _root_.GlobalTheory
end GlobalTheory
