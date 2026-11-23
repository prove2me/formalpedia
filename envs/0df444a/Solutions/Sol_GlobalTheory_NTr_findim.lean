-- Prove2me | solution 1 for GlobalTheory.NTr.findim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:54.426268+00:00
-- url     : https://prove2.me/submissions/4ea15a2a-e40e-4c73-9a37-9b4ade8a41b3

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.NTr
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
include hU
namespace GlobalTheory.NTr
theorem _root_.solution : FiniteDimensional F E :=
  Module.finite_of_finrank_eq_succ (hU.finrank_eq)
end GlobalTheory.NTr
