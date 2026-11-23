-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.twist_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:09.110475+00:00
-- url     : https://prove2.me/submissions/395214d9-588d-43a0-b3ff-3ec7d49ddd7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFrameProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {E : B.A} (hE : E * E = E) (x y : B.A) :
    (x * E + (1 - E)) * (y * E + (1 - E)) = x * y * E + (1 - E) := by
  linear_combination (x * y - x - y + 1) * hE
end GlobalTheory.UnitLemma.Desc
