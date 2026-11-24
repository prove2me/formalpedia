-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.mu_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:13.916282+00:00
-- url     : https://prove2.me/submissions/bfeeccbd-8b36-4e8e-b6e3-00d86656d6a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.ShapeOps
namespace GlobalTheory.Phase.ShapeOps
theorem _root_.solution {a : ℂ} (ha : IsMu a) : a ≠ 0 := by
  obtain ⟨m, hm, ha⟩ := ha
  rintro rfl
  rw [zero_pow hm.ne'] at ha
  exact zero_ne_one ha
end GlobalTheory.Phase.ShapeOps
