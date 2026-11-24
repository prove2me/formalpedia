-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.mu_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:25:58.311796+00:00
-- url     : https://prove2.me/submissions/b7d4c1f3-816a-465d-a9a7-5f373d3ae811

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
theorem _root_.solution {a : ℂ} (ha : IsMu a) : IsMu a⁻¹ := by
  obtain ⟨m, hm, ha⟩ := ha
  exact ⟨m, hm, by rw [inv_pow, ha, inv_one]⟩
end GlobalTheory.Phase.ShapeOps
