-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.mu_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:25:56.803215+00:00
-- url     : https://prove2.me/submissions/f847b5d6-e7d3-4f95-bf6c-fbc181fa8fef

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
theorem _root_.solution {a : ℂ} (ha : IsMu a) : IsMu (conj a) := by
  obtain ⟨m, hm, ha⟩ := ha
  exact ⟨m, hm, by rw [← map_pow, ha, map_one]⟩
end GlobalTheory.Phase.ShapeOps
