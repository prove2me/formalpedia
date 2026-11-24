-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.quad_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:26:00.955414+00:00
-- url     : https://prove2.me/submissions/88908d38-3b00-4be8-8b37-c49a70929c49

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
variable {M : Type} [AddCommGroup M]
namespace GlobalTheory.Phase.ShapeOps
theorem _root_.solution {S S' : AddSubgroup M} {f : M → ℂ} (h : S' ≤ S) (hf : Quad S f) : Quad S' f :=
  ⟨fun x hx => hf.1 x (h hx), fun x hx y hy z hz => hf.2 x (h hx) y (h hy) z (h hz)⟩
end GlobalTheory.Phase.ShapeOps
