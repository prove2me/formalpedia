-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.quad_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:40:06.704685+00:00
-- url     : https://prove2.me/submissions/e40e5880-0d97-4378-a067-f9497f5928ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_mu_conj

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
theorem _root_.solution {S : AddSubgroup M} {f : M → ℂ} (hf : Quad S f) : Quad S (fun x => conj (f x)) := by
  refine ⟨fun x hx => mu_conj (hf.1 x hx), fun x hx y hy z hz => ?_⟩
  have h1 := congrArg conj (hf.2 x hx y hy z hz)
  simpa only [map_mul] using h1
end GlobalTheory.Phase.ShapeOps
