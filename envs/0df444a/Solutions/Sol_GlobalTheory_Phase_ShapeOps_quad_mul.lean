-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.quad_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:12.603991+00:00
-- url     : https://prove2.me/submissions/7563707d-f860-47ca-8f3a-603c61d2eaaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_mu_mul

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
theorem _root_.solution {S : AddSubgroup M} {f g : M → ℂ} (hf : Quad S f) (hg : Quad S g) :
    Quad S (fun x => f x * g x) := by
  refine ⟨fun x hx => mu_mul (hf.1 x hx) (hg.1 x hx), fun x hx y hy z hz => ?_⟩
  have h1 := hf.2 x hx y hy z hz
  have h2 := hg.2 x hx y hy z hz
  calc _ = (f (x + y + z) * f x * f y * f z) * (g (x + y + z) * g x * g y * g z) := by ring
    _ = _ := by rw [h1, h2]; ring
end GlobalTheory.Phase.ShapeOps
