-- Prove2me | solution 1 for GlobalTheory.Phase.Calc.ph_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:38.471823+00:00
-- url     : https://prove2.me/submissions/64574089-5ca8-43e3-b804-0c8bf2758607

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ComplexPhaseCalculusRootOfUnity

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
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.Calc
namespace GlobalTheory.Phase.Calc
theorem _root_.solution {a : ℂ} (ha : Ph a) : Ph a⁻¹ := by
  obtain ⟨m, hm, ha⟩ := ha
  refine ⟨m, hm, ?_⟩
  rw [inv_pow, ha, norm_inv, Complex.ofReal_inv, inv_pow]
end GlobalTheory.Phase.Calc
