-- Prove2me | solution 1 for GlobalTheory.Phase.Calc.isMu_of_ph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:09:44.601543+00:00
-- url     : https://prove2.me/submissions/54b83980-ccab-4592-9b3f-eb01060b7680

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
theorem _root_.solution {a : ℂ} (ha : Ph a) (h : ‖a‖ = 1) : IsMu a := by
  obtain ⟨m, hm, ha⟩ := ha
  exact ⟨m, hm, by rw [ha, h]; simp⟩
end GlobalTheory.Phase.Calc
