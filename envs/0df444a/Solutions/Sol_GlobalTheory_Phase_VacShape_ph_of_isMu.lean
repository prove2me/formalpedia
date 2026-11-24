-- Prove2me | solution 1 for GlobalTheory.Phase.VacShape.ph_of_isMu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:58:01.989729+00:00
-- url     : https://prove2.me/submissions/09a2d48b-5883-4304-b704-f7183d5d0cd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SelfDualVacuumGaussianShapeRootOfUnityPhases

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
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.VacShape
open GlobalTheory.SW.Vac
namespace GlobalTheory.Phase.VacShape
theorem _root_.solution {a : ℂ} (ha : IsMu a) : Ph a := by
  obtain ⟨m, hm, ha⟩ := ha
  refine ⟨m, hm, ?_⟩
  rw [← Complex.ofReal_pow, ← norm_pow, ha]; simp
end GlobalTheory.Phase.VacShape
