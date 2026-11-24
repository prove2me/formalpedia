-- Prove2me | solution 1 for GlobalTheory.Phase.VacShape.isMu_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:57:00.618188+00:00
-- url     : https://prove2.me/submissions/6daa88d8-203f-4437-8a0d-65d091096e3f

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
theorem _root_.solution {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [mul_pow, pow_mul a, ha, pow_mul' b, hb]; simp
end GlobalTheory.Phase.VacShape
