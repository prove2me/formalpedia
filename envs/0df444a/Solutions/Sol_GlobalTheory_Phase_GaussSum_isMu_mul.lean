-- Prove2me | solution 1 for GlobalTheory.Phase.GaussSum.isMu_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:25:58.035952+00:00
-- url     : https://prove2.me/submissions/514693a4-c678-4ff4-85fb-692dfac5b930

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSum

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
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.GaussSum
namespace GlobalTheory.Phase.GaussSum
theorem _root_.solution {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by
  obtain ⟨m, hm, h⟩ := ha
  obtain ⟨k, hk, h'⟩ := hb
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  rw [mul_pow, pow_mul, h, mul_comm m, pow_mul, h']; simp
end GlobalTheory.Phase.GaussSum
