-- Prove2me | solution 1 for GlobalTheory.QFam.HasQ.const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:41:26.608267+00:00
-- url     : https://prove2.me/submissions/b1fb6a99-ccec-4d2b-8c0e-b7897c965f00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
namespace HasQ
theorem _root_.solution {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (c : ℂ) (hf : HasQ N f a) :
    HasQ N (fun τ => c * f τ) (fun n => c * a n) := by
  intro τ
  simpa only [mul_assoc] using (hf τ).mul_left c
end HasQ
end GlobalTheory.QFam
