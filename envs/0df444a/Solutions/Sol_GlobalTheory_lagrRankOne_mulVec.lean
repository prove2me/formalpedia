-- Prove2me | solution 1 for GlobalTheory.lagrRankOne_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:14:33.955268+00:00
-- url     : https://prove2.me/submissions/726cc94a-9bc6-43ca-9c19-92eae6ec80b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleLagrangianTransverseField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k : Type} [Field k] {n : ℕ}
    (S : Matrix (Fin n) (Fin n) k) (j : Fin n) (v : Fin n → k) :
    lagrRankOne S j *ᵥ v = Pi.single j ((v ᵥ* S) j) := by
  funext a
  by_cases h : a = j
  · subst h; simp [lagrRankOne, mulVec, vecMul, dotProduct, mul_comm]
  · simp [lagrRankOne, mulVec, dotProduct, h]
end GlobalTheory
