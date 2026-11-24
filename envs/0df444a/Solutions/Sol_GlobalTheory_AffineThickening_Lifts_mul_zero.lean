-- Prove2me | solution 1 for GlobalTheory.AffineThickening.Lifts.mul_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:07:13.590857+00:00
-- url     : https://prove2.me/submissions/ea06eaa3-b897-421a-8495-037a2d2ff926

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)
variable {i}
open GlobalTheory.AffineThickening.Lifts
variable {U V : Y.Opens} {a b : Γ(Y, U)} {r s : Γ(Z, ⊤)}
namespace GlobalTheory.AffineThickening.Lifts
theorem _root_.solution (a : Γ(Y, U)) (hb : Lifts i U b 0) : Lifts i U (a * b) 0 := by
  unfold Lifts at *
  rw [map_mul, hb, map_zero, MulZeroClass.mul_zero]
end GlobalTheory.AffineThickening.Lifts
