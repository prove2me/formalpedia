-- Prove2me | solution 1 for GlobalTheory.AffineThickening.Lifts.zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:04:53.842189+00:00
-- url     : https://prove2.me/submissions/5514386d-1d8d-4148-a15b-c8eade3f95cf

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
theorem _root_.solution : Lifts i U 0 0 := by
  unfold Lifts
  rw [map_zero, map_zero]
end GlobalTheory.AffineThickening.Lifts
