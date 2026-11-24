-- Prove2me | solution 1 for GlobalTheory.AffineThickening.Lifts.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:03:20.340359+00:00
-- url     : https://prove2.me/submissions/46b19af5-ebbf-4951-9143-3d8e431ebafa

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
theorem _root_.solution (ha : Lifts i U a r) (n : ℕ) : Lifts i U (a ^ n) (r ^ n) := by
  unfold Lifts at *
  rw [map_pow, map_pow, ha]
end GlobalTheory.AffineThickening.Lifts
