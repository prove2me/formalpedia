-- Prove2me | solution 1 for GlobalTheory.AffineThickening.Lifts.one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:04:52.972714+00:00
-- url     : https://prove2.me/submissions/ea8194b3-6128-4e39-ab94-1fd72d0d8274

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
theorem _root_.solution : Lifts i U 1 1 := by
  unfold Lifts
  rw [map_one, map_one]
end GlobalTheory.AffineThickening.Lifts
