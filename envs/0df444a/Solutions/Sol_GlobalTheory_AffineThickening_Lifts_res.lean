-- Prove2me | solution 1 for GlobalTheory.AffineThickening.Lifts.res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:24:31.925901+00:00
-- url     : https://prove2.me/submissions/1b7bfb10-73e7-420a-9b47-987641bcf7e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Theorems.Thm_GlobalTheory_AffineThickening_rs_rs
import Theorems.Thm_GlobalTheory_AffineThickening_app_rs

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
theorem _root_.solution (ha : Lifts i U a r) (h : V ≤ U) : Lifts i V (rs h a) r := by
  unfold Lifts at *
  rw [app_rs, ha, rs_rs]
end GlobalTheory.AffineThickening.Lifts
