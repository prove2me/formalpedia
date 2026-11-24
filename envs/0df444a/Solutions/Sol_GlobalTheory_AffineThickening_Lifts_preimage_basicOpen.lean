-- Prove2me | solution 1 for GlobalTheory.AffineThickening.Lifts.preimage_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:20:39.12822+00:00
-- url     : https://prove2.me/submissions/e015b197-dd30-430c-9808-e9911307e6ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Theorems.Thm_GlobalTheory_AffineThickening_basicOpen_rs

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
theorem _root_.solution (ha : Lifts i U a r) :
    i ⁻¹ᵁ Y.basicOpen a = i ⁻¹ᵁ U ⊓ Z.basicOpen r := by
  rw [Scheme.preimage_basicOpen, ← basicOpen_rs le_top, ← ha]
end GlobalTheory.AffineThickening.Lifts
