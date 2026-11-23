-- Prove2me | solution 1 for GlobalTheory.natCard_quotient_range_mulVecLin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:24.405839+00:00
-- url     : https://prove2.me/submissions/e45d373e-0e76-41da-8363-b56a9b3db9e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {b d : Matrix n n ℤ}
namespace GlobalTheory
theorem _root_.solution (hd : d.det ≠ 0) :
    Nat.card ((n → ℤ) ⧸ LinearMap.range d.mulVecLin) = d.det.natAbs := by
  have hinj : Function.Injective d.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
    exact fun v hv => eq_zero_of_mulVec_eq_zero hd hv
  rw [← Submodule.natAbs_det_equiv _ (LinearEquiv.ofInjective _ hinj), ← LinearMap.det_toLin']
  rfl
end GlobalTheory
