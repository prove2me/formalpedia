-- Prove2me | solution 1 for GlobalTheory.card_quotient_range_mulVecLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:25:56.028119+00:00
-- url     : https://prove2.me/submissions/873ccfa9-2d15-45c4-846e-e4234ee79c37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsRepresentativesModSimilitudeTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (hA : A.det ≠ 0) :
    Nat.card ((ι → ℤ) ⧸ LinearMap.range (Matrix.toLin' A)) = A.det.natAbs := by
  have hinj : Function.Injective (Matrix.toLin' A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hA (by simpa using hv)
  rw [← Submodule.natAbs_det_equiv _ (LinearEquiv.ofInjective _ hinj)]
  congr 1
  rw [← LinearMap.det_toLin' A]
  congr 1
end GlobalTheory
