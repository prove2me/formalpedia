-- Prove2me | solution 1 for GlobalTheory.UnipotentInvariant.leadMinor_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:49:51.656856+00:00
-- url     : https://prove2.me/submissions/2d4c8c27-0f13-4b46-9414-94450a858e72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}
namespace GlobalTheory.UnipotentInvariant
theorem _root_.solution (i : Fin p) (M : Matrix (Fin p) (Fin p) K) :
    leadMinor i Mᵀ = leadMinor i M := by
  unfold leadMinor
  rw [← det_transpose]
  rfl
end GlobalTheory.UnipotentInvariant
