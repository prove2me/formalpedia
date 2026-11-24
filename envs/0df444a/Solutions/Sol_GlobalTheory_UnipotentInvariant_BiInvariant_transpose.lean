-- Prove2me | solution 1 for GlobalTheory.UnipotentInvariant.BiInvariant.transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:49:48.001036+00:00
-- url     : https://prove2.me/submissions/64affcb5-e988-416d-a731-ddd2dc1acca5

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
namespace BiInvariant
theorem _root_.solution {f : Matrix (Fin p) (Fin p) K → K} (h : BiInvariant f) :
    BiInvariant fun M => f Mᵀ :=
  ⟨h.2, fun a b hab t M => by simpa using h.1 a b hab t M⟩
end BiInvariant
end GlobalTheory.UnipotentInvariant
