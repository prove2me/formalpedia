-- Prove2me | solution 1 for GlobalTheory.UnipotentInvariant.setBlock_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:35.534632+00:00
-- url     : https://prove2.me/submissions/80a87af5-931f-4d0c-abab-37cd7b0a3c9b

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
variable {σ : Type*} [DecidableEq σ]
omit [Field K] [DecidableEq σ]
namespace GlobalTheory.UnipotentInvariant
theorem _root_.solution {z : Fin p × Fin p → σ} (hz : Function.Injective z) (x : σ → K)
    (M : Matrix (Fin p) (Fin p) K) (w : Fin p × Fin p) : setBlock z x M (z w) = M w.1 w.2 :=
  hz.extend_apply _ _ _
end GlobalTheory.UnipotentInvariant
