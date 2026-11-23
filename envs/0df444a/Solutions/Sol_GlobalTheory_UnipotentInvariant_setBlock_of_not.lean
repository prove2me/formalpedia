-- Prove2me | solution 1 for GlobalTheory.UnipotentInvariant.setBlock_of_not
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:35.655449+00:00
-- url     : https://prove2.me/submissions/12dbb805-766c-4e90-a3fb-9cdd3df40895

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
theorem _root_.solution {z : Fin p × Fin p → σ} (x : σ → K)
    (M : Matrix (Fin p) (Fin p) K) {s : σ} (hs : ¬ ∃ w, z w = s) : setBlock z x M s = x s :=
  Function.extend_apply' _ _ _ hs
end GlobalTheory.UnipotentInvariant
