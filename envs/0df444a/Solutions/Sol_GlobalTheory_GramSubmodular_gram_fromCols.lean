-- Prove2me | solution 1 for GlobalTheory.GramSubmodular.gram_fromCols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:47:37.674798+00:00
-- url     : https://prove2.me/submissions/d988aec7-2bf8-4452-9648-d5556a317615

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetFromColsEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open GlobalTheory.GramSubmodular
variable {m α β γ : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
namespace GlobalTheory.GramSubmodular
theorem _root_.solution (U : Matrix m α ℂ) (V : Matrix m β ℂ) :
    (fromCols U V)ᴴ * fromCols U V = fromBlocks (Uᴴ * U) (Uᴴ * V) (Vᴴ * U) (Vᴴ * V) := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols]
end GlobalTheory.GramSubmodular
