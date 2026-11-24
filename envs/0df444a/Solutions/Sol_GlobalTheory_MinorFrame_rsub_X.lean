-- Prove2me | solution 1 for GlobalTheory.MinorFrame.rsub_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:58:06.311776+00:00
-- url     : https://prove2.me/submissions/8e2d49ef-a829-4b36-8cd4-f76fb511c597

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.MinorFrame
namespace GlobalTheory.MinorFrame
theorem _root_.solution {σ σ' : Type} [Fintype σ'] (M : Matrix σ' σ ℂ) (v : σ) :
    rsub M (X v) = ∑ w, C (M w v) * X w := aeval_X _ _
end GlobalTheory.MinorFrame
