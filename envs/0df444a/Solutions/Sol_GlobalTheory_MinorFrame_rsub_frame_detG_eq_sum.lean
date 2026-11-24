-- Prove2me | solution 1 for GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:51:25.516217+00:00
-- url     : https://prove2.me/submissions/0e7f1162-2fa9-4182-ad93-6359ee5cce72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumNormRowSubProdMinors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CauchyBinetColumnFrameProdDetPowEqSum
import Theorems.Thm_GlobalTheory_MinorFrame_rsub_frame_detG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
namespace GlobalTheory.MinorFrame
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (x₀ : Var ι d a → ℂ),
    rsub (frameMat x₀).conjTranspose (detG a n) =
      ∑ T : Tup ι a d n, star (MvPolynomial.eval x₀ (prodMinors T)) • prodMinors T :=
  fun _ _ n x₀ => rsub_frame_detG n x₀
end GlobalTheory.MinorFrame
