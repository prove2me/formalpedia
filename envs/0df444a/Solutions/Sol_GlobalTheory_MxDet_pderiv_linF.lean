-- Prove2me | solution 1 for GlobalTheory.MxDet.pderiv_linF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:02:37.725903+00:00
-- url     : https://prove2.me/submissions/a6d4970d-b845-43b1-96fb-d3f49b88a664

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReDetRelation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.MxDet
namespace GlobalTheory.MxDet
theorem _root_.solution {ι : Type} [Fintype ι] (x : ι → ℝ) (j : ι) :
    MvPolynomial.pderiv j (linF x) = MvPolynomial.C (x j) := by
  rw [linF, map_sum, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [MvPolynomial.pderiv_X, Pi.single_apply, hb, hb.symm]
  · simp
end GlobalTheory.MxDet
