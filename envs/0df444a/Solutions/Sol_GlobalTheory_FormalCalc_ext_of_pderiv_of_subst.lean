-- Prove2me | solution 1 for GlobalTheory.FormalCalc.ext_of_pderiv_of_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:43:36.862026+00:00
-- url     : https://prove2.me/submissions/50fe832b-e946-4cb3-b406-84ec16fde951

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Theorems.Thm_GlobalTheory_FormalCalc_coeff_subst_kill
import Theorems.Thm_GlobalTheory_FormalCalc_ext_of_pderiv_of_coeff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Sum
variable {σ τ ι κ μ A : Type*} [CommRing A]
namespace GlobalTheory.FormalCalc
theorem _root_.solution [IsAddTorsionFree A] (e : ι → κ) {b : κ → MvPowerSeries κ A}
    (hb0 : ∀ i, b (e i) = 0) (hb1 : ∀ k, k ∉ Set.range e → b k = X k)
    {f g : MvPowerSeries κ A} (hD : ∀ i, pderiv A (e i) f = pderiv A (e i) g)
    (h0 : subst b f = subst b g) : f = g := by
  refine ext_of_pderiv_of_coeff e hD fun α hα => ?_
  have := congrArg (coeff α) h0
  rwa [coeff_subst_kill e hb0 hb1, coeff_subst_kill e hb0 hb1, if_pos hα, if_pos hα] at this
end GlobalTheory.FormalCalc
