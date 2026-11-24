-- Prove2me | solution 1 for GlobalTheory.summable_prod_tuples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:12:35.045214+00:00
-- url     : https://prove2.me/submissions/c319b4e7-239a-4629-b195-b8e59cb9813d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummablePiProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Theorems.Thm_GlobalTheory_SummablePiProd_summable_pi_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped Real FourierTransform Pointwise
open GlobalTheory
variable {ι : Type*} [Fintype ι] {J : ι → Type*}
namespace GlobalTheory
theorem _root_.solution {u : ∀ i, J i → ℝ} (h0 : ∀ i j, 0 ≤ u i j) (hu : ∀ i, Summable (u i)) :
    Summable fun t : ∀ i, J i => ∏ i, u i (t i) := by
  first
  | exact @_root_.GlobalTheory.SummablePiProd.summable_pi_prod
  | exact _root_.GlobalTheory.SummablePiProd.summable_pi_prod
  | (apply _root_.GlobalTheory.SummablePiProd.summable_pi_prod <;> assumption)
  | (intros; apply _root_.GlobalTheory.SummablePiProd.summable_pi_prod <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SummablePiProd.summable_pi_prod <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SummablePiProd.summable_pi_prod ..)
end GlobalTheory
