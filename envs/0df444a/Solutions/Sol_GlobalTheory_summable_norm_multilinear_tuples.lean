-- Prove2me | solution 1 for GlobalTheory.summable_norm_multilinear_tuples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:55.87087+00:00
-- url     : https://prove2.me/submissions/a7921a32-d565-465d-bfbe-af31f6958f7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummablePiProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Theorems.Thm_GlobalTheory_summable_prod_tuples

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
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, NormedSpace 𝕜 (V i)] {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
namespace GlobalTheory
theorem _root_.solution (M : ContinuousMultilinearMap 𝕜 V W)
    {x : ∀ i, J i → V i} (hx : ∀ i, Summable fun j => ‖x i j‖) :
    Summable fun t : ∀ i, J i => ‖M fun i => x i (t i)‖ :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => M.le_opNorm _)
    ((summable_prod_tuples (fun i j => norm_nonneg (x i j)) hx).mul_left ‖M‖)
end GlobalTheory
