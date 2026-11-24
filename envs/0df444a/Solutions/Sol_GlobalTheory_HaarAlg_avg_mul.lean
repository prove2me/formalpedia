-- Prove2me | solution 1 for GlobalTheory.HaarAlg.avg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:13:38.895407+00:00
-- url     : https://prove2.me/submissions/566a41c6-5e5a-4f5a-97d9-3cf56df3cbf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsAlgebraicIntegral
import Theorems.Thm_GlobalTheory_HaarAlg_integrable_of_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.HaarAlg
variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (κ : Measure K) [IsProbabilityMeasure κ] {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Group K] [IsTopologicalGroup K] [DecidableEq ι]
namespace GlobalTheory.HaarAlg
theorem _root_.solution {F : K → Matrix ι ι ℂ} (hF : Continuous F) (M : Matrix ι ι ℂ) :
    avg κ F * M = avg κ fun g => F g * M := by
  ext a b
  simp only [avg, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl fun c _ => (integral_mul_const _ _).symm
  · exact fun c _ => integrable_of_continuous κ (by fun_prop)
end GlobalTheory.HaarAlg
