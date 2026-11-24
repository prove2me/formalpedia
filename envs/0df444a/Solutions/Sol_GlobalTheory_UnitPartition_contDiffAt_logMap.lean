-- Prove2me | solution 1 for GlobalTheory.UnitPartition.contDiffAt_logMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:15:45.352867+00:00
-- url     : https://prove2.me/submissions/ffec759d-b889-4fd9-91a9-62a21e37a27d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothCompactSupportHasSumLatticeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul
import Theorems.Thm_GlobalTheory_UnitPartition_contDiffAt_normAtPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open GlobalTheory.UnitPartition
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.UnitPartition
theorem _root_.solution (x : mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) :
    ContDiffAt ℝ ∞ (logMap (K := K)) x := by
  have hN : ∀ w, normAtPlace w x ≠ 0 := mixedEmbedding.norm_ne_zero_iff.1 hx
  have hnorm : ContDiffAt ℝ ∞ (fun y : mixedSpace K => mixedEmbedding.norm y) x := by
    have e : (fun y : mixedSpace K => mixedEmbedding.norm y) =
        fun y => ∏ w, normAtPlace w y ^ mult w := funext fun y => mixedEmbedding.norm_apply y
    rw [e]
    exact contDiffAt_prod fun w _ => (contDiffAt_normAtPlace w x (hN w)).pow _
  refine contDiffAt_pi.2 fun w => ?_
  simp only [logMap_apply]
  exact contDiffAt_const.mul (((contDiffAt_normAtPlace w.1 x (hN w.1)).log (hN w.1)).sub
    ((hnorm.log hx).mul contDiffAt_const))
end GlobalTheory.UnitPartition
