-- Prove2me | solution 1 for GlobalTheory.UnitPartition.contDiffAt_normAtPlace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:15.002174+00:00
-- url     : https://prove2.me/submissions/b89a66be-d0ca-4d29-8160-f03ee11e5b00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothCompactSupportHasSumLatticeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul

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
theorem _root_.solution (w : InfinitePlace K) (x : mixedSpace K)
    (hx : normAtPlace w x ≠ 0) : ContDiffAt ℝ ∞ (fun y : mixedSpace K => normAtPlace w y) x := by
  rcases w.isReal_or_isComplex with hw | hw
  · have e : (fun y : mixedSpace K => normAtPlace w y) = fun y => ‖y.1 ⟨w, hw⟩‖ :=
      funext fun y => normAtPlace_apply_of_isReal hw y
    rw [normAtPlace_apply_of_isReal hw] at hx
    rw [e]
    exact ContDiffAt.norm ℝ (by fun_prop) (norm_ne_zero_iff.1 hx)
  · have e : (fun y : mixedSpace K => normAtPlace w y) = fun y => ‖y.2 ⟨w, hw⟩‖ :=
      funext fun y => normAtPlace_apply_of_isComplex hw y
    rw [normAtPlace_apply_of_isComplex hw] at hx
    rw [e]
    exact ContDiffAt.norm ℝ (by fun_prop) (norm_ne_zero_iff.1 hx)
end GlobalTheory.UnitPartition
