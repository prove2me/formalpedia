-- Prove2me | solution 1 for GlobalTheory.FormalSeries.jacobian_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:46:59.171903+00:00
-- url     : https://prove2.me/submissions/178c48fb-3163-4744-9a47-67c6464c1cf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_apply
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_X
import Theorems.Thm_GlobalTheory_FormalSeries_coeff_single_subst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalSeries.jacobian_apply
attribute [local simp] GlobalTheory.FormalSeries.jacobian_X

set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FormalSeries
open MvPowerSeries
variable {σ τ υ R S : Type*} [CommRing R] [CommRing S]
variable [Algebra R S]
namespace GlobalTheory.FormalSeries
theorem _root_.solution [Fintype τ] {f : τ → MvPowerSeries σ R}
    (hf : ∀ s, constantCoeff (f s) = 0) (g : υ → MvPowerSeries τ R) :
    jacobian (fun i => (g i).subst f) = jacobian g * jacobian f := by
  ext i k
  simp only [Matrix.mul_apply, jacobian_apply, coeff_single_subst hf, smul_eq_mul]
end GlobalTheory.FormalSeries
