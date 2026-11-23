-- Prove2me | solution 1 for GlobalTheory.FormalSeries.jacobian_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:10.31378+00:00
-- url     : https://prove2.me/submissions/20efb47f-c6cc-4933-9321-e52360dd889f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalSeries.jacobian_apply

set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FormalSeries
open MvPowerSeries
variable {σ τ υ R S : Type*} [CommRing R] [CommRing S]
namespace GlobalTheory.FormalSeries
theorem _root_.solution [DecidableEq σ] :
    jacobian (X : σ → MvPowerSeries σ R) = 1 := by
  ext i j
  rw [jacobian_apply, coeff_index_single_X, Matrix.one_apply]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h, Ne.symm h]
end GlobalTheory.FormalSeries
