-- Prove2me | solution 1 for GlobalTheory.FormalSeries.eq_of_forall_le_order_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:20.285054+00:00
-- url     : https://prove2.me/submissions/f5ea074d-5d76-4948-994e-7f208c53d2af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_apply
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_X
import Theorems.Thm_GlobalTheory_FormalSeries_coeff_eq_of_le_order_sub
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
namespace GlobalTheory.FormalSeries
theorem _root_.solution {f g : MvPowerSeries σ R}
    (h : ∀ k : ℕ, (k : ℕ∞) ≤ (f - g).order) : f = g := by
  ext d
  exact coeff_eq_of_le_order_sub (h (d.degree + 1)) (Nat.lt_succ_self _)
end GlobalTheory.FormalSeries
