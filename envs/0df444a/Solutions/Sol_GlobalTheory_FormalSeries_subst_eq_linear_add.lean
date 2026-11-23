-- Prove2me | solution 1 for GlobalTheory.FormalSeries.subst_eq_linear_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:17.099972+00:00
-- url     : https://prove2.me/submissions/ae080b49-66ec-4026-841e-0c96bcd2c5ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_apply
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_X
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
theorem _root_.solution [Fintype σ] {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (f : MvPowerSeries σ R) :
    f.subst a = ∑ j, coeff (Finsupp.single j 1) f • a j +
      (f - ∑ j, coeff (Finsupp.single j 1) f • X j).subst a := by
  rw [← substAlgHom_apply ha, ← substAlgHom_apply ha, map_sub, map_sum]
  simp only [map_smul, substAlgHom_X]
  abel
end GlobalTheory.FormalSeries
