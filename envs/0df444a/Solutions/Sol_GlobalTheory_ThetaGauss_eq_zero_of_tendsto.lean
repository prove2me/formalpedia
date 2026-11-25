-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.eq_zero_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:02:47.495387+00:00
-- url     : https://prove2.me/submissions/f0702116-4002-41be-b14d-88c1d8e28178

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.ThetaGauss.transl_apply

set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}
namespace GlobalTheory.ThetaGauss
theorem _root_.solution (L : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L]
    {u : (Fin g → ℂ) → ℝ} (hu : Continuous u) (hp : ∀ a ∈ L, ∀ z, u (z + a) = u z)
    (z w : Fin g → ℂ) (ht : Tendsto (fun n : ℕ => u (z + n • w)) atTop (𝓝 0)) : u z = 0 := by
  let Q := (Fin g → ℂ) ⧸ L.toAddSubgroup
  haveI : CompactSpace Q := by
    have := IsZLattice.isCompact_range_of_periodic L (QuotientAddGroup.mk : _ → Q)
      QuotientAddGroup.continuous_mk fun z w hw => by
        rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).2 hw, add_zero]
    rw [QuotientAddGroup.mk_surjective.range_eq] at this
    exact ⟨this⟩
  let U : Q → ℝ := Quotient.lift (fun x => u (z + x)) fun a b hab => by
    have hab' : -a + b ∈ L := QuotientAddGroup.leftRel_apply.1 hab
    have := hp _ hab' (z + a)
    rw [← this]; congr 1; abel
  have hU : Continuous U := Continuous.quotient_lift (by fun_prop) _
  have h1 := (mapClusterPt_zero_atTop_nsmul (QuotientAddGroup.mk w : Q)).continuousAt_comp
    hU.continuousAt
  have h2 : U 0 = u z := by
    change u (z + 0) = u z
    rw [add_zero]
  rw [h2] at h1
  exact eq_of_nhds_neBot (ClusterPt.mono h1 ht)
end GlobalTheory.ThetaGauss
