-- Prove2me | solution 1 for GlobalTheory.JetSer.toJet_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:52.574802+00:00
-- url     : https://prove2.me/submissions/9899c224-d6be-4234-8438-8478edf5413b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Theorems.Thm_GlobalTheory_JetSer_toJet_eq_mk_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart
open GlobalTheory GlobalTheory.JetSer
variable {R : Type} [CommRing R] {κ : Type}
variable [Finite κ]
namespace GlobalTheory.JetSer
theorem _root_.solution (m : ℕ) (g g' : MvPowerSeries κ R) :
    toJet m g = toJet m g' ↔ ∀ e : κ →₀ ℕ, Finsupp.degree e < m + 1 → coeff e g = coeff e g' := by
  refine (toJet_eq_mk_iff m g _).trans (forall₂_congr fun e he => ?_)
  rw [coeff_truncTotal_eq_ite, if_pos he]
end GlobalTheory.JetSer
