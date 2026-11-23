-- Prove2me | solution 1 for GlobalTheory.JetSer.toJet_eq_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:01.485077+00:00
-- url     : https://prove2.me/submissions/cad3c9a0-3127-430f-900d-e41655685ff2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Theorems.Thm_GlobalTheory_JetSer_jet_mk_eq_iff

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
theorem _root_.solution (m : ℕ) (g : MvPowerSeries κ R) (Q : MvPolynomial κ R) :
    toJet m g = Ideal.Quotient.mk _ Q ↔
      ∀ e : κ →₀ ℕ, Finsupp.degree e < m + 1 → coeff e g = Q.coeff e := by
  unfold toJet
  rw [jet_mk_eq_iff]
  refine forall₂_congr fun e he => ?_
  rw [coeff_truncTotal_eq_ite, if_pos he]
end GlobalTheory.JetSer
