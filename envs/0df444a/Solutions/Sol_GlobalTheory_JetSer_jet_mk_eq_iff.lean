-- Prove2me | solution 1 for GlobalTheory.JetSer.jet_mk_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:14.654856+00:00
-- url     : https://prove2.me/submissions/7a5ac9e8-09a9-40b1-bdee-94462e313c8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq

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
namespace GlobalTheory.JetSer
theorem _root_.solution (m : ℕ) (P Q : MvPolynomial κ R) :
    (Ideal.Quotient.mk _ P : JetR R κ m) = Ideal.Quotient.mk _ Q ↔
      ∀ e : κ →₀ ℕ, Finsupp.degree e < m + 1 → P.coeff e = Q.coeff e := by
  rw [Ideal.Quotient.eq]
  refine (MvPolynomial.mem_pow_idealOfVars_iff' (m + 1) (P - Q)).trans ?_
  simp only [MvPolynomial.coeff_sub, sub_eq_zero]
end GlobalTheory.JetSer
