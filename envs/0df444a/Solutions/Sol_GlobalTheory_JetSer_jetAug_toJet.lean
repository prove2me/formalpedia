-- Prove2me | solution 1 for GlobalTheory.JetSer.jetAug_toJet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:31.574177+00:00
-- url     : https://prove2.me/submissions/53ff6576-ea63-4122-b597-0f0bfd00958d

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
variable [Finite κ]
namespace GlobalTheory.JetSer
theorem _root_.solution (m : ℕ) (g : MvPowerSeries κ R) :
    jetAug R κ m (toJet m g) = constantCoeff g := by
  show MvPolynomial.aeval (fun _ : κ => (0 : R)) (truncTotal (m + 1) g) = _
  rw [MvPolynomial.aeval_zero', MvPolynomial.constantCoeff_eq, coeff_truncTotal_eq_ite, if_pos (by simp)]
  rfl
end GlobalTheory.JetSer
