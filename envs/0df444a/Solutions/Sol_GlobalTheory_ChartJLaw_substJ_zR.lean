-- Prove2me | solution 1 for GlobalTheory.ChartJLaw.substJ_zR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:10:41.668012+00:00
-- url     : https://prove2.me/submissions/594a6ebc-775a-4a12-a672-9f79daffb92b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsFormalGroupLawOfChartOfJetChart
import Theorems.Thm_GlobalTheory_ChartJLaw_psJet_eq_toJet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ChartJLaw
variable {T : Type} [CommRing T] {d : ℕ}
namespace GlobalTheory.ChartJLaw
theorem _root_.solution {n : ℕ} (m : ℕ) (φ : Fin d → PS T n d) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (q : Fin 1 × Fin d) : substJ m φ hφ (zR m q) = JetSer.toJet m (φ q.2) := by
  rw [← psJet_eq_toJet m _ (hφ q.2)]
  show MvPolynomial.aeval (fun q : Fin 1 × Fin d => psJet m (φ q.2)) (MvPolynomial.X q) = _
  rw [MvPolynomial.aeval_X]
end GlobalTheory.ChartJLaw
