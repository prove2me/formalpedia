-- Prove2me | solution 1 for GlobalTheory.GaugeBaseChange.map_dpolyOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:27:00.41085+00:00
-- url     : https://prove2.me/submissions/eae5813c-94e0-4630-913f-9ef831be9ea8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeNabValBaseChange
import Theorems.Thm_GlobalTheory_map_dmonOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_eq_sum_of_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.GaugeBaseChange
open GlobalTheory.QuadDeriv
variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {d : ℕ}
namespace GlobalTheory.GaugeBaseChange
theorem _root_.solution (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (f : PS k 1 d) :
    MvPowerSeries.map φ (DpolyOf F u P f) =
      DpolyOf (mapP φ F) (fun l i => φ (u l i)) (MvPolynomial.map φ P) (MvPowerSeries.map φ f) := by
  rw [GE.dpolyOf_eq_sum_of_subset _ _ (MvPolynomial.map φ P) P.support
    (MvPolynomial.support_map_subset _ _), DpolyOf, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_C, GlobalTheory.map_dmonOf, MvPolynomial.coeff_map]
  rfl
end GlobalTheory.GaugeBaseChange
