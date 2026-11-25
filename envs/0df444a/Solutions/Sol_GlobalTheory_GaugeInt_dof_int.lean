-- Prove2me | solution 1 for GlobalTheory.GaugeInt.dof_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:14:21.532804+00:00
-- url     : https://prove2.me/submissions/f9ad5dc8-95bb-4340-8b77-011491dd8cec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Theorems.Thm_GlobalTheory_GaugeInt_IP_int
import Theorems.Thm_GlobalTheory_GaugeInt_int_pderiv
import Theorems.Thm_GlobalTheory_GaugeInt_dy_int

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
open GlobalTheory.QuadDeriv
open GlobalTheory GlobalTheory.GaugeInt
variable {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ}
variable {φ}
namespace GlobalTheory.GaugeInt
theorem _root_.solution {F : Pt k 2 d} (hF : IP φ F) {v : Fin d → k} (hv : ∀ i, v i ∈ φ.range)
    {f : PS k 1 d} (hf : f ∈ IntS φ 1 d) : Dof F v f ∈ IntS φ 1 d :=
  sum_mem fun j _ => mul_mem (dy_int hv (int_pderiv (hF.int j))) (int_pderiv hf _)
end GlobalTheory.GaugeInt
