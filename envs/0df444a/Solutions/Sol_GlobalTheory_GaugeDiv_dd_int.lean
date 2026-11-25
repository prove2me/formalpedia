-- Prove2me | solution 1 for GlobalTheory.GaugeDiv.dd_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:50:11.186665+00:00
-- url     : https://prove2.me/submissions/9508bee5-fed7-4eff-bb84-ac444c1f3cca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
import Theorems.Thm_GlobalTheory_GaugeInt_IP_int
import Theorems.Thm_GlobalTheory_GaugeInt_dy_int
import Theorems.Thm_GlobalTheory_GaugeInt_int_ev
import Theorems.Thm_GlobalTheory_GaugeInt_int_pderiv
import Theorems.Thm_GlobalTheory_GaugeInt_ip1
import Theorems.Thm_GlobalTheory_GaugeInt_ip_pt


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
open GlobalTheory.QuadDeriv GlobalTheory.GaugeInt
open GlobalTheory GlobalTheory.GaugeDiv
variable {R k : Type} [CommRing R] [CommRing k] {φ : R →+* k} {d : ℕ}
namespace GlobalTheory.GaugeDiv
theorem _root_.solution {F : Pt k 2 d} (hF : IP φ F) (a : Fin 2) {v : Fin d → k} (hv : ∀ i, v i ∈ φ.range)
    {G : PS k 2 d} (hG : G ∈ IntS φ 2 d) : DD F a v G ∈ IntS φ 2 d :=
  sum_mem fun j _ => mul_mem (int_ev (ip1 (ip_pt a)) (dy_int hv (int_pderiv (hF.int j))))
    (int_pderiv hG _)
end GlobalTheory.GaugeDiv
