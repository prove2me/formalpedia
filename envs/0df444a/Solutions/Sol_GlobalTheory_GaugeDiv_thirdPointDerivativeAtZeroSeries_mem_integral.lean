-- Prove2me | solution 1 for GlobalTheory.GaugeDiv.thirdPointDerivativeAtZeroSeries_mem_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:46:25.231183+00:00
-- url     : https://prove2.me/submissions/3bc91728-1d32-4a53-9cd1-a7a809428ff2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
import Theorems.Thm_GlobalTheory_GaugeInt_int_C
import Theorems.Thm_GlobalTheory_GaugeInt_int_ev
import Theorems.Thm_GlobalTheory_GaugeInt_ip3
import Theorems.Thm_GlobalTheory_GaugeInt_ip_pt
import Theorems.Thm_GlobalTheory_GaugeInt_ip_zero


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
theorem _root_.solution {v : Fin d → k} (hv : ∀ i, v i ∈ φ.range) {f : PS k 3 d} (hf : DI φ f) :
    dz3 v f ∈ IntS φ 2 d :=
  sum_mem fun i _ => mul_mem (int_C (hv i)) (int_ev (ip3 (ip_pt 0) (ip_pt 1) ip_zero) (hf _))
end GlobalTheory.GaugeDiv
