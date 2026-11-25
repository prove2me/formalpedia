-- Prove2me | solution 1 for GlobalTheory.GaugeInt.lin_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:35.715013+00:00
-- url     : https://prove2.me/submissions/c6495172-e66b-4244-b128-f8274afba65f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Theorems.Thm_GlobalTheory_GaugeInt_int_const
import Theorems.Thm_GlobalTheory_GaugeInt_int_pderiv

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
theorem _root_.solution {v : Fin d → k} (hv : ∀ i, v i ∈ φ.range) {f : PS k 1 d} (hf : f ∈ IntS φ 1 d) :
    lin v f ∈ φ.range :=
  sum_mem fun i _ => mul_mem (hv i) (int_const (int_pderiv hf _))
end GlobalTheory.GaugeInt
