-- Prove2me | solution 1 for GlobalTheory.TwistCheck.cc_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:12.263269+00:00
-- url     : https://prove2.me/submissions/825d1d9b-3f21-4e6d-90db-459f96d3a80e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_BilLActRight

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
open GlobalTheory GlobalTheory.TwistCheck
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
namespace GlobalTheory.TwistCheck
theorem _root_.solution (f : PS S 1 d) (j : Fin d) :
    constantCoeff (pderiv S ((0 : Fin 1), j) f) = coeff (Finsupp.single ((0 : Fin 1), j) 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]; simp
end GlobalTheory.TwistCheck
