-- Prove2me | solution 1 for GlobalTheory.FormalCalc.betaH_eq_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:26:31.67775+00:00
-- url     : https://prove2.me/submissions/039f3644-8222-4e0d-ac25-f5b85e5d1620

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_BetaHSumSmulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalCalc
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  (k : Type) [CommRing k] [Algebra R k]
namespace GlobalTheory.FormalCalc
theorem _root_.solution (ξ η : (Fin d → k) × (Fin d → k)) :
    betaH k ξ η = η.2 ⬝ᵥ ξ.1 - ξ.2 ⬝ᵥ η.1 := by
  simp [betaH, dotProduct, Finset.sum_sub_distrib]
end GlobalTheory.FormalCalc
