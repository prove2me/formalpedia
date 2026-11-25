-- Prove2me | solution 1 for GlobalTheory.FormalCalc.betaH_OactH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:08.398314+00:00
-- url     : https://prove2.me/submissions/ae31beea-27e6-4656-96ec-5d9520855f3b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_BetaHSumSmulRight
import Theorems.Thm_GlobalTheory_FormalCalc_betaH_eq_dotProduct

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
theorem _root_.solution (B : FB R d O) (a : O) (ξ η : (Fin d → k) × (Fin d → k)) :
    betaH k (OactH k B a ξ) η = betaH k ξ (OactH k B (star a) η) := by
  simp only [betaH_eq_dotProduct, OactH, star_star, Matrix.mulVec_transpose,
    Matrix.dotProduct_mulVec]
end GlobalTheory.FormalCalc
