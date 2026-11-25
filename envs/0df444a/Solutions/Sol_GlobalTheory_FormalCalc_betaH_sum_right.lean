-- Prove2me | solution 1 for GlobalTheory.FormalCalc.betaH_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:54.932791+00:00
-- url     : https://prove2.me/submissions/0c7cb83f-e76b-4291-bb0f-de13ce975fe6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_BetaHSumSmulRight
import Theorems.Thm_GlobalTheory_FormalCalc_betaH_sum_smul_right

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
theorem _root_.solution {ι : Type} (s : Finset ι)
    (ξ : (Fin d → k) × (Fin d → k)) (v : ι → (Fin d → k) × (Fin d → k)) :
    betaH k ξ (∑ i ∈ s, v i) = ∑ i ∈ s, betaH k ξ (v i) := by
  simpa using betaH_sum_smul_right k s (fun _ => 1) ξ v
end GlobalTheory.FormalCalc
