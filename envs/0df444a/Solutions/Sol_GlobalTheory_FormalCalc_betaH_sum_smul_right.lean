-- Prove2me | solution 1 for GlobalTheory.FormalCalc.betaH_sum_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:34:20.329723+00:00
-- url     : https://prove2.me/submissions/a7faf3ff-14b0-4559-98d5-0b501a83d52e

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
theorem _root_.solution {ι : Type} (s : Finset ι) (c : ι → k)
    (ξ : (Fin d → k) × (Fin d → k)) (v : ι → (Fin d → k) × (Fin d → k)) :
    betaH k ξ (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i * betaH k ξ (v i) := by
  simp only [betaH_eq_dotProduct, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
    dotProduct_sum, sum_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib]
end GlobalTheory.FormalCalc
