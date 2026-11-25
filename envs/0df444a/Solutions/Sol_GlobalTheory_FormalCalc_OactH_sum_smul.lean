-- Prove2me | solution 1 for GlobalTheory.FormalCalc.OactH_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:28.442387+00:00
-- url     : https://prove2.me/submissions/4f20bf0b-5148-434f-b8b8-b65bf52a0daa

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
theorem _root_.solution (B : FB R d O) (a : O) {ι : Type} (s : Finset ι) (c : ι → k)
    (v : ι → (Fin d → k) × (Fin d → k)) :
    OactH k B a (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • OactH k B a (v i) := by
  refine Prod.ext ?_ ?_ <;>
  simp only [OactH, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
    Matrix.mulVec_sum, Matrix.mulVec_smul]
end GlobalTheory.FormalCalc
