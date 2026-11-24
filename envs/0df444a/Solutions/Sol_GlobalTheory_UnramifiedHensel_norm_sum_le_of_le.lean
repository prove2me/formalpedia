-- Prove2me | solution 1 for GlobalTheory.UnramifiedHensel.norm_sum_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:31.50014+00:00
-- url     : https://prove2.me/submissions/de262677-867f-44a5-891b-d9b44c360288

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRelationGradient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.UnramifiedHensel
variable {K : Type} [NormedField K] [IsUltrametricDist K] {R ι : Type} [CommRing R]
namespace GlobalTheory.UnramifiedHensel
theorem _root_.solution [Fintype ι] (a : ι → K) {r : ℝ} (hr : 0 ≤ r) (ha : ∀ i, ‖a i‖ ≤ r) :
    ‖∑ i, a i‖ ≤ r :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr (fun i _ => ha i)
end GlobalTheory.UnramifiedHensel
