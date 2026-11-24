-- Prove2me | solution 1 for GlobalTheory.UnramifiedHensel.norm_eval_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:10:29.103024+00:00
-- url     : https://prove2.me/submissions/a27e25e4-77c3-4608-8905-70c03f31dd76

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
theorem _root_.solution (c : R →+* K) (hc : ∀ w, ‖c w‖ ≤ 1) (x : ι → K) (hx : ∀ i, ‖x i‖ ≤ 1)
    (G : MvPolynomial ι R) : ‖eval₂ c x G‖ ≤ 1 := by
  induction G using MvPolynomial.induction_on with
  | C a => simpa using hc a
  | add p q hp hq =>
    rw [eval₂_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hp hq)
  | mul_X p n hp =>
    rw [eval₂_mul, eval₂_X, norm_mul]
    exact mul_le_one₀ hp (norm_nonneg _) (hx n)
end GlobalTheory.UnramifiedHensel
