-- Prove2me | solution 1 for GlobalTheory.LimitSeriesPowSmul.mem_pow_smul_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:42:39.880694+00:00
-- url     : https://prove2.me/submissions/11f5c5ff-944e-48b7-b404-730607075d1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLimitSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LimitSeriesPowSmul
namespace GlobalTheory.LimitSeriesPowSmul
theorem _root_.solution {R : Type} [CommRing R] (p : R) (n : ℕ) (x : R) :
    x ∈ ((Ideal.span {p}) ^ n • (⊤ : Submodule R R)) ↔ p ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
end GlobalTheory.LimitSeriesPowSmul
