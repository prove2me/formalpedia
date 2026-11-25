-- Prove2me | solution 1 for GlobalTheory.AevalTotalDegreeBound.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:25:09.241967+00:00
-- url     : https://prove2.me/submissions/a7b137ad-3156-4a4c-9935-cdbdbf91285f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AevalTotalDegreeLe
import Theorems.Thm_GlobalTheory_AevalTotalDegreeBound_aeval_totalDegree_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.AevalTotalDegreeBound
open MvPolynomial
namespace GlobalTheory.AevalTotalDegreeBound
theorem _root_.solution : ∀ {σ : Type u_1} (f : σ → MvPolynomial σ ℂ), (∀ (v : σ), MvPolynomial.totalDegree (f v) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial σ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial σ ℂ → MvPolynomial σ ℂ) P) ≤ MvPolynomial.totalDegree P :=
  fun f hf P => aeval_totalDegree_le f hf P
end GlobalTheory.AevalTotalDegreeBound
