-- Prove2me | solution 1 for GlobalTheory.AevalTotalDegreeLinear.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:09:30.783044+00:00
-- url     : https://prove2.me/submissions/d7a719ad-db2b-44fc-bfc8-01c5f74bc3e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeAevalLeOfLinear
import Theorems.Thm_GlobalTheory_AevalTotalDegreeLinear_totalDegree_aeval_le_of_linear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AevalTotalDegreeLinear
open MvPolynomial
namespace GlobalTheory.AevalTotalDegreeLinear
theorem _root_.solution : ∀ {κ : Type} (f : κ → MvPolynomial κ ℂ), (∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial κ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P) ≤ MvPolynomial.totalDegree P :=
  fun f hf P => totalDegree_aeval_le_of_linear f hf P
end GlobalTheory.AevalTotalDegreeLinear
