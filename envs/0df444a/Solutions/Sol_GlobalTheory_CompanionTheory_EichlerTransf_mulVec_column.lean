-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EichlerTransf.mulVec_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:05:21.187896+00:00
-- url     : https://prove2.me/submissions/010c62f4-8f6b-4edb-9729-a071b9c62563

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExtendByZeroApplyOfNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EichlerTransf
open scoped ComplexOrder
variable {n m : ℕ}
namespace GlobalTheory.CompanionTheory.EichlerTransf
theorem _root_.solution {p q r : ℕ} (N : Matrix (Fin p) (Fin q) ℂ) (M : Matrix (Fin q) (Fin r) ℂ)
    (i : Fin r) : (N *ᵥ fun j => M j i) = fun j => (N * M) j i := by
  ext k; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
end GlobalTheory.CompanionTheory.EichlerTransf
