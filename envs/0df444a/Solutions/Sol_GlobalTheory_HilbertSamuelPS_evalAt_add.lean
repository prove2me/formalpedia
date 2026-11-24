-- Prove2me | solution 1 for GlobalTheory.HilbertSamuelPS.evalAt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:30:37.667398+00:00
-- url     : https://prove2.me/submissions/a87909c8-8914-48aa-b713-31194b9d4650

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open GlobalTheory.HilbertSamuelPS
open MvPowerSeries
variable {D n : ℕ} {A : Type} [CommRing A] [Algebra ℂ A]
  (φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ))
namespace GlobalTheory.HilbertSamuelPS
theorem _root_.solution (k : ℕ) (u v : A) : evalAt φ k (u + v) = evalAt φ k u + evalAt φ k v := by
  unfold evalAt; split_ifs <;> simp
end GlobalTheory.HilbertSamuelPS
