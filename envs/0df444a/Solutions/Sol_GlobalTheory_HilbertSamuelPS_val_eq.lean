-- Prove2me | solution 1 for GlobalTheory.HilbertSamuelPS.val_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:47:51.654374+00:00
-- url     : https://prove2.me/submissions/0a916578-5750-40d7-ac5a-8c0ff350652b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_firstIdx_eq

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
theorem _root_.solution {u : A} {k : ℕ} (hk : evalAt φ k u ≠ 0) (hlt : ∀ i < k, evalAt φ i u = 0) :
    val φ u = toLex (k, lexOrder (evalAt φ k u)) := by
  unfold val; rw [firstIdx_eq φ hk hlt]
end GlobalTheory.HilbertSamuelPS
