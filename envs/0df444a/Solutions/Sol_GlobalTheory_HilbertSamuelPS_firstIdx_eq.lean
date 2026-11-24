-- Prove2me | solution 1 for GlobalTheory.HilbertSamuelPS.firstIdx_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:30:46.215+00:00
-- url     : https://prove2.me/submissions/c7d05e87-5533-4f17-9e55-e4a735201cb8

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
theorem _root_.solution {u : A} {k : ℕ} (hk : evalAt φ k u ≠ 0) (hlt : ∀ i < k, evalAt φ i u = 0) :
    firstIdx φ u = k := by
  classical
  have h : ∃ k, evalAt φ k u ≠ 0 := ⟨k, hk⟩
  unfold firstIdx
  rw [dif_pos h, Nat.find_eq_iff]
  exact ⟨hk, fun i hi => not_not.mpr (hlt i hi)⟩
end GlobalTheory.HilbertSamuelPS
