-- Prove2me | solution 1 for GlobalTheory.HilbertSamuelPS.firstIdx_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:31.531575+00:00
-- url     : https://prove2.me/submissions/9df3c8d2-f4e9-41c4-aa7c-e86b362b06bc

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
theorem _root_.solution {u : A} (h : ∃ k, evalAt φ k u ≠ 0) :
    evalAt φ (firstIdx φ u) u ≠ 0 ∧ ∀ i < firstIdx φ u, evalAt φ i u = 0 := by
  classical
  unfold firstIdx
  rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun i hi => not_not.mp (Nat.find_min h hi)⟩
end GlobalTheory.HilbertSamuelPS
