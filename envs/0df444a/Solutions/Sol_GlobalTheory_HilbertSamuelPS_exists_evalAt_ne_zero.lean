-- Prove2me | solution 1 for GlobalTheory.HilbertSamuelPS.exists_evalAt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:33.12285+00:00
-- url     : https://prove2.me/submissions/e0b02356-2030-4808-bb5b-7c6492a3f003

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
import Theorems.Thm_GlobalTheory_HilbertSamuelPS_evalAt_of_lt

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
variable {φ}
namespace GlobalTheory.HilbertSamuelPS
theorem _root_.solution (hinj : ∀ u : A, (∀ j, φ j u = 0) → u = 0) {u : A} (hu : u ≠ 0) :
    ∃ k, evalAt φ k u ≠ 0 := by
  by_contra h
  push_neg at h
  exact hu (hinj u fun j => by simpa [evalAt_of_lt φ j.2] using h j)
end GlobalTheory.HilbertSamuelPS
