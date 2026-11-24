-- Prove2me | solution 1 for GlobalTheory.MinorNorm.cast_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:33.319114+00:00
-- url     : https://prove2.me/submissions/6c4efaad-25cf-4a8f-ba85-5943779cdc90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {k : ℕ} (x : Fin k → Fin k → R) (d : Fin k → Fin k → Derivation ℂ R R)
variable {x d}
namespace GlobalTheory.MinorNorm
theorem _root_.solution (ρ : Fin k → Fin k) :
    ((eps ρ : ℤ) : R) = (Matrix.of fun t s => if ρ t = s then (1 : R) else 0).det := by
  unfold eps
  rw [Int.cast_det]
  congr 1
  ext t s
  simp
end GlobalTheory.MinorNorm
