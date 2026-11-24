-- Prove2me | solution 1 for GlobalTheory.EigFlat.sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:24:57.151068+00:00
-- url     : https://prove2.me/submissions/5263ef6d-6589-4459-a4ae-49435979b6f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CommonEigenvectorsFlatBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix TensorProduct
open GlobalTheory
open GlobalTheory.EigFlat
variable {A : Type} [CommRing A]
namespace GlobalTheory.EigFlat
theorem _root_.solution {g m : ℕ} (u : Fin m → Fin g → A) (B : Type) [CommRing B]
    [Algebra A B] (cf : Fin m → B) :
    (∑ k, cf k • (fun j => algebraMap A B (u k j)))
      = cf ᵥ* (Matrix.of u).map (algebraMap A B) := by
  funext j
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
end GlobalTheory.EigFlat
