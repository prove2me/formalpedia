-- Prove2me | solution 1 for GlobalTheory.UnipotentBorder.udl_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:34.098801+00:00
-- url     : https://prove2.me/submissions/27e52f46-d0b7-46cd-96a5-05c701431643

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]
namespace GlobalTheory.UnipotentBorder
theorem _root_.solution {m : ℕ} (U L : Matrix (Fin m) (Fin m) O) (d : Fin m → O) (i j : Fin m) :
    (U * diagonal d * L) i j = ∑ k, U i k * d k * L k j := by
  rw [mul_apply]
  simp only [mul_diagonal]
end GlobalTheory.UnipotentBorder
