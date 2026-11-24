-- Prove2me | solution 1 for GlobalTheory.UnipotentDecomposition.udl_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:49:46.689951+00:00
-- url     : https://prove2.me/submissions/13ebce28-6c4b-495f-b332-2fcbf2f6311f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentDecomposition
open Matrix
namespace GlobalTheory.UnipotentDecomposition
theorem _root_.solution {O : Type} [CommRing O] {m : ℕ} (A B : Matrix (Fin m) (Fin m) O) (d : Fin m → O) (i j : Fin m) :
    (A * Matrix.diagonal d * B) i j = ∑ k, A i k * d k * B k j := by
  rw [Matrix.mul_apply]; simp_rw [Matrix.mul_diagonal]
end GlobalTheory.UnipotentDecomposition
