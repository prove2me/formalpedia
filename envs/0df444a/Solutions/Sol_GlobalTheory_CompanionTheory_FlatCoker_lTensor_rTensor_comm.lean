-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlatCoker.lTensor_rTensor_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:33:24.545358+00:00
-- url     : https://prove2.me/submissions/ce715ac6-cbf9-4096-9da7-b1e277f6d6f6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatQuotientOfUniversallyInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlatCoker
namespace GlobalTheory.CompanionTheory.FlatCoker
theorem _root_.solution {R P Q X Y : Type} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (i : P →ₗ[R] Q) (g : X →ₗ[R] Y) (t : P ⊗[R] X) :
    g.lTensor Q (i.rTensor X t) = i.rTensor Y (g.lTensor P t) := by
  have h1 := LinearMap.congr_fun (LinearMap.lTensor_comp_rTensor P i g) t
  have h2 := LinearMap.congr_fun (LinearMap.rTensor_comp_lTensor P i g) t
  exact h1.trans h2.symm
end GlobalTheory.CompanionTheory.FlatCoker
