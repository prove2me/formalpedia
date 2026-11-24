-- Prove2me | solution 1 for GlobalTheory.CubeLift.del_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:53.038829+00:00
-- url     : https://prove2.me/submissions/885094d4-b24c-471e-972c-3a36e21a0dc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_um_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]
namespace GlobalTheory.CubeLift
theorem _root_.solution {I : Ideal A} {g : (A[X])ˣ} (hg : g ∈ cong I) (a b c : X →+ Y) : del g a b c ∈ cong I :=
  div_mem (div_mem (div_mem (mul_mem (mul_mem (mul_mem (um_mem _ hg) (um_mem _ hg)) (um_mem _ hg)) (um_mem _ hg))
    (um_mem _ hg)) (um_mem _ hg)) (um_mem _ hg)
end GlobalTheory.CubeLift
