-- Prove2me | solution 1 for GlobalTheory.DualCokernelFlat.dual_baseChange_dualMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:35.864587+00:00
-- url     : https://prove2.me/submissions/d2441595-c01c-435c-b3c5-d26c92a9a4a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExactDualMapOfExactFibresOfIsRegularLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfComplexExactModMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatQuotientOfEquivCokerDualMapOfExactFibres
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_baseChange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct Function
open GlobalTheory
open GlobalTheory.DualCokernelFlat
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
namespace GlobalTheory.DualCokernelFlat
theorem _root_.solution {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (a : M →ₗ[A] N) (f : Module.Dual A N) :
    Module.Dual.baseChange B (a.dualMap f) =
      (a.baseChange B).dualMap (Module.Dual.baseChange B f) := by
  ext x
  simp
end GlobalTheory.DualCokernelFlat
