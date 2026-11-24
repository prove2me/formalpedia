-- Prove2me | solution 1 for GlobalTheory.ScalarSnakeLength.length_eq_ker_add_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:32:52.401582+00:00
-- url     : https://prove2.me/submissions/9c206cea-853c-4c32-9374-d83f2f85ec06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ScalarSnakeLength
variable {A : Type} [CommRing A]
namespace GlobalTheory.ScalarSnakeLength
theorem _root_.solution {M P : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (φ : M →ₗ[A] P) :
    Module.length A M =
      Module.length A (LinearMap.ker φ) + Module.length A (LinearMap.range φ) :=
  Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ.rangeRestrict
    Subtype.val_injective φ.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
end GlobalTheory.ScalarSnakeLength
