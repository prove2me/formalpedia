-- Prove2me | solution 1 for GlobalTheory.HermForm.Unimodular.exists_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:55.387861+00:00
-- url     : https://prove2.me/submissions/d01ad886-9642-40a6-883c-88236d01ee66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField
open GlobalTheory
open GlobalTheory.HermForm
variable {R M N P : Type*} [CommRing R] [StarRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable (h : HermForm R M)
variable {h}
namespace GlobalTheory.HermForm
namespace Unimodular
theorem _root_.solution (H : h.Unimodular) (φ : Module.Dual R M) :
    ∃ y, ∀ x, h x y = φ x :=
  (h.unimodular_iff.1 H).2 φ
end Unimodular
end GlobalTheory.HermForm
