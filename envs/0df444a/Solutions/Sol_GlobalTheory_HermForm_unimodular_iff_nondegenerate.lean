-- Prove2me | solution 1 for GlobalTheory.HermForm.unimodular_iff_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:50:37.616548+00:00
-- url     : https://prove2.me/submissions/01cc880e-d456-470f-a679-64e950173785

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Theorems.Thm_GlobalTheory_HermForm_IsometryEquiv_unimodular
import Theorems.Thm_GlobalTheory_HermForm_Nondegenerate_unimodular

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
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : HermForm K V}
namespace GlobalTheory.HermForm
theorem _root_.solution : h.Unimodular ↔ h.Nondegenerate :=
  ⟨Unimodular.nondegenerate, Nondegenerate.unimodular⟩
end GlobalTheory.HermForm
