-- Prove2me | solution 1 for GlobalTheory.FactorwiseExtension.toLinearMap_update_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:51:21.951893+00:00
-- url     : https://prove2.me/submissions/0941f09d-bf75-4ab4-8708-670a18bee141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMultilinearSlotwiseExtensionOfEquivariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function
open GlobalTheory GlobalTheory.FactorwiseExtension
variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
  {E : Type} [AddCommGroup E] [Module ℂ E]
namespace GlobalTheory.FactorwiseExtension
theorem _root_.solution (T : MultilinearMap ℂ H E) {i j : ι} (h : i ≠ j) (w : ∀ τ, H τ)
    (x y : H i) : T.toLinearMap (update w i (x + y)) j =
      T.toLinearMap (update w i x) j + T.toLinearMap (update w i y) j := by
  ext a
  simp only [MultilinearMap.toLinearMap_apply, LinearMap.add_apply]
  rw [update_comm h, update_comm h, update_comm h, T.map_update_add]
end GlobalTheory.FactorwiseExtension
