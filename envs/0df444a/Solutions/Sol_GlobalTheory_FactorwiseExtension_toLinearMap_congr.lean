-- Prove2me | solution 1 for GlobalTheory.FactorwiseExtension.toLinearMap_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:51:19.36745+00:00
-- url     : https://prove2.me/submissions/fe81f6b8-6796-43bd-a230-250fd69e5f83

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
theorem _root_.solution (T : MultilinearMap ℂ H E) {w w' : ∀ τ, H τ} (i : ι)
    (h : ∀ j, j ≠ i → w j = w' j) : T.toLinearMap w i = T.toLinearMap w' i := by
  ext x
  simp only [MultilinearMap.toLinearMap_apply]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [update_of_ne hj, h j hj]
end GlobalTheory.FactorwiseExtension
