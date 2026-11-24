-- Prove2me | solution 1 for GlobalTheory.PiSimple.pp_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:27:05.604346+00:00
-- url     : https://prove2.me/submissions/be9daae6-74c6-418a-a514-b63af88b3484

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmodulePiTensor
import Theorems.Thm_GlobalTheory_PiSimple_simpleOver_of_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.PiSimple
open GlobalTheory.TensHead
namespace GlobalTheory.PiSimple
theorem _root_.solution : PP PUnit := by
  intro _ M _ _ Op K _ _ hso
  let e := PiTensorProduct.subsingletonEquiv (R := ℂ) (s := M) PUnit.unit
  refine simpleOver_of_equiv e _ (Op PUnit.unit) _ (K PUnit.unit) ?_ ?_ (hso _)
  · apply le_antisymm
    · rw [piKer, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨y, ⟨i, hi⟩, rfl⟩, rfl⟩
      cases i
      simpa [e] using hi
    · intro x hx
      refine ⟨e.symm x, Submodule.subset_span ⟨_, ⟨PUnit.unit, by simpa using hx⟩, rfl⟩, by simp⟩
  · intro g hg
    refine ⟨piOp PUnit.unit g, ⟨PUnit.unit, g, hg, rfl⟩, fun x => ?_⟩
    have H : g ∘ₗ (e : _ →ₗ[ℂ] M PUnit.unit) = (e : _ →ₗ[ℂ] M PUnit.unit) ∘ₗ piOp PUnit.unit g := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro y
      simp [e, piOp, PiTensorProduct.map_tprod]
    exact LinearMap.congr_fun H x
end GlobalTheory.PiSimple
