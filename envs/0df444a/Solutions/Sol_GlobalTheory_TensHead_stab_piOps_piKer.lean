-- Prove2me | solution 1 for GlobalTheory.TensHead.stab_piOps_piKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:27:41.496048+00:00
-- url     : https://prove2.me/submissions/fe838b4f-de91-4612-877e-15c32d1c0fd2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead
open scoped TensorProduct
namespace GlobalTheory.TensHead
namespace _root_.GlobalTheory.TensHead
theorem _root_.solution {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i))
    (h : ∀ i, _root_.GlobalTheory.TensHead.Stab (Op i) (K i)) :
    _root_.GlobalTheory.TensHead.Stab (_root_.GlobalTheory.TensHead.piOps Op) (_root_.GlobalTheory.TensHead.piKer K) := by
  unfold _root_.GlobalTheory.TensHead.Stab at h ⊢
  rintro _ ⟨i, g, hg, rfl⟩ x hx
  unfold _root_.GlobalTheory.TensHead.piKer at hx ⊢
  have hle : Submodule.span ℂ {t | ∃ y : ∀ j, M j, (∃ j, y j ∈ K j) ∧ t = PiTensorProduct.tprod ℂ y}
      ≤ (Submodule.span ℂ {t | ∃ y : ∀ j, M j, (∃ j, y j ∈ K j) ∧ t = PiTensorProduct.tprod ℂ y}).comap
        (_root_.GlobalTheory.TensHead.piOp i g) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, ⟨j, hj⟩, rfl⟩
    refine Submodule.subset_span ⟨fun k => Function.update (fun _ => LinearMap.id) i g k (y k), ⟨j, ?_⟩, ?_⟩
    · by_cases hji : j = i
      · subst hji
        simpa using h j g hg _ hj
      · simpa [Function.update_of_ne hji] using hj
    · simp [_root_.GlobalTheory.TensHead.piOp]
  exact hle hx
end _root_.GlobalTheory.TensHead
end GlobalTheory.TensHead
