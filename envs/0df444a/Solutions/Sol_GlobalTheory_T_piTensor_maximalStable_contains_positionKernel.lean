-- Prove2me | solution 1 for GlobalTheory.T.piTensor_maximalStable_contains_positionKernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:15:39.64031+00:00
-- url     : https://prove2.me/submissions/98c4a874-9ac7-4392-bd83-3a375c13e644

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PiTensorMaximalStableContainsFactorKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimpleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PiTensorMaximalStableContainsSlotKernelStatement
import Theorems.Thm_GlobalTheory_TensHead_position_mem_of_maximal_stable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i))) (i : ι)
    (Rel K : Submodule ℂ (M i)),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (M i)), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op i, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ (M i), Rel ≤ N → GlobalTheory.TensHead.Stab (Op i) N → N ≠ ⊤ → N ≤ K) →
    K ≠ ⊤ → GlobalTheory.TensHead.Stab (Op i) K →
    ∀ N' : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)),
      (∀ x ∈ Rel, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N') →
      GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) N' →
      (∀ U, GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) U → N' ≤ U →
        U = N' ∨ U = ⊤) →
      ∀ x ∈ K, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N' := by
  first | exact @GlobalTheory.TensHead.position_mem_of_maximal_stable | exact GlobalTheory.TensHead.position_mem_of_maximal_stable | (intros; apply GlobalTheory.TensHead.position_mem_of_maximal_stable <;> assumption)
end _root_.GlobalTheory.T
