-- Prove2me | solution 1 for GlobalTheory.T.exists_eigen_complement_of_adjoint_stable_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:15:19.456826+00:00
-- url     : https://prove2.me/submissions/9b940e77-29b8-481b-a68f-09dad30a4a1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableComplementOfKernelExists
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableComplementOfKernelExistsStatement
import Theorems.Thm_GlobalTheory_stable_complement_of_kernel_exists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V), FiniteDimensional ℂ H0 → ∀ (A : Set (Module.End ℂ V)), (∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0) → (∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0) → (∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) → ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧ ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := by
  first | exact @GlobalTheory.stable_complement_of_kernel_exists | exact GlobalTheory.stable_complement_of_kernel_exists | (intros; apply GlobalTheory.stable_complement_of_kernel_exists <;> assumption)
end _root_.GlobalTheory.T
