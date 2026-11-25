-- Prove2me | solution 1 for GlobalTheory.T.exists_dual_frame_span_unitary_representation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:15:11.064398+00:00
-- url     : https://prove2.me/submissions/b4ad3d91-604a-4a7d-a934-571ca9cefd74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualFrameSpanUnitaryRepresentation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualFrameSpanUnitaryRepresentationStatement
import Theorems.Thm_GlobalTheory_DualFrameSpan_dual_frame


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
theorem _root_.solution : ∀ {G H : Type} [Mul G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (K : Set G) (ρ : G → (H →ₗ[ℂ] H)) (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h)
    (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g'), ∃ (m : ℕ) (k : Fin m → G) (B : Fin m → (H →ₗ[ℂ] H)), (∀ j, k j ∈ K) ∧
      (∀ A : H →ₗ[ℂ] H, ∀ g ∈ K, LinearMap.trace ℂ H (ρ g ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) * LinearMap.trace ℂ H (ρ g ∘ₗ B j)) ∧
      (∀ i, ∀ h ∈ K, B i ∘ₗ ρ h = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) • B j) := by
  first | exact @GlobalTheory.DualFrameSpan.dual_frame | exact GlobalTheory.DualFrameSpan.dual_frame | (intros; apply GlobalTheory.DualFrameSpan.dual_frame <;> assumption)
end _root_.GlobalTheory.T
