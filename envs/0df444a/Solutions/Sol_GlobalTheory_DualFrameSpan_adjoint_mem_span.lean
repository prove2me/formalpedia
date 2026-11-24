-- Prove2me | solution 1 for GlobalTheory.DualFrameSpan.adjoint_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:25:00.67782+00:00
-- url     : https://prove2.me/submissions/956e354a-27e1-4ed3-8e63-ced5baea583c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualFrameSpanUnitaryRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.DualFrameSpan
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {G : Type} [Mul G] (K : Set G) (ρ : G → (H →ₗ[ℂ] H))
namespace GlobalTheory.DualFrameSpan
theorem _root_.solution (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g')
    {X : H →ₗ[ℂ] H} (hX : X ∈ Submodule.span ℂ (ρ '' K)) :
    LinearMap.adjoint X ∈ Submodule.span ℂ (ρ '' K) := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨g', hg', he⟩ := hadj g hg
    rw [he]; exact Submodule.subset_span ⟨g', hg', rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
end GlobalTheory.DualFrameSpan
