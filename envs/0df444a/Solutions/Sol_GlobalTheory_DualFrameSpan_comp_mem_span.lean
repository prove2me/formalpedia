-- Prove2me | solution 1 for GlobalTheory.DualFrameSpan.comp_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:25:01.782918+00:00
-- url     : https://prove2.me/submissions/be88db2f-99c2-4725-9eca-ca1430ccad96

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
theorem _root_.solution (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h) {h : G} (hh : h ∈ K)
    {X : H →ₗ[ℂ] H} (hX : X ∈ Submodule.span ℂ (ρ '' K)) :
    X ∘ₗ ρ h ∈ Submodule.span ℂ (ρ '' K) := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [← hρ g hg h hh]; exact Submodule.subset_span ⟨_, hmul g hg h hh, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [LinearMap.add_comp]; exact add_mem hx hy
  | smul a x _ hx => rw [LinearMap.smul_comp]; exact Submodule.smul_mem _ _ hx
end GlobalTheory.DualFrameSpan
