-- Prove2me | solution 1 for GlobalTheory.KilledFin.span_adjoin_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:32:30.643+00:00
-- url     : https://prove2.me/submissions/92339a41-ddf3-4fb1-ab91-6365a1c41707

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAlgebraOrbitOfAnnihilated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.KilledFin
open Polynomial
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.KilledFin
theorem _root_.solution (s : Set (Module.End ℂ V)) (K : Submodule ℂ V)
    (hs : ∀ u ∈ s, ∀ v ∈ K, u v ∈ K) (ψ : V) (hψ : ψ ∈ K) :
    Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ s : Set (Module.End ℂ V)))
      ≤ K := by
  have key : ∀ z ∈ Algebra.adjoin ℂ s, ∀ v ∈ K, z v ∈ K := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx => exact hs x hx
    | algebraMap r =>
      intro v hv
      rw [Module.algebraMap_end_apply]
      exact K.smul_mem r hv
    | add x y _ _ hx hy =>
      intro v hv
      rw [LinearMap.add_apply]
      exact K.add_mem (hx v hv) (hy v hv)
    | mul x y _ _ hx hy =>
      intro v hv
      rw [Module.End.mul_apply]
      exact hx _ (hy v hv)
  rw [Submodule.span_le]
  rintro _ ⟨z, hz, rfl⟩
  exact key z hz ψ hψ
end GlobalTheory.KilledFin
