-- Prove2me | solution 1 for GlobalTheory.FinWeil.isHeis_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:50:10.994901+00:00
-- url     : https://prove2.me/submissions/d7e274bc-6410-43fc-be90-4329d64c78a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.FinWeil
theorem _root_.solution (σ : R →+* R) (w : R) (h1 : ∀ r, σ (σ r) = r) (h2 : w + σ w = 1) :
    IsHeis σ w (fun _ _ : X => (1 : ℂ)) (fun _ => (LinearMap.id : M →ₗ[ℂ] M)) :=
  ⟨h1, h2, by simp, by simp, by simp, by simp, by simp, by simp⟩
end GlobalTheory.FinWeil
