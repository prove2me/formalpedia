-- Prove2me | solution 1 for GlobalTheory.FinWeil.IsHeis.skew
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:50.993745+00:00
-- url     : https://prove2.me/submissions/07086f48-e4ee-4cdb-9bd7-be4d23b948ab

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
open GlobalTheory.FinWeil.IsHeis
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W)
include h
namespace GlobalTheory.FinWeil.IsHeis
theorem _root_.solution (x y : X) : γ x y * γ y x = 1 := by
  have h1 := h.alt (x + y)
  rw [h.add_left, h.add_right, h.add_right, h.alt, h.alt] at h1
  simpa using h1
end GlobalTheory.FinWeil.IsHeis
