-- Prove2me | solution 1 for GlobalTheory.FinWeil.IsHeis.zero_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:21.665123+00:00
-- url     : https://prove2.me/submissions/6586ab9b-88db-43ad-a49b-43b87bf288ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_ne_zero

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
theorem _root_.solution (y : X) : γ 0 y = 1 := by
  have h1 := h.add_left 0 0 y
  rw [add_zero] at h1
  exact (mul_eq_left₀ (h.ne_zero 0 y)).1 h1.symm
end GlobalTheory.FinWeil.IsHeis
