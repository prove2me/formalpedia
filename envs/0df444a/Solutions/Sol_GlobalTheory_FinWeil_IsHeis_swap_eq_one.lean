-- Prove2me | solution 1 for GlobalTheory.FinWeil.IsHeis.swap_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:21.131648+00:00
-- url     : https://prove2.me/submissions/ac3712bf-1b8c-4ab5-a92a-55a9b351b7e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_swap

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
theorem _root_.solution {x y : X} (hxy : γ x y = 1) : γ y x = 1 := by rw [h.swap, hxy, inv_one]
end GlobalTheory.FinWeil.IsHeis
