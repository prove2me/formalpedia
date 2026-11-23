-- Prove2me | solution 1 for GlobalTheory.FinWeil.IsHeis.iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:34.136106+00:00
-- url     : https://prove2.me/submissions/ce5c8fcb-36a2-4f33-8f45-2f038441b170

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
theorem _root_.solution {A : Submodule R X} (hA : SelfDual γ A) {x y : X} (hx : x ∈ A) (hy : y ∈ A) : γ x y = 1 := (hA x).1 hx y hy
end GlobalTheory.FinWeil.IsHeis
