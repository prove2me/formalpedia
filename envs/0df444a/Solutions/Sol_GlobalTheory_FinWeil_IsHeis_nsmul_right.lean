-- Prove2me | solution 1 for GlobalTheory.FinWeil.IsHeis.nsmul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:09:53.692257+00:00
-- url     : https://prove2.me/submissions/ed00b2db-c3d6-4b1c-8ae0-86af01900e15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_zero_right

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
theorem _root_.solution (n : ℕ) (x y : X) : γ x (n • y) = γ x y ^ n := by
  induction n with
  | zero => simp [h.zero_right]
  | succ n ih => rw [succ_nsmul, h.add_right, ih, pow_succ]
end GlobalTheory.FinWeil.IsHeis
