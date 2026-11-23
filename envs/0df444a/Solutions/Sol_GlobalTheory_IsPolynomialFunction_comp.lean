-- Prove2me | solution 1 for GlobalTheory.IsPolynomialFunction.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:33.982815+00:00
-- url     : https://prove2.me/submissions/74ab8376-e2d4-46df-98bd-2f9d35d60260

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
open GlobalTheory
variable (K : Type*) [CommSemiring K] {M : Type*} [AddCommMonoid M] [Module K M]
variable {K}
namespace GlobalTheory
namespace IsPolynomialFunction
theorem _root_.solution {N : Type*} [AddCommMonoid N] [Module K N] {P : M → K}
    (hP : IsPolynomialFunction K P) (L : N →ₗ[K] M) : IsPolynomialFunction K (fun y => P (L y)) := by
  induction hP using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨φ, rfl⟩ := hf
    exact IsPolynomialFunction.linear (φ ∘ₗ L)
  | algebraMap c => exact IsPolynomialFunction.const c
  | add f g _ _ hf hg => exact hf.add hg
  | mul f g _ _ hf hg => exact hf.mul hg
end IsPolynomialFunction
end GlobalTheory
