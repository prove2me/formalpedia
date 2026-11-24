-- Prove2me | solution 1 for GlobalTheory.IsPolynomialFunction.continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:54:00.929818+00:00
-- url     : https://prove2.me/submissions/d2dec3b8-d12c-4b34-b02a-f318c81e0fde

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
theorem _root_.solution {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] {P : E → 𝕜}
    (hP : IsPolynomialFunction 𝕜 P) : Continuous P := by
  induction hP using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨φ, rfl⟩ := hf
    exact φ.continuous_of_finiteDimensional
  | algebraMap c => exact continuous_const
  | add f g _ _ hf hg => exact hf.add hg
  | mul f g _ _ hf hg => exact hf.mul hg
end IsPolynomialFunction
end GlobalTheory
