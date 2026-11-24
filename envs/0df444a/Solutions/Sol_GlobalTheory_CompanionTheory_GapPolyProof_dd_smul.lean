-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapPolyProof.dd_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:33:10.704934+00:00
-- url     : https://prove2.me/submissions/f00528ef-7f9e-4377-8db6-e49d9d490f6c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountLeOfDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapPolyProof
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
namespace GlobalTheory.CompanionTheory.GapPolyProof
theorem _root_.solution (n : ℕ) (v : ℕ → E) (a : ℂ) (ψ : E →ₗ[ℂ] ℂ) : dd n v (a • ψ) = C a * dd n v ψ := by
  simp [dd, Finset.mul_sum, mul_assoc]
end GlobalTheory.CompanionTheory.GapPolyProof
