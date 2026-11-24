-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapPolyProof.dd_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:33:09.570117+00:00
-- url     : https://prove2.me/submissions/54246277-2f25-4825-8238-ac4223beb9b1

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
theorem _root_.solution (n : ℕ) (v : ℕ → E) (ψ ψ' : E →ₗ[ℂ] ℂ) : dd n v (ψ + ψ') = dd n v ψ + dd n v ψ' := by
  simp [dd, add_mul, Finset.sum_add_distrib]
end GlobalTheory.CompanionTheory.GapPolyProof
