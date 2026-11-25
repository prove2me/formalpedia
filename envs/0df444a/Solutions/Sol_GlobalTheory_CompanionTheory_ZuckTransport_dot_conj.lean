-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckTransport.dot_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:29:40.755872+00:00
-- url     : https://prove2.me/submissions/cbd507ef-c562-4b77-af39-adedce94afed

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_BetaAtInfinityZero
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZuckermanHypothesis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckTransport
open PI.UpqRep CompanionTheory.LimBd.SchurHpk
namespace GlobalTheory.CompanionTheory.ZuckTransport
theorem _root_.solution {n : ℕ} (P a Q : Matrix (Fin n) (Fin n) ℂ) (u x : Fin n → ℂ) :
    u ⬝ᵥ ((P * a * Q) *ᵥ x) = (u ᵥ* P) ⬝ᵥ (a *ᵥ (Q *ᵥ x)) := by
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
end GlobalTheory.CompanionTheory.ZuckTransport
