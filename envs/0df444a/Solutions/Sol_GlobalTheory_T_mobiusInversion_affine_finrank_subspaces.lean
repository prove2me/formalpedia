-- Prove2me | solution 1 for GlobalTheory.T.mobiusInversion_affine_finrank_subspaces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:13:26.192034+00:00
-- url     : https://prove2.me/submissions/e98886d6-7225-4256-a535-2046cc610fcf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusInversionAffineFinrankSubspaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusInversionAffineFinrankSubspacesStatement
import Theorems.Thm_GlobalTheory_CuspGL_moebius_affine_finrank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [Finite K] (U : Type) [AddCommGroup U] [Module K U] [FiniteDimensional K U] (G : Submodule K U → ℂ) (c₀ c : ℂ), 0 < Module.finrank K U → (∀ A : Submodule K U, ∑ᶠ B : {B : Submodule K U // B ≤ A}, G B.1 = c₀ + c * (Module.finrank K A : ℂ)) → G ⊤ = c * ∏ i ∈ Finset.Ico 1 (Module.finrank K U), (1 - (Nat.card K : ℂ) ^ i) := by
  first | exact @GlobalTheory.CuspGL.moebius_affine_finrank | exact GlobalTheory.CuspGL.moebius_affine_finrank | (intros; apply GlobalTheory.CuspGL.moebius_affine_finrank <;> assumption)
end _root_.GlobalTheory.T
