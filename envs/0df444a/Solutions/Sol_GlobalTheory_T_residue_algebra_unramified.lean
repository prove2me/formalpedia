-- Prove2me | solution 1 for GlobalTheory.T.residue_algebra_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:21:20.048722+00:00
-- url     : https://prove2.me/submissions/2537852d-8945-4a9d-a839-88e05042b857

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramifiedStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_resAlg_of_isUnrQuad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), ∀ h : IsUnrQuad R σ ϖ q ε, ResAlg (R ⧸ lev ϖ 1) (barσ σ ϖ h.fix_ϖ 1) q ε := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad | exact GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad | (intros; apply GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad <;> assumption)
end _root_.GlobalTheory.T
