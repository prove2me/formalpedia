-- Prove2me | solution 1 for GlobalTheory.T.gauss_sum_hermitian_norm_level_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:48:28.040056+00:00
-- url     : https://prove2.me/submissions/99974155-9416-4b04-9531-e6e0d267a10f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelOne
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelOneStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_gauss_level_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (a : R), σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ 1, ψ 1 (Ideal.Quotient.mk (lev ϖ 1) a * (barσ σ ϖ hR.fix_ϖ 1 w * w))) = (ε : ℂ) * q := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.gauss_level_one | exact GlobalTheory.CompanionTheory.SiegLoc.gauss_level_one | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.gauss_level_one <;> assumption)
end _root_.GlobalTheory.T
