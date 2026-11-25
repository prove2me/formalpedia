-- Prove2me | solution 1 for GlobalTheory.T.hermitian_character_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:12.585981+00:00
-- url     : https://prove2.me/submissions/8c0a8359-e7a4-4dbe-a462-f103c6abe893

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonality
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonalityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_orth_hermMod


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (n k : ℕ) (Y : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)), Y ∈ hermMod σ ϖ n k → (Y = 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = (Nat.card (hermMod σ ϖ n k) : ℂ)) ∧ (Y ≠ 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = 0) := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.HermOrth.orth_hermMod | exact GlobalTheory.CompanionTheory.SiegLoc.HermOrth.orth_hermMod | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.HermOrth.orth_hermMod <;> assumption)
end _root_.GlobalTheory.T
