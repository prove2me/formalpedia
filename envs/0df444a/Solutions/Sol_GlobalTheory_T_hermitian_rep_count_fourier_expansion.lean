-- Prove2me | solution 1 for GlobalTheory.T.hermitian_rep_count_fourier_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:13:36.021162+00:00
-- url     : https://prove2.me/submissions/4e1e8c47-1556-402b-be77-d4951f34b38c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianRepCountFourierExpansion
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianRepCountFourierExpansionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_level_identity


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (m n k : ℕ) (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), cT σ S = S → cT σ T = T → (∀ Y : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k), Y ∈ hermMod σ ϖ n k → (Y = 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = (Nat.card (hermMod σ ϖ n k) : ℂ)) ∧ (Y ≠ 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = 0)) → (∀ B ∈ hermMod σ ϖ n k, (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ψ k (Matrix.trace (B * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x)))) = (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) * (((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B))) → siegAt ϖ σ ψ q ε m T k = ((densAt σ ϖ S T k : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.level_identity | exact GlobalTheory.CompanionTheory.SiegLoc.level_identity | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.level_identity <;> assumption)
end _root_.GlobalTheory.T
