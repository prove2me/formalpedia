-- Prove2me | solution 1 for GlobalTheory.T.unimodular_hermitian_reps_count_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:08.855803+00:00
-- url     : https://prove2.me/submissions/30ae25f5-1ae1-4393-9fd1-c8958a4b1a83

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSucc
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSuccStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_solCount_succ


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsUnimod σ T → ∀ k : ℕ, 1 ≤ k → solCount σ ϖ S T (k + 1) = solCount σ ϖ S T k * q ^ (2 * m * n - n ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.solCount_succ | exact GlobalTheory.CompanionTheory.UnrDens.solCount_succ | (intros; apply GlobalTheory.CompanionTheory.UnrDens.solCount_succ <;> assumption)
end _root_.GlobalTheory.T
