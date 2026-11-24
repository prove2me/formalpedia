-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.wh_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:43:57.562471+00:00
-- url     : https://prove2.me/submissions/06eec093-a18e-4668-a62d-9aef17d0871f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternSetCardColumnStepStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AdditiveCharacterSumOrthogonalityStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerColumnRecursionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalUnipotentRadicalSumZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerVanishesOfRadicalSumsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GLTransitiveNonzeroVectorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockEmbeddingGLInverseStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerBlockEmbeddingConjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalWhittaker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep
namespace GlobalTheory.CompanionTheory.TyFin.ColStep
theorem _root_.solution (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) :
    wh (colGe d 1) (colGeE K d 1) ψ₀ χ = wh (fun i j : Fin d => i < j) (cutE K d 0) ψ₀ χ := by
  have h1 : colGe d 1 = fun i j : Fin d => i < j := by
    funext i l
    simp only [colGe, eq_iff_iff, and_iff_left_iff_imp]
    intro h
    have : (i : ℕ) < l := h
    omega
  have h2 : colGeE K d 1 = cutE K d 0 := by
    funext i l
    simp only [colGeE, cutE]
    congr 1
    apply propext
    omega
  rw [h1, h2]
end GlobalTheory.CompanionTheory.TyFin.ColStep
