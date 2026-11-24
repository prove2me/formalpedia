-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.colGeR_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:50:27.052599+00:00
-- url     : https://prove2.me/submissions/23543208-10ce-4a71-a74a-7c8ebcf335f6

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
theorem _root_.solution (K : Type) [Field K] (d j : ℕ) (hj : 1 ≤ j) :
    colGeR K d j (Pi.single (⟨j - 1, by omega⟩ : Fin j) (1 : K) : Fin j → K) = colGeE K d j := by
  funext i l
  by_cases hl : (l : ℕ) = j
  · by_cases hi : (l : ℕ) = i + 1
    · have hlt : (i : ℕ) < j := by omega
      have hij : (⟨(i : ℕ), hlt⟩ : Fin j) = ⟨j - 1, by omega⟩ := Fin.ext (by simp; omega)
      simp only [colGeR, colGeE]
      rw [dif_pos ⟨hl, hlt⟩, hij]
      simp [hl, hi]
      omega
    · simp only [colGeR, colGeE]
      by_cases hlt : (i : ℕ) < j
      · rw [dif_pos ⟨hl, hlt⟩]
        have hne : (⟨(i : ℕ), hlt⟩ : Fin j) ≠ ⟨j - 1, by omega⟩ := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        simp [hi, Pi.single_eq_of_ne hne]
      · rw [dif_neg (by tauto)]
        simp [hi]
  · simp only [colGeR, colGeE]
    rw [dif_neg (by tauto)]
    have : (j + 1 ≤ (l : ℕ)) ↔ j ≤ (l : ℕ) := by omega
    simp [this]
end GlobalTheory.CompanionTheory.TyFin.ColStep
