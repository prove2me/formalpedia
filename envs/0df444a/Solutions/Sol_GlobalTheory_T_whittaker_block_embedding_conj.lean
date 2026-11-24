-- Prove2me | solution 1 for GlobalTheory.T.whittaker_block_embedding_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:26:00.151471+00:00
-- url     : https://prove2.me/submissions/ffb117ce-a99b-4aa7-b018-3a2e0b20094a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerBlockEmbeddingConj
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerBlockEmbeddingConjStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Conj_wh_colGeR_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) (g : GL (Fin j) K) (h : GL (Fin d) K) (r : Fin j → K),
    j < d → (∀ x y, χ (x * y * x⁻¹) = χ y) →
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) →
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) →
    wh (colGe d j) (colGeR K d j r) ψ₀ χ = wh (colGe d j) (colGeR K d j (Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K))) ψ₀ χ := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.wh_colGeR_conj | exact GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.wh_colGeR_conj | (intros; apply GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.wh_colGeR_conj <;> assumption)
end _root_.GlobalTheory.T
