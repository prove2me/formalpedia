-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.sum_fin_of_ge_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:49:18.193608+00:00
-- url     : https://prove2.me/submissions/2c415e7f-4377-4b3f-83fb-0600d3a7cc34

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockEmbeddingGLInverse

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL
variable (K : Type) [Field K]
namespace GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL
theorem _root_.solution {d j : ℕ} (hjd : j ≤ d) (f : Fin d → K)
    (hf : ∀ k : Fin d, j ≤ (k : ℕ) → f k = 0) :
    ∑ k, f k = ∑ k : Fin j, f (Fin.castLE hjd k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjd
  rw [Fin.sum_univ_add]
  have h0 : ∑ k : Fin m, f (Fin.natAdd j k) = 0 :=
    Finset.sum_eq_zero fun k _ => hf _ (by simp)
  rw [h0, add_zero]
  rfl
end GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL
