-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:24:58.894702+00:00
-- url     : https://prove2.me/submissions/be4505c4-7e37-4ed5-8e63-8567de3e2a14

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockEmbeddingGLInverse
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_BlockEmbeddingGL_blkEmb_one
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_BlockEmbeddingGL_blkEmb_mul

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
theorem _root_.solution : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j ≤ d →
    ∀ g : GL (Fin j) K, ∃ h : GL (Fin d) K,
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) ∧
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) := by
  intro K _ _ _ d j hjd g
  refine ⟨⟨GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb K d j (g : Matrix (Fin j) (Fin j) K),
    GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K), ?_, ?_⟩, rfl, rfl⟩
  · rw [← GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_mul K hjd, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_one]
  · rw [← GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_mul K hjd, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_one]
end GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL
