-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.conj_apply_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:34.335935+00:00
-- url     : https://prove2.me/submissions/2d813ae6-c4c4-4bcb-8eea-d69f9e3aeeba

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerBlockEmbeddingConj
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Conj_blkEmb_mul_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Conj_mul_blkEmb_apply

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
variable {K : Type} [Field K]
namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
theorem _root_.solution {d j : ℕ} (hj : j ≤ d) (A B : Matrix (Fin j) (Fin j) K)
    (M : Matrix (Fin d) (Fin d) K) (i l : Fin d) (hl : j ≤ (l : ℕ)) :
    (blkEmb K d j A * M * blkEmb K d j B) i l =
      if h : (i : ℕ) < j then ∑ k : Fin j, A ⟨i, h⟩ k * M (Fin.castLE hj k) l else M i l := by
  rw [mul_blkEmb_apply hj, dif_neg (not_lt.2 hl), blkEmb_mul_apply hj]
end GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
