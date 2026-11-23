-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.blkEmb_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:32.971148+00:00
-- url     : https://prove2.me/submissions/e4ded940-3b95-414e-9157-82d4a672f8b3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerBlockEmbeddingConj

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
theorem _root_.solution {d j : ℕ} (hj : j ≤ d) (A : Matrix (Fin j) (Fin j) K)
    (M : Matrix (Fin d) (Fin d) K) (i l : Fin d) :
    (blkEmb K d j A * M) i l =
      if h : (i : ℕ) < j then ∑ k : Fin j, A ⟨i, h⟩ k * M (Fin.castLE hj k) l else M i l := by
  rw [Matrix.mul_apply]
  by_cases h : (i : ℕ) < j
  · rw [dif_pos h]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
    · intro a ha
      have ha' : ¬ (a : ℕ) < j := fun hlt => ha ⟨⟨a, hlt⟩, by ext; simp⟩
      have hne : i ≠ a := fun e => ha' (e ▸ h)
      simp [blkEmb, ha', hne]
    · intro k
      simp [blkEmb, h]
  · rw [dif_neg h, Finset.sum_eq_single i]
    · simp [blkEmb, h]
    · intro a _ ha
      simp [blkEmb, h, Ne.symm ha]
    · simp
end GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
