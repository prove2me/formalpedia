-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.mul_blkEmb_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:31.165951+00:00
-- url     : https://prove2.me/submissions/1312b1aa-d393-468d-98ef-de9fed976070

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
theorem _root_.solution {d j : ℕ} (hj : j ≤ d) (B : Matrix (Fin j) (Fin j) K)
    (M : Matrix (Fin d) (Fin d) K) (i l : Fin d) :
    (M * blkEmb K d j B) i l =
      if h : (l : ℕ) < j then ∑ k : Fin j, M i (Fin.castLE hj k) * B k ⟨l, h⟩ else M i l := by
  rw [Matrix.mul_apply]
  by_cases h : (l : ℕ) < j
  · rw [dif_pos h]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
    · intro a ha
      have ha' : ¬ (a : ℕ) < j := fun hlt => ha ⟨⟨a, hlt⟩, by ext; simp⟩
      have hne : a ≠ l := fun e => ha' (e ▸ h)
      simp [blkEmb, ha', hne]
    · intro k
      simp [blkEmb, h]
  · rw [dif_neg h, Finset.sum_eq_single l]
    · simp [blkEmb, h]
    · intro a _ ha
      simp [blkEmb, h, ha]
    · simp
end GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
