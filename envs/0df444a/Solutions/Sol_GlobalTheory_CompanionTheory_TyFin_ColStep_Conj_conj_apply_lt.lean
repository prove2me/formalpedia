-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.conj_apply_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:53:22.369305+00:00
-- url     : https://prove2.me/submissions/a1898a17-d881-4e5f-a897-ea2788c12ce7

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
theorem _root_.solution {d j : ℕ} (hj : j ≤ d) (A B : Matrix (Fin j) (Fin j) K) (hAB : A * B = 1)
    (M : Matrix (Fin d) (Fin d) K)
    (hM : ∀ i l : Fin d, (l : ℕ) < j → M i l = if i = l then 1 else 0)
    (i l : Fin d) (hl : (l : ℕ) < j) :
    (blkEmb K d j A * M * blkEmb K d j B) i l = if i = l then 1 else 0 := by
  rw [mul_blkEmb_apply hj, dif_pos hl]
  simp_rw [blkEmb_mul_apply hj]
  by_cases h : (i : ℕ) < j
  · simp only [dif_pos h]
    have inner : ∀ k : Fin j, ∑ m : Fin j, A ⟨i, h⟩ m * M (Fin.castLE hj m) (Fin.castLE hj k)
        = A ⟨i, h⟩ k := by
      intro k
      rw [Finset.sum_eq_single k]
      · rw [hM _ _ (by simp)]
        simp
      · intro m _ hm
        rw [hM _ _ (by simp), if_neg (fun e => hm (Fin.castLE_injective hj e))]
        simp
      · simp
    simp_rw [inner]
    have := congrFun (congrFun hAB ⟨i, h⟩) ⟨l, hl⟩
    rw [Matrix.mul_apply] at this
    rw [this, Matrix.one_apply]
    by_cases e : i = l
    · simp [e]
    · have e' : ¬ ((⟨i, h⟩ : Fin j) = ⟨l, hl⟩) := fun q => e (Fin.ext (by simpa using q))
      simp [e, e']
  · simp only [dif_neg h]
    have hne : i ≠ l := fun e => h (e ▸ hl)
    rw [if_neg hne]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk : i ≠ Fin.castLE hj k := fun e => h (by rw [e]; simp)
    rw [hM _ _ (by simp), if_neg hk]
    simp
end GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
