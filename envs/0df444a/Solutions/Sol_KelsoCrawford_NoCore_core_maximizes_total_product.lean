-- Prove2me | solution 1 for KelsoCrawford.NoCore.core_maximizes_total_product
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:25:35.224328+00:00
-- url     : https://prove2.me/submissions/af754da1-6dcf-478a-8ee7-90f365f1d005

import Mathlib
import Definitions.Def_KelsoCrawford_NoCore_Model
import Definitions.Def_KelsoCrawford_NoCore_Notions
open KelsoCrawford.NoCore
private theorem salaries_partition {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] (g : W → F) (s : W → ℝ) :
    (∑ j, ∑ i ∈ assignedTo g j, s i) = ∑ i, s i := by
  simp only [assignedTo, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp


theorem solution {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] (M : Market W F)
    (hu : ∀ i j s, M.u i j s = s) (hσ : ∀ i j, M.σ i j = 0)
    (A : Allocation W F) (hA : M.IsCore KelsoCrawford.ContinuousCore.anySalary A) (g : W → F) :
    M.totalProduct g ≤ M.totalProduct A.assign := by
  have hd (j : F) (C : Finset W) :
      KelsoCrawford.Process.profit (M.y j) C A.sal ≤
        KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal := by
    by_contra h
    have hgap : 0 < KelsoCrawford.Process.profit (M.y j) C A.sal -
        KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal := by linarith
    let d : ℝ := (KelsoCrawford.Process.profit (M.y j) C A.sal -
        KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal) / ((C.card : ℝ) + 1)
    have hden : 0 < (C.card : ℝ) + 1 := by positivity
    have hdpos : 0 < d := div_pos hgap hden
    apply hA.2.2
    refine ⟨j, C, fun i => A.sal i + d, ?_, ?_, ?_⟩
    · intro i hi
      trivial
    · intro i hi
      rw [hu, hu]
      linarith
    · have hdeq : d * ((C.card : ℝ) + 1) =
          KelsoCrawford.Process.profit (M.y j) C A.sal -
            KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal := by
        exact div_mul_cancel₀ _ (ne_of_gt hden)
      simp only [KelsoCrawford.Process.profit, Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul] at hdeq ⊢
      nlinarith
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset F)) =>
    hd j (assignedTo g j))
  simp only [KelsoCrawford.Process.profit, Finset.sum_sub_distrib] at hs
  have he : (∑ j, ∑ i ∈ A.hired j, A.sal i) = ∑ i, A.sal i := by
    exact salaries_partition A.assign A.sal
  rw [salaries_partition g A.sal, he] at hs
  change M.totalProduct g - (∑ i, A.sal i) ≤ M.totalProduct A.assign - (∑ i, A.sal i) at hs
  linarith

#print axioms solution
