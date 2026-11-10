-- Prove2me | solution 1 for MultiAllocToAlloc.Subadditive.corollary_11_moreover
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T19:15:37.140033+00:00
-- url     : https://prove2.me/submissions/37ddfb34-9f46-495b-800c-394a7bec713f

import Mathlib
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_PickingGame

private def w3 (e : Fin 3) : ℝ :=
  if e = 0 then 2 else 1

private def v3 (S : Finset (Fin 3)) : ℝ :=
  ∑ e ∈ S, w3 e

private lemma w3_nonneg (e : Fin 3) : 0 ≤ w3 e := by
  dsimp [w3]
  split_ifs <;> norm_num

private lemma v3_norm : MultiAllocToAlloc.Subadditive.IsNormalized v3 := by
  simp [MultiAllocToAlloc.Subadditive.IsNormalized, v3]

private lemma v3_mono : MultiAllocToAlloc.Subadditive.IsMonotone v3 := by
  intro S T hST
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun e _ _ => w3_nonneg e)

private lemma v3_sub : SubmodOrder.Subadditive v3 := by
  intro A B
  dsimp [v3]
  have h1 := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := w3)
  have h2 : 0 ≤ ∑ e ∈ A ∩ B, w3 e := Finset.sum_nonneg (fun e _ => w3_nonneg e)
  linarith

private lemma v3_delta : ∀ e ∈ (Finset.univ : Finset (Fin 3)), v3 {e} ≤ (2 : ℝ) := by
  intro e _
  simp only [v3, Finset.sum_singleton, w3]
  split_ifs <;> norm_num

private def f0 (e : Fin 3) : Fin 2 :=
  if e = 0 then 0 else 1

private lemma mms_v3_ge : (2 : ℝ) ≤ LittleCharity.MMS.mms v3 2 Finset.univ := by
  unfold LittleCharity.MMS.mms
  have hle : (2 : ℝ) ≤ ⨅ j : Fin 2, v3 (Finset.univ.filter (fun g => f0 g = j)) := by
    refine le_ciInf (fun j => ?_)
    fin_cases j
    · change (2 : ℝ) ≤ v3 (Finset.univ.filter (fun g => f0 g = 0))
      have hf : Finset.univ.filter (fun g : Fin 3 => f0 g = 0) = {0} := by decide
      rw [hf]
      simp [v3, w3]
    · change (2 : ℝ) ≤ v3 (Finset.univ.filter (fun g => f0 g = 1))
      have hf : Finset.univ.filter (fun g : Fin 3 => f0 g = 1) = {1, 2} := by decide
      rw [hf]
      have h12 : (1 : Fin 3) ≠ 2 := by decide
      simp [v3, w3, h12]
      norm_num
  have hsup :
      (⨅ j : Fin 2, v3 (Finset.univ.filter (fun g => f0 g = j))) ≤
        ⨆ f : Fin 3 → Fin 2, ⨅ j : Fin 2, v3 (Finset.univ.filter (fun g => f g = j)) :=
    le_ciSup
      (f := fun f : Fin 3 → Fin 2 => ⨅ j : Fin 2, v3 (Finset.univ.filter (fun g => f g = j)))
      (Set.Finite.bddAbove (Set.finite_range _)) f0
  exact hle.trans hsup

private lemma gameVal_step2_one :
    FairShares.gameVal v3 (0 : Fin 2) [1] ({2} : Finset (Fin 3)) {1} ≤ 1 := by
  have hne : ({2} : Finset (Fin 3)).Nonempty := ⟨2, by decide⟩
  have hp : (1 : Fin 2) ≠ 0 := by decide
  rw [FairShares.gameVal, dif_pos hne, if_neg hp]
  have hmem : (2 : Fin 3) ∈ ({2} : Finset (Fin 3)) := by decide
  refine (Finset.inf'_le _ hmem).trans ?_
  simp [FairShares.gameVal, v3, w3]

private lemma gameVal_step2_two :
    FairShares.gameVal v3 (0 : Fin 2) [1] ({1} : Finset (Fin 3)) {2} ≤ 1 := by
  have hne : ({1} : Finset (Fin 3)).Nonempty := ⟨1, by decide⟩
  have hp : (1 : Fin 2) ≠ 0 := by decide
  rw [FairShares.gameVal, dif_pos hne, if_neg hp]
  have hmem : (1 : Fin 3) ∈ ({1} : Finset (Fin 3)) := by decide
  refine (Finset.inf'_le _ hmem).trans ?_
  simp [FairShares.gameVal, v3, w3]

private lemma omegaQ_v3_le :
    MultiAllocToAlloc.Subadditive.omegaQ v3 Finset.univ ≤ 1 := by
  unfold MultiAllocToAlloc.Subadditive.omegaQ
  have hcard : (Finset.univ : Finset (Fin 3)).card = 3 := rfl
  have hseq : MultiAllocToAlloc.Subadditive.seqQ 3 = [1, 0, 1] := rfl
  rw [hcard, hseq]
  have hne0 : (Finset.univ : Finset (Fin 3)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  have hp0 : (1 : Fin 2) ≠ 0 := by decide
  rw [FairShares.gameVal, dif_pos hne0, if_neg hp0]
  refine (Finset.inf'_le _ (Finset.mem_univ (0 : Fin 3))).trans ?_
  have her0 : (Finset.univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide
  rw [her0]
  have hne1 : ({1, 2} : Finset (Fin 3)).Nonempty := ⟨1, by decide⟩
  rw [FairShares.gameVal, dif_pos hne1, if_pos rfl]
  refine Finset.sup'_le hne1 _ (fun e₁ he₁ => ?_)
  have he₁_cases : e₁ = 1 ∨ e₁ = 2 := by
    fin_cases e₁ <;> simp_all
  rcases he₁_cases with rfl | rfl
  · have her1 : ({1, 2} : Finset (Fin 3)).erase 1 = {2} := by decide
    have hins1 : (insert (1 : Fin 3) ∅ : Finset (Fin 3)) = {1} := by decide
    rw [her1, hins1]
    exact gameVal_step2_one
  · have her2 : ({1, 2} : Finset (Fin 3)).erase 2 = {1} := by decide
    have hins2 : (insert (2 : Fin 3) ∅ : Finset (Fin 3)) = {2} := by decide
    rw [her2, hins2]
    exact gameVal_step2_two

set_option linter.unusedVariables false in
theorem solution : ¬ (∀ {m : ℕ} (M : Finset (Fin m)) (v : Finset (Fin m) → ℝ)
    (hnorm : MultiAllocToAlloc.Subadditive.IsNormalized v)
    (hmono : MultiAllocToAlloc.Subadditive.IsMonotone v)
    (hsub : SubmodOrder.Subadditive v)
    (δ : ℝ) (hδ : ∀ e ∈ M, v {e} ≤ δ),
    LittleCharity.MMS.mms v 2 M ≤ MultiAllocToAlloc.Subadditive.omegaQ v M ∧
    LittleCharity.MMS.mms v 2 M ≤ MultiAllocToAlloc.Subadditive.omegaP v M) := by
  intro hAll
  have h := (hAll (m := 3) Finset.univ v3 v3_norm v3_mono v3_sub 2 v3_delta).1
  have hmms := mms_v3_ge
  have hom := omegaQ_v3_le
  linarith
