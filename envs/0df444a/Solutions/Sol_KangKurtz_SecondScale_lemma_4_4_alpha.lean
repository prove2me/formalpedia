-- Prove2me | solution 1 for KangKurtz.SecondScale.lemma_4_4_alpha
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:36:12.162672+00:00
-- url     : https://prove2.me/submissions/c56fcc1f-e417-4345-a0c4-59efcd9b2ef0

import Mathlib
import Definitions.Def_KangKurtz_SecondScale_Setting

set_option autoImplicit false
open KangKurtz.SecondScale

theorem solution {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i) (β : Fin r → ℝ)
    (θ : Fin s → ℝ) (i : Fin s) (l : Fin r)
    (hθ : θ ∈ K2 ν ν' α β) (hl : l ∈ GammaR1 ν ν' α β i)
    (hdot : KangKurtz.SCC.dot ν ν' θ l ≠ 0) :
    α i < alphaTheta α θ := by
  obtain ⟨hθ0, hθk⟩ := hθ
  have hl' : r1 ν ν' α β + (KangKurtz.SCC.rho ν α β l : EReal) = (α i : EReal) := by
    unfold GammaR1 at hl
    simpa using hl
  have hi : i ∈ S1 ν ν' α β := by
    unfold S1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨l, hl⟩
  have hsum := hθk l ⟨i, hl⟩
  -- split the dot product over S1 and its complement
  have hdot' : KangKurtz.SCC.dot ν ν' θ l =
      ∑ j ∈ Finset.univ.filter (fun j => j ∉ S1 ν ν' α β), θ j * KangKurtz.SCC.zeta ν ν' l j := by
    unfold KangKurtz.SCC.dot
    have h1 : ∑ j, θ j * Pi1 ν ν' α β (KangKurtz.SCC.zeta ν ν' l) j =
        ∑ j ∈ Finset.univ.filter (fun j => j ∈ S1 ν ν' α β), θ j * KangKurtz.SCC.zeta ν ν' l j := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold Pi1
      by_cases hj : j ∈ S1 ν ν' α β <;> simp [hj]
    rw [h1] at hsum
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ S1 ν ν' α β), hsum, zero_add]
  rw [hdot'] at hdot
  obtain ⟨j, hj, hj0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdot
  have hjS : j ∉ S1 ν ν' α β := (Finset.mem_filter.mp hj).2
  have hθj : θ j ≠ 0 := left_ne_zero_of_mul hj0
  have hzj : KangKurtz.SCC.zeta ν ν' l j ≠ 0 := right_ne_zero_of_mul hj0
  have hθpos : 0 < θ j := lt_of_le_of_ne (hθ0 j) (Ne.symm hθj)
  have hne : ν l j ≠ ν' l j := by
    intro h
    apply hzj
    unfold KangKurtz.SCC.zeta
    rw [h]; ring
  -- l lies in the union
  have hmem : l ∈ GammaSpPlus ν ν' j ∪ GammaSpMinus ν ν' j := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact Finset.mem_union_left _ (by unfold GammaSpPlus; simpa using h)
    · exact Finset.mem_union_right _ (by unfold GammaSpMinus; simpa using h)
  have hne' : (GammaSpPlus ν ν' j ∪ GammaSpMinus ν ν' j).Nonempty := ⟨l, hmem⟩
  have hle1 : r1 ν ν' α β ≤ gammaSp ν ν' α β j := iInf_le _ j
  have hg : gammaSp ν ν' α β j =
      ((α j - (GammaSpPlus ν ν' j ∪ GammaSpMinus ν ν' j).sup' hne' (KangKurtz.SCC.rho ν α β) : ℝ) : EReal) := by
    unfold gammaSp; rw [dif_pos hne']
  have hsup : KangKurtz.SCC.rho ν α β l ≤
      (GammaSpPlus ν ν' j ∪ GammaSpMinus ν ν' j).sup' hne' (KangKurtz.SCC.rho ν α β) :=
    Finset.le_sup' (KangKurtz.SCC.rho ν α β) hmem
  have hle2 : r1 ν ν' α β ≤ ((α j - KangKurtz.SCC.rho ν α β l : ℝ) : EReal) := by
    refine hle1.trans ?_
    rw [hg]
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  have hle3 : (α i : EReal) ≤ (α j : EReal) := by
    rw [← hl']
    calc r1 ν ν' α β + (KangKurtz.SCC.rho ν α β l : EReal)
        ≤ ((α j - KangKurtz.SCC.rho ν α β l : ℝ) : EReal) + (KangKurtz.SCC.rho ν α β l : EReal) :=
          add_le_add hle2 le_rfl
      _ = (α j : EReal) := by
          rw [← EReal.coe_add]; congr 1; ring
  have hle : α i ≤ α j := EReal.coe_le_coe_iff.mp hle3
  have hlt : α i < α j := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      apply hjS
      unfold S1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨l, ?_⟩
      unfold GammaR1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← h]; exact hl'
  have hsupp : (support θ).Nonempty := ⟨j, by unfold support; simpa using hθpos⟩
  have hjs : j ∈ support θ := by unfold support; simpa using hθpos
  have : α j ≤ alphaTheta α θ := by
    unfold alphaTheta
    rw [dif_pos hsupp]
    exact Finset.le_sup' α hjs
  linarith
