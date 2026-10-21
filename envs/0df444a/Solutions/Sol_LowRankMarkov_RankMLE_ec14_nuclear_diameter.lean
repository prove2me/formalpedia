-- Prove2me | solution 1 for LowRankMarkov.RankMLE.ec14_nuclear_diameter
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:34:47.081392+00:00
-- url     : https://prove2.me/submissions/253fd38c-f7a2-409d-8e0d-8f7f95b1659f

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic
import Definitions.Def_LowRankMarkov_RankMLE_Chain
import Definitions.Def_LowRankMarkov_RankMLE_Setting
import Theorems.Thm_LowRankMarkov_RankMLE_lemmaEC1_frob_le_kl
import Theorems.Thm_LowRankMarkov_RankMLE_rank_remark_nuclear_le

open LowRankMarkov.RankMLE CaiCandesShen.Convergence

theorem solution {p r : ℕ} (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (P Q : Matrix (Fin p) (Fin p) ℝ) (π : Fin p → ℝ)
    (hP : IsStochastic P) (hprim : IsPrimitive P) (hA1 : Assumption1 α β r P)
    (hπ : IsStationary π P) (hπ_pos : ∀ i, 0 < π i)
    (l : ℕ) (hl : 1 ≤ l) (η : ℝ) (hη : 0 < η)
    (hQ : RankFeasible α β r Q) (hC : ConcentrationClass α β P Q)
    (hηQ : η ≤ klDiv π P Q)
    (hlow : (2 : ℝ) ^ ((l : ℤ) - 1) * η ≤ klDiv π P Q)
    (hup : klDiv π P Q ≤ (2 : ℝ) ^ l * η) :
    nuclearNorm (Q - P) ≤ 2 * β * Real.sqrt ((2 : ℝ) ^ l * η * r / (p * α * piMin π)) := by
  have hnuc := (rank_remark_nuclear_le P Q hA1.1 hQ.2.2).2
  have hfrob := lemmaEC1_frob_le_kl α β hα hβ P Q π hP hprim hA1 hπ hπ_pos hC
  have hFsq : frobNorm (Q - P) ^ 2 = ∑ i, ∑ j, (P i j - Q i j) ^ 2 := by
    unfold frobNorm frobInner
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg ((Q - P) i j))]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.sub_apply]; ring
  have hcoef : 0 ≤ 2 * β ^ 2 / (α * piMin π * p) := by
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · subst hp0; simp
    have : 0 < piMin π := by
      have : Nonempty (Fin p) := ⟨⟨0, hp0⟩⟩
      obtain ⟨i₀, hi₀⟩ := exists_eq_ciInf_of_finite (f := π)
      unfold piMin; rw [← hi₀]; exact hπ_pos i₀
    positivity
  have hF2 : frobNorm (Q - P) ^ 2 ≤ 2 * β ^ 2 / (α * piMin π * p) * ((2 : ℝ) ^ l * η) := by
    rw [hFsq]; exact hfrob.trans (mul_le_mul_of_nonneg_left hup hcoef)
  have hFnn : 0 ≤ frobNorm (Q - P) := Real.sqrt_nonneg _
  refine hnuc.trans ?_
  have e1 : Real.sqrt (2 * (r : ℝ)) * frobNorm (Q - P) =
      Real.sqrt (2 * (r : ℝ) * frobNorm (Q - P) ^ 2) := by
    rw [Real.sqrt_mul (by positivity) (frobNorm (Q - P) ^ 2), Real.sqrt_sq hFnn]
  have e2 : 2 * β * Real.sqrt ((2 : ℝ) ^ l * η * r / (p * α * piMin π)) =
      Real.sqrt (2 * (r : ℝ) * (2 * β ^ 2 / (α * piMin π * p) * ((2 : ℝ) ^ l * η))) := by
    have h4 : 2 * (r : ℝ) * (2 * β ^ 2 / (α * piMin π * p) * ((2 : ℝ) ^ l * η)) =
        (2 * β) ^ 2 * ((2 : ℝ) ^ l * η * r / (p * α * piMin π)) := by ring
    rw [h4, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [e1, e2]
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left hF2 (by positivity)
